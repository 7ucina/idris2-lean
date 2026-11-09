||| Specialisation of higher-order functions for known closures, and
||| reduction of applications of known closures to direct calls (in the spirit
||| of Lean 4's `specialize` pass).
|||
|||   let c = pap g caps; ... f a c b ...
||| where f applies its parameter becomes
|||   ... f' a b caps ...
||| with  f' a b caps' = let c = pap g caps' in body_f   (self calls -> f')
||| after which applications of c inside f' are reduced to direct calls of g.
||| The transformation is always semantics preserving: the specialised
||| function rebuilds exactly the closure it was given.
module Lean.Spec

import Core.Name
import Lean.IR
import Control.Monad.State
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.SortedSet

%default covering

record SState where
  constructor MkSS
  decls : SortedMap Name Decl
  cache : SortedMap String Name
  pending : List Name
  count : Nat
  origin : SortedMap Name (Name, Nat, Nat)   -- clone -> (original, removed param, #captures)

S : Type -> Type
S = State SState

-- Limits against code explosion
maxSpecs : Nat
maxSpecs = 2000

maxBodySize : Nat
maxBodySize = 400

size : Body -> Nat
size (BLet _ _ _ b) = S (size b)
size (BJp _ _ jb r) = size jb + size r
size (BCase _ _ alts) = S (foldl (+) 0 (map (size . altBody) alts))
size _ = 1

||| Is parameter p used in a way that benefits from knowing its value?
usesAsFunction : Var -> Body -> Bool
usesAsFunction p (BLet _ _ (EAp f _) b) = f == p || usesAsFunction p b
usesAsFunction p (BLet _ _ (EFap _ as) b) = (AVar p `elem` as) || usesAsFunction p b
usesAsFunction p (BLet _ _ _ b) = usesAsFunction p b
usesAsFunction p (BJp _ _ jb r) = usesAsFunction p jb || usesAsFunction p r
usesAsFunction p (BCase _ _ alts) = any (usesAsFunction p . altBody) alts
usesAsFunction p _ = False

maxVarB : Body -> Int
maxVarB (BLet x _ _ b) = max x (maxVarB b)
maxVarB (BJp _ ps jb r) = foldl max (max (maxVarB jb) (maxVarB r)) (map pvar ps)
maxVarB (BCase x _ alts) = foldl max x (map (maxVarB . altBody) alts)
maxVarB (BRet (AVar x)) = x
maxVarB _ = 0

removeAt : Nat -> List a -> List a
removeAt _ [] = []
removeAt Z (_ :: xs) = xs
removeAt (S k) (x :: xs) = x :: removeAt k xs

at : Nat -> List a -> Maybe a
at _ [] = Nothing
at Z (x :: _) = Just x
at (S k) (_ :: xs) = at k xs

||| Redirect self-recursive calls passing p unchanged at position i
redirect : Name -> Nat -> Var -> Name -> List Arg -> Body -> Body
redirect f i p f' extra (BLet z t (EFap g as) b) =
  let e = if g == f && at i as == Just (AVar p)
             then EFap f' (removeAt i as ++ extra)
             else EFap g as
  in BLet z t e (redirect f i p f' extra b)
redirect f i p f' extra (BLet z t e b) = BLet z t e (redirect f i p f' extra b)
redirect f i p f' extra (BJp j ps jb r) = BJp j ps (redirect f i p f' extra jb) (redirect f i p f' extra r)
redirect f i p f' extra (BCase x t alts) = BCase x t (map (\a => setAltBody a (redirect f i p f' extra (altBody a))) alts)
redirect f i p f' extra b = b

capsKey : List Arg -> String
capsKey = pack . map (\a => case a of
                              AIrr => '_'
                              AVar _ => 'v')

getSpec : Decl -> Nat -> Name -> List Arg -> S (Maybe Name)
getSpec d i g caps =
  do st <- get
     let key = show d.name ++ "|" ++ show i ++ "|" ++ show g ++ "|" ++ capsKey caps
     case lookup key st.cache of
       Just n => pure (Just n)
       Nothing =>
         if st.count >= maxSpecs then pure Nothing else
         case at i d.params of
           Nothing => pure Nothing
           Just p =>
             do let n = MN ("spec:" ++ show d.name ++ "@" ++ show g) (cast st.count)
                let start = foldl max (maxVarB d.body) (map pvar d.params) + 1
                let capVars = take (length (filter isVar caps)) [start ..]
                let capArgs = rebuild caps capVars
                let extra = map AVar capVars
                let body = BLet p.pvar TObj (EPap g capArgs)
                                (redirect d.name i p.pvar n extra d.body)
                let params = removeAt i d.params ++ map (\v => MkParam v TObj False) capVars
                let nd = MkDecl n params d.ret body Normal
                let orig = fromMaybe (d.name, Z, Z) (lookup d.name st.origin)
                put ({ decls $= insert n nd, cache $= insert key n,
                       pending $= (n ::), count $= S,
                       origin $= insert n (d.name, i, length capVars) } st)
                pure (Just n)
  where
    isVar : Arg -> Bool
    isVar (AVar _) = True
    isVar AIrr = False

    rebuild : List Arg -> List Var -> List Arg
    rebuild (AIrr :: as) vs = AIrr :: rebuild as vs
    rebuild (AVar _ :: as) (v :: vs) = AVar v :: rebuild as vs
    rebuild _ _ = []

Known : Type
Known = SortedMap Var (Name, List Arg)

arityOf : Name -> S (Maybe Nat)
arityOf g = do st <- get
               pure (map (length . params) (lookup g st.decls))

||| Try to specialise a call
trySpec : Known -> Name -> List Arg -> S Expr
trySpec known f args =
  do st <- get
     case lookup f st.decls of
       Just d =>
         case d.kind of
           Normal =>
             if size d.body > maxBodySize then pure (EFap f args)
             else go d (zip [0 .. length args] args)
           _ => pure (EFap f args)
       Nothing => pure (EFap f args)
  where
    go : Decl -> List (Nat, Arg) -> S Expr
    go d [] = pure (EFap f args)
    go d ((i, AVar v) :: rest) =
      case (lookup v known, at i d.params) of
        (Just (g, caps), Just p) =>
          if usesAsFunction p.pvar d.body
             then do Just n <- getSpec d i g caps
                       | Nothing => pure (EFap f args)
                     pure (EFap n (removeAt i args ++ filter isVar caps))
             else go d rest
        _ => go d rest
      where
        isVar : Arg -> Bool
        isVar (AVar _) = True
        isVar AIrr = False
    go d (_ :: rest) = go d rest

specBody : Known -> Body -> S Body
specBody known (BLet z t e b) =
  do e' <- case e of
             EFap f args => trySpec known f args
             EAp c [a] =>
               case lookup c known of
                 Just (g, as) =>
                   do Just n <- arityOf g
                        | Nothing => pure e
                      pure (if length as + 1 == n then EFap g (as ++ [a])
                            else if length as + 1 < n then EPap g (as ++ [a])
                            else e)
                 Nothing => pure e
             _ => pure e
     -- a specialised call may itself be specialisable further
     e'' <- case (e, e') of
              (EFap f _, EFap f' args') => if f /= f' then trySpec known f' args' else pure e'
              (EAp _ _, EFap g args') => trySpec known g args'
              _ => pure e'
     let known' = case e'' of
                    EPap g as => insert z (g, as) known
                    _ => known
     BLet z t e'' <$> specBody known' b
specBody known (BJp j ps jb r) = BJp j ps <$> specBody known jb <*> specBody known r
specBody known (BCase x t alts) = BCase x t <$> traverse (\a => setAltBody a <$> specBody known (altBody a)) alts
specBody known b = pure b

processDecl : Name -> S ()
processDecl n =
  do st <- get
     case lookup n st.decls of
       Just d => case d.kind of
                   Normal => do b <- specBody empty d.body
                                modify ({ decls $= insert n ({ body := b } d) })
                   _ => pure ()
       Nothing => pure ()

processPending : Nat -> S ()
processPending Z = pure ()
processPending (S fuel) =
  do st <- get
     case st.pending of
       [] => pure ()
       (n :: ns) => do put ({ pending := ns } st)
                       processDecl n
                       processPending fuel

||| Returns the new declaration list and, for each clone, the function it was
||| cloned from, the index of the removed parameter and the number of added
||| parameters (appended at the end).
export
specialise : List Decl -> (List Decl, SortedMap Name (Name, Nat, Nat))
specialise ds =
  let st0 = MkSS (fromList (map (\d => (d.name, d)) ds)) empty [] 0 empty
      st = execState st0 (do traverse_ (processDecl . name) ds
                             processPending (maxSpecs * 2))
      origNames = map name ds
      origSet = SortedSet.fromList origNames
      newNames = filter (\n => not (contains n origSet)) (map fst (SortedMap.toList st.decls))
  in (mapMaybe (\n => lookup n st.decls) (origNames ++ newNames), st.origin)
