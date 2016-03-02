module MicroKanren

import Data.SortedMap


Var : Type
Var = Int

data Term a
  = LVar Var
  | LVal a
  | Pair (Term a) (Term a)

Substitution : Type -> Type
Substitution a = SortedMap Var (Term a)

record State : Type -> Type where
   MkState : (s : Substitution a) ->
             (c : Var) -> State a

data LStream a
  = Empty
  | Immature (Lazy (LStream a))
  | Mature (State a) (LStream a)

Goal : Type -> Type
Goal a = (State a) -> LStream a


interface Eq a => Unifiable a where
  unifyLVal : a -> a -> Substitution a -> Maybe (Substitution a)
  unifyLVal u v s = if u == v
                    then Just s
                    else Nothing


unit : Goal a
unit sc = Mature sc Empty

mzero : LStream a
mzero = Empty


extS : Var -> Term a -> Substitution a -> Substitution a
extS k v s = insert k v s

walk : Term a -> Substitution a -> Term a
walk t@(LVar v) s = case lookup v s of
                      Just u => walk u s
                      Nothing => LVar v    -- is `t` not bound?
walk t _ = t

unify : Unifiable a => Term a -> Term a -> Substitution a -> Maybe (Substitution a)
unify u v s =
  let u' = walk u s
      v' = walk v s
  in
      case (u', v') of
        (LVar n, LVar m) => if n == m then Just s else Nothing
        (LVal x, LVal y) => unifyLVal x y s
        (LVar n, _) => Just (extS n v' s)
        (_, LVar m) => Just (extS m u' s)
        (Pair x y, Pair x1 y1) => case unify x x1 s of
                                    Just s' => unify y y1 s'
                                    Nothing => Nothing
        _ => Nothing


mplus : LStream a -> LStream a -> LStream a
mplus Empty          s2 = s2
mplus (Immature s1)  s2 = Immature (Delay (mplus s2 s1))
mplus (Mature sc s1) s2 = Mature sc (mplus s2 s1)

bind : LStream a -> Goal a -> LStream a
bind Empty         g = mzero
bind (Immature s)  g = Immature (Delay (bind s g))
bind (Mature sc s) g = mplus (g sc) (bind s g)

infixl 2 ===
(===) : Unifiable a => Term a -> Term a -> Goal a
(===) u v =
  \sc => case unify u v (s sc) of
           Just s' => unit (record { s = s' } sc)
           Nothing => mzero

callFresh : (Term a -> Goal a) -> Goal a
callFresh f =
  \sc => let c' = c sc
         in f (LVar c') (record { c = c' + 1} sc)

disj : Goal a -> Goal a -> Goal a
disj g1 g2 =
  \sc => g1 sc `mplus` g2 sc

conj : Goal a -> Goal a -> Goal a
conj g1 g2 =
  \sc => g1 sc `bind` g2
