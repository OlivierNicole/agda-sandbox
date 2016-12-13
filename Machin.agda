module Machin where
  open import Data.Nat renaming (ℕ to Nat) hiding (fold)

  data Parity : Nat -> Set where
    even : (k : Nat) -> Parity (k * 2)
    odd  : (k : Nat) -> Parity (1 + k * 2)

  parity : (n : Nat) -> Parity n
  parity zero = even zero
  parity (suc zero) = odd zero
  parity (suc (suc n)) with parity n
  parity (suc (suc .(k * 2))) | even k = even (suc k)
  parity (suc (suc .(suc (k * 2)))) | odd k = odd (suc k)


  data False : Set where

  data True : Set where
    [] : True

  infixr 50 _|+|_ _⊕_
  infixr 60 _|x|_ _×_

  data Functor : Set1 where
    |Id|  : Functor
    |K|   : Set -> Functor
    _|+|_ : Functor -> Functor -> Functor
    _|x|_ : Functor -> Functor -> Functor

  data _⊕_ (A B : Set) : Set where
    inl : A -> A ⊕ B
    inr : B -> A ⊕ B

  data _×_ (A B : Set) : Set where
    _,_ : A -> B -> A × B

  [_] : Functor -> Set -> Set
  [ |Id| ] t = t
  [ |K| x ] t = x
  [ f |+| g ] t = [ f ] t ⊕ [ g ] t
  [ f |x| g ] t = [ f ] t × [ g ] t

  map : (F : Functor){X Y : Set} -> (X -> Y) -> [ F ] X -> [ F ] Y
  map |Id| f x = f x
  map (|K| x) f x₁ = x₁
  map (F |+| G) f (inl x) = inl (map F f x)
  map (F |+| G) f (inr x) = inr (map G f x)
  map (F |x| G) f (x , x₁) = map F f x , map G f x₁

  option : Set → Set
  option t = True ⊕ t

  optmap : {T U : Set} → (T → U) → option T → option U
  optmap = map (|K| True |+| |Id|)

  data μ_ (F : Functor) : Set where
    <_> : [ F ] (μ F) -> μ F

  mapFold : forall {X} F G -> ([ G ] X -> X) -> [ F ] (μ G) -> [ F ] X
  mapFold |Id| G φ < x > = φ (mapFold G G φ x)
  mapFold (|K| x) G φ x₁ = x₁
  mapFold (F |+| F₁) G φ (inl x) = inl (mapFold F G φ x)
  mapFold (F |+| F₁) G φ (inr x) = inr (mapFold F₁ G φ x)
  mapFold (F |x| F₁) G φ (x , x₁) = mapFold F G φ x , mapFold F₁ G φ x₁

  fold : {F : Functor}{A : Set} -> ([ F ] A -> A) -> μ F -> A
  fold {F} φ < x > = φ (mapFold F F φ x)

  listF : Functor
  listF = |K| True |+| (|K| Nat |x| |Id|)

  listnat : Set
  listnat = μ listF

  nil : listnat
  nil = < (inl []) >

  cons : Nat → listnat → listnat
  cons x xs = < (inr (x , xs)) >
