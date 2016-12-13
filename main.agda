data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

infix 21 _::_
data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A

apply : {A : Set}{B : A → Set} →
  ((x : A) → B x) → (a : A) → B a
apply f a = f a

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x :: xs) = f x :: map f xs

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  _::_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

head : {A : Set}{n : ℕ} → Vec A (suc n) → A
head (x :: _) = x

vmap : {A B : Set}{n : ℕ} → (A → B) → Vec A n → Vec B n
vmap f [] = []
vmap f (x :: xs) = f x :: vmap f xs

data False : Set where
record True : Set where

trivial : True
trivial = _

data Bool : Set where
  true : Bool
  false : Bool

isTrue : Bool → Set
isTrue true = True
isTrue false = False

_<_ : ℕ → ℕ → Bool
_ < zero = false
zero < (suc _) = true
suc m < suc n = m < n

length : {A : Set} → List A → ℕ
length [] = zero
length (x :: xs) = suc (length xs)

lookup : {A : Set}(xs : List A)(n : ℕ) →
  isTrue (n < length xs) → A
lookup [] n ()
lookup (x :: _) zero _ = x
lookup (_ :: xs) (suc n) p = lookup xs n p

data _==_ {A : Set}(x : A) : A → Set where
  refl : x == x

x : zero == zero
x = refl

data _≤_ : ℕ → ℕ → Set where
  leq-zero : {n : ℕ} → zero ≤ n
  leq-suc : {m n : ℕ} → m ≤ n → suc m ≤ suc n

leq-trans : {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
leq-trans leq-zero _ = leq-zero
leq-trans (leq-suc p) (leq-suc q) = leq-suc (leq-trans p q)

y : zero ≤ suc (suc zero)
y = leq-zero

z : suc (suc zero) ≤ suc (suc (suc (suc zero)))
z = leq-suc (leq-suc (leq-zero))

z' : zero ≤ suc (suc (suc (suc zero)))
z' = leq-trans y z

min : ℕ → ℕ → ℕ
min x y with x < y
min x _ | true = x
min _ y | false = y

filter : {A : Set} → (A → Bool) → List A → List A
filter _ [] = []
filter f (x :: xs) with f x
... | true = x :: filter f xs
... | false = filter f xs

even : ℕ → Bool
even zero = true
even (suc zero) = false
even (suc (suc n)) = even n

l : List ℕ
l = filter even (zero :: (suc zero :: (suc (suc (suc zero)) ::
  ((suc (suc zero)) :: []))))

data _≠_ : ℕ → ℕ → Set where
  z≠s : {n : ℕ} → zero ≠ suc n
  s≠z : {n : ℕ} → suc n ≠ zero
  s≠s : {m n : ℕ} → m ≠ n → suc m ≠ suc n

data Equal? (n m : ℕ) : Set where
  eq : n == m → Equal? n m
  neq : n ≠ m → Equal? n m

equal? : (n m : ℕ) → Equal? n m
equal? zero zero = eq refl
equal? zero (suc _) = neq z≠s
equal? (suc _) zero = neq s≠z
equal? (suc m) (suc n) with equal? m n
equal? (suc n) (suc .n) | eq refl = eq refl
equal? (suc n) (suc m) | neq p = neq (s≠s p)

infix 20 _⊆_
data _⊆_ {A : Set} : List A → List A → Set where
  stop : [] ⊆ []
  drop : ∀ {xs y ys} → xs ⊆ ys → xs ⊆ y :: ys
  keep : ∀ {x xs ys} → xs ⊆ ys → x :: xs ⊆ x :: ys

α : [] ⊆ suc zero :: []
α = drop stop

filter-subeq : {A : Set}(p : A → Bool)(xs : List A) → filter p xs ⊆ xs
filter-subeq _ [] = stop
filter-subeq p (x :: xs) with p x
... | true = keep (filter-subeq p xs)
... | false = drop (filter-subeq p xs)

data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (suc n)
  fsuc : {n : ℕ} → Fin n → Fin (suc n)

_!_ : {n : ℕ}{A : Set} → Vec A n → Fin n → A
[] ! ()
(x :: _) ! fzero = x
(_ :: xs) ! (fsuc n) = xs ! n

Matrix : Set → ℕ → ℕ → Set
Matrix A m n = Vec (Vec A n) m

vec : {n : ℕ}{A : Set} → A → Vec A n
vec {zero} _ = []
vec {suc n} x = x :: vec {n} x

infixl 90 _$_
_$_ : {n : ℕ}{A B : Set} → Vec (A → B) n → Vec A n → Vec B n
[] $ [] = []
(f :: fs) $ (x :: xs) = f x :: fs $ xs

fin : (n : ℕ) → Fin (suc n)
fin zero = fzero
fin (suc m) = fsuc (fin m)

nat : {max : ℕ} → Fin max → ℕ
nat fzero = zero
nat (fsuc n) = suc (nat n)

relax : {max : ℕ} → Fin max → Fin (suc max)
relax fzero = fzero
relax (fsuc n) = fsuc (relax n)

range : (max : ℕ) (n : Fin max) → Vec (Fin max) (nat n)
range (suc max) fzero = []
range (suc (suc max)) (fsuc fzero) = fzero :: range (suc (suc max)) fzero
range (suc max) (fsuc n) = n :: range (suc max) ?

{-
transpose : ∀ {A m n} → Matrix A m n → Matrix A n m
transpose {m} {n} mat =
  (\idx → (vec {m} (\r → r ! fzero)) $ mat) $ (range n)
-}
