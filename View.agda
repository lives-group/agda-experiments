module View where

open import DTPA

data Parity : Nat -> Set where
  even : (k : Nat) -> Parity (k * 2)
  odd  : (k : Nat) -> Parity (1 + k * 2)

parity : (n : Nat) -> Parity n
parity zero = even zero
parity (suc n) with parity n
parity (suc .(k * 2))     | even k = odd k
parity (suc .(1 + k * 2)) | odd  k = even (suc k)

half : Nat -> Nat
half n with parity n
half .(k * 2)     | even k = k
half .(1 + k * 2) | odd  k = k

infixr 30 _:all:_
data All {A : Set}(P : A -> Set) : List A -> Set where
  all[]   : All P []
  _:all:_ : forall {x xs} -> P x -> All P xs -> All P (x :: xs)

satisfies : {A : Set} -> (A -> Bool) -> A -> Set
satisfies p x = isTrue (p x)

data Find {A : Set}(p : A -> Bool) : List A -> Set where
  found     : (xs : List A)(y : A) -> satisfies p y -> (ys : List A) -> Find p (xs ++ y :: ys)
  not-found : forall {xs} -> All (satisfies (not ∘ p)) xs -> Find p xs

--find₁ : {A : Set}(p : A -> Bool)(xs : List A) -> Find p xs
--find₁ p [] = not-found all[]
--find₁ p (x :: xs) with p x
--...| true = found [] x {!!} xs
--...| false = {!!}

data Inspect {A : Set}(x : A) : Set where
  it : (y : A) -> x == y -> Inspect x

inspect : {A : Set}(x : A) -> Inspect x
inspect x = it x refl

trueIsTrue : {x : Bool} -> x == true -> isTrue x
trueIsTrue refl = _

falseIsFalse : {x : Bool} -> x == false -> isFalse x
falseIsFalse refl = _

find : {A : Set}(p : A -> Bool)(xs : List A) -> Find p xs
find p [] = not-found all[]
find p (x :: xs) with inspect (p x)
...| it true prf = found [] x (trueIsTrue prf) xs
...| it false prf with find p xs
find p (x :: ._) | it false _   | found xs y py ys = found (x :: xs) y py ys
find p (x :: xs) | it false prf | not-found npxs   = not-found (falseIsFalse prf :all: npxs)

data _Per_ {A : Set}(x : A) : List A -> Set where
  hd : forall {xs}   -> x Per x :: xs
  t1 : forall {y xs} -> x Per xs -> x Per y :: xs

index : forall {A}{x : A}{xs} -> x Per xs -> Nat
index hd     = zero
index (t1 p) = suc (index p)

data Lookup {A : Set}(xs : List A) : Nat -> Set where
  inside  : (x : A)(p : x Per xs) -> Lookup xs (index p)
  outside : (m : Nat) -> Lookup xs (length xs + m)

_!!_ : {A : Set}(xs : List A)(n : Nat) -> Lookup xs n
[] !! n = outside n
(x :: xs) !! zero = inside x hd
(x :: xs) !! suc n with xs !! n
(x :: xs) !! suc .(index p)       | inside y p = inside y (t1 p)
(x :: xs) !! suc .(length xs + n) | outside n  = outside n

infixr 30 _⇒_ 
data Type : Set where
  ₁   : Type
  _⇒_ : Type -> Type -> Type

data Equal?? : Type -> Type -> Set where
  yes : forall {τ}   -> Equal?? τ τ
  no  : forall {σ τ} -> Equal?? σ τ

_=?=_ : (σ τ : Type) -> Equal?? σ τ
₁       =?= ₁       = yes
₁       =?= _ ⇒ _   = no
_ ⇒ _   =?= ₁       = no
σ₁ ⇒ τ₁ =?= σ₂ ⇒ τ₂ with σ₁ =?= σ₂ | τ₁ =?= τ₂
σ ⇒ τ   =?= .σ ⇒ .τ  | yes | yes = yes
σ₁ ⇒ τ₁ =?= σ₂ ⇒ τ₂  | _   | _   = no

infixl 80 _%_
data Raw : Set where
  var : Nat -> Raw
  _%_ : Raw -> Raw -> Raw
  lam : Type -> Raw -> Raw

Cxt = List Type

data Term (⌈ : Cxt) : Type -> Set where
  var : forall {τ}   -> τ Per ⌈ -> Term ⌈ τ
  _%_ : forall {σ τ} -> Term ⌈ (σ ⇒ τ) -> Term ⌈ σ -> Term ⌈ τ
  lam : forall σ {τ} -> Term (σ :: ⌈) τ -> Term ⌈ (σ ⇒ τ)

erase : forall {⌈ τ} -> Term ⌈ τ -> Raw
erase (var x)   = var (index x)
erase (t % u)   = erase t % erase u
erase (lam σ t) = lam σ (erase t)

data Infer (⌈ : Cxt) : Raw -> Set where
  ok    : (τ : Type)(t : Term ⌈ τ) -> Infer ⌈ (erase t)
  bad   : {e : Raw} -> Infer ⌈ e
  
infer : (⌈ : Cxt)(e : Raw) -> Infer ⌈ e
infer ⌈ (var n) with ⌈ !! n
infer ⌈ (var .(length ⌈ + n)) | outside n  = bad
infer ⌈ (var .(index x))      | inside σ x = ok σ (var x)
infer ⌈ (e₁ % e₂) with infer ⌈ e₁
infer ⌈ (e₁ % e₂)          | bad = bad
infer ⌈ (.(erase t₁) % e₂) | ok ₁ t₁ = bad
infer ⌈ (.(erase t₁) % e₂) | ok (σ ⇒ τ) t₁ with infer ⌈ e₂
infer ⌈ (.(erase t₁) % e₂)          | ok (σ ⇒ τ) t₁ | bad = bad
infer ⌈ (.(erase t₁) % .(erase t₂)) | ok (σ ⇒ τ) t₁ | ok σ₀ t₂ with σ =?= σ₀
infer ⌈ (.(erase t₁) % .(erase t₂)) | ok (σ ⇒ τ) t₁ | ok .σ t₂ | yes = ok τ (t₁ % t₂)
infer ⌈ (.(erase t₁) % .(erase t₂)) | ok (σ ⇒ τ) t₁ | ok σ₀ t₂ | no  = bad
infer ⌈ (lam σ e) with infer (σ :: ⌈) e
infer ⌈ (lam σ .(erase t)) | ok τ t = ok (σ ⇒ τ) (lam σ t)
infer ⌈ (lam σ e)          | bad    = bad

module Universes where
 
  --data   False : Set where
  --record True  : Set where

  --data Bool : Set where
  --  true  : True
  --  false : False

  --isTrue : Bool -> Set
  --isTrue true  = True
  --isTrue false = False

  infixr 30 not_
  infixr 25 _and_

  not_ : Bool -> Bool
  not true  = false
  not false = true

  _and_ : Bool -> Bool -> Bool
  true  and x = x
  false and x = false

  notNotId : (a : Bool) -> isTrue (not_ (not_ a)) -> isTrue a -- ?? Deu biziu aqui
  notNotId true p = p
  notNotId false ()
  
  andIntro : (a b : Bool)-> isTrue a -> isTrue b -> isTrue (a and b)
  andIntro true  _ _  p = p
  andIntro false _ () _

  nonZero : Nat -> Bool
  nonZero zero    = false
  nonZero (suc _) = true

  postulate _div_ : Nat -> (m : Nat){p : isTrue (nonZero m)} -> Nat
  
  three = 16 div 5
