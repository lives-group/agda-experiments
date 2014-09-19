module Unify where

-- Translated from http://strictlypositive.org/unify.ps.gz

open import Data.Empty
import Data.Maybe as Maybe
open Maybe hiding (map)
open import Data.Nat
open import Data.Fin
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality

_>>=_ : ∀ {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
just x >>= f = f x
nothing >>= f = nothing

data Term (n : ℕ) : Set where
  ι : (i : Fin n) → Term n
  leaf : Term n
  _fork_ : (s t : Term n) → Term n

map : ∀ {m n} → (Fin m → Fin n) → Fin m → Term n
map r i = ι (r i)

bind : ∀ {m n} → (Fin m → Term n) → Term m → Term n
bind f (ι i) = f i
bind f leaf = leaf
bind f (s fork t) = (bind f s) fork (bind f t)

compose : ∀ {m n l} → (Fin m → Term n) → (Fin l → Term m) → (Fin l → Term n)
compose f g i = bind f (g i)

thin : ∀ {n} → Fin (suc n) → Fin n → Fin (suc n)
thin zero y = suc y
thin (suc x) zero = zero
thin (suc x) (suc y) = suc (thin x y)

data Thick {n} (x : Fin (suc n)) : Fin (suc n) → Set where
  yes : (y : Fin n) → Thick x (thin x y)
  no  : Thick x x

thick : ∀ {n} -> (x y : Fin (suc n)) -> Thick x y
thick zero zero = no
thick zero (suc y) = yes y
thick {zero} (suc ()) _
thick {suc _} (suc x) zero = yes zero
thick {suc _} (suc x) (suc y) with thick x y
thick {suc _} (suc x) (suc ._) | yes y = yes (suc y)
thick {suc _} (suc x) (suc ._) | no    = no

_for_ : ∀ {n} → Term n → Fin (suc n) → Fin (suc n) → Term n
(t for x) y with thick x y
(t for x) ._ | yes z = ι z
(t for x) ._ | no    = t

data Occurs {n} (x : Fin (suc n)) : Term (suc n) → Set where
  ι : Occurs x (ι x)
  forkˡ : ∀ {s′ t′} (s : Occurs x s′) → Occurs x (s′ fork t′)
  forkʳ : ∀ {s′ t′} (t : Occurs x t′) → Occurs x (s′ fork t′)

data Check {n} (x : Fin (suc n)) : Term (suc n) → Set where
  yes : (c : Term n) → Check x (bind (map (thin x)) c)
  no  : ∀ {t} (o : Occurs x t) → Check x t

check : ∀ {n} (x : Fin (suc n)) (t : Term (suc n)) → Check x t
check x (ι i) with thick x i
check x (ι ._) | yes y = yes (ι y)
check x (ι ._) | no = no ι
check x leaf = yes leaf
check x (s fork t) with check x s | check x t
check x (._ fork ._) | yes q | yes r = yes (q fork r)
check x (s  fork  t) | _     | no ¬r = no  (forkʳ ¬r)
check x (s  fork  t) | no ¬q | _     = no  (forkˡ ¬q)



data AList : (m n : ℕ) → Set where
  nil  : ∀ {n} → AList n n
  snoc : ∀ {m n} (as : AList m n) (a : Term m) (i : Fin (suc m)) → AList (suc m) n

comp : ∀ {m n l} → AList m n → AList l m → AList l n
comp as nil = as
comp as (snoc bs b i) = snoc (comp as bs) b i

sub : ∀ {m n} → AList m n → Fin m → Term n
sub nil = ι
sub (snoc as a i) = compose (sub as) (a for i)

flexFlex : ∀ {n} (x y : Fin n) → ∃ (AList n)
flexFlex {zero} () ()
flexFlex {suc n} x y with thick x y
flexFlex {suc n} x ._ | yes t = , snoc nil (ι t) x
flexFlex {suc n} x ._ | no    = , nil

flexRigid : ∀ {n} → Fin n → Term n → Maybe (∃ (AList n))
flexRigid {zero} () t
flexRigid {suc n} x t with check x t
flexRigid {suc n} x ._ | yes c = just (, (snoc nil c x))
flexRigid {suc n} x ._ | no  o = nothing


amgu : ∀ {n} (s t : Term n) → ∃ (AList n) → Maybe (∃ (AList n))
amgu leaf leaf xs = just xs
amgu leaf (t fork t₁) xs = nothing
amgu (s fork s₁) leaf xs = nothing
amgu (s fork s₁) (t fork t₁) xs = amgu s t xs >>= amgu s₁ t₁
amgu (ι x) (ι y) (n , nil) = just (flexFlex x y)
amgu (ι x) t (n , nil) = flexRigid x t
amgu s (ι y) (n , nil) = flexRigid y s
amgu s t (n , snoc xs x i) with amgu (bind (x for i) s) (bind (x for i) t) (, xs)
amgu s t (n , snoc xs x i) | just a  = just (, (snoc (proj₂ a) x i))
amgu s t (n , snoc xs x i) | nothing = nothing

mgu : ∀ {n} (s t : Term n) → Maybe (∃ (AList n))
mgu s t = amgu s t (, nil)
