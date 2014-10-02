module SF where

open import Agda.Primitive

-- Não existe na apostila
--> Inicio
  
infix 4 _≡_

data _≡_ {l}{A : Set l}(x : A) : A → Set l where
  refl : x ≡ x
  
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

trans : ∀ {l}{A : Set l}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl
  
cong : ∀ {l}{A B : Set l}{x y : A}(f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

sym : ∀ {l}{A : Set l}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

--> Fim

  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  
  -- Chapter 1
  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

module BasicFunction where

  -- 1.2.1 Day of Week
  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  
  data Day : Set where
    Monday    : Day
    Tuesday   : Day
    Wednesday : Day
    Thursday  : Day
    Friday    : Day
    Saturday  : Day
    Sunday    : Day

  nextDay : Day → Day
  nextDay Monday    = Tuesday
  nextDay Tuesday   = Wednesday
  nextDay Wednesday = Thursday
  nextDay Thursday  = Friday
  nextDay Friday    = Saturday
  nextDay Saturday  = Sunday
  nextDay Sunday    = Monday
  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  
  -- 1.2.2 Booleans
  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  data Bool : Set where
    True  : Bool
    False : Bool

  ¬ : Bool → Bool
  ¬ True  = False
  ¬ False = True
  
  _∧_ : Bool → Bool → Bool
  _∧_ True t  = t
  _∧_ False _ = False

  _∨_ : Bool → Bool → Bool
  _∨_ True _  = True
  _∨_ False t = t
  
  infix  1  ¬
  infixl 10 _∨_
  infixl 10 _∧_

  -- ⇒ Exercise 1.1 (nand)
  ------------------------------------------------------------------------------------------------------
  
  nand : Bool → Bool → Bool
  nand a b = ¬ (a ∧ b)
  
  ------------------------------------------------------------------------------------------------------
  
  -- ⇒ Execise 1.2 (and3)
  ------------------------------------------------------------------------------------------------------

  and3 : Bool → Bool → Bool → Bool
  and3 a b c =  a ∧ b ∧ c

  ------------------------------------------------------------------------------------------------------

open BasicFunction public

module Natural where

  -- 1.2.4 Numbers
  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  
  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

  {-# BUILTIN NATURAL ℕ #-} -- Não é necessário mais do que o Builtin Natural
       
  infix 1 suc
  
  pred : ℕ → ℕ
  pred zero    = zero
  pred (suc n) = n

  evenb : ℕ → Bool
  evenb zero          = True
  evenb (suc zero)    = False
  evenb (suc (suc n)) = evenb n
  
  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  
  -- ⇒ Exercise 1.3 (oddb)
  ------------------------------------------------------------------------------------------------------

  oddb : ℕ → Bool
  oddb zero          = False
  oddb (suc zero)    = True
  oddb (suc (suc n)) = oddb n 
  --oddb n = ¬ (evenb n)

  ------------------------------------------------------------------------------------------------------
  
  _+_ : ℕ → ℕ → ℕ
  zero  + m = m
  suc n + m = suc (n + m)

  _×_ : ℕ → ℕ → ℕ
  zero  × m = zero
  suc n × m = m + (n × m)

  _-_ : ℕ → ℕ → ℕ 
  zero    - _       = zero
  suc n   - zero    = suc n
  (suc n) - (suc m) = n - m 

  infixl 20 _+_
  infixl 20 _-_
  infixl 10 _×_

  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  
  -- ⇒ Exercise 1.4 (fatorial)
  ------------------------------------------------------------------------------------------------------

  fatorial : ℕ → ℕ
  fatorial zero = 1
  fatorial (suc n) = (suc n) × fatorial n

  --_! : ℕ → ℕ 
  --zero ! = 1
  --(suc n) ! = (suc n) × (n !)  
  
  beqNat : ℕ → ℕ → Bool
  beqNat zero zero       = True
  beqNat (suc _) zero    = False
  beqNat zero (suc _)    = False
  beqNat (suc n) (suc m) = beqNat n m

  bleNat : ℕ → ℕ → Bool
  bleNat zero _ = True
  bleNat (suc _) zero = False
  bleNat (suc n) (suc m) = bleNat n m

  -- ⇒ Exercise 1.5 (bltNat)
  ------------------------------------------------------------------------------------------------------

  bltNat : ℕ → ℕ → Bool
  bltNat _       zero    = True
  bltNat zero    (suc _) = False
  bltNat (suc n) (suc m) = bltNat n m

  ------------------------------------------------------------------------------------------------------
  
  
  -- 1.3  Proof by Simplification
  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  
  lemmaPlus0N : ∀ (n : ℕ) → 0 + n ≡ n
  lemmaPlus0N n = refl
  
  lemmaPlus1N : ∀ (n : ℕ) → 1 + n ≡ suc n
  lemmaPlus1N n = refl
  
  lemmaMult0L : ∀ (n : ℕ) → 0 × n ≡ 0
  lemmaMult0L n = refl
  
  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  
  -- 1.4  Proof by Rewriting
  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  
  plusIdExample : ∀ (n m : ℕ) → n ≡ m → n + n ≡ m + m
  plusIdExample n .n refl = refl

  -- ⇒ Exercise 1.6 (plusIdExercise)
  ------------------------------------------------------------------------------------------------------

  plusIdExercice : ∀ (n m o : ℕ) → n ≡ m → m ≡ o → n + m ≡ m + o
  plusIdExercice n .n .n refl refl = refl

  ------------------------------------------------------------------------------------------------------  

  mult0Plus : ∀ (n m : ℕ) → (0 + n) × m ≡ n × m
  mult0Plus n m = refl

  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  
  -- 1.5  Proof by Case Analysis
  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  beqNatN+1=0 : ∀ (n : ℕ) → beqNat (n + 1) 0 ≡ False
  beqNatN+1=0 zero    = refl
  beqNatN+1=0 (suc n) = refl

  notInvolutive : ∀ (b : Bool) → ¬ (¬ b) ≡ b
  notInvolutive False = refl
  notInvolutive True  = refl

  zeroNBeq+1 : ∀ (n : ℕ) → beqNat 0 (n + 1) ≡ False
  zeroNBeq+1 zero    = refl
  zeroNBeq+1 (suc n) = refl

  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  
  -- 1.6  More Exercises
  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  
  -- ⇒ Exercise 1.8 (identityFnAppliedTwice and negativeFnAppliedTwice)
  ------------------------------------------------------------------------------------------------------
  
  identityFnAppliedTwice : ∀ (f : Bool → Bool)(_ : ∀ (x : Bool) → f x ≡ x) → ∀ (b : Bool) → f (f b) ≡ b -- Alterar no GitHub
  identityFnAppliedTwice f y x = trans (y (f x)) (y x) -- Resolveu sozinho

  negativeFnAppliedTwice : ∀ (f : Bool → Bool)(_ : ∀ (x : Bool) → f x ≡ ¬ x) → ∀ (b : Bool) → f (f b) ≡ b
  negativeFnAppliedTwice f y x = trans (y (f x)) (trans (cong ¬ (y x)) (notInvolutive x))

  ------------------------------------------------------------------------------------------------------

  -- ⇒ Exercise 1.9 (lemma)
  ------------------------------------------------------------------------------------------------------

  lemma : ∀ (b c : Bool) → (b ∧ c) ≡ (b ∨ c) → b ≡ c
  lemma False c prf = prf
  lemma True  c prf = sym prf
  
  -----------------------------------------------------------------------------------------------------
    
  -- ⇒ Exercise 1.10 
  -----------------------------------------------------------------------------------------------------
  
  -- 1.10 - 1 (defition of bynary number)
  -----------------------------------------------------------------------------------------------------
  
  data 𝔹 : Set where -- binary number
    zero   : 𝔹       -- zero
    double : 𝔹 → 𝔹   -- par
    dPlus  : 𝔹 → 𝔹   -- impar

  -----------------------------------------------------------------------------------------------------

  -- 1.10 - 2 (sucessor for bynary number ∧ convertion [bynary number → unary number])
  -----------------------------------------------------------------------------------------------------
  suc𝔹 : 𝔹 → 𝔹
  suc𝔹 zero       = dPlus zero
  suc𝔹 (double x) = dPlus x
  suc𝔹 (dPlus x)  = double (suc𝔹 x)

  𝔹ℕ : 𝔹 → ℕ
  𝔹ℕ zero       = zero
  𝔹ℕ (double x) = 2 × (𝔹ℕ x)
  𝔹ℕ (dPlus x)  = 2 × (𝔹ℕ x) + 1
  ------------------------------------------------------------------------------------------------------

open Natural public

  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  
  -- Chapter 2
  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

module Induction where
  
  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  
  -- 2.1  Naming Case
  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  
  andElim1 : ∀ (b c : Bool) → b ∧ c ≡ True → b ≡ True
  andElim1 True  c prf = refl
  andElim1 False c ()

  -- ⇒ Exercise 2.1 (andElim2)
  ------------------------------------------------------------------------------------------------------

  andElim2 : ∀ (b c : Bool) → b ∧ c ≡ True → c ≡ True
  andElim2 b True  prf = refl
  --andElim2 b False ()
  andElim2 True False ()
  andElim2 False False ()

  ------------------------------------------------------------------------------------------------------

  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  -- 2.2 Proof by Induction
  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  plus0R : ∀ (n : ℕ) → n + 0 ≡ n
  plus0R zero    = refl
  plus0R (suc n) = cong suc (plus0R n)

  minusDiag : ∀ (n : ℕ) → n - n ≡ 0
  minusDiag zero    = refl
  minusDiag (suc n) = minusDiag n

  -- ⇒ Exercise 2.2 (mult0R ∧ plusNSucM ∧ plusComm ∧ plusAssoc)
  ------------------------------------------------------------------------------------------------------

  mult0R : ∀ (n : ℕ) → n × 0 ≡ 0
  mult0R zero    = refl
  mult0R (suc n) = mult0R n

  plusNSucM : ∀ (n m : ℕ) → suc (n + m) ≡ n + suc m
  plusNSucM zero    m = refl 
  plusNSucM (suc n) m = cong suc (plusNSucM n m)

  plusComm : ∀ (n m : ℕ) → n + m ≡ m + n
  plusComm zero    m = sym (plus0R m)
  plusComm (suc n) m = trans (cong suc (plusComm n m)) (plusNSucM m n)

  plusAssoc : ∀ (n m p : ℕ) → n + (m + p) ≡ (n + m) + p
  plusAssoc zero    m p = refl
  plusAssoc (suc n) m p = cong suc (plusAssoc n m p)
  ------------------------------------------------------------------------------------------------------

  -- ⇒ Exercise 2.3 (doublePlus)
  ------------------------------------------------------------------------------------------------------

  double1 : ℕ → ℕ -- já existe double (criado para o binário)
  double1 zero    = zero
  double1 (suc n) = suc (suc (double1 n))
  
  doublePlus : ∀ (n : ℕ) → double1 n ≡ n + n
  doublePlus zero    = refl
  doublePlus (suc n) = cong suc (trans (cong suc (doublePlus n)) (plusNSucM n n))
  
  ------------------------------------------------------------------------------------------------------
  
  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  
  -- 2.3  Proofs within Proofs
  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  mult0Plus1 : ∀ (n m : ℕ) → (0 + n) × m ≡  n × m
  mult0Plus1 n m = cong (λ n → n × m) h where
    h : 0 + n ≡ n
    h = refl

  plusRearrenge : ∀ (n m p q : ℕ) → (n + m) + (p + q) ≡ (m + n) + (p + q)
  plusRearrenge n m p q = cong (\n → n + (p + q)) nmComm where
    nmComm : n + m ≡ m + n
    nmComm = plusComm n m

  -- ⇒ Exercise 2.4 (plusSwap ∧ multComm)
  ------------------------------------------------------------------------------------------------------

  plusSwap : ∀ (n m p : ℕ) → n + (m + p) ≡ m + (n + p)
  plusSwap n m p = trans (plusAssoc n m p) (trans (cong (λ a → a + p) nmComm) (mnpComm m n p) )  where
    nmComm : n + m ≡ m + n 
    nmComm = plusComm n m
    mnpComm : ∀ ( m n p : ℕ) → m + n + p ≡ m + (n + p)
    mnpComm zero    n p = refl
    mnpComm (suc m) n p = cong suc (mnpComm m n p)

  multComm : ∀ (n m : ℕ) → n × m ≡ m × n
  multComm zero    m = sym (mult0R m)
  multComm (suc n) m = trans (cong (λ a → m + a) (multComm n m)) (mMxN m n) where
    mMxN : ∀ (m n : ℕ) → m + (m × n) ≡ m × (suc n)
    mMxN zero    n = refl
    mMxN (suc m) n = cong suc (trans (plusSwap m n (m × n)) (cong (λ a → n + a) (mMxN m n))) 
  ------------------------------------------------------------------------------------------------------

  -- ⇒ Exercise 2.5 (evenNoddSucN) -- Corrigir na Apostila
  ------------------------------------------------------------------------------------------------------

  --evenNoddSucN : ∀ (n : ℕ) → evenb n ≡ ¬ (oddb (suc n)) -- n e par (se e somente se) nao (impar (suc n))? Falso ...
  --evenNoddSucN zero    = {!!}
  --evenNoddSucN (suc n) = {!!}

  evenOddSucN : ∀ (n : ℕ) → evenb n ≡ oddb (suc n)
  evenOddSucN zero       = refl
  evenOddSucN (suc zero) = refl
  evenOddSucN (suc n)    = {!!}

  ------------------------------------------------------------------------------------------------------

  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  
  -- 2.4 More Exercices
  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  
  -- ⇒ Exercise 2.6 (bleNatrefl ∧ zeroNbeqSuc ∧ andFalseR ∧ plusBleCompatL ∧ sucNBeq0 ∧ mult1L ∧ all3Spec ∧ multPlusDistR ∧ multAssoc ∧ beqNatRefl)
  ------------------------------------------------------------------------------------------------------
  
  bleNatRefl : ∀ (n : ℕ) → True ≡ bleNat n n
  bleNatRefl zero    = refl
  bleNatRefl (suc n) = bleNatRefl n

  zeroNbeqSuc : ∀ (n : ℕ) → beqNat 0 (suc n) ≡ False
  zeroNbeqSuc n = refl

  andFalseR : ∀ (b : Bool) → b ∧ False ≡ False
  andFalseR True  = refl
  andFalseR False = refl

  plusBleCompatL : ∀ (n m p : ℕ) → bleNat n m ≡ True → bleNat (p + n) (p + m) ≡ True
  plusBleCompatL n m zero    prf = prf
  plusBleCompatL n m (suc p) prf = plusBleCompatL n m p prf

  sucNBeq0 : ∀ (n : ℕ) → beqNat (suc n) zero ≡ False
  sucNBeq0 n = refl

  mult1L : ∀ (n : ℕ) → 1 × n ≡ n
  mult1L n = plus0R n

  all3Spec : ∀ (b c : Bool) → (b ∧ c) ∨ (¬ b ∨ ¬ c) ≡ True
  all3Spec True True  = refl
  all3Spec True False = refl
  all3Spec False c    = refl

  multPlusDistrR : ∀ (n m p : ℕ) → (n + m) × p ≡ (n × p) + (m × p)
  multPlusDistrR zero    m p = refl
  multPlusDistrR (suc n) m p = {!!}
  
  multAssoc : ∀ (n m p : ℕ) → n × (m × p) ≡ (n × m) × p
  multAssoc zero    m p = refl
  multAssoc (suc n) m p = {!!}

  beqNatRefl : ∀ (n : ℕ) → True ≡ beqNat n n
  beqNatRefl zero    = refl
  beqNatRefl (suc n) = beqNatRefl n

open Induction public

  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  
  -- Chapter 3
  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

module List where

  data ℕProd : Set where
    _,_ : ℕ → ℕ → ℕProd

  fst : ℕProd → ℕ -- colocar espaco
  fst (n , _) = n

  snd : ℕProd → ℕ
  snd (_ , n) = n

  surjectivePairing : ∀ (n m : ℕ) → (n , m) ≡ ((fst (n , m)) , (snd (n , m)))
  surjectivePairing n m = refl
  
  surjectivePairing1 : ∀ (p : ℕProd) → p ≡ ((fst p) , (snd p))
  surjectivePairing1 (n , m) = refl

  -- Exercise 3.1
  ------------------------------------------------------------------------------------------------------

  swap : ℕProd → ℕProd
  swap (n , m) = (m , n)

  fstSndSwap : (p : ℕProd) → (snd p , fst p) ≡ swap p
  fstSndSwap (n , m) = refl

  ------------------------------------------------------------------------------------------------------
  
  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  
  -- 3.2 List of Numbers
  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  data NList : Set where
    nil : NList
    _,_ : ℕ → NList → NList

  infixr 4 _,_

  sample : NList
  sample = 1 , 2 , 3 , nil

  repeat : ℕ → ℕ → NList
  repeat n zero    = nil
  repeat n (suc m) = n , repeat n m
  
  length : NList → ℕ
  length nil = 0
  length (x , xs) = suc (length xs)

  infixr 4 _++_
  
  _++_ : NList → NList → NList
  nil      ++ ys = ys
  (x , xs) ++ ys = x , (xs ++ ys)

  head : NList → (default : ℕ) → ℕ
  head nil     d = d
  head (x , _) _ = x

  tail : NList → NList
  tail nil      = nil
  tail (x , xs) = xs

  -- Exercise 3.2
  ------------------------------------------------------------------------------------------------------
  
  nonZeros : NList → NList
  nonZeros nil         = nil
  nonZeros (zero , xs) = nonZeros xs
  nonZeros (x , xs)    = x , nonZeros xs

  testNonZeros : nonZeros ( 0 , 1 , 0 , 2 , 0 , nil) ≡ (1 , 2 , nil) -- chamar a funcao
  testNonZeros = refl
 
  ------------------------------------------------------------------------------------------------------
  
  -- Exercise 3.3
  ------------------------------------------------------------------------------------------------------

  --if_than_else_ : ∀ {A : Set} → Bool → A → A → A
  --if True  than a else _ = a
  --if False than _ else a = a
 
  oddMembers : NList → NList
  oddMembers nil      = nil
  oddMembers (n , xs) with oddb n
  ...| True  = n , oddMembers xs
  ...| False = oddMembers xs
  --oddMembers (n , xs) = if (oddb n) than (n , oddMembers xs) else oddMembers xs
  
  
  testOddMembers : oddMembers (1 , 2 , 3 , 4 , nil) ≡ (1 , 3 , nil)
  testOddMembers = refl

  ------------------------------------------------------------------------------------------------------

  -- Exercise 3.4
  ------------------------------------------------------------------------------------------------------
 
  alternative : NList → NList → NList -- nao entendi o que tem que fazer
  alternative nil xs      = xs
  alternative (x , xs) ys = x , alternative ys xs

  ------------------------------------------------------------------------------------------------------

  -- 3.3  Bag via Lists
  ------------------------------------------------------------------------------------------------------
