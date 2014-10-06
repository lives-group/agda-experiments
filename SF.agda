

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

infixr 1 _≡⟨_⟩_

_≡⟨_⟩_ : ∀ {l}{A : Set l}(x : A) {y z} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ xy ⟩ yz = trans xy yz

infixr 1 _∎

_∎ : ∀ {l}{A : Set l}(x : A) → x ≡ x
x ∎ = refl

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

  {-# BUILTIN NATURAL ℕ #-} 
       
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
  bleNat zero    _       = True
  bleNat (suc _) zero    = False
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
  evenOddSucN (suc (suc n)) = evenOddSucN n


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
  multPlusDistrR n m zero rewrite mult0R (n + m) | mult0R n | mult0R m =  refl
  multPlusDistrR n m (suc p) rewrite multComm n (suc p) | multComm m (suc p) = trans (multComm (n + m) (suc p)) {!!} 

  multAssoc : ∀ (n m p : ℕ) → n × (m × p) ≡ (n × m) × p
  multAssoc zero    m p = refl
  multAssoc (suc n) zero p = multAssoc n zero p
  multAssoc (suc n) (suc m) p = {!!}

  beqNatRefl : ∀ (n : ℕ) → True ≡ beqNat n n
  beqNatRefl zero    = refl
  beqNatRefl (suc n) = beqNatRefl n

open Induction public

  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  
  -- Chapter 3
  --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

module Lists where

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

  testNonZeros : nonZeros ( 0 , 1 , 0 , 2 , 0 , nil) ≡ (1 , 2 , nil)
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
 
  alternative : NList → NList → NList
  alternative nil      ys = ys
  alternative (x , xs) ys = x , alternative ys xs

  ------------------------------------------------------------------------------------------------------

  -- 3.3  Bag via Lists
  ------------------------------------------------------------------------------------------------------

  Bag : Set
  Bag = NList

  -- ⇒ Exercise 3.5
  ---

  count : ℕ → NList → ℕ
  count _ nil = zero
  count x (y , ys) with (beqNat x y)
  ...| True  = suc (count x ys)
  ...| False = count x ys 
  --count x (y , ys) = if (x ≡ y) than suc (count x ys) else (count x ys)
  
  testCount1 : count 1 (1 , 2 , 1 , nil) ≡ 2
  testCount1 = refl
  
  testCount2 : count 3 (1 , 2 , 1 , nil) ≡ 0
  testCount2 = refl
  
  sum : Bag → ℕ
  sum nil = zero
  sum (x , xs) = x + (sum xs)
  
  testSum : sum (1 , 2 , 1 , nil) ≡ 4
  testSum = refl

  add : ℕ → Bag → Bag
  add x ys = (x , ys)

  testAdd : count 1 (add 1 (1 , 2 , 1 , nil)) ≡ 3
  testAdd = refl

  member : ℕ → Bag → Bool
  member _ nil = False
  member x (y , ys) with (beqNat x y)
  ...| True  = True
  ...| False = member x ys
  
  testMember1 : member 1 (1 , 2 , 1 , nil) ≡ True
  testMember1 = refl

  testMember2 : member 3 (1 , 2 , 1 , nil) ≡ False
  testMember2 = refl

  -- ⇒ Exercise 3.6
  ----

  removeOne : ℕ → Bag → Bag
  removeOne _ nil = nil
  removeOne x (y , ys) with (beqNat x y)
  ...| True  = ys
  ...| False = y , removeOne x ys

  testRemoveOne1 : count 1 (removeOne 1 (1 , 2 , 1 , nil)) ≡ 1 
  testRemoveOne1 = refl

  testRemoveOne2 : count 1 (removeOne 2 (1 , 2 , 1 , nil)) ≡ 2 
  testRemoveOne2 = refl

  removeAll : ℕ → Bag → Bag
  removeAll _ nil = nil
  removeAll x (y , ys) with (beqNat x y)
  ...| True  = removeAll x ys
  ...| False = y , removeAll x ys

  testRemoveAll : count 1 (removeAll 1 (1 , 2 , 1 , nil)) ≡ 0
  testRemoveAll = refl

  contem : ℕ → Bag → Bool
  contem _ nil = False
  contem x (y , ys) with (beqNat x y)
  ...| True  = True
  ...| False = contem x ys

  subset : Bag → Bag → Bool
  subset nil _   = True
  subset (x , xs) ys = (contem x ys) ∧ subset xs ys

  testSubset1 : subset (1 , 2 , nil) (1 , 2 , 1 , nil) ≡ True
  testSubset1 = refl
  
  testSubset2 : subset (2 , 3 , nil) (1 , 2 , 4 , nil) ≡ False
  testSubset2 = refl

  testSubsetA : subset (2 , 3 , nil) ( 3 , 2 , 1 , nil) ≡ True
  testSubsetA = refl
  
  testSubset3 : subset (1 , 1 , nil) (1 , 2 , 1 , nil) ≡ True
  testSubset3 = refl

  ------------------------------------------------------------------------------------------------------
  
  -- ⇒ Exercise 3.7 --> Nao entendi o que tem que fazer
  ------------------------------------------------------------------------------------------------------

  -- 3.4  Reasoning about Lists
  ------------------------------------------------------------------------------------------------------
  
  nilAppL : ∀ (n : NList) → nil ++ n ≡ n
  nilAppL n = refl

  tailLengthPred : ∀ (n : NList) → pred (length n) ≡ length (tail n)
  tailLengthPred nil     = refl
  tailLengthPred (x , n) = refl
  
  appAssoc : ∀ (l1 l2 l3 : NList) → l1 ++ (l2 ++ l3) ≡ (l1 ++ l2) ++ l3
  appAssoc nil      l2 l3 = refl
  appAssoc (x , l1) l2 l3 =                                              --trans refl (cong (λ p → x , p) (appAssoc l1 l2 l3)) 
    ((x , l1) ++ l2 ++ l3)   ≡⟨ refl ⟩
    (x , (l1 ++ (l2 ++ l3))) ≡⟨ cong (λ p → x , p) (appAssoc l1 l2 l3) ⟩ 
    (x , ((l1 ++ l2) ++ l3))
    ∎

  appLength : ∀ (n m : NList) → length (n ++ m) ≡ length n + length m
  appLength nil      m = refl
  appLength (x , xs) m =                                                 --cong suc (appLength xs m)
    length ((x , xs) ++ m)     ≡⟨ refl ⟩ 
    length (x , (xs ++ m))     ≡⟨ refl ⟩
    suc (length (xs ++ m))     ≡⟨ cong suc (appLength xs m) ⟩
    suc (length xs + length m) ≡⟨ refl ⟩ 
    length (x , xs) + length m
    ∎ 
    

  -- ⇒ Exercise 3.8
  ------------------------------------------------------------------------------------------------------
  
  snoc : ℕ → NList → NList
  snoc n nil      = n , nil
  snoc n (x , xs) = x , snoc n xs

  rev : NList → NList
  rev nil      = nil
  rev (x , xs) = snoc x (rev xs)

  lengthSnoc : ∀ (n : ℕ)(l : NList) → length (snoc n l) ≡ suc (length l)
  lengthSnoc n nil      = refl
  lengthSnoc n (x , xs) = 
    length (snoc n (x , xs)) ≡⟨ refl ⟩
    length (x , (snoc n xs)) ≡⟨ refl ⟩
    suc (length (snoc n xs)) ≡⟨ cong suc (lengthSnoc n xs) ⟩
    suc (length (x , xs))
    ∎

  revLength : ∀ (n : NList) → length (rev n) ≡ length n
  revLength nil      = refl
  revLength (x , xs) = 
    length (rev (x , xs))    ≡⟨ refl ⟩
    length (snoc x (rev xs)) ≡⟨ lengthSnoc x (rev xs) ⟩
    suc (length (rev xs))    ≡⟨ cong suc (revLength xs) ⟩
    suc (length xs)          ≡⟨ refl ⟩ 
    length (x , xs) 
    ∎

  -- 3.4.3  List Exercise, part 1

  appNilEnd : ∀ (l : NList) → l ++ nil ≡ l
  appNilEnd nil     = refl
  appNilEnd (x , l) = 
    (x , l) ++ nil   ≡⟨ refl ⟩
    (x , (l ++ nil)) ≡⟨ cong (λ a → x , a ) (appNilEnd l) ⟩
    (x , l)
    ∎

  appAss : ∀ (l1 l2 l3 l4 : NList) → l1 ++ (l2 ++ (l3 ++ l4)) ≡ ((l1 ++ l2) ++ l3) ++ l4
  appAss nil l2 l3 l4 = appAssoc l2 l3 l4
  appAss (x , l1) l2 l3 l4 = 
    (x , l1) ++ (l2 ++ (l3 ++ l4)) ≡⟨ refl ⟩
    (x , l1 ++ (l2 ++ (l3 ++ l4))) ≡⟨ cong (λ a → x , a) (appAss l1 l2 l3 l4) ⟩
    (x , ((l1 ++ l2) ++ l3) ++ l4)
    ∎

  snocApp : ∀ (n : ℕ)(l : NList) → snoc n l ≡ l ++ (n , nil) 
  snocApp n nil     = refl
  snocApp n (x , l) = 
    snoc n (x , l)     ≡⟨ refl ⟩ 
    (x , snoc n l)     ≡⟨ cong (λ a → x , a) (snocApp n l) ⟩ 
    (x , l ++ n , nil)
    ∎

  distRev : ∀ (l1 l2 : NList) → rev (l1 ++ l2) ≡ (rev l2) ++ (rev l1)
  distRev nil      l2 = sym (appNilEnd (rev l2))
  distRev (x , l1) l2 = 
    rev ((x , l1) ++ l2)            ≡⟨ refl ⟩
    snoc x (rev (l1 ++ l2))         ≡⟨ snocApp x (rev (l1 ++ l2)) ⟩ 
    (rev (l1 ++ l2) ++ x , nil)     ≡⟨ cong (λ a → (a ++ x , nil)) (distRev l1 l2) ⟩
    ((rev l2 ++ rev l1) ++ x , nil) ≡⟨ sym (appAssoc (rev l2) (rev l1) (x , nil)) ⟩ 
    rev l2 ++ rev l1 ++ x , nil     ≡⟨ cong (λ a → rev l2 ++ a) (sym (snocApp x (rev l1))) ⟩
    rev l2 ++ snoc x (rev l1)
    ∎

  revInjective : ∀ (l1 l2 : NList) → rev l1 ≡ rev l2 → l1 ≡ l2
  revInjective nil      nil      refl = refl
  revInjective _        nil      ()
  revInjective nil      _        ()
  revInjective (x , l1) (y , l2) prf with beqNat x y
  ...| True  = {!!}
  ...| False = {!!}

  revInvolutive : ∀ (l : NList) → rev (rev l) ≡ l
  revInvolutive nil     = refl
  revInvolutive (x , l) =
    rev (rev (x , l))            ≡⟨ refl ⟩
    rev (snoc x (rev l))         ≡⟨ cong (λ a → rev a) (snocApp x (rev l)) ⟩
    rev (rev l ++ x , nil)       ≡⟨ distRev (rev l) (x , nil) ⟩ 
    rev (x , nil) ++ rev (rev l) ≡⟨ refl ⟩
    (x , nil) ++ rev (rev l)     ≡⟨ refl ⟩
    (x , rev (rev l))            ≡⟨ cong (λ a → x , a) (revInvolutive l) ⟩ 
    (x , l) 
    ∎
 
  ------------------------------------------------------------------------------------------------------
  
  --3.5  Maybe
  ------------------------------------------------------------------------------------------------------
  
  data NMaybe : Set where
    Just    : ℕ → NMaybe
    Nothing : NMaybe

  indexBad : ℕ → NList → ℕ
  indexBad _       nil      = 42 --arbitrary
  indexBad zero    (x , xs) = x
  indexBad (suc n) (x , xs) = indexBad n xs

  index : ℕ → NList → NMaybe
  index _       nil      = Nothing
  index zero    (x , xs) = Just x
  index (suc n) (x , xs) = index n xs

  headM : NList → NMaybe
  headM nil      = Nothing
  headM (x , xs) = Just x

  beqNList : NList → NList → Bool
  beqNList nil      nil      = True
  beqNList _        nil      = False
  beqNList nil      _        = False
  beqNList (x , xs) (y , ys) with beqNat x y
  ...| True  = beqNList xs ys
  ...| False = False

  beqNListRefl : ∀ (l : NList) → beqNList l l ≡ True
  beqNListRefl nil     = refl
  beqNListRefl (x , l) with beqNat x x
  ...| True  = beqNListRefl l 
  ...| False = {!!}

--open Lists public

module Polymorphism where

  data BList : Set where
    nil  : BList
    cons : Bool → BList → BList

  data List {l}(A : Set l) : Set l where
    nil : List A
    _,_ : A → List A → List A

  lengthA : (A : Set) → List A → ℕ
  lengthA A nil      = zero
  lengthA A (_ , xs) = suc (lengthA A xs)

  testLengthBool : lengthA Bool (nil) ≡ 0
  testLengthBool = refl

  test1LengthBool : lengthA ℕ (zero , nil) ≡ 1
  test1LengthBool = refl

  test3LengthBool : lengthA Bool (True , nil) ≡ 1
  test3LengthBool = refl

  test4LengthBool : lengthA Bool (False , (True , nil)) ≡ 2 -- Olhar com o Rodrigo
  test4LengthBool = refl

  _⟨+⟩_ : (A : Set) → List A → List A → List A
  _⟨+⟩_ A nil      ys = ys
  _⟨+⟩_ A (x , xs) ys = x , (_⟨+⟩_ A xs ys)

  snocL : (A : Set) → A → List A → List A
  snocL A x nil      = x , nil
  snocL A x (y , ys) = y , (snocL A x ys)

  revL : (A : Set) → List A → List A
  revL A nil      = nil
  revL A (x , xs) = snocL A x (revL A xs) 

  -- 
  Age = ℕ
  
  --appL A nil      ys = ys
  --appL A (x , xs) ys = x , (appL A xs ys)

  --

  length : {A : Set} → List A → ℕ
  length {A} nil      = zero
  length {A} (_ , xs) = suc (length {A} xs)

  -- 4.1.5  Exercices: Polymorphic List

  repeat : {A : Set}(n : A)(count : ℕ) → List A
  repeat {A} _ zero        = nil
  repeat {A} n (suc count) = n , (repeat {A} n count)

  testRepeat : repeat True 2 ≡ True , (True , nil)
  testRepeat = refl
 
  _⟨++⟩_ : {A : Set} → List A → List A → List A
  nil      ⟨++⟩ ys = ys
  (x , xs) ⟨++⟩ ys = x , ( xs ⟨++⟩ ys)

  snoc : {A : Set} → A → List A → List A
  snoc x nil      = x , nil
  snoc x (y , ys) = y , (snoc x ys)

  rev : {A : Set} → List A → List A
  rev nil      = nil
  rev (x , xs) = snoc x (rev xs) 

  appAssoc : ∀ {A : Set}(l1 l2 l3 : List A) → l1 ⟨++⟩ (l2 ⟨++⟩ l3) ≡ (l1 ⟨++⟩ l2) ⟨++⟩ l3
  appAssoc nil      l2 l3 = refl
  appAssoc (x , l1) l2 l3 = 
    (x , l1) ⟨++⟩ (l2 ⟨++⟩ l3) ≡⟨ refl ⟩
    x , (l1 ⟨++⟩ (l2 ⟨++⟩ l3)) ≡⟨ cong (λ a → x , a) (appAssoc l1 l2 l3) ⟩
    x , ((l1 ⟨++⟩ l2) ⟨++⟩ l3) 
    ∎

  nilApp : ∀ {A : Set}(l : List A) → nil ⟨++⟩ l ≡ l -- Olhar com o Rodrigo
  nilApp {A} l = refl
  
  nilApp2 : ∀ {A : Set}(l : List A) → l ⟨++⟩ nil ≡ l -- Olhar com o Rodrigo
  nilApp2 nil     = refl
  nilApp2 (x , l) = 
    (x , l) ⟨++⟩ nil ≡⟨ refl ⟩
    x ,(l ⟨++⟩ nil)  ≡⟨ cong (λ a → x , a) (nilApp2 l) ⟩ 
    x , l
    ∎

  revSnoc : ∀ {A : Set}(v : A)(s : List A) → rev (snoc v s) ≡ v , (rev s)
  revSnoc v nil     = refl
  revSnoc v (x , s) = 
    rev (snoc v (x , s))    ≡⟨ refl ⟩
    snoc x (rev (snoc v s)) ≡⟨ cong (λ a → snoc x a) (revSnoc v s) ⟩ 
    snoc x (v , rev s)      ≡⟨ refl ⟩
    v , snoc x (rev s)      ≡⟨ refl ⟩
    v , (rev (x , s))
    ∎
 
  snocApp : ∀ {A : Set}(n : A)(l : List A) → snoc n l ≡ l ⟨++⟩ (n , nil)
  snocApp n nil     = refl
  snocApp n (x , l) = 
    snoc n (x , l)        ≡⟨ refl ⟩
    x , snoc n l          ≡⟨ cong (λ a → x , a) (snocApp n l) ⟩
    x , (l ⟨++⟩ (n , nil)) ≡⟨ refl ⟩ 
    (x , l) ⟨++⟩ (n , nil)
    ∎

  distRev : ∀ {A : Set}(l1 l2 : List A) → rev (l1 ⟨++⟩ l2) ≡ (rev l2) ⟨++⟩ (rev l1)
  distRev nil      l2 = sym (nilApp2 (rev l2))
  distRev (x , l1) l2 = 
    rev ((x , l1) ⟨++⟩ l2)             ≡⟨ refl ⟩
    snoc x (rev (l1 ⟨++⟩ l2))          ≡⟨ cong (λ a → snoc x a) (distRev l1 l2) ⟩
    snoc x (rev l2 ⟨++⟩ rev l1)        ≡⟨ snocApp x (rev l2 ⟨++⟩ rev l1) ⟩
    (rev l2 ⟨++⟩ rev l1) ⟨++⟩ (x , nil) ≡⟨ sym (appAssoc (rev l2) (rev l1) (x , nil)) ⟩ 
    rev l2 ⟨++⟩ (rev l1 ⟨++⟩ (x , nil)) ≡⟨ cong (λ a → rev l2 ⟨++⟩ a) (sym (snocApp x (rev l1))) ⟩
    rev l2 ⟨++⟩ rev (x , l1)
    ∎

  revInvolutive : ∀ {A : Set}(l : List A) → rev (rev l) ≡ l
  revInvolutive nil     = refl
  revInvolutive (x , l) = 
    rev (rev (x , l))             ≡⟨ refl ⟩
    rev (snoc x (rev l))          ≡⟨ cong (λ a → rev a) (snocApp x (rev l)) ⟩
    rev (rev l ⟨++⟩ (x , nil))     ≡⟨ distRev (rev l) (x , nil) ⟩
    rev (x , nil) ⟨++⟩ rev (rev l) ≡⟨ refl ⟩
    (x , nil) ⟨++⟩ rev (rev l)     ≡⟨ refl ⟩
    x , rev (rev l)               ≡⟨ cong (λ a → x , a) (revInvolutive l) ⟩
    x , l
    ∎

  snocWithApp : {A : Set}(x : A)(l1 l2 : List A) → snoc x (l1 ⟨++⟩ l2) ≡ l1 ⟨++⟩ (snoc x l2)
  snocWithApp x nil      l2 = refl
  snocWithApp x (y , l1) l2 = 
    snoc x ((y , l1) ⟨++⟩ l2) ≡⟨ refl ⟩
    y , snoc x (l1 ⟨++⟩ l2)   ≡⟨ cong (λ a → y , a) (snocWithApp x l1 l2) ⟩
    y , (l1 ⟨++⟩ snoc x l2)
    ∎ 
 

  -- 4.1.6  Polymorphic Pairs

  data _X_ (A B : Set) : Set where
    _,_ : A → B → A X B

  fst : {A B : Set} → A X B → A
  fst (x , _) = x
  
  snd : {A B : Set} → A X B → B
  snd (_ , x) = x

  zip : {A B : Set} → List A → List B → List (A X B)
  zip nil      _        = nil
  zip _        nil      = nil
  zip (x , xs) (y , ys) = (x , y) , zip xs ys

  -- Exercise 4.1

  unzip : {A B : Set} → List (A X B) → (List A X List B)
  unzip nil     = nil , nil
  unzip ((x , y) , a) = (x , fst z) , (y , snd z) where
    z = unzip a

  -- 4.1.7  Polymorphic Maybe

  data Maybe (A : Set) : Set where
    Just    : A → Maybe A
    Nothing : Maybe A

  index : {A : Set} → ℕ → List A → Maybe A
  index n       nil      = Nothing
  index zero    (x , _)  = Just x
  index (suc n) (_ , xs) = index n xs

  -- 4.2.1  High-Order Functions

  dolt3Times : {A : Set} → (A → A) → A → A
  dolt3Times f x = f (f (f x))

  -- 4.2.2  Partial Application
  
  --+ : ℕ → ℕ → ℕ
  
  plus3 : ℕ → ℕ
  plus3 = _+_ 3

  testPlus3 : plus3 4 ≡ 7
  testPlus3 = refl

  -- 4.2.3  Digression: Currying
  
  curry : {A B C : Set} → (A → B → C) → A X B → C
  curry f (x , y) = f x y
  
  uncurry : {A B C : Set} → (A X B → C) → A → B → C
  uncurry f x y = f (x , y)
    
  -- Exercise 4.2

  uncurryCurry : ∀ {A B C : Set}(f : A X B → C)(p : A X B) → curry (uncurry f) p ≡ f p 
  uncurryCurry f p = {!!}

  curryUncurry : ∀ {A B C : Set}(f : A → B → C)(x : A)(y : B) → uncurry (curry f) x y ≡ f x y
  curryUncurry f x y = {!!}

  -- 4.2.4  Filter
  
  filter  : {A : Set} → (A → Bool) → List A → List A
  filter p nil      = nil
  filter p (x , xs) with p x
  filter p (x , xs) | True  = x , filter p xs
  filter p (x , xs) | False = filter p xs

  testFilterEven : filter evenb (1 , (2 , (0 , (3 , nil)))) ≡ (2 , (0 , nil))
  testFilterEven = refl
  
  countOddMembers : List ℕ → ℕ
  countOddMembers l = length (filter oddb l)

  testCountOddMembers : countOddMembers (1 , (2 , (3 , nil))) ≡ 2
  testCountOddMembers = refl

  -- 4.2.5 
    
  lengthls1 : {A : Set} → List A → Bool
  lengthls1 l = beqNat (length l) 1
  
  testFilter : filter lengthls1 ((1 , (2 , nil)) , ((1 , nil) , nil)) ≡ ((1 , nil) , nil)
  testFilter = refl

  testAnonymous : (dolt3Times {ℕ} (λ x → x + x) 2) ≡ 16
  testAnonymous = refl

  testFilter2 : filter (λ x → beqNat (length x) 1) ((1 , (2 , nil)) , ((1 , nil) , nil)) ≡ ((1 , nil) , nil)
  testFilter2 = refl

  -- Exercise 4.3 
  
  filterEven7 : List ℕ → List ℕ
  filterEven7 l = filter (bleNat 7) (filter evenb l)

  testFilterEven7 : filterEven7 (10 , ( 8 , (9 , (4 , (3 , nil))))) ≡ (10 , (8 , nil))
  testFilterEven7 = refl

  -- Exercise 4.4
  
  partition : {A : Set} → (A → Bool) → List A → (List A X List A)
  partition p l = {!!}
  
  -- 4.2.6  Map

  map : {A B : Set} → (A → B) → List A → List B
  map _ nil      = nil
  map f (x , xs) = f x , map f xs

  testMap : map plus3 (1 , (2 , nil)) ≡ (4 , (5 , nil))
  testMap = refl

  testMap1 : map evenb (1 , (2 , (3 , nil))) ≡ (False , (True , (False , nil)))
  testMap1 = refl

  -- Exercise 4.5
  
  distMap : ∀ {A B : Set}(f : A → B)(l1 l2 : List A) → map f (l1 ⟨++⟩ l2) ≡ map f l1 ⟨++⟩ map f l2
  distMap f nil      l2 = refl
  distMap f (x , l1) l2 = 
    map f ((x , l1) ⟨++⟩ l2) ≡⟨ refl ⟩
    f x , map f (l1 ⟨++⟩ l2) ≡⟨ cong (λ a → f x , a) (distMap f l1 l2) ⟩
    f x , ((map f l1) ⟨++⟩ (map f l2))
    ∎

  mapRevComm : ∀ {A B : Set}(f : A → B)(l : List A) → map f (rev l) ≡ rev (map f l)
  mapRevComm f nil     = refl
  mapRevComm f (x , l) = 
    map f (rev (x , l))            ≡⟨ refl ⟩
    map f (snoc x (rev l))         ≡⟨ cong (λ a → map f a) (snocApp x (rev l)) ⟩
    map f (rev l ⟨++⟩ (x , nil))   ≡⟨ distMap f (rev l) (x , nil) ⟩
    map f (rev l) ⟨++⟩ (f x , nil) ≡⟨ sym (snocApp (f x) (map f (rev l))) ⟩
    snoc (f x) (map f (rev l))     ≡⟨ cong (λ a → snoc (f x) a) (mapRevComm f l) ⟩
    snoc (f x) (rev (map f l))     ≡⟨ refl ⟩
    rev (map f (x , l))
    ∎ 

  -- Exercise 4.6 -- Arrumar no PDF

  concatMap : {A B : Set} →  (A → List B) →  List A → List B
  concatMap f nil     = nil
  concatMap f (x , l) = f x ⟨++⟩ (concatMap f l)

  testConcatMap : concatMap (λ n → (n , (n + 1 , (n + 2 , nil)))) (1 , (5 , (10 , nil))) ≡ (1 , (2 , (3 , (5 , (6 , (7 , (10 , (11 , (12 , nil)))))))))
  testConcatMap = refl

  mapMaybe : {A B : Set} → (A → B) → Maybe A → Maybe B
  mapMaybe f (Just x) = Just (f x)
  mapMaybe f Nothing  = Nothing

  -- 4.2.7  Fold

  fold : {A B : Set} → (A → B → B) → B → List A → B
  fold f v nil = v
  fold f v (x , xs) = f x (fold f v xs)

  testFold : fold _+_ 0 (1 , (2 , (3 , (4 , nil)))) ≡ 10
  testFold = refl

  -- 4.2.8  Functions for Constructing Fuctions

  constFun : {A : Set} → A → ℕ → A
  constFun x n = x
  
  ftrue : ℕ → Bool
  ftrue = constFun True
  
  testFtrue1 : ftrue 0 ≡ True
  testFtrue1 = refl
  
  override : {A : Set} → (ℕ → A) → ℕ → A → ℕ → A
  override f x a y with beqNat x y
  ...| True  = a
  ...| False = f y
  
  fMostlyTrue : ℕ → Bool
  fMostlyTrue = override (override ftrue 1 False) 3 False
  
  testFMostlyTrue1 : fMostlyTrue 0 ≡ True
  testFMostlyTrue1 = refl
  
  testFMostlyTrue2 : fMostlyTrue 1 ≡ False
  testFMostlyTrue2 = refl

  -- Exercise 4.7
  
  overrideExample : ∀ (b : Bool) → (override (constFun b) 3 True) 2 ≡ b
  overrideExample True  = {!!}
  overrideExample False = {!!}

  -- 4.3   Additional Exercices
  
  -- Exercise 4.8
  
  foldLength : ∀ {A : Set} → List A → ℕ
  foldLength = fold (λ _ a → suc a) 0

  theoremLength : ∀ {A : Set}(l : List A) → length l ≡ foldLength l
  theoremLength nil     = refl
  theoremLength (x , l) = 
    length (x , l)     ≡⟨ refl ⟩
    suc (length l)     ≡⟨ cong suc (theoremLength l) ⟩
    suc (foldLength l)
    ∎

  --mapFold : {A B : Set} → (A → B) → List A → List B
  --mapFold f l = fold (λ x y → f x , y) nil l

  foldMap : {A B : Set}(f : A → B)(l : List A) → map f l ≡ fold (λ a b → f a , b) nil l
  foldMap f nil     = refl
  foldMap f (x , l) = 
    map f (x , l)                      ≡⟨ refl ⟩
    f x , map f l                      ≡⟨ cong (λ a → f x , a) (foldMap f l) ⟩
    f x , fold (λ a b → f a , b) nil l ≡⟨ refl ⟩
    fold (λ a b → f a , b) nil (x , l)
    ∎

open Polymorphism public

module MoreAgda where

  Eq : {l : Level}(A : Set l) → A → A → Set l
  Eq {l} A x y = _≡_ {l} {A} x y
  
  NListEq : List ℕ → List ℕ → Set
  NListEq l1 l2 = Eq (List ℕ) l1 l2

  Silly : (n m o p : ℕ) → Set
  Silly n m o p = n ≡ m → t1 → t2
    where
      t1 = NListEq (n , (o , nil)) (n , (p , nil))
      t2 = NListEq (n , (o , nil)) (m , (p , nil))
  
  id : Set → Set
  id x = x → x

  silly1 : ∀ (n m o p : ℕ) → Silly m o n p -- Perguntar o Rodrigo (nao foi feito o id)
  silly1 m n o p nm rewrite nm = λ x → x --id

  Hyp : ℕ → ℕ → Set
  Hyp o p = ∀ (q r : ℕ) → q ≡ r → t q r
    where
      t : ℕ → ℕ → Set
      t q r = NListEq (q , (o , nil)) (r , (p , nil))

  Silly2 : (m n o p : ℕ) → Set
  Silly2 m n o p = n ≡ m → Hyp o p → t
    where
      t = NListEq (n , (o , nil)) (m , (p , nil))


  silly2 : ∀ (m n o p : ℕ) → Silly2 m n o p
  silly2 m n o p nm hyp = hyp n m nm

  NPairEq : (m n o p : ℕ) → Set
  NPairEq m n o p = Eq (ℕ X ℕ) (m , n) (o , p)
  
  Hyp2a : Set
  Hyp2a = ∀ (q r : ℕ) → NPairEq q q r r → NListEq (q , nil) (r , nil)
  
  Silly2a : ℕ → ℕ → Set
  Silly2a n m = NPairEq n n m m → Hyp2a → NListEq (n , nil) (m , nil)
  
  silly2a : ∀ (n m : ℕ) → Silly2a n m
  silly2a .m m refl hyp = refl
  
  SillyEx : Set
  SillyEx = ∀ (n : ℕ) → evenb n ≡ True → oddb (suc n) ≡ True
  
  sillyEx : SillyEx → evenb 3 ≡ True → oddb 4 ≡ True
  sillyEx silly = silly (suc (suc (suc zero)))

  silly3 : ∀ (n : ℕ) → True ≡ beqNat n 5 → beqNat (suc (suc n)) 7 ≡ True
  silly3 n = sym
  
  revExercice1 : ∀ (l1 l2 : List ℕ) → l1 ≡ rev l2 → l2 ≡ rev l1
  revExercice1 nil      l2 prf = {!!}
  revExercice1 (x , l1) l2 prf = {!!}
