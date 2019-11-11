-- This file contains Agda versions of proofs from Session 4 of the
-- Incredible Proof Machine http://incredible.pm/

infixl 20 _∧_
infixl 20 _and_
data _∧_ (A : Set) (B : Set) : Set where
  _and_ : A → B → A ∧ B

infixl 19 _∨_
infix 19 or→_
infix 18 _←or
data _∨_ (A : Set) (B : Set) : Set where
  _←or : A → A ∨ B
  or→_ : B → A ∨ B

data ⊥ : Set where

empty : {X : Set} → ⊥ → X
empty ()

-- more convenient syntax for representing a contradiction
infix 2 _↯_
_↯_ : {X Y : Set} → X → (X → ⊥) → Y
x ↯ ¬x = empty (¬x x)

-- the standard formulation of TND. needs to be postulated in Agda.
postulate
  TND₀ : {X : Set} → X ∨ (X → ⊥)

-- helper syntax for dealing with TND₀
data TND-case (X : Set) : Set where
  ʸ : X → TND-case X
  ⁿ : (X → ⊥) → TND-case X
TND : {X Y : Set} → (TND-case X → Y) → Y
TND {X} {Y} f = g TND₀
  where g : X ∨ (X → ⊥) → Y
        g (x ←or    ) = f (ʸ  x)
        g (   or→ ¬x) = f (ⁿ ¬x)

module _ {A B C : Set} where
  p1 : A ∨ (A → ⊥)
  p1 = TND₀

  p1′ : A ∨ (A → ⊥)
  p1′ = TND λ where
    (ʸ  a) →  a ←or
    (ⁿ ¬a) →     or→ ¬a

  p2 : ((B → ⊥) → (A → ⊥)) → (A → B)
  p2 f = TND λ where
    (ʸ  b) → λ a → b
    (ⁿ ¬b) → λ a → let ¬a = f ¬b in a ↯ ¬a

  p3 : (A ∧ B → ⊥) → (A → ⊥) ∨ (B → ⊥)
  p3 f = TND λ where
    (ʸ  a) →     or→ λ b → f (a and b)
    (ⁿ ¬a) → ¬a ←or

  p4 : ((A → ⊥) → ⊥) → A
  p4 ¬¬a = TND λ where
    (ʸ  a) → a
    (ⁿ ¬a) → ¬a ↯ ¬¬a

  p5 : (A → B) → (A → ⊥) ∨ B
  p5 f = TND λ where
    (ʸ  a) →     or→ f a
    (ⁿ ¬a) → ¬a ←or

  p6 : (A → B) → (B → C) → (A → ⊥) ∨ C
  p6 f g = TND λ where
    (ʸ  a) →     or→ g (f a)
    (ⁿ ¬a) → ¬a ←or

  p7 : (((A → B) → A) → A)
  p7 = TND λ where
    (ʸ  a) → λ _ → a
    (ⁿ ¬a) → λ f → f (λ a → a ↯ ¬a)

  p8 : (A ∧ B ∧ C → ⊥) → (A → ⊥) ∨ (B → ⊥) ∨ (C → ⊥)
  p8 ¬abc = TND λ where
      (ʸ  a) → TND λ where
        (ʸ  b) → let ¬c = λ c → a and b and c ↯ ¬abc
                 in (            or→ ¬c)
        (ⁿ ¬b) →    (    or→ ¬b ←or    )
      (ⁿ ¬a) →      (¬a ←or     ←or    )

  p9 : ((A → B) → ⊥) → A ∧ (B → ⊥)
  p9 ¬a→b = let a = TND λ where
                      (ʸ  a) → a
                      (ⁿ ¬a) → (λ a → a ↯ ¬a) ↯ ¬a→b
                ¬b = λ b → (λ _ → b) ↯ ¬a→b
            in a and ¬b
