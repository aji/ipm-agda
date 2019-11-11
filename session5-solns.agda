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

postulate
  TND : {X : Set} → X ∨ (X → ⊥)

-- helper for branching on TND
infix 1 TNDʸ→_ⁿ→_
TNDʸ→_ⁿ→_ : {X Y : Set} → (X → Y) → ((X → ⊥) → Y) → Y
TNDʸ→_ⁿ→_ {X} {Y} f g = h TND
  where h : X ∨ (X → ⊥) → Y
        h (x ←or    ) = f  x
        h (   or→ ¬x) = g ¬x

module _ {A B C : Set} where
  p1 : A ∨ (A → ⊥)
  p1 = TND

  p2 : ((B → ⊥) → (A → ⊥)) → (A → B)
  p2 f = TNDʸ→ (λ  b → λ a → b)
            ⁿ→ (λ ¬b → λ a → let ¬a = f ¬b in a ↯ ¬a)

  p3 : (A ∧ B → ⊥) → (A → ⊥) ∨ (B → ⊥)
  p3 f = TNDʸ→ (λ  a →     or→ λ b → f (a and b))
            ⁿ→ (λ ¬a → ¬a ←or)

  p4 : ((A → ⊥) → ⊥) → A
  p4 ¬¬a = TNDʸ→ (λ  a → a)
              ⁿ→ (λ ¬a → ¬a ↯ ¬¬a)

  p5 : (A → B) → (A → ⊥) ∨ B
  p5 f = TNDʸ→ (λ  a →     or→ f a)
            ⁿ→ (λ ¬a → ¬a ←or)

  p6 : (A → B) → (B → C) → (A → ⊥) ∨ C
  p6 f g = TNDʸ→ (λ  a →     or→ g (f a))
              ⁿ→ (λ ¬a → ¬a ←or)

  p7 : (((A → B) → A) → A)
  p7 = TNDʸ→ (λ  a → λ _ → a)
          ⁿ→ (λ ¬a → λ f → f (λ a → a ↯ ¬a))

  p8 : (A ∧ B ∧ C → ⊥) → (A → ⊥) ∨ (B → ⊥) ∨ (C → ⊥)
  p8 ¬abc = let ¬c a b = λ c → a and b and c ↯ ¬abc
            in TNDʸ→ (λ  a → TNDʸ→ (λ  b →             or→ ¬c a b)
                                ⁿ→ (λ ¬b →     or→ ¬b ←or))
                  ⁿ→ (λ ¬a →               ¬a ←or     ←or)

  p9 : ((A → B) → ⊥) → A ∧ (B → ⊥)
  p9 ¬a→b = let a = TNDʸ→ (λ  a → a)
                       ⁿ→ (λ ¬a → (λ a → a ↯ ¬a) ↯ ¬a→b)
                ¬b = λ b → (λ _ → b) ↯ ¬a→b
            in a and ¬b
