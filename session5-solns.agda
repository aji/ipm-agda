-- This file contains Agda versions of proofs from Session 4 of the
-- Incredible Proof Machine http://incredible.pm/

data _∧_ (A : Set) (B : Set) : Set where
  _and_ : A → B → A ∧ B

data _∨_ (A : Set) (B : Set) : Set where
  _←or : A → A ∨ B
  or→_ : B → A ∨ B

data ⊥ : Set where

empty : {X : Set} → ⊥ → X
empty ()

postulate
  TND : {X : Set} → X ∨ (X → ⊥)

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
            ⁿ→ (λ ¬b → λ a → empty ((f ¬b) a))

  p3 : (A ∧ B → ⊥) → (A → ⊥) ∨ (B → ⊥)
  p3 f = TNDʸ→ (λ  a →     or→ λ b → f (a and b))
            ⁿ→ (λ ¬a → ¬a ←or)

  p4 : ((A → ⊥) → ⊥) → A
  p4 f = TNDʸ→ (λ  a → a)
            ⁿ→ (λ ¬a → empty (f ¬a))

  p5 : (A → B) → (A → ⊥) ∨ B
  p5 f = TNDʸ→ (λ  a →     or→ f a)
            ⁿ→ (λ ¬a → ¬a ←or)

  p6 : (A → B) → (B → C) → (A → ⊥) ∨ C
  p6 f g = TNDʸ→ (λ  a →     or→ g (f a))
              ⁿ→ (λ ¬a → ¬a ←or)

  p7 : (((A → B) → A) → A)
  p7 = TNDʸ→ (λ  a → λ _ → a)
          ⁿ→ (λ ¬a → λ f → f (λ a → empty (¬a a)))

  p8 : (((A ∧ B) ∧ C) → ⊥) → (((A → ⊥) ∨ (B → ⊥)) ∨ (C → ⊥))
  p8 f = TNDʸ→ (λ  a → TNDʸ→ (λ  b → let ¬c : C → ⊥
                                         ¬c c = f ((a and b) and c)
                                     in            or→ ¬c)
                          ⁿ→ (λ ¬b → (    or→ ¬b) ←or))
            ⁿ→ (λ ¬a →               (¬a ←or    ) ←or)

  p9 : ((A → B) → ⊥) → A ∧ (B → ⊥)
  p9 f = let ∃a : A
             ∃a = TNDʸ→ (λ  a → a)
                     ⁿ→ (λ ¬a → empty (f (λ a → empty (¬a a))))
             ¬b : B → ⊥
             ¬b b = f (λ _ → b)
         in (∃a and ¬b)
