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

module _ {A B C : Set} where
  p1 : ⊥ → A
  p1 x = empty x

  p2 : ⊥ → A ∧ B
  p2 x = empty x

  p3 : A → ⊥ ∨ A
  p3 a = or→ a

  p4 : ⊥ ∨ A → A
  p4 (! ←or   ) = empty !
  p4 (   or→ a) = a

  p5 : ⊥ ∧ A → ⊥
  p5 (! and a) = !

  p6 : (⊥ → A)
  p6 = p1

  p7 : (A → B) → ((B → ⊥) → (A → ⊥))
  p7 a→b = λ ¬b → λ a → ¬b (a→b a)

  p8 : (A ∨ B → ⊥) → (A → ⊥) ∧ (B → ⊥)
  p8 f = (λ a → f (a ←or)) and (λ b → f (or→ b))

  p9 : (A → ⊥) ∧ (B → ⊥) → (A ∨ B → ⊥)
  p9 (f and g) = λ{ (a ←or   ) → f a ;
                    (   or→ b) → g b }

  p10 : (A → ⊥) ∨ (B → ⊥) → (A ∧ B → ⊥)
  p10 (¬a ←or    ) = λ{ (a and _) → a ↯ ¬a }
  p10 (    or→ ¬b) = λ{ (_ and b) → b ↯ ¬b }

  p11 : (((A → ⊥) → ⊥) → ⊥) → (A → ⊥)
  p11 f = λ a → f (λ ¬a → a ↯ ¬a)

  p12 : (A → ⊥) ∨ B → (A → B)
  p12 (¬a ←or   )  = λ a → a ↯ ¬a
  p12 (    or→ b)  = λ _ → b

  p13 : (A → ⊥) → (B → A) → (B → ⊥)
  p13 ¬a f = λ b → ¬a (f b)

  p14 : (A → ⊥) ∨ (B → ⊥) ∨ (C → ⊥) → (A ∧ B ∧ C → ⊥)
  p14 (¬a ←or     ←or    )  = λ{ (a and _ and _) → a ↯ ¬a }
  p14 (    or→ ¬b ←or    )  = λ{ (_ and b and _) → b ↯ ¬b }
  p14 (            or→ ¬c)  = λ{ (_ and _ and c) → c ↯ ¬c }

  p15 : (A ∨ (A → ⊥) → ⊥) → ⊥
  p15 = λ f → f (or→ λ a → f (a ←or))
