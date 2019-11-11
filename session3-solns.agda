-- This file contains Agda versions of proofs from Session 3 of the
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

module _ {A B C : Set} where
  p1 : A → B → A ∨ B
  p1 a _ = a ←or

  p2 : A → A ∨ B
  p2 a = a ←or

  p3 : B → A ∨ B
  p3 b = or→ b

  p4 : A → A ∨ A
  p4 a = a ←or

  p5 : A ∨ B → B ∨ A
  p5 (a ←or   ) =    or→ a
  p5 (   or→ b) = b ←or

  p6 : A ∨ (B ∨ C) → (A ∨ B) ∨ C
  p6 (a ←or            ) = (a ←or   ) ←or
  p6 (   or→ (b ←or   )) = (   or→ b) ←or
  p6 (   or→ (   or→ c)) =             or→ c

  p7 : A ∧ B → A ∨ B
  p7 (a and _) = a ←or

  p8 : (A ∧ B) ∨ C → (A ∨ C) ∧ (B ∨ C)
  p8 ((a and b) ←or   ) = (a ←or   ) and (b ←or   )
  p8 (           or→ c) = (   or→ c) and (   or→ c)

  p9 : (A ∨ B) ∧ C → (A ∧ C) ∨ (B ∧ C)
  p9 ((a ←or   ) and c) = (a and c) ←or
  p9 ((   or→ b) and c) =            or→ (b and c)

  p10 : (A → C) ∧ (B → C) → (A ∨ B → C)
  p10 (f and g) = h
    where h : A ∨ B → C
          h (a ←or   ) = f a
          h (   or→ b) = g b

  p11 : (A ∨ B → C) → (A → C) ∨ (B → C)
  p11 f = or→ λ b → f (or→ b)

  p12 : (A → B) ∨ (A → C) → (A → (B ∨ C))
  p12 (f ←or   ) = λ a → f a ←or
  p12 (   or→ g) = λ a →      or→ g a
