-- This file contains Agda versions of proofs from Session 1 of the
-- Incredible Proof Machine http://incredible.pm/

-- Some problems are commented since the formulation in Agda is not
-- very interesting, or ends up being identical to a previous question.

data _∧_ (A : Set) (B : Set) : Set where
  _and_ : A → B → A ∧ B

module _ {A B C : Set} where
  p1 : A → A
  p1 a = a

  p2 : A → B → A
  p2 a b = a

  -- p3 : {A B : Set} → A → B → B ∧ A
  -- p3 a b = ?

  p4 : A → B → A ∧ B
  p4 a b = a and b

  p5 : A → A ∧ A
  p5 a = a and a

  p6 : A ∧ B → A
  p6 (a and _) = a

  -- p7 : A ∧ B → A ∧ B
  -- p7 a∧b = ?

  -- p8 : A ∧ B → A ∧ B
  -- p8 a∧b = ?

  p9 : A ∧ B → B ∧ A
  p9 (a and b) = b and a

  -- p10 : (A ∧ B) ∧ C → (A ∧ B) ∧ C
  -- p10 a∧b∧c = {!!}

  p11 : (A ∧ B) ∧ C → A ∧ C
  p11 ((a and b) and c) = a and c

  p12 : (A ∧ B) ∧ C → A ∧ (B ∧ C)
  p12 ((a and b) and c) = a and (b and c)
