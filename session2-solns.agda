-- This file contains Agda versions of proofs from Session 2 of the
-- Incredible Proof Machine http://incredible.pm/

data _∧_ (A : Set) (B : Set) : Set where
  _and_ : A → B → A ∧ B

module _ {A B C D : Set} where
  p1 : A → (A → B) → B
  p1 a a→b = a→b a

  p2 : A → (A → B) → (B → C) → C
  p2 a a→b b→c = b→c (a→b a)

  p3 : A → (A → B) → (A → C) → (B → D) → (C → D) → D
  p3 a a→b a→c b→d c→d = c→d (a→c a)

  p4 : A → (A → A) → A
  p4 a _ = a

  p5 : (A → B) → (B → C) → (A → C)
  p5 a→b b→c = λ a → b→c (a→b a)

  p6 : (A → B) → (A → (B → C)) → (A → C)
  p6 a→b a⇒b→c = λ a → (a⇒b→c a) (a→b a)

  p7 : (A → A)
  p7 = λ a → a

  p8 : (A → C) → (B → C) → A ∧ B → C
  p8 a→c _ (a and _) = a→c a

  p9 : (A → C) → (B → C) → (A ∧ B → C)
  p9 = p8

  p10 : B → (A → B)
  p10 b = λ _ → b

  p11 : (A ∧ B → C) → (A → (B → C))
  p11 f = λ a → λ b → f (a and b)

  p12 : (A → (B → C)) → (A ∧ B → C)
  p12 f = λ{ (a and b) → (f a) b }

  p13 : (A → B) ∧ (A → C) → (A → B ∧ C)
  p13 (a→b and a→c) = λ a → (a→b a and a→c a)

  p14 : (A → (A → B)) → ((A → B) → A) → B
  p14 f g = h (g h)
    where h : A → B
          h a = (f a) a
