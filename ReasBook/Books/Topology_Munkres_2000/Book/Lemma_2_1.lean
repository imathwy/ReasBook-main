module

public import Mathlib.Logic.Function.Basic

public section

/-- Lemma 2.1 (1): A function admitting a left inverse and a right inverse is bijective. -/
theorem Function.Bijective.of_leftInverse_of_rightInverse {A : Sort u} {B : Sort v}
    {f : A → B} {g h : B → A} (hg : Function.LeftInverse g f)
    (hh : Function.RightInverse h f) :
    Function.Bijective f :=
  ⟨hg.injective, hh.surjective⟩

/- Lemma 2.1 (2): A left inverse and a right inverse of the same function are equal,
so their common value is the inverse of that function. -/
#check Function.LeftInverse.eq_rightInverse
