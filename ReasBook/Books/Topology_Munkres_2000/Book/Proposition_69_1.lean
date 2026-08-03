module

public import Mathlib.GroupTheory.CoprodI

public section

universe u

variable {ι : Type u}

open Monoid.CoprodI.Word

/-- Proposition 69.1. Every element of the external free product of infinite cyclic groups has a
unique reduced-word representation in tagged integer exponents. -/
theorem freeGroup_existsUnique_reducedWord
    (x : Monoid.CoprodI (fun _ : ι ↦ Multiplicative ℤ)) :
    ∃! w : Monoid.CoprodI.Word (fun _ : ι ↦ Multiplicative ℤ), w.prod = x := by
  classical
  let e : Monoid.CoprodI (fun _ : ι ↦ Multiplicative ℤ) ≃
      Monoid.CoprodI.Word (fun _ : ι ↦ Multiplicative ℤ) := equiv
  refine ⟨e x, e.left_inv x, ?_⟩
  intro w hw
  apply e.symm.injective
  exact hw.trans (e.left_inv x).symm

/- A reduced word evaluates to the represented element of the free product. -/
#check prod

/- Every letter of a reduced word is nontrivial; for cyclic factors its integer exponent is
nonzero. -/
#check ne_one

/- Adjacent letters of a reduced word come from distinct factors. -/
#check chain_ne
