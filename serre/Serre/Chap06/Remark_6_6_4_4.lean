import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Algebra

universe u v

section

/-- Remark 6-6.4-4: after replacing `ℤ` by an arbitrary commutative noetherian ring, the three
conditions from Proposition 6-6.4-1 remain equivalent for elements of any ring algebra over that
base. -/
lemma isIntegral_tfae_finite_adjoin_simple (A : Type u) {B : Type v}
    [CommRing A] [Ring B] [Algebra A B] [IsNoetherianRing A] (x : B) :
    [IsIntegral A x,
      Module.Finite A A[x],
      ∃ M : Submodule A B,
        Module.Finite A M ∧ A[x].toSubmodule ≤ M].TFAE := by
  tfae_have 1 → 2 := Algebra.finite_adjoin_simple_of_isIntegral
  tfae_have 2 → 1 := by
    intro h
    letI : Module.Finite A A[x].toSubmodule :=
      Module.Finite.equiv (Subalgebra.toSubmoduleEquiv A[x]).symm
    exact IsIntegral.of_mem_of_fg A[x] Submodule.FG.of_finite x
      (Algebra.self_mem_adjoin_singleton A x)
  tfae_have 2 → 3 := fun h ↦
    ⟨A[x].toSubmodule, by simpa using h, le_rfl⟩
  tfae_have 3 → 2 := by
    rintro ⟨M, hM, hle⟩
    letI : Module.Finite A M := hM
    simpa using Module.Finite.of_fg ((Submodule.FG.of_finite : M.FG).of_le hle)
  tfae_finish

end
