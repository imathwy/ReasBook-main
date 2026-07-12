import Mathlib
import StacksProject_2024.Chap10.Definition_10_104_6
import StacksProject_2024.Chap10.Lemma_10_103_13

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

open RingTheory Sequence
open scoped ENat TensorProduct

section

variable {R : Type u} [CommRing R]

private theorem regularSequenceLengths_eq_of_equiv {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (I : Ideal R) (e : M ≃ₗ[R] N) :
    Ideal.regularSequenceLengths I M = Ideal.regularSequenceLengths I N := by
  ext d
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).1 hreg, hI, rfl⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).2 hreg, hI, rfl⟩

private theorem ideal_depth_eq_of_equiv {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N] (I : Ideal R)
    (e : M ≃ₗ[R] N) : Ideal.depth I M = Ideal.depth I N := by
  have htop : I • (⊤ : Submodule R M) = ⊤ ↔ I • (⊤ : Submodule R N) = ⊤ := by
    constructor
    · intro h
      have := congrArg (Submodule.map e.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.surjective] using this
    · intro h
      have := congrArg (Submodule.map e.symm.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.symm.surjective] using this
  by_cases hM : I • (⊤ : Submodule R M) = ⊤
  · rw [Ideal.depth_eq_top_of_smul_top I M hM, Ideal.depth_eq_top_of_smul_top I N (htop.mp hM)]
  · rw [Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I M hM,
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I N (mt htop.mpr hM),
      regularSequenceLengths_eq_of_equiv I e]

private theorem Module.CohenMacaulay.of_linearEquiv [IsLocalRing R] [IsNoetherianRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    [h : Module.CohenMacaulay R M] : Module.CohenMacaulay R N := by
  let _ : Module.Finite R N := Module.Finite.equiv e
  exact ⟨by
    rw [← Module.supportDim_eq_of_equiv e, ← moduleDepth_eq_of_equiv e, h.supportDim_eq_moduleDepth]⟩

private theorem Module.LocallyCohenMacaulay.of_linearEquiv [IsNoetherianRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    [h : Module.LocallyCohenMacaulay R M] : Module.LocallyCohenMacaulay R N := by
  let _ : Module.Finite R N := Module.Finite.equiv e
  exact ⟨fun p ↦ by
    let ep : LocalizedModule.AtPrime p.asIdeal M ≃ₗ[Localization.AtPrime p.asIdeal]
        LocalizedModule.AtPrime p.asIdeal N :=
      LinearEquiv.ofBijective (LocalizedModule.map p.asIdeal.primeCompl e.toLinearMap)
        ⟨LocalizedModule.map_injective p.asIdeal.primeCompl e.toLinearMap e.injective,
          LocalizedModule.map_surjective p.asIdeal.primeCompl e.toLinearMap e.surjective⟩
    let _ :
        Module.CohenMacaulay (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) :=
      h.localizedModule_cohenMacaulay p
    exact Module.CohenMacaulay.of_linearEquiv ep⟩

-- Proof sketch: view a Cohen-Macaulay ring as a locally Cohen-Macaulay self-module, apply
-- `Module.LocallyCohenMacaulay.mvPolynomial` with `M = R`, and translate the resulting local
-- self-module statement back to the owner class `CohenMacaulayRing` for the polynomial ring using
-- the canonical `MvPolynomial (Fin n) R ⊗[R] R ≃ₐ[MvPolynomial (Fin n) R] MvPolynomial (Fin n) R`.
/-- Lemma 10.104.7: if `R` is a Noetherian Cohen-Macaulay ring, then every finite polynomial ring
`R[x₁, …, xₙ]`, represented by `MvPolynomial (Fin n) R`, is Cohen-Macaulay. -/
@[stacks 00ND]
theorem cohenMacaulayRing_mvPolynomial (hCM : CohenMacaulayRing R) (n : ℕ) :
    CohenMacaulayRing (MvPolynomial (Fin n) R) := by
  let _ : CohenMacaulayRing R := hCM
  let S := MvPolynomial (Fin n) R
  let _ : Module.LocallyCohenMacaulay S (S ⊗[R] R) :=
    Module.LocallyCohenMacaulay.mvPolynomial (inferInstance : Module.LocallyCohenMacaulay R R) n
  let _ : Module.LocallyCohenMacaulay S S :=
    Module.LocallyCohenMacaulay.of_linearEquiv (Algebra.TensorProduct.rid R S S).toLinearEquiv
  exact CohenMacaulayRing.mk

end
