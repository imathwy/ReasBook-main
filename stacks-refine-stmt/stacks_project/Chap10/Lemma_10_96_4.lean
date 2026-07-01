import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AdicCompletion

noncomputable section

universe u v

section

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M N Q : Type v}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q]

/-- A module annihilated by a power of `I` is `I`-adically complete. -/
-- Proof sketch: if `I ^ c • Q = 0`, then the inverse system `Q / I^n Q` is eventually constant with
-- value `Q`, so the canonical map `Q → AdicCompletion I Q` is bijective. Conclude using
-- `AdicCompletion.of_bijective_iff`.
theorem isAdicComplete_of_pow_smul_top_eq_bot (c : ℕ)
    (hc : I ^ c • (⊤ : Submodule R Q) = ⊥) : IsAdicComplete I Q := sorry

namespace AdicCompletion

/-- The map from the `I`-adic completion of `N` to an `I`-adically complete target `Q` induced by
`g : N →ₗ[R] Q`. -/
noncomputable abbrev mapToComplete (g : N →ₗ[R] Q) [IsAdicComplete I Q] :
    AdicCompletion I N →ₗ[R] Q :=
  ((ofLinearEquiv I Q).symm : AdicCompletion I Q →ₗ[R] Q).comp ((map I g).restrictScalars R)

@[simp]
theorem mapToComplete_of (g : N →ₗ[R] Q) [IsAdicComplete I Q] (x : N) :
    mapToComplete I g (of I N x) = g x := by
  apply (ofLinearEquiv I Q).injective
  rw [mapToComplete, LinearMap.comp_apply, LinearMap.restrictScalars_apply, map_of]
  simp

@[simp]
theorem mapToComplete_comp_of (g : N →ₗ[R] Q) [IsAdicComplete I Q] :
    (mapToComplete I g).comp (of I N) = g := by
  ext x
  exact mapToComplete_of I g x

theorem mapToComplete_comp_eq_zero {f : M →ₗ[R] N} {g : N →ₗ[R] Q} [IsAdicComplete I Q]
    (hfg : Function.Exact f g) :
    (mapToComplete I g).comp ((map I f).restrictScalars R) = 0 := by
  apply DFunLike.ext
  intro x
  apply (ofLinearEquiv I Q).injective
  simp [mapToComplete, map_comp_apply, hfg.linearMap_comp_eq_zero]

end AdicCompletion

/-- The map from `N^∧` to a quotient module `Q` annihilated by a power of `I`, obtained from the
canonical identification `Q^∧ ≃ Q`. -/
noncomputable abbrev completionMapToPowSmulTopEqBot (g : N →ₗ[R] Q) {c : ℕ}
    (hc : I ^ c • (⊤ : Submodule R Q) = ⊥) : AdicCompletion I N →ₗ[R] Q :=
  let _ : IsAdicComplete I Q :=
    isAdicComplete_of_pow_smul_top_eq_bot I c hc
  AdicCompletion.mapToComplete I g

theorem completionMapToPowSmulTopEqBot_comp_eq_zero
    {f : M →ₗ[R] N} {g : N →ₗ[R] Q} (hfg : Function.Exact f g)
    {c : ℕ} (hc : I ^ c • (⊤ : Submodule R Q) = ⊥) :
    (completionMapToPowSmulTopEqBot I g hc).comp ((AdicCompletion.map I f).restrictScalars R) =
      0 := sorry

-- Proof sketch: choose `c` with `I ^ c • Q = 0`, identify `Q / I^n Q` with `Q` for `n ≥ c`, and
-- rewrite the left quotients using `M ∩ I^n N`. Apply Lemma `10.87.1` to the inverse system of
-- short exact sequences `0 → M / (M ∩ I^n N) → N / I^n N → Q → 0`, then transport the right term
-- along the identification `Q^ ≃ Q`.
/-- Lemma 10.96.4: if `0 → M → N → Q → 0` is exact and a power of `I` annihilates `Q`, then
completion yields a short exact sequence `0 → M^ → N^ → Q → 0`. -/
theorem completion_shortExact_of_pow_smul_top_eq_bot
    {f : M →ₗ[R] N} {g : N →ₗ[R] Q}
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    {c : ℕ} (hc : I ^ c • (⊤ : Submodule R Q) = ⊥) :
    (ShortComplex.moduleCatMk
      ((AdicCompletion.map I f).restrictScalars R)
      (completionMapToPowSmulTopEqBot I g hc)
      (completionMapToPowSmulTopEqBot_comp_eq_zero I hfg hc)).ShortExact := sorry

end
