import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open scoped DirectSum

universe u

/-
Domain-style sampling for 19.2.6.1:
- primary domain: pushouts in `ModuleCat R` presenting the one-step Baer construction;
- sampled owner API:
  `CategoryTheory.Limits.pushout`,
  `CategoryTheory.Limits.pushout.inl`,
  `CategoryTheory.Limits.pushout.inr`,
  `CategoryTheory.CommSq`;
- best owner abstraction: the source-facing Baer step is a specific pushout object, with its
  canonical maps and commuting square derived from the pushout owner API;
- primitive data: the Baer index type and the two maps of the defining span;
- derived API: the notation `𝐌(M)`, the canonical maps into the pushout, and the commuting square.

Source/core/bridge triage:
- `source-facing`: the Baer pushout object `𝐌(M)` and its canonical maps;
- `core/canonical`: `pushout`, `pushout.inl`, `pushout.inr`, and `CommSq`;
- `bridge/view`: the two explicit direct-sum objects and the span maps that present the source
  object as a pushout. -/

section

variable (R : Type u) [Ring R]

/-- The indexing type for the Baer pushout construction, consisting of an ideal of `R` together
with an `R`-linear map from that ideal to `M`. -/
abbrev baerModuleIndex (M : ModuleCat R) :=
  Σ I : Ideal R, I →ₗ[R] M

/-- The direct sum `⨁_𝔞 ⨁_{φ : Hom_R(𝔞, M)} 𝔞` occurring in the Baer pushout construction. -/
noncomputable abbrev baerModuleIdealDirectSum (M : ModuleCat R) : ModuleCat R :=
  let _ : DecidableEq (baerModuleIndex R M) := Classical.decEq _
  ModuleCat.of R (⨁ j : baerModuleIndex R M, j.1)

/-- The direct sum `⨁_𝔞 ⨁_{φ : Hom_R(𝔞, M)} R` occurring in the Baer pushout construction. -/
noncomputable abbrev baerModuleRingDirectSum (M : ModuleCat R) : ModuleCat R :=
  let _ : DecidableEq (baerModuleIndex R M) := Classical.decEq _
  ModuleCat.of R (⨁ _j : baerModuleIndex R M, R)

/-- The top horizontal map in the Baer pushout diagram, sending the summand indexed by
`(𝔞, φ)` to `M` via `φ`. -/
noncomputable abbrev baerModuleTopMap (M : ModuleCat R) :
    baerModuleIdealDirectSum R M ⟶ M :=
  let _ : DecidableEq (baerModuleIndex R M) := Classical.decEq _
  ModuleCat.ofHom <|
    DirectSum.toModule R (baerModuleIndex R M) M fun j ↦ j.2

/-- The left vertical map in the Baer pushout diagram, sending the summand `𝔞` indexed by
`(𝔞, φ)` into the corresponding copy of `R` by the inclusion `𝔞 ↪ R`. -/
noncomputable abbrev baerModuleLeftVertical (M : ModuleCat R) :
    baerModuleIdealDirectSum R M ⟶ baerModuleRingDirectSum R M :=
  let _ : DecidableEq (baerModuleIndex R M) := Classical.decEq _
  ModuleCat.ofHom <|
    DirectSum.toModule R (baerModuleIndex R M) (⨁ _j : baerModuleIndex R M, R)
      (fun j ↦
        (DirectSum.lof R (baerModuleIndex R M) (fun _j ↦ R) j).comp j.1.subtype)

/-- 19.2.6.1: for an `R`-module `M`, the object `\mathbf{M}(M)` is the pushout of the huge
diagram
`⨁_𝔞 ⨁_{φ : Hom_R(𝔞, M)} 𝔞 ⟶ M` and
`⨁_𝔞 ⨁_{φ : Hom_R(𝔞, M)} 𝔞 ⟶ ⨁_𝔞 ⨁_{φ : Hom_R(𝔞, M)} R`. -/
noncomputable abbrev baerModuleStep (M : ModuleCat R) : ModuleCat R :=
  pushout (baerModuleLeftVertical R M) (baerModuleTopMap R M)

end

notation:max "𝐌(" M ")" => baerModuleStep _ M

section

variable (R : Type u) [Ring R]

/-- The canonical map `M ⟶ \mathbf{M}(M)` from the right side of the Baer pushout diagram. -/
noncomputable abbrev baerModuleStepInclusion (M : ModuleCat R) :
    M ⟶ 𝐌(M) :=
  pushout.inr (baerModuleLeftVertical R M) (baerModuleTopMap R M)

/-- The canonical map from `⨁_𝔞 ⨁_{φ : Hom_R(𝔞, M)} R` into `\mathbf{M}(M)` in the Baer
pushout diagram. -/
noncomputable abbrev baerModuleStepFromRingDirectSum (M : ModuleCat R) :
    baerModuleRingDirectSum R M ⟶ 𝐌(M) :=
  pushout.inl (baerModuleLeftVertical R M) (baerModuleTopMap R M)

/-- The defining Baer pushout square commutes. -/
theorem baerModuleStep_square_commutes (M : ModuleCat R) :
    CommSq (baerModuleLeftVertical R M) (baerModuleTopMap R M)
      (baerModuleStepFromRingDirectSum R M) (baerModuleStepInclusion R M) := by
  refine ⟨?_⟩
  simpa [baerModuleStepFromRingDirectSum, baerModuleStepInclusion] using
    (pushout.condition :
      baerModuleLeftVertical R M ≫ pushout.inl (baerModuleLeftVertical R M) (baerModuleTopMap R M) =
        baerModuleTopMap R M ≫ pushout.inr (baerModuleLeftVertical R M) (baerModuleTopMap R M))

end
