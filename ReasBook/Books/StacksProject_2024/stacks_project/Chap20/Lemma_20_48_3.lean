import StacksProject_2024.Chap20.Tor_amplitude_on_opens_ringed_site
import StacksProject_2024.Chap21.Lemma_21_46_3

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open AlgebraicGeometry
open SheafOfModules.RingedSite.CochainComplex

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

variable [CategoryWithHomology (Modules X)]
variable [HasCountableCoproducts (Modules X)]
variable [MonoidalCategory (Modules X)]
variable [MonoidalPreadditive (Modules X)]
variable [HasColimits (Modules X)]
variable [(curriedTensor (Modules X)).Additive]
variable [∀ ℱ : Modules X, ((curriedTensor (Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (Modules X))]
variable [MonoidalCategory (DerivedCategory (Modules X))]

local notation "ModX" => Modules X
local notation "DMod" => DerivedCategory (Modules X)

/- Domain-style sampling for Lemma 20.48.3:
- primary domain: tor-amplitude in `D(𝒪_X)` described via bounded flat representatives;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `DerivedCategory.Q.obj`,
  `CochainComplex.IsTermwiseFlat`,
  `SheafOfModules.RingedSite.hasTorAmplitudeIn_iff_exists_flat_representative`;
- best owner abstraction:
  `source-facing`: the Chapter 20 tor-amplitude owner `HasTorAmplitudeIn` together with the
    existence of a bounded flat representative from the source text;
  `core/canonical`: the Chapter 21 owner theorem
    `SheafOfModules.RingedSite.hasTorAmplitudeIn_iff_exists_flat_representative` on the opens
    ringed site, together with `DerivedCategory.Q.obj` and `SheafOfModules.IsFlat`;
  `bridge/view`: the opens-ringed-site identification of `D(𝒪_X)` with the ambient
    ringed-site derived category, used only to restate the owner theorem on a ringed space.

Source/core/bridge triage:
- `source-facing`: tor-amplitude in `[a, b]` for an object of `D(𝒪_X)`;
- `core/canonical`: the Chapter 21 ringed-site theorem
  `SheafOfModules.RingedSite.hasTorAmplitudeIn_iff_exists_flat_representative`;
- `bridge/view`: the opens-ringed-site specialization back to `RingedSpace`.

Primitive vs. derived:
- primitive data: the derived object `E`, the interval bounds `a, b`, and a cochain complex `K`
  of `𝒪_X`-modules with support in `[a, b]`, termwise flat, and an isomorphism
  `E ≅ DerivedCategory.Q.obj K`;
- derived API: only the source-facing existential criterion below.
-/

-- Proof sketch: compare the Chapter 20 tor-amplitude condition with the existence of a bounded
-- flat representative computing `E` in the derived category. The canonical owner theorem is the
-- Chapter 21 ringed-site result on the opens ringed site of `X`; this file keeps only the
-- source-facing ringed-space restatement.
/-- Lemma 20.48.3: for a ringed space `(X, 𝒪_X)`, an object `E` of `D(𝒪_X)`
has tor-amplitude in `[a, b]` if and only if it admits a bounded representative by flat
`𝒪_X`-modules vanishing outside `[a, b]`. -/
@[stacks 08CI]
theorem hasTorAmplitudeIn_iff_exists_flat_representative
    (E : DMod) (a b : ℤ) :
    HasTorAmplitudeIn E a b ↔
      ∃ (K : CochainComplex ModX ℤ) (_ : E ≅ DerivedCategory.Q.obj K),
        K.IsStrictlyGE a ∧ K.IsStrictlyLE b ∧ IsTermwiseFlat K := by
  rw [hasTorAmplitudeIn_iff_opensRingedSiteHasTorAmplitudeIn]
  constructor
  · intro hE
    rcases
        (SheafOfModules.RingedSite.hasTorAmplitudeIn_iff_exists_flat_representative E a b).1 hE
      with ⟨K, e, hge, hle, hFlat⟩
    exact ⟨K, e, hge, hle, hFlat⟩
  · rintro ⟨K, e, hge, hle, hFlat⟩
    exact
      (SheafOfModules.RingedSite.hasTorAmplitudeIn_iff_exists_flat_representative E a b).2
        ⟨K, e, hge, hle, hFlat⟩

namespace HasTorAmplitudeIn

/-- A tor-amplitude bound in `[a, b]` on a ringed space yields a flat representative supported in
`[a, b]`. -/
theorem exists_flat_representative
    {E : DMod} {a b : ℤ}
    (hE : HasTorAmplitudeIn E a b) :
    ∃ (K : CochainComplex ModX ℤ) (_ : E ≅ DerivedCategory.Q.obj K),
      K.IsStrictlyGE a ∧ K.IsStrictlyLE b ∧ IsTermwiseFlat K :=
  (hasTorAmplitudeIn_iff_exists_flat_representative E a b).1 hE

end HasTorAmplitudeIn

/-- A bounded flat representative supported in `[a, b]` on a ringed space gives tor-amplitude in
`[a, b]`. -/
theorem hasTorAmplitudeIn_of_exists_flat_representative
    {E : DMod} {a b : ℤ}
    (hE : ∃ (K : CochainComplex ModX ℤ) (_ : E ≅ DerivedCategory.Q.obj K),
      K.IsStrictlyGE a ∧ K.IsStrictlyLE b ∧ IsTermwiseFlat K) :
    HasTorAmplitudeIn E a b :=
  (hasTorAmplitudeIn_iff_exists_flat_representative E a b).2 hE

end

end AlgebraicGeometry.RingedSpace
