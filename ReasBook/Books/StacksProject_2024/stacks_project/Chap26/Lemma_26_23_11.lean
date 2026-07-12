import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

-- Semantic recall: `Pi.evalRingHom`, `CategoryTheory.Limits.Sigma.map'`, and
-- `CategoryTheory.Limits.Sigma.ι_comp_map'` are the canonical bridge maps behind the product-side
-- and coproduct-side source clauses.
-- Source/core/bridge triage for Lemma 26.23.11:
-- - `source-facing`: the subproduct and subcoproduct presentations classified by subsets;
-- - `core/canonical`: the corresponding arrows in the slice categories over the ambient product
--   and coproduct;
-- - `bridge/view`: `specPiSubsetInclusion`, `sigmaSpecSubsetInclusion`, and the companion
--   computation formulas for their defining maps.

/-- The spectrum of the subproduct indexed by `J`. -/
noncomputable abbrev specPiSubset {ι : Type u} (k : ι → Type v) [∀ i, CommRing (k i)] (J : Set ι) :
    Scheme :=
  Spec (CommRingCat.of ((j : J) → k j))

/-- The spectrum of the ambient product of the family `k`. -/
noncomputable abbrev specPiFamily {ι : Type u} (k : ι → Type v) [∀ i, CommRing (k i)] :
    Scheme :=
  Spec (CommRingCat.of ((i : ι) → k i))

/-- The canonical inclusion of the spectrum of the subproduct indexed by `J` into the spectrum of
the ambient product. -/
noncomputable abbrev specPiSubsetInclusion {ι : Type u} (k : ι → Type v)
    [∀ i, CommRing (k i)] (J : Set ι) :
    specPiSubset k J ⟶ specPiFamily k :=
  Spec.map <| CommRingCat.ofHom <| Pi.ringHom fun j : J ↦ Pi.evalRingHom k j.1

/-- Companion API for `specPiSubsetInclusion`: on rings, the defining map from the ambient product
to the subproduct evaluates an ambient tuple at the corresponding coordinate. -/
@[simp] theorem specPiSubsetInclusion_ringHom_apply {ι : Type u} (k : ι → Type v)
    [∀ i, CommRing (k i)] (J : Set ι) (x : (i : ι) → k i) (j : J) :
    (Pi.ringHom (fun t : J ↦ Pi.evalRingHom k t.1)) x j = x j.1 := by
  rfl

/-- The coproduct of the spectra indexed by `J`. -/
noncomputable abbrev sigmaSpecSubset {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, CommRing (k i)] (J : Set ι) : Scheme :=
  ∐ fun j : J ↦ Spec (CommRingCat.of (k j))

/-- The ambient coproduct of the spectra of the family `k`. -/
noncomputable abbrev sigmaSpecFamily {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, CommRing (k i)] : Scheme :=
  ∐ fun i : ι ↦ Spec (CommRingCat.of (k i))

/-- The canonical inclusion of the coproduct over `J` into the coproduct over `ι`. -/
noncomputable abbrev sigmaSpecSubsetInclusion {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, CommRing (k i)] (J : Set ι) :
    sigmaSpecSubset k J ⟶ sigmaSpecFamily k :=
  Sigma.map' (fun j : J ↦ (j : ι)) (fun j ↦ 𝟙 (Spec (CommRingCat.of (k j))))

/-- Companion API for `sigmaSpecSubsetInclusion`: the `j`th coproduct summand maps to the ambient
`j.1`st summand by the canonical coproduct inclusion. -/
@[simp, reassoc]
theorem sigmaSpecSubsetInclusion_ι {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, CommRing (k i)] (J : Set ι) (j : J) :
    Sigma.ι (fun t : J ↦ Spec (CommRingCat.of (k t))) j ≫ sigmaSpecSubsetInclusion k J =
      Sigma.ι (fun i : ι ↦ Spec (CommRingCat.of (k i))) j.1 := by
  rw [sigmaSpecSubsetInclusion, Sigma.ι_comp_map']
  simp

/-- Lemma 26.23.11 (1): a monomorphism into the spectrum of a finite product of fields is
isomorphic, over the target, to the spectrum of the subproduct indexed by a subset. -/
@[stacks 03DP]
theorem Scheme.Hom.exists_subset_specPi_isoOver_of_mono {ι : Type u} [Finite ι]
    (k : ι → Type v) [∀ i, Field (k i)]
    {X : Scheme} (f : X ⟶ specPiFamily k) [Mono f] :
    ∃ J : Set ι, Over.mk f ≅ Over.mk (specPiSubsetInclusion k J) := sorry

/-- Companion API for Lemma 26.23.11 (1): unpack the slice-category isomorphism into an ordinary
scheme isomorphism whose structure map agrees with `f`. -/
theorem Scheme.Hom.exists_subset_specPi_iso_of_mono {ι : Type u} [Finite ι]
    (k : ι → Type v) [∀ i, Field (k i)]
    {X : Scheme} (f : X ⟶ specPiFamily k) [Mono f] :
    ∃ J : Set ι, ∃ e : X ≅ specPiSubset k J,
      e.hom ≫ specPiSubsetInclusion k J = f := by
  rcases Scheme.Hom.exists_subset_specPi_isoOver_of_mono k f with ⟨J, e⟩
  refine ⟨J, asIso e.hom.left, ?_⟩
  simpa using e.hom.w

/-- Lemma 26.23.11 (2): a monomorphism into a disjoint union of spectra of fields is isomorphic,
over the target, to the coproduct of the components indexed by a subset. -/
@[stacks 03DP]
theorem Scheme.Hom.exists_subset_sigmaSpec_isoOver_of_mono {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, Field (k i)]
    {Y : Scheme} (f : Y ⟶ sigmaSpecFamily k) [Mono f] :
    ∃ J : Set ι, Over.mk f ≅ Over.mk (sigmaSpecSubsetInclusion k J) := sorry

/-- Companion API for Lemma 26.23.11 (2): unpack the slice-category isomorphism into an ordinary
scheme isomorphism whose structure map agrees with `f`. -/
theorem Scheme.Hom.exists_subset_sigmaSpec_iso_of_mono {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, Field (k i)]
    {Y : Scheme} (f : Y ⟶ sigmaSpecFamily k) [Mono f] :
    ∃ J : Set ι, ∃ e : Y ≅ sigmaSpecSubset k J,
      e.hom ≫ sigmaSpecSubsetInclusion k J = f := by
  rcases Scheme.Hom.exists_subset_sigmaSpec_isoOver_of_mono k f with ⟨J, e⟩
  refine ⟨J, asIso e.hom.left, ?_⟩
  simpa using e.hom.w

end AlgebraicGeometry
