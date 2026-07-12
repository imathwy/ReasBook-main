import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Stalk

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: the statement reuses the canonical locally-Artinian owner
-- `AlgebraicGeometry.IsLocallyArtinian.of_topologicalKrullDim_le_zero`, the canonical local-spectrum
-- map `Scheme.fromSpecStalk`, and the existing disjoint-union-of-spectra pattern from
-- `Chap26/Lemma_26_23_11`.

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- The coproduct of the spectra of the stalks of `X`. -/
noncomputable abbrev sigmaSpecStalk : Scheme.{u} :=
  ∐ fun x : X ↦ Spec (X.presheaf.stalk x)

/-- The canonical coproduct map from the spectra of the stalks of `X` to `X`. -/
noncomputable abbrev sigmaFromSpecStalk :
    X.sigmaSpecStalk ⟶ X :=
  Sigma.desc (fun x : X ↦ X.fromSpecStalk x)

@[simp, reassoc] theorem Sigma_ι_sigmaFromSpecStalk (x : X) :
    Sigma.ι (fun y : X ↦ Spec (X.presheaf.stalk y)) x ≫ X.sigmaFromSpecStalk = X.fromSpecStalk x := by
  simp [sigmaFromSpecStalk]

/-- Lemma 28.10.5: a locally Noetherian scheme of dimension `0` is a disjoint union of spectra of
Artinian local rings. Here the disjoint union is expressed canonically as the coproduct of the
spectra of the stalks of `X`, and the comparison map is induced by `X.fromSpecStalk`. -/
@[stacks 0AAX]
theorem isIso_sigmaFromSpecStalk_of_dimZero
    (hXdim : topologicalKrullDim X = 0) :
    IsIso X.sigmaFromSpecStalk := sorry

/-- Companion form of Lemma 28.10.5: after identifying the canonical family of local Artinian
stalk rings, the scheme `X` is isomorphic to the coproduct of their spectra. -/
@[stacks 0AAX]
theorem sigmaSpecStalkIso_of_dimZero
    (hXdim : topologicalKrullDim X = 0) :
    X ≅ X.sigmaSpecStalk := by
  letI : IsIso X.sigmaFromSpecStalk := isIso_sigmaFromSpecStalk_of_dimZero X hXdim
  exact (asIso X.sigmaFromSpecStalk).symm

/-- In Lemma 28.10.5, every stalk ring of `X` is Artinian local. -/
@[stacks 0AAX]
theorem isArtinianRing_stalk_of_dimZero
    (hXdim : topologicalKrullDim X = 0) (x : X) :
    IsArtinianRing (X.presheaf.stalk x) := by
  letI : IsLocallyArtinian X :=
    IsLocallyArtinian.of_topologicalKrullDim_le_zero (X := X) hXdim.le
  infer_instance

end AlgebraicGeometry.Scheme
