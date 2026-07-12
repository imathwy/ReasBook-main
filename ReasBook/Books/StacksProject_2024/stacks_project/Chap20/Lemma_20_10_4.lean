import StacksProject_2024.Chap20.Lemma_20_10_3

open CategoryTheory Opposite TopologicalSpace PresheafOfModules
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u}

/- Domain-style sampling for Lemma 20.10.4:
- primary domain: homology of the cover chain complex in `PMod(𝒪_X)` and the canonical
  degree-zero augmentation to the unit `𝒪_X`-module;
- sampled owner declarations:
  `openCoverChainComplex`,
  `unit`,
  `image`,
  `HomologicalComplex.homology`;
- best owner abstraction: the source-facing object is the chain complex
  `openCoverChainComplex 𝒰`; its degree-zero term `(openCoverChainComplex 𝒰).X 0` and the unit
  module `unit X.ringCatSheaf.obj` are canonical owners, so the only local bridge data kept here
  is the augmentation morphism between them.

Primitive data is only the ringed space `X` and the indexed open family `𝒰`. The explicit sigma
coproduct model for degree `0` is derived from `openCoverChainComplex 𝒰`, and the image object is
derived API of the augmentation rather than a second owner declaration.

Source/core/bridge triage:
- `source-facing`: the homology description of `openCoverChainComplex 𝒰`;
- `core/canonical`: `openCoverChainComplex`, `unit`, `image`, and homology;
- `bridge/view`: the augmentation from degree `0` of the cover chain complex to the structure
  presheaf, written via the public degree-zero chain-term API from
  `stacks_project/Chap20/Lemma_20_10_3`. -/

/-- The canonical augmentation from degree `0` of the Čech cover chain complex to the structure
presheaf, sending the distinguished generator of each summand to `1`. -/
noncomputable def openCoverChainComplexAugmentation (𝒰 : ι → Opens X.carrier) :
    (openCoverChainComplex 𝒰).X 0 ⟶ unit X.ringCatSheaf.obj :=
  let O := X.ringCatSheaf.obj
  eqToHom (openCoverChainDegree_eq 𝒰 0) ≫
    Sigma.desc fun i : openCoverPowerIndex 𝒰 0 ↦
      freeYonedaEquiv.symm
        (show (unit O).obj (op (openCoverPowerOpen 𝒰 0 i)) from
          (1 : O.obj (op (openCoverPowerOpen 𝒰 0 i))))

-- Proof sketch: the augmented Čech complex is exact at degree `0` up to the augmentation, so the
-- degree-zero homology identifies canonically with the image presheaf of the augmentation.
/-- The degree-zero homology of the cover chain complex is isomorphic to the image presheaf of the
canonical augmentation to the structure presheaf.

This file keeps the comparison at the proposition-level owner `IsIsomorphic`, rather than adding a
chosen concrete isomorphism to the public API. -/
@[stacks 01EM]
theorem openCoverChainComplex_homology_zero_isomorphic_coverStructureImage
    (𝒰 : ι → Opens X.carrier) :
    IsIsomorphic ((openCoverChainComplex 𝒰).homology 0)
      (image (openCoverChainComplexAugmentation 𝒰)) := by
  sorry

-- Proof sketch: the augmented Čech complex is exact in every positive degree, so the homology of
-- the cover chain complex vanishes at each index of the form `p + 1`.
/-- In every positive degree, the homology of the cover chain complex vanishes. -/
theorem openCoverChainComplex_homology_succ_isZero
    (𝒰 : ι → Opens X.carrier) (p : ℕ) :
    IsZero ((openCoverChainComplex 𝒰).homology (p + 1)) := sorry

end AlgebraicGeometry.RingedSpace
