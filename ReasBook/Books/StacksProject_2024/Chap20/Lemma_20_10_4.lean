import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import StacksProject_2024.Chap20.Lemma_20_10_3

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits
open scoped ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u}

/-- The structure presheaf of a ringed space, viewed as a presheaf of modules over itself. -/
abbrev structurePresheafModule (X : RingedSpace.{u}) : ringedSpacePresheafModules X :=
  PresheafOfModules.unit ((RingedSpace.ringCatSheaf X)).obj

/-- The degree-zero term of the canonical Čech cover chain complex, written as the coproduct of the
free Yoneda modules attached to the members of the open family. -/
noncomputable abbrev openCoverDegreeZeroModule (𝒰 : ι → Opens X.carrier) :
    ringedSpacePresheafModules X :=
  ∐ fun i : ι ↦ (yoneda ⋙ PresheafOfModules.free ((RingedSpace.ringCatSheaf X)).obj).obj (𝒰 i)

/-- The canonical augmentation from degree `0` of the Čech cover chain complex to the structure
presheaf, sending the distinguished generator of each summand to `1`. -/
noncomputable def openCoverDegreeZeroToStructure (𝒰 : ι → Opens X.carrier) :
    openCoverDegreeZeroModule 𝒰 ⟶ structurePresheafModule X :=
  Sigma.desc fun i ↦
    (PresheafOfModules.freeYonedaEquiv.symm
      (show (structurePresheafModule X).obj (op (𝒰 i)) from
        (1 : ((RingedSpace.ringCatSheaf X)).obj.obj (op (𝒰 i)))))

/-- The image presheaf of the canonical augmentation from degree `0` of the cover chain complex to
the structure presheaf. -/
noncomputable abbrev openCoverStructureImage (𝒰 : ι → Opens X.carrier) :
    ringedSpacePresheafModules X :=
  image (openCoverDegreeZeroToStructure 𝒰)

/-- The canonical monomorphism from the image presheaf of the cover augmentation into the
structure presheaf. -/
noncomputable abbrev openCoverStructureImageι (𝒰 : ι → Opens X.carrier) :
    openCoverStructureImage 𝒰 ⟶ structurePresheafModule X :=
  image.ι (openCoverDegreeZeroToStructure 𝒰)

-- Proof sketch: augment `openCoverChainComplex 𝒰` by the canonical map from degree `0` to the
-- structure presheaf. On sections over any open subset, this becomes the extended alternating
-- Čech complex from the textbook, and the explicit contracting homotopy there shows the augmented
-- complex is exact. Therefore the positive homology objects vanish, while degree-zero homology is
-- the image of the augmentation.
/-- Lemma 20.10.4: for a ringed space `X` and an open family `𝒰`, the homology presheaf of the
cover chain complex `K(\mathcal U)_\bullet` is canonically the image presheaf of the degree-zero
augmentation in degree `0`, and is zero in every other degree. -/
theorem openCoverChainComplex_homology_iso_coverImage_or_zero
    (𝒰 : ι → Opens X.carrier) (i : ℕ) :
    IsIsomorphic ((openCoverChainComplex 𝒰).homology i)
      (if h : i = 0 then openCoverStructureImage 𝒰 else 0) := sorry

-- Proof sketch: specialize the main homology computation to an index `i ≠ 0`; then the
-- right-hand side becomes the zero object, so the corresponding homology object is zero.
/-- Away from degree `0`, the homology of the cover chain complex vanishes. -/
theorem openCoverChainComplex_homology_isZero_of_ne_zero
    (𝒰 : ι → Opens X.carrier) {i : ℕ} (hi : i ≠ 0) :
    IsZero ((openCoverChainComplex 𝒰).homology i) := sorry

-- Proof sketch: evaluate the main homology computation at `i = 0`; the case distinction collapses
-- to the image presheaf of the canonical degree-zero augmentation.
/-- The degree-zero homology of the cover chain complex is the image presheaf of the canonical
augmentation to the structure presheaf. -/
theorem openCoverChainComplex_homology_zero_isomorphic_coverStructureImage
    (𝒰 : ι → Opens X.carrier) :
    IsIsomorphic ((openCoverChainComplex 𝒰).homology 0)
      (openCoverStructureImage 𝒰) := sorry

end AlgebraicGeometry.RingedSpace
