import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical quasi-separatedness owners
-- `AlgebraicGeometry.QuasiSeparated`,
-- `AlgebraicGeometry.quasiSeparatedSpace_iff_affine`, and
-- `AlgebraicGeometry.Scheme.quasiSeparatedSpace_of_isOpenCover`. The source item is therefore
-- recorded as two source-facing affine-open criteria around the existing `QuasiSeparated` owner.

variable {X S : Scheme.{u}}

/-- An open subset of a scheme is a finite union of affine opens if it is the union of finitely
many members of the canonical affine-open family. -/
def IsFiniteUnionOfAffineOpens (U : X.Opens) : Prop :=
  ∃ (ι : Type u) (_ : Finite ι) (V : ι → X.affineOpens),
    iSup (fun i ↦ (V i : X.Opens)) = U

/-- Lemma 26.21.6 (1): a morphism of schemes is quasi-separated if and only if, for every pair of
affine opens of the source which both map into a common affine open of the target, their
intersection is a finite union of affine opens of the source. -/
@[stacks 01KO]
theorem Scheme.Hom.quasiSeparated_iff_forall_affineOpens_inter_isFiniteUnionOfAffineOpens
    (f : X ⟶ S) :
    QuasiSeparated f ↔
      ∀ U V : X.affineOpens,
        (∃ W : S.affineOpens,
          (U : X.Opens) ≤ (Opens.map f.base).obj (W : S.Opens) ∧
            (V : X.Opens) ≤ (Opens.map f.base).obj (W : S.Opens)) →
          IsFiniteUnionOfAffineOpens ((U : X.Opens) ⊓ (V : X.Opens)) := sorry

/-- Lemma 26.21.6 (2): a morphism of schemes is quasi-separated if and only if the target admits
an affine open cover whose inverse images admit affine open covers with pairwise intersections that
are finite unions of affine opens of the source. -/
@[stacks 01KO]
theorem Scheme.Hom.quasiSeparated_iff_exists_affineOpenCover_preimage_inter_isFiniteUnionOfAffineOpens
    (f : X ⟶ S) :
    QuasiSeparated f ↔
      ∃ 𝒰 : S.AffineOpenCover,
        ∀ i : 𝒰.I₀,
          ∃ (ι : Type u) (_ : Finite ι) (V : ι → X.affineOpens),
            iSup (fun j ↦ (V j : X.Opens)) =
                (Opens.map f.base).obj ((𝒰.openCover.f i).opensRange) ∧
              ∀ j j',
                IsFiniteUnionOfAffineOpens ((V j : X.Opens) ⊓ (V j' : X.Opens)) := sorry

end AlgebraicGeometry
