import stacks_project.Chap12.Lemma_12_19_9
import stacks_project.Chap12.Lemma_12_19_12

open CategoryTheory CategoryTheory.Limits

universe u v

noncomputable section

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

namespace FilteredObject.Hom

open FilteredObject

variable {A B C : FilteredObject 𝒜}

/-
Source/core/bridge triage for Lemma 12.19.14:
- source-facing: the graded complex `gr^p(A) ⟶ gr^p(B) ⟶ gr^p(C)` and the quotient
  `gr^p(\ker β / \operatorname{im} α)`
- core/canonical owner: `ShortComplex 𝒜` and its homology API
- bridge/view: the canonical filtered projection
  `kernelFilteredObject β ⟶ B.subobjectSubquotientFilteredObject (image_le_kernel α.hom β.hom hcomp)`
  and the induced left-homology data on that owner short complex
-/

/-- Lemma 12.19.14: for a complex `A ⟶ B ⟶ C` of filtered objects in an abelian category with
strict maps `α` and `β`, the associated graded of `ker β / im α` is canonically isomorphic to the
homology of the graded complex `gr A ⟶ gr B ⟶ gr C`. -/
noncomputable def graded_homology_iso_graded_complex_homology
    (α : A ⟶ B) (β : B ⟶ C) (hcomp : α ≫ β = 0)
    (hα : Strict α) (hβ : Strict β) (p : ℤ) :
    let hcomp_hom : α.hom ≫ β.hom = 0 := congrArg FilteredObject.Hom.hom hcomp
    (B.subobjectSubquotientFilteredObject (image_le_kernel α.hom β.hom hcomp_hom)).gradedPiece p ≅
      (ShortComplex.mk (gradedPieceMap α p) (gradedPieceMap β p)
        (gradedPieceMap_comp_zero α β hcomp p)).homology :=
  let hcomp_hom : α.hom ≫ β.hom = 0 := congrArg FilteredObject.Hom.hom hcomp
  let S : ShortComplex 𝒜 :=
    ShortComplex.mk (gradedPieceMap α p) (gradedPieceMap β p)
      (gradedPieceMap_comp_zero α β hcomp p)
  let hS : S.LeftHomologyData :=
    { K := (kernelFilteredObject β).gradedPiece p
      H := (B.subobjectSubquotientFilteredObject (image_le_kernel α.hom β.hom hcomp_hom)).gradedPiece p
      i := gradedPieceMap (kernelι β) p
      π := gradedPieceMap (B.subobjectToSubquotient (image_le_kernel α.hom β.hom hcomp_hom)) p
      wi := gradedPieceMap_comp_zero (kernelι β) β (kernelι_comp β) p
      hi := by
        sorry
      wπ := by
        sorry
      hπ := by
        sorry }
  hS.homologyIso.symm

end FilteredObject.Hom

end CategoryTheory
