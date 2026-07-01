import Mathlib
import stacks_project.Chap21.Definition_21_31_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.GrothendieckTopology

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory.GrothendieckTopology

section

variable (SmallSheaf QcSheaf : LCCat.{u} → Type (u + 1))
variable [∀ X : LCCat.{u}, Category.{u} (SmallSheaf X)]
variable [∀ X : LCCat.{u}, Category.{u} (QcSheaf X)]
variable [∀ X : LCCat.{u}, Abelian (SmallSheaf X)]
variable [∀ X : LCCat.{u}, Abelian (QcSheaf X)]
variable [∀ X : LCCat.{u}, HasDerivedCategory (SmallSheaf X)]
variable [∀ X : LCCat.{u}, HasDerivedCategory (QcSheaf X)]

variable (smallAbelianSheafCohomology :
  ∀ X : LCCat.{u}, SmallSheaf X → ℕ → AddCommGrpCat.{u + 1})
variable (qcAbelianSheafCohomology :
  ∀ X : LCCat.{u}, QcSheaf X → ℕ → AddCommGrpCat.{u + 1})
variable (smallAbelianSheafHypercohomology :
  ∀ X : LCCat.{u}, DerivedCategory (SmallSheaf X) → ℕ → AddCommGrpCat.{u + 1})
variable (qcAbelianSheafHypercohomology :
  ∀ X : LCCat.{u}, DerivedCategory (QcSheaf X) → ℕ → AddCommGrpCat.{u + 1})
variable (smallDplus :
  ∀ X : LCCat.{u}, ObjectProperty (DerivedCategory (SmallSheaf X)))
variable (aInverseAb : ∀ X : LCCat.{u}, SmallSheaf X ⥤ QcSheaf X)
variable (aInverseDerived :
  ∀ X : LCCat.{u}, DerivedCategory (SmallSheaf X) ⥤ DerivedCategory (QcSheaf X))
variable (smallConstantAbelianSheaf :
  ∀ X : LCCat.{u}, AddCommGrpCat.{u + 1} → SmallSheaf X)
variable (qcConstantAbelianSheaf :
  ∀ X : LCCat.{u}, AddCommGrpCat.{u + 1} → QcSheaf X)

-- Proof sketch: apply Lemma `21.31.11` to the degree-zero complex attached to `ℱ` and use
-- Remark `21.14.4` to identify the resulting derived global-sections comparison with the
-- degree-`n` cohomology groups on the small and qc sites.
/-- Lemma 21.31.12 (1): for an abelian sheaf `\mathcal F` on `X ∈ LC_{qc}`, the global
cohomology `H^n(X, \mathcal F)` is canonically isomorphic to the qc cohomology
`H^n_{qc}(X, a_X^{-1}\mathcal F)`. -/
theorem smallCohomology_iso_qcCohomology_of_aInverse
    (X : LCCat.{u}) (ℱ : SmallSheaf X) (n : ℕ) :
    IsIsomorphic
      (smallAbelianSheafCohomology X ℱ n)
      (qcAbelianSheafCohomology X ((aInverseAb X).obj ℱ) n) := sorry

-- Proof sketch: combine Lemma `21.31.11`, which identifies `K` with `R a_{X,*} a_X^{-1} K` for
-- bounded-below `K`, with Remark `21.14.4` to compare derived global sections on the small and qc
-- sites, then pass to degree-`n` homology.
/-- Lemma 21.31.12 (2): for `K ∈ D^+(X)`, the degree-`n` hypercohomology `H^n(X, K)` is
canonically isomorphic to the qc hypercohomology `H^n_{qc}(X, a_X^{-1} K)`. -/
theorem smallHypercohomology_iso_qcHypercohomology_of_aInverse
    (X : LCCat.{u})
    (K : DerivedCategory (SmallSheaf X))
    (hK : smallDplus X K)
    (n : ℕ) :
    IsIsomorphic
      (smallAbelianSheafHypercohomology X K n)
      (qcAbelianSheafHypercohomology X ((aInverseDerived X).obj K) n) := sorry

-- Proof sketch: apply clause `(1)` to the constant abelian sheaf `\underline A`; the inverse
-- image of a constant sheaf along the qc localization is again the constant sheaf with value `A`.
/-- Lemma 21.31.12 (3): for an abelian group `A`, the cohomology of the constant sheaf
`\underline A` on `X` is canonically isomorphic to the qc cohomology of the constant sheaf
`\underline A` on `LC_{qc}/X`. -/
theorem constantSheaf_smallCohomology_iso_qcCohomology
    (X : LCCat.{u}) (A : AddCommGrpCat.{u + 1}) (n : ℕ) :
    IsIsomorphic
      (smallAbelianSheafCohomology X (smallConstantAbelianSheaf X A) n)
      (qcAbelianSheafCohomology X (qcConstantAbelianSheaf X A) n) := sorry

end

end CategoryTheory.GrothendieckTopology
