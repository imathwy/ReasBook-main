import Mathlib
import StacksProject_2024.stacks_project.Chap06.Lemma_6_30_7
import StacksProject_2024.stacks_project.Chap26.Lemma_26_11_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Presheaf
open Opposite
open TopologicalSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the scheme-side standard-open owners
-- `Scheme.affineBasicOpen`, `Scheme.affineBasicOpen_coe`, `Scheme.basicOpen_mul`, and
-- `isAffineOpen_bot`; the Chapter 6 bridge from ordinary sheaves to basis sheaves is
-- `BasisSheaf.restrictFromSheaf`.

/-- The binary standard-open gluing condition on the affine-open basis of a scheme, together with
the requirement that the value on the empty affine open is a singleton. This is the source-facing
condition appearing in clause (3) of Lemma 26.11.7, expressed by unique gluing over binary
standard-open covers instead of by an injective equalizer map. -/
def AffineBasisStandardOpenGluingCondition
    {X : Scheme.{u}} (F : Presheaf.{max u v} (BasisOpen X.affineOpens)) : Prop :=
  let basisObj : X.affineOpens → BasisOpen X.affineOpens := fun U ↦ ⟨(U : X.Opens), U.2⟩
  let restrict :
      {U V : X.affineOpens} → ((U : X.Opens) ≤ (V : X.Opens)) →
        F.obj (op (basisObj V)) → F.obj (op (basisObj U)) :=
    fun {U V} h ↦
      let i : basisObj U ⟶ basisObj V := ⟨homOfLE h⟩
      F.map i.op
  let emptyU : X.affineOpens := ⟨⊥, by simpa using isAffineOpen_bot X⟩
  Subsingleton (F.obj (op (basisObj emptyU))) ∧ Nonempty (F.obj (op (basisObj emptyU))) ∧
    ∀ (U : X.affineOpens) (f g : Γ(X, (U : X.Opens))),
      (U : X.Opens) = X.basicOpen f ⊔ X.basicOpen g →
        ∀ s :
          F.obj (op (basisObj (X.affineBasicOpen f))) ×
            F.obj (op (basisObj (X.affineBasicOpen g))),
          @restrict
              (X.affineBasicOpen (f * g)) (X.affineBasicOpen f)
              (by
                rw [Scheme.affineBasicOpen_coe, Scheme.affineBasicOpen_coe, Scheme.basicOpen_mul]
                exact inf_le_left)
              s.1 =
            @restrict
              (X.affineBasicOpen (f * g)) (X.affineBasicOpen g)
              (by
                rw [Scheme.affineBasicOpen_coe, Scheme.affineBasicOpen_coe, Scheme.basicOpen_mul]
                exact inf_le_right)
              s.2 ↔
            ∃! t : F.obj (op (basisObj U)),
              @restrict
                  (X.affineBasicOpen f) U
                  (by
                    rw [Scheme.affineBasicOpen_coe]
                    exact X.basicOpen_le f)
                  t = s.1 ∧
                @restrict
                  (X.affineBasicOpen g) U
                  (by
                    rw [Scheme.affineBasicOpen_coe]
                    exact X.basicOpen_le g)
                  t = s.2

/-- Lemma 26.11.7 (1): a presheaf of sets on the affine-open basis of a scheme is the restriction
of a sheaf on the whole scheme if and only if it is a sheaf on that basis. -/
@[stacks 0F1A]
theorem exists_restrictFromSheaf_iff_isBasisSheaf
    {X : Scheme.{u}} (F : Presheaf.{max u v} (BasisOpen X.affineOpens)) :
    (∃ G : TopCat.Sheaf (Type (max u v)) X,
      (BasisSheaf.restrictFromSheaf (Scheme.isBasis_affineOpens X) G).obj = F) ↔
      F.IsBasisSheaf := sorry

/-- Lemma 26.11.7 (2): for a presheaf of sets on the affine-open basis of a scheme, being a sheaf
on that basis is equivalent to the empty-open singleton condition together with unique gluing over
every binary standard-open cover of an affine open. This is the source's clause (3), rewritten in
the equivalent unique-gluing form. -/
@[stacks 0F1A]
theorem isBasisSheaf_iff_affineBasisStandardOpenGluingCondition
    {X : Scheme.{u}} (F : Presheaf.{max u v} (BasisOpen X.affineOpens)) :
    F.IsBasisSheaf ↔ AffineBasisStandardOpenGluingCondition F := sorry

end AlgebraicGeometry.Scheme
