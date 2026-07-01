import Mathlib.Algebra.Homology.TotalComplexShift
import stacks_project.Chap12.Definition_12_18_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Category ComplexShape Limits
open HomologicalComplex₂
open scoped HomologicalComplex₂

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
variable (a b : ℤ) [K.HasTotal (up ℤ)]

/- Domain-style sampling for Remark 12.18.5:
- primary domain: compatibility of totalization with bidegree shifts of a cohomological
  bicomplex;
- sampled owner declarations:
  `HomologicalComplex₂.totalShift₁Iso`,
  `HomologicalComplex₂.totalShift₂Iso`,
  `HomologicalComplex₂.shiftFunctor₁₂CommIso`,
  `HomologicalComplex₂.totalShift₁Iso_trans_totalShift₂Iso`;
- best owner abstraction:
  `source-facing`: the bidegree-shifted bicomplex `K[a, b]`,
  `core/canonical`: mathlib's `shiftFunctor₁`, `shiftFunctor₂`, and their total-shift
    comparison isomorphisms,
  `bridge/view`: the totalization comparison `K.totalShiftBidegreeIso a b`;
- primitive data: the bicomplex `K`;
- derived API: the notation `K[a, b]` for the bicomplex shifted in bidegree `(a, b)` and the
  specific bridge/view comparison from `Tot(K)⟦a + b⟧` to `Tot(K[a, b])`.

This file should therefore expose the source-facing bidegree shift itself as a thin abbreviation
over the canonical shift functors, and state the totalization comparison using that notation. -/
#check HomologicalComplex₂.totalShift₁Iso_trans_totalShift₂Iso

namespace HomologicalComplex₂

/-- The bicomplex obtained from `K` by shifting bidegrees by `(a, b)`. -/
abbrev bidegreeShift (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (a b : ℤ) :
    HomologicalComplex₂ C (up ℤ) (up ℤ) :=
  (shiftFunctor₁ C a).obj ((shiftFunctor₂ C b).obj K)

scoped[HomologicalComplex₂] notation:max K:max "[" a ", " b "]" =>
  HomologicalComplex₂.bidegreeShift K a b

open scoped HomologicalComplex₂

/-- The bridge/view comparison from the total complex shifted by `a + b` to the total complex of
the bidegree-shifted bicomplex `K[a, b]`. -/
noncomputable def totalShiftBidegreeIso :
    Tot(K)⟦a + b⟧ ≅ Tot(K[a, b]) :=
  show Tot(K)⟦a + b⟧ ≅ Tot((shiftFunctor₁ C a).obj ((shiftFunctor₂ C b).obj K)) from
    ((((shiftFunctor₂ C b).obj K).totalShift₁Iso a) ≪≫
        (shiftFunctor _ a).mapIso (K.totalShift₂Iso b) ≪≫
        ((shiftFunctorAdd' _ b a (a + b) (add_comm b a)).app (Tot(K))).symm).symm

-- Proof sketch: expand `K.totalShiftBidegreeIso a b` and apply the owner component formulas
-- `ι_totalShift₁Iso_inv_f` and `ι_totalShift₂Iso_inv_f`. The only nontrivial sign comes from
-- `totalShift₂Iso`, giving `(-1)^(p b)`.
/-- On the summand indexed by `(p, q)`, the canonical bidegree-shift comparison
`K.totalShiftBidegreeIso a b` acts by the sign `(-1)^(p b)` and sends it to the shifted summand
`(p - a, q - b)`. -/
@[reassoc]
theorem ι_totalShiftBidegreeIso_hom_f
    (n p q : ℤ) (h : p + q = n + (a + b)) :
    K.ιTotal (up ℤ) p q (n + (a + b)) h ≫
        (CochainComplex.shiftFunctorObjXIso (Tot(K)) (a + b)
          n (n + (a + b)) rfl).inv ≫
        (K.totalShiftBidegreeIso a b).hom.f n =
      (p * b).negOnePow •
        ((K.shiftFunctor₂XXIso p (q - b) b q (Int.sub_add_cancel q b).symm).inv ≫
          (((shiftFunctor₂ C b).obj K).shiftFunctor₁XXIso (p - a) a p
            (Int.sub_add_cancel p a).symm (q - b)).inv ≫
            ((K[a, b]).ιTotal
              (up ℤ) (p - a) (q - b) n (by
                dsimp [π] at h ⊢
                linarith))) := sorry

end HomologicalComplex₂
