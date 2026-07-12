import Mathlib.Algebra.Homology.TotalComplexShift
import StacksProject_2024.Chap12.Definition_12_18_3

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
/-- Helper for Remark 12.18.5: the second-direction total-shift comparison contributes the
expected sign `(-1)^(p b)` when rewritten in the arithmetic normalization used for the target
statement. -/
@[reassoc]
lemma shifted_second_direction_total_component
    (n p q : ℤ) (h₂ : p + (q - b) = n + a) (h : p + q = n + (a + b)) :
    K.ιTotal (up ℤ) p q (n + (a + b)) h ≫
      (CochainComplex.shiftFunctorObjXIso (Tot(K)) b (n + a) (n + (a + b))
        (Int.add_assoc n a b).symm).inv ≫
        (K.totalShift₂Iso b).inv.f (n + a) =
      (p * b).negOnePow •
        ((K.shiftFunctor₂XXIso p (q - b) b q (Int.sub_add_cancel q b).symm).inv ≫
          (((shiftFunctor₂ C b).obj K).ιTotal (up ℤ) p (q - b) (n + a) h₂)) := by
  have h_shift : n + (a + b) = n + a + b := by
    omega
  -- This is exactly the owner component formula for `totalShift₂Iso`, specialized to the
  -- arithmetic normalization appearing in the bidegree-shift statement.
  simpa using
    (K.ι_totalShift₂Iso_inv_f b p (q - b) (n + a) h₂ q (n + (a + b)) h h_shift)

/-- Helper for Remark 12.18.5: after the second-direction shift is removed, the remaining
first-direction total-shift comparison introduces no additional sign. -/
@[reassoc]
lemma shifted_first_direction_total_component
    (n p q : ℤ) (h₁ : (p - a) + (q - b) = n) (h₂ : p + (q - b) = n + a) :
    (((shiftFunctor₂ C b).obj K).ιTotal (up ℤ) p (q - b) (n + a) h₂) ≫
      (CochainComplex.shiftFunctorObjXIso (Tot((shiftFunctor₂ C b).obj K)) a
        n (n + a) rfl).inv ≫
        (((shiftFunctor₂ C b).obj K).totalShift₁Iso a).inv.f n =
      (((shiftFunctor₂ C b).obj K).shiftFunctor₁XXIso (p - a) a p
        (Int.sub_add_cancel p a).symm (q - b)).inv ≫
        ((K[a, b]).ιTotal (up ℤ) (p - a) (q - b) n h₁) := by
  -- This is the owner component formula for `totalShift₁Iso`, with the target identified with
  -- the chosen notation `K[a, b]`.
  simpa [HomologicalComplex₂.bidegreeShift] using
    (((shiftFunctor₂ C b).obj K).ι_totalShift₁Iso_inv_f a (p - a) (q - b) n h₁ p (n + a) h₂
      rfl)

/-- Helper for Remark 12.18.5: the two associativity transports appearing in the shift-add
comparison induce the same morphism after postcomposition with `(K.totalShift₂Iso b).inv`. -/
lemma shift_add_transport_normalization (n : ℤ) :
    (Tot(K).XIsoOfEq (Int.add_assoc n a b).symm).hom ≫ (K.totalShift₂Iso b).inv.f (n + a) =
      (Tot(K).XIsoOfEq (Int.add_assoc n a b)).inv ≫ (K.totalShift₂Iso b).inv.f (n + a) := by
  -- Both sides are the same transported component; only proof-irrelevant equality witnesses differ.
  simp [HomologicalComplex.XIsoOfEq]

/-- Helper for Remark 12.18.5: the shift-add comparison followed by the shifted
second-direction total-shift map is the canonical nested-shift transport used by the owner
component formulas. -/
@[reassoc]
lemma shift_add_component_rewrite (n : ℤ) :
    (CochainComplex.shiftFunctorObjXIso (Tot(K)) (a + b) n (n + (a + b)) rfl).inv ≫
        (((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) b a (a + b)
          (add_comm b a)).hom.app (Tot(K))).f n) ≫
        (((shiftFunctor (CochainComplex C ℤ) a).map (K.totalShift₂Iso b).inv).f n) =
      (CochainComplex.shiftFunctorObjXIso (Tot(K)) b (n + a) (n + (a + b))
          (Int.add_assoc n a b).symm).inv ≫
        (K.totalShift₂Iso b).inv.f (n + a) ≫
        (CochainComplex.shiftFunctorObjXIso (Tot((shiftFunctor₂ C b).obj K)) a
          n (n + a) rfl).inv := by
  -- Rewrite the shift-add bridge through the canonical degree identifications.
  rw [← Category.assoc]
  rw [CochainComplex.shiftFunctorAdd'_hom_app_f']
  -- The only remaining discrepancy is the proof-irrelevant choice of associativity transport.
  simpa using shift_add_transport_normalization (K := K) (a := a) (b := b) (n := n)

/-- Helper for Remark 12.18.5: postcomposing the second-direction component formula with the
remaining first-direction transport preserves the source-route equality. -/
@[reassoc]
lemma shifted_second_direction_total_component_postcompose
    (n p q : ℤ) (h₂ : p + (q - b) = n + a) (h : p + q = n + (a + b)) :
    K.ιTotal (up ℤ) p q (n + (a + b)) h ≫
        ((CochainComplex.shiftFunctorObjXIso (Tot(K)) b (n + a) (n + (a + b))
            (Int.add_assoc n a b).symm).inv ≫
          (K.totalShift₂Iso b).inv.f (n + a) ≫
          (CochainComplex.shiftFunctorObjXIso (Tot((shiftFunctor₂ C b).obj K)) a
            n (n + a) rfl).inv) ≫
        ((((shiftFunctor₂ C b).obj K).totalShift₁Iso a).inv.f n) =
      ((p * b).negOnePow •
        ((K.shiftFunctor₂XXIso p (q - b) b q (Int.sub_add_cancel q b).symm).inv ≫
          (((shiftFunctor₂ C b).obj K).ιTotal (up ℤ) p (q - b) (n + a) h₂))) ≫
        (CochainComplex.shiftFunctorObjXIso (Tot((shiftFunctor₂ C b).obj K)) a
          n (n + a) rfl).inv ≫
        ((((shiftFunctor₂ C b).obj K).totalShift₁Iso a).inv.f n) := by
  -- Postcompose the owner second-direction formula with the remaining first-direction terms.
  simpa [Category.assoc] using congrArg
    (fun k ↦ k ≫
      (CochainComplex.shiftFunctorObjXIso (Tot((shiftFunctor₂ C b).obj K)) a
        n (n + a) rfl).inv ≫
      ((((shiftFunctor₂ C b).obj K).totalShift₁Iso a).inv.f n))
    (shifted_second_direction_total_component (K := K) (a := a) (b := b)
      (n := n) (p := p) (q := q) (h₂ := h₂) (h := h))

/-- Helper for Remark 12.18.5: inserting the first-direction component formula inside the signed
second-direction term gives the final shifted summand formula. -/
lemma shifted_first_direction_total_component_smul
    (n p q : ℤ) (h₁ : (p - a) + (q - b) = n) (h₂ : p + (q - b) = n + a) :
    (p * b).negOnePow •
      ((K.shiftFunctor₂XXIso p (q - b) b q (Int.sub_add_cancel q b).symm).inv ≫
        (((shiftFunctor₂ C b).obj K).ιTotal (up ℤ) p (q - b) (n + a) h₂) ≫
          (CochainComplex.shiftFunctorObjXIso (Tot((shiftFunctor₂ C b).obj K)) a
            n (n + a) rfl).inv ≫
          ((((shiftFunctor₂ C b).obj K).totalShift₁Iso a).inv.f n)) =
      (p * b).negOnePow •
        ((K.shiftFunctor₂XXIso p (q - b) b q (Int.sub_add_cancel q b).symm).inv ≫
          (((shiftFunctor₂ C b).obj K).shiftFunctor₁XXIso (p - a) a p
            (Int.sub_add_cancel p a).symm (q - b)).inv ≫
            ((K[a, b]).ιTotal (up ℤ) (p - a) (q - b) n h₁)) := by
  -- Apply the owner first-direction formula inside the scalar multiple.
  congr 1
  simpa [Category.assoc] using congrArg
    (fun k ↦ (K.shiftFunctor₂XXIso p (q - b) b q (Int.sub_add_cancel q b).symm).inv ≫ k)
    (shifted_first_direction_total_component (K := K) (a := a) (b := b)
      (n := n) (p := p) (q := q) (h₁ := h₁) (h₂ := h₂))

/-- Helper for Remark 12.18.5: the degree-`n` component of `totalShiftBidegreeIso` is the
source-proof composite of the shift-add bridge, the second-direction comparison, and the
first-direction comparison. -/
lemma totalShiftBidegreeIso_hom_component (n : ℤ) :
    (K.totalShiftBidegreeIso a b).hom.f n =
      (((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) b a (a + b)
        (add_comm b a)).hom.app (Tot(K))).f n) ≫
        (((shiftFunctor (CochainComplex C ℤ) a).map (K.totalShift₂Iso b).inv).f n) ≫
        ((((shiftFunctor₂ C b).obj K).totalShift₁Iso a).inv.f n) := by
  -- Unfold the chosen comparison and normalize the inverse of the shifted-map isomorphism.
  simpa [HomologicalComplex₂.totalShiftBidegreeIso, Functor.mapIso_inv, Category.assoc]

/-- Helper for Remark 12.18.5: if `(p, q)` contributes to total degree `n + (a + b)`, then the
shifted index `(p - a, q - b)` contributes to total degree `n`. -/
lemma shifted_bidegree_total_index
    (n p q : ℤ) (h : p + q = n + (a + b)) :
    (p - a) + (q - b) = n := by
  linarith

/-- Remark 12.18.5: on the summand indexed by `(p, q)`, the canonical bidegree-shift comparison
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
              (up ℤ) (p - a) (q - b) n
              (shifted_bidegree_total_index (a := a) (b := b) (n := n)
                (p := p) (q := q) h))) := by
  have h₂ : p + (q - b) = n + a := by
    dsimp [π] at h ⊢
    linarith
  have h₁ : (p - a) + (q - b) = n := by
    dsimp [π] at h ⊢
    linarith
  -- Expand the canonical comparison into the shift-add bridge, then the second-direction
  -- comparison, and finally the first-direction comparison.
  -- Route correction: the final proof keeps the source factorization through the shift-add
  -- bridge and normalizes that prefix before invoking the two owner component formulas.
  have h_expand := totalShiftBidegreeIso_hom_component (K := K) (a := a) (b := b) (n := n)
  have h_shift := shift_add_component_rewrite (K := K) (a := a) (b := b) (n := n)
  calc
    K.ιTotal (up ℤ) p q (n + (a + b)) h ≫
        (CochainComplex.shiftFunctorObjXIso (Tot(K)) (a + b)
          n (n + (a + b)) rfl).inv ≫
        (K.totalShiftBidegreeIso a b).hom.f n =
      K.ιTotal (up ℤ) p q (n + (a + b)) h ≫
        ((CochainComplex.shiftFunctorObjXIso (Tot(K)) (a + b)
            n (n + (a + b)) rfl).inv ≫
          (((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) b a (a + b)
            (add_comm b a)).hom.app (Tot(K))).f n) ≫
          (((shiftFunctor (CochainComplex C ℤ) a).map (K.totalShift₂Iso b).inv).f n)) ≫
        ((((shiftFunctor₂ C b).obj K).totalShift₁Iso a).inv.f n) := by
      rw [h_expand]
      simp [Category.assoc]
    _ =
      K.ιTotal (up ℤ) p q (n + (a + b)) h ≫
        ((CochainComplex.shiftFunctorObjXIso (Tot(K)) b (n + a) (n + (a + b))
            (Int.add_assoc n a b).symm).inv ≫
          (K.totalShift₂Iso b).inv.f (n + a) ≫
          (CochainComplex.shiftFunctorObjXIso (Tot((shiftFunctor₂ C b).obj K)) a
            n (n + a) rfl).inv) ≫
        ((((shiftFunctor₂ C b).obj K).totalShift₁Iso a).inv.f n) := by
      simpa [Category.assoc] using congrArg
        (fun k ↦ K.ιTotal (up ℤ) p q (n + (a + b)) h ≫
          (k ≫ ((((shiftFunctor₂ C b).obj K).totalShift₁Iso a).inv.f n))) h_shift
    _ =
      ((p * b).negOnePow •
        ((K.shiftFunctor₂XXIso p (q - b) b q (Int.sub_add_cancel q b).symm).inv ≫
          (((shiftFunctor₂ C b).obj K).ιTotal (up ℤ) p (q - b) (n + a) h₂))) ≫
        (CochainComplex.shiftFunctorObjXIso (Tot((shiftFunctor₂ C b).obj K)) a
          n (n + a) rfl).inv ≫
        ((((shiftFunctor₂ C b).obj K).totalShift₁Iso a).inv.f n) := by
      exact shifted_second_direction_total_component_postcompose (K := K) (a := a) (b := b)
        (n := n) (p := p) (q := q) (h₂ := h₂) (h := h)
    _ = (p * b).negOnePow •
        ((K.shiftFunctor₂XXIso p (q - b) b q (Int.sub_add_cancel q b).symm).inv ≫
          (((shiftFunctor₂ C b).obj K).shiftFunctor₁XXIso (p - a) a p
            (Int.sub_add_cancel p a).symm (q - b)).inv ≫
            ((K[a, b]).ιTotal
              (up ℤ) (p - a) (q - b) n
              (shifted_bidegree_total_index (a := a) (b := b) (n := n)
                (p := p) (q := q) h))) := by
      simpa [HomologicalComplex₂.bidegreeShift] using
        shifted_first_direction_total_component_smul (K := K) (a := a) (b := b)
          (n := n) (p := p) (q := q) (h₁ := h₁) (h₂ := h₂)

end HomologicalComplex₂
