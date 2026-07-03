import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite

universe v u

namespace CategoryTheory

open Idempotents
open Limits

section

variable {C : Type u} [Category.{v} C] [Preadditive C]

/- Domain-style sampling for Lemma 12.4.2:
- primary domain: idempotent completeness of preadditive categories and the resulting direct-sum
  decomposition of idempotents;
- sampled owner API:
  `IsIdempotentComplete`,
  `isIdempotentComplete_iff_idempotents_have_kernels`,
  `IsIdempotentComplete.idempotents_split`,
  `isBinaryBilimitOfTotal`;
- source/core/bridge triage:
  `core/canonical`: `IsIdempotentComplete C`;
  `bridge/view`: the cokernel criterion obtained by passing the kernel criterion to `Cᵒᵖ`;
  `source-facing`: `CategoryTheory.karoubian_tfae`.

Primitive data are the ambient preadditive category and an idempotent endomorphism. The kernel
criterion and the split-idempotent package are owner-level API from mathlib; this file only adds
the dual cokernel bridge and packages the three textbook clauses into a TFAE statement.
-/
/-- In a preadditive category, idempotent completeness is equivalent to existence of a cokernel
for every idempotent endomorphism. -/
-- Proof sketch: pass to the opposite category, apply
-- `CategoryTheory.Idempotents.isIdempotentComplete_iff_idempotents_have_kernels`, and translate
-- kernels in `Cᵒᵖ` back to cokernels in `C`.
theorem isIdempotentComplete_iff_idempotents_have_cokernels :
    IsIdempotentComplete C ↔ ∀ (z : C) (p : End z) (_ : p ≫ p = p), HasCokernel p := by
  constructor
  · intro h z p hp
    have hk : HasKernel p.op :=
      (isIdempotentComplete_iff_idempotents_have_kernels Cᵒᵖ).1
        (isIdempotentComplete_iff_opposite.2 h) (op z) p.op
        (by simpa using congrArg Quiver.Hom.op hp)
    letI := hk
    let w : p ≫ (kernel.ι p.op).unop = 0 := by
      have h := congrArg Quiver.Hom.unop (kernel.condition p.op)
      change (p.op.unop ≫ (kernel.ι p.op).unop) = 0 at h
      simpa using h
    refine ⟨⟨CokernelCofork.ofπ (kernel.ι p.op).unop w, ?_⟩⟩
    exact KernelFork.IsLimit.ofιUnop (kernel.ι p.op) (kernel.condition p.op) (kernelIsKernel p.op)
  · intro h
    apply isIdempotentComplete_iff_opposite.1
    rw [isIdempotentComplete_iff_idempotents_have_kernels]
    intro z p hp
    letI : HasCokernel p.unop := h z.unop p.unop (by simpa using congrArg Quiver.Hom.unop hp)
    let w : (cokernel.π p.unop).op ≫ p = 0 := by
      have hπ := congrArg Quiver.Hom.op (cokernel.condition p.unop)
      change (cokernel.π p.unop).op ≫ p = 0 at hπ
      simpa using hπ
    refine ⟨⟨KernelFork.ofι (cokernel.π p.unop).op w, ?_⟩⟩
    exact CokernelCofork.IsColimit.ofπOp (cokernel.π p.unop) (cokernel.condition p.unop)
      (cokernelIsCokernel p.unop)

/-- In an idempotent-complete preadditive category, every idempotent is, after choosing a binary
biproduct decomposition, the projection onto the second summand. -/
theorem idempotent_is_second_summand_projection [IsIdempotentComplete C] {z : C}
    (p : z ⟶ z) (hp : p ≫ p = p) :
    ∃ (x y : C) (_ : HasBinaryBiproduct x y) (e : x ⊞ y ≅ z),
      p = e.inv ≫ biprod.snd ≫ biprod.inr ≫ e.hom := by
  rcases IsIdempotentComplete.idempotents_split z (𝟙 z - p)
      (idem_of_id_sub_idem p hp) with
    ⟨x, i, a, hi, ha⟩
  rcases IsIdempotentComplete.idempotents_split z p hp with ⟨y, j, q, hj, hq⟩
  have hjp : j ≫ p = j := by
    calc
      j ≫ p = j ≫ (q ≫ j) := by rw [hq]
      _ = j := by rw [← Category.assoc, hj, Category.id_comp]
  have hpj : j ≫ a = 0 := by
    have hjzero : j ≫ (𝟙 z - p) = 0 := by
      simp [hjp]
    have h : j ≫ a ≫ i = 0 := by
      change j ≫ (a ≫ i) = 0
      rw [ha]
      exact hjzero
    have h' : j ≫ a ≫ i ≫ a = 0 := by
      simpa [Category.assoc] using congrArg (fun f ↦ f ≫ a) h
    simpa [Category.assoc, hi] using h'
  have hqi : i ≫ q = 0 := by
    have h : i ≫ (𝟙 z - p) = i := by
      calc
        i ≫ (𝟙 z - p) = i ≫ (a ≫ i) := by rw [ha]
        _ = (i ≫ a) ≫ i := by rw [← Category.assoc]
        _ = i := by rw [hi, Category.id_comp]
    have hip : i ≫ p = 0 := by
      have h' : i + -(i ≫ p) = i := by
        simpa [sub_eq_add_neg, Category.assoc] using h
      have h'' := congrArg (fun f ↦ -i + f) h'
      simpa [add_assoc] using h''
    have h' : i ≫ q ≫ j = 0 := by
      change i ≫ (q ≫ j) = 0
      rw [hq]
      exact hip
    have h'' : i ≫ q ≫ j ≫ q = 0 := by
      simpa [Category.assoc] using congrArg (fun f ↦ f ≫ q) h'
    simpa [Category.assoc, hj] using h''
  have htotal : a ≫ i + q ≫ j = 𝟙 z := by
    rw [ha, hq, sub_add_cancel]
  let b : BinaryBicone x y :=
    { pt := z
      fst := a
      snd := q
      inl := i
      inr := j
      inl_fst := hi
      inl_snd := hqi
      inr_fst := hpj
      inr_snd := hj }
  letI : HasBinaryBiproduct x y := hasBinaryBiproduct_of_total b htotal
  refine ⟨x, y, ‹HasBinaryBiproduct x y›,
    (biprod.uniqueUpToIso x y (isBinaryBilimitOfTotal b htotal)).symm, ?_⟩
  calc
    p = q ≫ j := hq.symm
    _ = biprod.lift a q ≫ biprod.snd ≫ biprod.inr ≫ biprod.desc i j := by
      simp

/-- Lemma 12.4.2: for a preadditive category, the following are equivalent: the category is
Karoubian, every idempotent endomorphism has a cokernel, and every idempotent endomorphism is the
projection onto the second summand in some direct-sum decomposition. -/
-- Proof sketch: use `isIdempotentComplete_iff_idempotents_have_cokernels` for `(1) ↔ (2)`. If
-- the category is idempotent complete, split the idempotent and apply the direct-sum criterion of
-- Remark `12.3.6` to obtain clause `(3)`. Conversely, clause `(3)` already exhibits a splitting
-- of the idempotent, hence gives clause `(1)`.
lemma karoubian_tfae :
    List.TFAE
      [ IsIdempotentComplete C
      , ∀ (z : C) (p : End z) (_ : p ≫ p = p), HasCokernel p
      , ∀ (z : C) (p : End z) (_ : p ≫ p = p),
          ∃ (x y : C) (_ : HasBinaryBiproduct x y) (e : x ⊞ y ≅ z),
            p = e.inv ≫ biprod.snd ≫ biprod.inr ≫ e.hom
      ] := by
  tfae_have 1 ↔ 2 := by
    exact isIdempotentComplete_iff_idempotents_have_cokernels
  tfae_have 1 → 3 := by
    intro h z p hp
    letI := h
    exact idempotent_is_second_summand_projection p hp
  tfae_have 3 → 1 := by
    intro h
    refine ⟨?_⟩
    intro z p hp
    rcases h z p hp with ⟨x, y, _, e, rfl⟩
    refine ⟨y, biprod.inr ≫ e.hom, e.inv ≫ biprod.snd, ?_, ?_⟩
    · simp
    · simp [Category.assoc]
  tfae_finish

end

end CategoryTheory
