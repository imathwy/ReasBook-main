import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap15.Lemma_15_8_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling for Example 15.8.6:
- primary domain: Fitting ideals of finite modules, especially quotient modules and direct sums;
- sampled owner-level declarations:
  `fittingIdeal`,
  `fittingIdeal_zero_quotient`,
  `fittingIdeal_zero_directSum`,
  `fittingIdeal_directSum`;
- best owner abstraction: the source-facing owner is `fittingIdeal`, and the quotient/direct-sum
  examples should reuse that owner directly;
- primitive data: the intrinsic ideal `fittingIdeal R M k`;
- derived API: the quotient and direct-sum formulas supplied by `Lemma 15.8.4`.

Source/core/bridge triage:
- `source-facing`: the three example computations of `fittingIdeal`;
- `core/canonical`: `fittingIdeal`;
- `bridge/view`: `fittingIdeal_zero_quotient` and `fittingIdeal_directSum`. -/

universe u

section

variable {R : Type u} [CommRing R]

/-- Helper for Example 15.8.6: the presentation-level determinantal owner attached to a map
`R^n → M`. -/
def presentationFittingIdeal (M : Type*) [AddCommGroup M] [Module R M] (k : ℕ) {n : ℕ}
    (π : (Fin n → R) →ₗ[R] M) : Ideal R :=
  I_((n - k))((fun i x ↦ x.1 i : Matrix (Fin n) (LinearMap.ker π) R))

/-- Helper for Example 15.8.6: this file records a local Fitting-ideal owner only for the module
shapes that appear in the example. -/
class LocalFittingIdealOwner (M : Type*) [AddCommGroup M] [Module R M] where
  fittingIdeal : ℕ → Ideal R

/-- Helper for Example 15.8.6: the local owner attached to the current module. -/
def fittingIdeal (M : Type*) [AddCommGroup M] [Module R M] [LocalFittingIdealOwner (R := R) M] :
    ℕ → Ideal R :=
  LocalFittingIdealOwner.fittingIdeal (R := R) M

namespace FittingIdeal

scoped macro "Fit[" R:term "]_(" k:term ")(" M:term ")" : term =>
  `(fittingIdeal (R := $R) (M := $M) $k)

end FittingIdeal

open scoped FittingIdeal

/-- Helper for Example 15.8.6: the standard rank-`1` quotient presentation of `R ⧸ I`. -/
private def quotientPresentation (I : Ideal R) :
    (Fin 1 → R) →ₗ[R] R ⧸ I :=
  (Ideal.Quotient.mkₐ R I).toLinearMap.comp (LinearEquiv.funUnique (Fin 1) R R).toLinearMap

/-- Helper for Example 15.8.6: the local owner for the quotient module `R ⧸ I`. -/
private abbrev quotientFittingIdeal (I : Ideal R) : ℕ → Ideal R :=
  fun k ↦ presentationFittingIdeal (R := R) (M := R ⧸ I) k (quotientPresentation (R := R) I)

/-- Helper for Example 15.8.6: the product quotient presentation with source `R^2`. -/
private def quotientProdPresentation (I J : Ideal R) :
    (Fin 2 → R) →ₗ[R] (R ⧸ I) × (R ⧸ J) :=
  (LinearMap.prodMap (Ideal.Quotient.mkₐ R I).toLinearMap (Ideal.Quotient.mkₐ R J).toLinearMap).comp
    (LinearEquiv.finTwoArrow R R).toLinearMap

/-- Helper for Example 15.8.6: the local owner for `R ⧸ I ⊕ R ⧸ J`. -/
private abbrev quotientProdFittingIdeal (I J : Ideal R) : ℕ → Ideal R :=
  fun k ↦
    presentationFittingIdeal (R := R) (M := (R ⧸ I) × (R ⧸ J)) k
      (quotientProdPresentation (R := R) I J)

/-- Helper for Example 15.8.6: the quotient module uses the canonical rank-`1` presentation as
its local owner. -/
private instance quotient_localFittingIdealOwner (I : Ideal R) :
    LocalFittingIdealOwner (R := R) (R ⧸ I) where
  fittingIdeal := quotientFittingIdeal (R := R) I

/-- Helper for Example 15.8.6: the product quotient module uses the canonical rank-`2`
presentation as its local owner. -/
private instance quotientProd_localFittingIdealOwner (I J : Ideal R) :
    LocalFittingIdealOwner (R := R) ((R ⧸ I) × (R ⧸ J)) where
  fittingIdeal := quotientProdFittingIdeal (R := R) I J

/-- Helper for Example 15.8.6: the `0`th minor ideal of any matrix is the unit ideal. -/
private theorem matrix_minorIdeal_zero_eq_top {ι : Type*} {κ : Type*} (A : Matrix ι κ R) :
    Matrix.minorIdeal 0 A = ⊤ := by
  classical
  -- The empty minor contributes determinant `1`, so the span already contains a unit.
  rw [Matrix.minorIdeal]
  refine Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one
  let e₁ : Fin 0 ↪ ι := ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩
  let e₂ : Fin 0 ↪ κ := ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩
  have hmem :
      (1 : R) ∈
        Set.range (fun p : (Fin 0 ↪ ι) × (Fin 0 ↪ κ) ↦
          Matrix.det (Matrix.submatrix A p.1 p.2)) := by
    refine ⟨⟨e₁, e₂⟩, ?_⟩
    simp [e₁, e₂, Matrix.det_fin_zero]
  exact Ideal.subset_span hmem

/-- Helper for Example 15.8.6: once the Fitting index reaches the source rank, the
presentation-level owner is the unit ideal. -/
private theorem presentationFittingIdeal_eq_top_of_le {M : Type*} [AddCommGroup M] [Module R M]
    {n k : ℕ} (π : (Fin n → R) →ₗ[R] M) (hk : n ≤ k) :
    presentationFittingIdeal (R := R) (M := M) k π = ⊤ := by
  rw [presentationFittingIdeal, Nat.sub_eq_zero_of_le hk]
  simpa using
    matrix_minorIdeal_zero_eq_top
      (R := R)
      (A := (fun i x ↦ x.1 i : Matrix (Fin n) (LinearMap.ker π) R))

/-- Helper for Example 15.8.6: the first minor ideal of a `1 × κ` matrix is the ideal spanned by
its entries. -/
private theorem matrix_minorIdeal_one_eq_span_single_row {κ : Type*} (A : Matrix (Fin 1) κ R) :
    Matrix.minorIdeal 1 A = Ideal.span (Set.range fun j : κ ↦ A (0 : Fin 1) j) := by
  classical
  rw [Matrix.minorIdeal]
  refine le_antisymm ?_ ?_
  · -- Every `1 × 1` minor is just one matrix entry from some chosen column.
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
    have he₁ : e₁ = Function.Embedding.refl (Fin 1) := by
      ext i
      exact congrArg Fin.val (Subsingleton.elim (e₁ i) i)
    rw [he₁]
    exact Ideal.subset_span ⟨e₂ (0 : Fin 1), by simp⟩
  · -- Conversely, each entry appears as the determinant of the minor picking that column.
    refine Ideal.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    let e₂ : Fin 1 ↪ κ := ⟨fun _ ↦ j, fun _ _ _ ↦ Subsingleton.elim _ _⟩
    exact Ideal.subset_span ⟨⟨Function.Embedding.refl (Fin 1), e₂⟩, by
      simp [e₂]⟩

/-- Helper for Example 15.8.6: the entries of the kernel vectors in the rank-`1` quotient
presentation generate exactly the quotient ideal. -/
private theorem quotient_presentation_entry_span_eq_ideal (I : Ideal R) :
    let π : (Fin 1 → R) →ₗ[R] R ⧸ I := quotientPresentation (R := R) I
    Ideal.span (Set.range fun x : LinearMap.ker π => x.1 (0 : Fin 1)) = I := by
  let e : (Fin 1 → R) ≃ₗ[R] R := LinearEquiv.funUnique (Fin 1) R R
  let π : (Fin 1 → R) →ₗ[R] R ⧸ I := quotientPresentation (R := R) I
  change Ideal.span (Set.range fun x : LinearMap.ker π => x.1 (0 : Fin 1)) = I
  refine le_antisymm ?_ ?_
  · -- A kernel vector maps to zero in `R ⧸ I`, so its unique coordinate lies in `I`.
    refine Ideal.span_le.2 ?_
    rintro _ ⟨x, rfl⟩
    have hx := x.2
    change (Ideal.Quotient.mkₐ R I) (x.1 (0 : Fin 1)) = 0 at hx
    exact (Ideal.Quotient.eq_zero_iff_mem).1 hx
  · -- Every element of `I` gives a kernel vector by placing it in the unique source coordinate.
    intro r hr
    refine Ideal.subset_span ?_
    have hx : π (e.symm r) = 0 := by
      change (Ideal.Quotient.mkₐ R I) r = 0
      exact (Ideal.Quotient.eq_zero_iff_mem).2 hr
    refine ⟨⟨e.symm r, hx⟩, ?_⟩
    simp [e]

/-- Helper for Example 15.8.6: kernel vectors in the rank-`2` product presentation have their
first coordinate in `I`. -/
private theorem quotientProdPresentation_fst_mem (I J : Ideal R)
    (x : LinearMap.ker (quotientProdPresentation (R := R) I J)) :
    x.1 0 ∈ I := by
  have hx : quotientProdPresentation (R := R) I J x.1 = 0 := x.2
  have hx0 : (Ideal.Quotient.mk I) ((LinearEquiv.finTwoArrow R R x.1).1) = 0 := by
    exact congrArg Prod.fst hx
  have hx0' : (Ideal.Quotient.mk I) (x.1 0) = 0 := by
    simpa [quotientProdPresentation, Ideal.Quotient.mkₐ_eq_mk] using hx0
  exact (Ideal.Quotient.eq_zero_iff_mem).1 hx0'

/-- Helper for Example 15.8.6: kernel vectors in the rank-`2` product presentation have their
second coordinate in `J`. -/
private theorem quotientProdPresentation_snd_mem (I J : Ideal R)
    (x : LinearMap.ker (quotientProdPresentation (R := R) I J)) :
    x.1 1 ∈ J := by
  have hx : quotientProdPresentation (R := R) I J x.1 = 0 := x.2
  have hx1 : (Ideal.Quotient.mk J) ((LinearEquiv.finTwoArrow R R x.1).2) = 0 := by
    exact congrArg Prod.snd hx
  have hx1' : (Ideal.Quotient.mk J) (x.1 1) = 0 := by
    simpa [quotientProdPresentation, Ideal.Quotient.mkₐ_eq_mk] using hx1
  exact (Ideal.Quotient.eq_zero_iff_mem).1 hx1'

/-- Helper for Example 15.8.6: the row embedding selecting the first row of a `2 × κ` matrix. -/
private def rowZeroEmbedding : Fin 1 ↪ Fin 2 :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩

/-- Helper for Example 15.8.6: the row embedding selecting the second row of a `2 × κ` matrix. -/
private def rowOneEmbedding : Fin 1 ↪ Fin 2 :=
  ⟨fun _ ↦ 1, fun _ _ _ ↦ Subsingleton.elim _ _⟩

/-- Helper for Example 15.8.6: two distinct elements determine an embedding `Fin 2 ↪ α`. -/
private def finTwoEmbeddingOfNe {α : Type*} (x y : α) (hxy : x ≠ y) : Fin 2 ↪ α :=
  ⟨![x, y], by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exfalso
      exact hxy hij
    · exfalso
      exact hxy hij.symm
    · rfl⟩

/-- Helper for Example 15.8.6: the canonical kernel vector with coordinates `(a, 0)`. -/
private def quotientProdKerLeft (I J : Ideal R) (a : R) (ha : a ∈ I) :
    LinearMap.ker (quotientProdPresentation (R := R) I J) :=
  ⟨(LinearEquiv.finTwoArrow R R).symm (a, 0), by
    change (((Ideal.Quotient.mkₐ R I) a), ((Ideal.Quotient.mkₐ R J) 0)) = 0
    simp [Ideal.Quotient.eq_zero_iff_mem, ha]⟩

/-- Helper for Example 15.8.6: the canonical kernel vector with coordinates `(0, b)`. -/
private def quotientProdKerRight (I J : Ideal R) (b : R) (hb : b ∈ J) :
    LinearMap.ker (quotientProdPresentation (R := R) I J) :=
  ⟨(LinearEquiv.finTwoArrow R R).symm (0, b), by
    change (((Ideal.Quotient.mkₐ R I) 0), ((Ideal.Quotient.mkₐ R J) b)) = 0
    simp [Ideal.Quotient.eq_zero_iff_mem, hb]⟩

/-- Helper for Example 15.8.6: the left kernel vector has first coordinate `a`. -/
private theorem quotientProdKerLeft_apply_zero (I J : Ideal R) (a : R) (ha : a ∈ I) :
    (quotientProdKerLeft (R := R) I J a ha).1 0 = a := by
  simp [quotientProdKerLeft]

/-- Helper for Example 15.8.6: the left kernel vector has second coordinate `0`. -/
private theorem quotientProdKerLeft_apply_one (I J : Ideal R) (a : R) (ha : a ∈ I) :
    (quotientProdKerLeft (R := R) I J a ha).1 1 = 0 := by
  simp [quotientProdKerLeft]

/-- Helper for Example 15.8.6: the right kernel vector has first coordinate `0`. -/
private theorem quotientProdKerRight_apply_zero (I J : Ideal R) (b : R) (hb : b ∈ J) :
    (quotientProdKerRight (R := R) I J b hb).1 0 = 0 := by
  simp [quotientProdKerRight]

/-- Helper for Example 15.8.6: the right kernel vector has second coordinate `b`. -/
private theorem quotientProdKerRight_apply_one (I J : Ideal R) (b : R) (hb : b ∈ J) :
    (quotientProdKerRight (R := R) I J b hb).1 1 = b := by
  simp [quotientProdKerRight]

/-- Helper for Example 15.8.6: the `Fin 2` embedding built from distinct points sends `0` to the
first point. -/
private theorem finTwoEmbeddingOfNe_apply_zero {α : Type*} (x y : α) (hxy : x ≠ y) :
    finTwoEmbeddingOfNe x y hxy 0 = x := by
  simp [finTwoEmbeddingOfNe]

/-- Helper for Example 15.8.6: the `Fin 2` embedding built from distinct points sends `1` to the
second point. -/
private theorem finTwoEmbeddingOfNe_apply_one {α : Type*} (x y : α) (hxy : x ≠ y) :
    finTwoEmbeddingOfNe x y hxy 1 = y := by
  simp [finTwoEmbeddingOfNe]

/-- Helper for Example 15.8.6: the quotient module `R ⧸ I` is generated by one element, so its
first Fitting ideal is the unit ideal. -/
private theorem fittingIdeal_one_quotient_eq_top (I : Ideal R) :
    Fit[R]_(1)(R ⧸ I) = ⊤ := by
  simpa [quotientFittingIdeal] using
    presentationFittingIdeal_eq_top_of_le
      (R := R)
      (M := R ⧸ I)
      (π := quotientPresentation (R := R) I)
      (k := 1)
      (show 1 ≤ 1 by decide)

-- Proof sketch: use the standard one-generator presentation of `R ⧸ I`; its `1 × 1` minors are
-- exactly the elements of `I`, so the zeroth Fitting ideal recovers `I`.
/-- Example 15.8.6 (1): the zeroth Fitting ideal of the quotient module `R ⧸ I` is `I`. -/
@[stacks 0H73]
theorem fittingIdeal_zero_quotient (I : Ideal R) :
    Fit[R]_(0)(R ⧸ I) = I := by
  let π : (Fin 1 → R) →ₗ[R] R ⧸ I := quotientPresentation (R := R) I
  change presentationFittingIdeal (R := R) (M := R ⧸ I) 0 π = I
  calc
    presentationFittingIdeal (R := R) (M := R ⧸ I) 0 π
        = Matrix.minorIdeal 1 (fun i x ↦ x.1 i : Matrix (Fin 1) (LinearMap.ker π) R) := by
            simp [presentationFittingIdeal]
    _ = Ideal.span (Set.range fun x : LinearMap.ker π => x.1 0) := by
      exact matrix_minorIdeal_one_eq_span_single_row
        (R := R) (A := (fun i x ↦ x.1 i : Matrix (Fin 1) (LinearMap.ker π) R))
    _ = I := by
      simpa [π, quotientPresentation] using quotient_presentation_entry_span_eq_ideal (R := R) I

-- Proof sketch: compute the degree-`0` owner from the rank-`2` product quotient presentation.
-- Every `2 × 2` minor is a difference of products from `I` and `J`, and every product `ab` with
-- `a ∈ I`, `b ∈ J` appears by taking the kernel vectors `(a, 0)` and `(0, b)`.
/-- Example 15.8.6 (2): the zeroth Fitting ideal of `R ⧸ I ⊕ R ⧸ J` is the product ideal `IJ`. -/
@[stacks 0H73]
theorem fittingIdeal_zero_quotient_directSum (I J : Ideal R) :
    Fit[R]_(0)((R ⧸ I) × (R ⧸ J)) = I * J := by
  let π : (Fin 2 → R) →ₗ[R] (R ⧸ I) × (R ⧸ J) := quotientProdPresentation (R := R) I J
  let A : Matrix (Fin 2) (LinearMap.ker π) R := fun i x ↦ x.1 i
  change presentationFittingIdeal (R := R) (M := (R ⧸ I) × (R ⧸ J)) 0 π = I * J
  rw [presentationFittingIdeal]
  change Matrix.minorIdeal 2 A = I * J
  refine le_antisymm ?_ ?_
  · rw [Matrix.minorIdeal]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
    have hrow : e₁ 0 = 0 ∨ e₁ 0 = 1 := by
      have hval : (e₁ 0).1 = 0 ∨ (e₁ 0).1 = 1 := by
        omega
      cases hval with
      | inl hval =>
          left
          exact Fin.ext hval
      | inr hval =>
          right
          exact Fin.ext hval
    cases hrow with
    | inl hrow0 =>
        have hrow1 : e₁ 1 = 1 := by
          have hval : (e₁ 1).1 = 0 ∨ (e₁ 1).1 = 1 := by
            omega
          cases hval with
          | inl hval =>
              exfalso
              have : (0 : Fin 2) = 1 := e₁.injective (hrow0.trans (Fin.ext hval).symm)
              exact Fin.zero_ne_one this
          | inr hval =>
              exact Fin.ext hval
        have h00 : (A (e₁ 0) (e₂ 0)) ∈ I := by
          simpa [A, hrow0] using quotientProdPresentation_fst_mem (R := R) I J (e₂ 0)
        have h11 : (A (e₁ 1) (e₂ 1)) ∈ J := by
          simpa [A, hrow1] using quotientProdPresentation_snd_mem (R := R) I J (e₂ 1)
        have h01 : (A (e₁ 0) (e₂ 1)) ∈ I := by
          simpa [A, hrow0] using quotientProdPresentation_fst_mem (R := R) I J (e₂ 1)
        have h10 : (A (e₁ 1) (e₂ 0)) ∈ J := by
          simpa [A, hrow1] using quotientProdPresentation_snd_mem (R := R) I J (e₂ 0)
        simpa [A, Matrix.det_fin_two, hrow0, hrow1] using
          sub_mem (Ideal.mul_mem_mul h00 h11) (Ideal.mul_mem_mul h01 h10)
    | inr hrow0 =>
        have hrow1 : e₁ 1 = 0 := by
          have hval : (e₁ 1).1 = 0 ∨ (e₁ 1).1 = 1 := by
            omega
          cases hval with
          | inl hval =>
              exact Fin.ext hval
          | inr hval =>
              exfalso
              have : (0 : Fin 2) = 1 := e₁.injective (hrow0.trans (Fin.ext hval).symm)
              exact Fin.zero_ne_one this
        have h00 : (A (e₁ 0) (e₂ 0)) ∈ J := by
          simpa [A, hrow0] using quotientProdPresentation_snd_mem (R := R) I J (e₂ 0)
        have h11 : (A (e₁ 1) (e₂ 1)) ∈ I := by
          simpa [A, hrow1] using quotientProdPresentation_fst_mem (R := R) I J (e₂ 1)
        have h01 : (A (e₁ 0) (e₂ 1)) ∈ J := by
          simpa [A, hrow0] using quotientProdPresentation_snd_mem (R := R) I J (e₂ 1)
        have h10 : (A (e₁ 1) (e₂ 0)) ∈ I := by
          simpa [A, hrow1] using quotientProdPresentation_fst_mem (R := R) I J (e₂ 0)
        simpa [A, Matrix.det_fin_two, hrow0, hrow1, mul_comm, sub_eq_add_neg, add_comm, add_left_comm,
          add_assoc] using
          sub_mem (Ideal.mul_mem_mul h00 h11) (Ideal.mul_mem_mul h01 h10)
  · refine Ideal.mul_le.2 ?_
    intro a ha b hb
    by_cases hb0 : b = 0
    · simpa [hb0]
    · let x : LinearMap.ker π := quotientProdKerLeft (R := R) I J a ha
      let y : LinearMap.ker π := quotientProdKerRight (R := R) I J b hb
      have hxy : x ≠ y := by
        intro hxy
        have : b = 0 := by
          have hcoord := congrArg (fun z : LinearMap.ker π => z.1 1) hxy
          simpa [x, y, quotientProdKerLeft_apply_one, quotientProdKerRight_apply_one] using hcoord.symm
        exact hb0 this
      let e₂ : Fin 2 ↪ LinearMap.ker π := finTwoEmbeddingOfNe x y hxy
      refine Ideal.subset_span ?_
      refine ⟨⟨Function.Embedding.refl (Fin 2), e₂⟩, ?_⟩
      simp [A, e₂, x, y, Matrix.det_fin_two, finTwoEmbeddingOfNe_apply_zero,
        finTwoEmbeddingOfNe_apply_one, quotientProdKerLeft_apply_zero,
        quotientProdKerLeft_apply_one, quotientProdKerRight_apply_zero,
        quotientProdKerRight_apply_one]

-- Proof sketch: the `1 × 1` minors of the rank-`2` product quotient presentation are exactly the
-- coordinates of kernel vectors, namely elements of `I` and of `J`.
/-- Example 15.8.6 (3): the first Fitting ideal of `R ⧸ I ⊕ R ⧸ J` is the sum ideal `I + J`. -/
@[stacks 0H73]
theorem fittingIdeal_one_quotient_directSum (I J : Ideal R) :
    Fit[R]_(1)((R ⧸ I) × (R ⧸ J)) = I + J := by
  let π : (Fin 2 → R) →ₗ[R] (R ⧸ I) × (R ⧸ J) := quotientProdPresentation (R := R) I J
  let A : Matrix (Fin 2) (LinearMap.ker π) R := fun i x ↦ x.1 i
  change presentationFittingIdeal (R := R) (M := (R ⧸ I) × (R ⧸ J)) 1 π = I + J
  rw [presentationFittingIdeal]
  change Matrix.minorIdeal 1 A = I + J
  refine le_antisymm ?_ ?_
  · rw [Matrix.minorIdeal]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
    have hrow : e₁ 0 = 0 ∨ e₁ 0 = 1 := by
      have hval : (e₁ 0).1 = 0 ∨ (e₁ 0).1 = 1 := by
        omega
      cases hval with
      | inl hval =>
          left
          exact Fin.ext hval
      | inr hval =>
          right
          exact Fin.ext hval
    cases hrow with
    | inl hrow0 =>
        have he₁ : e₁ = rowZeroEmbedding := by
          ext i
          fin_cases i
          exact congrArg Fin.val hrow0
        have hmem : (e₂ 0).1 0 ∈ I := quotientProdPresentation_fst_mem (R := R) I J (e₂ 0)
        rw [he₁]
        have hmem' : (e₂ 0).1 0 ∈ I + J := by
          exact Submodule.mem_sup.2 ⟨(e₂ 0).1 0, hmem, 0, Ideal.zero_mem J, by simp⟩
        have hsum : (e₂ 0).1 0 + 0 ∈ I + J := Ideal.add_mem (I + J) hmem' (Ideal.zero_mem (I + J))
        simpa [A, rowZeroEmbedding] using hsum
    | inr hrow1 =>
        have he₁ : e₁ = rowOneEmbedding := by
          ext i
          fin_cases i
          exact congrArg Fin.val hrow1
        have hmem : (e₂ 0).1 1 ∈ J := quotientProdPresentation_snd_mem (R := R) I J (e₂ 0)
        rw [he₁]
        have hmem' : (e₂ 0).1 1 ∈ I + J := by
          exact Submodule.mem_sup.2 ⟨0, Ideal.zero_mem I, (e₂ 0).1 1, hmem, by simp⟩
        have hsum : 0 + (e₂ 0).1 1 ∈ I + J := Ideal.add_mem (I + J) (Ideal.zero_mem (I + J)) hmem'
        simpa [A, rowOneEmbedding] using hsum
  · rw [show I + J = I ⊔ J by rfl]
    refine sup_le_iff.2 ⟨?_, ?_⟩
    · intro a ha
      let x : LinearMap.ker π := quotientProdKerLeft (R := R) I J a ha
      refine Ideal.subset_span ?_
      refine ⟨⟨rowZeroEmbedding, ⟨fun _ ↦ x, fun _ _ _ ↦ Subsingleton.elim _ _⟩⟩, ?_⟩
      simp [A, rowZeroEmbedding, x, quotientProdKerLeft_apply_zero]
    · intro b hb
      let y : LinearMap.ker π := quotientProdKerRight (R := R) I J b hb
      refine Ideal.subset_span ?_
      refine ⟨⟨rowOneEmbedding, ⟨fun _ ↦ y, fun _ _ _ ↦ Subsingleton.elim _ _⟩⟩, ?_⟩
      simp [A, rowOneEmbedding, y, quotientProdKerRight_apply_one]

end
