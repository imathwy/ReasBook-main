import Mathlib
import Serre.Chap02.Corollary_2_2_3_4
import Serre.Chap02.Proposition_2_2_1_1
import Serre.Chap12.Proposition_12_12_1_3
import Serre.RepresentationTheory.RealizableOver

-- Declarations for this item will be appended below by the statement pipeline.

open LinearMap (BilinForm)
open scoped TensorProduct
open scoped ComplexStarModule
open scoped Polynomial

noncomputable section

universe u v

namespace LinearMap.BilinForm

section

variable {R : Type*} [CommSemiring R]
variable {G : Type u} [Monoid G]
variable {V : Type v} [AddCommMonoid V] [Module R V]

/-- A bilinear form on a representation is invariant if each group element acts by an isometry for
that form. -/
def IsInvariantUnder (B : BilinForm R V) (ρ : Representation R G V) : Prop :=
  ∀ g : G, B.comp (ρ g) (ρ g) = B

/-- A bilinear form on a representation is invariant exactly when it is preserved pointwise by the
action of every group element. -/
theorem isInvariantUnder_iff (B : BilinForm R V) (ρ : Representation R G V) :
    B.IsInvariantUnder ρ ↔ ∀ g : G, ∀ x y : V, B (ρ g x) (ρ g y) = B x y := by
  constructor
  · intro h g x y
    simpa using BilinForm.congr_fun (h g) x y
  · intro h g
    ext x y
    simpa using h g x y

end

end LinearMap.BilinForm

namespace Representation

open LinearMap.BilinForm

section

variable {k : Type*} [Field k]
variable {G : Type u} [Group G]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

omit [FiniteDimensional k V] in
/-- Helper for Theorem 13-13.2-1: an invariant bilinear form is exactly a `G`-equivariant map to
the dual representation. -/
theorem isInvariantUnder_iff_dual_intertwining
    (B : BilinForm k V) (ρ : Representation k G V) :
    B.IsInvariantUnder ρ ↔ ∀ g : G, B ∘ₗ ρ g = ρ.dual g ∘ₗ B := by
  constructor
  · intro h g
    ext x y
    -- Evaluate the invariance identity after rewriting the second variable by `ρ g⁻¹`.
    have hxy := (LinearMap.BilinForm.isInvariantUnder_iff B ρ).1 h g x (ρ g⁻¹ y)
    simpa using hxy
  · intro h
    rw [LinearMap.BilinForm.isInvariantUnder_iff]
    intro g x y
    -- Apply the intertwining identity first in `x`, then in `ρ g y`.
    have hxy := LinearMap.congr_fun (h g) x
    have hxy' := LinearMap.congr_fun hxy (ρ g y)
    simpa [Representation.dual_apply, Module.Dual.transpose_apply] using hxy'

-- Proof sketch: a nondegenerate invariant bilinear form identifies `V` with the dual
-- representation via `B.toDual`, and conversely an equivariant equivalence `ρ ≃ ρ.dual`
-- transports the dual evaluation pairing to a nondegenerate `G`-invariant bilinear form.
/-- A finite-dimensional representation over a field is equivariantly self-dual if and only if it
admits a nondegenerate invariant bilinear form. -/
theorem nonempty_equiv_dual_iff_exists_invariant_nondegenerate_bilinForm
    (ρ : Representation k G V) :
    Nonempty (ρ.Equiv ρ.dual) ↔
      ∃ B : BilinForm k V, B.Nondegenerate ∧ B.IsInvariantUnder ρ := by
  constructor
  · rintro ⟨e⟩
    -- Turn an equivariant self-duality into the transported dual pairing on `V`.
    refine ⟨e.toLinearMap, ?_, ?_⟩
    refine ⟨?_, ?_⟩
    · rw [LinearMap.separatingLeft_iff_ker_eq_bot]
      exact LinearMap.ker_eq_bot.mpr e.toLinearEquiv.injective
    · intro y hy
      refine (Module.forall_dual_apply_eq_zero_iff k y).mp ?_
      intro f
      rcases e.toLinearEquiv.surjective f with ⟨x, rfl⟩
      exact hy x
    -- The intertwining relation for `e` is exactly invariance of the associated bilinear form.
    rw [isInvariantUnder_iff_dual_intertwining]
    intro g
    exact e.isIntertwining' g
  · rintro ⟨B, hB, hB_invariant⟩
    -- A nondegenerate invariant bilinear form identifies `V` with the dual representation.
    refine ⟨Representation.Equiv.mk (B.toDual hB) ?_⟩
    rw [isInvariantUnder_iff_dual_intertwining] at hB_invariant
    intro g
    ext x y
    have hxy := LinearMap.congr_fun (hB_invariant g) x
    have hxy' := LinearMap.congr_fun hxy y
    simpa [B.toDual_def] using hxy'

end

section

variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

-- Proof sketch: by Proposition `2-2.1-1`, the character of `ρ.dual` is the complex conjugate of
-- the character of `ρ`; by Corollary `2-2.3-4`, two finite-dimensional complex representations of
-- a finite group have the same character exactly when they are equivariantly isomorphic.
/-- A finite-dimensional complex representation of a finite group has real-valued character if and
only if it is equivariantly self-dual. The public owner for "real-valued character" is the
Chapter `12` predicate `IsValuedInBaseField ℝ` applied to `ρ.character`. -/
theorem hasRealValuedCharacter_iff_nonempty_equiv_dual (ρ : Representation ℂ G V) :
    IsValuedInBaseField ℝ ρ.character ↔ Nonempty (ρ.Equiv ρ.dual) := by
  letI : Fintype G := Fintype.ofFinite G
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard_ne
  have hval :
      IsValuedInBaseField ℝ ρ.character ↔
        ∀ g : G, star (ρ.character g) = ρ.character g := by
    rw [Representation.isValuedInBaseField_iff_mem_pointwiseAlgebraMap_range]
    constructor
    · rintro ⟨χR, hχR⟩ g
      -- A character coming from `ℝ` is fixed by complex conjugation pointwise.
      rw [← congrFun hχR g]
      simp
    · intro hstar
      -- Conversely, a conjugation-fixed complex value is the image of its real part.
      refine ⟨fun g ↦ (ρ.character g).re, ?_⟩
      ext g
      exact (Complex.conj_eq_iff_re).mp (hstar g)
  rw [hval]
  constructor
  · intro hstar
    -- Real-valuedness identifies the character with the dual character.
    have hchar : ρ.character = ρ.dual.character := by
      ext g
      rw [Representation.char_dual_eq_star]
      exact (hstar g).symm
    exact (Representation.character_eq_iff_nonempty_equiv ρ ρ.dual).mp hchar
  · rintro ⟨e⟩ g
    -- An equivariant self-duality forces equality of the two characters.
    rw [← Representation.char_dual_eq_star]
    exact (congrFun (Representation.char_iso e) g).symm

-- Proof sketch: use `Representation.char_dual` and the fact that, for finite-dimensional complex
-- representations of a finite group, equality of characters is equivalent to equivariant
-- isomorphism. A nondegenerate invariant bilinear form identifies `V` with the dual
-- representation, and conversely an equivariant isomorphism `ρ ≃ ρ.dual` transports the canonical
-- dual pairing to a nondegenerate `G`-invariant bilinear form on `V`.
/-- Theorem 13-13.2-1 (1): a finite-dimensional complex representation has real-valued character if
and only if it admits a nondegenerate `G`-invariant complex bilinear form. -/
theorem hasRealValuedCharacter_iff_exists_invariant_nondegenerate_bilinForm
    (ρ : Representation ℂ G V) :
    IsValuedInBaseField ℝ ρ.character ↔
      ∃ B : BilinForm ℂ V, B.Nondegenerate ∧ B.IsInvariantUnder ρ := by
  rw [hasRealValuedCharacter_iff_nonempty_equiv_dual,
    nonempty_equiv_dual_iff_exists_invariant_nondegenerate_bilinForm]

/-- Helper for Theorem 13-13.2-1: a finite-dimensional real representation of a finite group admits
an invariant symmetric nondegenerate real bilinear form, obtained by averaging the standard form
attached to a basis. -/
theorem exists_invariant_nondegenerate_symmetric_real_bilinForm
    {W : Type v} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (ρ : Representation ℝ G W) :
    ∃ B : BilinForm ℝ W, B.Nondegenerate ∧ B.IsSymm ∧ B.IsInvariantUnder ρ := by
  letI : Fintype G := Fintype.ofFinite G
  let b := Module.Free.chooseBasis ℝ W
  let ι := Module.Free.ChooseBasisIndex ℝ W
  letI : Finite ι := Module.Finite.finite_basis b
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  let Bstd : BilinForm ℝ W := Matrix.toBilin b (1 : Matrix ι ι ℝ)
  let B : BilinForm ℝ W := ∑ g : G, Bstd.comp (ρ g) (ρ g)
  refine ⟨B, ?_, ?_, ?_⟩
  · -- The averaged form is positive on nonzero vectors because the identity term is already
    -- positive; that positivity forces nondegeneracy.
    constructor
    · intro x hx
      by_contra hx0
      have hxrepr : b.repr x ≠ 0 := by
        intro hrepr
        apply hx0
        exact b.repr.injective (by simpa using hrepr)
      obtain ⟨i, hi⟩ : ∃ i : ι, b.repr x i ≠ 0 := by
        by_contra h
        apply hxrepr
        ext j
        by_contra hj
        exact h ⟨j, hj⟩
      have hBstd_sum_pos : 0 < ∑ j : ι, (b.repr x j)^2 := by
        refine Finset.sum_pos' ?_ ?_
        · intro j hj
          exact sq_nonneg _
        · exact ⟨i, Finset.mem_univ i, by simpa using sq_pos_of_ne_zero hi⟩
      have hBstd_xx : 0 < Bstd x x := by
        simpa [Bstd, Matrix.one_apply, pow_two] using hBstd_sum_pos
      have hB_xx : B x x = 0 := hx x
      have hB_term_nonneg :
          ∀ g ∈ (Finset.univ : Finset G), 0 ≤ Bstd (ρ g x) (ρ g x) := by
        intro g hg
        have hsum_nonneg : 0 ≤ ∑ j : ι, (b.repr (ρ g x) j)^2 := by
          refine Finset.sum_nonneg ?_
          intro j hj'
          exact sq_nonneg _
        simpa [Bstd, Matrix.one_apply, pow_two] using hsum_nonneg
      have hB_pos : 0 < B x x := by
        calc
          0 < Bstd x x := hBstd_xx
          _ ≤ ∑ g : G, Bstd (ρ g x) (ρ g x) := by
            have hmem : (1 : G) ∈ (Finset.univ : Finset G) := Finset.mem_univ 1
            simpa [B, LinearMap.BilinForm.comp_apply] using
              Finset.single_le_sum hB_term_nonneg hmem
          _ = B x x := by
            simp [B, LinearMap.BilinForm.comp_apply]
      exact (lt_irrefl 0) (hB_xx ▸ hB_pos)
    · intro y hy
      by_contra hy0
      have hleft : B y y = 0 := hy y
      have hyrepr : b.repr y ≠ 0 := by
        intro hrepr
        apply hy0
        exact b.repr.injective (by simpa using hrepr)
      obtain ⟨i, hi⟩ : ∃ i : ι, b.repr y i ≠ 0 := by
        by_contra h
        apply hyrepr
        ext j
        by_contra hj
        exact h ⟨j, hj⟩
      have hBstd_sum_pos : 0 < ∑ j : ι, (b.repr y j)^2 := by
        refine Finset.sum_pos' ?_ ?_
        · intro j hj
          exact sq_nonneg _
        · exact ⟨i, Finset.mem_univ i, by simpa using sq_pos_of_ne_zero hi⟩
      have hBstd_yy : 0 < Bstd y y := by
        simpa [Bstd, Matrix.one_apply, pow_two] using hBstd_sum_pos
      have hB_term_nonneg :
          ∀ g ∈ (Finset.univ : Finset G), 0 ≤ Bstd (ρ g y) (ρ g y) := by
        intro g hg
        have hsum_nonneg : 0 ≤ ∑ j : ι, (b.repr (ρ g y) j)^2 := by
          refine Finset.sum_nonneg ?_
          intro j hj'
          exact sq_nonneg _
        simpa [Bstd, Matrix.one_apply, pow_two] using hsum_nonneg
      have hB_pos : 0 < B y y := by
        calc
          0 < Bstd y y := hBstd_yy
          _ ≤ ∑ g : G, Bstd (ρ g y) (ρ g y) := by
            have hmem : (1 : G) ∈ (Finset.univ : Finset G) := Finset.mem_univ 1
            simpa [B, LinearMap.BilinForm.comp_apply] using
              Finset.single_le_sum hB_term_nonneg hmem
          _ = B y y := by
            simp [B, LinearMap.BilinForm.comp_apply]
      exact (lt_irrefl 0) (hleft ▸ hB_pos)
  · -- Symmetry survives both composition with the same map and finite summation.
    refine ⟨?_⟩
    intro x y
    simp [B, Bstd, Matrix.toBilin_apply, Matrix.one_apply, mul_comm]
  · -- Averaging over right multiplication makes the form invariant under the representation.
    rw [LinearMap.BilinForm.isInvariantUnder_iff]
    intro a x y
    simp only [B]
    simpa [map_mul] using
      (Equiv.sum_comp (Equiv.mulRight a) (fun g : G => Bstd (ρ g x) (ρ g y)))

/-- Helper for Theorem 13-13.2-1: scalar extension carries an invariant symmetric nondegenerate
real bilinear form to an invariant symmetric nondegenerate complex bilinear form. -/
theorem baseChange_nondegenerate_invariant_symmetric_bilinForm
    {W : Type v} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (ρ : Representation ℝ G W) (B : BilinForm ℝ W)
    (hB : B.Nondegenerate) (hB_symm : B.IsSymm) (hB_invariant : B.IsInvariantUnder ρ) :
    let BC := B.baseChange ℂ
    BC.Nondegenerate ∧ BC.IsSymm ∧ BC.IsInvariantUnder (Representation.scalarExtension ρ) := by
  classical
  let BC := B.baseChange ℂ
  refine ⟨?_, ?_, ?_⟩
  · -- Compare the Gram matrix of the base-changed form with the scalar extension of the real Gram
    -- matrix; the determinant stays nonzero after applying `algebraMap ℝ ℂ`.
    let b := Module.Free.chooseBasis ℝ W
    let bC := Algebra.TensorProduct.basis ℂ b
    have hdet : (LinearMap.BilinForm.toMatrix b B).det ≠ 0 :=
      (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB
    have hmatrix :
        LinearMap.BilinForm.toMatrix bC BC =
          (LinearMap.BilinForm.toMatrix b B).map (algebraMap ℝ ℂ) := by
      ext i j
      simp [BC, bC, b]
    refine (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bC).2 ?_
    rw [hmatrix]
    have hmapdet :
        (((LinearMap.BilinForm.toMatrix b B).map (algebraMap ℝ ℂ)).det) =
          algebraMap ℝ ℂ ((LinearMap.BilinForm.toMatrix b B).det) := by
      simpa using
        (RingHom.map_det (algebraMap ℝ ℂ) (LinearMap.BilinForm.toMatrix b B)).symm
    rw [hmapdet]
    intro hzero
    exact hdet (Complex.ofReal_eq_zero.mp hzero)
  · -- Symmetry can also be checked on pure tensors and then extended by bilinearity.
    refine ⟨?_⟩
    intro x y
    induction x using TensorProduct.induction_on with
    | zero =>
        simp [BC]
    | tmul a x =>
        induction y using TensorProduct.induction_on with
        | zero =>
            simp [BC]
        | tmul b y =>
            simp [BC, hB_symm.eq x y, mul_comm, mul_left_comm, mul_assoc]
        | add y₁ y₂ hy₁ hy₂ =>
            simp [BC, hy₁, hy₂]
    | add x₁ x₂ hx₁ hx₂ =>
        simp [BC, hx₁, hx₂]
  · -- Check invariance on pure tensors, then extend by bilinearity in each variable.
    rw [LinearMap.BilinForm.isInvariantUnder_iff]
    intro g x y
    have hB_pointwise := (LinearMap.BilinForm.isInvariantUnder_iff B ρ).1 hB_invariant
    induction x using TensorProduct.induction_on with
    | zero =>
        simp
    | tmul a x =>
        induction y using TensorProduct.induction_on with
        | zero =>
            simp
        | tmul b y =>
            -- On pure tensors the claim is exactly the real invariance of `B`.
            change BC (((ρ g).baseChange ℂ) (a ⊗ₜ[ℝ] x)) (((ρ g).baseChange ℂ) (b ⊗ₜ[ℝ] y)) =
              BC (a ⊗ₜ[ℝ] x) (b ⊗ₜ[ℝ] y)
            simp [BC, hB_pointwise g x y, mul_assoc, mul_left_comm, mul_comm]
        | add y₁ y₂ hy₁ hy₂ =>
            simp [hy₁, hy₂]
    | add x₁ x₂ hx₁ hx₂ =>
        simp [hx₁, hx₂]

/-- Helper for Theorem 13-13.2-1: a real model yields the invariant symmetric nondegenerate
complex bilinear form promised by the Frobenius-Schur criterion. -/
theorem exists_invariant_nondegenerate_symmetric_bilinForm_of_isRealizableOverReal
    (ρ : Representation ℂ G V) (hρ : IsRealizableOver ℝ ρ) :
    ∃ B : BilinForm ℂ V, B.Nondegenerate ∧ B.IsSymm ∧ B.IsInvariantUnder ρ := by
  rcases hρ with ⟨W, _instAddCommGroupW, _instModuleW, _instFiniteDimensionalW, ρ₀, hρ₀⟩
  rcases hρ₀ with ⟨e⟩
  rcases exists_invariant_nondegenerate_symmetric_real_bilinForm (ρ := ρ₀) with
    ⟨B₀, hB₀, hB₀_symm, hB₀_invariant⟩
  have hBC :=
    baseChange_nondegenerate_invariant_symmetric_bilinForm (ρ := ρ₀) (B := B₀)
      hB₀ hB₀_symm hB₀_invariant
  let BC : BilinForm ℂ (TensorProduct ℝ ℂ W) := B₀.baseChange ℂ
  let BV : BilinForm ℂ V := LinearMap.BilinForm.congr e.toLinearEquiv BC
  refine ⟨BV, ?_, ?_, ?_⟩
  · -- Transport nondegeneracy through the chosen equivariant complexification equivalence.
    simpa [BV, BC] using hBC.1.congr e.toLinearEquiv
  · -- Symmetry is preserved under congruence by a linear equivalence.
    refine ⟨?_⟩
    intro x y
    simpa [BV, BC] using hBC.2.1.eq (e.toLinearEquiv.symm x) (e.toLinearEquiv.symm y)
  · -- Transport invariance across the intertwining equivalence `e`.
    rw [LinearMap.BilinForm.isInvariantUnder_iff]
    intro g x y
    have hx :
        e.toLinearEquiv.symm (ρ g x) =
          (Representation.scalarExtension ρ₀) g (e.toLinearEquiv.symm x) := by
      simpa using congr($(e.symm.isIntertwining' g) x)
    have hy :
        e.toLinearEquiv.symm (ρ g y) =
          (Representation.scalarExtension ρ₀) g (e.toLinearEquiv.symm y) := by
      simpa using congr($(e.symm.isIntertwining' g) y)
    -- Once both arguments are moved back to the scalar extension, the claim reduces to the
    -- invariance already proved for `BC`.
    rw [show BV (ρ g x) (ρ g y) =
        BC (e.toLinearEquiv.symm (ρ g x)) (e.toLinearEquiv.symm (ρ g y)) by rfl]
    rw [show BV x y = BC (e.toLinearEquiv.symm x) (e.toLinearEquiv.symm y) by rfl]
    rw [hx, hy]
    exact ((LinearMap.BilinForm.isInvariantUnder_iff BC (Representation.scalarExtension ρ₀)).1
      hBC.2.2) g _ _

/-- Helper for Theorem 13-13.2-1: an equivariant conjugation on `V` determines a `G`-stable real
form whose complex span is all of `V`. -/
theorem exists_stable_real_form_data_of_equivariant_conjugation
    (ρ : Representation ℂ G V) (σ : V →ₗ[ℝ] V)
    (hσ_smul : ∀ z : ℂ, ∀ x : V, σ (z • x) = star z • σ x)
    (hσ_sq : ∀ x : V, σ (σ x) = x)
    (hσ_equiv : ∀ g : G, ∀ x : V, σ (ρ g x) = ρ g (σ x)) :
    ∃ W : Submodule ℝ V,
      (∀ g : G, ∀ x : V, x ∈ W → ρ g x ∈ W) ∧
      Submodule.span ℂ (W : Set V) = ⊤ := by
  letI : Module ℝ V := .restrictScalars ℝ ℂ V
  letI : IsScalarTower ℝ ℂ V := .restrictScalars ℝ ℂ V
  -- Use `σ` as the star operation so that the fixed vectors become the self-adjoint submodule.
  letI : StarAddMonoid V :=
    { star := σ
      star_involutive := hσ_sq
      star_add := by
        intro x y
        exact σ.map_add x y }
  letI : StarModule ℂ V := { star_smul := hσ_smul }
  letI : StarModule ℝ V := by
    refine ⟨?_⟩
    intro r x
    simpa using hσ_smul (r : ℂ) x
  refine ⟨selfAdjoint.submodule ℝ V, ?_, ?_⟩
  · -- Equivariance makes the fixed-point real form stable under the `G`-action.
    intro g x hx
    change σ (ρ g x) = ρ g x
    rw [hσ_equiv g x, show σ x = x by exact hx]
  · -- The real and imaginary parts of any vector are fixed by `σ`, so these fixed vectors span.
    simpa using (span_selfAdjoint (A := V))

/-- Helper for Theorem 13-13.2-1: every vector in a complex star module decomposes into a
self-adjoint real part and a self-adjoint imaginary part. -/
theorem exists_selfAdjoint_real_imaginary_decomposition
    [Module ℝ V] [IsScalarTower ℝ ℂ V] [StarAddMonoid V] [StarModule ℂ V]
    (v : V) :
    ∃ a b : selfAdjoint V, (a : V) + Complex.I • (b : V) = v := by
  -- Package the standard `realPart`/`imaginaryPart` decomposition into existential form for the
  -- later tensor inverse construction.
  refine ⟨ℜ v, ℑ v, ?_⟩
  simpa using (realPart_add_I_smul_imaginaryPart v)

/-- Helper for Theorem 13-13.2-1: a vector fixed by the conjugation star structure has itself as
its real part and vanishing imaginary part. -/
theorem real_imaginary_parts_of_selfAdjoint
    [Module ℝ V] [IsScalarTower ℝ ℂ V] [StarAddMonoid V] [StarModule ℂ V] [StarModule ℝ V]
    (w : selfAdjoint.submodule ℝ V) :
    ℜ (w : V) = w ∧ ℑ (w : V) = 0 := by
  -- Record the fixed-real-form identities needed for the eventual explicit tensor inverse.
  exact ⟨Subtype.ext w.property.coe_realPart, w.property.imaginaryPart⟩

/-- Helper for Theorem 13-13.2-1: in the canonical complex-to-real restriction, the explicit
real/imaginary inverse on the fixed real form recovers each pure tensor. -/
theorem tensor_fixed_real_form_inverse_on_pure_tensors
    [StarAddMonoid V] [StarModule ℂ V]
    (z : ℂ) (w : selfAdjoint.submodule ℝ V) :
    (1 : ℂ) ⊗ₜ[ℝ] (ℜ (z • (w : V)) : selfAdjoint.submodule ℝ V) +
        Complex.I ⊗ₜ[ℝ] (ℑ (z • (w : V)) : selfAdjoint.submodule ℝ V) =
      z ⊗ₜ[ℝ] w := by
  -- Rewrite the real and imaginary parts using that `w` is fixed by the star operation.
  have hre : ℜ (z • (w : V)) = ((z.re : ℝ) • w : selfAdjoint.submodule ℝ V) := by
    ext
    rw [realPart_smul]
    simp
  have him : ℑ (z • (w : V)) = ((z.im : ℝ) • w : selfAdjoint.submodule ℝ V) := by
    ext
    rw [imaginaryPart_smul]
    simp
  calc
    (1 : ℂ) ⊗ₜ[ℝ] (ℜ (z • (w : V)) : selfAdjoint.submodule ℝ V) +
        Complex.I ⊗ₜ[ℝ] (ℑ (z • (w : V)) : selfAdjoint.submodule ℝ V)
        =
          (1 : ℂ) ⊗ₜ[ℝ] (((z.re : ℝ) • w : selfAdjoint.submodule ℝ V)) +
            Complex.I ⊗ₜ[ℝ] (((z.im : ℝ) • w : selfAdjoint.submodule ℝ V)) := by
          rw [hre, him]
          rfl
    _ = (z.re : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] w) + (z.im : ℂ) • (Complex.I ⊗ₜ[ℝ] w) := by
          rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul]
          rfl
    _ = ((z.re : ℂ) * (1 : ℂ)) ⊗ₜ[ℝ] w + ((z.im : ℂ) * Complex.I) ⊗ₜ[ℝ] w := by
          rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']
          simp
    _ = ((z.re : ℂ) + (z.im : ℂ) * Complex.I) ⊗ₜ[ℝ] w := by
          rw [← TensorProduct.add_tmul]
          simp
    _ = z ⊗ₜ[ℝ] w := by
          rw [Complex.re_add_im]

/-- Helper for Theorem 13-13.2-1: the fixed real form of a complex star module complexifies back
to the whole complex module. -/
theorem tensor_fixed_real_form_linearEquiv
    [StarAddMonoid V] [StarModule ℂ V] :
    let W := selfAdjoint.submodule ℝ V
    ∃ e : ℂ ⊗[ℝ] W ≃ₗ[ℂ] V,
      ∀ z : ℂ, ∀ w : W, e (z ⊗ₜ[ℝ] w) = z • (w : V) := by
  let W := selfAdjoint.submodule ℝ V
  let fR : ℂ →ₗ[ℝ] W →ₗ[ℝ] V :=
    { toFun := fun z =>
        { toFun := fun w => z • (w : V)
          map_add' := by
            intro w₁ w₂
            simp [smul_add]
          map_smul' := by
            intro r w
            -- Move the real scalar through the complex action before building the tensor lift.
            calc
              z • (r • (w : V)) = (z * (r : ℂ)) • (w : V) := by
                simpa [smul_assoc] using (mul_smul z (r : ℂ) (w : V)).symm
              _ = ((r : ℂ) * z) • (w : V) := by
                rw [mul_comm]
              _ = r • z • (w : V) := by
                simpa [smul_assoc] using (mul_smul (r : ℂ) z (w : V)) }
      map_add' := by
        intro z₁ z₂
        ext w
        simp [add_smul]
      map_smul' := by
        intro r z
        ext w
        -- The first tensor factor is only `ℝ`-linear, so rewrite the scalar action in `ℂ`.
        simpa [smul_assoc] using (mul_smul (r : ℂ) z (w : V)) }
  let eR : ℂ ⊗[ℝ] W →ₗ[ℝ] V := TensorProduct.lift fR
  let e : ℂ ⊗[ℝ] W →ₗ[ℂ] V :=
    { toFun := eR
      map_add' := eR.map_add
      map_smul' := by
        intro c x
        -- Check complex linearity on pure tensors and extend by tensor induction.
        refine TensorProduct.induction_on x ?_ ?_ ?_
        · simp [eR]
        · intro z w
          change eR ((c * z) ⊗ₜ[ℝ] w) = c • eR (z ⊗ₜ[ℝ] w)
          simpa [eR, fR] using (mul_smul c z (w : V))
        · intro x y hx hy
          simp [hx, hy] }
  let inv : V → ℂ ⊗[ℝ] W := fun x ↦
    (1 : ℂ) ⊗ₜ[ℝ] (ℜ x : W) + Complex.I ⊗ₜ[ℝ] (ℑ x : W)
  have he_inv : ∀ x : V, e (inv x) = x := by
    intro x
    -- The explicit real/imaginary inverse collapses under the forward tensor map.
    calc
      e (inv x) =
          e ((1 : ℂ) ⊗ₜ[ℝ] (ℜ x : W)) + e (Complex.I ⊗ₜ[ℝ] (ℑ x : W)) := by
        change e
            ((1 : ℂ) ⊗ₜ[ℝ] (ℜ x : W) + Complex.I ⊗ₜ[ℝ] (ℑ x : W)) =
          e ((1 : ℂ) ⊗ₜ[ℝ] (ℜ x : W)) + e (Complex.I ⊗ₜ[ℝ] (ℑ x : W))
        exact e.map_add _ _
      _ = (1 : ℂ) • (ℜ x : V) + Complex.I • (ℑ x : V) := by
        simp [e, eR, fR]
      _ = x := by
        simpa using (realPart_add_I_smul_imaginaryPart x)
  have hinv_zero : inv (0 : V) = 0 := by
    simp [inv]
    rfl
  have hinv_add : ∀ x y : V, inv (x + y) = inv x + inv y := by
    intro x y
    -- Additivity follows from the additive behavior of real and imaginary parts.
    let a : ℂ ⊗[ℝ] W := (1 : ℂ) ⊗ₜ[ℝ] (ℜ x : W)
    let b : ℂ ⊗[ℝ] W := (1 : ℂ) ⊗ₜ[ℝ] (ℜ y : W)
    let c : ℂ ⊗[ℝ] W := Complex.I ⊗ₜ[ℝ] (ℑ x : W)
    let d : ℂ ⊗[ℝ] W := Complex.I ⊗ₜ[ℝ] (ℑ y : W)
    calc
      inv (x + y) = (a + b) + (c + d) := by
        simp [inv, a, b, c, d, TensorProduct.tmul_add]
        rfl
      _ = (a + c) + (b + d) := by
        simpa [add_assoc, add_left_comm, add_comm]
      _ = inv x + inv y := by
        simp [inv, a, b, c, d, add_assoc]
        rfl
  have hinv_e : ∀ x : ℂ ⊗[ℝ] W, inv (e x) = x := by
    intro x
    -- It is enough to check the inverse identity on pure tensors.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · rw [LinearMap.map_zero]
      exact hinv_zero
    · intro z w
      simpa [e, eR, fR, inv] using
        (tensor_fixed_real_form_inverse_on_pure_tensors (V := V) z w)
    · intro x y hx hy
      rw [LinearMap.map_add, hinv_add, hx, hy]
  have hbij : Function.Bijective e := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      have hxy' := congrArg inv hxy
      simpa [hinv_e x, hinv_e y] using hxy'
    · intro x
      exact ⟨inv x, he_inv x⟩
  refine ⟨LinearEquiv.ofBijective e hbij, ?_⟩
  intro z w
  rfl

/-- Helper for Theorem 13-13.2-1: an equivariant conjugation identifies `V` with the complex
scalar extension of its fixed real form, hence realizes the representation over `ℝ`. -/
theorem isRealizableOverReal_of_equivariant_conjugation
    (ρ : Representation ℂ G V) (σ : V →ₗ[ℝ] V)
    (hσ_smul : ∀ z : ℂ, ∀ x : V, σ (z • x) = star z • σ x)
    (hσ_sq : ∀ x : V, σ (σ x) = x)
    (hσ_equiv : ∀ g : G, ∀ x : V, σ (ρ g x) = ρ g (σ x)) :
    IsRealizableOver ℝ ρ := by
  letI : Module ℝ V := .restrictScalars ℝ ℂ V
  letI : IsScalarTower ℝ ℂ V := .restrictScalars ℝ ℂ V
  letI : Module.Finite ℂ V := by infer_instance
  letI : Module.Finite ℝ V := Module.Finite.trans ℂ V
  letI : FiniteDimensional ℝ V := by infer_instance
  letI : StarAddMonoid V :=
    { star := σ
      star_involutive := hσ_sq
      star_add := by
        intro x y
        exact σ.map_add x y }
  letI : StarModule ℂ V := { star_smul := hσ_smul }
  letI : StarModule ℝ V := by
    refine ⟨?_⟩
    intro r x
    simpa using hσ_smul (r : ℂ) x
  let W := selfAdjoint.submodule ℝ V
  let ρ₀ : Representation ℝ G W :=
    { toFun := fun g =>
        ((ρ g).restrictScalars ℝ).restrict <| by
          intro x hx
          change σ (ρ g x) = ρ g x
          have hx' : σ x = x := by
            simpa [W] using hx
          rw [hσ_equiv g x]
          exact congrArg (ρ g) hx'
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro g h
        ext x
        simp }
  have htensor :
      ∃ e : ℂ ⊗[ℝ] W ≃ₗ[ℂ] V,
        ∀ z : ℂ, ∀ w : W, e (z ⊗ₜ[ℝ] w) = z • (w : V) := by
    -- Route correction: use the canonical tensor-span equivalence for the fixed real form instead
    -- of hand-building the inverse from real and imaginary parts.
    simpa [W] using (tensor_fixed_real_form_linearEquiv (V := V))
  rcases htensor with ⟨e, he⟩
  refine ⟨W, inferInstance, inferInstance, inferInstance, ρ₀, ?_⟩
  refine ⟨Representation.Equiv.mk e ?_⟩
  intro g
  apply TensorProduct.AlgebraTensorModule.ext
  intro z w
  -- On pure tensors, the scalar extension action is exactly base change of `ρ₀`.
  change e (((ρ₀ g).baseChange ℂ) (z ⊗ₜ[ℝ] w)) = ρ g (e (z ⊗ₜ[ℝ] w))
  rw [LinearMap.baseChange_tmul]
  calc
    e (z ⊗ₜ[ℝ] (ρ₀ g) w) = z • (((ρ₀ g) w : W) : V) := by
      simpa using he z ((ρ₀ g) w)
    _ = z • (ρ g (w : V)) := by
      rfl
    _ = ρ g (z • (w : V)) := by
      simp [smul_assoc]
    _ = ρ g (e (z ⊗ₜ[ℝ] w)) := by
      rw [he z w]

/-- Helper for Theorem 13-13.2-1: averaging the standard Hermitian pairing produces an invariant
positive conjugate-dual equivalence. -/
theorem exists_invariant_positive_conjugate_dual_equiv
    (ρ : Representation ℂ G V) :
    ∃ J : V ≃ₗ⋆[ℂ] Module.Dual ℂ V,
      (∀ g : G, ∀ x y : V, J (ρ g x) (ρ g y) = J x y) ∧
      (∀ x y : V, star (J x y) = J y x) ∧
      (∀ x : V, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ)) := by
  letI : Fintype G := Fintype.ofFinite G
  let b := Module.Free.chooseBasis ℂ V
  let ι := Module.Free.ChooseBasisIndex ℂ V
  letI : Finite ι := Module.Finite.finite_basis b
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  let Jstd : V →ₗ⋆[ℂ] Module.Dual ℂ V :=
    Matrix.toLinearMapₛₗ₂ (R := ℂ) (σ₁ := (↑Complex.conjAe : ℂ →+* ℂ)) b b
      (1 : Matrix ι ι ℂ)
  -- Expand the standard conjugate-dual map in basis coordinates so both Hermitian symmetry and
  -- diagonal positivity reduce to the familiar coordinate formulas.
  have hJstd_apply : ∀ x y : V, Jstd x y = ∑ i : ι, star (b.repr x i) * b.repr y i := by
    intro x y
    have hmat : LinearMap.toMatrix₂ b b Jstd = (1 : Matrix ι ι ℂ) := by
      change
        LinearMap.toMatrix₂ b b
            ((Matrix.toLinearMapₛₗ₂ (σ₁ := (↑Complex.conjAe : ℂ →+* ℂ)) b b)
              (1 : Matrix ι ι ℂ)) =
          (1 : Matrix ι ι ℂ)
      simp
    calc
      Jstd x y = star (b.repr x) ⬝ᵥ (LinearMap.toMatrix₂ b b Jstd).mulVec (b.repr y) := by
        exact apply_eq_star_dotProduct_toMatrix₂_mulVec b x y
      _ = star (b.repr x) ⬝ᵥ (b.repr y) := by
        rw [hmat, Matrix.one_mulVec]
      _ = ∑ i : ι, star (b.repr x i) * b.repr y i := by
        rw [dotProduct]
        apply Finset.sum_congr rfl
        intro i hi
        simp
  have hJstd_herm : ∀ x y : V, star (Jstd x y) = Jstd y x := by
    intro x y
    simp [hJstd_apply, Finset.sum_comm, mul_comm]
  have hJstd_diag : ∀ x : V, Jstd x x = ∑ i : ι, (Complex.normSq (b.repr x i) : ℂ) := by
    intro x
    simpa [Complex.normSq_eq_conj_mul_self] using hJstd_apply x x
  let Jmap : V →ₗ⋆[ℂ] Module.Dual ℂ V := ∑ g : G, (Jstd.comp (ρ g)).compl₂ (ρ g)
  -- Averaging makes both invariance and Hermitian symmetry compatible with the `G`-action.
  have hJ_invariant : ∀ g : G, ∀ x y : V, Jmap (ρ g x) (ρ g y) = Jmap x y := by
    intro g x y
    simp only [Jmap]
    simpa [map_mul] using
      (Equiv.sum_comp (Equiv.mulRight g) (fun h : G ↦ Jstd (ρ h x) (ρ h y)))
  have hJ_herm : ∀ x y : V, star (Jmap x y) = Jmap y x := by
    intro x y
    simp [Jmap, hJstd_herm]
  have hJ_pos : ∀ x : V, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ Jmap x x = (r : ℂ) := by
    intro x hx
    have hxrepr : b.repr x ≠ 0 := by
      intro hrepr
      apply hx
      exact b.repr.injective (by simpa using hrepr)
    obtain ⟨i, hi⟩ : ∃ i : ι, b.repr x i ≠ 0 := by
      by_contra h
      apply hxrepr
      ext j
      by_contra hj
      exact h ⟨j, hj⟩
    let r : ℝ := ∑ g : G, ∑ j : ι, Complex.normSq (b.repr (ρ g x) j)
    refine ⟨r, ?_, ?_⟩
    · have hterm_nonneg :
          ∀ g ∈ (Finset.univ : Finset G), 0 ≤ ∑ j : ι, Complex.normSq (b.repr (ρ g x) j) := by
        intro g hg
        refine Finset.sum_nonneg ?_
        intro j hj
        exact Complex.normSq_nonneg _
      have hterm_pos : 0 < ∑ j : ι, Complex.normSq (b.repr x j) := by
        refine Finset.sum_pos' ?_ ?_
        · intro j hj
          exact Complex.normSq_nonneg _
        · refine ⟨i, Finset.mem_univ i, ?_⟩
          exact Complex.normSq_pos.mpr hi
      have hsingle :
          0 < ∑ g : G, ∑ j : ι, Complex.normSq (b.repr (ρ g x) j) := by
        have hmem : (1 : G) ∈ (Finset.univ : Finset G) := Finset.mem_univ 1
        have hle :
            ∑ j : ι, Complex.normSq (b.repr x j) ≤
              ∑ g : G, ∑ j : ι, Complex.normSq (b.repr (ρ g x) j) := by
          simpa [r] using Finset.single_le_sum hterm_nonneg hmem
        exact lt_of_lt_of_le hterm_pos hle
      simpa [r] using hsingle
    · calc
        Jmap x x = ∑ g : G, Jstd (ρ g x) (ρ g x) := by
          simp [Jmap]
        _ = ∑ g : G, ∑ j : ι, (Complex.normSq (b.repr (ρ g x) j) : ℂ) := by
          apply Finset.sum_congr rfl
          intro g hg
          simpa using hJstd_diag (ρ g x)
        _ = (r : ℂ) := by
          simp [r]
  have hJ_zero : ∀ {x : V}, Jmap x = 0 → x = 0 := by
    intro x hxJ
    by_contra hx
    rcases hJ_pos x hx with ⟨r, hr, hr_eq⟩
    have hxx : Jmap x x = 0 := by
      exact congrArg (fun f : Module.Dual ℂ V ↦ f x) hxJ
    rw [hr_eq] at hxx
    exact hr.ne' (Complex.ofReal_eq_zero.mp hxx)
  have hJ_inj : Function.Injective Jmap := by
    intro x y hxy
    apply sub_eq_zero.mp
    have hsub : Jmap (x - y) = 0 := by
      simpa [map_sub, hxy]
    exact hJ_zero hsub
  have hJR_smul : ∀ r : ℝ, ∀ x : V, Jmap (r • x) = r • Jmap x := by
    intro r x
    simpa using Jmap.map_smulₛₗ (r : ℂ) x
  let JR : V →ₗ[ℝ] Module.Dual ℂ V :=
    { toFun := Jmap
      map_add' := Jmap.map_add
      map_smul' := hJR_smul }
  have hJR_inj : Function.Injective JR := hJ_inj
  have hfinrankR : Module.finrank ℝ V = Module.finrank ℝ (Module.Dual ℂ V) := by
    calc
      Module.finrank ℝ V = 2 * Module.finrank ℂ V := by
        simpa [two_mul] using (finrank_real_of_complex V)
      _ = 2 * Module.finrank ℂ (Module.Dual ℂ V) := by
        rw [Subspace.dual_finrank_eq]
      _ = Module.finrank ℝ (Module.Dual ℂ V) := by
        symm
        simpa [two_mul] using (finrank_real_of_complex (Module.Dual ℂ V))
  have hJ_surj : Function.Surjective Jmap := by
    have hJR_surj : Function.Surjective JR := by
      exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrankR).mp hJR_inj
    exact hJR_surj
  let J : V ≃ₗ⋆[ℂ] Module.Dual ℂ V := LinearEquiv.ofBijective Jmap ⟨hJ_inj, hJ_surj⟩
  refine ⟨J, ?_, ?_, ?_⟩
  · intro g x y
    exact hJ_invariant g x y
  · intro x y
    exact hJ_herm x y
  · intro x hx
    exact hJ_pos x hx

/-- Helper for Theorem 13-13.2-1: a nondegenerate symmetric invariant complex bilinear form should
yield the source-proof equivariant conjugation. -/
theorem equivariant_conjugation_of_invariant_symmetric_nondegenerate_bilinForm
    (ρ : Representation ℂ G V)
    (B : BilinForm ℂ V) (hB : B.Nondegenerate) (hB_symm : B.IsSymm)
    (hB_invariant : B.IsInvariantUnder ρ) :
    ∃ σ : V →ₗ[ℝ] V,
      (∀ z : ℂ, ∀ x : V, σ (z • x) = star z • σ x) ∧
      (∀ x : V, σ (σ x) = x) ∧
      (∀ g : G, ∀ x : V, σ (ρ g x) = ρ g (σ x)) := by
  -- Route correction: the real-form packaging is now isolated above, so the only remaining work is
  -- the source-faithful linear-algebra bridge from `B` to an equivariant conjugation.
  letI : Module ℝ V := .restrictScalars ℝ ℂ V
  letI : IsScalarTower ℝ ℂ V := .restrictScalars ℝ ℂ V
  rcases exists_invariant_positive_conjugate_dual_equiv (ρ := ρ) with
    ⟨J, hJ_invariant, hJ_star, hJ_pos⟩
  have hJ_dual : ∀ g : G, ∀ x y : V, J (ρ g x) y = J x (ρ g⁻¹ y) := by
    intro g x y
    have hxy := hJ_invariant g x (ρ g⁻¹ y)
    simpa [map_mul] using hxy
  have hB_pointwise : ∀ g : G, ∀ x y : V, B (ρ g x) (ρ g y) = B x y :=
    (LinearMap.BilinForm.isInvariantUnder_iff B ρ).1 hB_invariant
  have hB_dual : ∀ g : G, ∀ x y : V, B (ρ g x) y = B x (ρ g⁻¹ y) := by
    intro g x y
    simpa using hB_pointwise g x (ρ g⁻¹ y)
  let innerCore : InnerProductSpace.Core ℂ V :=
    { inner := fun x y ↦ J x y
      conj_inner_symm := by
        intro x y
        simpa using (hJ_star y x)
      re_inner_nonneg := by
        intro x
        by_cases hx : x = 0
        · simp [hx]
        · rcases hJ_pos x hx with ⟨r, hr, hr_eq⟩
          simpa [hr_eq] using hr.le
      add_left := by
        intro x y z
        exact congrArg (fun f : Module.Dual ℂ V ↦ f z) (J.map_add x y)
      smul_left := by
        intro x y z
        exact congrArg (fun f : Module.Dual ℂ V ↦ f y) (J.map_smulₛₗ z x)
      definite := by
        intro x hx
        by_contra hne
        rcases hJ_pos x hne with ⟨r, hr, hr_eq⟩
        rw [hr_eq] at hx
        exact hr.ne' (Complex.ofReal_eq_zero.mp hx) }
  letI : InnerProductSpace.Core ℂ V := innerCore
  letI : NormedAddCommGroup V := @InnerProductSpace.Core.toNormedAddCommGroup ℂ V _ _ _ innerCore
  letI : InnerProductSpace ℂ V :=
    @InnerProductSpace.ofCore _ _ _ _ _ (show PreInnerProductSpace.Core ℂ V from inferInstance)
  let TEquiv : V ≃ₗ⋆[ℂ] V := (B.toDual hB).trans J.symm
  let T : V →ₗ⋆[ℂ] V := TEquiv.toLinearMap
  let L : V →ₗ[ℂ] V := T.comp T
  -- Comparing `B` with the invariant Hermitian form produces the source-proof conjugate-linear
  -- operator `T`.
  have hT_apply : ∀ x y : V, J (T x) y = B x y := by
    intro x y
    simp [T, TEquiv, LinearMap.BilinForm.toDual_def]
  have hT_inj : Function.Injective T := TEquiv.injective
  have hT_comm : ∀ g : G, ∀ x : V, T (ρ g x) = ρ g (T x) := by
    intro g x
    apply J.injective
    ext y
    simp [hT_apply, hB_dual, hJ_dual]
  -- The square `L = T²` is the positive linear operator from the source proof.
  have hL_symm : L.IsSymmetric := by
    intro x y
    change J (L x) y = J x (L y)
    have hTyTx : J (T y) (T x) = J x (L y) := by
      calc
        J (T y) (T x) = star (J (T x) (T y)) := by
          simpa using (hJ_star (T x) (T y)).symm
        _ = star (J (L y) x) := by
          congr 1
          calc
            J (T x) (T y) = B x (T y) := hT_apply x (T y)
            _ = B (T y) x := hB_symm.eq _ _
            _ = J (L y) x := by
              simpa [L, LinearMap.comp_apply] using (hT_apply (T y) x).symm
        _ = J x (L y) := by
          simpa using (hJ_star (L y) x)
    calc
      J (L x) y = B (T x) y := by
        simpa [L, LinearMap.comp_apply] using hT_apply (T x) y
      _ = B y (T x) := hB_symm.eq _ _
      _ = J (T y) (T x) := by
        simpa using (hT_apply y (T x)).symm
      _ = J x (L y) := hTyTx
  have hL_pos : L.IsPositive := by
    refine (LinearMap.isPositive_iff_complex L).2 ?_
    intro x
    by_cases hx : x = 0
    · simp [hx, L]
    · have hTx_ne : T x ≠ 0 := by
        intro hTx
        exact hx (hT_inj (by simpa using hTx))
      rcases hJ_pos (T x) hTx_ne with ⟨r, hr, hr_eq⟩
      have hinner : inner ℂ (L x) x = (r : ℂ) := by
        change J (L x) x = (r : ℂ)
        calc
          J (L x) x = B (T x) x := by
            simpa [L, LinearMap.comp_apply] using hT_apply (T x) x
          _ = B x (T x) := hB_symm.eq _ _
          _ = J (T x) (T x) := by
            simpa using (hT_apply x (T x)).symm
          _ = (r : ℂ) := hr_eq
      refine ⟨?_, ?_⟩
      · simpa [hinner]
      · simpa [hinner] using hr.le
  let eig : Fin (Module.finrank ℂ V) → ℝ := hL_symm.eigenvalues rfl
  let basis : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V := hL_symm.eigenvectorBasis rfl
  have hbasis_apply : ∀ i : Fin (Module.finrank ℂ V), L (basis i) = (eig i : ℂ) • basis i := by
    intro i
    simpa [basis, eig] using hL_symm.apply_eigenvectorBasis rfl i
  have hbasis_ne_zero : ∀ i : Fin (Module.finrank ℂ V), basis i ≠ 0 := by
    intro i hzero
    simpa [hzero] using basis.norm_eq_one i
  have hEig_nonneg : ∀ i : Fin (Module.finrank ℂ V), 0 ≤ eig i := by
    intro i
    exact hL_pos.nonneg_eigenvalues rfl i
  have hEig_nonzero : ∀ i : Fin (Module.finrank ℂ V), eig i ≠ 0 := by
    intro i hi
    have hzero : L (basis i) = 0 := by
      simpa [hbasis_apply i, hi]
    have hTzero : T (basis i) = 0 := by
      apply hT_inj
      simpa [L, LinearMap.comp_apply] using hzero
    exact hbasis_ne_zero i (hT_inj (by simpa using hTzero))
  have hEig_pos : ∀ i : Fin (Module.finrank ℂ V), 0 < eig i := by
    intro i
    exact lt_of_le_of_ne (hEig_nonneg i) (fun h => hEig_nonzero i h.symm)
  have hRoot_sq :
      ∀ i : Fin (Module.finrank ℂ V),
        Complex.sqrt (eig i : ℂ) * Complex.sqrt (eig i : ℂ) = (eig i : ℂ) := by
    intro i
    rw [Complex.sqrt_of_nonneg (by exact_mod_cast hEig_nonneg i)]
    have hreal : Real.sqrt (eig i) * Real.sqrt (eig i) = eig i := by
      rw [← sq]
      exact Real.sq_sqrt (hEig_nonneg i)
    exact_mod_cast hreal
  have hRoot_ne_zero :
      ∀ i : Fin (Module.finrank ℂ V), Complex.sqrt (eig i : ℂ) ≠ 0 := by
    intro i hzero
    apply hEig_nonzero i
    apply Complex.ofReal_eq_zero.mp
    calc
      (eig i : ℂ) = Complex.sqrt (eig i : ℂ) * Complex.sqrt (eig i : ℂ) := (hRoot_sq i).symm
      _ = 0 := by simp [hzero]
  have hRoot_star :
      ∀ i : Fin (Module.finrank ℂ V),
        star (Complex.sqrt (eig i : ℂ)) = Complex.sqrt (eig i : ℂ) := by
    intro i
    rw [Complex.sqrt_of_nonneg (by exact_mod_cast hEig_nonneg i)]
    simp
  let s : Finset ℂ :=
    Finset.univ.image fun i : Fin (Module.finrank ℂ V) => (eig i : ℂ)
  let p : ℂ[X] := Lagrange.interpolate s (fun z : ℂ ↦ z) (fun z : ℂ ↦ Complex.sqrt z)
  let q : ℂ[X] := Lagrange.interpolate s (fun z : ℂ ↦ z) (fun z : ℂ ↦ (Complex.sqrt z)⁻¹)
  have hs_inj : Set.InjOn (fun z : ℂ ↦ z) (s : Set ℂ) := by
    intro z hz w hw hzw
    exact hzw
  have hp_eval_eig : ∀ i : Fin (Module.finrank ℂ V), p.eval (eig i : ℂ) = Complex.sqrt (eig i : ℂ) := by
    intro i
    have hi : (eig i : ℂ) ∈ s := by
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    simpa [p, s] using
      (Lagrange.eval_interpolate_at_node (s := s) (v := fun z : ℂ ↦ z)
        (r := fun z : ℂ ↦ Complex.sqrt z) hs_inj hi)
  have hq_eval_eig :
      ∀ i : Fin (Module.finrank ℂ V), q.eval (eig i : ℂ) = (Complex.sqrt (eig i : ℂ))⁻¹ := by
    intro i
    have hi : (eig i : ℂ) ∈ s := by
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    simpa [q, s] using
      (Lagrange.eval_interpolate_at_node (s := s) (v := fun z : ℂ ↦ z)
        (r := fun z : ℂ ↦ (Complex.sqrt z)⁻¹) hs_inj hi)
  let ψ : V →ₗ[ℂ] V := Polynomial.aeval L p
  let ψInv : V →ₗ[ℂ] V := Polynomial.aeval L q
  have hψInv_basis :
      ∀ i : Fin (Module.finrank ℂ V), ψInv (basis i) = (Complex.sqrt (eig i : ℂ))⁻¹ • basis i := by
    intro i
    simpa [basis, eig, ψInv, hq_eval_eig i] using
      (Module.End.aeval_apply_of_hasEigenvector
        (f := L) (p := q) (h := hL_symm.hasEigenvector_eigenvectorBasis rfl i))
  have hT_comm_ψInv : T.comp ψInv = ψInv.comp T := by
    apply basis.toBasis.ext
    intro i
    have hTbasis_eig : L (T (basis i)) = (eig i : ℂ) • T (basis i) := by
      calc
        L (T (basis i)) = T (L (basis i)) := by rfl
        _ = T ((eig i : ℂ) • basis i) := by rw [hbasis_apply i]
        _ = star (eig i : ℂ) • T (basis i) := by
          simpa using T.map_smulₛₗ (eig i : ℂ) (basis i)
        _ = (eig i : ℂ) • T (basis i) := by simp
    have hTbasis_ne_zero : T (basis i) ≠ 0 := by
      intro hzero
      exact hbasis_ne_zero i (hT_inj (by simpa using hzero))
    calc
      T (ψInv (basis i)) = T (((Complex.sqrt (eig i : ℂ))⁻¹) • basis i) := by
        rw [hψInv_basis i]
      _ = star ((Complex.sqrt (eig i : ℂ))⁻¹) • T (basis i) := by
        simpa using T.map_smulₛₗ ((Complex.sqrt (eig i : ℂ))⁻¹) (basis i)
      _ = (Complex.sqrt (eig i : ℂ))⁻¹ • T (basis i) := by
        simp [hRoot_star i]
      _ = ψInv (T (basis i)) := by
        symm
        simpa [ψInv, hq_eval_eig i] using
          (Module.End.aeval_apply_of_hasEigenvector (f := L) (p := q)
            (h := ⟨Module.End.mem_eigenspace_iff.mpr hTbasis_eig, hTbasis_ne_zero⟩))
  have hψInv_comm_ρ : ∀ g : G, ψInv.comp (ρ g) = (ρ g).comp ψInv := by
    intro g
    apply basis.toBasis.ext
    intro i
    have hρbasis_eig : L (ρ g (basis i)) = (eig i : ℂ) • ρ g (basis i) := by
      calc
        L (ρ g (basis i)) = ρ g (L (basis i)) := by
          calc
            L (ρ g (basis i)) = T (T (ρ g (basis i))) := rfl
            _ = T (ρ g (T (basis i))) := by rw [hT_comm g (basis i)]
            _ = ρ g (T (T (basis i))) := by rw [hT_comm g (T (basis i))]
            _ = ρ g (L (basis i)) := rfl
        _ = ρ g ((eig i : ℂ) • basis i) := by rw [hbasis_apply i]
        _ = (eig i : ℂ) • ρ g (basis i) := by
          simpa using (ρ g).map_smul (eig i : ℂ) (basis i)
    have hρbasis_ne_zero : ρ g (basis i) ≠ 0 := by
      intro hzero
      apply hbasis_ne_zero i
      have hback := congrArg (ρ g⁻¹) hzero
      simpa [map_mul] using hback
    calc
      ψInv (ρ g (basis i)) = (Complex.sqrt (eig i : ℂ))⁻¹ • ρ g (basis i) := by
        simpa [ψInv, hq_eval_eig i] using
          (Module.End.aeval_apply_of_hasEigenvector (f := L) (p := q)
            (h := ⟨Module.End.mem_eigenspace_iff.mpr hρbasis_eig, hρbasis_ne_zero⟩))
      _ = ρ g (((Complex.sqrt (eig i : ℂ))⁻¹) • basis i) := by
        symm
        simpa using (ρ g).map_smul ((Complex.sqrt (eig i : ℂ))⁻¹) (basis i)
      _ = ρ g (ψInv (basis i)) := by
        rw [hψInv_basis i]
  have hψInv_sq_L : ψInv.comp (ψInv.comp L) = 1 := by
    apply basis.toBasis.ext
    intro i
    calc
      ψInv (ψInv (L (basis i))) = ψInv (((eig i : ℂ) * (Complex.sqrt (eig i : ℂ))⁻¹) • basis i) := by
        rw [hbasis_apply i, LinearMap.map_smul, hψInv_basis i]
        simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]
      _ =
          (((eig i : ℂ) * (Complex.sqrt (eig i : ℂ))⁻¹) *
            (Complex.sqrt (eig i : ℂ))⁻¹) • basis i := by
        rw [LinearMap.map_smul, hψInv_basis i]
        simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]
      _ = basis i := by
        have hscalar :
            (((eig i : ℂ) * (Complex.sqrt (eig i : ℂ))⁻¹) *
              (Complex.sqrt (eig i : ℂ))⁻¹) = 1 := by
          field_simp [hRoot_ne_zero i]
          simpa [sq] using (hRoot_sq i).symm
        simp [hscalar]
  let σStar : V →ₗ⋆[ℂ] V := ψInv.comp T
  let σ : V →ₗ[ℝ] V :=
    { toFun := σStar
      map_add' := σStar.map_add
      map_smul' := by
        intro r x
        simpa using σStar.map_smulₛₗ (r : ℂ) x }
  refine ⟨σ, ?_, ?_, ?_⟩
  · intro z x
    -- The normalization is still conjugate-linear because `ψInv` is complex-linear.
    change ψInv (T (z • x)) = star z • ψInv (T x)
    rw [T.map_smulₛₗ]
    simpa using ψInv.map_smul (star z) (T x)
  · intro x
    -- Commute `T` past `ψInv`, then use `ψInv² ∘ L = 1`.
    change ψInv (T (ψInv (T x))) = x
    have hcomm := congrArg (fun f : V →ₗ⋆[ℂ] V => f (T x)) hT_comm_ψInv
    rw [show T (ψInv (T x)) = ψInv (T (T x)) by
      simpa [LinearMap.comp_apply] using hcomm]
    have hsquare := congrArg (fun f : V →ₗ[ℂ] V => f x) hψInv_sq_L
    simpa [L, LinearMap.comp_apply] using hsquare
  · intro g x
    -- Equivariance is inherited from the commutation of both `T` and `ψInv` with the action.
    change ψInv (T (ρ g x)) = ρ g (ψInv (T x))
    rw [hT_comm g x]
    have hcomm := congrArg (fun f : V →ₗ[ℂ] V => f (T x)) (hψInv_comm_ρ g)
    simpa [LinearMap.comp_apply] using hcomm

-- Proof sketch: if `ρ` is realizable over `ℝ`, average any positive definite real quadratic form
-- on the real model and extend scalars to obtain a nondegenerate symmetric invariant complex
-- bilinear form. Conversely, from such a form choose an invariant Hermitian product, build the
-- associated antilinear involution, and recover a `G`-stable real form whose complexification is
-- equivalent to `ρ`.
/-- Theorem 13-13.2-1 (2): a finite-dimensional complex representation is realizable over `ℝ` if
and only if it admits a nondegenerate symmetric `G`-invariant complex bilinear form. -/
theorem isRealizableOverReal_iff_exists_invariant_nondegenerate_symmetric_bilinForm
    (ρ : Representation ℂ G V) :
    IsRealizableOver ℝ ρ ↔
      ∃ B : BilinForm ℂ V,
        B.Nondegenerate ∧ B.IsSymm ∧ B.IsInvariantUnder ρ := by
  -- Route correction: the self-duality and character criteria above are now proved directly.
  constructor
  · intro hρ
    -- The easy direction follows the source proof directly: average on the real model, extend
    -- scalars, then transport the form across the chosen complexification equivalence.
    exact exists_invariant_nondegenerate_symmetric_bilinForm_of_isRealizableOverReal ρ hρ
  · rintro ⟨B, hB, hB_symm, hB_invariant⟩
    -- Reduce the hard direction to the single named source-faithful helper built from `B`.
    rcases
        equivariant_conjugation_of_invariant_symmetric_nondegenerate_bilinForm
          ρ B hB hB_symm hB_invariant with
      ⟨σ, hσ_smul, hσ_sq, hσ_equiv⟩
    -- Once the equivariant conjugation is available, the fixed real form and its tensor
    -- decomposition realize `ρ` over `ℝ`.
    exact isRealizableOverReal_of_equivariant_conjugation ρ σ hσ_smul hσ_sq hσ_equiv

end

end Representation
