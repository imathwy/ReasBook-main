import Mathlib
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.RingTheory.Morita.Matrix
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_13_13_2_3 (from Chap13) -/
noncomputable section

open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped TensorProduct
open scoped ComplexStarModule

universe u v

namespace LinearMap.BilinForm

section

variable {R : Type*} [CommSemiring R]
variable {G : Type u} [Monoid G]
variable {V : Type v} [AddCommMonoid V] [Module R V]

/-- Helper for Proposition 13-13.2-3: a bilinear form on a representation is invariant when each
group element acts by an isometry for that form. -/
def IsInvariantUnder (B : BilinForm R V) (ρ : Representation R G V) : Prop :=
  ∀ g : G, B.comp (ρ g) (ρ g) = B

/-- Helper for Proposition 13-13.2-3: invariance of a bilinear form is equivalent to the
pointwise fixed-value identity on every pair of vectors. -/
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

section

variable (K : Type*) [Field K]
variable {L : Type*} [Field L] [Algebra K L]
variable {G : Type u}

/-- Helper for Proposition 13-13.2-3: an `L`-valued class function is `K`-valued when every value
lies in the image of the coefficient embedding `K → L`. -/
def IsValuedInBaseField (χ : G → L) : Prop :=
  χ ∈ Submodule.pi Set.univ
    (fun _ : G ↦ LinearMap.range ((Algebra.linearMap K L).restrictScalars ℤ))

/-- Helper for Proposition 13-13.2-3: being `K`-valued is equivalent to lying in the range of the
coefficientwise embedding from `K`-valued functions. -/
theorem isValuedInBaseField_iff_mem_pointwiseAlgebraMap_range (χ : G → L) :
    IsValuedInBaseField K χ ↔
      χ ∈ LinearMap.range
        (((Algebra.linearMap K L).restrictScalars ℤ).compLeft G) := by
  simp [IsValuedInBaseField, LinearMap.range_compLeft]

end

section

variable {k : Type*} [Field k]
variable {G : Type u} [Group G]
variable {V : Type v} [AddCommGroup V] [Module k V]

/-- Helper for Proposition 13-13.2-3: an invariant bilinear form is exactly a `G`-equivariant map
to the dual representation. -/
theorem isInvariantUnder_iff_dual_intertwining
    (B : BilinForm k V) (ρ : Representation k G V) :
    B.IsInvariantUnder ρ ↔ ∀ g : G, B ∘ₗ ρ g = ρ.dual g ∘ₗ B := by
  constructor
  · intro h g
    ext x y
    have hxy := (LinearMap.BilinForm.isInvariantUnder_iff B ρ).1 h g x (ρ g⁻¹ y)
    simpa using hxy
  · intro h
    rw [LinearMap.BilinForm.isInvariantUnder_iff]
    intro g x y
    have hxy := LinearMap.congr_fun (h g) x
    have hxy' := LinearMap.congr_fun hxy (ρ g y)
    simpa [Representation.dual_apply, Module.Dual.transpose_apply] using hxy'

end

section

variable {k : Type*} [Field k]
variable {G : Type u} [Group G]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Helper for Proposition 13-13.2-3: a finite-dimensional representation is equivariantly
self-dual if and only if it admits a nondegenerate invariant bilinear form. -/
theorem nonempty_equiv_dual_iff_exists_invariant_nondegenerate_bilinForm
    (ρ : Representation k G V) :
    Nonempty (ρ.Equiv ρ.dual) ↔
      ∃ B : BilinForm k V, B.Nondegenerate ∧ B.IsInvariantUnder ρ := by
  constructor
  · rintro ⟨e⟩
    refine ⟨e.toLinearMap, ?_, ?_⟩
    refine ⟨?_, ?_⟩
    · rw [LinearMap.separatingLeft_iff_ker_eq_bot]
      exact LinearMap.ker_eq_bot.mpr e.toLinearEquiv.injective
    · intro y hy
      refine (Module.forall_dual_apply_eq_zero_iff k y).mp ?_
      intro f
      rcases e.toLinearEquiv.surjective f with ⟨x, rfl⟩
      exact hy x
    rw [isInvariantUnder_iff_dual_intertwining]
    intro g
    exact e.isIntertwining' g
  · rintro ⟨B, hB, hB_invariant⟩
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
variable {V : Type v} [AddCommGroup V] [Module ℂ V]

variable (ρ : Representation ℂ G V) [ρ.IsIrreducible]

/-- Helper for Proposition 13-13.2-3: for an irreducible complex representation of a finite
group, equality with the dual character already forces an equivariant self-duality. -/
theorem nonempty_equiv_dual_of_character_eq (ρ : Representation ℂ G V)
    [ρ.IsIrreducible] [FiniteDimensional ℂ V] (hχ : ρ.character = ρ.dual.character) :
    Nonempty (ρ.Equiv ρ.dual) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (NeZero.ne (Nat.card G : ℂ))
  -- Compare the intertwining-space dimension with the self-pairing of the character.
  have hdim :
      (Module.finrank ℂ (ρ.IntertwiningMap ρ.dual) : ℂ) = 1 := by
    calc
      (Module.finrank ℂ (ρ.IntertwiningMap ρ.dual) : ℂ) =
          (Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.dual.character g * ρ.character g⁻¹ := by
            symm
            exact Representation.card_inv_mul_sum_char_mul_char_eq_finrank (ρ := ρ) (σ := ρ.dual)
      _ = (Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g * ρ.character g⁻¹ := by
            congr 1
            apply Finset.sum_congr rfl
            intro g _
            rw [hχ]
      _ = (Module.finrank ℂ (ρ.IntertwiningMap ρ) : ℂ) := by
            rw [Representation.card_inv_mul_sum_char_mul_char_eq_finrank (ρ := ρ) (σ := ρ)]
      _ = 1 := by
            exact_mod_cast (Representation.IsIrreducible.finrank_intertwiningMap_self (ρ := ρ))
  have hfinrank_ne_zero : Module.finrank ℂ (ρ.IntertwiningMap ρ.dual) ≠ 0 := by
    intro hzero
    have hzero' : (0 : ℂ) = 1 := by
      simpa [hzero] using hdim
    exact zero_ne_one hzero'
  letI : Nontrivial (ρ.IntertwiningMap ρ.dual) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (Nat.pos_of_ne_zero hfinrank_ne_zero)
  obtain ⟨f, hf_ne⟩ := exists_ne (0 : ρ.IntertwiningMap ρ.dual)
  have hf_inj : Function.Injective f :=
    (Representation.IsIrreducible.injective_or_eq_zero (ρ := ρ) (σ := ρ.dual) f).resolve_right
      hf_ne
  have hf_surj : Function.Surjective f := by
    have hfinrankV : Module.finrank ℂ V = Module.finrank ℂ (Module.Dual ℂ V) := by
      simpa using (Subspace.dual_finrank_eq (K := ℂ) (V := V)).symm
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrankV).mp hf_inj
  have hf_bij : Function.Bijective f := ⟨hf_inj, hf_surj⟩
  -- A nonzero intertwiner between irreducibles is bijective, hence a representation equivalence.
  exact Representation.nonempty_equiv_of_bijective_intertwiningMap
    (ρ1 := ρ) (ρ2 := ρ.dual) f hf_bij

/-- Helper for Proposition 13-13.2-3: a finite-dimensional complex representation of a finite
group has real-valued character if and only if it is equivariantly self-dual. -/
theorem hasRealValuedCharacter_iff_nonempty_equiv_dual (ρ : Representation ℂ G V)
    [ρ.IsIrreducible] [FiniteDimensional ℂ V] :
    IsValuedInBaseField ℝ ρ.character ↔ Nonempty (ρ.Equiv ρ.dual) := by
  letI : Fintype G := Fintype.ofFinite G
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : NeZero (Nat.card G : ℂ) := ⟨hcard_ne⟩
  have hval :
      IsValuedInBaseField ℝ ρ.character ↔
        ∀ g : G, star (ρ.character g) = ρ.character g := by
    rw [Representation.isValuedInBaseField_iff_mem_pointwiseAlgebraMap_range]
    constructor
    · rintro ⟨χR, hχR⟩ g
      rw [← congrFun hχR g]
      simp
    · intro hstar
      refine ⟨fun g ↦ (ρ.character g).re, ?_⟩
      ext g
      exact (Complex.conj_eq_iff_re).mp (hstar g)
  rw [hval]
  constructor
  · intro hstar
    have hchar : ρ.character = ρ.dual.character := by
      ext g
      rw [Representation.char_dual_eq_star]
      exact (hstar g).symm
    exact nonempty_equiv_dual_of_character_eq ρ hchar
  · rintro ⟨e⟩ g
    rw [← Representation.char_dual_eq_star]
    exact (congrFun (Representation.char_iso e) g).symm

/-- Helper for Proposition 13-13.2-3: a finite-dimensional complex representation has real-valued
character if and only if it admits a nondegenerate invariant complex bilinear form. -/
theorem hasRealValuedCharacter_iff_exists_invariant_nondegenerate_bilinForm
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] [FiniteDimensional ℂ V] :
    IsValuedInBaseField ℝ ρ.character ↔
      ∃ B : BilinForm ℂ V, B.Nondegenerate ∧ B.IsInvariantUnder ρ := by
  rw [hasRealValuedCharacter_iff_nonempty_equiv_dual,
    nonempty_equiv_dual_iff_exists_invariant_nondegenerate_bilinForm]

/-- Helper for Proposition 13-13.2-3: a finite-dimensional real representation of a finite group
admits an invariant symmetric nondegenerate real bilinear form obtained by averaging a standard
form. -/
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
  · -- The identity term in the average is positive on any nonzero vector, forcing nondegeneracy.
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
      (Equiv.sum_comp (Equiv.mulRight a) (fun g : G ↦ Bstd (ρ g x) (ρ g y)))

/-- Helper for Proposition 13-13.2-3: scalar extension transports a real invariant symmetric
nondegenerate bilinear form to the corresponding complex form. -/
theorem baseChange_nondegenerate_invariant_symmetric_bilinForm
    {W : Type v} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (ρ : Representation ℝ G W) (B : BilinForm ℝ W)
    (hB : B.Nondegenerate) (hB_symm : B.IsSymm) (hB_invariant : B.IsInvariantUnder ρ) :
    let BC := B.baseChange ℂ
    BC.Nondegenerate ∧ BC.IsSymm ∧ BC.IsInvariantUnder (Representation.scalarExtension ρ) := by
  classical
  let BC := B.baseChange ℂ
  refine ⟨?_, ?_, ?_⟩
  · -- Compare the Gram matrices before and after scalar extension.
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
        ((LinearMap.BilinForm.toMatrix b B).map (algebraMap ℝ ℂ)).det =
          algebraMap ℝ ℂ ((LinearMap.BilinForm.toMatrix b B).det) := by
      simpa using
        (RingHom.map_det (algebraMap ℝ ℂ) (LinearMap.BilinForm.toMatrix b B)).symm
    rw [hmapdet]
    intro hzero
    exact hdet (Complex.ofReal_eq_zero.mp hzero)
  · -- Symmetry can be checked on pure tensors and then extended by bilinearity.
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
  · -- The invariant identity likewise reduces to pure tensors.
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
            change BC (((ρ g).baseChange ℂ) (a ⊗ₜ[ℝ] x))
                (((ρ g).baseChange ℂ) (b ⊗ₜ[ℝ] y)) = BC (a ⊗ₜ[ℝ] x) (b ⊗ₜ[ℝ] y)
            simp [BC, hB_pointwise g x y, mul_assoc, mul_left_comm, mul_comm]
        | add y₁ y₂ hy₁ hy₂ =>
            simp [hy₁, hy₂]
    | add x₁ x₂ hx₁ hx₂ =>
        simp [hx₁, hx₂]

/-- Helper for Proposition 13-13.2-3: a real model of the representation yields the invariant
symmetric nondegenerate complex bilinear form used in the source proof. -/
theorem exists_invariant_nondegenerate_symmetric_bilinForm_of_isRealizableOverReal
    (ρ : Representation ℂ G V) [FiniteDimensional ℂ V] (hρ : IsRealizableOver ℝ ρ) :
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
  · -- Transport nondegeneracy across the chosen scalar-extension equivalence.
    simpa [BV, BC] using hBC.1.congr e.toLinearEquiv
  · -- Symmetry is preserved under congruence by a linear equivalence.
    refine ⟨?_⟩
    intro x y
    simpa [BV, BC] using hBC.2.1.eq (e.toLinearEquiv.symm x) (e.toLinearEquiv.symm y)
  · -- Move the invariance identity back across `e` and use the base-changed real form.
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
    rw [show BV (ρ g x) (ρ g y) =
        BC (e.toLinearEquiv.symm (ρ g x)) (e.toLinearEquiv.symm (ρ g y)) by rfl]
    rw [show BV x y = BC (e.toLinearEquiv.symm x) (e.toLinearEquiv.symm y) by rfl]
    rw [hx, hy]
    exact ((LinearMap.BilinForm.isInvariantUnder_iff BC (Representation.scalarExtension ρ₀)).1
      hBC.2.2) g _ _

/-- Helper for Proposition 13-13.2-3: an equivariant conjugation on `V` determines a `G`-stable
real form whose complex span is all of `V`. -/
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
  · -- The real and imaginary parts of every vector are fixed by `σ`, so these fixed vectors span.
    simpa using (span_selfAdjoint (A := V))

/-- Helper for Proposition 13-13.2-3: every vector in a complex star module splits as its
self-adjoint real part plus `I` times its self-adjoint imaginary part. -/
theorem exists_selfAdjoint_real_imaginary_decomposition
    [Module ℝ V] [IsScalarTower ℝ ℂ V] [StarAddMonoid V] [StarModule ℂ V]
    (v : V) :
    ∃ a b : selfAdjoint V, (a : V) + Complex.I • (b : V) = v := by
  -- Package the standard real/imaginary-part decomposition for later tensor arguments.
  refine ⟨ℜ v, ℑ v, ?_⟩
  simpa using (realPart_add_I_smul_imaginaryPart v)

/-- Helper for Proposition 13-13.2-3: the explicit real/imaginary inverse on the fixed real form
recovers each pure tensor. -/
theorem tensor_fixed_real_form_inverse_on_pure_tensors
    [StarAddMonoid V] [StarModule ℂ V]
    (z : ℂ) (w : selfAdjoint.submodule ℝ V) :
    (1 : ℂ) ⊗ₜ[ℝ] (ℜ (z • (w : V)) : selfAdjoint.submodule ℝ V) +
        Complex.I ⊗ₜ[ℝ] (ℑ (z • (w : V)) : selfAdjoint.submodule ℝ V) =
      z ⊗ₜ[ℝ] w := by
  -- Rewrite the real and imaginary parts using that `w` is fixed by the star operation.
  have hre : ℜ (z • (w : V)) = ((z.re : ℝ) • w : selfAdjoint.submodule ℝ V) := by
    rw [realPart_smul]
    simp
    rfl
  have him : ℑ (z • (w : V)) = ((z.im : ℝ) • w : selfAdjoint.submodule ℝ V) := by
    rw [imaginaryPart_smul]
    simp
    rfl
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

/-- Helper for Proposition 13-13.2-3: the fixed real form of a complex star module complexifies
back to the whole complex module. -/
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
            -- Move the real scalar through the complex scalar by rewriting both sides as a single
            -- complex scalar action.
            calc
              z • (r • (w : V)) = (z * (r : ℂ)) • (w : V) := by
                simpa [Complex.coe_smul] using (mul_smul z (r : ℂ) (w : V)).symm
              _ = ((r : ℂ) * z) • (w : V) := by
                rw [mul_comm]
              _ = r • z • (w : V) := by
                simpa [Complex.coe_smul] using (mul_smul (r : ℂ) z (w : V)) }
      map_add' := by
        intro z₁ z₂
        ext w
        simp [add_smul]
      map_smul' := by
        intro r z
        ext w
        -- The first tensor factor is only `ℝ`-linear here, so express the real action on `ℂ`
        -- through multiplication in `ℂ`.
        simpa [Algebra.smul_def] using (mul_smul (r : ℂ) z (w : V)) }
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
    -- The forward map sends the explicit real/imaginary inverse back to `x`.
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
    -- The inverse candidate is additive because real and imaginary parts are additive.
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

/-- Helper for Proposition 13-13.2-3: an equivariant conjugation identifies `V` with the complex
scalar extension of its fixed real form, hence realizes the representation over `ℝ`. -/
theorem isRealizableOverReal_of_equivariant_conjugation
    (ρ : Representation ℂ G V) [FiniteDimensional ℂ V] (σ : V →ₗ[ℝ] V)
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

/-- Helper for Proposition 13-13.2-3: averaging the standard conjugate-duality over a finite group
produces an invariant positive conjugate-linear equivalence from `V` to its complex dual. -/
theorem exists_invariant_positive_conjugate_dual_equiv
    (ρ : Representation ℂ G V) [FiniteDimensional ℂ V] :
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

/-- Helper for Proposition 13-13.2-3: an invariant symmetric nondegenerate bilinear form should
yield the source-proof equivariant conjugation. -/
theorem equivariant_conjugation_of_invariant_symmetric_nondegenerate_bilinForm
    (ρ : Representation ℂ G V) [FiniteDimensional ℂ V]
    (B : BilinForm ℂ V) (hB : B.Nondegenerate) (hBsymm : B.IsSymm)
    (hBinv : B.IsInvariantUnder ρ) :
    ∃ σ : V →ₗ[ℝ] V,
      (∀ z : ℂ, ∀ x : V, σ (z • x) = star z • σ x) ∧
      (∀ x : V, σ (σ x) = x) ∧
      (∀ g : G, ∀ x : V, σ (ρ g x) = ρ g (σ x)) := by
  -- Route correction: the real-form packaging is already isolated above, so the only remaining
  -- work is the source-faithful linear-algebra bridge from `B` to an equivariant conjugation.
  letI : Module ℝ V := .restrictScalars ℝ ℂ V
  letI : IsScalarTower ℝ ℂ V := .restrictScalars ℝ ℂ V
  rcases exists_invariant_positive_conjugate_dual_equiv (ρ := ρ) with
    ⟨J, hJ_invariant, hJ_star, hJ_pos⟩
  have hJ_dual : ∀ g : G, ∀ x y : V, J (ρ g x) y = J x (ρ g⁻¹ y) := by
    intro g x y
    have hxy := hJ_invariant g x (ρ g⁻¹ y)
    simpa [map_mul] using hxy
  have hB_pointwise : ∀ g : G, ∀ x y : V, B (ρ g x) (ρ g y) = B x y :=
    (LinearMap.BilinForm.isInvariantUnder_iff B ρ).1 hBinv
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
            _ = B (T y) x := hBsymm.eq _ _
            _ = J (L y) x := by
              simpa [L, LinearMap.comp_apply] using (hT_apply (T y) x).symm
        _ = J x (L y) := by
          exact hJ_star (L y) x
    calc
      J (L x) y = B (T x) y := by
        simpa [L, LinearMap.comp_apply] using hT_apply (T x) y
      _ = B y (T x) := hBsymm.eq _ _
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
          _ = B x (T x) := hBsymm.eq _ _
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
      exact hT_inj (by simpa [L, LinearMap.comp_apply] using hzero)
    exact hbasis_ne_zero i (hT_inj (by simpa using hTzero))
  have hEig_pos : ∀ i : Fin (Module.finrank ℂ V), 0 < eig i := by
    intro i
    exact lt_of_le_of_ne (hEig_nonneg i) (fun h => hEig_nonzero i h.symm)
  have hRoot_sq :
      ∀ i : Fin (Module.finrank ℂ V),
        Complex.sqrt (eig i : ℂ) * Complex.sqrt (eig i : ℂ) = (eig i : ℂ) := by
    intro i
    rw [Complex.sqrt_of_nonneg (by exact_mod_cast hEig_nonneg i)]
    simpa [pow_two] using congrArg (fun r : ℝ => (r : ℂ)) (Real.sq_sqrt (hEig_nonneg i))
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
  let p : Polynomial ℂ := Lagrange.interpolate s (fun z : ℂ ↦ z) (fun z : ℂ ↦ Complex.sqrt z)
  let q : Polynomial ℂ := Lagrange.interpolate s (fun z : ℂ ↦ z) (fun z : ℂ ↦ (Complex.sqrt z)⁻¹)
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
    simpa [ψInv, basis, eig, hq_eval_eig i] using
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
          simpa [pow_two] using (hRoot_sq i).symm
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

/-- Helper for Proposition 13-13.2-3: realizability over `ℝ` is equivalent to the existence of a
nondegenerate symmetric invariant complex bilinear form. -/
theorem isRealizableOverReal_iff_exists_invariant_nondegenerate_symmetric_bilinForm
    (ρ : Representation ℂ G V) [FiniteDimensional ℂ V] :
    IsRealizableOver ℝ ρ ↔
      ∃ B : BilinForm ℂ V,
        B.Nondegenerate ∧ B.IsSymm ∧ B.IsInvariantUnder ρ := by
  -- Route correction: keep the source-proof architecture `real model -> symmetric form` and
  -- `symmetric form -> conjugation -> fixed real form`, rather than switching to a later shortcut.
  constructor
  · intro hρ
    exact exists_invariant_nondegenerate_symmetric_bilinForm_of_isRealizableOverReal ρ hρ
  · rintro ⟨B, hB, hBsymm, hBinv⟩
    rcases
        equivariant_conjugation_of_invariant_symmetric_nondegenerate_bilinForm
          ρ B hB hBsymm hBinv with
      ⟨σ, hσ_smul, hσ_sq, hσ_equiv⟩
    -- Once the equivariant conjugation is available, the fixed real form and its tensor
    -- decomposition realize `ρ` over `ℝ`.
    exact isRealizableOverReal_of_equivariant_conjugation ρ σ hσ_smul hσ_sq hσ_equiv

-- Source/core/bridge triage: this is a `source-facing` bridge from invariant bilinear forms to
-- the Chapter `12` owner `IsValuedInBaseField ℝ` applied to the character `ρ.character`.
-- Irreducibility is essential here, not cosmetic: the source proposition is about irreducible
-- representations, and without that hypothesis the zero-dimensional trivial representation would
-- be a counterexample.
-- Finite-dimensionality is automatic from `IsIrreducible.finiteDimensional_of_finite ρ`.
-- Proof sketch: if `ρ` were not of type `1`, then `ρ` would have real-valued character. By
-- Theorem `13-13.2-1 (1)`, there would exist a nondegenerate invariant bilinear form. An
-- irreducible representation is nontrivial, so such a form is nonzero, contradicting the
-- hypothesis.
/-- Proposition 13-13.2-3 (1): source part (a). If an irreducible complex representation of a
finite group has no nonzero `G`-invariant bilinear form, then its character is not real-valued.
Finite-dimensionality is automatic here. -/
theorem isTypeOne_of_no_nonzero_invariant_bilinForm
    (hρ : ¬ ∃ B : BilinForm ℂ V, B.IsInvariantUnder ρ ∧ B ≠ 0) :
    ¬ IsValuedInBaseField ℝ ρ.character := by
  letI := IsIrreducible.finiteDimensional_of_finite ρ
  letI : Nontrivial V := by
    by_contra hV
    letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    have hbot : (⊥ : Subrepresentation ρ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      ext y
      constructor
      · intro _
        trivial
      · intro _
        simpa using (Subsingleton.elim y 0)
    exact bot_ne_top hbot
  intro hreal
  rcases
      (hasRealValuedCharacter_iff_exists_invariant_nondegenerate_bilinForm ρ).1 hreal with
    ⟨B, hBnondeg, hBinv⟩
  exact hρ ⟨B, hBinv, hBnondeg.ne_zero⟩

end

end Representation

namespace LinearMap.BilinForm

section

variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]

variable (ρ : Representation ℂ G V) [ρ.IsIrreducible]

/-- Helper for Proposition 13-13.2-3: an invariant bilinear form packages into the canonical
equivariant map from the representation to its dual. -/
noncomputable def toDual_intertwiningMap_of_isInvariantUnder
    (B : BilinForm ℂ V) (hB : B.IsInvariantUnder ρ) :
    ρ.IntertwiningMap ρ.dual :=
  -- Repackage the source-language invariance condition using the dual-representation owner API.
  ⟨B, (Representation.isInvariantUnder_iff_dual_intertwining B ρ).1 hB⟩

-- Proof sketch: a nonzero invariant bilinear form gives a nonzero intertwining map
-- `V → Module.Dual ℂ V`. For an irreducible representation, Schur's lemma identifies the
-- intertwining space with a one-dimensional `ℂ`-vector space, so any two such forms differ by a
-- unique nonzero scalar. Finite-dimensionality is automatic from
-- `IsIrreducible.finiteDimensional_of_finite ρ`.
/-- Proposition 13-13.2-3 (2): source part (b). Any two nonzero `G`-invariant bilinear forms on
an irreducible complex representation of a finite group differ by a homothety. Finite-dimensionality
is automatic here. -/
theorem exists_units_smul_eq_of_isInvariantUnder
    (B₁ B₂ : BilinForm ℂ V)
    (hB₁ : B₁.IsInvariantUnder ρ) (hB₁0 : B₁ ≠ 0)
    (hB₂ : B₂.IsInvariantUnder ρ) (hB₂0 : B₂ ≠ 0) :
    ∃ c : ℂˣ, B₂ = (c : ℂ) • B₁ := by
  letI := Representation.IsIrreducible.finiteDimensional_of_finite ρ
  have hB₁_nondeg : B₁.Nondegenerate := by
    let f : ρ.IntertwiningMap ρ.dual := toDual_intertwiningMap_of_isInvariantUnder ρ B₁ hB₁
    have hf_ne : f ≠ 0 := by
      intro hf
      apply hB₁0
      ext x y
      have hfx : f x = 0 := by
        simpa using congrArg (fun T : ρ.IntertwiningMap ρ.dual ↦ T x) hf
      exact congrArg (fun φ : Module.Dual ℂ V ↦ φ y) hfx
    have hf_inj : Function.Injective f :=
      (Representation.IsIrreducible.injective_or_eq_zero (ρ := ρ) (σ := ρ.dual) f).resolve_right
        hf_ne
    exact
      (LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot (B := B₁)).2
        (LinearMap.ker_eq_bot.mpr hf_inj)
  let e : ρ.Equiv ρ.dual :=
    Representation.Equiv.mk (B₁.toDual hB₁_nondeg) <| by
      exact (Representation.isInvariantUnder_iff_dual_intertwining B₁ ρ).1 hB₁
  let f : ρ.IntertwiningMap ρ :=
    e.symm.toIntertwiningMap.comp (toDual_intertwiningMap_of_isInvariantUnder ρ B₂ hB₂)
  -- Move the second invariant form back to an equivariant endomorphism of `ρ`, then apply Schur.
  obtain ⟨c, hc⟩ := Representation.intertwiningMap_eq_smul_id (ρ := ρ) f
  have hB₂_eq : B₂ = c • B₁ := by
    ext x y
    have hxy : f x = c • x := by
      simpa using congrArg (fun T : ρ.IntertwiningMap ρ ↦ T x) hc
    have hxy' := congrArg (fun z : V ↦ B₁ z y) hxy
    -- Evaluating through `B₁.toDual` converts the endomorphism identity back into a form identity.
    simp [f, e, LinearMap.BilinForm.apply_toDual_symm_apply] at hxy'
    simpa [smul_eq_mul] using hxy'
  have hc0 : c ≠ 0 := by
    intro hc0
    apply hB₂0
    rw [hB₂_eq, hc0, zero_smul]
  exact ⟨Units.mk0 c hc0, by simp [hB₂_eq]⟩

-- Proof sketch: a nonzero invariant bilinear form corresponds to a nonzero equivariant map
-- `V → Module.Dual ℂ V`. Since `ρ` is irreducible, Schur's lemma forces that map to be an
-- isomorphism of finite-group representations, which is exactly nondegeneracy of the form.
-- Finite-dimensionality is automatic from `IsIrreducible.finiteDimensional_of_finite ρ`.
/-- Proposition 13-13.2-3 (3): source part (b). Every nonzero `G`-invariant bilinear form on an
irreducible complex representation of a finite group is nondegenerate. Finite-dimensionality is
automatic here. -/
theorem nondegenerate_of_nonzero_isInvariantUnder
    (B : BilinForm ℂ V) (hB : B.IsInvariantUnder ρ) (hB0 : B ≠ 0) :
    B.Nondegenerate := by
  letI := Representation.IsIrreducible.finiteDimensional_of_finite ρ
  let f : ρ.IntertwiningMap ρ.dual := toDual_intertwiningMap_of_isInvariantUnder ρ B hB
  have hf_ne : f ≠ 0 := by
    intro hf
    apply hB0
    ext x y
    have hfx : f x = 0 := by
      simpa using congrArg (fun T : ρ.IntertwiningMap ρ.dual ↦ T x) hf
    exact congrArg (fun φ : Module.Dual ℂ V ↦ φ y) hfx
  -- The kernel argument is packaged by Schur as: a nonzero map out of an irreducible is injective.
  have hf_inj : Function.Injective f :=
    (Representation.IsIrreducible.injective_or_eq_zero (ρ := ρ) (σ := ρ.dual) f).resolve_right
      hf_ne
  -- Injectivity of `B.toDual` is exactly trivial kernel, hence nondegeneracy.
  exact
    (LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot (B := B)).2
      (LinearMap.ker_eq_bot.mpr hf_inj)

/-- Helper for Proposition 13-13.2-3: over `ℂ`, a bilinear form that is both symmetric and
alternating must vanish. -/
lemma eq_zero_of_isSymm_and_isAlt
    (B : BilinForm ℂ V) (hSymm : B.IsSymm) (hAlt : B.IsAlt) :
    B = 0 := by
  ext x y
  have hneg : -B x y = B x y := by
    rw [hAlt.neg_eq, hSymm.eq]
  have hsum : B x y + B x y = 0 := by
    have hsum' := congrArg (fun z : ℂ ↦ z + B x y) hneg
    simpa [add_assoc, add_comm, add_left_comm] using hsum'.symm
  have htwo : (2 : ℂ) * B x y = 0 := by
    simpa [two_mul] using hsum
  exact (mul_eq_zero.mp htwo).resolve_left two_ne_zero

-- Proof sketch: decompose `B` as the sum of its symmetric and alternating parts. Both parts are
-- again invariant, and uniqueness up to homothety forces one of them to vanish, so `B` is either
-- symmetric or alternating. Finite-dimensionality is automatic from
-- `IsIrreducible.finiteDimensional_of_finite ρ`.
/-- Proposition 13-13.2-3 (4): source part (b). Every nonzero `G`-invariant bilinear form on an
irreducible complex representation of a finite group is either symmetric or alternating.
Finite-dimensionality is automatic here. -/
theorem isSymm_or_isAlt_of_nonzero_isInvariantUnder
    (B : BilinForm ℂ V) (hB : B.IsInvariantUnder ρ) (_hB0 : B ≠ 0) :
    B.IsSymm ∨ B.IsAlt := by
  let Bplus : BilinForm ℂ V := (1 / 2 : ℂ) • (B + B.flip)
  let Bminus : BilinForm ℂ V := (1 / 2 : ℂ) • (B - B.flip)
  have hflip : B.flip.IsInvariantUnder ρ := by
    -- Flipping the variables preserves the same source invariance identity.
    rw [LinearMap.BilinForm.isInvariantUnder_iff]
    intro g x y
    simpa [LinearMap.BilinForm.flip_apply] using
      (LinearMap.BilinForm.isInvariantUnder_iff B ρ).1 hB g y x
  have hBplus : Bplus.IsInvariantUnder ρ := by
    rw [LinearMap.BilinForm.isInvariantUnder_iff]
    intro g x y
    have hBxy := (LinearMap.BilinForm.isInvariantUnder_iff B ρ).1 hB g x y
    have hflipxy := (LinearMap.BilinForm.isInvariantUnder_iff B.flip ρ).1 hflip g x y
    simp [Bplus, hBxy, hflipxy]
  have hBminus : Bminus.IsInvariantUnder ρ := by
    rw [LinearMap.BilinForm.isInvariantUnder_iff]
    intro g x y
    have hBxy := (LinearMap.BilinForm.isInvariantUnder_iff B ρ).1 hB g x y
    have hflipxy := (LinearMap.BilinForm.isInvariantUnder_iff B.flip ρ).1 hflip g x y
    simp [Bminus, hBxy, hflipxy]
  have hdecomp : B = Bplus + Bminus := by
    -- This is the standard symmetric/alternating decomposition.
    ext x y
    simp [Bplus, Bminus, sub_eq_add_neg, LinearMap.BilinForm.flip_apply]
    ring
  have hplus_symm : Bplus.IsSymm := by
    refine ⟨?_⟩
    intro x y
    simp [Bplus, add_comm, LinearMap.BilinForm.flip_apply]
  have hminus_alt : Bminus.IsAlt := by
    intro x
    simp [Bminus, LinearMap.BilinForm.flip_apply]
  by_cases hplus0 : Bplus = 0
  · right
    have hB_eq : B = Bminus := by
      simpa [hplus0] using hdecomp
    rw [hB_eq]
    exact hminus_alt
  · left
    have hminus0 : Bminus = 0 := by
      by_contra hminus0
      obtain ⟨c, hc⟩ :=
        exists_units_smul_eq_of_isInvariantUnder ρ Bminus Bplus hBminus hminus0 hBplus hplus0
      have hplus_alt : Bplus.IsAlt := by
        rw [hc]
        exact hminus_alt.smul (c : ℂ)
      exact hplus0 (eq_zero_of_isSymm_and_isAlt Bplus hplus_symm hplus_alt)
    have hB_eq : B = Bplus := by
      simpa [hminus0] using hdecomp
    rw [hB_eq]
    exact hplus_symm

end

end LinearMap.BilinForm

namespace Representation

section

variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) [ρ.IsIrreducible]

-- Proof sketch: by the previous clause, a nonzero symmetric invariant bilinear form is
-- automatically nondegenerate, and then Theorem `13-13.2-1 (2)` identifies such a form with
-- realizability over `ℝ`, which is exactly LinearRepresentations_Serre_1977 type `2`. Finite-dimensionality is automatic
-- from `IsIrreducible.finiteDimensional_of_finite ρ`.
/-- Proposition 13-13.2-3 (5): source part (b). A nonzero symmetric `G`-invariant bilinear form
on an irreducible complex representation of a finite group forces the representation to be of
LinearRepresentations_Serre_1977 type `2`. Finite-dimensionality is automatic here. -/
theorem isTypeTwo_of_nonzero_invariant_symmetric_bilinForm
    (B : BilinForm ℂ V) (hB : B.IsInvariantUnder ρ)
    (hBsymm : B.IsSymm) (hB0 : B ≠ 0) :
    IsRealizableOver ℝ ρ := by
  letI := IsIrreducible.finiteDimensional_of_finite ρ
  refine (isRealizableOverReal_iff_exists_invariant_nondegenerate_symmetric_bilinForm ρ).2 ?_
  exact ⟨B, LinearMap.BilinForm.nondegenerate_of_nonzero_isInvariantUnder ρ B hB hB0, hBsymm, hB⟩

-- Proof sketch: Theorem `13-13.2-1 (1)` gives real-valued character from any nonzero invariant
-- bilinear form, while the preceding clause shows that a representation admitting a nonzero
-- symmetric invariant form would be of type `2`. Hence a nonzero alternating invariant form gives
-- real-valued character but prevents
-- realizability over `ℝ`, i.e. LinearRepresentations_Serre_1977 type `3`. Finite-dimensionality is automatic from
-- `IsIrreducible.finiteDimensional_of_finite ρ`.
/-- Proposition 13-13.2-3 (6): source part (b). A nonzero alternating `G`-invariant bilinear form
on an irreducible complex representation of a finite group forces the representation to be of
LinearRepresentations_Serre_1977 type `3`. Finite-dimensionality is automatic here. -/
theorem isTypeThree_of_nonzero_invariant_alternating_bilinForm
    (B : BilinForm ℂ V) (hB : B.IsInvariantUnder ρ)
    (hBalt : B.IsAlt) (hB0 : B ≠ 0) :
    IsValuedInBaseField ℝ ρ.character ∧ ¬ IsRealizableOver ℝ ρ := by
  letI := IsIrreducible.finiteDimensional_of_finite ρ
  letI : Nontrivial V := by
    by_contra hV
    letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    have hbot : (⊥ : Subrepresentation ρ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      ext y
      constructor
      · intro _
        trivial
      · intro _
        simpa using (Subsingleton.elim y 0)
    exact bot_ne_top hbot
  have hB_nondeg : B.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_of_nonzero_isInvariantUnder ρ B hB hB0
  constructor
  · -- The alternating form is nondegenerate, so Theorem `13-13.2-1 (1)` gives real-valued character.
    exact (hasRealValuedCharacter_iff_exists_invariant_nondegenerate_bilinForm ρ).2
      ⟨B, hB_nondeg, hB⟩
  · intro hreal
    rcases
        (isRealizableOverReal_iff_exists_invariant_nondegenerate_symmetric_bilinForm ρ).1 hreal with
      ⟨B', hB'_nondeg, hB'_symm, hB'_inv⟩
    have hB'0 : B' ≠ 0 := hB'_nondeg.ne_zero
    -- A real model would give a nonzero symmetric invariant form, contradicting uniqueness up to
    -- homothety with the given alternating one.
    obtain ⟨c, hc⟩ :=
      LinearMap.BilinForm.exists_units_smul_eq_of_isInvariantUnder ρ B B' hB hB0 hB'_inv hB'0
    have hB'_alt : B'.IsAlt := by
      rw [hc]
      exact hBalt.smul (c : ℂ)
    exact hB'0 (LinearMap.BilinForm.eq_zero_of_isSymm_and_isAlt B' hB'_symm hB'_alt)

end

end Representation
