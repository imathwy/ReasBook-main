import Mathlib
import Mathlib.RingTheory.Morita.Matrix
import Serre.Chap12.Proposition_12_12_1_3
import Serre.RepresentationTheory.RealizableOver

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped TensorProduct
open scoped ComplexStarModule
open scoped Matrix.Module
open scoped Polynomial

noncomputable section

universe u v

namespace LinearMap.BilinForm

section

variable {R : Type*} [CommSemiring R]
variable {G : Type u} [Monoid G]
variable {V : Type v} [AddCommMonoid V] [Module R V]

/-- Helper for Remark 13-13.2-2: a bilinear form on a representation is invariant when each group
element acts by an isometry for that form. -/
def IsInvariantUnder (B : BilinForm R V) (ρ : Representation R G V) : Prop :=
  ∀ g : G, B.comp (ρ g) (ρ g) = B

/-- Helper for Remark 13-13.2-2: invariance of a bilinear form is equivalent to the pointwise
identity obtained by applying the form after the group action. -/
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

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
variable [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [T2Space V]
variable [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
/-- Helper for Remark 13-13.2-2: invariance of a bilinear form is equivalent to saying that the
associated map to the dual representation intertwines the `G`-action. -/
theorem isInvariantUnder_iff_dual_intertwining
    (B : BilinForm ℂ V) (ρ : Representation ℂ G V) :
    B.IsInvariantUnder ρ ↔ ∀ g : G, B ∘ₗ ρ g = ρ.dual g ∘ₗ B := by
  constructor
  · intro h g
    ext x y
    -- Rewrite the second slot by `ρ g⁻¹` and use the pointwise invariance identity.
    have hxy := (LinearMap.BilinForm.isInvariantUnder_iff B ρ).1 h g x (ρ g⁻¹ y)
    simpa using hxy
  · intro h
    rw [LinearMap.BilinForm.isInvariantUnder_iff]
    intro g x y
    -- Evaluate the intertwining identity at `x` and then at `ρ g y`.
    have hxy := LinearMap.congr_fun (h g) x
    have hxy' := LinearMap.congr_fun hxy (ρ g y)
    simpa [Representation.dual_apply, Module.Dual.transpose_apply] using hxy'

/-- Helper for Remark 13-13.2-2: a finite-dimensional representation is equivariantly self-dual
exactly when it admits a nondegenerate invariant bilinear form. -/
theorem nonempty_equiv_dual_iff_exists_invariant_nondegenerate_bilinForm
    (ρ : Representation ℂ G V) :
    Nonempty (ρ.Equiv ρ.dual) ↔
      ∃ B : BilinForm ℂ V, B.Nondegenerate ∧ B.IsInvariantUnder ρ := by
  constructor
  · rintro ⟨e⟩
    -- Transport the dual evaluation pairing across the chosen equivariant self-duality.
    refine ⟨e.toLinearMap, ?_, ?_⟩
    refine ⟨?_, ?_⟩
    · rw [LinearMap.separatingLeft_iff_ker_eq_bot]
      exact LinearMap.ker_eq_bot.mpr e.toLinearEquiv.injective
    · intro y hy
      refine (Module.forall_dual_apply_eq_zero_iff ℂ y).mp ?_
      intro f
      rcases e.toLinearEquiv.surjective f with ⟨x, rfl⟩
      exact hy x
    -- The intertwining relation for `e` is exactly invariance of the resulting form.
    rw [isInvariantUnder_iff_dual_intertwining]
    intro g
    exact e.isIntertwining' g
  · rintro ⟨B, hB, hBinv⟩
    -- A nondegenerate invariant bilinear form identifies `V` with the dual representation.
    refine ⟨Representation.Equiv.mk (B.toDual hB) ?_⟩
    rw [isInvariantUnder_iff_dual_intertwining] at hBinv
    intro g
    ext x y
    have hxy := LinearMap.congr_fun (hBinv g) x
    have hxy' := LinearMap.congr_fun hxy y
    simpa [B.toDual_def] using hxy'

-- Source/core/bridge triage: these are `source-facing` compact-group analogues of
-- `Theorem_13_13_2_1`. The owner predicates remain the Chapter `12` and representation-theoretic
-- owners `IsValuedInBaseField`, `IsRealizableOver`, and `BilinForm.IsInvariantUnder`.

-- Primitive data versus derived API: the compact-group-specific content is the bridge from
-- real-valued character to equivariant self-duality. The invariant-bilinear-form criterion is
-- already owned upstream by `nonempty_equiv_dual_iff_exists_invariant_nondegenerate_bilinForm`,
-- so the source-facing bilinear-form statement below should derive from that owner theorem rather
-- than restating its full content as new primitive API.
-- Proof sketch: use compact-group harmonic analysis to identify real-valued character with
-- equivariant self-duality for continuous finite-dimensional representations.
/-- Helper for Remark 13-13.2-2: a complex character is `ℝ`-valued exactly when it is fixed
pointwise by complex conjugation. -/
private theorem character_isValuedInBaseField_iff_forall_star_eq
    (ρ : Representation ℂ G V) :
    IsValuedInBaseField ℝ ρ.character ↔
      ∀ g : G, star (ρ.character g) = ρ.character g := by
  rw [Representation.isValuedInBaseField_iff_mem_pointwiseAlgebraMap_range]
  constructor
  · intro hval g
    rcases hval with ⟨χR, hχR⟩
    -- Evaluate the range witness at `g` and use that real scalars are fixed by conjugation.
    rw [← congrFun hχR g]
    simp
  · intro hstar
    -- Recover the real-valued lift by taking the real part pointwise.
    refine ⟨fun g ↦ (ρ.character g).re, ?_⟩
    ext g
    exact (Complex.conj_eq_iff_re).mp (hstar g)

/-- Helper for Remark 13-13.2-2: averaging a positive Hermitian form over Haar measure should
produce the invariant conjugate-dual equivalence used by the compact Frobenius-Schur argument. -/
private theorem exists_invariant_positive_conjugate_dual_equiv_of_compactGroup
    (ρ : Representation ℂ G V) (hρ : Continuous fun p : G × V ↦ ρ p.1 p.2) :
    ∃ J : V ≃ₗ⋆[ℂ] Module.Dual ℂ V,
      (∀ g : G, ∀ x y : V, J (ρ g x) (ρ g y) = J x y) ∧
      (∀ x y : V, star (J x y) = J y x) ∧
      (∀ x : V, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ)) := by
  let _ : MeasurableSpace G := borel G
  let _ : BorelSpace G := ⟨rfl⟩
  let b := Module.Free.chooseBasis ℂ V
  let ι := Module.Free.ChooseBasisIndex ℂ V
  letI : Finite ι := Module.Finite.finite_basis b
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  let Jstd : V →ₗ⋆[ℂ] Module.Dual ℂ V :=
    Matrix.toLinearMapₛₗ₂ (R := ℂ) (σ₁ := (↑Complex.conjAe : ℂ →+* ℂ)) b b
      (1 : Matrix ι ι ℂ)
  -- Start from the standard positive Hermitian pairing attached to a basis.
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
    simp [hJstd_apply, mul_comm]
  have hJstd_diag : ∀ x : V, Jstd x x = ∑ i : ι, (Complex.normSq (b.repr x i) : ℂ) := by
    intro x
    simpa [Complex.normSq_eq_conj_mul_self] using hJstd_apply x x
  have hρ_apply (x : V) : Continuous fun g : G ↦ ρ g x := by
    -- Fix the vector and read continuity from the joint action.
    simpa using hρ.comp (continuous_id.prodMk continuous_const)
  have hcoord_cont (x : V) (i : ι) : Continuous fun g : G ↦ b.coord i (ρ g⁻¹ x) := by
    exact
      (b.coord i).continuous_of_finiteDimensional.comp ((hρ_apply x).comp continuous_inv)
  have hpair_cont (x y : V) :
      Continuous fun g : G ↦ Jstd (ρ g⁻¹ x) (ρ g⁻¹ y) := by
    -- Each coordinate term is continuous, so the finite Hermitian sum is continuous.
    have hsum_cont :
        Continuous fun g : G ↦ ∑ i : ι, star (b.coord i (ρ g⁻¹ x)) * b.coord i (ρ g⁻¹ y) := by
      refine continuous_finset_sum _ ?_
      intro i hi
      exact (Complex.continuous_conj.comp (hcoord_cont x i)).mul (hcoord_cont y i)
    simpa [hJstd_apply] using hsum_cont
  have hpair_integrable (x y : V) :
      Integrable
        (fun g : G ↦ Jstd (ρ g⁻¹ x) (ρ g⁻¹ y))
        (Measure.haar : Measure G) := by
    exact
      (hpair_cont x y).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  let Jmap : V →ₗ⋆[ℂ] Module.Dual ℂ V :=
    LinearMap.mk₂'ₛₗ (ρ₁₂ := (↑Complex.conjAe : ℂ →+* ℂ)) (σ₁₂ := RingHom.id ℂ)
      (fun x y ↦ ∫ g : G, Jstd (ρ g⁻¹ x) (ρ g⁻¹ y) ∂(Measure.haar : Measure G))
      (by
        intro x y z
        -- Additivity in the first slot is preserved by the Haar integral.
        have hyz := hpair_integrable y z
        have hxz := hpair_integrable x z
        change
          (∫ g : G, Jstd (ρ g⁻¹ (x + y)) (ρ g⁻¹ z) ∂(Measure.haar : Measure G)) =
            (∫ g : G, Jstd (ρ g⁻¹ x) (ρ g⁻¹ z) ∂(Measure.haar : Measure G)) +
              ∫ g : G, Jstd (ρ g⁻¹ y) (ρ g⁻¹ z) ∂(Measure.haar : Measure G)
        rw [show
            (fun g : G ↦ Jstd (ρ g⁻¹ (x + y)) (ρ g⁻¹ z)) =
              fun g : G ↦ Jstd (ρ g⁻¹ x) (ρ g⁻¹ z) + Jstd (ρ g⁻¹ y) (ρ g⁻¹ z) by
            ext g
            simp
          , integral_add hxz hyz])
      (by
        intro c x y
        -- The conjugate scalar in the first slot also passes through the integral.
        change
          (∫ g : G, Jstd (ρ g⁻¹ (c • x)) (ρ g⁻¹ y) ∂(Measure.haar : Measure G)) =
            star c • ∫ g : G, Jstd (ρ g⁻¹ x) (ρ g⁻¹ y) ∂(Measure.haar : Measure G)
        rw [show
            (fun g : G ↦ Jstd (ρ g⁻¹ (c • x)) (ρ g⁻¹ y)) =
              fun g : G ↦ star c • Jstd (ρ g⁻¹ x) (ρ g⁻¹ y) by
            ext g
            simp
          , integral_smul (star c)])
      (by
        intro x y z
        -- Additivity in the second slot is handled the same way.
        have hxy := hpair_integrable x y
        have hxz := hpair_integrable x z
        change
          (∫ g : G, Jstd (ρ g⁻¹ x) (ρ g⁻¹ (y + z)) ∂(Measure.haar : Measure G)) =
            (∫ g : G, Jstd (ρ g⁻¹ x) (ρ g⁻¹ y) ∂(Measure.haar : Measure G)) +
              ∫ g : G, Jstd (ρ g⁻¹ x) (ρ g⁻¹ z) ∂(Measure.haar : Measure G)
        rw [show
            (fun g : G ↦ Jstd (ρ g⁻¹ x) (ρ g⁻¹ (y + z))) =
              fun g : G ↦ Jstd (ρ g⁻¹ x) (ρ g⁻¹ y) + Jstd (ρ g⁻¹ x) (ρ g⁻¹ z) by
            ext g
            simp
          , integral_add hxy hxz])
      (by
        intro c x y
        -- Linearity in the second slot also commutes with Haar integration.
        change
          (∫ g : G, Jstd (ρ g⁻¹ x) (ρ g⁻¹ (c • y)) ∂(Measure.haar : Measure G)) =
            c • ∫ g : G, Jstd (ρ g⁻¹ x) (ρ g⁻¹ y) ∂(Measure.haar : Measure G)
        rw [show
            (fun g : G ↦ Jstd (ρ g⁻¹ x) (ρ g⁻¹ (c • y))) =
              fun g : G ↦ c • Jstd (ρ g⁻¹ x) (ρ g⁻¹ y) by
            ext g
            simp
          , integral_smul c])
  have hJ_invariant : ∀ g : G, ∀ x y : V, Jmap (ρ g x) (ρ g y) = Jmap x y := by
    intro g x y
    let f : G → ℂ := fun h ↦ Jstd (ρ h⁻¹ x) (ρ h⁻¹ y)
    -- Haar left-invariance removes the extra translate.
    change
      (∫ h : G, Jstd (ρ h⁻¹ (ρ g x)) (ρ h⁻¹ (ρ g y)) ∂(Measure.haar : Measure G)) =
        ∫ h : G, f h ∂(Measure.haar : Measure G)
    rw [show
        (fun h : G ↦ Jstd (ρ h⁻¹ (ρ g x)) (ρ h⁻¹ (ρ g y))) =
          fun h : G ↦ f (g⁻¹ * h) by
        ext h
        simp [f, map_mul]]
    simpa using
      (MeasureTheory.integral_mul_left_eq_self
        (μ := (Measure.haar : Measure G)) f g⁻¹)
  have hJ_herm : ∀ x y : V, star (Jmap x y) = Jmap y x := by
    intro x y
    -- Hermitian symmetry passes pointwise under the integral.
    calc
      star (Jmap x y)
          = ∫ g : G, star (Jstd (ρ g⁻¹ x) (ρ g⁻¹ y)) ∂(Measure.haar : Measure G) := by
              symm
              simpa [Jmap] using
                (integral_conj
                  (μ := (Measure.haar : Measure G))
                  (f := fun g : G ↦ Jstd (ρ g⁻¹ x) (ρ g⁻¹ y)))
      _ = ∫ g : G, Jstd (ρ g⁻¹ y) (ρ g⁻¹ x) ∂(Measure.haar : Measure G) := by
            congr 1
            ext g
            exact hJstd_herm (ρ g⁻¹ x) (ρ g⁻¹ y)
      _ = Jmap y x := by
            rfl
  have hJ_pos : ∀ x : V, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ Jmap x x = (r : ℂ) := by
    intro x hx
    let f : G → ℝ := fun g ↦ ∑ j : ι, Complex.normSq (b.repr (ρ g⁻¹ x) j)
    have hf_cont : Continuous f := by
      have hsum_cont :
          Continuous fun g : G ↦ ∑ j : ι, Complex.normSq (b.repr (ρ g⁻¹ x) j) := by
        refine continuous_finset_sum _ ?_
        intro j hj
        exact Complex.continuous_normSq.comp (hcoord_cont x j)
      simpa [f] using hsum_cont
    have hf_nonneg : ∀ g : G, 0 ≤ f g := by
      intro g
      refine Finset.sum_nonneg ?_
      intro j hj
      exact Complex.normSq_nonneg _
    have hf_one : f 1 ≠ 0 := by
      have hxrepr : b.repr x ≠ 0 := by
        intro hrepr
        exact hx (b.repr.injective (by simpa using hrepr))
      obtain ⟨i, hi⟩ : ∃ i : ι, b.repr x i ≠ 0 := by
        by_contra h
        apply hxrepr
        ext j
        by_contra hj
        exact h ⟨j, hj⟩
      have hsum_pos : 0 < ∑ j : ι, Complex.normSq (b.repr x j) := by
        refine Finset.sum_pos' ?_ ?_
        · intro j hj
          exact Complex.normSq_nonneg _
        · exact ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩
      simpa [f] using hsum_pos.ne'
    let r : ℝ := ∫ g : G, f g ∂(Measure.haar : Measure G)
    refine ⟨r, ?_, ?_⟩
    · -- Positivity follows because the diagonal norm-square function is continuous, nonnegative,
      -- and nonzero at the identity.
      simpa [r, f] using
        (hf_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero
          (μ := (Measure.haar : Measure G))
          (x := (1 : G))
          (HasCompactSupport.of_compactSpace f) hf_nonneg hf_one)
    · -- Identify the diagonal integral with the integral of the real-valued norm-square function.
      calc
        Jmap x x
            = ∫ g : G, Jstd (ρ g⁻¹ x) (ρ g⁻¹ x) ∂(Measure.haar : Measure G) := by
                rfl
        _ = ∫ g : G, (f g : ℂ) ∂(Measure.haar : Measure G) := by
              congr 1
              ext g
              simpa [f] using hJstd_diag (ρ g⁻¹ x)
        _ = (r : ℂ) := by
              simpa [r] using
                (integral_ofReal
                  (μ := (Measure.haar : Measure G))
                  (f := f))
  have hJ_zero : ∀ {x : V}, Jmap x = 0 → x = 0 := by
    intro x hxJ
    by_contra hx0
    rcases hJ_pos x hx0 with ⟨r, hr, hr_eq⟩
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

/-- Helper for Remark 13-13.2-2: in the compact-group setting, the dual character is the
pointwise complex conjugate of the original character. -/
private theorem char_dual_eq_star_of_compactGroup
    (ρ : Representation ℂ G V) (hρ : Continuous fun p : G × V ↦ ρ p.1 p.2) (g : G) :
    ρ.dual.character g = star (ρ.character g) := by
  rcases exists_invariant_positive_conjugate_dual_equiv_of_compactGroup ρ hρ with
    ⟨J, hJ_invariant, hJ_star, hJ_pos⟩
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
  have hadj' : ρ g⁻¹ = LinearMap.adjoint (ρ g) := by
    exact (LinearMap.eq_adjoint_iff (A := ρ g⁻¹) (B := ρ g)).2 fun x y ↦ by
      simpa [map_mul] using hJ_invariant g⁻¹ x (ρ g y)
  have hadj : LinearMap.adjoint (ρ g) = ρ g⁻¹ := hadj'.symm
  have htrace_adjoint :
      ∀ T : V →ₗ[ℂ] V, LinearMap.trace ℂ V (LinearMap.adjoint T) = star (LinearMap.trace ℂ V T) := by
    intro T
    let b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V := stdOrthonormalBasis ℂ V
    calc
      LinearMap.trace ℂ V (LinearMap.adjoint T) =
          ∑ i, inner ℂ (b i) (LinearMap.adjoint T (b i)) := by
            simpa using (LinearMap.trace_eq_sum_inner (T := LinearMap.adjoint T) b)
      _ = ∑ i, inner ℂ (T (b i)) (b i) := by
            simp [LinearMap.adjoint_inner_right]
      _ = ∑ i, star (inner ℂ (b i) (T (b i))) := by
            apply Finset.sum_congr rfl
            intro i hi
            simpa using (inner_conj_symm (T (b i)) (b i))
      _ = star (∑ i, inner ℂ (b i) (T (b i))) := by
            simp
      _ = star (LinearMap.trace ℂ V T) := by
            rw [LinearMap.trace_eq_sum_inner (T := T) b]
  rw [Representation.char_dual]
  change LinearMap.trace ℂ V (ρ g⁻¹) = star (LinearMap.trace ℂ V (ρ g))
  rw [← hadj]
  exact htrace_adjoint (ρ g)

/-- Helper for Remark 13-13.2-2: a continuous finite-dimensional compact-group representation is
semisimple because the averaged invariant Hermitian form makes orthogonal complements stable. -/
private theorem isSemisimpleRepresentation_of_compactGroup
    (ρ : Representation ℂ G V) (hρ : Continuous fun p : G × V ↦ ρ p.1 p.2) :
    ρ.IsSemisimpleRepresentation := by
  rcases exists_invariant_positive_conjugate_dual_equiv_of_compactGroup ρ hρ with
    ⟨J, hJ_invariant, hJ_star, hJ_pos⟩
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
  have hadj : ∀ g : G, LinearMap.adjoint (ρ g) = ρ g⁻¹ := by
    intro g
    exact
      ((LinearMap.eq_adjoint_iff (A := ρ g⁻¹) (B := ρ g)).2 fun x y ↦ by
        simpa [map_mul] using hJ_invariant g⁻¹ x (ρ g y)).symm
  classical
  refine ⟨?_⟩
  intro U
  let Uorth : Subrepresentation ρ :=
    { toSubmodule := U.toSubmodule.orthogonal
      apply_mem_toSubmodule := by
        intro g x hx
        rw [Submodule.mem_orthogonal]
        intro y hy
        have hy' : ρ g⁻¹ y ∈ U.toSubmodule := U.apply_mem_toSubmodule g⁻¹ hy
        calc
          inner ℂ y (ρ g x) = inner ℂ ((LinearMap.adjoint (ρ g)) y) x := by
            simpa using (LinearMap.adjoint_inner_left (A := ρ g) x y).symm
          _ = inner ℂ (ρ g⁻¹ y) x := by
            rw [hadj g]
          _ = 0 := hx _ hy' }
  refine ⟨Uorth, ?_⟩
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    simpa [Uorth] using (U.toSubmodule.inf_orthogonal_eq_bot)
  · rw [codisjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    simpa [Uorth] using
      (Submodule.sup_orthogonal_of_hasOrthogonalProjection (K := U.toSubmodule))

/-- Helper for Remark 13-13.2-2: the dual of a continuous finite-dimensional compact-group
representation is semisimple, by transporting complements through the averaged conjugate-dual
equivalence. -/
private theorem dual_isSemisimpleRepresentation_of_compactGroup
    (ρ : Representation ℂ G V) (hρ : Continuous fun p : G × V ↦ ρ p.1 p.2) :
    ρ.dual.IsSemisimpleRepresentation := by
  rcases exists_invariant_positive_conjugate_dual_equiv_of_compactGroup ρ hρ with
    ⟨J, hJ_invariant, _hJ_star, _hJ_pos⟩
  have hJ_lin : ∀ g : G, ∀ x : V, J (ρ g x) = ρ.dual g (J x) := by
    intro g x
    ext y
    calc
      J (ρ g x) y = J (ρ g x) (ρ g (ρ g⁻¹ y)) := by
        simp
      _ = J x (ρ g⁻¹ y) := by
        simpa using hJ_invariant g x (ρ g⁻¹ y)
      _ = ρ.dual g (J x) y := by
        rfl
  letI : ρ.IsSemisimpleRepresentation := isSemisimpleRepresentation_of_compactGroup ρ hρ
  classical
  refine ⟨?_⟩
  intro U
  let preU : Subrepresentation ρ :=
    { toSubmodule :=
        { carrier := {x : V | J x ∈ U.toSubmodule}
          zero_mem' := by
            simp
          add_mem' := by
            intro x y hx hy
            simpa using U.toSubmodule.add_mem hx hy
          smul_mem' := by
            intro c x hx
            change J (c • x) ∈ U.toSubmodule
            rw [J.map_smulₛₗ]
            exact U.toSubmodule.smul_mem (star c) hx }
      apply_mem_toSubmodule := by
        intro g x hx
        simpa [hJ_lin g x] using U.apply_mem_toSubmodule g hx }
  obtain ⟨Q, hQcompl⟩ := exists_isCompl preU
  let imgQ : Subrepresentation ρ.dual :=
    { toSubmodule :=
        { carrier := {f : Module.Dual ℂ V | ∃ x ∈ Q.toSubmodule, J x = f}
          zero_mem' := by
            refine ⟨0, Q.toSubmodule.zero_mem, ?_⟩
            simp
          add_mem' := by
            intro f g hf hg
            rcases hf with ⟨x, hx, rfl⟩
            rcases hg with ⟨y, hy, rfl⟩
            refine ⟨x + y, Q.toSubmodule.add_mem hx hy, ?_⟩
            simp
          smul_mem' := by
            intro c f hf
            rcases hf with ⟨x, hx, rfl⟩
            refine ⟨star c • x, Q.toSubmodule.smul_mem (star c) hx, ?_⟩
            simpa using (J.map_smulₛₗ (star c) x) }
      apply_mem_toSubmodule := by
        intro g f hf
        rcases hf with ⟨x, hx, rfl⟩
        refine ⟨ρ g x, Q.apply_mem_toSubmodule g hx, ?_⟩
        simp [hJ_lin g x] }
  refine ⟨imgQ, ?_⟩
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    ext f
    constructor
    · intro hf
      rcases hf with ⟨hfU, hfQ⟩
      rcases hfQ with ⟨x, hxQ, rfl⟩
      have hxU : x ∈ preU.toSubmodule := by
        exact (show J x ∈ U.toSubmodule from hfU)
      have hx0 : x = 0 := by
        have hxbot : x ∈ (preU ⊓ Q).toSubmodule := ⟨hxU, hxQ⟩
        simpa [hQcompl.inf_eq_bot] using hxbot
      simp [hx0]
    · intro hf
      have hf0 : f = 0 := by
        simpa using hf
      simp [hf0]
  · rw [codisjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    ext f
    constructor
    · intro _hf
      exact Submodule.mem_top
    · intro _hf
      let x := J.symm f
      have hx : x ∈ (preU ⊔ Q).toSubmodule := by
        simpa [hQcompl.sup_eq_top] using
          (show x ∈ (⊤ : Subrepresentation ρ).toSubmodule from Submodule.mem_top)
      rcases Submodule.mem_sup.1 hx with ⟨xU, hxU, xQ, hxQ, hsumx⟩
      refine Submodule.mem_sup.2 ?_
      refine ⟨J xU, ?_, J xQ, ?_, ?_⟩
      · exact (show J xU ∈ U.toSubmodule from hxU)
      · exact ⟨xQ, hxQ, rfl⟩
      · calc
          J xU + J xQ = J (xU + xQ) := by
            simp
          _ = J x := by
            rw [hsumx]
          _ = f := by
            simp [x]

/-- Helper for Remark 13-13.2-2: equality of characters gives equality of traces on every element
of the monoid algebra. -/
private theorem trace_eq_asAlgebraHom_of_character_eq
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W}
    (hchar : ρ.character = ρ'.character) (a : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ V (ρ.asAlgebraHom a) = LinearMap.trace ℂ W (ρ'.asAlgebraHom a) := by
  -- Compare traces on monoid generators first, then extend linearly across the monoid algebra.
  refine
    MonoidAlgebra.induction_on
      (p := fun a : MonoidAlgebra ℂ G ↦
        LinearMap.trace ℂ V (ρ.asAlgebraHom a) = LinearMap.trace ℂ W (ρ'.asAlgebraHom a))
      a ?_ ?_ ?_
  · intro g
    simpa [Representation.character, Representation.asAlgebraHom_of] using congrFun hchar g
  · intro a b ha hb
    simp [ha, hb]
  · intro r a ha
    simp [ha]

/-- Helper for Remark 13-13.2-2: the kernel of the product algebra action is contained in the
kernel of the left factor. -/
private theorem prod_asAlgebraHom_ker_le_left
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} :
    RingHom.ker (ρ.asAlgebraHom.prod ρ'.asAlgebraHom) ≤ RingHom.ker ρ.asAlgebraHom := by
  -- Project the vanishing product action to its left coordinate.
  intro a ha
  exact congrArg Prod.fst ha

/-- Helper for Remark 13-13.2-2: the kernel of the product algebra action is contained in the
kernel of the right factor. -/
private theorem prod_asAlgebraHom_ker_le_right
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} :
    RingHom.ker (ρ.asAlgebraHom.prod ρ'.asAlgebraHom) ≤ RingHom.ker ρ'.asAlgebraHom := by
  -- Project the vanishing product action to its right coordinate.
  intro a ha
  exact congrArg Prod.snd ha

/-- Helper for Remark 13-13.2-2: character equality descends to trace equality on the common
kernel quotient algebra. -/
private theorem trace_eq_on_common_kernel_quotient_of_character_eq
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W}
    (hchar : ρ.character = ρ'.character) :
    let ψ : MonoidAlgebra ℂ G →ₐ[ℂ] Module.End ℂ V × Module.End ℂ W :=
      ρ.asAlgebraHom.prod ρ'.asAlgebraHom
    let I : Ideal (MonoidAlgebra ℂ G) := RingHom.ker ψ
    let A := MonoidAlgebra ℂ G ⧸ I
    let φV : A →ₐ[ℂ] Module.End ℂ V :=
      Ideal.Quotient.liftₐ I ρ.asAlgebraHom
        (prod_asAlgebraHom_ker_le_left (ρ := ρ) (ρ' := ρ'))
    let φW : A →ₐ[ℂ] Module.End ℂ W :=
      Ideal.Quotient.liftₐ I ρ'.asAlgebraHom
        (prod_asAlgebraHom_ker_le_right (ρ := ρ) (ρ' := ρ'))
    ∀ a : A, LinearMap.trace ℂ V (φV a) = LinearMap.trace ℂ W (φW a) := by
  let ψ : MonoidAlgebra ℂ G →ₐ[ℂ] Module.End ℂ V × Module.End ℂ W :=
    ρ.asAlgebraHom.prod ρ'.asAlgebraHom
  let I : Ideal (MonoidAlgebra ℂ G) := RingHom.ker ψ
  letI : I.IsTwoSided := by
    change (RingHom.ker ψ).IsTwoSided
    infer_instance
  let A := MonoidAlgebra ℂ G ⧸ I
  let φV : A →ₐ[ℂ] Module.End ℂ V :=
    Ideal.Quotient.liftₐ I ρ.asAlgebraHom
      (prod_asAlgebraHom_ker_le_left (ρ := ρ) (ρ' := ρ'))
  let φW : A →ₐ[ℂ] Module.End ℂ W :=
    Ideal.Quotient.liftₐ I ρ'.asAlgebraHom
      (prod_asAlgebraHom_ker_le_right (ρ := ρ) (ρ' := ρ'))
  have htrace : ∀ a : A, LinearMap.trace ℂ V (φV a) = LinearMap.trace ℂ W (φW a) := by
    intro a
    -- Lift each quotient element back to the monoid algebra and apply the original trace identity.
    rcases Ideal.Quotient.mkₐ_surjective ℂ I a with ⟨b, hb⟩
    rw [← hb]
    simpa [φV, φW] using trace_eq_asAlgebraHom_of_character_eq (ρ := ρ) (ρ' := ρ') hchar b
  simpa [ψ, I, A, φV, φW] using htrace

/-- Helper for Remark 13-13.2-2: the common-kernel quotient algebra is finite-dimensional over
`ℂ`. -/
private theorem common_kernel_quotient_finite
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} :
    let ψ : MonoidAlgebra ℂ G →ₐ[ℂ] Module.End ℂ V × Module.End ℂ W :=
      ρ.asAlgebraHom.prod ρ'.asAlgebraHom
    let I : Ideal (MonoidAlgebra ℂ G) := RingHom.ker ψ
    let A := MonoidAlgebra ℂ G ⧸ I
    Module.Finite ℂ A := by
  let ψ : MonoidAlgebra ℂ G →ₐ[ℂ] Module.End ℂ V × Module.End ℂ W :=
    ρ.asAlgebraHom.prod ρ'.asAlgebraHom
  let I : Ideal (MonoidAlgebra ℂ G) := RingHom.ker ψ
  let A := MonoidAlgebra ℂ G ⧸ I
  have hfiniteRange : Module.Finite ℂ ψ.range := by
    infer_instance
  let e : A ≃ₐ[ℂ] ψ.range := by
    simpa [A, I] using Ideal.quotientKerEquivRange (R := ℂ) ψ
  -- Transport finite dimensionality across the canonical quotient-range algebra equivalence.
  have hfinite : Module.Finite ℂ A := Module.Finite.equiv e.toLinearEquiv.symm
  simpa [ψ, I, A] using hfinite

/-- Helper for Remark 13-13.2-2: semisimplicity descends along a surjective ring homomorphism. -/
private theorem isSemisimpleModule_of_ringHom_surjective
    {R A M : Type*} [Ring R] [Ring A] [AddCommGroup M] [Module A M]
    (q : R →+* A) (hq : Function.Surjective q)
    (hM : let _ : Module R M := Module.compHom M q
      IsSemisimpleModule R M) :
    IsSemisimpleModule A M := by
  let _ : Module R M := Module.compHom M q
  letI : RingHomSurjective q := ⟨hq⟩
  let l : M →ₛₗ[q] M :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hbij : Function.Bijective l := by
    constructor
    · intro x y hxy
      exact hxy
    · intro x
      exact ⟨x, rfl⟩
  -- The identity semilinear map compares the restricted and descended scalar actions directly.
  exact (l.isSemisimpleModule_iff_of_bijective hbij).mp hM

/-- Helper for Remark 13-13.2-2: the common-kernel quotient algebra is semisimple once both
representations are semisimple. -/
private theorem common_kernel_quotient_isSemisimpleRing
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W}
    (hρ : ρ.IsSemisimpleRepresentation) (hρ' : ρ'.IsSemisimpleRepresentation) :
    let ψ : MonoidAlgebra ℂ G →ₐ[ℂ] Module.End ℂ V × Module.End ℂ W :=
      ρ.asAlgebraHom.prod ρ'.asAlgebraHom
    let I : Ideal (MonoidAlgebra ℂ G) := RingHom.ker ψ
    let A := MonoidAlgebra ℂ G ⧸ I
    IsSemisimpleRing A := by
  let ψ : MonoidAlgebra ℂ G →ₐ[ℂ] Module.End ℂ V × Module.End ℂ W :=
    ρ.asAlgebraHom.prod ρ'.asAlgebraHom
  let I : Ideal (MonoidAlgebra ℂ G) := RingHom.ker ψ
  letI : I.IsTwoSided := by
    change (RingHom.ker ψ).IsTwoSided
    infer_instance
  let A := MonoidAlgebra ℂ G ⧸ I
  let B := ψ.range
  let φV : B →ₐ[ℂ] Module.End ℂ V :=
    (AlgHom.fst ℂ (Module.End ℂ V) (Module.End ℂ W)).comp (Subalgebra.val B)
  let φW : B →ₐ[ℂ] Module.End ℂ W :=
    (AlgHom.snd ℂ (Module.End ℂ V) (Module.End ℂ W)).comp (Subalgebra.val B)
  letI : Module B V := Module.compHom V φV.toRingHom
  letI : Module B W := Module.compHom W φW.toRingHom
  have hsemV_fromR :
      let _ : Module (MonoidAlgebra ℂ G) V :=
        Module.compHom V (φV.toRingHom.comp ψ.rangeRestrict.toRingHom)
      IsSemisimpleModule (MonoidAlgebra ℂ G) V := by
    -- Restrict the descended `B`-action back to the original `ℂ[G]`-action on `V`.
    simpa [B, φV, ψ] using
      (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp hρ
  have hsemW_fromR :
      let _ : Module (MonoidAlgebra ℂ G) W :=
        Module.compHom W (φW.toRingHom.comp ψ.rangeRestrict.toRingHom)
      IsSemisimpleModule (MonoidAlgebra ℂ G) W := by
    -- The same restriction-of-scalars comparison holds for `W`.
    simpa [B, φW, ψ] using
      (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ').mp hρ'
  have hsemV : IsSemisimpleModule B V :=
    isSemisimpleModule_of_ringHom_surjective
      (q := ψ.rangeRestrict.toRingHom) ψ.rangeRestrict_surjective hsemV_fromR
  have hsemW : IsSemisimpleModule B W :=
    isSemisimpleModule_of_ringHom_surjective
      (q := ψ.rangeRestrict.toRingHom) ψ.rangeRestrict_surjective hsemW_fromR
  have hjacV : Ring.jacobson B ≤ Module.annihilator B V := by
    simpa using (IsSemisimpleModule.jacobson_le_annihilator (R := B) (M := V))
  have hjacW : Ring.jacobson B ≤ Module.annihilator B W := by
    simpa using (IsSemisimpleModule.jacobson_le_annihilator (R := B) (M := W))
  have hann :
      Module.annihilator B V ⊓ Module.annihilator B W = ⊥ := by
    apply le_antisymm
    · intro a ha
      -- If an image-algebra element annihilates both coordinate modules, both coordinates vanish.
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · ext x
        exact Module.mem_annihilator.mp ha.1 x
      · ext x
        exact Module.mem_annihilator.mp ha.2 x
    · exact bot_le
  have hjac :
      Ring.jacobson B ≤ Module.annihilator B V ⊓ Module.annihilator B W := by
    intro a ha
    exact ⟨hjacV ha, hjacW ha⟩
  have hjac_eq_bot : Ring.jacobson B = ⊥ := by
    exact le_antisymm (hjac.trans <| by simpa [hann]) bot_le
  let _ : Module.Finite ℂ B := by
    infer_instance
  let _ : IsArtinianRing ℂ := inferInstance
  let _ : IsArtinianRing B := IsArtinianRing.of_finite ℂ B
  have hsemB : IsSemisimpleRing B := by
    -- Finite-dimensionality makes the image algebra Artinian, so Jacobson-zero implies semisimple.
    exact (IsArtinianRing.isSemisimpleRing_iff_jacobson (R := B)).2 hjac_eq_bot
  let e : A ≃ₐ[ℂ] B := by
    simpa [A, I] using Ideal.quotientKerEquivRange (R := ℂ) ψ
  -- Transport semisimplicity back across the canonical quotient-to-range equivalence.
  exact e.symm.isSemisimpleRing

/-- Helper for Remark 13-13.2-2: a coefficientwise complex linear equivalence induces the
corresponding matrix-linear equivalence on the standard matrix modules. -/
private noncomputable def matrix_module_linearEquiv_of_linearEquiv
    {n : Type*} [Fintype n] [DecidableEq n]
    {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (e : X ≃ₗ[ℂ] Y) :
    (n → X) ≃ₗ[Matrix n n ℂ] n → Y := by
  -- Apply the coefficientwise map and use the inverse coefficientwise map for bijectivity.
  refine LinearEquiv.ofBijective (LinearMap.mapMatrixModule n e.toLinearMap) ?_
  constructor
  · intro f g hfg
    ext i
    exact e.injective (congrFun hfg i)
  · intro y
    refine ⟨LinearMap.mapMatrixModule n e.symm.toLinearMap y, ?_⟩
    ext i
    simp

/-- Helper for Remark 13-13.2-2: on a finite product, the trace of a block-diagonal endomorphism
with a single nonzero block is the trace of that block. -/
private theorem trace_pi_single_eq_trace_coordinate_factor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    [∀ i, Module.Free ℂ (M i)] [∀ i, Module.Finite ℂ (M i)]
    (i : ι) (f : M i →ₗ[ℂ] M i) :
    LinearMap.trace ℂ (∀ j, M j) (LinearMap.piMap (Pi.single i f)) =
      LinearMap.trace ℂ (M i) f := by
  let b : ∀ a, Module.Basis _ ℂ (M a) := fun a ↦ Module.Free.chooseBasis ℂ (M a)
  have hsum :
      LinearMap.trace ℂ (∀ j, M j) (LinearMap.piMap (Pi.single i f)) =
        ∑ a, LinearMap.trace ℂ (M a) ((Pi.single i f : ∀ a, M a →ₗ[ℂ] M a) a) := by
    -- Compute the product trace in the sigma-indexed basis induced from the factor bases.
    rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basis b)]
    simp [Matrix.trace, Matrix.diag_apply, Fintype.sum_sigma, LinearMap.piMap,
      LinearMap.toMatrix_apply]
    congr with a
    simpa [Matrix.trace, LinearMap.toMatrix_apply] using
      (LinearMap.trace_eq_matrix_trace ℂ (b a)
        ((Pi.single i f : ∀ a, M a →ₗ[ℂ] M a) a)).symm
  rw [hsum, Finset.sum_eq_single i]
  · simp
  · intro j _ hij
    simp [Pi.single_eq_of_ne hij]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Helper for Remark 13-13.2-2: multiplication by the `i`-th product idempotent is linear over
the whole product algebra because that idempotent is central. -/
private def pi_coordinate_projection
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra ℂ (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module ℂ M]
    [IsScalarTower ℂ (Π i, R i) M]
    (i : ι) : M →ₗ[Π i, R i] M where
  toFun x := (Pi.single i (1 : R i)) • x
  map_add' x y := by simp [smul_add]
  map_smul' a x := by
    -- Commute the scalar `a` past the central idempotent `Pi.single i 1`.
    calc
      (Pi.single i (1 : R i)) • (a • x) = (((Pi.single i (1 : R i)) : Π j, R j) * a) • x := by
        rw [mul_smul]
      _ = ((a * Pi.single i (1 : R i)) • x : M) := by
        congr 1
        ext j
        by_cases hj : j = i
        · subst hj
          simp
        · simp [Pi.single_eq_of_ne hj]
      _ = a • ((Pi.single i (1 : R i)) • x) := by
        rw [mul_smul]

/-- Helper for Remark 13-13.2-2: the `i`-th central idempotent in a finite product algebra cuts
out the corresponding coordinate submodule. -/
private def pi_coordinate_submodule
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra ℂ (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module ℂ M]
    [IsScalarTower ℂ (Π i, R i) M]
    (i : ι) : Submodule (Π i, R i) M :=
  LinearMap.range (pi_coordinate_projection (R := R) (M := M) i)

/-- Helper for Remark 13-13.2-2: membership in the coordinate submodule means coming from the
action of the `i`-th central idempotent. -/
private theorem mem_pi_coordinate_submodule_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra ℂ (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module ℂ M]
    [IsScalarTower ℂ (Π i, R i) M]
    (i : ι) {x : M} :
    x ∈ pi_coordinate_submodule (R := R) (M := M) i ↔
      ∃ y : M, (Pi.single i (1 : R i)) • y = x := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by simpa [pi_coordinate_projection] using hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, by simpa [pi_coordinate_projection] using hy⟩

/-- Helper for Remark 13-13.2-2: the image of the `i`-th product idempotent already lies in the
corresponding coordinate submodule. -/
private theorem pi_coordinate_projection_mem
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra ℂ (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module ℂ M]
    [IsScalarTower ℂ (Π i, R i) M]
    (i : ι) (x : M) :
    pi_coordinate_projection (R := R) (M := M) i x ∈
      pi_coordinate_submodule (R := R) (M := M) i := by
  -- The coordinate submodule is defined as the range of the projection map.
  exact ⟨x, rfl⟩

/-- Helper for Remark 13-13.2-2: the `i`-th coordinate summand inherits the projected action of
the full product algebra. -/
private def pi_coordinate_toSubmodule
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra ℂ (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module ℂ M]
    [IsScalarTower ℂ (Π i, R i) M]
    (i : ι) : M →ₗ[Π i, R i] pi_coordinate_submodule (R := R) (M := M) i :=
  LinearMap.codRestrict
    (pi_coordinate_submodule (R := R) (M := M) i)
    (pi_coordinate_projection (R := R) (M := M) i)
    (pi_coordinate_projection_mem (R := R) (M := M) i)

/-- Helper for Remark 13-13.2-2: on the `i`-th coordinate summand, the full product action only
depends on the `i`-th factor. -/
private theorem pi_coordinate_submodule_action_factors_through_eval
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra ℂ (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module ℂ M]
    [IsScalarTower ℂ (Π i, R i) M]
    (i : ι) (b : Π j, R j)
    (x : pi_coordinate_submodule (R := R) (M := M) i) :
    b • (x : M) = (Pi.single i (b i)) • (x : M) := by
  rcases x with ⟨x, hx⟩
  rcases (mem_pi_coordinate_submodule_iff (R := R) (M := M) i).1 hx with ⟨y, rfl⟩
  -- Unpack the coordinate summand as the image of the `i`-th central idempotent.
  calc
    b • ((Pi.single i (1 : R i)) • y) =
        (((b : Π j, R j) * Pi.single i (1 : R i)) • y : M) := by
          rw [← mul_smul]
    _ = ((Pi.single i (b i) : Π j, R j) • y : M) := by
          congr 1
          ext j
          by_cases hj : j = i
          · subst hj
            simp
          · simp [Pi.single_eq_of_ne hj]
    _ = ((((Pi.single i (b i) : Π j, R j) * Pi.single i (1 : R i))) • y : M) := by
          congr 1
          ext j
          by_cases hj : j = i
          · subst hj
            simp
          · simp [Pi.single_eq_of_ne hj]
    _ = (Pi.single i (b i)) • ((Pi.single i (1 : R i)) • y) := by
          rw [mul_smul]

/-- Helper for Remark 13-13.2-2: the `i`-th central idempotent acts as the identity on its own
coordinate summand. -/
private theorem pi_coordinate_submodule_single_smul_eq_self
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra ℂ (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module ℂ M]
    [IsScalarTower ℂ (Π i, R i) M]
    (i : ι)
    (x : pi_coordinate_submodule (R := R) (M := M) i) :
    (Pi.single i (1 : R i)) • (x : M) = x := by
  rcases x with ⟨x, hx⟩
  rcases (mem_pi_coordinate_submodule_iff (R := R) (M := M) i).1 hx with ⟨y, rfl⟩
  -- Squaring the central idempotent leaves its image fixed.
  rw [← mul_smul]
  congr 1
  ext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Pi.single_eq_of_ne hj]

/-- Helper for Remark 13-13.2-2: a central idempotent from a different factor annihilates the
`j`-th coordinate summand. -/
private theorem pi_coordinate_submodule_single_smul_eq_zero_of_ne
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra ℂ (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module ℂ M]
    [IsScalarTower ℂ (Π i, R i) M]
    {i j : ι} (hij : i ≠ j)
    (x : pi_coordinate_submodule (R := R) (M := M) j) :
    (Pi.single i (1 : R i)) • (x : M) = 0 := by
  -- Reduce the action to the `j`-th coordinate, where the off-diagonal idempotent vanishes.
  have h :=
    pi_coordinate_submodule_action_factors_through_eval
      (R := R) (M := M) j (Pi.single i (1 : R i)) x
  have hij0 : (Pi.single i (1 : R i) : Π l, R l) j = 0 := by
    simp [Pi.single_eq_of_ne (show j ≠ i from hij.symm)]
  calc
    (Pi.single i (1 : R i)) • (x : M) = (Pi.single j ((Pi.single i (1 : R i) : Π l, R l) j)) •
        (x : M) := h
    _ = 0 := by
        rw [hij0]
        calc
          (Pi.single j (0 : R j) : Π l, R l) • (x : M) = (0 : Π l, R l) • (x : M) := by
            congr 1
            ext l
            by_cases hl : l = j
            · subst hl
              simp
            · simp [Pi.single_eq_of_ne hl]
          _ = 0 := by
            simp

/-- Helper for Remark 13-13.2-2: collect all coordinate projections into a map from the module
to the product of its coordinate summands. -/
private def pi_coordinate_decompose
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra ℂ (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module ℂ M]
    [IsScalarTower ℂ (Π i, R i) M] :
    M →ₗ[Π i, R i] (∀ i, pi_coordinate_submodule (R := R) (M := M) i) :=
  LinearMap.pi fun i ↦ pi_coordinate_toSubmodule (R := R) (M := M) i

/-- Helper for Remark 13-13.2-2: sum the coordinate summands back into the ambient module. -/
private def pi_coordinate_reassemble
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra ℂ (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module ℂ M]
    [IsScalarTower ℂ (Π i, R i) M] :
    (∀ i, pi_coordinate_submodule (R := R) (M := M) i) →ₗ[Π i, R i] M :=
  LinearMap.lsum (Π i, R i)
    (fun i ↦ pi_coordinate_submodule (R := R) (M := M) i)
    ℕ
    fun i ↦ (pi_coordinate_submodule (R := R) (M := M) i).subtype

/-- Helper for Remark 13-13.2-2: summing the idempotent pieces of a vector recovers the vector
itself. -/
private theorem pi_coordinate_reassemble_decompose_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra ℂ (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module ℂ M]
    [IsScalarTower ℂ (Π i, R i) M]
    (x : M) :
    pi_coordinate_reassemble (R := R) (M := M)
        (pi_coordinate_decompose (R := R) (M := M) x) =
      x := by
  -- The product idempotents sum to `1`, so their images reconstruct `x`.
  simpa [pi_coordinate_reassemble, pi_coordinate_decompose, pi_coordinate_toSubmodule,
    pi_coordinate_projection] using
    show (∑ i : ι, (Pi.single i (1 : R i)) • x) = x by
      rw [← Finset.sum_smul]
      calc
        (∑ i : ι, (Pi.single i (1 : R i) : Π j, R j)) • x = (1 : Π j, R j) • x := by
          congr 1
          ext j
          simp
        _ = x := by
          simp

/-- Helper for Remark 13-13.2-2: decomposing a tuple of coordinate vectors and then summing it
back leaves each coordinate unchanged. -/
private theorem pi_coordinate_decompose_reassemble_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra ℂ (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module ℂ M]
    [IsScalarTower ℂ (Π i, R i) M]
    (x : ∀ i, pi_coordinate_submodule (R := R) (M := M) i) :
    pi_coordinate_decompose (R := R) (M := M)
        (pi_coordinate_reassemble (R := R) (M := M) x) =
      x := by
  funext i
  apply Subtype.ext
  -- Only the `i`-th idempotent acts nontrivially on the `i`-th summand.
  simpa [pi_coordinate_decompose, pi_coordinate_reassemble, pi_coordinate_toSubmodule,
    pi_coordinate_projection] using
    show (∑ j : ι, (Pi.single i (1 : R i)) • (x j : M)) = (x i : M) by
      rw [Finset.sum_eq_single i]
      · simpa using pi_coordinate_submodule_single_smul_eq_self
          (R := R) (M := M) i (x i)
      · intro j _ hji
        simpa using pi_coordinate_submodule_single_smul_eq_zero_of_ne
          (R := R) (M := M) (show i ≠ j from hji.symm) (x j)
      · intro hi
        exact (hi (Finset.mem_univ i)).elim

/-- Helper for Remark 13-13.2-2: the coordinate projection map is bijective, with inverse given
by summing the coordinate inclusions. -/
private theorem pi_coordinate_decompose_bijective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra ℂ (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module ℂ M]
    [IsScalarTower ℂ (Π i, R i) M] :
    Function.Bijective (pi_coordinate_decompose (R := R) (M := M)) := by
  constructor
  · intro x y hxy
    -- Apply the reassembly map to both sides and use the verified left inverse.
    have hxy' := congrArg (pi_coordinate_reassemble (R := R) (M := M)) hxy
    simpa [pi_coordinate_reassemble_decompose_apply] using hxy'
  · intro x
    -- The explicit inverse is the sum of the coordinate-submodule inclusions.
    exact ⟨pi_coordinate_reassemble (R := R) (M := M) x,
      pi_coordinate_decompose_reassemble_apply (R := R) (M := M) x⟩

/-- Helper for Remark 13-13.2-2: every module over a finite product algebra splits as the
product of the coordinate summands cut out by the central idempotents. -/
private noncomputable def pi_idempotent_linearEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra ℂ (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module ℂ M]
    [IsScalarTower ℂ (Π i, R i) M] :
    M ≃ₗ[Π i, R i] (∀ i, pi_coordinate_submodule (R := R) (M := M) i) :=
  LinearEquiv.ofBijective
    (pi_coordinate_decompose (R := R) (M := M))
    (pi_coordinate_decompose_bijective (R := R) (M := M))

/-- Helper for Remark 13-13.2-2: the `i`-th coordinate summand carries the natural action of the
`i`-th factor, implemented through the corresponding product idempotent. -/
@[reducible] private def pi_coordinate_submodule_factorModule
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra ℂ (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module ℂ M]
    [IsScalarTower ℂ (Π i, R i) M]
    (i : ι) :
    Module (R i) (pi_coordinate_submodule (R := R) (M := M) i) where
  smul a x :=
    ⟨(Pi.single i a) • (x : M),
      (pi_coordinate_submodule (R := R) (M := M) i).smul_mem (Pi.single i a) x.2⟩
  one_smul x := by
    apply Subtype.ext
    change ((Pi.single i (1 : R i)) • (x : M)) = x
    simpa using
      pi_coordinate_submodule_single_smul_eq_self (R := R) (M := M) i x
  mul_smul a b x := by
    apply Subtype.ext
    change ((Pi.single i (a * b) : Π j, R j) • (x : M)) =
      ((Pi.single i a : Π j, R j) • ((Pi.single i b : Π j, R j) • (x : M)))
    rw [← mul_smul]
    congr 1
    ext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.single_eq_of_ne hj]
  smul_zero a := by
    apply Subtype.ext
    change ((Pi.single i a : Π j, R j) • (0 : M)) = 0
    simp
  smul_add a x y := by
    apply Subtype.ext
    change ((Pi.single i a : Π j, R j) • ((x : M) + y)) =
      ((Pi.single i a : Π j, R j) • (x : M)) + ((Pi.single i a : Π j, R j) • (y : M))
    simp
  zero_smul x := by
    apply Subtype.ext
    change ((Pi.single i (0 : R i) : Π j, R j) • (x : M)) = 0
    simp
  add_smul a b x := by
    apply Subtype.ext
    change ((Pi.single i (a + b) : Π j, R j) • (x : M)) =
      ((Pi.single i a : Π j, R j) • (x : M)) + ((Pi.single i b : Π j, R j) • (x : M))
    rw [← add_smul]
    congr 1
    ext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.single_eq_of_ne hj]

/-- Helper for Remark 13-13.2-2: the factor action on the `i`-th coordinate summand is
compatible with the ambient complex scalar action. -/
private theorem pi_coordinate_submodule_factor_isScalarTower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra ℂ (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module ℂ M]
    [IsScalarTower ℂ (Π i, R i) M]
    (i : ι) :
    let Xi := pi_coordinate_submodule (R := R) (M := M) i
    let _ : Module (R i) Xi := pi_coordinate_submodule_factorModule (R := R) (M := M) i
    IsScalarTower ℂ (R i) Xi := by
  let B := Π j, R j
  let Xi := pi_coordinate_submodule (R := R) (M := M) i
  let _ : Module (R i) Xi := pi_coordinate_submodule_factorModule (R := R) (M := M) i
  -- Compare the induced factor action with the original `ℂ`-action on the ambient module.
  exact
    IsScalarTower.of_algebraMap_smul (R := ℂ) (A := R i) (M := Xi) fun r x ↦ by
      apply Subtype.ext
      have hcoord :=
        pi_coordinate_submodule_action_factors_through_eval
          (R := R) (M := M) i ((algebraMap ℂ B) r) x
      calc
        ((((algebraMap ℂ (R i)) r) • x : Xi) : M) =
            ((Pi.single i ((algebraMap ℂ (R i)) r) : B) • (x : M)) := by
              rfl
        _ = ((Pi.single i (((algebraMap ℂ B) r) i) : B) • (x : M)) := by
              rfl
        _ = ((algebraMap ℂ B) r) • (x : M) := by
              symm
              exact hcoord
        _ = r • (x : M) := by
              simpa using IsScalarTower.algebraMap_smul (R := ℂ) (A := B) r (x : M)

/-- Helper for Remark 13-13.2-2: the trace of `Pi.single i a` on a module over a product algebra
is the trace of the induced action on the `i`-th coordinate summand. -/
private theorem trace_pi_single_action_eq_trace_coordinate_action
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra ℂ (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module ℂ M]
    [FiniteDimensional ℂ M] [IsScalarTower ℂ (Π i, R i) M]
    (i : ι) (a : R i) :
    let Xi := pi_coordinate_submodule (R := R) (M := M) i
    let _ : Module (R i) Xi := pi_coordinate_submodule_factorModule (R := R) (M := M) i
    let _ : IsScalarTower ℂ (R i) Xi :=
      pi_coordinate_submodule_factor_isScalarTower (R := R) (M := M) i
    LinearMap.trace ℂ M (DistribSMul.toLinearMap ℂ M (Pi.single i a)) =
      LinearMap.trace ℂ Xi (DistribSMul.toLinearMap ℂ Xi a) := by
  let Xi := pi_coordinate_submodule (R := R) (M := M) i
  let _ : Module (R i) Xi := pi_coordinate_submodule_factorModule (R := R) (M := M) i
  let _ : IsScalarTower ℂ (R i) Xi :=
    pi_coordinate_submodule_factor_isScalarTower (R := R) (M := M) i
  let e := pi_idempotent_linearEquiv (R := R) (M := M)
  let ek := e.restrictScalars ℂ
  let f :
      (j : ι) →
        pi_coordinate_submodule (R := R) (M := M) j →ₗ[ℂ]
          pi_coordinate_submodule (R := R) (M := M) j :=
    fun j ↦
      if h : j = i then by
        subst h
        exact DistribSMul.toLinearMap ℂ Xi a
      else 0
  have hconj :
      ek.conj (DistribSMul.toLinearMap ℂ M (Pi.single i a)) =
        LinearMap.piMap f := by
    -- Conjugating by the product-idempotent decomposition turns `Pi.single i a` into the
    -- block-diagonal endomorphism supported only on the `i`-th coordinate.
    apply LinearMap.ext
    intro x
    funext j
    rcases ek.surjective x with ⟨y, rfl⟩
    by_cases hj : j = i
    · subst j
      apply Subtype.ext
      rw [LinearEquiv.conj_apply_apply]
      simp [ek, e, pi_idempotent_linearEquiv,
        pi_coordinate_decompose, pi_coordinate_toSubmodule, pi_coordinate_projection, f,
        pi_coordinate_submodule_factorModule]
      rfl
    · apply Subtype.ext
      simp [LinearEquiv.conj_apply_apply, ek, e, pi_idempotent_linearEquiv,
        pi_coordinate_decompose, pi_coordinate_toSubmodule, pi_coordinate_projection, f, hj]
      rw [← mul_smul]
      have hmul :
          ((Pi.single i a : Π l, R l) * (Pi.single j (1 : R j) : Π l, R l)) = 0 := by
        ext l
        by_cases hli : l = i
        · subst hli
          simp [Pi.single_eq_of_ne (fun h => hj h.symm)]
        · by_cases hlj : l = j
          · subst hlj
            simp [Pi.single_eq_of_ne hj]
          · simp [Pi.single_eq_of_ne hlj, Pi.single_eq_of_ne hli]
      rw [hmul, zero_smul]
  have hpi :
      LinearMap.piMap f =
        LinearMap.piMap
          (Pi.single i
            (DistribSMul.toLinearMap ℂ
              (pi_coordinate_submodule (R := R) (M := M) i) a)) := by
    apply LinearMap.ext
    intro x
    funext j
    by_cases hj : j = i
    · subst j
      simp [f]
    · simp [f, hj]
  let _ :
      ∀ j, Module.Finite ℂ (pi_coordinate_submodule (R := R) (M := M) j) := fun j ↦
    Module.Finite.of_injective
      ((pi_coordinate_submodule (R := R) (M := M) j).subtype.restrictScalars ℂ)
      Subtype.val_injective
  -- Trace is invariant under conjugation, and the product trace keeps only the `i`-th block.
  calc
        LinearMap.trace ℂ M (DistribSMul.toLinearMap ℂ M (Pi.single i a)) =
        LinearMap.trace ℂ (∀ j, pi_coordinate_submodule (R := R) (M := M) j)
          (ek.conj (DistribSMul.toLinearMap ℂ M (Pi.single i a))) := by
            symm
            exact LinearMap.trace_conj' (DistribSMul.toLinearMap ℂ M (Pi.single i a))
              ek
    _ = LinearMap.trace ℂ (∀ j, pi_coordinate_submodule (R := R) (M := M) j)
          (LinearMap.piMap f) := by
            rw [hconj]
    _ = LinearMap.trace ℂ Xi (DistribSMul.toLinearMap ℂ Xi a) := by
          rw [hpi]
          change
            LinearMap.trace ℂ
                (∀ j, pi_coordinate_submodule (R := R) (M := M) j)
                (LinearMap.piMap
                  (Pi.single i
                    (DistribSMul.toLinearMap ℂ
                      (pi_coordinate_submodule (R := R) (M := M) i) a))) =
              LinearMap.trace ℂ Xi (DistribSMul.toLinearMap ℂ Xi a)
          simpa using
            trace_pi_single_eq_trace_coordinate_factor
              (M := fun j ↦ pi_coordinate_submodule (R := R) (M := M) j)
              (i := i)
              (f := DistribSMul.toLinearMap ℂ
                (pi_coordinate_submodule (R := R) (M := M) i) a)

/-- Helper for Remark 13-13.2-2: a factorwise linear equivalence between coordinate summands is
automatically linear for the ambient product algebra. -/
private noncomputable def coordinate_linearEquiv_is_product_linear
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra ℂ (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module ℂ M]
    [IsScalarTower ℂ (Π i, R i) M]
    {N : Type*} [AddCommGroup N] [Module (Π i, R i) N] [Module ℂ N]
    [IsScalarTower ℂ (Π i, R i) N]
    (i : ι) :
    let XiM := pi_coordinate_submodule (R := R) (M := M) i
    let XiN := pi_coordinate_submodule (R := R) (M := N) i
    let _ : Module (R i) XiM := pi_coordinate_submodule_factorModule (R := R) (M := M) i
    let _ : Module (R i) XiN := pi_coordinate_submodule_factorModule (R := R) (M := N) i
    (XiM ≃ₗ[R i] XiN) → XiM ≃ₗ[Π j, R j] XiN := by
  let XiM := pi_coordinate_submodule (R := R) (M := M) i
  let XiN := pi_coordinate_submodule (R := R) (M := N) i
  let _ : Module (R i) XiM := pi_coordinate_submodule_factorModule (R := R) (M := M) i
  let _ : Module (R i) XiN := pi_coordinate_submodule_factorModule (R := R) (M := N) i
  dsimp
  intro e
  -- The underlying equivalence is already additive and bijective; only ambient product-linearity
  -- remains to be checked.
  refine
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := ?_ }
  intro b x
  -- On both source and target, the ambient product action factors through the `i`-th
  -- coordinate, so `R i`-linearity of `e` is enough.
  have hx :
      b • x = ((b i) • x : XiM) := by
    have hx_single :
        ((((b i) • x : XiM)) : M) =
          (Pi.single i (b i)) • (x : M) := by
      rfl
    apply Subtype.ext
    calc
      b • (x : M) = (Pi.single i (b i)) • (x : M) := by
        exact
          pi_coordinate_submodule_action_factors_through_eval
            (R := R) (M := M) i b x
      _ = (((b i) • x : XiM) : M) := by
            symm
            exact hx_single
  have hy :
      b • e x = ((b i) • e x : XiN) := by
    have hy_single :
        ((((b i) • e x : XiN)) : N) =
          (Pi.single i (b i)) • (e x : N) := by
      rfl
    apply Subtype.ext
    calc
      b • (e x : N) = (Pi.single i (b i)) • (e x : N) := by
        exact
          pi_coordinate_submodule_action_factors_through_eval
            (R := R) (M := N) i b (e x)
      _ = (((b i) • e x : XiN) : N) := by
            symm
            exact hy_single
  calc
    e (b • x) = e ((b i) • x) := by rw [hx]
    _ = (b i) • e x := e.map_smul (b i) x
    _ = b • e x := by rw [hy]

/-- Helper for Remark 13-13.2-2: on the standard matrix module, the corner idempotent acts by
projecting to the corresponding coordinate. -/
private theorem matrix_corner_action_eq_pi_single_id
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {X : Type*} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    (i : n) :
    (DistribSMul.toLinearMap ℂ (n → X) (Matrix.single i i (1 : ℂ))) =
      LinearMap.piMap (Pi.single i (LinearMap.id : X →ₗ[ℂ] X)) := by
  let f : (j : n) → X →ₗ[ℂ] X := Pi.single i (LinearMap.id : X →ₗ[ℂ] X)
  -- Evaluate the matrix action coordinatewise: only the `i`-th row survives.
  apply LinearMap.ext
  intro v
  funext j
  change (Matrix.single i i (1 : ℂ) • v) j = (f j) (v j)
  rw [Matrix.Module.single_smul]
  by_cases h : j = i
  · subst h
    simp [f]
  · simp [f, h]

/-- Helper for Remark 13-13.2-2: on the standard matrix module, the trace of a corner idempotent
is the complex dimension of one coefficient space. -/
private theorem trace_matrix_corner_idempotent_eq_finrank
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {X : Type*} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    (i : n) :
    LinearMap.trace ℂ (n → X)
      (DistribSMul.toLinearMap ℂ (n → X) (Matrix.single i i (1 : ℂ))) =
        Module.finrank ℂ X := by
  letI : Module.Finite ℂ X := inferInstance
  letI : ∀ j : n, Module.Free ℂ ((fun _ : n ↦ X) j) := fun _ ↦ inferInstance
  letI : ∀ j : n, Module.Finite ℂ ((fun _ : n ↦ X) j) := fun _ ↦ inferInstance
  -- First rewrite the corner action as the product endomorphism supported on a single block.
  rw [matrix_corner_action_eq_pi_single_id (X := X) i]
  -- Then collapse the product trace to the unique surviving coordinate.
  simpa [LinearMap.trace_id] using
    trace_pi_single_eq_trace_coordinate_factor (M := fun _ : n ↦ X) (i := i)
      (f := (LinearMap.id : X →ₗ[ℂ] X))

/-- Helper for Remark 13-13.2-2: conjugating the action of a matrix corner idempotent through the
Morita equivalence identifies its trace with the dimension of the corresponding coefficient
module. -/
private theorem finiteDimensional_toModuleCatObj_of_matrix_module
    {m : ℕ} [NeZero m]
    {M : Type*} [AddCommGroup M] [Module (Matrix (Fin m) (Fin m) ℂ) M]
    [Module ℂ M] [FiniteDimensional ℂ M] [IsScalarTower ℂ (Matrix (Fin m) (Fin m) ℂ) M]
    (j : Fin m) :
    FiniteDimensional ℂ
      (MatrixModCat.toModuleCatObj ℂ
        (↑(ModuleCat.of (Matrix (Fin m) (Fin m) ℂ) M)) j) := by
  -- A Morita corner is a submodule of the ambient finite-dimensional complex module.
  dsimp
  infer_instance

/-- Helper for Remark 13-13.2-2: the Morita corner defined using the induced scalar structure is
canonically the same complex vector space as the ambient range of the corner idempotent. -/
private theorem toModuleCatObj_equiv_corner_range
    {m : ℕ} [NeZero m]
    {M : Type*} [AddCommGroup M] [Module (Matrix (Fin m) (Fin m) ℂ) M]
    [Module ℂ M] [FiniteDimensional ℂ M] [IsScalarTower ℂ (Matrix (Fin m) (Fin m) ℂ) M]
    (j : Fin m) :
    let Xj := MatrixModCat.toModuleCatObj ℂ
      (↑(ModuleCat.of (Matrix (Fin m) (Fin m) ℂ) M)) j
    let Yj : Submodule ℂ M :=
      LinearMap.range (DistribSMul.toLinearMap ℂ M (Matrix.single j j (1 : ℂ)))
    Nonempty (Xj ≃ₗ[ℂ] Yj) := by
  intro Xj Yj
  -- The two corner modules have the same carrier; only the scalar structures differ.
  let g : Xj →ₗ[ℂ] Yj :=
    { toFun := fun x ↦ ⟨x.1, by simpa [Xj, Yj, MatrixModCat.toModuleCatObj] using x.2⟩
      map_add' := fun x y ↦ rfl
      map_smul' := by
        intro r x
        apply Subtype.ext
        change ((r • x : Xj) : M) = r • (x : M)
        have hscalar :
            ((letI : Module ℂ M := Module.compHom M (Matrix.scalar (α := ℂ) (Fin m))
              (r : ℂ) • (x : M)) : M) = r • (x : M) := by
          -- Compare the induced scalar action with the ambient one through the scalar matrix.
          change (Matrix.scalar (Fin m) r) • (x : M) = r • (x : M)
          calc
            (Matrix.scalar (Fin m) r) • (x : M) =
                (r • (1 : Matrix (Fin m) (Fin m) ℂ)) • (x : M) := by
                  simp [Matrix.smul_one_eq_diagonal]
            _ = r • ((1 : Matrix (Fin m) (Fin m) ℂ) • (x : M)) := by
                  exact smul_assoc r (1 : Matrix (Fin m) (Fin m) ℂ) (x : M)
            _ = r • (x : M) := by
                  simp
        simpa using hscalar }
  have hg_bij : Function.Bijective g := by
    constructor
    · intro x y hxy
      ext
      exact congrArg Subtype.val hxy
    · intro y
      -- Surjectivity is again the identity map on the shared carrier set.
      refine ⟨⟨y.1, ?_⟩, ?_⟩
      · simpa [Xj, Yj, MatrixModCat.toModuleCatObj] using y.2
      · ext
        rfl
  exact ⟨LinearEquiv.ofBijective g hg_bij⟩

/-- Helper for Remark 13-13.2-2: conjugating the action of a matrix corner idempotent through the
Morita equivalence identifies its trace with the dimension of the corresponding coefficient
module. -/
private theorem trace_matrix_corner_action_eq_finrank_toModuleCatObj
    {m : ℕ} [NeZero m]
    {M : Type*} [AddCommGroup M] [Module (Matrix (Fin m) (Fin m) ℂ) M]
    [Module ℂ M] [FiniteDimensional ℂ M] [IsScalarTower ℂ (Matrix (Fin m) (Fin m) ℂ) M]
    (j : Fin m) :
    let Xj := MatrixModCat.toModuleCatObj ℂ
      (↑(ModuleCat.of (Matrix (Fin m) (Fin m) ℂ) M)) j
    LinearMap.trace ℂ M
      (DistribSMul.toLinearMap ℂ M (Matrix.single j j (1 : ℂ))) =
        Module.finrank ℂ Xj := by
  intro Xj
  let f : M →ₗ[ℂ] M := DistribSMul.toLinearMap ℂ M (Matrix.single j j (1 : ℂ))
  let Yj : Submodule ℂ M := LinearMap.range f
  have hf_idem : IsIdempotentElem f := by
    -- The matrix corner acts as an idempotent projector.
    change f * f = f
    ext x
    change Matrix.single j j (1 : ℂ) • (Matrix.single j j (1 : ℂ) • x) =
      Matrix.single j j (1 : ℂ) • x
    rw [← smul_assoc]
    congr 1
    simpa using (Matrix.single_mul_single_same (c := (1 : ℂ)) j j j (d := (1 : ℂ)))
  have htraceY : LinearMap.trace ℂ M f = (Module.finrank ℂ Yj : ℂ) := by
    -- The trace of a projector is the dimension of its image.
    letI : Module.Free ℂ Yj := inferInstance
    letI : Module.Finite ℂ Yj := inferInstance
    letI : Module.Free ℂ (LinearMap.ker f) := inferInstance
    letI : Module.Finite ℂ (LinearMap.ker f) := inferInstance
    simpa [Yj, f] using
      (LinearMap.IsProj.trace (R := ℂ) (M := M) (p := Yj) (f := f)
        (LinearMap.IsIdempotentElem.isProj_range f hf_idem))
  -- Identify the Morita corner with the ordinary range of the corner projector.
  calc
    LinearMap.trace ℂ M (DistribSMul.toLinearMap ℂ M (Matrix.single j j (1 : ℂ))) =
        LinearMap.trace ℂ M f := by
          rfl
    _ = (Module.finrank ℂ Yj : ℂ) := htraceY
    _ = Module.finrank ℂ Xj := by
          classical
          let e := Classical.choice (toModuleCatObj_equiv_corner_range (M := M) j)
          simpa [Yj] using
            (LinearEquiv.finrank_eq e)

/-- Helper for Remark 13-13.2-2: the `ℂ`-module structure on a Morita corner coming from
`Matrix.scalar` agrees with the ambient complex structure. -/
private theorem toModuleCatObj_scalar_restrict_linearEquiv
    {m : ℕ} [NeZero m]
    {M : Type*} [AddCommGroup M] [Module (Matrix (Fin m) (Fin m) ℂ) M]
    [Module ℂ M] [IsScalarTower ℂ (Matrix (Fin m) (Fin m) ℂ) M]
    (j : Fin m) :
    let MM : ModuleCat (Matrix (Fin m) (Fin m) ℂ) := ModuleCat.of (Matrix (Fin m) (Fin m) ℂ) M
    letI : Module ℂ M := Module.compHom M (Matrix.scalar (α := ℂ) (Fin m))
    letI : IsScalarTower ℂ (Matrix (Fin m) (Fin m) ℂ) M :=
      MatrixModCat.isScalarTower_toModuleCat (R := ℂ) MM
    Nonempty
      (MatrixModCat.toModuleCatObj ℂ M j ≃ₗ[ℂ]
        MatrixModCat.toModuleCatObj ℂ (↑(ModuleCat.of (Matrix (Fin m) (Fin m) ℂ) M)) j) := by
  let MM : ModuleCat (Matrix (Fin m) (Fin m) ℂ) := ModuleCat.of (Matrix (Fin m) (Fin m) ℂ) M
  letI : Module ℂ M := Module.compHom M (Matrix.scalar (α := ℂ) (Fin m))
  letI : IsScalarTower ℂ (Matrix (Fin m) (Fin m) ℂ) M :=
    MatrixModCat.isScalarTower_toModuleCat (R := ℂ) MM
  let Xj := MatrixModCat.toModuleCatObj ℂ M j
  let Yj := MatrixModCat.toModuleCatObj ℂ (↑(ModuleCat.of (Matrix (Fin m) (Fin m) ℂ) M)) j
  -- Both corners have the same carrier subset; only the ambient `ℂ`-action has been rewritten.
  let f : Xj →ₗ[ℂ] Yj :=
    { toFun := fun x ↦ ⟨x.1, by simpa [Xj, Yj, MatrixModCat.toModuleCatObj] using x.2⟩
      map_add' := fun x y ↦ rfl
      map_smul' := by
        intro r x
        apply Subtype.ext
        change
          (((letI : Module ℂ M := Module.compHom M (Matrix.scalar (α := ℂ) (Fin m))
            r • (x : M)) : M)) =
            r • (x : M)
        simpa using
          (IsScalarTower.algebraMap_smul
            (R := ℂ) (A := Matrix (Fin m) (Fin m) ℂ) r (x : M)) }
  have hf_bij : Function.Bijective f := by
    constructor
    · intro x y hxy
      ext
      exact congrArg Subtype.val hxy
    · intro y
      -- Surjectivity is again the identity map on the common carrier subset.
      refine ⟨⟨y.1, by simpa [Xj, Yj, MatrixModCat.toModuleCatObj] using y.2⟩, ?_⟩
      ext
      rfl
  exact ⟨LinearEquiv.ofBijective f hf_bij⟩

/-- Helper for Remark 13-13.2-2: for an algebra action into endomorphisms, scalar elements act by
the ambient complex scalar multiplication. -/
private theorem algHom_scalar_action_apply
    {A : Type*} [Ring A] [Algebra ℂ A]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (φ : A →ₐ[ℂ] Module.End ℂ W) (r : ℂ) (x : W) :
    (φ (algebraMap ℂ A r)) x = r • x := by
  -- Evaluate the algebra-hom commutation relation at the chosen vector.
  simpa using congrArg (fun f : Module.End ℂ W ↦ f x) (φ.commutes r)

/-- Helper for Remark 13-13.2-2: in the frozen ambient Morita corner, coercing a scalar multiple
back to the ambient module agrees with the ambient scalar action. -/
private theorem frozen_ambient_corner_coe_smul
    {m : ℕ} [NeZero m]
    {M : Type*} [AddCommGroup M] [Module (Matrix (Fin m) (Fin m) ℂ) M]
    [Module ℂ M] [IsScalarTower ℂ (Matrix (Fin m) (Fin m) ℂ) M]
    (j : Fin m) :
    let Xambient : Submodule ℂ (↑(ModuleCat.of (Matrix (Fin m) (Fin m) ℂ) M)) :=
      MatrixModCat.toModuleCatObj ℂ (↑(ModuleCat.of (Matrix (Fin m) (Fin m) ℂ) M)) j
    ∀ (r : ℂ) (x : Xambient),
      ((RingHom.id ℂ) r) • ((x : Xambient) : M) =
        (((((RingHom.id ℂ) r) • x) : Xambient) : M) := by
  intro Xambient r x
  -- In the frozen ambient corner, the subtype scalar action is inherited from the ambient module.
  rfl

/-- Helper for Remark 13-13.2-2: under the scalar tower from `ℂ` to matrix scalars, the scalar
matrix acts by the ambient complex scalar multiplication. -/
private theorem matrix_scalar_smul_eq_complex_smul
    {m : ℕ} [NeZero m]
    {M : Type*} [AddCommGroup M] [Module (Matrix (Fin m) (Fin m) ℂ) M]
    [Module ℂ M] [IsScalarTower ℂ (Matrix (Fin m) (Fin m) ℂ) M]
    (r : ℂ) (x : M) :
    (Matrix.scalar (Fin m) r) • x = r • x := by
  -- Expand the scalar matrix as `r • 1` and then reassociate the action through the scalar tower.
  calc
    (Matrix.scalar (Fin m) r) • x =
        (r • (1 : Matrix (Fin m) (Fin m) ℂ)) • x := by
          simp [Matrix.smul_one_eq_diagonal]
    _ = r • ((1 : Matrix (Fin m) (Fin m) ℂ) • x) := by
          exact smul_assoc r (1 : Matrix (Fin m) (Fin m) ℂ) x
    _ = r • x := by
          simp

/-- Helper for Remark 13-13.2-2: Morita reassembly for a matrix module can be transported to the
ambient corner module without changing the matrix-linearity. -/
private theorem toModuleCatFromModuleCatLinearEquiv_to_ambient_corner
    {m : ℕ} [NeZero m]
    {M : Type*} [AddCommGroup M] [Module (Matrix (Fin m) (Fin m) ℂ) M]
    [Module ℂ M] [IsScalarTower ℂ (Matrix (Fin m) (Fin m) ℂ) M]
    (j : Fin m) :
    let Xj := MatrixModCat.toModuleCatObj ℂ
      (↑(ModuleCat.of (Matrix (Fin m) (Fin m) ℂ) M)) j
    Nonempty (M ≃ₗ[Matrix (Fin m) (Fin m) ℂ] (Fin m → Xj)) := by
  intro Xj
  subst Xj
  classical
  -- Route correction: isolate the scalar-instance mismatch on the Morita corner once, then lift
  -- it coefficientwise before composing with the standard Morita reassembly equivalence.
  -- Freeze the ambient corner before introducing the Morita-local scalar structure.
  let Xambient : Submodule ℂ (↑(ModuleCat.of (Matrix (Fin m) (Fin m) ℂ) M)) :=
    MatrixModCat.toModuleCatObj ℂ (↑(ModuleCat.of (Matrix (Fin m) (Fin m) ℂ) M)) j
  let moduleC : Module ℂ M := inferInstance
  let scalarTowerAmbient : IsScalarTower ℂ (Matrix (Fin m) (Fin m) ℂ) M := inferInstance
  have htransport :
      Nonempty
        (M ≃ₗ[Matrix (Fin m) (Fin m) ℂ]
          (Fin m →
            MatrixModCat.toModuleCatObj ℂ
              (↑(ModuleCat.of (Matrix (Fin m) (Fin m) ℂ) M)) j)) := by
    let MM : ModuleCat (Matrix (Fin m) (Fin m) ℂ) :=
      ModuleCat.of (Matrix (Fin m) (Fin m) ℂ) M
    letI : Module ℂ M := Module.compHom M (Matrix.scalar (α := ℂ) (Fin m))
    letI : IsScalarTower ℂ (Matrix (Fin m) (Fin m) ℂ) M :=
      MatrixModCat.isScalarTower_toModuleCat (R := ℂ) MM
    -- Reassemble via Morita with the scalar-restricted corner, then transport the corner
    -- coefficientwise back to the frozen ambient `ℂ`-module structure.
    let eMorita :
        M ≃ₗ[Matrix (Fin m) (Fin m) ℂ]
          (Fin m → MatrixModCat.toModuleCatObj ℂ M j) :=
      toModuleCatFromModuleCatLinearEquiv ℂ MM j
    let Xinternal := MatrixModCat.toModuleCatObj ℂ M j
    let eCorner : Xinternal ≃ₗ[ℂ] Xambient := by
      -- The internal and ambient corners have the same carrier subset; only the ambient
      -- `ℂ`-action differs.
      let f : Xinternal →ₗ[ℂ] Xambient :=
        { toFun := fun x ↦ ⟨x.1, by simpa [Xinternal, Xambient, MatrixModCat.toModuleCatObj] using x.2⟩
          map_add' := fun x y ↦ rfl
          map_smul' := by
            intro r x
            apply Subtype.ext
            let xAmbient : Xambient :=
              ⟨(x : M), by simpa [Xinternal, Xambient, MatrixModCat.toModuleCatObj] using x.2⟩
            change
              ((r • x : Xinternal) : M) =
                (((RingHom.id ℂ) r • xAmbient : Xambient) : M)
            have hscalar :
                ((r • x : Xinternal) : M) =
                  (letI : Module ℂ M := moduleC
                   r • (x : M)) := by
              change
                (Matrix.scalar (Fin m) r) • (x : M) =
                  (letI : Module ℂ M := moduleC
                   r • (x : M))
              letI : Module ℂ M := moduleC
              letI : IsScalarTower ℂ (Matrix (Fin m) (Fin m) ℂ) M := scalarTowerAmbient
              simpa using
                (matrix_scalar_smul_eq_complex_smul (m := m) (M := M) r (x : M))
            have hambient :
                (letI : Module ℂ M := moduleC
                 r • (x : M)) =
                  (((RingHom.id ℂ) r • xAmbient : Xambient) : M) := by
              letI : Module ℂ M := moduleC
              rfl
            exact hscalar.trans hambient }
      have hf_bij : Function.Bijective f := by
        constructor
        · intro x y hxy
          ext
          exact congrArg Subtype.val hxy
        · intro y
          refine ⟨⟨y.1, by simpa [Xinternal, Xambient, MatrixModCat.toModuleCatObj] using y.2⟩, ?_⟩
          ext
          rfl
      exact LinearEquiv.ofBijective f hf_bij
    let eCoeff :
        (Fin m → Xinternal) ≃ₗ[Matrix (Fin m) (Fin m) ℂ]
          (Fin m → Xambient) :=
      matrix_module_linearEquiv_of_linearEquiv eCorner
    exact ⟨by
      simpa [Xinternal, Xambient] using (eMorita.trans eCoeff)⟩
  exact htransport

/-- Helper for Remark 13-13.2-2: equality of traces on a matrix corner idempotent identifies the
dimensions of the corresponding Morita coefficient spaces. -/
private theorem finrank_toModuleCatObj_eq_of_trace_eq_on_matrix_complex
    {m : ℕ} [NeZero m]
    {M : Type*} [AddCommGroup M] [Module (Matrix (Fin m) (Fin m) ℂ) M]
    [Module ℂ M] [FiniteDimensional ℂ M] [IsScalarTower ℂ (Matrix (Fin m) (Fin m) ℂ) M]
    {N : Type*} [AddCommGroup N] [Module (Matrix (Fin m) (Fin m) ℂ) N]
    [Module ℂ N] [FiniteDimensional ℂ N] [IsScalarTower ℂ (Matrix (Fin m) (Fin m) ℂ) N]
    (htrace : ∀ a : Matrix (Fin m) (Fin m) ℂ,
      LinearMap.trace ℂ M (DistribSMul.toLinearMap ℂ M a) =
        LinearMap.trace ℂ N (DistribSMul.toLinearMap ℂ N a))
    (j : Fin m) :
    Module.finrank ℂ
      (MatrixModCat.toModuleCatObj ℂ
        (↑(ModuleCat.of (Matrix (Fin m) (Fin m) ℂ) M)) j) =
      Module.finrank ℂ
        (MatrixModCat.toModuleCatObj ℂ
          (↑(ModuleCat.of (Matrix (Fin m) (Fin m) ℂ) N)) j) := by
  let XM := MatrixModCat.toModuleCatObj ℂ
    (↑(ModuleCat.of (Matrix (Fin m) (Fin m) ℂ) M)) j
  let XN := MatrixModCat.toModuleCatObj ℂ
    (↑(ModuleCat.of (Matrix (Fin m) (Fin m) ℂ) N)) j
  -- Evaluate the common trace identity on the primitive corner idempotent.
  have hcorner :
      LinearMap.trace ℂ M (DistribSMul.toLinearMap ℂ M (Matrix.single j j (1 : ℂ))) =
        LinearMap.trace ℂ N (DistribSMul.toLinearMap ℂ N (Matrix.single j j (1 : ℂ))) :=
    htrace (Matrix.single j j (1 : ℂ))
  -- Rewrite both traces as the dimensions of the corresponding Morita corners.
  have hcorner' : ((Module.finrank ℂ XM : ℕ) : ℂ) = Module.finrank ℂ XN := by
    calc
      ((Module.finrank ℂ XM : ℕ) : ℂ) =
          LinearMap.trace ℂ M
            (DistribSMul.toLinearMap ℂ M (Matrix.single j j (1 : ℂ))) := by
            symm
            simpa [XM] using
              (trace_matrix_corner_action_eq_finrank_toModuleCatObj (M := M) j)
      _ =
          LinearMap.trace ℂ N
            (DistribSMul.toLinearMap ℂ N (Matrix.single j j (1 : ℂ))) := hcorner
      _ = Module.finrank ℂ XN := by
            simpa [XN] using
              (trace_matrix_corner_action_eq_finrank_toModuleCatObj (M := N) j)
  exact_mod_cast hcorner'

/-- Helper for Remark 13-13.2-2: over a matrix algebra, equality of traces on every element
forces two finite-dimensional modules to be linearly equivalent. -/
private theorem nonempty_linearEquiv_of_trace_eq_on_matrix_complex
    {m : ℕ} [NeZero m]
    {M : Type*} [AddCommGroup M] [Module (Matrix (Fin m) (Fin m) ℂ) M]
    [Module ℂ M] [FiniteDimensional ℂ M] [IsScalarTower ℂ (Matrix (Fin m) (Fin m) ℂ) M]
    {N : Type*} [AddCommGroup N] [Module (Matrix (Fin m) (Fin m) ℂ) N]
    [Module ℂ N] [FiniteDimensional ℂ N] [IsScalarTower ℂ (Matrix (Fin m) (Fin m) ℂ) N]
    (htrace : ∀ a : Matrix (Fin m) (Fin m) ℂ,
      LinearMap.trace ℂ M (DistribSMul.toLinearMap ℂ M a) =
        LinearMap.trace ℂ N (DistribSMul.toLinearMap ℂ N a)) :
    Nonempty (M ≃ₗ[Matrix (Fin m) (Fin m) ℂ] N) := by
  classical
  let j : Fin m := 0
  let XM := MatrixModCat.toModuleCatObj ℂ
    (↑(ModuleCat.of (Matrix (Fin m) (Fin m) ℂ) M)) j
  let XN := MatrixModCat.toModuleCatObj ℂ
    (↑(ModuleCat.of (Matrix (Fin m) (Fin m) ℂ) N)) j
  let _ : FiniteDimensional ℂ XM := by
    simpa [XM] using (finiteDimensional_toModuleCatObj_of_matrix_module (M := M) j)
  let _ : FiniteDimensional ℂ XN := by
    simpa [XN] using (finiteDimensional_toModuleCatObj_of_matrix_module (M := N) j)
  -- Compare one Morita corner by evaluating the common trace identity on its primitive
  -- idempotent.
  have hdim : Module.finrank ℂ XM = Module.finrank ℂ XN := by
    simpa [XM, XN] using
      (finrank_toModuleCatObj_eq_of_trace_eq_on_matrix_complex
        (M := M) (N := N) htrace j)
  -- Build the coefficient-space equivalence from the resulting finrank equality.
  let eCorner : XM ≃ₗ[ℂ] XN := LinearEquiv.ofFinrankEq XM XN hdim
  -- Route correction: reassemble entirely in the ambient-corner model so the scalar transport
  -- is isolated in the dedicated adapter theorem.
  let eMoritaM : M ≃ₗ[Matrix (Fin m) (Fin m) ℂ] (Fin m → XM) := by
    simpa [XM] using
      (Classical.choice
        (toModuleCatFromModuleCatLinearEquiv_to_ambient_corner (M := M) j))
  let eMoritaN : N ≃ₗ[Matrix (Fin m) (Fin m) ℂ] (Fin m → XN) := by
    simpa [XN] using
      (Classical.choice
        (toModuleCatFromModuleCatLinearEquiv_to_ambient_corner (M := N) j))
  let eCoeff : (Fin m → XM) ≃ₗ[Matrix (Fin m) (Fin m) ℂ] (Fin m → XN) :=
    matrix_module_linearEquiv_of_linearEquiv eCorner
  -- Lift the corner equivalence coefficientwise and sandwich it between the two Morita
  -- reassemblies.
  exact ⟨eMoritaM.trans (eCoeff.trans eMoritaN.symm)⟩

/-- Helper for Remark 13-13.2-2: after transporting to a finite product of complex matrix
algebras, equality of traces on every element forces a product-linear equivalence. -/
private theorem nonempty_linearEquiv_of_trace_eq_on_pi_matrix_complex
    {n : ℕ} {d : Fin n → ℕ}
    (hd : ∀ i, NeZero (d i))
    {V' : Type*} [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    {W' : Type*} [AddCommGroup W'] [Module ℂ W'] [FiniteDimensional ℂ W']
    (φV : (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] Module.End ℂ V')
    (φW : (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] Module.End ℂ W')
    (htrace : ∀ b : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ,
      LinearMap.trace ℂ V' (φV b) = LinearMap.trace ℂ W' (φW b)) :
    let B := Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ
    let _ : Module B V' := Module.compHom V' φV.toRingHom
    let _ : Module B W' := Module.compHom W' φW.toRingHom
    Nonempty (V' ≃ₗ[B] W') := by
  let B := Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ
  let _ : Module B V' := Module.compHom V' φV.toRingHom
  let _ : Module B W' := Module.compHom W' φW.toRingHom
  let _ : IsScalarTower ℂ B V' :=
    IsScalarTower.of_algebraMap_smul (R := ℂ) (A := B) (M := V') fun r x ↦ by
      exact algHom_scalar_action_apply φV r x
  let _ : IsScalarTower ℂ B W' :=
    IsScalarTower.of_algebraMap_smul (R := ℂ) (A := B) (M := W') fun r x ↦ by
      exact algHom_scalar_action_apply φW r x
  let eV := pi_idempotent_linearEquiv (R := fun i ↦ Matrix (Fin (d i)) (Fin (d i)) ℂ) (M := V')
  let eW := pi_idempotent_linearEquiv (R := fun i ↦ Matrix (Fin (d i)) (Fin (d i)) ℂ) (M := W')
  let factorEquiv :
      (i : Fin n) →
        pi_coordinate_submodule (R := fun i ↦ Matrix (Fin (d i)) (Fin (d i)) ℂ) (M := V') i ≃ₗ[B]
          pi_coordinate_submodule (R := fun i ↦ Matrix (Fin (d i)) (Fin (d i)) ℂ) (M := W') i :=
    fun i ↦ by
      let XiV := pi_coordinate_submodule
        (R := fun i ↦ Matrix (Fin (d i)) (Fin (d i)) ℂ) (M := V') i
      let XiW := pi_coordinate_submodule
        (R := fun i ↦ Matrix (Fin (d i)) (Fin (d i)) ℂ) (M := W') i
      let _ : Module (Matrix (Fin (d i)) (Fin (d i)) ℂ) XiV :=
        pi_coordinate_submodule_factorModule
          (R := fun i ↦ Matrix (Fin (d i)) (Fin (d i)) ℂ) (M := V') i
      let _ : Module (Matrix (Fin (d i)) (Fin (d i)) ℂ) XiW :=
        pi_coordinate_submodule_factorModule
          (R := fun i ↦ Matrix (Fin (d i)) (Fin (d i)) ℂ) (M := W') i
      let _ : IsScalarTower ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ) XiV :=
        pi_coordinate_submodule_factor_isScalarTower
          (R := fun i ↦ Matrix (Fin (d i)) (Fin (d i)) ℂ) (M := V') i
      let _ : IsScalarTower ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ) XiW :=
        pi_coordinate_submodule_factor_isScalarTower
          (R := fun i ↦ Matrix (Fin (d i)) (Fin (d i)) ℂ) (M := W') i
      have htrace_i :
          ∀ a : Matrix (Fin (d i)) (Fin (d i)) ℂ,
            LinearMap.trace ℂ XiV (DistribSMul.toLinearMap ℂ XiV a) =
              LinearMap.trace ℂ XiW (DistribSMul.toLinearMap ℂ XiW a) := by
        intro a
        have hVtrace :
            LinearMap.trace ℂ V' (φV (Pi.single i a : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ)) =
              LinearMap.trace ℂ XiV (DistribSMul.toLinearMap ℂ XiV a) := by
          change
            LinearMap.trace ℂ V'
                (DistribSMul.toLinearMap ℂ V'
                  (Pi.single i a : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ)) =
              LinearMap.trace ℂ XiV (DistribSMul.toLinearMap ℂ XiV a)
          simpa [XiV] using
            (trace_pi_single_action_eq_trace_coordinate_action
              (R := fun i ↦ Matrix (Fin (d i)) (Fin (d i)) ℂ) (M := V') i a)
        have hWtrace :
            LinearMap.trace ℂ W' (φW (Pi.single i a : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ)) =
              LinearMap.trace ℂ XiW (DistribSMul.toLinearMap ℂ XiW a) := by
          change
            LinearMap.trace ℂ W'
                (DistribSMul.toLinearMap ℂ W'
                  (Pi.single i a : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ)) =
              LinearMap.trace ℂ XiW (DistribSMul.toLinearMap ℂ XiW a)
          simpa [XiW] using
            (trace_pi_single_action_eq_trace_coordinate_action
              (R := fun i ↦ Matrix (Fin (d i)) (Fin (d i)) ℂ) (M := W') i a)
        -- Specialize the global trace identity to the `i`-th block idempotent summand.
        rw [← hVtrace, ← hWtrace]
        exact htrace (Pi.single i a : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
      letI : NeZero (d i) := hd i
      let _ : FiniteDimensional ℂ XiV :=
        FiniteDimensional.of_injective
          ((pi_coordinate_submodule
            (R := fun i ↦ Matrix (Fin (d i)) (Fin (d i)) ℂ) (M := V') i).subtype.restrictScalars ℂ)
          Subtype.val_injective
      let _ : FiniteDimensional ℂ XiW :=
        FiniteDimensional.of_injective
          ((pi_coordinate_submodule
            (R := fun i ↦ Matrix (Fin (d i)) (Fin (d i)) ℂ) (M := W') i).subtype.restrictScalars ℂ)
          Subtype.val_injective
      let eFactor : XiV ≃ₗ[Matrix (Fin (d i)) (Fin (d i)) ℂ] XiW :=
        Classical.choice
          (nonempty_linearEquiv_of_trace_eq_on_matrix_complex
            (m := d i) (M := XiV) (N := XiW) htrace_i)
      -- Upgrade the factorwise equivalence to ambient product-linearity.
      exact
        coordinate_linearEquiv_is_product_linear
          (R := fun i ↦ Matrix (Fin (d i)) (Fin (d i)) ℂ) (M := V') (N := W') i eFactor
  -- Reassemble the ambient product modules from their coordinate summands.
  exact
    ⟨eV.trans ((LinearEquiv.piCongrRight factorEquiv).trans eW.symm)⟩

/-- Helper for Remark 13-13.2-2: over a finite-dimensional semisimple `ℂ`-algebra, equality of
traces on every algebra element should force an equivariant linear equivalence. -/
private theorem nonempty_linearEquiv_of_trace_eq_on_finite_semisimple_algebra_complex
    {A : Type*} [Ring A] [Algebra ℂ A] [Module.Finite ℂ A] [IsSemisimpleRing A]
    {V' : Type*} [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    {W' : Type*} [AddCommGroup W'] [Module ℂ W'] [FiniteDimensional ℂ W']
    (φV : A →ₐ[ℂ] Module.End ℂ V') (φW : A →ₐ[ℂ] Module.End ℂ W')
    (hV : let _ : Module A V' := Module.compHom V' φV.toRingHom
      IsSemisimpleModule A V')
    (hW : let _ : Module A W' := Module.compHom W' φW.toRingHom
      IsSemisimpleModule A W')
    (htrace : ∀ a : A, LinearMap.trace ℂ V' (φV a) = LinearMap.trace ℂ W' (φW a)) :
    let _ : Module A V' := Module.compHom V' φV.toRingHom
    let _ : Module A W' := Module.compHom W' φW.toRingHom
    Nonempty (V' ≃ₗ[A] W') := by
  let _ := hV
  let _ := hW
  let _ : Module A V' := Module.compHom V' φV.toRingHom
  let _ : Module A W' := Module.compHom W' φW.toRingHom
  classical
  -- Route correction: transport the algebra action along the complex-specialized Wedderburn
  -- equivalence, solve the product-of-matrix owner, and pull the resulting equivalence back.
  obtain ⟨n, d, hd, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ A
  let B := Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ
  let φV' : B →ₐ[ℂ] Module.End ℂ V' := φV.comp e.symm.toAlgHom
  let φW' : B →ₐ[ℂ] Module.End ℂ W' := φW.comp e.symm.toAlgHom
  have htrace' :
      ∀ b : B, LinearMap.trace ℂ V' (φV' b) = LinearMap.trace ℂ W' (φW' b) := by
    intro b
    -- Evaluate the original trace identity at the preimage of `b`.
    simpa [φV', φW'] using htrace (e.symm b)
  let _ : Module B V' := Module.compHom V' φV'.toRingHom
  let _ : Module B W' := Module.compHom W' φW'.toRingHom
  let _ : IsScalarTower ℂ B V' :=
    IsScalarTower.of_algebraMap_smul (R := ℂ) (A := B) (M := V') fun r x ↦ by
      exact algHom_scalar_action_apply φV' r x
  let _ : IsScalarTower ℂ B W' :=
    IsScalarTower.of_algebraMap_smul (R := ℂ) (A := B) (M := W') fun r x ↦ by
      exact algHom_scalar_action_apply φW' r x
  obtain ⟨eVW⟩ :=
    nonempty_linearEquiv_of_trace_eq_on_pi_matrix_complex
      (hd := hd) (φV := φV') (φW := φW') htrace'
  refine ⟨
    { toFun := eVW
      invFun := eVW.symm
      left_inv := eVW.left_inv
      right_inv := eVW.right_inv
      map_add' := eVW.map_add
      map_smul' := fun a x ↦ by
        -- Rewrite the `A`-action through the transported `B`-action and apply `B`-linearity.
        have hVaction : a • x = (e a : B) • x := by
          change (φV a) x = (φV' (e a)) x
          simp [φV']
        have hWaction : a • eVW x = (e a : B) • eVW x := by
          change (φW a) (eVW x) = (φW' (e a)) (eVW x)
          simp [φW']
        calc
          eVW (a • x) = eVW ((e a : B) • x) := by rw [hVaction]
          _ = (e a : B) • eVW x := eVW.map_smul (e a) x
          _ = a • eVW x := by rw [hWaction] }⟩

/-- Helper for Remark 13-13.2-2: equality with the dual character forces equivariant self-duality
for a continuous finite-dimensional compact-group representation. -/
private theorem nonempty_equiv_dual_of_character_eq_of_compactGroup
    (ρ : Representation ℂ G V) (hρ : Continuous fun p : G × V ↦ ρ p.1 p.2)
    (hχ : ρ.character = ρ.dual.character) :
    Nonempty (ρ.Equiv ρ.dual) := by
  -- Route correction: instead of searching for an external compact Peter-Weyl rigidity theorem,
  -- descend the common character to a finite-dimensional semisimple quotient of `ℂ[G]`.
  let ψ : MonoidAlgebra ℂ G →ₐ[ℂ] Module.End ℂ V × Module.End ℂ (Module.Dual ℂ V) :=
    ρ.asAlgebraHom.prod ρ.dual.asAlgebraHom
  let I : Ideal (MonoidAlgebra ℂ G) := RingHom.ker ψ
  letI : I.IsTwoSided := by
    change (RingHom.ker ψ).IsTwoSided
    infer_instance
  let A := MonoidAlgebra ℂ G ⧸ I
  let φV : A →ₐ[ℂ] Module.End ℂ V :=
    Ideal.Quotient.liftₐ I ρ.asAlgebraHom
      (prod_asAlgebraHom_ker_le_left (ρ := ρ) (ρ' := ρ.dual))
  let φW : A →ₐ[ℂ] Module.End ℂ (Module.Dual ℂ V) :=
    Ideal.Quotient.liftₐ I ρ.dual.asAlgebraHom
      (prod_asAlgebraHom_ker_le_right (ρ := ρ) (ρ' := ρ.dual))
  have htrace :
      ∀ a : A, LinearMap.trace ℂ V (φV a) = LinearMap.trace ℂ (Module.Dual ℂ V) (φW a) := by
    -- Character equality already controls traces on the whole common quotient algebra.
    simpa [ψ, I, A, φV, φW] using
      trace_eq_on_common_kernel_quotient_of_character_eq (ρ := ρ) (ρ' := ρ.dual) hχ
  let _ : Module.Finite ℂ A := by
    simpa [ψ, I, A] using common_kernel_quotient_finite (ρ := ρ) (ρ' := ρ.dual)
  let _ : IsSemisimpleRing A := by
    simpa [ψ, I, A] using
      common_kernel_quotient_isSemisimpleRing
        (ρ := ρ) (ρ' := ρ.dual)
        (isSemisimpleRepresentation_of_compactGroup ρ hρ)
        (dual_isSemisimpleRepresentation_of_compactGroup ρ hρ)
  let _ : Module A V := Module.compHom V φV.toRingHom
  let _ : Module A (Module.Dual ℂ V) := Module.compHom (Module.Dual ℂ V) φW.toRingHom
  have hsemV : IsSemisimpleModule A V := by
    have hsemV_from_monoidAlgebra :
        let _ : Module (MonoidAlgebra ℂ G) V :=
          Module.compHom V (φV.toRingHom.comp (Ideal.Quotient.mkₐ ℂ I).toRingHom)
        IsSemisimpleModule (MonoidAlgebra ℂ G) V := by
      -- Restrict the quotient action back to the original `ℂ[G]`-module structure on `V`.
      simpa [A, I, φV, ψ] using
        (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp
          (isSemisimpleRepresentation_of_compactGroup ρ hρ)
    exact
      isSemisimpleModule_of_ringHom_surjective
        (q := (Ideal.Quotient.mkₐ ℂ I).toRingHom)
        (hq := Ideal.Quotient.mk_surjective)
        hsemV_from_monoidAlgebra
  have hsemW : IsSemisimpleModule A (Module.Dual ℂ V) := by
    have hsemW_from_monoidAlgebra :
        let _ : Module (MonoidAlgebra ℂ G) (Module.Dual ℂ V) :=
          Module.compHom (Module.Dual ℂ V)
            (φW.toRingHom.comp (Ideal.Quotient.mkₐ ℂ I).toRingHom)
        IsSemisimpleModule (MonoidAlgebra ℂ G) (Module.Dual ℂ V) := by
      -- The same quotient-action comparison works for the dual representation.
      simpa [A, I, φW, ψ] using
        (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ.dual).mp
          (dual_isSemisimpleRepresentation_of_compactGroup ρ hρ)
    exact
      isSemisimpleModule_of_ringHom_surjective
        (q := (Ideal.Quotient.mkₐ ℂ I).toRingHom)
        (hq := Ideal.Quotient.mk_surjective)
        hsemW_from_monoidAlgebra
  have hAlinear : Nonempty (V ≃ₗ[A] Module.Dual ℂ V) := by
    -- The remaining algebraic owner is now purely semisimple trace-rigidity over a finite
    -- dimensional `ℂ`-algebra.
    simpa [A, φV, φW] using
      nonempty_linearEquiv_of_trace_eq_on_finite_semisimple_algebra_complex
        (A := A) (φV := φV) (φW := φW)
        (by simpa [A, φV] using hsemV)
        (by simpa [A, φW] using hsemW)
        htrace
  rcases hAlinear with ⟨e⟩
  let eℂ : V ≃ₗ[ℂ] Module.Dual ℂ V :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro r x
        have hVscalar : (φV (algebraMap ℂ A r) : V →ₗ[ℂ] V) x = r • x := by
          simpa using congrArg (fun f : Module.End ℂ V ↦ f x) (φV.commutes r)
        have hWscalar :
            (φW (algebraMap ℂ A r) : Module.Dual ℂ V →ₗ[ℂ] Module.Dual ℂ V) (e x) = r • e x := by
          simpa using
            congrArg (fun f : Module.End ℂ (Module.Dual ℂ V) ↦ f (e x)) (φW.commutes r)
        calc
          e (r • x) = e ((φV (algebraMap ℂ A r)) x) := by rw [hVscalar]
          _ = (φW (algebraMap ℂ A r)) (e x) := by
                exact e.map_smul (algebraMap ℂ A r) x
          _ = r • e x := hWscalar }
  refine ⟨Representation.Equiv.mk eℂ ?_⟩
  intro g
  ext x y
  let a : A := Ideal.Quotient.mkₐ ℂ I ((MonoidAlgebra.of ℂ G) g)
  have hVg : (φV a : V →ₗ[ℂ] V) x = (ρ g) x := by
    simpa [a, A, I, φV, Representation.asAlgebraHom_of]
  have hWg :
      (φW a : Module.Dual ℂ V →ₗ[ℂ] Module.Dual ℂ V) (eℂ x) y = (ρ.dual g (eℂ x)) y := by
    simpa [a, A, I, φW, Representation.asAlgebraHom_of]
  calc
    eℂ ((ρ g) x) y = eℂ ((φV a) x) y := by rw [hVg]
    _ = (φW a) (eℂ x) y := by
          exact congrArg (fun f : Module.Dual ℂ V ↦ f y) (e.map_smul a x)
    _ = (ρ.dual g (eℂ x)) y := hWg

/-- For a continuous finite-dimensional complex representation of a compact Hausdorff group on a
Hausdorff complex topological vector space, having real-valued character is equivalent to being
equivariantly self-dual. This is the compact-group bridge feeding the invariant-form criterion
already owned by `Theorem 13-13.2-1`. -/
theorem hasRealValuedCharacter_iff_nonempty_equiv_dual_of_compactGroup
    (ρ : Representation ℂ G V) (hρ : Continuous fun p : G × V ↦ ρ p.1 p.2) :
    IsValuedInBaseField ℝ ρ.character ↔ Nonempty (ρ.Equiv ρ.dual) := by
  rw [character_isValuedInBaseField_iff_forall_star_eq]
  constructor
  · intro hstar
    -- Route correction: the finite-group proof used the explicit finite-order trace identity;
    -- here the compact input is isolated in `char_dual_eq_star_of_compactGroup`.
    have hchar : ρ.character = ρ.dual.character := by
      ext g
      rw [char_dual_eq_star_of_compactGroup (ρ := ρ) hρ g]
      exact (hstar g).symm
    exact nonempty_equiv_dual_of_character_eq_of_compactGroup ρ hρ hchar
  · rintro ⟨e⟩ g
    -- Once self-duality is known, compare characters and rewrite the dual character by conjugation.
    rw [← char_dual_eq_star_of_compactGroup (ρ := ρ) hρ g]
    exact (congrFun (Representation.char_iso e) g).symm

-- Proof sketch: average a nondegenerate bilinear form over Haar measure to make it `G`-invariant,
-- then apply the compact-group analogue of the bilinear-form criterion from
-- `Theorem 13-13.2-1`.
/-- Remark 13-13.2-2 (1): for a continuous finite-dimensional complex representation of a compact
Hausdorff group on a Hausdorff complex topological vector space, having real-valued character is
equivalent to the existence of a nondegenerate invariant complex bilinear form. -/
theorem hasRealValuedCharacter_iff_exists_invariant_nondegenerate_bilinForm_of_compactGroup
    (ρ : Representation ℂ G V) (hρ : Continuous fun p : G × V ↦ ρ p.1 p.2) :
    IsValuedInBaseField ℝ ρ.character ↔
      ∃ B : BilinForm ℂ V, B.Nondegenerate ∧ B.IsInvariantUnder ρ := by
  rw [hasRealValuedCharacter_iff_nonempty_equiv_dual_of_compactGroup ρ hρ,
    nonempty_equiv_dual_iff_exists_invariant_nondegenerate_bilinForm]

-- Proof sketch: average a positive definite form on a real model over Haar measure to obtain a
-- `G`-invariant symmetric form, and conversely recover a `G`-stable real form from an invariant
-- orthogonal form as in `Theorem 13-13.2-1`.
/-- Helper for Remark 13-13.2-2: an equivariant conjugation determines a `G`-stable real form
whose complex span is all of `V`. -/
private theorem exists_stable_real_form_data_of_equivariant_conjugation_of_group
    (ρ : Representation ℂ G V) (σ : V →ₗ[ℝ] V)
    (hσ_smul : ∀ z : ℂ, ∀ x : V, σ (z • x) = star z • σ x)
    (hσ_sq : ∀ x : V, σ (σ x) = x)
    (hσ_equiv : ∀ g : G, ∀ x : V, σ (ρ g x) = ρ g (σ x)) :
    ∃ W : Submodule ℝ V,
      (∀ g : G, ∀ x : V, x ∈ W → ρ g x ∈ W) ∧
      Submodule.span ℂ (W : Set V) = ⊤ := by
  letI : Module ℝ V := .restrictScalars ℝ ℂ V
  letI : IsScalarTower ℝ ℂ V := .restrictScalars ℝ ℂ V
  -- Use `σ` as the star operation so that fixed vectors become the self-adjoint real form.
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
  · -- Equivariance preserves the fixed-point real form.
    intro g x hx
    change σ (ρ g x) = ρ g x
    rw [hσ_equiv g x, show σ x = x by exact hx]
  · -- The fixed vectors span after adjoining `i`, via the usual real/imaginary decomposition.
    simpa using (span_selfAdjoint (A := V))

/-- Helper for Remark 13-13.2-2: the fixed real form of a complex star module complexifies back
to the whole complex module. -/
private theorem exists_fixed_real_form_real_imaginary_decomposition
    [Module ℝ V] [IsScalarTower ℝ ℂ V] [StarAddMonoid V] [StarModule ℂ V] [StarModule ℝ V]
    (v : V) :
    ∃ a b : selfAdjoint.submodule ℝ V, (a : V) + Complex.I • (b : V) = v := by
  -- Split `v` into its self-adjoint real and imaginary parts inside the fixed real form.
  refine ⟨ℜ v, ℑ v, ?_⟩
  simpa using (realPart_add_I_smul_imaginaryPart v)

/-- Helper for Remark 13-13.2-2: the fixed real form of a complex star module complexifies back
to the whole complex module. -/
private theorem real_imaginary_parts_of_selfAdjoint
    [Module ℝ V] [IsScalarTower ℝ ℂ V] [StarAddMonoid V] [StarModule ℂ V] [StarModule ℝ V]
    (w : selfAdjoint.submodule ℝ V) :
    ℜ (w : V) = w ∧ ℑ (w : V) = 0 := by
  exact ⟨Subtype.ext w.property.coe_realPart, w.property.imaginaryPart⟩

/-- Helper for Remark 13-13.2-2: the subtype of self-adjoint vectors is canonically the same real
submodule as `selfAdjoint.submodule ℝ V`. -/
private def selfAdjoint_submodule_linearEquiv
    [Module ℝ V] [IsScalarTower ℝ ℂ V] [StarAddMonoid V] [StarModule ℂ V] [StarModule ℝ V] :
    selfAdjoint V ≃ₗ[ℝ] selfAdjoint.submodule ℝ V :=
  { toFun := fun w => ⟨(w : V), w.property⟩
    invFun := fun w => ⟨(w : V), by simpa using w.property⟩
    left_inv := by
      intro w
      rfl
    right_inv := by
      intro w
      rfl
    map_add' := by
      intro x y
      rfl
    map_smul' := by
      intro r x
      rfl }

/-- Helper for Remark 13-13.2-2: the fixed real form of a complex star module complexifies back
to the whole complex module. -/
private theorem tensor_fixed_real_form_inverse_on_pure_tensors_of_group
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

/-- Helper for Remark 13-13.2-2: the fixed real form of a complex star module complexifies back
to the whole complex module. -/
private theorem tensor_fixed_real_form_linearEquiv_of_group
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
        (tensor_fixed_real_form_inverse_on_pure_tensors_of_group (V := V) z w)
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

/-- Helper for Remark 13-13.2-2: an equivariant conjugation realizes the representation over
`ℝ`. -/
private theorem isRealizableOverReal_of_equivariant_conjugation_of_group
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
  letI : ContinuousSMul ℝ V :=
    { continuous_smul := by
        simpa using ((Complex.continuous_ofReal.comp continuous_fst).smul continuous_snd) }
  -- Package the conjugation as the star structure whose fixed vectors form the real model.
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
    -- Route correction: use the canonical tensor-span equivalence instead of constructing an
    -- inverse explicitly from real and imaginary parts.
    simpa [W] using (tensor_fixed_real_form_linearEquiv_of_group (V := V))
  rcases htensor with ⟨e, he⟩
  refine ⟨W, inferInstance, inferInstance, inferInstance, ρ₀, ?_⟩
  refine ⟨Representation.Equiv.mk e ?_⟩
  intro g
  apply TensorProduct.AlgebraTensorModule.ext
  intro z w
  -- On pure tensors, scalar extension acts by base change of `ρ₀`.
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

/-- Helper for Remark 13-13.2-2: a realization over `ℝ` carries the tensor-factor conjugation, and
transporting that involution across the scalar-extension equivalence yields an equivariant
conjugation on the complex representation space. -/
private theorem equivariant_conjugation_of_isRealizableOverReal_of_group
    (ρ : Representation ℂ G V) (hreal : IsRealizableOver ℝ ρ) :
    ∃ σ : V →ₗ[ℝ] V,
      (∀ z : ℂ, ∀ x : V, σ (z • x) = star z • σ x) ∧
      (∀ x : V, σ (σ x) = x) ∧
      (∀ g : G, ∀ x : V, σ (ρ g x) = ρ g (σ x)) := by
  rcases hreal with ⟨W, _instAddCommGroupW, _instModuleW, _instFiniteDimensionalW, ρ₀, hρ₀⟩
  rcases hρ₀ with ⟨e⟩
  let τ : ℂ ⊗[ℝ] W →ₗ[ℝ] ℂ ⊗[ℝ] W :=
    TensorProduct.map (Complex.conjAe.toLinearMap : ℂ →ₗ[ℝ] ℂ) (LinearMap.id : W →ₗ[ℝ] W)
  -- Transport the tensor-factor conjugation through the chosen realization equivalence.
  let σ : V →ₗ[ℝ] V :=
    { toFun := fun x ↦ e (τ (e.symm x))
      map_add' := by
        intro x y
        calc
          e (τ (e.symm (x + y))) = e (τ (e.symm x + e.symm y)) := by
            rw [show e.symm (x + y) = e.symm x + e.symm y by
              simpa using e.symm.map_add x y]
          _ = e (τ (e.symm x) + τ (e.symm y)) := by
            exact congrArg e (τ.map_add (e.symm x) (e.symm y))
          _ = e (τ (e.symm x)) + e (τ (e.symm y)) := by
            exact e.map_add (τ (e.symm x)) (τ (e.symm y))
      map_smul' := by
        intro r x
        rw [show e.symm (r • x) = (r : ℂ) • e.symm x by
          simpa using e.symm.map_smul (r : ℂ) x]
        change e (τ (r • e.symm x)) = r • e (τ (e.symm x))
        rw [show τ (r • e.symm x) = r • τ (e.symm x) by
          exact τ.map_smul r (e.symm x)]
        simpa using e.map_smul (r : ℂ) (τ (e.symm x)) }
  have hτ_smul : ∀ z : ℂ, ∀ x : ℂ ⊗[ℝ] W, τ (z • x) = star z • τ x := by
    intro z x
    -- On the scalar extension, conjugation acts only on the left tensor factor.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp [τ]
    · intro a w
      change τ ((z * a) ⊗ₜ[ℝ] w) = star z • τ (a ⊗ₜ[ℝ] w)
      simp [τ, TensorProduct.smul_tmul', mul_assoc, mul_left_comm, mul_comm]
    · intro x y hx hy
      simp [hx, hy]
  have hτ_sq : ∀ x : ℂ ⊗[ℝ] W, τ (τ x) = x := by
    intro x
    -- Applying complex conjugation twice is the identity on pure tensors.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp [τ]
    · intro z w
      simp [τ]
    · intro x y hx hy
      simp [hx, hy]
  have hτ_equiv :
      ∀ g : G, ∀ x : ℂ ⊗[ℝ] W,
        τ ((Representation.scalarExtension ρ₀) g x) =
          (Representation.scalarExtension ρ₀) g (τ x) := by
    intro g x
    -- The scalar-extension action touches only the right tensor factor, so it commutes with `τ`.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · calc
        τ ((Representation.scalarExtension ρ₀) g 0) = τ 0 := by
          rw [(Representation.scalarExtension ρ₀ g).map_zero]
          rfl
        _ = 0 := by
          rw [τ.map_zero]
        _ = (Representation.scalarExtension ρ₀) g 0 := by
          rw [(Representation.scalarExtension ρ₀ g).map_zero]
          rfl
    · intro z w
      change τ (((ρ₀ g).baseChange ℂ) (z ⊗ₜ[ℝ] w)) =
        ((ρ₀ g).baseChange ℂ) (τ (z ⊗ₜ[ℝ] w))
      calc
        τ (((ρ₀ g).baseChange ℂ) (z ⊗ₜ[ℝ] w))
            = star z ⊗ₜ[ℝ] (ρ₀ g w) := by
                rw [LinearMap.baseChange_tmul]
                rfl
        _ = ((ρ₀ g).baseChange ℂ) (star z ⊗ₜ[ℝ] w) := by
              rw [LinearMap.baseChange_tmul]
              rfl
        _ = ((ρ₀ g).baseChange ℂ) (τ (z ⊗ₜ[ℝ] w)) := by
              rfl
    · intro x y hx hy
      calc
        τ ((Representation.scalarExtension ρ₀) g (x + y))
            = τ (((Representation.scalarExtension ρ₀) g x) +
                ((Representation.scalarExtension ρ₀) g y)) := by
                  exact congrArg τ ((Representation.scalarExtension ρ₀ g).map_add x y)
        _ = τ ((Representation.scalarExtension ρ₀) g x) +
              τ ((Representation.scalarExtension ρ₀) g y) := by
                exact τ.map_add ((Representation.scalarExtension ρ₀) g x)
                  ((Representation.scalarExtension ρ₀) g y)
        _ = (Representation.scalarExtension ρ₀) g (τ x) +
              (Representation.scalarExtension ρ₀) g (τ y) := by
                rw [hx, hy]
                rfl
        _ = (Representation.scalarExtension ρ₀) g (τ x + τ y) := by
              exact ((Representation.scalarExtension ρ₀ g).map_add (τ x) (τ y)).symm
        _ = (Representation.scalarExtension ρ₀) g (τ (x + y)) := by
              exact congrArg ((Representation.scalarExtension ρ₀) g) (τ.map_add x y).symm
  refine ⟨σ, ?_, ?_, ?_⟩
  · intro z x
    -- The transported involution is conjugate-linear because `τ` is.
    change e (τ (e.symm (z • x))) = star z • e (τ (e.symm x))
    rw [show e.symm (z • x) = z • e.symm x by simpa using e.symm.map_smul z x]
    rw [show τ (z • e.symm x) = star z • τ (e.symm x) by
      exact hτ_smul z (e.symm x)]
    exact e.map_smul (star z) (τ (e.symm x))
  · intro x
    -- The square collapses because both `τ²` and `e ∘ e.symm` are the identity.
    change e (τ (e.symm (e (τ (e.symm x))))) = x
    rw [e.symm_apply_apply]
    rw [hτ_sq]
    exact e.apply_symm_apply x
  · intro g x
    -- Equivariance follows from the intertwining property of `e` and the commutation of `τ`
    -- with the scalar-extension action.
    change e (τ (e.symm (ρ g x))) = ρ g (e (τ (e.symm x)))
    rw [show e.symm (ρ g x) = (Representation.scalarExtension ρ₀) g (e.symm x) by
      simpa using congr($(e.symm.isIntertwining' g) x)]
    rw [hτ_equiv]
    simpa using congr($(e.isIntertwining' g) (τ (e.symm x)))

/-- Helper for Remark 13-13.2-2: a real model of a continuous compact-group representation should
produce the invariant symmetric nondegenerate bilinear form from the source proof. -/
private theorem exists_invariant_nondegenerate_symmetric_real_bilinForm_of_compactGroup
    {W : Type v} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [T2Space W] [FiniteDimensional ℝ W]
    (ρ : Representation ℝ G W) (hρ : Continuous fun p : G × W ↦ ρ p.1 p.2) :
    ∃ B : BilinForm ℝ W, B.Nondegenerate ∧ B.IsSymm ∧ B.IsInvariantUnder ρ := by
  let _ : MeasurableSpace G := borel G
  let _ : BorelSpace G := ⟨rfl⟩
  let b := Module.Free.chooseBasis ℝ W
  let ι := Module.Free.ChooseBasisIndex ℝ W
  letI : Finite ι := Module.Finite.finite_basis b
  letI : Fintype ι := Fintype.ofFinite ι
  let Bstd : BilinForm ℝ W :=
    LinearMap.mk₂ ℝ
      (fun x y ↦ ∑ i : ι, b.repr x i * b.repr y i)
      (by
        intro x y z
        simp [add_mul, Finset.sum_add_distrib])
      (by
        intro r x y
        simp [mul_assoc, Finset.mul_sum])
      (by
        intro x y z
        simp [mul_add, Finset.sum_add_distrib])
      (by
        intro r x y
        simp [mul_left_comm, mul_assoc, Finset.mul_sum])
  have hBstd_symm : Bstd.IsSymm := by
    -- The coordinate dot product is symmetric over `ℝ`.
    refine ⟨?_⟩
    intro x y
    simp [Bstd, mul_comm]
  have hBstd_nonneg : ∀ x : W, 0 ≤ Bstd x x := by
    intro x
    -- Diagonal values are sums of squares in the chosen basis.
    have hsum_nonneg : 0 ≤ ∑ i : ι, (b.repr x i)^2 := by
      refine Finset.sum_nonneg ?_
      intro i hi
      exact sq_nonneg _
    simpa [Bstd, pow_two] using hsum_nonneg
  have hBstd_pos : ∀ x : W, x ≠ 0 → 0 < Bstd x x := by
    intro x hx
    have hxrepr : b.repr x ≠ 0 := by
      intro hrepr
      exact hx (b.repr.injective (by simpa using hrepr))
    obtain ⟨i, hi⟩ : ∃ i : ι, b.repr x i ≠ 0 := by
      by_contra h
      apply hxrepr
      ext j
      by_contra hj
      exact h ⟨j, hj⟩
    have hsum_pos : 0 < ∑ j : ι, (b.repr x j)^2 := by
      refine Finset.sum_pos' ?_ ?_
      · intro j hj
        exact sq_nonneg _
      · exact ⟨i, Finset.mem_univ i, by simpa using sq_pos_of_ne_zero hi⟩
    simpa [Bstd, pow_two] using hsum_pos
  have hρ_apply (x : W) : Continuous fun g : G ↦ ρ g x := by
    -- Fixing the vector turns joint continuity into continuity in the group variable.
    simpa using hρ.comp (continuous_id.prodMk continuous_const)
  have hcoord_cont (x : W) (i : ι) : Continuous fun g : G ↦ b.coord i (ρ g⁻¹ x) := by
    exact
      (b.coord i).continuous_of_finiteDimensional.comp ((hρ_apply x).comp continuous_inv)
  have hpair_cont (x y : W) : Continuous fun g : G ↦ Bstd (ρ g⁻¹ x) (ρ g⁻¹ y) := by
    -- Each coordinate product is continuous, so the finite sum is continuous.
    have hsum_cont :
        Continuous fun g : G ↦ ∑ i : ι, b.coord i (ρ g⁻¹ x) * b.coord i (ρ g⁻¹ y) := by
      refine continuous_finset_sum _ ?_
      intro i hi
      exact (hcoord_cont x i).mul (hcoord_cont y i)
    simpa [Bstd] using hsum_cont
  have hpair_integrable (x y : W) :
      MeasureTheory.Integrable
        (fun g : G ↦ Bstd (ρ g⁻¹ x) (ρ g⁻¹ y))
          (MeasureTheory.Measure.haar : MeasureTheory.Measure G) := by
    exact
      (hpair_cont x y).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  let B : BilinForm ℝ W :=
    LinearMap.mk₂ ℝ
      (fun x y ↦ ∫ g : G, Bstd (ρ g⁻¹ x) (ρ g⁻¹ y)
          ∂(MeasureTheory.Measure.haar : MeasureTheory.Measure G))
      (by
        intro x y z
        -- Push additivity in the first slot under the scalar-valued Haar integral.
        have hxz := hpair_integrable x z
        have hyz := hpair_integrable y z
        change
          (∫ g : G, Bstd (ρ g⁻¹ (x + y)) (ρ g⁻¹ z)
              ∂(MeasureTheory.Measure.haar : MeasureTheory.Measure G)) =
            (∫ g : G, Bstd (ρ g⁻¹ x) (ρ g⁻¹ z)
              ∂(MeasureTheory.Measure.haar : MeasureTheory.Measure G)) +
              ∫ g : G, Bstd (ρ g⁻¹ y) (ρ g⁻¹ z)
                ∂(MeasureTheory.Measure.haar : MeasureTheory.Measure G)
        rw [show
            (fun g : G ↦ Bstd (ρ g⁻¹ (x + y)) (ρ g⁻¹ z)) =
              fun g : G ↦ Bstd (ρ g⁻¹ x) (ρ g⁻¹ z) + Bstd (ρ g⁻¹ y) (ρ g⁻¹ z) by
            ext g
            simp
          , MeasureTheory.integral_add hxz hyz])
      (by
        intro r x y
        -- The first-slot scalar can be pulled through the integral.
        change
          (∫ g : G, Bstd (ρ g⁻¹ (r • x)) (ρ g⁻¹ y)
              ∂(MeasureTheory.Measure.haar : MeasureTheory.Measure G)) =
            r • ∫ g : G, Bstd (ρ g⁻¹ x) (ρ g⁻¹ y)
              ∂(MeasureTheory.Measure.haar : MeasureTheory.Measure G)
        rw [show
            (fun g : G ↦ Bstd (ρ g⁻¹ (r • x)) (ρ g⁻¹ y)) =
              fun g : G ↦ r • Bstd (ρ g⁻¹ x) (ρ g⁻¹ y) by
            ext g
            simp
          , MeasureTheory.integral_smul r])
      (by
        intro x y z
        -- Push additivity in the second slot under the scalar-valued Haar integral.
        have hxy := hpair_integrable x y
        have hxz := hpair_integrable x z
        change
          (∫ g : G, Bstd (ρ g⁻¹ x) (ρ g⁻¹ (y + z))
              ∂(MeasureTheory.Measure.haar : MeasureTheory.Measure G)) =
            (∫ g : G, Bstd (ρ g⁻¹ x) (ρ g⁻¹ y)
              ∂(MeasureTheory.Measure.haar : MeasureTheory.Measure G)) +
              ∫ g : G, Bstd (ρ g⁻¹ x) (ρ g⁻¹ z)
                ∂(MeasureTheory.Measure.haar : MeasureTheory.Measure G)
        rw [show
            (fun g : G ↦ Bstd (ρ g⁻¹ x) (ρ g⁻¹ (y + z))) =
              fun g : G ↦ Bstd (ρ g⁻¹ x) (ρ g⁻¹ y) + Bstd (ρ g⁻¹ x) (ρ g⁻¹ z) by
            ext g
            simp
          , MeasureTheory.integral_add hxy hxz])
      (by
        intro r x y
        -- The second-slot scalar can be pulled through the integral.
        change
          (∫ g : G, Bstd (ρ g⁻¹ x) (ρ g⁻¹ (r • y))
              ∂(MeasureTheory.Measure.haar : MeasureTheory.Measure G)) =
            r • ∫ g : G, Bstd (ρ g⁻¹ x) (ρ g⁻¹ y)
              ∂(MeasureTheory.Measure.haar : MeasureTheory.Measure G)
        rw [show
            (fun g : G ↦ Bstd (ρ g⁻¹ x) (ρ g⁻¹ (r • y))) =
              fun g : G ↦ r • Bstd (ρ g⁻¹ x) (ρ g⁻¹ y) by
            ext g
            simp
          , MeasureTheory.integral_smul r])
  have hB_diag_pos : ∀ x : W, x ≠ 0 → 0 < B x x := by
    intro x hx
    let f : G → ℝ := fun g ↦ Bstd (ρ g⁻¹ x) (ρ g⁻¹ x)
    have hf_cont : Continuous f := by
      simpa [f] using hpair_cont x x
    have hf_nonneg : 0 ≤ f := by
      intro g
      exact hBstd_nonneg (ρ g⁻¹ x)
    have hf_one : f 1 ≠ 0 := by
      simpa [f] using (hBstd_pos x hx).ne'
    -- Positivity comes from the identity point of the Haar average.
    simpa [B, f] using
      (hf_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero
        (μ := (MeasureTheory.Measure.haar : MeasureTheory.Measure G))
        (x := (1 : G))
        (HasCompactSupport.of_compactSpace f) hf_nonneg hf_one)
  refine ⟨B, ?_, ?_, ?_⟩
  · -- Strict positivity on the diagonal rules out both kernels.
    constructor
    · intro x hx
      by_contra hx0
      exact (hB_diag_pos x hx0).ne' (hx x)
    · intro y hy
      by_contra hy0
      exact (hB_diag_pos y hy0).ne' (hy y)
  · -- Symmetry is preserved pointwise under Haar averaging.
    refine ⟨?_⟩
    intro x y
    change
      (∫ g : G, Bstd (ρ g⁻¹ x) (ρ g⁻¹ y)
          ∂(MeasureTheory.Measure.haar : MeasureTheory.Measure G)) =
        ∫ g : G, Bstd (ρ g⁻¹ y) (ρ g⁻¹ x)
          ∂(MeasureTheory.Measure.haar : MeasureTheory.Measure G)
    congr 1
    ext g
    exact hBstd_symm.eq (ρ g⁻¹ x) (ρ g⁻¹ y)
  · -- Right translation of Haar measure gives `G`-invariance of the averaged form.
    rw [LinearMap.BilinForm.isInvariantUnder_iff]
    intro a x y
    let f : G → ℝ := fun g ↦ Bstd (ρ g⁻¹ x) (ρ g⁻¹ y)
    change
      (∫ g : G, Bstd (ρ g⁻¹ (ρ a x)) (ρ g⁻¹ (ρ a y))
          ∂(MeasureTheory.Measure.haar : MeasureTheory.Measure G)) =
        ∫ g : G, f g ∂(MeasureTheory.Measure.haar : MeasureTheory.Measure G)
    rw [show
        (fun g : G ↦ Bstd (ρ g⁻¹ (ρ a x)) (ρ g⁻¹ (ρ a y))) =
          fun g : G ↦ f (a⁻¹ * g) by
        ext g
        simp [f, map_mul]]
    simpa using
      (MeasureTheory.integral_mul_left_eq_self
        (μ := (MeasureTheory.Measure.haar : MeasureTheory.Measure G)) f a⁻¹)

/-- Helper for Remark 13-13.2-2: scalar extension carries an invariant symmetric nondegenerate
real bilinear form to an invariant symmetric nondegenerate complex bilinear form. -/
private theorem baseChange_nondegenerate_invariant_symmetric_bilinForm_of_group
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

/-- Helper for Remark 13-13.2-2: once an equivariant conjugation is available on `V`, the compact
invariant Hermitian structure can be converted into the symmetric invariant bilinear form required
by the source proof. -/
private theorem exists_invariant_nondegenerate_symmetric_bilinForm_of_equivariant_conjugation_of_compactGroup
    (ρ : Representation ℂ G V) (hρ : Continuous fun p : G × V ↦ ρ p.1 p.2)
    (σ : V →ₗ[ℝ] V)
    (hσ_smul : ∀ z : ℂ, ∀ x : V, σ (z • x) = star z • σ x)
    (hσ_sq : ∀ x : V, σ (σ x) = x)
    (hσ_equiv : ∀ g : G, ∀ x : V, σ (ρ g x) = ρ g (σ x)) :
    ∃ B : BilinForm ℂ V, B.Nondegenerate ∧ B.IsSymm ∧ B.IsInvariantUnder ρ := by
  letI : Module ℝ V := .restrictScalars ℝ ℂ V
  letI : IsScalarTower ℝ ℂ V := .restrictScalars ℝ ℂ V
  letI : Module.Finite ℂ V := by infer_instance
  letI : Module.Finite ℝ V := Module.Finite.trans ℂ V
  letI : FiniteDimensional ℝ V := by infer_instance
  letI : ContinuousSMul ℝ V :=
    { continuous_smul := by
        simpa using ((Complex.continuous_ofReal.comp continuous_fst).smul continuous_snd) }
  -- Route correction: pass to the fixed real form of `σ`, average there over Haar measure, and
  -- only then transport the resulting symmetric form back to `V`.
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
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  letI : ContinuousSMul ℝ W := SMulMemClass.continuousSMul W
  letI : FiniteDimensional ℝ W := by infer_instance
  let ρ₀ : Representation ℝ G W :=
    { toFun := fun g =>
        ((ρ g).restrictScalars ℝ).restrict <| by
          intro x hx
          change σ (ρ g x) = ρ g x
          rw [hσ_equiv g x]
          exact congrArg (ρ g) hx
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro g h
        ext x
        simp }
  have hρ₀ : Continuous fun p : G × W ↦ ρ₀ p.1 p.2 := by
    -- Restrict the continuous complex action to the fixed real form.
    rw [Topology.IsInducing.subtypeVal.continuous_iff]
    simpa [ρ₀] using hρ.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  rcases exists_invariant_nondegenerate_symmetric_real_bilinForm_of_compactGroup
      (ρ := ρ₀) hρ₀ with ⟨B₀, hB₀, hB₀_symm, hB₀_invariant⟩
  have hBC :=
    baseChange_nondegenerate_invariant_symmetric_bilinForm_of_group
      (ρ := ρ₀) (B := B₀) hB₀ hB₀_symm hB₀_invariant
  have htensor :
      ∃ e : ℂ ⊗[ℝ] W ≃ₗ[ℂ] V,
        ∀ z : ℂ, ∀ w : W, e (z ⊗ₜ[ℝ] w) = z • (w : V) := by
    -- The fixed real form complexifies back to the original representation space.
    simpa [W] using (tensor_fixed_real_form_linearEquiv_of_group (V := V))
  rcases htensor with ⟨e, he⟩
  let eρ : (Representation.scalarExtension ρ₀).Equiv ρ := by
    refine Representation.Equiv.mk e ?_
    intro g
    apply TensorProduct.AlgebraTensorModule.ext
    intro z w
    -- On pure tensors, scalar extension acts by base change of the restricted real action.
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
  let BC : BilinForm ℂ (TensorProduct ℝ ℂ W) := B₀.baseChange ℂ
  let BV : BilinForm ℂ V := LinearMap.BilinForm.congr e BC
  refine ⟨BV, ?_, ?_, ?_⟩
  · -- Transport nondegeneracy across the complexification equivalence.
    simpa [BV, BC] using hBC.1.congr e
  · -- Symmetry is preserved under congruence by the complexification equivalence.
    refine ⟨?_⟩
    intro x y
    simpa [BV, BC] using hBC.2.1.eq (e.symm x) (e.symm y)
  · -- Move the invariance statement back through the intertwining complexification equivalence.
    rw [LinearMap.BilinForm.isInvariantUnder_iff]
    intro g x y
    have hx :
        e.symm (ρ g x) =
          (Representation.scalarExtension ρ₀) g (e.symm x) := by
      simpa using congr($(eρ.symm.isIntertwining' g) x)
    have hy :
        e.symm (ρ g y) =
          (Representation.scalarExtension ρ₀) g (e.symm y) := by
      simpa using congr($(eρ.symm.isIntertwining' g) y)
    rw [show BV (ρ g x) (ρ g y) =
        BC (e.symm (ρ g x)) (e.symm (ρ g y)) by rfl]
    rw [show BV x y = BC (e.symm x) (e.symm y) by rfl]
    rw [hx, hy]
    exact ((LinearMap.BilinForm.isInvariantUnder_iff BC (Representation.scalarExtension ρ₀)).1
      hBC.2.2) g _ _

/-- Helper for Remark 13-13.2-2: a real model of a compact-group representation produces the
invariant symmetric nondegenerate complex bilinear form from the source proof. -/
private theorem exists_invariant_nondegenerate_symmetric_bilinForm_of_isRealizableOverReal_of_compactGroup
    (ρ : Representation ℂ G V) (hρ : Continuous fun p : G × V ↦ ρ p.1 p.2)
    (hreal : IsRealizableOver ℝ ρ) :
    ∃ B : BilinForm ℂ V, B.Nondegenerate ∧ B.IsSymm ∧ B.IsInvariantUnder ρ := by
  rcases equivariant_conjugation_of_isRealizableOverReal_of_group ρ hreal with
    ⟨σ, hσ_smul, hσ_sq, hσ_equiv⟩
  -- Route correction: stay on `V`, extract the algebraic conjugation from the realization, and
  -- reduce the compact step to the Hermitian-plus-conjugation construction.
  exact
    exists_invariant_nondegenerate_symmetric_bilinForm_of_equivariant_conjugation_of_compactGroup
      ρ hρ σ hσ_smul hσ_sq hσ_equiv

/-- Helper for Remark 13-13.2-2: an invariant symmetric nondegenerate bilinear form should yield
the equivariant conjugation used to recover a real form. -/
private theorem equivariant_conjugation_of_invariant_symmetric_nondegenerate_bilinForm_of_compactGroup
    (ρ : Representation ℂ G V) (hρ : Continuous fun p : G × V ↦ ρ p.1 p.2)
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
  rcases exists_invariant_positive_conjugate_dual_equiv_of_compactGroup ρ hρ with
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
          simpa using (hJ_star (L y) x)
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
  have hp_eval_eig :
      ∀ i : Fin (Module.finrank ℂ V), p.eval (eig i : ℂ) = Complex.sqrt (eig i : ℂ) := by
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
      ψInv (ψInv (L (basis i))) =
          ψInv (((eig i : ℂ) * (Complex.sqrt (eig i : ℂ))⁻¹) • basis i) := by
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

/-- Remark 13-13.2-2 (2): for a continuous finite-dimensional complex representation of a compact
Hausdorff group on a Hausdorff complex topological vector space, realizability over `ℝ` is
equivalent to the existence of a nondegenerate symmetric invariant complex bilinear form. -/
theorem isRealizableOverReal_iff_exists_invariant_nondegenerate_symmetric_bilinForm_of_compactGroup
    (ρ : Representation ℂ G V) (hρ : Continuous fun p : G × V ↦ ρ p.1 p.2) :
    IsRealizableOver ℝ ρ ↔
      ∃ B : BilinForm ℂ V,
        B.Nondegenerate ∧ B.IsSymm ∧ B.IsInvariantUnder ρ := by
  constructor
  · intro hreal
    -- Route correction: the forward direction should stay on the real model and average there,
    -- rather than trying to average directly on the abstract realization witness.
    exact
      exists_invariant_nondegenerate_symmetric_bilinForm_of_isRealizableOverReal_of_compactGroup
        ρ hρ hreal
  · rintro ⟨B, hB, hBsymm, hBinv⟩
    rcases
        equivariant_conjugation_of_invariant_symmetric_nondegenerate_bilinForm_of_compactGroup
          ρ hρ B hB hBsymm hBinv with
      ⟨σ, hσ_smul, hσ_sq, hσ_equiv⟩
    -- Once the equivariant conjugation exists, the fixed real form realizes `ρ` over `ℝ`.
    exact isRealizableOverReal_of_equivariant_conjugation_of_group ρ σ hσ_smul hσ_sq hσ_equiv

end

end Representation
