import Mathlib

open MeasureTheory
open DomMulAct
open scoped ENNReal MonoidAlgebra
open scoped ComplexStarModule

noncomputable section

universe u v

namespace Representation

section PeterWeyl

variable {G : Type u} [MeasurableSpace G] [Group G] [TopologicalSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
variable {W : Type v} [TopologicalSpace W] [AddCommGroup W] [Module ℂ W]
  [IsTopologicalAddGroup W] [ContinuousSMul ℂ W] [T2Space W] [FiniteDimensional ℂ W]

/-- Helper for Remark 4-4.3-1: averaging the standard Hermitian form over Haar measure produces a
`G`-invariant positive conjugate-dual equivalence on `W`. -/
theorem averaged_invariant_toDual
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2) :
    ∃ J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W,
      (∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y) ∧
      (∀ x y : W, star (J x y) = J y x) ∧
      (∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ)) := by
  let b := Module.Free.chooseBasis ℂ W
  let ι := Module.Free.ChooseBasisIndex ℂ W
  letI : Finite ι := Module.Finite.finite_basis b
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  let Jstd : W →ₗ⋆[ℂ] Module.Dual ℂ W :=
    Matrix.toLinearMapₛₗ₂ (R := ℂ) (σ₁ := (↑Complex.conjAe : ℂ →+* ℂ)) b b
      (1 : Matrix ι ι ℂ)
  have hJstd_apply : ∀ x y : W, Jstd x y = ∑ i : ι, star (b.repr x i) * b.repr y i := by
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
  have hJstd_herm : ∀ x y : W, star (Jstd x y) = Jstd y x := by
    intro x y
    simp [hJstd_apply, mul_comm]
  have hJstd_diag : ∀ x : W, Jstd x x = ∑ i : ι, (Complex.normSq (b.repr x i) : ℂ) := by
    intro x
    simpa [Complex.normSq_eq_conj_mul_self] using hJstd_apply x x
  have hσ_apply (x : W) : Continuous fun g : G ↦ σ g x := by
    simpa using hσ.comp (continuous_id.prodMk continuous_const)
  have hcoord_cont (x : W) (i : ι) : Continuous fun g : G ↦ b.coord i (σ g⁻¹ x) := by
    exact
      (b.coord i).continuous_of_finiteDimensional.comp ((hσ_apply x).comp continuous_inv)
  have hpair_cont (x y : W) :
      Continuous fun g : G ↦ Jstd (σ g⁻¹ x) (σ g⁻¹ y) := by
    have hsum_cont :
        Continuous fun g : G ↦ ∑ i : ι, star (b.coord i (σ g⁻¹ x)) * b.coord i (σ g⁻¹ y) := by
      refine continuous_finset_sum _ ?_
      intro i hi
      exact (Complex.continuous_conj.comp (hcoord_cont x i)).mul (hcoord_cont y i)
    simpa [hJstd_apply] using hsum_cont
  have hpair_integrable (x y : W) :
      Integrable
        (fun g : G ↦ Jstd (σ g⁻¹ x) (σ g⁻¹ y))
        (Measure.haar : Measure G) := by
    exact
      (hpair_cont x y).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  let Jmap : W →ₗ⋆[ℂ] Module.Dual ℂ W :=
    LinearMap.mk₂'ₛₗ (ρ₁₂ := (↑Complex.conjAe : ℂ →+* ℂ)) (σ₁₂ := RingHom.id ℂ)
      (fun x y ↦ ∫ g : G, Jstd (σ g⁻¹ x) (σ g⁻¹ y) ∂(Measure.haar : Measure G))
      (by
        intro x y z
        have hyz := hpair_integrable y z
        have hxz := hpair_integrable x z
        change
          (∫ g : G, Jstd (σ g⁻¹ (x + y)) (σ g⁻¹ z) ∂(Measure.haar : Measure G)) =
            (∫ g : G, Jstd (σ g⁻¹ x) (σ g⁻¹ z) ∂(Measure.haar : Measure G)) +
              ∫ g : G, Jstd (σ g⁻¹ y) (σ g⁻¹ z) ∂(Measure.haar : Measure G)
        rw [show
            (fun g : G ↦ Jstd (σ g⁻¹ (x + y)) (σ g⁻¹ z)) =
              fun g : G ↦ Jstd (σ g⁻¹ x) (σ g⁻¹ z) + Jstd (σ g⁻¹ y) (σ g⁻¹ z) by
            ext g
            simp
          , integral_add hxz hyz])
      (by
        intro c x y
        change
          (∫ g : G, Jstd (σ g⁻¹ (c • x)) (σ g⁻¹ y) ∂(Measure.haar : Measure G)) =
            star c • ∫ g : G, Jstd (σ g⁻¹ x) (σ g⁻¹ y) ∂(Measure.haar : Measure G)
        rw [show
            (fun g : G ↦ Jstd (σ g⁻¹ (c • x)) (σ g⁻¹ y)) =
              fun g : G ↦ star c • Jstd (σ g⁻¹ x) (σ g⁻¹ y) by
            ext g
            simp
          , integral_smul (star c)])
      (by
        intro x y z
        have hxy := hpair_integrable x y
        have hxz := hpair_integrable x z
        change
          (∫ g : G, Jstd (σ g⁻¹ x) (σ g⁻¹ (y + z)) ∂(Measure.haar : Measure G)) =
            (∫ g : G, Jstd (σ g⁻¹ x) (σ g⁻¹ y) ∂(Measure.haar : Measure G)) +
              ∫ g : G, Jstd (σ g⁻¹ x) (σ g⁻¹ z) ∂(Measure.haar : Measure G)
        rw [show
            (fun g : G ↦ Jstd (σ g⁻¹ x) (σ g⁻¹ (y + z))) =
              fun g : G ↦ Jstd (σ g⁻¹ x) (σ g⁻¹ y) + Jstd (σ g⁻¹ x) (σ g⁻¹ z) by
            ext g
            simp
          , integral_add hxy hxz])
      (by
        intro c x y
        change
          (∫ g : G, Jstd (σ g⁻¹ x) (σ g⁻¹ (c • y)) ∂(Measure.haar : Measure G)) =
            c • ∫ g : G, Jstd (σ g⁻¹ x) (σ g⁻¹ y) ∂(Measure.haar : Measure G)
        rw [show
            (fun g : G ↦ Jstd (σ g⁻¹ x) (σ g⁻¹ (c • y))) =
              fun g : G ↦ c • Jstd (σ g⁻¹ x) (σ g⁻¹ y) by
            ext g
            simp
          , integral_smul c])
  have hJ_invariant : ∀ g : G, ∀ x y : W, Jmap (σ g x) (σ g y) = Jmap x y := by
    intro g x y
    let f : G → ℂ := fun h ↦ Jstd (σ h⁻¹ x) (σ h⁻¹ y)
    change
      (∫ h : G, Jstd (σ h⁻¹ (σ g x)) (σ h⁻¹ (σ g y)) ∂(Measure.haar : Measure G)) =
        ∫ h : G, f h ∂(Measure.haar : Measure G)
    rw [show
        (fun h : G ↦ Jstd (σ h⁻¹ (σ g x)) (σ h⁻¹ (σ g y))) =
          fun h : G ↦ f (g⁻¹ * h) by
        ext h
        simp [f, map_mul]]
    simpa using
      (MeasureTheory.integral_mul_left_eq_self
        (μ := (Measure.haar : Measure G)) f g⁻¹)
  have hJ_herm : ∀ x y : W, star (Jmap x y) = Jmap y x := by
    intro x y
    calc
      star (Jmap x y)
          = ∫ g : G, star (Jstd (σ g⁻¹ x) (σ g⁻¹ y)) ∂(Measure.haar : Measure G) := by
              symm
              simpa [Jmap] using
                (integral_conj
                  (μ := (Measure.haar : Measure G))
                  (f := fun g : G ↦ Jstd (σ g⁻¹ x) (σ g⁻¹ y)))
      _ = ∫ g : G, Jstd (σ g⁻¹ y) (σ g⁻¹ x) ∂(Measure.haar : Measure G) := by
            congr 1
            ext g
            exact hJstd_herm (σ g⁻¹ x) (σ g⁻¹ y)
      _ = Jmap y x := by
            rfl
  have hJ_pos : ∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ Jmap x x = (r : ℂ) := by
    intro x hx
    let f : G → ℝ := fun g ↦ ∑ j : ι, Complex.normSq (b.repr (σ g⁻¹ x) j)
    have hf_cont : Continuous f := by
      have hsum_cont :
          Continuous fun g : G ↦ ∑ j : ι, Complex.normSq (b.repr (σ g⁻¹ x) j) := by
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
    · simpa [r, f] using
        (hf_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero
          (μ := (Measure.haar : Measure G))
          (x := (1 : G))
          (HasCompactSupport.of_compactSpace f) hf_nonneg hf_one)
    · calc
        Jmap x x
            = ∫ g : G, Jstd (σ g⁻¹ x) (σ g⁻¹ x) ∂(Measure.haar : Measure G) := by
                rfl
        _ = ∫ g : G, (f g : ℂ) ∂(Measure.haar : Measure G) := by
              congr 1
              ext g
              simpa [f] using hJstd_diag (σ g⁻¹ x)
        _ = (r : ℂ) := by
              simpa [r] using
                (integral_ofReal
                  (μ := (Measure.haar : Measure G))
                  (f := f))
  have hJ_zero : ∀ {x : W}, Jmap x = 0 → x = 0 := by
    intro x hxJ
    by_contra hx0
    rcases hJ_pos x hx0 with ⟨r, hr, hr_eq⟩
    have hxx : Jmap x x = 0 := by
      exact congrArg (fun f : Module.Dual ℂ W ↦ f x) hxJ
    rw [hr_eq] at hxx
    exact hr.ne' (Complex.ofReal_eq_zero.mp hxx)
  have hJ_inj : Function.Injective Jmap := by
    intro x y hxy
    apply sub_eq_zero.mp
    have hsub : Jmap (x - y) = 0 := by
      simpa [map_sub, hxy]
    exact hJ_zero hsub
  have hJR_smul : ∀ r : ℝ, ∀ x : W, Jmap (r • x) = r • Jmap x := by
    intro r x
    simpa using Jmap.map_smulₛₗ (r : ℂ) x
  let JR : W →ₗ[ℝ] Module.Dual ℂ W :=
    { toFun := Jmap
      map_add' := Jmap.map_add
      map_smul' := hJR_smul }
  have hJR_inj : Function.Injective JR := hJ_inj
  have hfinrankR : Module.finrank ℝ W = Module.finrank ℝ (Module.Dual ℂ W) := by
    calc
      Module.finrank ℝ W = 2 * Module.finrank ℂ W := by
        simpa [two_mul] using (finrank_real_of_complex W)
      _ = 2 * Module.finrank ℂ (Module.Dual ℂ W) := by
        rw [Subspace.dual_finrank_eq]
      _ = Module.finrank ℝ (Module.Dual ℂ W) := by
        symm
        simpa [two_mul] using (finrank_real_of_complex (Module.Dual ℂ W))
  have hJ_surj : Function.Surjective Jmap := by
    have hJR_surj : Function.Surjective JR := by
      exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrankR).mp hJR_inj
    exact hJR_surj
  let J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W := LinearEquiv.ofBijective Jmap ⟨hJ_inj, hJ_surj⟩
  refine ⟨J, ?_, ?_, ?_⟩
  · intro g x y
    exact hJ_invariant g x y
  · intro x y
    exact hJ_herm x y
  · intro x hx
    exact hJ_pos x hx

/-- Helper for Remark 4-4.3-1: an irreducible finite-dimensional representation contains a
nonzero vector. -/
theorem exists_ne_zero_irreducible_vector
    (σ : Representation ℂ G W) [σ.IsIrreducible] :
    ∃ x : W, x ≠ 0 := by
  letI : Module ℂ[G] W := σ.instModuleMonoidAlgebraAsModule
  letI : IsScalarTower ℂ ℂ[G] W := by
    simpa using σ.instIsScalarTowerMonoidAlgebraAsModule
  letI : IsSimpleModule ℂ[G] W := by
    simpa using (Representation.irreducible_iff_isSimpleModule_asModule σ).mp inferInstance
  letI : Nontrivial W := IsSimpleModule.nontrivial ℂ[G] W
  exact exists_ne (0 : W)

/-- Helper for Remark 4-4.3-1: fix a nonzero source vector for Schur-scalar extraction. -/
noncomputable def chosen_irreducible_vector
    (σ : Representation ℂ G W) [σ.IsIrreducible] : W :=
  Classical.choose (exists_ne_zero_irreducible_vector (G := G) σ)

/-- Helper for Remark 4-4.3-1: the chosen source vector is nonzero. -/
theorem chosen_irreducible_vector_ne_zero
    (σ : Representation ℂ G W) [σ.IsIrreducible] :
    chosen_irreducible_vector (G := G) σ ≠ 0 :=
  Classical.choose_spec (exists_ne_zero_irreducible_vector (G := G) σ)

/-- Helper for Remark 4-4.3-1: choose a dual vector normalized on the fixed nonzero source vector.
-/
noncomputable def chosen_irreducible_dual
    (σ : Representation ℂ G W) [σ.IsIrreducible] : Module.Dual ℂ W :=
  Classical.choose
    (Module.Projective.exists_dual_eq_one ℂ
      (chosen_irreducible_vector_ne_zero (G := G) σ))

/-- Helper for Remark 4-4.3-1: the chosen dual vector evaluates to `1` on the chosen source
vector. -/
theorem chosen_irreducible_dual_apply
    (σ : Representation ℂ G W) [σ.IsIrreducible] :
    chosen_irreducible_dual (G := G) σ (chosen_irreducible_vector (G := G) σ) = 1 :=
  Classical.choose_spec
    (Module.Projective.exists_dual_eq_one ℂ
      (chosen_irreducible_vector_ne_zero (G := G) σ))

/-- Helper for Remark 4-4.3-1: evaluate a self-intertwiner on the fixed source vector to read off
its Schur scalar. -/
noncomputable def scalar_of_intertwining_end
    (σ : Representation ℂ G W) [σ.IsIrreducible] :
    (σ.IntertwiningMap σ) →ₗ[ℂ] ℂ where
  toFun f :=
    chosen_irreducible_dual (G := G) σ (f (chosen_irreducible_vector (G := G) σ))
  map_add' f g := by
    change
      chosen_irreducible_dual (G := G) σ
          (f (chosen_irreducible_vector (G := G) σ) +
            g (chosen_irreducible_vector (G := G) σ)) =
        _
    exact map_add (chosen_irreducible_dual (G := G) σ) _ _
  map_smul' a f := by
    change
      chosen_irreducible_dual (G := G) σ
          (a • f (chosen_irreducible_vector (G := G) σ)) =
        _
    simp [smul_eq_mul]

/-- Helper for Remark 4-4.3-1: the identity endomorphism has extracted Schur scalar `1`. -/
theorem scalar_of_intertwining_end_id
    (σ : Representation ℂ G W) [σ.IsIrreducible] :
    scalar_of_intertwining_end (G := G) σ (Representation.IntertwiningMap.id σ) = 1 := by
  simp [scalar_of_intertwining_end, chosen_irreducible_dual_apply]

/-- Helper for Remark 4-4.3-1: Schur's lemma turns every self-intertwiner of `σ` into its extracted
scalar multiple of the identity. -/
theorem scalar_of_intertwining_end_smul_id
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    (f : σ.IntertwiningMap σ) :
    scalar_of_intertwining_end (G := G) σ f • Representation.IntertwiningMap.id σ = f := by
  have hId_ne : (Representation.IntertwiningMap.id σ : σ.IntertwiningMap σ) ≠ 0 := by
    intro hzero
    have hvalue := congrArg
      (fun F : σ.IntertwiningMap σ ↦ F (chosen_irreducible_vector (G := G) σ)) hzero
    exact chosen_irreducible_vector_ne_zero (G := G) σ (by simpa using hvalue)
  have hfinrank :
      Module.finrank ℂ (σ.IntertwiningMap σ) = 1 := by
    simpa using Representation.IsIrreducible.finrank_intertwiningMap_self (k := ℂ) σ
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' (Representation.IntertwiningMap.id σ) hId_ne).mp hfinrank f
  have hscalar :
      scalar_of_intertwining_end (G := G) σ f = c := by
    rw [← hc]
    simp [scalar_of_intertwining_end_id]
  simpa [hscalar] using hc

end PeterWeyl

end Representation
