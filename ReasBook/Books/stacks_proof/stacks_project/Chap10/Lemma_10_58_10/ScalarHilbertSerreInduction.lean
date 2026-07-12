import StacksProject_2024.Chap10.Lemma_10_58_10.ScalarHilbertSerre

open Filter
open HomogeneousIdeal
open scoped BigOperators DirectSum

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.decomposition
attribute [local instance] MvPolynomial.HomogeneousSubmodule.gradedMonoid

noncomputable section

universe u v

section

/-- Helper for Chap10 Lemma 10 58 10: the standard grading shifts integer scalar degrees by
addition. -/
local instance scalarInductionNatVAddInt : AddAction ℕ ℤ where
  vadd n z := (n : ℤ) + z
  zero_vadd := by
    intro z
    change ((0 : ℕ) : ℤ) + z = z
    simp
  add_vadd := by
    intro m n z
    change (((m + n : ℕ) : ℤ) + z) = ((m : ℤ) + ((n : ℤ) + z))
    simp [Nat.cast_add, add_assoc]

variable {k : Type u} [Field k] {d : ℕ}
variable {M : Type v} [AddCommGroup M] [Module k M]
variable [Module (MvPolynomial (Fin d) k) M] [IsScalarTower k (MvPolynomial (Fin d) k) M]

local notation "S" => MvPolynomial (Fin d) k
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin d) k

omit [IsScalarTower k S M] in
/-- Helper for Chap10 Lemma 10 58 10: projecting `a • m` to degree `d + 1` only sees the
degree-`d` scalar component of `m` when `a` has degree `1`. -/
lemma scalar_decompose_degree_succ_smul_eq
    (ℳ : ℤ → Submodule k M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    {a : S} (ha_deg : a ∈ 𝒜 1) (m : M) (d : ℤ) :
    ((DirectSum.decompose ℳ (a • m) (d + 1) : ℳ (d + 1)) : M) =
      a • ((DirectSum.decompose ℳ m d : ℳ d) : M) := by
  classical
  let g : ℤ → M := fun i ↦
    ((DirectSum.decompose ℳ (a • (((DirectSum.decompose ℳ m) i : ℳ i) : M)) (d + 1) :
        ℳ (d + 1)) : M)
  have ha_one :
      ((DirectSum.decompose 𝒜 a 1 : 𝒜 1) : S) = a := by
    -- The scalar is already homogeneous of degree `1`, so its degree-one projection is itself.
    simpa [GradedRing.proj_apply] using (DirectSum.decompose_of_mem_same 𝒜 ha_deg)
  have hsum :
      ∑ i ∈ (DirectSum.decompose ℳ m).support, g i = g d := by
    by_cases hd : d ∈ (DirectSum.decompose ℳ m).support
    · rw [Finset.sum_eq_single_of_mem d hd]
      · intro i hi hid
        have hi_ne : (1 : ℤ) + i ≠ d + 1 := by
          intro hi_eq
          have hid_eq : i = d := by
            linarith
          exact hid hid_eq
        simpa [g] using
          (scalar_directsum_component_of_homogeneous_scalar_smul_ne
            (ℳ := ℳ) (ha_e := ha_deg)
            (hm_eta := (DirectSum.decompose ℳ m i).2) hi_ne)
    · have hsum_zero :
          ∑ i ∈ (DirectSum.decompose ℳ m).support, g i = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        have hi_ne : (1 : ℤ) + i ≠ d + 1 := by
          intro hi_eq
          have : i = d := by
            linarith
          exact hd (this ▸ hi)
        simpa [g] using
          (scalar_directsum_component_of_homogeneous_scalar_smul_ne
            (ℳ := ℳ) (ha_e := ha_deg)
            (hm_eta := (DirectSum.decompose ℳ m i).2) hi_ne)
      have hd_zero : DirectSum.decompose ℳ m d = 0 := by
        simpa [DFinsupp.mem_support_iff] using hd
      have hg_zero : g d = 0 := by
        simp [g, hd_zero]
      rw [hsum_zero, hg_zero]
  have happly :
      ((((∑ i ∈ (DirectSum.decompose ℳ m).support,
            DirectSum.decompose ℳ (a • (((DirectSum.decompose ℳ m) i : ℳ i) : M))) (d + 1) :
          ℳ (d + 1)) : M)) =
        ∑ i ∈ (DirectSum.decompose ℳ m).support, g i := by
    -- Evaluate the `(d + 1)`-coordinate after pushing decomposition through the finite sum.
    simpa [g] using congrArg (fun z : ℳ (d + 1) ↦ (z : M))
      (DFinsupp.finset_sum_apply
        ((DirectSum.decompose ℳ m).support)
        (fun i ↦ DirectSum.decompose ℳ (a • (((DirectSum.decompose ℳ m) i : ℳ i) : M)))
        (d + 1))
  have hdecomp :
      ((DirectSum.decompose ℳ (a • m) (d + 1) : ℳ (d + 1)) : M) =
        ∑ i ∈ (DirectSum.decompose ℳ m).support, g i := by
    -- Expand `m` into scalar homogeneous components before applying the degree-one scalar.
    have h :=
      congrArg (fun z : M ↦ ((DirectSum.decompose ℳ (a • z) (d + 1) : ℳ (d + 1)) : M))
        (DirectSum.sum_support_decompose ℳ m)
    simpa [g, Finset.smul_sum, DirectSum.decompose_sum, happly] using h.symm
  calc
    ((DirectSum.decompose ℳ (a • m) (d + 1) : ℳ (d + 1)) : M) =
        ∑ i ∈ (DirectSum.decompose ℳ m).support, g i := hdecomp
    _ = g d := hsum
    _ = ((DirectSum.decompose 𝒜 a 1 : 𝒜 1) : S) •
          ((DirectSum.decompose ℳ m d : ℳ d) : M) := by
          -- The unique matching component is the scalar degree-one part acting on `m_d`.
          dsimp [g]
          exact
            (scalar_decompose_smul_homogeneous_generator_eq
              (ℳ := ℳ)
              (a := a)
              (m := ((DirectSum.decompose ℳ m d : ℳ d) : M))
              (hm := (DirectSum.decompose ℳ m d).2)
              (hnd := by ring))
    _ = a • ((DirectSum.decompose ℳ m d : ℳ d) : M) := by
          exact congrArg (fun b : S ↦ b • ((DirectSum.decompose ℳ m d : ℳ d) : M)) ha_one

/-- Helper for Chap10 Lemma 10 58 10: kernels of iterated multiplication by a degree-one scalar
are homogeneous for scalar graded pieces. -/
lemma scalar_degree_one_mul_kernel_pow_isHomogeneous
    (ℳ : ℤ → Submodule k M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    {a : S} (ha_deg : a ∈ 𝒜 1) (r : ℕ) :
    ((LinearMap.ker ((a • LinearMap.id : M →ₗ[S] M) ^ r)).restrictScalars k).IsHomogeneous ℳ := by
  induction r with
  | zero =>
      intro e x hx
      -- For the identity map, membership in the kernel says the element is zero.
      change (((a • LinearMap.id : M →ₗ[S] M) ^ 0) x = 0) at hx
      change (((a • LinearMap.id : M →ₗ[S] M) ^ 0)
        (((DirectSum.decompose ℳ x) e : ℳ e) : M) = 0)
      simpa [pow_zero] using congrArg (fun y : M ↦ ((DirectSum.decompose ℳ y e : ℳ e) : M)) hx
  | succ r ihr =>
      intro e x hx
      change (((a • LinearMap.id : M →ₗ[S] M) ^ (r + 1)) x = 0) at hx
      change (((a • LinearMap.id : M →ₗ[S] M) ^ (r + 1))
        (((DirectSum.decompose ℳ x) e : ℳ e) : M) = 0)
      have hax_mem :
          a • x ∈ (LinearMap.ker ((a • LinearMap.id : M →ₗ[S] M) ^ r)).restrictScalars k := by
        -- Peel off the final multiplication-by-`a` from the iterated kernel condition.
        change (((a • LinearMap.id : M →ₗ[S] M) ^ r) (a • x) = 0)
        simpa [pow_succ] using hx
      have hcomponent_mem :=
        ihr (e + 1) (m := a • x) hax_mem
      have hcomponent_zero :
          ((a • LinearMap.id : M →ₗ[S] M) ^ r)
            (a • ((DirectSum.decompose ℳ x e : ℳ e) : M)) = 0 := by
        -- Homogeneity of the lower kernel applies to the degree-`e + 1` part of `a • x`.
        change (((a • LinearMap.id : M →ₗ[S] M) ^ r)
          (((DirectSum.decompose ℳ (a • x)) (e + 1) : ℳ (e + 1)) : M) = 0) at hcomponent_mem
        rw [scalar_decompose_degree_succ_smul_eq (ℳ := ℳ) ha_deg x e] at hcomponent_mem
        exact hcomponent_mem
      -- Reinsert the final multiplication-by-`a` to obtain the successor kernel condition.
      simpa [pow_succ, LinearMap.comp_apply] using hcomponent_zero

omit [Module k M] [IsScalarTower k S M] in
/-- Helper for Chap10 Lemma 10 58 10: stabilization of the multiplication-kernel filtration
makes multiplication by the chosen degree-one scalar injective on the stabilized quotient. -/
lemma scalar_degree_one_stable_kernel_quotient_injective
    {a : S} {r : ℕ}
    (hstab :
      ⨆ m, LinearMap.ker (((a • LinearMap.id : M →ₗ[S] M) ^ m)) =
        LinearMap.ker (((a • LinearMap.id : M →ₗ[S] M) ^ r))) :
    Function.Injective
      ((a • LinearMap.id :
        M ⧸ LinearMap.ker (((a • LinearMap.id : M →ₗ[S] M) ^ r)) →ₗ[S]
          M ⧸ LinearMap.ker (((a • LinearMap.id : M →ₗ[S] M) ^ r)))) := by
  -- The injectivity step is grading-free, so reuse the owner-level kernel-filtration lemma.
  exact degree_one_stable_kernel_quotient_injective (a := a) (r := r) hstab

/-- Helper for Chap10 Lemma 10 58 10: a Noetherian scalar graded module has a stabilized
degree-one multiplication kernel that is homogeneous and gives an injective quotient action. -/
lemma scalar_degree_one_stable_kernel_package
    [IsNoetherian S M]
    (ℳ : ℤ → Submodule k M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    {a : S} (ha_deg : a ∈ 𝒜 1) :
    ∃ r : ℕ,
      ((LinearMap.ker ((a • LinearMap.id : M →ₗ[S] M) ^ r)).restrictScalars k).IsHomogeneous ℳ ∧
        Function.Injective
          ((a • LinearMap.id :
            M ⧸ LinearMap.ker (((a • LinearMap.id : M →ₗ[S] M) ^ r)) →ₗ[S]
              M ⧸ LinearMap.ker (((a • LinearMap.id : M →ₗ[S] M) ^ r)))) := by
  -- Noetherianity gives a stable kernel in the ascending chain of powers of multiplication by `a`.
  obtain ⟨r, hr⟩ :=
    Filter.eventually_atTop.mp
      (LinearMap.eventually_iSup_ker_pow_eq (f := (a • LinearMap.id : M →ₗ[S] M)))
  refine ⟨r, ?_, ?_⟩
  · -- The scalar projection formula proves homogeneity for every kernel in the filtration.
    exact scalar_degree_one_mul_kernel_pow_isHomogeneous (ℳ := ℳ) ha_deg r
  · -- The stabilized kernel equality is exactly the input for injectivity on the quotient.
    exact scalar_degree_one_stable_kernel_quotient_injective (a := a) (r := r) (hr r le_rfl)

end
