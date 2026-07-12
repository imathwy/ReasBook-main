import Mathlib
import StacksProject_2024.Chap10.Lemma_10_55_6
import StacksProject_2024.Chap10.Definition_10_58_3
import StacksProject_2024.Chap10.Lemma_10_56_1
import StacksProject_2024.Chap10.Lemma_10_58_4
import StacksProject_2024.Chap10.Lemma_10_58_2
import StacksProject_2024.Chap10.Lemma_10_58_6


-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open CategoryTheory
open CategoryTheory.ShortComplex.ShortExact
open HomogeneousIdeal

section

/-- Helper for Chap10 Proposition 10 58 7: the integer grading carries the natural degree-shift
action by `ℕ`. -/
local instance instAddActionNatIntDegreeOneKernels10587 : AddAction ℕ ℤ where
  vadd n d := (n : ℤ) + d
  zero_vadd := by
    intro d
    change ((0 : ℕ) : ℤ) + d = d
    simp
  add_vadd := by
    intro m n d
    change (((m + n : ℕ) : ℤ) + d) = (m : ℤ) + ((n : ℤ) + d)
    simp [Nat.cast_add, add_assoc]

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜]
variable [IsNoetherianRing S]

/-- Helper for Proposition 10.58.7: projecting `a • m` to degree `d + 1` only sees the degree-`d`
component of `m` when `a` is homogeneous of degree `1`. -/
lemma decompose_degree_succ_smul_eq
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
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
    -- The chosen scalar is already homogeneous of degree `1`, so its degree-`1` component is
    -- itself.
    simpa [GradedRing.proj_apply] using (DirectSum.decompose_of_mem_same 𝒜 ha_deg)
  have hsum :
      ∑ i ∈ (DirectSum.decompose ℳ m).support, g i = g d := by
    by_cases hd : d ∈ (DirectSum.decompose ℳ m).support
    · rw [Finset.sum_eq_single_of_mem d hd]
      · intro i hi hid
        -- Off the matching degree, a degree-one scalar lands in the wrong graded piece.
        have hi_ne : (1 : ℤ) + i ≠ d + 1 := by
          intro hi_eq
          have hid_eq : i = d := by linarith
          exact hid hid_eq
        simpa [g] using
          (directsum_component_of_homogeneous_scalar_smul_ne
            (𝒜 := 𝒜) (ℳ := ℳ) (ha_d := ha_deg)
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
          (directsum_component_of_homogeneous_scalar_smul_ne
            (𝒜 := 𝒜) (ℳ := ℳ) (ha_d := ha_deg)
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
    -- Evaluate the `(d + 1)`-coordinate after pushing `DirectSum.decompose` through the finite sum.
    simpa [g] using congrArg (fun z : ℳ (d + 1) ↦ (z : M))
      (DFinsupp.finset_sum_apply
        ((DirectSum.decompose ℳ m).support)
        (fun i ↦ DirectSum.decompose ℳ (a • (((DirectSum.decompose ℳ m) i : ℳ i) : M)))
        (d + 1))
  have hdecomp :
      ((DirectSum.decompose ℳ (a • m) (d + 1) : ℳ (d + 1)) : M) =
        ∑ i ∈ (DirectSum.decompose ℳ m).support, g i := by
    -- First expand `m` into homogeneous pieces, then project the scalar action termwise.
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
          -- On the unique matching degree, the one-step shift is exactly the homogeneous action.
          simpa [g] using
            (decompose_smul_homogeneous_generator_eq
              (𝒜 := 𝒜) (ℳ := ℳ)
              (a := a)
              (m := ((DirectSum.decompose ℳ m d : ℳ d) : M))
              (hm := (DirectSum.decompose ℳ m d).2)
              (hnd := by simpa [add_comm]))
    _ = a • ((DirectSum.decompose ℳ m d : ℳ d) : M) := by rw [ha_one]

/-- Helper for Proposition 10.58.7: every homogeneous element of `(a)M` comes from a homogeneous
preimage one degree lower. -/
lemma exists_homogeneous_preimage_of_mem_smul_top
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    {a : S} (ha_deg : a ∈ 𝒜 1)
    {e : ℤ} {z : M} (hz_deg : z ∈ ℳ e)
    (hzN : z ∈ ((Ideal.span ({a} : Set S)) • (⊤ : Submodule S M))) :
    ∃ y : ℳ (e - 1), a • (y : M) = z := by
  rw [Submodule.ideal_span_singleton_smul] at hzN
  rw [Submodule.mem_smul_pointwise_iff_exists] at hzN
  rcases hzN with ⟨m, -, rfl⟩
  refine ⟨DirectSum.decompose ℳ m (e - 1), ?_⟩
  -- The degree-`e` component of `a • m` is controlled by the degree-`e - 1` component of `m`.
  calc
    a • ((DirectSum.decompose ℳ m (e - 1) : ℳ (e - 1)) : M) =
        ((DirectSum.decompose ℳ (a • m) ((e - 1) + 1) : ℳ ((e - 1) + 1)) : M) := by
          symm
          exact decompose_degree_succ_smul_eq (𝒜 := 𝒜) (ℳ := ℳ) ha_deg m (e - 1)
    _ = ((DirectSum.decompose ℳ (a • m) e : ℳ e) : M) := by
          have he_shift : (e - 1) + 1 = e := by linarith
          rw [he_shift]
    _ = a • m := by
          simpa using (DirectSum.decompose_of_mem_same ℳ hz_deg)

/-- Helper for Proposition 10.58.7: the submodule `(a)M` is homogeneous when `a` has degree `1`.
-/
lemma degree_one_smul_top_isHomogeneous
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    {a : S} (ha_deg : a ∈ 𝒜 1) :
    (((Ideal.span ({a} : Set S)) • (⊤ : Submodule S M)) : Submodule S M).IsHomogeneous ℳ := by
  intro n z hzN
  rw [Submodule.ideal_span_singleton_smul] at hzN ⊢
  rw [Submodule.mem_smul_pointwise_iff_exists] at hzN ⊢
  rcases hzN with ⟨m, -, rfl⟩
  refine ⟨((DirectSum.decompose ℳ m (n - 1) : ℳ (n - 1)) : M), by simp, ?_⟩
  -- Projecting `a • m` to degree `n` keeps it inside the principal image `aM`.
  symm
  have hn_shift : (n - 1) + 1 = n := by linarith
  have hshifted :=
    decompose_degree_succ_smul_eq (𝒜 := 𝒜) (ℳ := ℳ) ha_deg m (n - 1)
  rw [hn_shift] at hshifted
  exact hshifted

/-- Helper for Proposition 10.58.7: iterating multiplication by `a` on a module is the same as
multiplication by the scalar power `a ^ r`. -/
lemma smul_linearMap_pow_eq_pow_smul_id
    {M : Type w} [AddCommGroup M] [Module S M]
    (a : S) (r : ℕ) :
    ((a • LinearMap.id : M →ₗ[S] M) ^ r) = (a ^ r) • LinearMap.id := by
  induction r with
  | zero =>
      -- Both zero-th powers are the identity endomorphism.
      ext m
      simp
  | succ r ihr =>
      -- Compose one more multiplication-by-`a` step and collapse the scalar action.
      ext m
      simp [pow_succ, ihr, smul_smul, mul_comm]

/-- Helper for Proposition 10.58.7: the kernels of the iterated multiplication maps by a
degree-one element are homogeneous submodules. -/
lemma degree_one_mul_kernel_pow_isHomogeneous
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    {a : S} (ha_deg : a ∈ 𝒜 1) (r : ℕ) :
    (LinearMap.ker ((a • LinearMap.id : M →ₗ[S] M) ^ r)).IsHomogeneous ℳ := by
  induction r with
  | zero =>
      intro d x hx
      -- For the identity map, membership in the kernel means the element is already zero.
      rw [LinearMap.mem_ker] at hx ⊢
      simpa [pow_zero] using congrArg (fun y : M ↦ ((DirectSum.decompose ℳ y d : ℳ d) : M)) hx
  | succ r ihr =>
      intro d x hx
      rw [LinearMap.mem_ker] at hx ⊢
      have hax_mem :
          a • x ∈ LinearMap.ker ((a • LinearMap.id : M →ₗ[S] M) ^ r) := by
        -- Peel off one multiplication-by-`a` step from the iterated kernel condition.
        rw [LinearMap.mem_ker]
        simpa [pow_succ] using hx
      have hcomponent_mem :=
        ihr (d + 1) (m := a • x) hax_mem
      have hcomponent_zero :
          ((a • LinearMap.id : M →ₗ[S] M) ^ r)
            (a • ((DirectSum.decompose ℳ x d : ℳ d) : M)) = 0 := by
        -- Apply the induction hypothesis to the degree-`d + 1` component of `a • x`.
        rw [LinearMap.mem_ker] at hcomponent_mem
        rw [decompose_degree_succ_smul_eq (𝒜 := 𝒜) (ℳ := ℳ) ha_deg x d] at hcomponent_mem
        exact hcomponent_mem
      -- Reinsert the final multiplication-by-`a` to recover the `(r + 1)`-st kernel.
      simpa [pow_succ] using hcomponent_zero

/-- Helper for Chap10 Proposition 10 58 7: the `a`-torsion submodule is homogeneous when `a` is
homogeneous of degree `1`. -/
lemma degree_one_torsionBy_isHomogeneous
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    {a : S} (ha_deg : a ∈ 𝒜 1) :
    (Submodule.torsionBy S M a).IsHomogeneous ℳ := by
  -- `torsionBy` is the kernel of multiplication by `a`, which is the first kernel in the
  -- homogeneous kernel filtration proved above.
  simpa [Submodule.torsionBy] using
    (degree_one_mul_kernel_pow_isHomogeneous (𝒜 := 𝒜) (ℳ := ℳ) ha_deg 1)

/-- Helper for Proposition 10.58.7: once the kernel filtration of multiplication by `a`
stabilizes, multiplication by `a` is injective on the quotient by the stabilized kernel. -/
lemma degree_one_stable_kernel_quotient_injective
    {M : Type w} [AddCommGroup M] [Module S M]
    {a : S} {r : ℕ}
    (hstab :
      ⨆ m, LinearMap.ker (((a • LinearMap.id : M →ₗ[S] M) ^ m)) =
        LinearMap.ker (((a • LinearMap.id : M →ₗ[S] M) ^ r))) :
    Function.Injective
      ((a • LinearMap.id :
        M ⧸ LinearMap.ker (((a • LinearMap.id : M →ₗ[S] M) ^ r)) →ₗ[S]
          M ⧸ LinearMap.ker (((a • LinearMap.id : M →ₗ[S] M) ^ r)))) := by
  have hzero :
      ∀ q :
        M ⧸ LinearMap.ker (((a • LinearMap.id : M →ₗ[S] M) ^ r)),
        a • q = 0 → q = 0 := by
    intro q hq_zero
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
      (LinearMap.ker (((a • LinearMap.id : M →ₗ[S] M) ^ r))) q
    change
      (LinearMap.ker (((a • LinearMap.id : M →ₗ[S] M) ^ r))).mkQ x = 0
    have hax_mem :
        a • x ∈ LinearMap.ker (((a • LinearMap.id : M →ₗ[S] M) ^ r)) := by
      -- Vanishing in the quotient means the representative already maps into the stabilized
      -- kernel.
      change
        (LinearMap.ker (((a • LinearMap.id : M →ₗ[S] M) ^ r))).mkQ (a • x) = 0 at hq_zero
      exact (Submodule.Quotient.mk_eq_zero _).1 hq_zero
    have hx_pow :
        x ∈ LinearMap.ker (((a • LinearMap.id : M →ₗ[S] M) ^ (r + 1))) := by
      -- Membership of `a • x` in the `r`-th kernel is exactly the `(r + 1)`-st kernel condition.
      rw [LinearMap.mem_ker]
      rw [LinearMap.mem_ker] at hax_mem
      simpa [pow_succ] using hax_mem
    have hx_iSup :
        x ∈ ⨆ m, LinearMap.ker (((a • LinearMap.id : M →ₗ[S] M) ^ m)) :=
      (le_iSup (fun m ↦ LinearMap.ker (((a • LinearMap.id : M →ₗ[S] M) ^ m))) (r + 1)) hx_pow
    have hx_mem :
        x ∈ LinearMap.ker (((a • LinearMap.id : M →ₗ[S] M) ^ r)) := by
      rw [← hstab]
      exact hx_iSup
    exact (Submodule.Quotient.mk_eq_zero _).2 hx_mem
  -- Reduce injectivity to the claim that only the zero quotient element is killed by `a`.
  intro q₁ q₂ hq
  apply sub_eq_zero.mp
  exact hzero (q₁ - q₂) (by
    simpa [smul_sub] using sub_eq_zero.mpr hq)


end
