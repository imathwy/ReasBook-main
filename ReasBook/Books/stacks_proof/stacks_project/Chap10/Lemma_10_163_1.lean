import Mathlib
import StacksProject_2024.Chap10.Definition_10_72_1
import StacksProject_2024.Chap10.Lemma_10_39_12
import StacksProject_2024.Chap10.Lemma_10_72_5
import StacksProject_2024.Chap10.Lemma_10_72_7
import StacksProject_2024.Chap10.Lemma_10_99_1
import StacksProject_2024.Chap10.Lemma_10_99_4
import StacksProject_2024.Chap10.Lemma_10_63_18
import StacksProject_2024.Chap10.Lemma_10_163_1.Index

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open RingTheory Sequence Ideal IsLocalRing
open TensorProduct.AlgebraTensorModule
open scoped TensorProduct Pointwise

universe u v w x uA uP

section

variable {R : Type u} {S : Type v} {M : Type w} {N : Type x}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
variable [Module.Finite S N] [Module.Flat R N]

local notation "𝔪S" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S
local notation "ClosedFiberModule" => ClosedFiber ⊗[S] N

/- Domain-style sampling pass:
* primary domain: local commutative algebra of depth for finite modules under flat local base
  change, with the closed fiber carried by the canonical fiber-ring owner;
* sampled owner declarations:
  `moduleDepth`,
  `Ideal.Fiber`,
  `Module.Finite.base_change`,
  `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`;
* best owner abstraction: the right-hand side belongs on the canonical local depth
  `moduleDepth ClosedFiber ClosedFiberModule`, where
  `ClosedFiber = Ideal.Fiber (maximalIdeal R) S` and
  `ClosedFiberModule = ClosedFiber ⊗[S] N`; the quotient module
  `N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N))` is only a bridge.

Primitive data vs. derived API:
* primitive data: the local flat map `R → S`, the finite `R`-module `M`, and the finite
  `S`-module `N` that is flat over `R`;
* derived API: the quotient presentation of the closed fiber and of the closed-fiber module.

Source/core/bridge triage:
* `source-facing`: the Stacks additivity formula for depth under flat local base change;
* `core/canonical`: `moduleDepth` on the owner ring/module pair `ClosedFiber` and
  `ClosedFiberModule`;
* `bridge/view`: the quotient presentation `S ⧸ 𝔪S` and
  `N ⧸ (𝔪S • (⊤ : Submodule S N))`.
-/

/-- Helper for Chap10 Lemma 10 163 1: if quotienting by a maximal-ideal regular element has finite
depth `n`, then the original module has depth `n + 1`. -/
private lemma moduleDepth_eq_succ_of_quotSMulTop_eq_of_regular
    {A : Type uA} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {P : Type uP} [AddCommGroup P] [Module A P] [Module.Finite A P] {x : A}
    (hreg : IsSMulRegular P x) (hx : x ∈ maximalIdeal A) {n : ℕ}
    (hquot : moduleDepth A (QuotSMulTop x P) = n) :
    moduleDepth A P = n + 1 := by
  by_cases hP : Subsingleton P
  · letI : Subsingleton P := hP
    letI : Subsingleton (QuotSMulTop x P) := by infer_instance
    have htop : moduleDepth A (QuotSMulTop x P) = ⊤ :=
      moduleDepth_eq_top_of_subsingleton_for_entry (A := A) (P := QuotSMulTop x P)
    have hn_top : (n : ℕ∞) = ⊤ := by
      simpa [hquot] using htop
    exact False.elim ((ENat.coe_ne_top (a := n)) hn_top)
  · letI : Nontrivial P := not_subsingleton_iff_nontrivial.mp hP
    obtain ⟨m, hm⟩ :=
      exists_nat_moduleDepth_of_nontrivial_finite_for_entry (A := A) (P := P)
    have hdrop : moduleDepth A (QuotSMulTop x P) = moduleDepth A P - 1 :=
      moduleDepth_quotSMulTop_eq_sub_one_univ (A := A) (P := P) hreg hx
    have hone : (1 : ℕ∞) ≤ moduleDepth A P :=
      one_le_moduleDepth_of_mem_maximalIdeal_of_isSMulRegular_for_entry
        (A := A) (P := P) hx hreg
    have hmpos : 0 < m := by
      rw [hm] at hone
      exact_mod_cast hone
    have hn_eq : n = m - 1 := by
      -- Proof comment: compare the finite quotient depth with the standard depth-drop identity.
      have hnat : (n : ℕ∞) = (m : ℕ∞) - 1 := by
        rw [← hquot, hdrop, hm]
      exact_mod_cast hnat
    have hm_eq : m = n + 1 := by omega
    -- Proof comment: the predecessor comparison and positivity recover the original depth.
    simpa [hm_eq] using hm

/-- Helper for Chap10 Lemma 10 163 1: a positive closed-fiber depth yields a lift in `maximalIdeal S`
that is regular on the closed-fiber module, regular on `N'`, and has flat quotient over `R`. -/
private lemma exists_lift_closedFiber_regular_of_moduleDepth_pos
    {N' : Type x} [AddCommGroup N'] [Module S N'] [Module R N'] [IsScalarTower R S N']
    [Module.Finite S N'] [Module.Flat R N'] {b : ℕ}
    (hCF : moduleDepth ClosedFiber (ClosedFiber ⊗[S] N') = b) (hbpos : 0 < b) :
    ∃ f : S,
      f ∈ maximalIdeal S ∧
        IsSMulRegular (ClosedFiber ⊗[S] N') (algebraMap S ClosedFiber f) ∧
          IsSMulRegular N' f ∧ Module.Flat R (QuotSMulTop f N') := by
  letI : Nontrivial (ClosedFiber ⊗[S] N') :=
    nontrivial_of_moduleDepth_eq_nat_for_entry
      (A := ClosedFiber) (P := ClosedFiber ⊗[S] N') hCF
  have hCF_ne_zero : moduleDepth ClosedFiber (ClosedFiber ⊗[S] N') ≠ 0 := by
    intro hzero
    have hb_zero : b = 0 := by
      exact_mod_cast (hCF.symm.trans hzero)
    omega
  rcases exists_mem_maximalIdeal_isSMulRegular_of_moduleDepth_ne_zero_for_entry
      (A := ClosedFiber) (P := ClosedFiber ⊗[S] N') hCF_ne_zero with
    ⟨y, hy, hyreg⟩
  letI : IsLocalHom (algebraMap S ClosedFiber) :=
    IsLocalHom.of_surjective (algebraMap S ClosedFiber)
      (closedFiber_algebraMap_surjective (R := R) (S := S))
  rcases closedFiber_algebraMap_surjective (R := R) (S := S) y with ⟨f, hfmap⟩
  have hf : f ∈ maximalIdeal S := by
    have hcomap :
        Ideal.comap (algebraMap S ClosedFiber) (maximalIdeal ClosedFiber) =
          maximalIdeal S :=
      IsLocalRing.maximalIdeal_comap (algebraMap S ClosedFiber)
    have hfpre :
        f ∈ Ideal.comap (algebraMap S ClosedFiber) (maximalIdeal ClosedFiber) := by
      simpa [hfmap] using hy
    simpa [hcomap] using hfpre
  have hfregCF : IsSMulRegular (ClosedFiber ⊗[S] N') (algebraMap S ClosedFiber f) := by
    simpa [hfmap] using hyreg
  have hNF := lift_closed_fiber_regular_element (R := R) (S := S) (N := N') hfregCF
  -- Proof comment: the flatness and regularity on `N'` are exactly the lifting theorem output.
  exact ⟨f, hf, hfregCF, hNF.1, hNF.2⟩

/-- Helper for Chap10 Lemma 10 163 1: the source-positive and closed-fiber-zero branch of the bounded
depth-sum induction proceeds by quotienting `M'` by a source regular element. -/
private lemma depth_tensor_additivity_source_step
    (n : ℕ)
    (ih :
      ∀ {M'' : Type w} [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
        {N'' : Type x} [AddCommGroup N''] [Module S N''] [Module R N'']
        [IsScalarTower R S N''] [Module.Finite S N''] [Module.Flat R N'']
        {a' b' : ℕ},
        a' + b' ≤ n →
          moduleDepth R M'' = a' →
          moduleDepth ClosedFiber (ClosedFiber ⊗[S] N'') = b' →
          moduleDepth S (N'' ⊗[R] M'') = a' + b')
    {M' : Type w} [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    {N' : Type x} [AddCommGroup N'] [Module S N'] [Module R N'] [IsScalarTower R S N']
    [Module.Finite S N'] [Module.Flat R N'] {a b : ℕ}
    (hsum : a + b ≤ n + 1)
    (hM : moduleDepth R M' = a)
    (hCF : moduleDepth ClosedFiber (ClosedFiber ⊗[S] N') = b)
    (hb0 : b = 0)
    (hapos : 0 < a) :
    moduleDepth S (N' ⊗[R] M') = a + b := by
  letI : Nontrivial M' :=
    nontrivial_of_moduleDepth_eq_nat_for_entry (A := R) (P := M') hM
  have hM_ne_zero : moduleDepth R M' ≠ 0 := by
    intro hzero
    have ha_zero : a = 0 := by
      exact_mod_cast (hM.symm.trans hzero)
    omega
  rcases exists_mem_maximalIdeal_isSMulRegular_of_moduleDepth_ne_zero_for_entry
      (A := R) (P := M') hM_ne_zero with
    ⟨r, hr, hrreg⟩
  have hrS : algebraMap R S r ∈ maximalIdeal S :=
    (IsLocalRing.map_maximalIdeal_le (algebraMap R S))
      (Ideal.mem_map_of_mem (algebraMap R S) hr)
  have hregTensor : IsSMulRegular (N' ⊗[R] M') (algebraMap R S r) :=
    source_regular_on_tensor (R := R) (S := S) (M := M') (N := N') hrreg
  have hMq : moduleDepth R (QuotSMulTop r M') = a - 1 := by
    -- Proof comment: the quotient source depth is the predecessor of the given source depth.
    have hdrop : moduleDepth R (QuotSMulTop r M') = moduleDepth R M' - 1 :=
      moduleDepth_quotSMulTop_eq_sub_one_univ (A := R) (P := M') hrreg hr
    simpa [hM, ENat.coe_sub] using hdrop
  have hsum' : (a - 1) + b ≤ n := by omega
  have hrec : moduleDepth S (N' ⊗[R] QuotSMulTop r M') = (a - 1) + b :=
    ih (M'' := QuotSMulTop r M') (N'' := N') hsum' hMq hCF
  have hquotTensor :
      moduleDepth S (QuotSMulTop (algebraMap R S r) (N' ⊗[R] M')) =
        (a - 1) + b := by
    -- Proof comment: transport the recursive quotient depth across the source tensor-quotient
    -- comparison.
    have htransport :=
      moduleDepth_eq_of_linearEquiv
        (A := S) (e := tensor_quotient_by_source_element (R := R) (S := S)
          (M := M') (N := N') r)
    rw [htransport]
    exact hrec
  have hrecover :=
    moduleDepth_eq_succ_of_quotSMulTop_eq_of_regular
      (A := S) (P := N' ⊗[R] M') hregTensor hrS hquotTensor
  have hNat : (a - 1 + b) + 1 = a + b := by omega
  -- Proof comment: invert the tensor depth drop and simplify the predecessor arithmetic.
  exact hrecover.trans (by exact_mod_cast hNat)

/-- Helper for Chap10 Lemma 10 163 1: the target-positive branch of the bounded induction proceeds by
quotienting `N'` by a lift of a closed-fiber regular element. -/
private lemma depth_tensor_additivity_target_step
    (n : ℕ)
    (ih :
      ∀ {M'' : Type w} [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
        {N'' : Type x} [AddCommGroup N''] [Module S N''] [Module R N'']
        [IsScalarTower R S N''] [Module.Finite S N''] [Module.Flat R N'']
        {a' b' : ℕ},
        a' + b' ≤ n →
          moduleDepth R M'' = a' →
          moduleDepth ClosedFiber (ClosedFiber ⊗[S] N'') = b' →
          moduleDepth S (N'' ⊗[R] M'') = a' + b')
    {M' : Type w} [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    {N' : Type x} [AddCommGroup N'] [Module S N'] [Module R N'] [IsScalarTower R S N']
    [Module.Finite S N'] [Module.Flat R N'] {a b : ℕ}
    (hsum : a + b ≤ n + 1)
    (hM : moduleDepth R M' = a)
    (hCF : moduleDepth ClosedFiber (ClosedFiber ⊗[S] N') = b)
    (hbpos : 0 < b) :
    moduleDepth S (N' ⊗[R] M') = a + b := by
  rcases exists_lift_closedFiber_regular_of_moduleDepth_pos
      (R := R) (S := S) (N' := N') hCF hbpos with
    ⟨f, hf, hfregCF, hfregN, hflat⟩
  letI : Module.Flat R (QuotSMulTop f N') := hflat
  have hCFq : moduleDepth ClosedFiber (ClosedFiber ⊗[S] QuotSMulTop f N') = b - 1 := by
    -- Proof comment: quotienting by the lifted closed-fiber regular element drops the
    -- closed-fiber depth by one.
    have hdrop :=
      closed_fiber_depth_after_target_quotient
        (R := R) (S := S) (N' := N') hf hfregCF
    simpa [hCF, ENat.coe_sub] using hdrop
  have hsum' : a + (b - 1) ≤ n := by omega
  have hrec : moduleDepth S (QuotSMulTop f N' ⊗[R] M') = a + (b - 1) :=
    ih (M'' := M') (N'' := QuotSMulTop f N') hsum' hM hCFq
  have hquotTensor :
      moduleDepth S (QuotSMulTop f (N' ⊗[R] M')) = a + (b - 1) := by
    -- Proof comment: transport the recursive target-quotient tensor depth back to the quotient
    -- of the original tensor product.
    have htransport :=
      moduleDepth_eq_of_linearEquiv
        (A := S) (e := tensor_quotient_by_target_element (R := R) (S := S)
          (M' := M') (N' := N') f)
    rw [htransport]
    exact hrec
  have hregTensor : IsSMulRegular (N' ⊗[R] M') f :=
    target_regular_on_tensor (R := R) (S := S) (M' := M') (N' := N') hfregN hflat
  have hrecover :=
    moduleDepth_eq_succ_of_quotSMulTop_eq_of_regular
      (A := S) (P := N' ⊗[R] M') hregTensor hf hquotTensor
  have hNat : (a + (b - 1)) + 1 = a + b := by omega
  -- Proof comment: invert the tensor depth drop and simplify the target predecessor arithmetic.
  exact hrecover.trans (by exact_mod_cast hNat)

/-- Chap10 Lemma 10 163 1: bounded induction on the natural depth sum proves the tensor-depth
additivity formula for every recursive pair with sum at most `n`. -/
private theorem depth_tensor_additivity_up_to_sum
    (n : ℕ)
    {M' : Type w} [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    {N' : Type x} [AddCommGroup N'] [Module S N'] [Module R N'] [IsScalarTower R S N']
    [Module.Finite S N'] [Module.Flat R N'] {a b : ℕ}
    (hsum : a + b ≤ n)
    (hM : moduleDepth R M' = a)
    (hCF : moduleDepth ClosedFiber (ClosedFiber ⊗[S] N') = b) :
    moduleDepth S (N' ⊗[R] M') = a + b := by
  induction n generalizing M' N' a b with
  | zero =>
      have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      have hM0 : moduleDepth R M' = 0 := by
        simpa [ha0] using hM
      have hCF0 : moduleDepth ClosedFiber (ClosedFiber ⊗[S] N') = 0 := by
        simpa [hb0] using hCF
      have hbase : moduleDepth S (N' ⊗[R] M') = 0 :=
        depth_zero_tensor_of_depth_zero_closed_fiber_generic
          (R := R) (S := S) (M' := M') (N' := N') hM0 hCF0
      -- Proof comment: sum zero forces both component depths to be zero, so the base theorem
      -- applies directly.
      simpa [ha0, hb0] using hbase
  | succ n ih =>
      by_cases hbpos : 0 < b
      · exact
          depth_tensor_additivity_target_step
            (R := R) (S := S) (n := n) ih hsum hM hCF hbpos
      · have hb0 : b = 0 := by omega
        by_cases hapos : 0 < a
        · exact
            depth_tensor_additivity_source_step
              (R := R) (S := S) (n := n) ih hsum hM hCF hb0 hapos
        · have ha0 : a = 0 := by omega
          have hM0 : moduleDepth R M' = 0 := by
            simpa [ha0] using hM
          have hCF0 : moduleDepth ClosedFiber (ClosedFiber ⊗[S] N') = 0 := by
            simpa [hb0] using hCF
          have hbase : moduleDepth S (N' ⊗[R] M') = 0 :=
            depth_zero_tensor_of_depth_zero_closed_fiber_generic
              (R := R) (S := S) (M' := M') (N' := N') hM0 hCF0
          -- Proof comment: if neither side has positive depth, the successor case also reduces
          -- to the depth-zero base theorem.
          simpa [ha0, hb0] using hbase

/-- Helper for Chap10 Lemma 10 163 1: once the two depths are represented by natural numbers, the source
proof proceeds by strong induction on their sum. -/
private theorem depth_tensor_additivity_of_nat_depth_sum
    {M' : Type w} [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    {N' : Type x} [AddCommGroup N'] [Module S N'] [Module R N'] [IsScalarTower R S N']
    [Module.Finite S N'] [Module.Flat R N'] {a b : ℕ}
    (hM : moduleDepth R M' = a)
    (hCF : moduleDepth ClosedFiber (ClosedFiber ⊗[S] N') = b) :
    moduleDepth S (N' ⊗[R] M') = a + b := by
  -- Route correction: the direct strong induction over the full parameter pack repeatedly
  -- reintroduced large quotient transports at the recursive call site. The stable route is the
  -- bounded predicate `depth_tensor_additivity_up_to_sum`, which names the quotient modules
  -- before recursion and then specializes at `n = a + b`.
  exact
    depth_tensor_additivity_up_to_sum
      (R := R) (S := S) (n := a + b) (M' := M') (N' := N')
      (a := a) (b := b) le_rfl hM hCF

omit [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite R M]
  [IsScalarTower R S N] [Module.Flat R N] in
/-- Helper for Chap10 Lemma 10 163 1: if the canonical closed-fiber module is trivial, then the tensor
product is trivial as well. -/
private lemma subsingleton_tensor_of_subsingleton_closed_fiber_module
    [Subsingleton ClosedFiberModule] :
    Subsingleton (N ⊗[R] M) := by
  let e := closed_fiber_module_quotient_equiv (R := R) (S := S) (M := N)
  have hquot_sub :
      Subsingleton (N ⧸ (𝔪S • (⊤ : Submodule S N))) := by
    refine ⟨fun x y => ?_⟩
    simpa using congrArg e (Subsingleton.elim (e.symm x) (e.symm y))
  have hsmul_top : 𝔪S • (⊤ : Submodule S N) = ⊤ := by
    exact (Submodule.Quotient.subsingleton_iff).mp hquot_sub
  have hIjac : 𝔪S ≤ Ring.jacobson S := by
    exact
      (IsLocalRing.map_maximalIdeal_le (algebraMap R S)).trans
        (by simpa [Ideal.jacobson_bot] using
          (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal S)))
  letI : Subsingleton N :=
    subsingleton_of_ideal_smul_top_eq_top_of_le_ring_jacobson
      (R := S) (M := N) (I := 𝔪S) hsmul_top hIjac
  -- Proof comment: once `N` is zero, the tensor product is zero by the generic tensor instance.
  infer_instance

/-- Helper for Chap10 Lemma 10 163 1: in the nontrivial branch, the theorem is exactly the natural-depth
induction statement specialized to the ambient pair `(M, N)`. -/
private lemma depth_tensor_of_nontrivial_modules
    [Nontrivial M] [Nontrivial ClosedFiberModule] :
    moduleDepth S (N ⊗[R] M) =
      moduleDepth R M + moduleDepth ClosedFiber ClosedFiberModule := by
  obtain ⟨a, ha⟩ :=
    exists_nat_moduleDepth_of_nontrivial_finite_for_entry
      (A := R) (P := M)
  obtain ⟨b, hb⟩ :=
    exists_nat_moduleDepth_of_nontrivial_finite_for_entry
      (A := ClosedFiber) (P := ClosedFiberModule)
  -- Proof comment: the natural-depth induction theorem now applies verbatim to the ambient
  -- source module `M` and target module `N`.
  calc
    moduleDepth S (N ⊗[R] M) = a + b :=
      depth_tensor_additivity_of_nat_depth_sum
        (R := R) (S := S) (M' := M) (N' := N) ha hb
    _ = moduleDepth R M + moduleDepth ClosedFiber ClosedFiberModule := by
          simpa [ha, hb]

-- Proof sketch: argue by induction on the sum of the two depths. If the closed fiber has positive
-- depth, choose a nonzerodivisor in the maximal ideal of `S` on the closed fiber, use the flat
-- lifting lemma to show it is a nonzerodivisor on `N`, reduce to `N / fN`, and apply the depth
-- drop lemma. If the closed fiber has depth zero but the sum is positive, choose a
-- nonzerodivisor in the maximal ideal of `R` on `M`, use flatness of `N` to keep it regular on
-- the tensor product, pass to `M / xM`, and conclude by induction.
/-- Consequence for Chap10 Lemma 10 163 1: for a flat local homomorphism `R → S` of Noetherian local rings, a finite
`R`-module `M`, and a finite `S`-module `N` that is flat over `R`, the local depth of the tensor
product equals the local depth of `M` plus the local depth of the canonical closed-fiber module
`ClosedFiberModule = ((maximalIdeal R).Fiber S) ⊗[S] N`, equivalently
`N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N))`, over the canonical
closed-fiber ring `ClosedFiber = (maximalIdeal R).Fiber S`, equivalently
`S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`. -/
@[stacks 0338]
theorem depth_tensorProduct_eq_depth_add_depth_closedFiber :
    moduleDepth S (N ⊗[R] M) =
      moduleDepth R M + moduleDepth ClosedFiber ClosedFiberModule := by
  by_cases hM : Subsingleton M
  · letI : Subsingleton M := hM
    letI : Subsingleton (N ⊗[R] M) := by infer_instance
    -- Proof comment: if `M` is zero, then both the source depth and the tensor-product depth are
    -- infinite, so the formula is immediate.
    rw [moduleDepth_eq_top_of_subsingleton_for_entry (A := S) (P := N ⊗[R] M),
      moduleDepth_eq_top_of_subsingleton_for_entry (A := R) (P := M)]
    simp
  · letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
    by_cases hCF : Subsingleton ClosedFiberModule
    · letI : Subsingleton ClosedFiberModule := hCF
      letI : Subsingleton (N ⊗[R] M) :=
        subsingleton_tensor_of_subsingleton_closed_fiber_module
          (R := R) (S := S) (M := M) (N := N)
      -- Proof comment: a zero closed fiber forces `N = 0` by Nakayama, hence the tensor product
      -- is also zero and both sides have infinite depth.
      rw [moduleDepth_eq_top_of_subsingleton_for_entry (A := S) (P := N ⊗[R] M),
        moduleDepth_eq_top_of_subsingleton_for_entry
          (A := ClosedFiber) (P := ClosedFiberModule)]
      simp
    · letI : Nontrivial ClosedFiberModule := not_subsingleton_iff_nontrivial.mp hCF
      -- Proof comment: once both modules are nontrivial, the theorem is exactly the natural-depth
      -- additivity statement proved above by strong induction.
      exact depth_tensor_of_nontrivial_modules (R := R) (S := S) (M := M) (N := N)

end
