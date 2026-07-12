import Mathlib

open LinearMap TensorProduct MulOpposite
open scoped TensorProduct

attribute [local instance] TensorProduct.Algebra.module

universe u v w

section

variable {k : Type u} {K : Type v} {V : Type w}
variable [Field k] [DivisionRing K] [Algebra k K]
variable [AddCommGroup V] [Module k V]

/- Domain triage:
- primary domain: tensor products and submodules with commuting left/right scalar actions over a
  `k`-algebra `K`.
- sampled owner declarations: `Subbimodule.toSubmodule`, `Submodule.baseChange`,
  `Submodule.baseChange_eq_span`, `Submodule.map_comap_eq`.
- `source-facing`: a `k`-submodule of `V ⊗[k] K` stable under left and right multiplication on the
  `K`-factor, viewed through the canonical factor-swap `TensorProduct.comm k V K`.
- `core/canonical`: after commuting factors, a `K`-`K` subbimodule
  `W : Submodule (K ⊗[k] Kᵐᵒᵖ) (K ⊗[k] V)`.
- `bridge/view`: the corresponding `K`-submodule `Subbimodule.toSubmodule W` and its source-model
  transport back to `V ⊗[k] K`.

Primitive data vs derived API:
- primitive owner data: the ambient `K`-`K` subbimodule on `K ⊗[k] V`, and the source-facing
  `k`-submodule together with its left/right stability data;
- derived/source-facing data: the underlying left `K`-submodule, together with the corresponding
  generation/base change descriptions in the two tensor models.
-/

/-- Right multiplication on the `K`-factor of `K ⊗[k] V` is the canonical `Kᵐᵒᵖ`-action coming
from the first tensor factor. -/
@[simp] theorem op_smul_eq_rTensor_mulRight (a : K) (x : K ⊗[k] V) :
    op a • x = (((mulRight k a).rTensor V) : K ⊗[k] V →ₗ[k] K ⊗[k] V) x := by
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul b v =>
      simp [TensorProduct.smul_tmul']
  | add x y hx hy =>
      simp [hx, hy]

section TwoSidedSubmodule

/-- Helper for Chap11 Lemma 11 4 3: the canonical `Kᵐᵒᵖ`-action on `K ⊗[k] V` multiplies each
basis coordinate on the right. -/
lemma equivFinsuppOfBasisRight_op_smul
    {ι : Type*} [DecidableEq ι] (b : Module.Basis ι k V) (a : K) (x : K ⊗[k] V) :
    TensorProduct.equivFinsuppOfBasisRight b (op a • x) =
      Finsupp.mapRange (fun z : K ↦ z * a) (by simp) (TensorProduct.equivFinsuppOfBasisRight b x) := by
  -- Compare the two coordinate descriptions on pure tensors and extend by additivity.
  induction x using TensorProduct.induction_on with
  | zero =>
      ext i
      simp
  | tmul c v =>
      ext i
      simp [TensorProduct.smul_tmul']
  | add x y hx hy =>
      rw [smul_add, map_add, hx, hy]
      rw [← Finsupp.mapRange_add (f := fun z : K ↦ z * a) (hf' := fun x y : K ↦ add_mul x y a)]
      rw [map_add]

/-- Helper for Chap11 Lemma 11 4 3: left scalar multiplication on `K ⊗[k] V` multiplies each
basis coordinate on the left. -/
lemma equivFinsuppOfBasisRight_smul
    {ι : Type*} [DecidableEq ι] (b : Module.Basis ι k V) (a : K) (x : K ⊗[k] V) :
    TensorProduct.equivFinsuppOfBasisRight b (a • x) =
      a • TensorProduct.equivFinsuppOfBasisRight b x := by
  -- Route correction: expose the transported `K`-linearity as a named equality instead of
  -- relying on a fragile `change` step inside later proofs.
  induction x using TensorProduct.induction_on with
  | zero =>
      ext i
      simp
  | tmul c v =>
      ext i
      simp [TensorProduct.smul_tmul']
  | add x y hx hy =>
      simp [smul_add, hx, hy]

/-- Helper for Chap11 Lemma 11 4 3: evaluating the left scalar-action formula at one basis
coordinate gives left multiplication by that scalar. -/
lemma equivFinsuppOfBasisRight_smul_apply
    {ι : Type*} [DecidableEq ι] (b : Module.Basis ι k V) (a : K) (x : K ⊗[k] V) (i : ι) :
    TensorProduct.equivFinsuppOfBasisRight b (a • x) i =
      a * TensorProduct.equivFinsuppOfBasisRight b x i := by
  -- Evaluate the named scalar-transport identity at the chosen coordinate.
  simpa [equivFinsuppOfBasisRight_smul (k := k) (K := K) (V := V) b a x, smul_eq_mul]

/-- Helper for Chap11 Lemma 11 4 3: evaluating the right `Kᵐᵒᵖ`-action formula at one basis
coordinate gives right multiplication by that scalar. -/
lemma equivFinsuppOfBasisRight_op_smul_apply
    {ι : Type*} [DecidableEq ι] (b : Module.Basis ι k V) (a : K) (x : K ⊗[k] V) (i : ι) :
    TensorProduct.equivFinsuppOfBasisRight b (op a • x) i =
      TensorProduct.equivFinsuppOfBasisRight b x i * a := by
  -- Evaluate the already-packaged right-action formula at the chosen coordinate.
  simpa using
    congrArg (fun f : ι →₀ K ↦ f i)
      (equivFinsuppOfBasisRight_op_smul (k := k) (K := K) (V := V) b a x)

/-- Helper for Chap11 Lemma 11 4 3: every generator `1 ⊗ v` coming from the contracted slice
already lies in the original two-sided submodule. -/
lemma baseChangeComapOneTmul_le
    (W : Submodule (K ⊗[k] Kᵐᵒᵖ) (K ⊗[k] V)) :
    let V' := ((Subbimodule.toSubmodule W).restrictScalars k).comap (mk k K V 1)
    V'.baseChange K ≤ Subbimodule.toSubmodule W := by
  intro V'
  -- Rewrite base change as the span of the pure tensors `1 ⊗ v` with `v ∈ V'`.
  rw [Submodule.baseChange_eq_span]
  refine Submodule.span_le.2 ?_
  rintro z ⟨v, hv, rfl⟩
  exact hv

/-- Helper for Chap11 Lemma 11 4 3: tensoring the quotient map by `V'` commutes with the canonical
right `Kᵐᵒᵖ`-action. -/
lemma baseChange_mkQ_op_smul
    (V' : Submodule k V) (a : K) (x : K ⊗[k] V) :
    (V'.mkQ.baseChange K) (op a • x) = op a • ((V'.mkQ.baseChange K) x) := by
  -- Verify the compatibility on pure tensors and extend by additivity.
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul b v =>
      simp [TensorProduct.smul_tmul']
  | add x y hx hy =>
      rw [smul_add, map_add, hx, hy, map_add, ← smul_add]

/-- Helper for Chap11 Lemma 11 4 3: once one basis coefficient has been normalized to `1`, the
left-right commutator loses that basis index from its support. -/
lemma supportCommutatorSubsetEraseOfNormalizedCoefficient
    {ι : Type*} [DecidableEq ι] (b : Module.Basis ι k V) (i : ι) (y : K ⊗[k] V)
    (hi : TensorProduct.equivFinsuppOfBasisRight b y i = 1) (a : K) :
    (TensorProduct.equivFinsuppOfBasisRight b (a • y - op a • y)).support ⊆
      (TensorProduct.equivFinsuppOfBasisRight b y).support.erase i := by
  intro j hj
  -- Compare the `j`-th commutator coordinate with the normalized basis coefficients of `y`.
  have hcoord :
      TensorProduct.equivFinsuppOfBasisRight b (a • y - op a • y) j =
        a * TensorProduct.equivFinsuppOfBasisRight b y j -
          TensorProduct.equivFinsuppOfBasisRight b y j * a := by
    have hleft :
        TensorProduct.equivFinsuppOfBasisRight b (a • y) j =
          a * TensorProduct.equivFinsuppOfBasisRight b y j := by
      -- Evaluate the named left-action coordinate formula at the chosen basis index.
      simpa using
        equivFinsuppOfBasisRight_smul_apply (k := k) (K := K) (V := V) b a y j
    have hright :
        TensorProduct.equivFinsuppOfBasisRight b (op a • y) j =
          TensorProduct.equivFinsuppOfBasisRight b y j * a := by
      -- Evaluate the named right-action coordinate formula at the same basis index.
      simpa using
        equivFinsuppOfBasisRight_op_smul_apply (k := k) (K := K) (V := V) b a y j
    calc
      TensorProduct.equivFinsuppOfBasisRight b (a • y - op a • y) j
          = TensorProduct.equivFinsuppOfBasisRight b (a • y) j
              - TensorProduct.equivFinsuppOfBasisRight b (op a • y) j := by
                simp
      _ = a * TensorProduct.equivFinsuppOfBasisRight b y j
            - TensorProduct.equivFinsuppOfBasisRight b y j * a := by
              rw [hleft, hright]
  have hji : j ≠ i := by
    intro hji
    have hzero :
        TensorProduct.equivFinsuppOfBasisRight b (a • y - op a • y) j = 0 := by
      rw [hcoord, hji, hi]
      simp
    exact (Finsupp.mem_support_iff.mp hj) hzero
  have hyj :
      TensorProduct.equivFinsuppOfBasisRight b y j ≠ 0 := by
    intro hyj
    have hzero :
        TensorProduct.equivFinsuppOfBasisRight b (a • y - op a • y) j = 0 := by
      rw [hcoord, hyj]
      simp
    exact (Finsupp.mem_support_iff.mp hj) hzero
  exact Finset.mem_erase.mpr ⟨hji, Finsupp.mem_support_iff.mpr hyj⟩

/-- Helper for Chap11 Lemma 11 4 3: if every basis coefficient comes from the center `k`, then the
tensor already lies in the slice `1 ⊗ V`. -/
lemma memRangeMkOfCentralBasisCoefficients
    {ι : Type*} [DecidableEq ι] (b : Module.Basis ι k V) (y : K ⊗[k] V)
    (hcentral : ∀ i, ∃ r : k, TensorProduct.equivFinsuppOfBasisRight b y i = algebraMap k K r) :
    y ∈ LinearMap.range (mk k K V 1) := by
  classical
  let fy := TensorProduct.equivFinsuppOfBasisRight b y
  let coeffLift : K → k := fun z =>
    if hz : ∃ r : k, z = algebraMap k K r then Classical.choose hz else 0
  have hcoeffLift_zero : coeffLift 0 = 0 := by
    dsimp [coeffLift]
    split_ifs with h
    · exact (algebraMap k K).injective (by simpa [eq_comm] using Classical.choose_spec h)
    · rfl
  let coeffs : ι →₀ k := fy.mapRange coeffLift hcoeffLift_zero
  have hcoeffs_map :
      coeffs.mapRange (algebraMap k K) (by simp) = fy := by
    ext i
    -- Rewrite each coordinate using the chosen preimage from the center.
    rcases hcentral i with ⟨r, hr⟩
    simp [coeffs, fy, coeffLift, hr]
  refine LinearMap.mem_range.mpr ?_
  refine ⟨coeffs.sum fun i r ↦ r • b i, ?_⟩
  -- Rebuild the tensor from its basis coefficients and rewrite each coefficient as `1 ⊗ r • b i`.
  calc
    (mk k K V 1) (coeffs.sum fun i r ↦ r • b i)
        = coeffs.sum fun i r ↦ (algebraMap k K r) ⊗ₜ[k] b i := by
          calc
            (mk k K V 1) (coeffs.sum fun i r ↦ r • b i)
                = ∑ i ∈ coeffs.support, (mk k K V 1) (coeffs i • b i) := by
                    simp [Finsupp.sum]
            _ = ∑ i ∈ coeffs.support, (algebraMap k K (coeffs i)) ⊗ₜ[k] b i := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    calc
                      (mk k K V 1) (coeffs i • b i) = (1 : K) ⊗ₜ[k] (coeffs i • b i) := rfl
                      _ = coeffs i • ((1 : K) ⊗ₜ[k] b i) := by
                            simpa using
                              (TensorProduct.tmul_smul (R := k) (r := coeffs i) (x := (1 : K))
                                (y := b i))
                      _ = (algebraMap k K (coeffs i)) ⊗ₜ[k] b i := by
                            simp [TensorProduct.smul_tmul', Algebra.smul_def]
            _ = coeffs.sum fun i r ↦ (algebraMap k K r) ⊗ₜ[k] b i := by
                    simp [Finsupp.sum]
    _ = (coeffs.mapRange (algebraMap k K) (by simp)).sum fun i m ↦ m ⊗ₜ[k] b i := by
          symm
          simpa using
            (Finsupp.sum_mapRange_index
              (g := coeffs)
              (f := algebraMap k K)
              (h := fun i m ↦ m ⊗ₜ[k] b i)
              (by intro i; simp))
    _ = fy.sum fun i m ↦ m ⊗ₜ[k] b i := by
          rw [hcoeffs_map]
    _ = y := by
          simpa [fy] using
            (TensorProduct.equivFinsuppOfBasisRight_symm_apply (𝒞 := b) fy).symm

variable [Algebra.IsCentral k K]

/-- Helper for Chap11 Lemma 11 4 3: every nonzero two-sided submodule of `K ⊗[k] V` contains a
nonzero element of the slice `1 ⊗ V`. -/
lemma exists_nonzero_mem_range_mk_of_nonzeroTwoSided
    (W : Submodule (K ⊗[k] Kᵐᵒᵖ) (K ⊗[k] V))
    (hW : W ≠ ⊥) :
    ∃ z, z ≠ 0 ∧ z ∈ Subbimodule.toSubmodule W ∧ z ∈ LinearMap.range (mk k K V 1) := by
  classical
  obtain ⟨s, hs⟩ := Module.Basis.exists_basis (K := k) (V := V)
  let b : Module.Basis s k V := Classical.choice hs
  let P : ℕ → Prop := fun n =>
    ∀ x, x ∈ Subbimodule.toSubmodule W →
      (TensorProduct.equivFinsuppOfBasisRight b x).support.card ≤ n →
      x ≠ 0 →
      ∃ z, z ≠ 0 ∧ z ∈ Subbimodule.toSubmodule W ∧ z ∈ LinearMap.range (mk k K V 1)
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih x hxW hxcard hx0
    let fx := TensorProduct.equivFinsuppOfBasisRight b x
    have hfx0 : fx ≠ 0 := by
      intro hfx0
      exact hx0 ((TensorProduct.equivFinsuppOfBasisRight b).injective (by simpa [fx] using hfx0))
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hfx0
    have hfxi : fx i ≠ 0 := Finsupp.mem_support_iff.mp hi
    let y : K ⊗[k] V := (fx i)⁻¹ • x
    let fy := TensorProduct.equivFinsuppOfBasisRight b y
    have hyW : y ∈ Subbimodule.toSubmodule W := by
      -- Normalize the chosen nonzero coefficient while staying inside the two-sided submodule.
      simpa [y, fx] using Subbimodule.smul_mem W (fx i)⁻¹ hxW
    have hy0 : y ≠ 0 := by
      -- Nonzero scalar multiplication preserves nonvanishing.
      simpa [y] using smul_ne_zero (inv_ne_zero hfxi) hx0
    have hfy : fy = (fx i)⁻¹ • fx := by
      -- Push the normalization through the coordinate equivalence via the named scalar formula.
      simpa [fy, fx, y] using
        (equivFinsuppOfBasisRight_smul (k := k) (K := K) (V := V) b (fx i)⁻¹ x)
    have hfy_i : fy i = 1 := by
      -- The selected basis coordinate is now exactly `1`.
      rw [hfy]
      simp [hfxi]
    have hfy_support : fy.support = fx.support := by
      -- Rescaling by a nonzero scalar does not change the coordinate support.
      rw [hfy]
      simpa using
        (Finsupp.support_smul_eq (b := (fx i)⁻¹) (g := fx) (hb := inv_ne_zero hfxi))
    have hfy_card : fy.support.card ≤ n := by
      rwa [hfy_support]
    -- Route correction: use induction on support cardinality rather than a `Nat.find`-minimal
    -- witness, so every fallback commutator is handled by the same local induction hypothesis.
    by_cases hcomm : ∃ a : K, a • y - op a • y ≠ 0
    · rcases hcomm with ⟨a, ha0⟩
      let u : K ⊗[k] V := a • y - op a • y
      have huW : u ∈ Subbimodule.toSubmodule W := by
        -- The left-right commutator stays inside the two-sided submodule.
        refine Submodule.sub_mem _ ?_ ?_
        · exact Subbimodule.smul_mem W a hyW
        · exact Subbimodule.smul_mem' W (op a) hyW
      have hu_subset :
          (TensorProduct.equivFinsuppOfBasisRight b u).support ⊆ fy.support.erase i := by
        -- The normalized coefficient vanishes in the commutator support.
        simpa [u, fy] using
          supportCommutatorSubsetEraseOfNormalizedCoefficient
            (k := k) (K := K) (V := V) b i y hfy_i a
      have hfy_mem : i ∈ fy.support := by
        exact Finsupp.mem_support_iff.mpr (by simpa [hfy_i])
      have hu_lt : (TensorProduct.equivFinsuppOfBasisRight b u).support.card < n := by
        have hu_lt' :
            (TensorProduct.equivFinsuppOfBasisRight b u).support.card < fy.support.card := by
          exact lt_of_le_of_lt
            (Finset.card_le_card hu_subset)
            (Finset.card_lt_card (Finset.erase_ssubset hfy_mem))
        exact lt_of_lt_of_le hu_lt' hfy_card
      exact ih _ hu_lt u huW le_rfl ha0
    · have hcommEq : ∀ a : K, a • y = op a • y := by
        intro a
        have hzero : a • y - op a • y = 0 := by
          by_contra hzero
          exact hcomm ⟨a, hzero⟩
        exact sub_eq_zero.mp hzero
      have hcentral : ∀ j, ∃ r : k, fy j = algebraMap k K r := by
        intro j
        have hj_center : fy j ∈ Subalgebra.center k K := by
          rw [Subalgebra.mem_center_iff]
          intro a
          -- Compare the `j`-th basis coordinate of the left and right scalar actions.
          have hcoord :=
            congrArg (fun t : K ⊗[k] V ↦ TensorProduct.equivFinsuppOfBasisRight b t j) (hcommEq a)
          have hleft :
              TensorProduct.equivFinsuppOfBasisRight b (a • y) j = a * fy j := by
            -- Evaluate the named left-action coordinate formula at the `j`-th basis coefficient.
            simpa [fy] using
              equivFinsuppOfBasisRight_smul_apply (k := k) (K := K) (V := V) b a y j
          have hright :
              TensorProduct.equivFinsuppOfBasisRight b (op a • y) j = fy j * a := by
            -- Evaluate the named right-action coordinate formula at the same basis coefficient.
            simpa [fy] using
              equivFinsuppOfBasisRight_op_smul_apply (k := k) (K := K) (V := V) b a y j
          calc
            a * fy j = TensorProduct.equivFinsuppOfBasisRight b (a • y) j := by simpa using hleft.symm
            _ = TensorProduct.equivFinsuppOfBasisRight b (op a • y) j := hcoord
            _ = fy j * a := hright
        exact (Algebra.IsCentral.mem_center_iff (K := k) (D := K) (x := fy j)).mp hj_center
      refine ⟨y, hy0, hyW, ?_⟩
      -- Central coefficients reconstruct `y` as an element of the slice `1 ⊗ V`.
      exact memRangeMkOfCentralBasisCoefficients
        (k := k) (K := K) (V := V) b y hcentral
  have hW' : Subbimodule.toSubmodule W ≠ ⊥ := by
    intro hbot
    apply hW
    ext z
    exact Iff.of_eq (by
      simpa [Subbimodule.toSubmodule] using
        congrArg (fun S : Submodule K (K ⊗[k] V) ↦ z ∈ S) hbot)
  obtain ⟨x, hxW, hx0⟩ := (Submodule.ne_bot_iff _).mp hW'
  exact hP _ x hxW le_rfl hx0

/-- Helper for Chap11 Lemma 11 4 3: in the commuted owner model `K ⊗[k] V`, a two-sided
submodule is the base change of its contraction along `v ↦ 1 ⊗ v`. -/
lemma twoSidedSubmodule_eqBaseChangeComapOneTmulAux
    (W : Submodule (K ⊗[k] Kᵐᵒᵖ) (K ⊗[k] V)) :
    let V' := ((Subbimodule.toSubmodule W).restrictScalars k).comap
      (mk k K V 1)
    V'.baseChange K = Subbimodule.toSubmodule W := by
  intro V'
  let U : Submodule K (K ⊗[k] V) := V'.baseChange K
  let q : K ⊗[k] V →ₗ[K] K ⊗[k] (V ⧸ V') := V'.mkQ.baseChange K
  have hUle : U ≤ Subbimodule.toSubmodule W := by
    -- The contracted slice already generates a base-changed submodule inside `W`.
    simpa [U, V'] using baseChangeComapOneTmul_le (k := k) (K := K) (V := V) W
  have hker : LinearMap.ker q = U := by
    -- The tensorized quotient map has kernel exactly the base change of `V'`.
    ext x
    have hx := congrArg (fun S : Submodule k (K ⊗[k] V) ↦ x ∈ S) (lTensor_mkQ (Q := K) (N := V'))
    simpa [q, U, LinearMap.baseChange_eq_ltensor, Submodule.baseChange] using hx
  let Wq : Submodule (K ⊗[k] Kᵐᵒᵖ) (K ⊗[k] (V ⧸ V')) :=
    Subbimodule.mk (Submodule.map q (Subbimodule.toSubmodule W)).toAddSubmonoid
      (fun a {x} hx ↦ by
        -- The quotient image remains stable under the left `K`-action.
        rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
        exact Submodule.mem_map.mpr ⟨a • y, Subbimodule.smul_mem W a hy, by simp⟩)
      (fun a {x} hx ↦ by
        -- The quotient image also remains stable under the right `Kᵐᵒᵖ`-action.
        rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
        refine Submodule.mem_map.mpr ⟨a • y, Subbimodule.smul_mem' W a hy, ?_⟩
        simpa [q] using baseChange_mkQ_op_smul (k := k) (K := K) (V := V) V' a.unop y)
  have hWq_bot : Wq = ⊥ := by
    by_contra hWq
    obtain ⟨z, hz0, hzWq, hzslice⟩ :=
      exists_nonzero_mem_range_mk_of_nonzeroTwoSided (k := k) (K := K) (V := V ⧸ V') Wq hWq
    rcases Submodule.mem_map.mp hzWq with ⟨y, hyW, hyq⟩
    rcases LinearMap.mem_range.mp hzslice with ⟨vbar, rfl⟩
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective V' vbar
    have hyq' : q y = (1 : K) ⊗ₜ[k] (V'.mkQ v) := by
      simpa using hyq
    have hqone : q ((1 : K) ⊗ₜ[k] v) = (1 : K) ⊗ₜ[k] (V'.mkQ v) := by
      simpa [q] using (LinearMap.baseChange_tmul (f := V'.mkQ) (a := (1 : K)) (x := v))
    have hdiff_zero : q (y - ((1 : K) ⊗ₜ[k] v)) = 0 := by
      rw [LinearMap.map_sub, hyq', hqone, sub_self]
    have hdiff_memU : y - ((1 : K) ⊗ₜ[k] v) ∈ U := by
      rw [← hker]
      simpa [LinearMap.mem_ker] using hdiff_zero
    have hdiff_memW : y - ((1 : K) ⊗ₜ[k] v) ∈ Subbimodule.toSubmodule W := hUle hdiff_memU
    have hone_memW : ((1 : K) ⊗ₜ[k] v) ∈ Subbimodule.toSubmodule W := by
      -- Compare `y` with its slice representative in the quotient and descend back to `W`.
      simpa [sub_eq_add_neg, add_assoc] using Submodule.sub_mem _ hyW hdiff_memW
    have hv_mem : v ∈ V' := hone_memW
    have hz_eq_zero : (1 : K) ⊗ₜ[k] (V'.mkQ v) = 0 := by
      simp [hv_mem]
    exact hz0 (by simpa [hqone] using hz_eq_zero)
  refine le_antisymm hUle ?_
  intro x hxW
  have hxq_mem : q x ∈ Subbimodule.toSubmodule Wq := Submodule.mem_map.mpr ⟨x, hxW, rfl⟩
  have hxq_zero : q x = 0 := by
    simpa [hWq_bot] using hxq_mem
  have hx_memker : x ∈ LinearMap.ker q := by
    rw [LinearMap.mem_ker]
    exact hxq_zero
  simpa [hker] using hx_memker

omit [Algebra.IsCentral k K] in
/-- Helper for Chap11 Lemma 11 4 3: commuting the factors turns left multiplication on the
`K`-tensor factor into the left `K`-action on `K ⊗[k] V`. -/
lemma comm_lTensor_mulLeft (a : K) (x : V ⊗[k] K) :
    (TensorProduct.comm k V K) (((mulLeft k a).lTensor V) x) =
      a • (TensorProduct.comm k V K x) := by
  -- Check the transport identity on pure tensors and extend by additivity.
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul v b =>
      simp [TensorProduct.comm_tmul, TensorProduct.smul_tmul']
  | add x y hx hy =>
      simp [hx, hy]

omit [Algebra.IsCentral k K] in
/-- Helper for Chap11 Lemma 11 4 3: commuting the factors turns right multiplication on the
`K`-tensor factor into the canonical `Kᵐᵒᵖ`-action on `K ⊗[k] V`. -/
lemma comm_lTensor_mulRight (a : K) (x : V ⊗[k] K) :
    (TensorProduct.comm k V K) (((mulRight k a).lTensor V) x) =
      op a • (TensorProduct.comm k V K x) := by
  -- Check the transport identity on pure tensors and extend by additivity.
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul v b =>
      simp [TensorProduct.comm_tmul, TensorProduct.smul_tmul']
  | add x y hx hy =>
      simp [hx, hy]

/-- Chap11 Lemma 11 4 3: source-facing bridge/view for a `k`-vector space `V` and a central
`k`-division algebra `K`; a `k`-submodule of `V ⊗[k] K` stable under left and right multiplication
on the `K`-factor is obtained by transporting back the left `K`-span of the intersection of its
commuted image with `1 ⊗ V`. -/
@[stacks 074B]
theorem two_sided_submodule_eq_generated_by_inter_tmul_one
    (W : Submodule k (V ⊗[k] K))
    (hW_left :
      ∀ a : K,
        Set.MapsTo (((mulLeft k a).lTensor V) : V ⊗[k] K →ₗ[k] V ⊗[k] K) W W)
    (hW_right :
      ∀ a : K,
        Set.MapsTo (((mulRight k a).lTensor V) : V ⊗[k] K →ₗ[k] V ⊗[k] K) W W)
    :
    let W' : Submodule k (K ⊗[k] V) := W.map (TensorProduct.comm k V K).toLinearMap
    ((Submodule.span K ↑(W' ⊓ LinearMap.range (mk k K V 1))).restrictScalars k).map
      (TensorProduct.comm k K V).toLinearMap = W := by
  let W' : Submodule k (K ⊗[k] V) := W.map (TensorProduct.comm k V K).toLinearMap
  let W'' : Submodule (K ⊗[k] Kᵐᵒᵖ) (K ⊗[k] V) :=
    Subbimodule.mk W'.toAddSubmonoid
      (fun a {x} hx ↦ by
        -- Transport the left `K`-stability of `W` across the tensor-factor swap.
        rcases hx with ⟨y, hy, rfl⟩
        refine ⟨((mulLeft k a).lTensor V) y, hW_left a hy, ?_⟩
        exact comm_lTensor_mulLeft (k := k) (K := K) (V := V) a y
      )
      (fun a {x} hx ↦ by
        -- Transport the right `K`-stability of `W` into the canonical `Kᵐᵒᵖ`-action.
        rcases hx with ⟨y, hy, rfl⟩
        refine ⟨((mulRight k a.unop).lTensor V) y, hW_right a.unop hy, ?_⟩
        simpa using comm_lTensor_mulRight (k := k) (K := K) (V := V) a.unop y
      )
  have hcomm :
      Submodule.span K ↑(W' ⊓ LinearMap.range (mk k K V 1)) = Subbimodule.toSubmodule W'' := by
    -- Route correction: work in the commuted bimodule model, where the core descent theorem
    -- applies directly.
    simpa [W', W'', Submodule.baseChange_eq_span, Submodule.map_comap_eq, Set.inter_comm] using
      twoSidedSubmodule_eqBaseChangeComapOneTmulAux (k := k) (K := K) (V := V) W''
  have hback :
      ((Subbimodule.toSubmodule W'').restrictScalars k).map
        (TensorProduct.comm k K V).toLinearMap = W := by
    -- The two commutation maps are inverse linear equivalences on the underlying `k`-submodule.
    change (W'.map (TensorProduct.comm k K V).toLinearMap) = W
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨z, hz, rfl⟩
      simpa using hz
    · intro hx
      refine ⟨(TensorProduct.comm k V K) x, ?_, by simp⟩
      exact ⟨x, hx, by simp⟩
  -- Map the commuted-model equality back across `TensorProduct.comm`.
  have := congrArg
      (fun S : Submodule K (K ⊗[k] V) ↦
        (S.restrictScalars k).map (TensorProduct.comm k K V).toLinearMap)
      hcomm
  exact this.trans hback

/-- Core/canonical bridge for Lemma 11.4.3: for a `k`-vector space `V` and a central
`k`-division algebra `K`, a two-sided `K`-submodule of `K ⊗[k] V` is the base change of its
contraction along `v ↦ 1 ⊗ v`. -/
theorem two_sided_submodule_eq_baseChange_comap_one_tmul
    (W : Submodule (K ⊗[k] Kᵐᵒᵖ) (K ⊗[k] V)) :
    let V' := ((Subbimodule.toSubmodule W).restrictScalars k).comap
      (mk k K V 1)
    V'.baseChange K = Subbimodule.toSubmodule W := by
  -- Keep the public theorem as a thin wrapper around the local owner-model helper.
  simpa using twoSidedSubmodule_eqBaseChangeComapOneTmulAux (k := k) (K := K) (V := V) W

/-- Bridge/view companion to Lemma 11.4.3, in the commuted owner model `K ⊗[k] V`: for a central
`k`-division algebra `K`, a two-sided `K`-submodule is the left `K`-span of its intersection with
`1 ⊗ V`. -/
theorem two_sided_submodule_comm_eq_generated_by_inter_tmul_one
    (W : Submodule (K ⊗[k] Kᵐᵒᵖ) (K ⊗[k] V)) :
    Submodule.span K ↑((Subbimodule.toSubmodule W).restrictScalars k ⊓
      LinearMap.range (mk k K V 1)) = Subbimodule.toSubmodule W := by
  simpa [Submodule.baseChange_eq_span, Submodule.map_comap_eq, inf_comm] using
    two_sided_submodule_eq_baseChange_comap_one_tmul W

end TwoSidedSubmodule

end
