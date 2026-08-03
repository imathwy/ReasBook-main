import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.MetricSpace.Bounded
import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap01.Text_1_0_13
import BauschkeLean.Chap17.Proposition_17_39.SelectionContinuity
import BauschkeLean.Chap20.Example_20_41
import BauschkeLean.Chap21.Definition_21_10
import BauschkeLean.Chap21.Theorem_21_18

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open SetValuedOperator
open scoped InnerProductSpace SetValuedOperator Topology

noncomputable section

local notation "L2" => ℓ²(ℕ, ℝ)

/-- The standard Hilbert basis on `ℓ²(ℕ, ℝ)`. -/
private def example21_22Basis : HilbertBasis ℕ ℝ L2 :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ L2)

/-- The diagonal weights `β n = (2^n)⁻¹` used in Example 21.22. -/
private def example21_22Weight (n : ℕ) : NNRealˣ :=
  (Units.mk0 ((2 : NNReal) ^ n) (pow_ne_zero n (by norm_num : (2 : NNReal) ≠ 0)))⁻¹

/-- The Example 21.22 weights satisfy `β n ≤ 1`. -/
private theorem example21_22Weight_le_one (n : ℕ) :
    (example21_22Weight n : NNReal) ≤ 1 := by
  change (((2 : NNReal) ^ n)⁻¹ : NNReal) ≤ 1
  exact inv_le_one_of_one_le₀ (one_le_pow_of_one_le' (by norm_num : (1 : NNReal) ≤ 2) n)

/-- Helper for Example 21.22: the diagonal weight equals `(2^n)⁻¹` after coercing to `ℝ`. -/
private theorem weightCoeReal (n : ℕ) :
    (example21_22Weight n : ℝ) = ((2 : ℝ) ^ n)⁻¹ := by
  -- The concrete example uses the inverse of the positive unit `(2^n)`.
  simp [example21_22Weight]

/-- Helper for Example 21.22: the inverse weight simplifies back to `2^n` in `ℝ`. -/
private theorem weightInvCoeReal (n : ℕ) :
    ((example21_22Weight n : ℝ)⁻¹) = (2 : ℝ) ^ n := by
  -- The weight is nonzero because each power of `2` is nonzero.
  rw [weightCoeReal]
  simp

/-- Helper for Example 21.22: the weight sequence tends to `0`. -/
private theorem weightTendstoZero :
    Tendsto (fun n ↦ (example21_22Weight n : ℝ)) atTop (𝓝 0) := by
  -- This is the standard inverse-power decay of `2 ^ n`.
  simpa [weightCoeReal] using
    (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two))

/-- Helper for Example 21.22: the standard Hilbert basis is the coordinate basis on `ℓ²`. -/
private theorem example21_22Basis_apply (n m : ℕ) :
    example21_22Basis n m = if n = m then 1 else 0 := by
  -- The chosen Hilbert-basis equivalence is the identity on `ℓ²`.
  change (({ repr := LinearIsometryEquiv.refl ℝ L2 } : HilbertBasis ℕ ℝ L2) n) m =
      if n = m then 1 else 0
  have hb :
      (({ repr := LinearIsometryEquiv.refl ℝ L2 } : HilbertBasis ℕ ℝ L2) n : L2) =
        (LinearIsometryEquiv.refl ℝ L2).symm
          (lp.single (E := fun _ : ℕ => ℝ) 2 n (1 : ℝ)) := by
    simpa using
      (HilbertBasis.repr_symm_single
        ({ repr := LinearIsometryEquiv.refl ℝ L2 } : HilbertBasis ℕ ℝ L2) n).symm
  have hm := congrArg (fun z : L2 ↦ z m) hb
  calc
    (({ repr := LinearIsometryEquiv.refl ℝ L2 } : HilbertBasis ℕ ℝ L2) n) m
        = ((LinearIsometryEquiv.refl ℝ L2).symm
            (lp.single (E := fun _ : ℕ => ℝ) 2 n (1 : ℝ))) m := hm
    _ = if n = m then 1 else 0 := by
      have hvec :
          (LinearIsometryEquiv.refl ℝ L2).symm
              (lp.single (E := fun _ : ℕ => ℝ) 2 n (1 : ℝ)) =
            lp.single (E := fun _ : ℕ => ℝ) 2 n (1 : ℝ) := by
        simpa using
          (LinearIsometryEquiv.symm_apply_apply (LinearIsometryEquiv.refl ℝ L2)
            (lp.single (E := fun _ : ℕ => ℝ) 2 n (1 : ℝ)))
      have hm' := congrArg (fun z : L2 ↦ z m) hvec
      simpa [Pi.single_apply, eq_comm] using hm'

/-- For Example 21.22 (1), the diagonal operator `A` on `ℓ²(ℕ, ℝ)` has coordinates
`A x = (fun n ↦ x n / (2 : ℝ) ^ n)`. -/
def example21_22ForwardOperator : L2 →L[ℝ] L2 :=
  HilbertBasis.diagonalForwardOperator
    example21_22Basis example21_22Weight example21_22Weight_le_one

/-- The forward diagonal operator acts coordinatewise by division by `2 ^ n`. -/
@[simp] theorem example21_22ForwardOperator_apply (x : L2) (n : ℕ) :
    example21_22ForwardOperator x n = x n / (2 : ℝ) ^ n := by
  -- The abstract diagonal operator becomes the standard coordinate multiplier on `ℓ²`.
  simp only [example21_22ForwardOperator, HilbertBasis.diagonalForwardOperator,
    ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, Function.comp_apply]
  change (example21_22Weight n : ℝ) * x n = x n * ((2 : ℝ) ^ n)⁻¹
  rw [weightCoeReal, mul_comm]

/-- For Example 21.22 (2), the forward diagonal operator is maximally monotone when viewed as
its associated singleton-valued set-valued operator. -/
theorem example21_22ForwardOperator_isMaximallyMonotone :
    Maximal IsMonotone example21_22ForwardOperator.toSetValuedOperator := by
  -- Example 20.41 already proves maximal monotonicity for every diagonal contraction.
  simpa [example21_22ForwardOperator] using
    HilbertBasis.diagonalForwardOperator_isMaximallyMonotone
      example21_22Basis example21_22Weight example21_22Weight_le_one

/-- For Example 21.22 (3), the forward diagonal operator is locally bounded at every point of
`ℓ²(ℕ, ℝ)`. -/
theorem example21_22ForwardOperator_locallyBoundedEverywhere :
    example21_22ForwardOperator.toSetValuedOperator.IsLocallyBounded := by
  -- Local boundedness is proved pointwise from bounded images of metric balls.
  intro x
  refine ⟨1, by norm_num, ?_⟩
  have hbounded :
      Bornology.IsBounded (example21_22ForwardOperator '' Metric.ball x 1) :=
    (Metric.isBounded_ball).image example21_22ForwardOperator
  have himage :
      example21_22ForwardOperator.toSetValuedOperator.image (Metric.ball x 1) =
        example21_22ForwardOperator '' Metric.ball x 1 := by
    ext y
    constructor <;> simp [SetValuedOperator.image, Function.toSetValuedOperator_apply, eq_comm]
  rw [himage]
  exact hbounded

/-- The forward diagonal operator is locally bounded at each point of `ℓ²(ℕ, ℝ)`. -/
theorem example21_22ForwardOperator_isLocallyBoundedAt (x : L2) :
    example21_22ForwardOperator.toSetValuedOperator.IsLocallyBoundedAt x := by
  -- A continuous linear map sends the unit ball around `x` to a bounded set.
  refine ⟨1, by norm_num, ?_⟩
  have hbounded :
      Bornology.IsBounded (example21_22ForwardOperator '' Metric.ball x 1) :=
    (Metric.isBounded_ball).image example21_22ForwardOperator
  -- The singleton-valued operator image is the ordinary set image of the map.
  have himage :
      example21_22ForwardOperator.toSetValuedOperator.image (Metric.ball x 1) =
        example21_22ForwardOperator '' Metric.ball x 1 := by
    ext y
    constructor <;> simp [SetValuedOperator.image, Function.toSetValuedOperator_apply, eq_comm]
  rw [himage]
  exact hbounded

/-- For Example 21.22 (4), the domain of the forward operator is all of `ℓ²(ℕ, ℝ)`. -/
theorem example21_22ForwardOperator_dom_eq_univ :
    example21_22ForwardOperator.toSetValuedOperator.dom = Set.univ := by
  -- A singleton-valued everywhere-defined operator has full domain.
  ext x
  constructor
  · intro _
    simp
  · intro _
    exact (SetValuedOperator.mem_dom_iff _ x).2 ⟨example21_22ForwardOperator x, by simp⟩

/-- For Example 21.22, this is the dense linear subspace that is the natural domain of the
inverse diagonal operator. -/
def example21_22InverseDomain : Submodule ℝ L2 :=
  HilbertBasis.diagonalInverseDomain example21_22Basis example21_22Weight

/-- Membership in the inverse domain means square summability of the reweighted coordinate
sequence `n ↦ (2 : ℝ) ^ n * x n`. -/
@[simp] theorem mem_example21_22InverseDomain (x : L2) :
    x ∈ example21_22InverseDomain ↔ Memℓp (fun n ↦ (2 : ℝ) ^ n * x n) 2 := by
  -- The generic inverse-domain condition specializes to the concrete weights `2^n`.
  rw [example21_22InverseDomain, HilbertBasis.mem_diagonalInverseDomain]
  simp [example21_22Basis, weightInvCoeReal]

/-- The single-valued inverse diagonal map on its natural dense domain. -/
def example21_22InverseLinearMap : example21_22InverseDomain →ₗ[ℝ] L2 :=
  HilbertBasis.diagonalInverseLinearMap example21_22Basis example21_22Weight

/-- The inverse diagonal map acts coordinatewise by multiplication by `2 ^ n`. -/
@[simp] theorem example21_22InverseLinearMap_apply {x : L2}
    (hx : x ∈ example21_22InverseDomain) (n : ℕ) :
    example21_22InverseLinearMap ⟨x, hx⟩ n = (2 : ℝ) ^ n * x n := by
  -- The inverse linear map multiplies the `n`th coordinate by the inverse weight.
  simp only [example21_22InverseLinearMap, HilbertBasis.diagonalInverseLinearMap,
    example21_22InverseDomain]
  change ((example21_22Weight n : ℝ)⁻¹) * x n = (2 : ℝ) ^ n * x n
  rw [weightInvCoeReal]

/-- Helper for Example 21.22: the spike vector lies in the dense inverse-domain subspace. -/
private theorem inverseSpike_mem (n : ℕ) :
    (n : ℝ) • ((example21_22Weight n : ℝ) • example21_22Basis n) ∈ example21_22InverseDomain := by
  -- Start from the weighted basis vector already known to lie in the inverse domain.
  refine example21_22InverseDomain.smul_mem (n : ℝ) ?_
  simpa [example21_22InverseDomain] using
    HilbertBasis.smul_basis_mem_diagonalInverseDomain example21_22Basis example21_22Weight n

/-- Helper for Example 21.22: the spike sequence used to witness inverse-side blow-up. -/
private def inverseSpike (n : ℕ) : example21_22InverseDomain :=
  ⟨(n : ℝ) • ((example21_22Weight n : ℝ) • example21_22Basis n), inverseSpike_mem n⟩

/-- Helper for Example 21.22: the ambient norm of the spike is `n / 2^n`. -/
private theorem norm_inverseSpike (n : ℕ) :
    ‖((inverseSpike n : example21_22InverseDomain) : L2)‖ = (n : ℝ) / (2 : ℝ) ^ n := by
  -- The spike is a scalar multiple of one basis vector, so its norm is the product of scalar
  -- norms.
  change ‖(n : ℝ) • ((example21_22Weight n : ℝ) • example21_22Basis n)‖ =
      (n : ℝ) / (2 : ℝ) ^ n
  have hn : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hβ : 0 ≤ ((2 : ℝ) ^ n)⁻¹ := by
    exact inv_nonneg.mpr (pow_nonneg (by positivity : 0 ≤ (2 : ℝ)) n)
  rw [norm_smul, norm_smul, weightCoeReal, Real.norm_of_nonneg hn, Real.norm_of_nonneg hβ,
    example21_22Basis.orthonormal.norm_eq_one]
  simp [div_eq_mul_inv]

/-- Helper for Example 21.22: the ambient spike sequence converges to `0`. -/
private theorem inverseSpike_tendsto_zero :
    Tendsto (fun n ↦ ((inverseSpike n : example21_22InverseDomain) : L2)) atTop (𝓝 0) := by
  -- The norm formula reduces the claim to the standard limit `n / 2^n → 0`.
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hpow :
      Tendsto (fun n ↦ (n : ℝ) ^ 1 / (2 : ℝ) ^ n : ℕ → ℝ) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 1 one_lt_two
  simpa [norm_inverseSpike, pow_one] using hpow

/-- Helper for Example 21.22: the spike sequence also converges to `0` in the inverse-domain
subtype topology. -/
private theorem inverseSpike_tendsto_zero_subtype :
    Tendsto inverseSpike atTop (𝓝 (0 : example21_22InverseDomain)) := by
  -- The subtype topology is induced from the ambient Hilbert space.
  simpa using (tendsto_subtype_rng.2 inverseSpike_tendsto_zero)

/-- Helper for Example 21.22: the inverse map sends the spike at `n` to `n • e_n`. -/
private theorem inverseLinearMap_inverseSpike (n : ℕ) :
    example21_22InverseLinearMap (inverseSpike n) = (n : ℝ) • example21_22Basis n := by
  -- Compare coordinates: only the `n`th basis coordinate survives after reweighting.
  ext m
  rw [example21_22InverseLinearMap_apply (hx := (inverseSpike n).2)]
  by_cases hnm : n = m
  · subst hnm
    simp [inverseSpike, example21_22Basis_apply, weightCoeReal, mul_left_comm, mul_comm]
  · simp [inverseSpike, example21_22Basis_apply, hnm]

/-- Helper for Example 21.22: the image spike has norm exactly `n`. -/
private theorem norm_inverseLinearMap_inverseSpike (n : ℕ) :
    ‖example21_22InverseLinearMap (inverseSpike n)‖ = n := by
  -- Once the image is `n • e_n`, the orthonormality of the basis gives the norm.
  rw [inverseLinearMap_inverseSpike, norm_smul, example21_22Basis.orthonormal.norm_eq_one]
  simp

/-- For Example 21.22 (5), `B = A⁻¹` is the inverse operator associated with the diagonal map
`A`. -/
def example21_22InverseOperator : SetValuedOperator L2 L2 :=
  ofFunction (example21_22InverseDomain : Set L2) example21_22InverseLinearMap

/-- The source-facing inverse operator agrees with the coordinate inverse map on its natural
domain. -/
theorem example21_22InverseOperator_eq_ofFunction :
    example21_22InverseOperator =
      ofFunction (example21_22InverseDomain : Set L2) example21_22InverseLinearMap := rfl

/-- The source-facing inverse operator is the graph inverse of
`example21_22ForwardOperator.toSetValuedOperator`. -/
theorem example21_22InverseOperator_eq_inverseForwardOperator :
    example21_22InverseOperator = example21_22ForwardOperator.toSetValuedOperator⁻¹ := by
  simpa [example21_22InverseOperator, example21_22ForwardOperator] using
    (HilbertBasis.diagonalInverseOperator_eq_ofFunction
      example21_22Basis example21_22Weight example21_22Weight_le_one).symm

/-- For Example 21.22 (6), the inverse operator is maximally monotone. -/
theorem example21_22InverseOperator_isMaximallyMonotone :
    Maximal IsMonotone example21_22InverseOperator := by
  rw [example21_22InverseOperator_eq_inverseForwardOperator]
  simpa [example21_22ForwardOperator, HilbertBasis.diagonalInverseOperator] using
    HilbertBasis.diagonalInverseOperator_isMaximallyMonotone
      example21_22Basis example21_22Weight example21_22Weight_le_one

/-- On points of `example21_22InverseDomain`, the inverse operator takes the singleton value given
by the coordinate inverse map. -/
@[simp] theorem example21_22InverseOperator_apply_of_mem {x : L2}
    (hx : x ∈ example21_22InverseDomain) :
    example21_22InverseOperator x =
      ({example21_22InverseLinearMap ⟨x, hx⟩} : Set L2) := by
  simpa [example21_22InverseOperator] using
    ofFunction_apply_of_mem (example21_22InverseDomain : Set L2)
      example21_22InverseLinearMap hx

/-- Outside `example21_22InverseDomain`, the inverse operator has empty value set. -/
@[simp] theorem example21_22InverseOperator_apply_of_not_mem {x : L2}
    (hx : x ∉ example21_22InverseDomain) :
    example21_22InverseOperator x = (∅ : Set L2) := by
  simpa [example21_22InverseOperator] using
    ofFunction_apply_of_not_mem (example21_22InverseDomain : Set L2)
      example21_22InverseLinearMap hx

/-- For Example 21.22 (7), the domain of the inverse operator is the dense linear subspace
`example21_22InverseDomain`. -/
theorem example21_22InverseOperator_dom_eq_inverseDomain :
    example21_22InverseOperator.dom = example21_22InverseDomain := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy⟩
    rcases hy with ⟨hx, rfl⟩
    exact hx
  · intro hx
    exact ⟨example21_22InverseLinearMap ⟨x, hx⟩, ⟨hx, rfl⟩⟩

/-- Membership in the inverse-operator domain is exactly membership in the inverse-domain
subspace. -/
@[simp] theorem mem_dom_example21_22InverseOperator_iff (x : L2) :
    x ∈ example21_22InverseOperator.dom ↔ x ∈ example21_22InverseDomain := by
  rw [example21_22InverseOperator_dom_eq_inverseDomain]
  rfl

-- Semantic recall: Chapter 21 uses `SetValuedOperator.IsLocallyBoundedAt` for local boundedness,
-- and Chapter 17 uses `SetValuedOperator.SelectionContinuousAt` for continuity of a single-valued
-- realization on an operator domain.
/-- The inverse operator agrees with the coordinate inverse map on its natural domain. -/
@[simp] theorem mem_example21_22InverseOperator_iff (x y : L2) :
    y ∈ example21_22InverseOperator x ↔
      ∃ hx : x ∈ example21_22InverseDomain, y = example21_22InverseLinearMap ⟨x, hx⟩ := by
  constructor
  · rintro ⟨hx, rfl⟩
    exact ⟨hx, rfl⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨hx, rfl⟩

/-- For Example 21.22 (8), the domain of the inverse operator is dense in `ℓ²(ℕ, ℝ)`. -/
theorem example21_22InverseDomain_dense :
    Dense example21_22InverseOperator.dom := by
  -- The generic dense-domain theorem applies directly to this strictly positive weight sequence.
  simpa [example21_22InverseOperator_dom_eq_inverseDomain, example21_22InverseDomain] using
    (HilbertBasis.diagonalInverseDomain_dense example21_22Basis example21_22Weight)

/-- For Example 21.22 (9), the domain of the inverse operator is a proper linear subspace of
`ℓ²(ℕ, ℝ)`. -/
theorem example21_22InverseDomain_ne_univ :
    example21_22InverseDomain ≠ ⊤ := by
  -- Properness follows from the fact that the weights tend to `0`.
  simpa [example21_22InverseDomain] using
    (HilbertBasis.diagonalInverseDomain_ne_univ
      example21_22Basis example21_22Weight weightTendstoZero)

/-- Auxiliary support theorem: the coordinate inverse map is nowhere locally bounded on its natural
domain `example21_22InverseDomain`. -/
theorem example21_22InverseLinearMap_nowhereLocallyBounded :
    ∀ x : example21_22InverseDomain,
      ¬ Filter.IsBoundedUnder (· ≤ ·) (𝓝 x)
        (fun y : example21_22InverseDomain ↦ ‖example21_22InverseLinearMap y‖) := by
  intro x hbounded
  -- Translate the spike sequence to the point `x` and pull the neighborhood bound back to `atTop`.
  have htranslate :
      Tendsto (fun n ↦ x + inverseSpike n) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.add inverseSpike_tendsto_zero_subtype
  have hshifted :
      Filter.IsBoundedUnder (· ≤ ·) atTop
        (fun n ↦ ‖example21_22InverseLinearMap (x + inverseSpike n)‖) := by
    exact htranslate.isBoundedUnder_comp hbounded
  have hshiftedPlus :
      Filter.IsBoundedUnder (· ≤ ·) atTop
        (fun n ↦ ‖example21_22InverseLinearMap (x + inverseSpike n)‖ +
          ‖example21_22InverseLinearMap x‖) := by
    have hmono : Monotone (fun t : ℝ ↦ t + ‖example21_22InverseLinearMap x‖) := by
      intro a b hab
      simpa [add_comm] using add_le_add_right hab ‖example21_22InverseLinearMap x‖
    exact
      hmono.isBoundedUnder_le_comp hshifted
  have hnatBounded :
      Filter.IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ ↦ (n : ℝ)) := by
    refine hshiftedPlus.mono_le ?_
    refine Filter.Eventually.of_forall ?_
    intro n
    -- The triangle inequality compares the translated image with the spike image.
    have htriangle :
        ‖example21_22InverseLinearMap (inverseSpike n)‖ ≤
          ‖example21_22InverseLinearMap (x + inverseSpike n)‖ +
            ‖example21_22InverseLinearMap x‖ := by
      simpa [map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (norm_sub_le
          (example21_22InverseLinearMap (x + inverseSpike n))
          (example21_22InverseLinearMap x))
    simpa [norm_inverseLinearMap_inverseSpike n] using htriangle
  exact
    (not_isBoundedUnder_of_tendsto_atTop
      (show Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop from tendsto_natCast_atTop_atTop))
      hnatBounded

/-- For Example 21.22 (10), the inverse operator `B = A⁻¹` is nowhere locally bounded on
`ℓ²(ℕ, ℝ)`. -/
theorem example21_22InverseOperator_nowhereLocallyBounded :
    ∀ x : L2, ¬ example21_22InverseOperator.IsLocallyBoundedAt x := by
  have hdense : Dense (example21_22InverseDomain : Set L2) := by
    simpa [example21_22InverseDomain] using
      (HilbertBasis.diagonalInverseDomain_dense example21_22Basis example21_22Weight)
  have hproper : (example21_22InverseDomain : Set L2) ≠ Set.univ := by
    simpa using example21_22InverseDomain_ne_univ
  have hinterior : interior (example21_22InverseDomain : Set L2) = ∅ := by
    -- A dense proper linear subspace of a Hilbert space has empty interior.
    simpa [example21_22InverseDomain] using
      (HilbertBasis.diagonalInverseDomain_interior_eq_empty
        example21_22Basis example21_22Weight hdense hproper)
  have hfrontier : frontier example21_22InverseOperator.dom = Set.univ := by
    -- Dense closure plus empty interior forces the full-space frontier.
    rw [example21_22InverseOperator_dom_eq_inverseDomain, frontier, hdense.closure_eq, hinterior]
    simp
  intro x hloc
  have hxfrontier : x ∈ frontier example21_22InverseOperator.dom := by
    simp [hfrontier]
  exact
    ((SetValuedOperator.isLocallyBoundedAt_iff_not_mem_frontier_dom_of_maximal
      example21_22InverseOperator example21_22InverseOperator_isMaximallyMonotone x).1 hloc)
      hxfrontier

/-- Auxiliary support theorem: the coordinate inverse map is nowhere continuous on its natural
domain `example21_22InverseDomain`. -/
theorem example21_22InverseLinearMap_nowhereContinuous :
    ∀ x : example21_22InverseDomain, ¬ ContinuousAt example21_22InverseLinearMap x := by
  intro x hcont
  -- Continuity of the normed map would force boundedness of the norm on the neighborhood filter.
  exact
    example21_22InverseLinearMap_nowhereLocallyBounded x
      (hcont.norm.isBoundedUnder_le)

/-- The canonical selection of `example21_22InverseOperator` on its domain is the coordinate
inverse map on `example21_22InverseDomain`. -/
def example21_22InverseOperatorSelection : example21_22InverseOperator.dom → L2 :=
  fun z ↦ example21_22InverseLinearMap ⟨z.1, (mem_dom_example21_22InverseOperator_iff z.1).mp z.2⟩

/-- Evaluating the canonical selection uses the coordinate inverse map on the corresponding domain
point. -/
@[simp] theorem example21_22InverseOperatorSelection_apply
    (z : example21_22InverseOperator.dom) :
    example21_22InverseOperatorSelection z =
      example21_22InverseLinearMap
        ⟨z.1, (mem_dom_example21_22InverseOperator_iff z.1).mp z.2⟩ := rfl

/-- Example 21.22 (11): on its operator domain, the inverse operator `B = A⁻¹` is nowhere
continuous. -/
theorem example21_22InverseOperator_nowhereContinuous :
    ∀ x : example21_22InverseOperator.dom,
      ¬ SetValuedOperator.SelectionContinuousAt
        example21_22InverseOperator example21_22InverseOperatorSelection x := by
  intro x hselection
  have hselectionAt : ContinuousAt example21_22InverseOperatorSelection x := by
    -- Unfold the selection continuity predicate at the current domain point.
    exact
      (SetValuedOperator.selectionContinuousAt_iff
        example21_22InverseOperator example21_22InverseOperatorSelection x.1).1
        hselection x.2
  let y : example21_22InverseDomain :=
    ⟨x.1, (mem_dom_example21_22InverseOperator_iff x.1).mp x.2⟩
  let toDom : example21_22InverseDomain → example21_22InverseOperator.dom := fun z ↦
    ⟨z.1, (mem_dom_example21_22InverseOperator_iff z.1).mpr z.2⟩
  have htoDom : Continuous toDom := by
    -- The two domain subtypes differ only by the domain predicate proof.
    exact
      Continuous.subtype_mk continuous_subtype_val
        (fun z ↦ (mem_dom_example21_22InverseOperator_iff z.1).mpr z.2)
  have hy : toDom y = x := by
    -- Both subtype points have the same underlying vector.
    ext
    rfl
  have hlinearAt : ContinuousAt example21_22InverseLinearMap y := by
    -- Compose the continuous selection with the canonical inclusion from the inverse domain.
    have hcomp : ContinuousAt (example21_22InverseOperatorSelection ∘ toDom) y := by
      exact hselectionAt.comp (by simpa [hy] using htoDom.continuousAt)
    simpa [example21_22InverseOperatorSelection, toDom, y] using hcomp
  exact example21_22InverseLinearMap_nowhereContinuous y hlinearAt
