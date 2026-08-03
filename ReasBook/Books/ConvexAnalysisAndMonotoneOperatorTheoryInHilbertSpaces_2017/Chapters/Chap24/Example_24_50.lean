import BauschkeLean.Chap07.Definition_7_8
import BauschkeLean.Chap07.Exercise_7_1
import BauschkeLean.Chap07.Exercise_7_9
import BauschkeLean.Chap09.Remark_9_37
import BauschkeLean.Chap24.Definition_24_48
import BauschkeLean.Chap24.CoordinatePermutationInvariant
import BauschkeLean.Chap24.Example_24_40
import BauschkeLean.Chap13.Example_13_41
import BauschkeLean.Chap24.Proposition_24_12
import BauschkeLean.Chap24.Proposition_24_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped EuclideanSpace InnerProductSpace Pointwise

namespace ERealFunction

noncomputable section

-- Semantic recall note: `lean_leansearch` did not surface a ready-made finite-dimensional Burg
-- entropy prox theorem, so this item follows the local Chapter 24 owners from Example 24.40 and
-- Proposition 24.12, and uses Proposition 24.17 directly for the constant-weight `ℓ¹` penalty.

section Euclidean

variable {N : ℕ}

/-- The finite-dimensional negative Burg entropy on `ℝ^N`, obtained by transporting the
coordinatewise Hilbert-sum owner of the scalar negative Burg entropy from Example 24.40. -/
abbrev negativeBurgEntropyFinite :
    EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    directSumFunction (fun _ : Fin N ↦ negativeBurgEntropyIoi)
      ((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm x)

/-- Helper for Example 24.50: the finite-dimensional negative Burg entropy is the canonical
finite direct sum of the scalar Burg owner after transporting across `lpPiLpₗᵢ`. -/
private theorem negativeBurgEntropyFinite_asDirectSum
    (x : EuclideanSpace ℝ (Fin N)) :
    (negativeBurgEntropyFinite x : EReal) =
      (directSumFunction
        (fun _ : Fin N ↦ negativeBurgEntropyIoi)
        ((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm x) : EReal) := by
  rfl

/-- The finite-dimensional negative Burg entropy is invariant under coordinate permutations. -/
theorem negativeBurgEntropyFinite_coordinatePermutationInvariant :
    CoordinatePermutationInvariant
      (negativeBurgEntropyFinite : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal)) := by
  intro σ x
  apply Subtype.ext
  -- Rewrite both sides to the finite direct-sum owner and reindex the finite sum.
  rw [negativeBurgEntropyFinite_asDirectSum, negativeBurgEntropyFinite_asDirectSum]
  calc
    ∑ i, (negativeBurgEntropyIoi
        (((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm (permuteCoordVec σ x)) i) : EReal)
        =
        ∑ i, (negativeBurgEntropyIoi (x (σ.symm i)) : EReal) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [coe_lpPiLpₗᵢ_symm]
          simp [permuteCoordVec]
    _ = ∑ i, (negativeBurgEntropyIoi (x i) : EReal) := by
          simpa using
            (Fintype.sum_equiv σ.symm
              (fun i : Fin N ↦ (negativeBurgEntropyIoi (x (σ.symm i)) : EReal))
              (fun i : Fin N ↦ (negativeBurgEntropyIoi (x i) : EReal))
              (fun _ ↦ rfl))

/-- The constant weight vector `(μ, ..., μ)` on `ℝ^N`. -/
private abbrev constantWeightVector (μ : PosReal) : EuclideanSpace ℝ (Fin N) :=
  (EuclideanSpace.equiv (Fin N) ℝ).symm fun _ : Fin N ↦ (μ : ℝ)

private theorem constantWeightVector_nonneg (μ : PosReal) :
    ∀ i : Fin N, 0 ≤ constantWeightVector μ i := by
  intro i
  simp [constantWeightVector, μ.2.le]

/-- The constant-weight coordinatewise absolute-value penalty `x ↦ μ ‖x‖₁`. -/
abbrev constantWeightAbsPenalty (μ : PosReal) :
    EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal) :=
  weightedCoordinateAbsPenalty (constantWeightVector μ)

@[simp] theorem constantWeightAbsPenalty_apply
    (μ : PosReal) (x : EuclideanSpace ℝ (Fin N)) :
    (constantWeightAbsPenalty μ x : EReal) = (((μ : ℝ) * ‖x‖_[1] : ℝ) : EReal) := by
  rw [weightedCoordinateAbsPenalty_apply]
  rw [EuclideanSpace.lpNorm_apply]
  rw [PiLp.norm_eq_of_L1]
  simp [constantWeightVector, Finset.mul_sum, Real.norm_eq_abs]

private theorem constantWeightAbsPenalty_apply_eq_weightedCoordinateAbsPenalty_constant
    (μ : PosReal) (x : EuclideanSpace ℝ (Fin N)) :
    (constantWeightAbsPenalty μ x : EReal) =
      (weightedCoordinateAbsPenalty (constantWeightVector μ) x : EReal) := by
  rfl

@[simp] theorem constantWeightAbsPenalty_mem_gammaZero (μ : PosReal) :
    constantWeightAbsPenalty μ ∈ Γ₀(EuclideanSpace ℝ (Fin N)) := by
  simpa [constantWeightAbsPenalty] using
    weightedCoordinateAbsPenalty_mem_gammaZero
      (constantWeightVector μ)
      (constantWeightVector_nonneg μ)

/-- The sum of the finite-dimensional negative Burg entropy and the constant-weight `ℓ¹`
penalty `x ↦ μ ‖x‖₁`. -/
abbrev negativeBurgEntropyWithConstantWeightAbsPenalty (μ : PosReal) :
    EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal) :=
  negativeBurgEntropyFinite + constantWeightAbsPenalty μ

/-- Helper for Example 24.50: on the finite `ℓ²` direct sum, the coordinatewise proximal vector is
the packaged Chapter 24 Hilbert-sum coordinatewise proximal map. -/
private def directSumCoordinatewiseProx
    (f : Fin N → ℝ → Set.Ioi (⊥ : EReal))
    (hf : ∀ i, f i ∈ Γ₀(ℝ)) :
    lp (fun _ : Fin N ↦ ℝ) 2 → lp (fun _ : Fin N ↦ ℝ) 2 :=
  hilbertSumCoordinatewiseProx f hf

/-- Helper for Example 24.50: evaluating the finite coordinatewise proximal vector returns the
scalar proximal value in that coordinate. -/
@[simp] private theorem directSumCoordinatewiseProx_apply
    (f : Fin N → ℝ → Set.Ioi (⊥ : EReal))
    (hf : ∀ i, f i ∈ Γ₀(ℝ))
    (x : lp (fun _ : Fin N ↦ ℝ) 2) (i : Fin N) :
    directSumCoordinatewiseProx f hf x i = Prox[f i, hf i] (x i) :=
  rfl

/-- The box `[-μ, μ]^N`, viewed canonically as the scalar multiple of the `ℓ^∞` closed unit
ball in `ℝ^N`. -/
def burgThresholdBox (μ : PosReal) : Set (EuclideanSpace ℝ (Fin N)) :=
  (μ : ℝ) • (Set.lpClosedUnitBall N ⊤)

/-- A vector lies in `burgThresholdBox μ` exactly when each coordinate satisfies `|xᵢ| ≤ μ`. -/
theorem mem_burgThresholdBox_iff (μ : PosReal) (x : EuclideanSpace ℝ (Fin N)) :
    x ∈ burgThresholdBox μ ↔ ∀ i : Fin N, |x i| ≤ (μ : ℝ) := by
  -- Rewrite membership in the scaled box to membership of the rescaled vector in the unit ball.
  rw [burgThresholdBox, Set.mem_smul_set_iff_inv_smul_mem₀ μ.2.ne']
  rw [Set.mem_lpClosedUnitBall_iff, EuclideanSpace.lpNorm_apply, PiLp.norm_toLp, Pi.norm_def]
  constructor
  · intro hx i
    -- A coordinate is bounded by the supremum defining the `ℓ^∞` norm.
    have hi' :
        ‖((EuclideanSpace.equiv (Fin N) ℝ) (((μ : ℝ)⁻¹ • x)) i)‖₊ ≤
          Finset.univ.sup
            (fun j : Fin N ↦ ‖((EuclideanSpace.equiv (Fin N) ℝ) (((μ : ℝ)⁻¹ • x)) j)‖₊) := by
      exact Finset.le_sup (f := fun j : Fin N ↦
        ‖((EuclideanSpace.equiv (Fin N) ℝ) (((μ : ℝ)⁻¹ • x)) j)‖₊) (Finset.mem_univ i)
    have hsup :
        Finset.univ.sup
            (fun j : Fin N ↦ ‖((EuclideanSpace.equiv (Fin N) ℝ) (((μ : ℝ)⁻¹ • x)) j)‖₊) ≤
          (1 : NNReal) := by
      exact_mod_cast hx
    have hi :
        ‖((EuclideanSpace.equiv (Fin N) ℝ) (((μ : ℝ)⁻¹ • x)) i)‖ ≤ 1 := by
      exact_mod_cast le_trans hi' hsup
    have hdiv : |x i| / (μ : ℝ) ≤ 1 := by
      simpa [div_eq_mul_inv, Pi.smul_apply, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos μ.2,
        mul_comm]
        using hi
    simpa [one_mul] using (div_le_iff₀ μ.2).1 hdiv
  · intro hx
    -- Coordinatewise bounds control every term in the supremum defining the `ℓ^∞` norm.
    have hsup :
        Finset.univ.sup
            (fun j : Fin N ↦ ‖((EuclideanSpace.equiv (Fin N) ℝ) (((μ : ℝ)⁻¹ • x)) j)‖₊) ≤
          (1 : NNReal) := by
      refine Finset.sup_le ?_
      intro i hi
      have hdiv : |x i| / (μ : ℝ) ≤ 1 := by
        exact (div_le_iff₀ μ.2).2 (by simpa [one_mul] using hx i)
      have hcoord :
          ‖((EuclideanSpace.equiv (Fin N) ℝ) (((μ : ℝ)⁻¹ • x)) i)‖ ≤ 1 := by
        simpa [div_eq_mul_inv, Pi.smul_apply, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos μ.2,
          mul_comm]
          using hdiv
      exact_mod_cast hcoord
    exact_mod_cast hsup

/-- The finite-dimensional negative Burg entropy belongs to `Γ₀(ℝ^N)`. -/
theorem negativeBurgEntropyFinite_mem_gammaZero :
    negativeBurgEntropyFinite ∈ Γ₀(EuclideanSpace ℝ (Fin N)) := by
  -- Transport `Γ₀` membership across the Euclidean/`lp` equivalence.
  let f : Fin N → ℝ → Set.Ioi (⊥ : EReal) := fun _ : Fin N ↦ negativeBurgEntropyIoi
  let e : EuclideanSpace ℝ (Fin N) ≃L[ℝ] lp (fun _ : Fin N ↦ ℝ) 2 :=
    ((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm.toContinuousLinearEquiv)
  let F : lp (fun _ : Fin N ↦ ℝ) 2 → Set.Ioi (⊥ : EReal) := directSumFunction f
  have hF : F ∈ Γ₀(lp (fun _ : Fin N ↦ ℝ) 2) :=
    directSumFunction_mem_gammaZero_of_forall_mem_gammaZero
      (f := f)
      (hf := fun _ ↦ negativeBurgEntropyIoi_mem_gammaZero)
  simpa [negativeBurgEntropyFinite, f, F, e] using
    (mem_gammaZero_comp_continuousLinearEquiv hF e)

/-- Helper for Example 24.50: the finite-dimensional Burg prox is the Euclidean transport of the
canonical finite direct-sum proximal map. -/
private theorem prox_negativeBurgEntropyFinite_eq_directSumCoordinatewiseProx
    (x : EuclideanSpace ℝ (Fin N)) :
    Prox[negativeBurgEntropyFinite, negativeBurgEntropyFinite_mem_gammaZero] x =
      (lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ)
        (directSumCoordinatewiseProx
          (fun _ : Fin N ↦ negativeBurgEntropyIoi)
          (fun _ : Fin N ↦ negativeBurgEntropyIoi_mem_gammaZero)
          ((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm x)) := by
  let hγ : negativeBurgEntropyFinite ∈ Γ₀(EuclideanSpace ℝ (Fin N)) :=
    negativeBurgEntropyFinite_mem_gammaZero
  change Prox[negativeBurgEntropyFinite, hγ] x =
      (lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ)
        (directSumCoordinatewiseProx
          (fun _ : Fin N ↦ negativeBurgEntropyIoi)
          (fun _ : Fin N ↦ negativeBurgEntropyIoi_mem_gammaZero)
          ((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm x))
  let e : lp (fun _ : Fin N ↦ ℝ) 2 ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N) :=
    lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ
  let f : Fin N → ℝ → Set.Ioi (⊥ : EReal) := fun _ : Fin N ↦ negativeBurgEntropyIoi
  let hf : ∀ i, f i ∈ Γ₀(ℝ) := fun _ : Fin N ↦ negativeBurgEntropyIoi_mem_gammaZero
  let F : lp (fun _ : Fin N ↦ ℝ) 2 → Set.Ioi (⊥ : EReal) := hilbertSum f
  have hF_eq :
      F = directSumFunction f := by
    funext z
    apply Subtype.ext
    rw [hilbertSum_apply]
    simpa [F, f] using (directSumFunction_coe_eq_hilbertSumFunction f z).symm
  have hF : F ∈ Γ₀(lp (fun _ : Fin N ↦ ℝ) 2) := by
    rw [hF_eq]
    exact directSumFunction_mem_gammaZero_of_forall_mem_gammaZero f hf
  let xLp := e.symm x
  let pLp := directSumCoordinatewiseProx f hf xLp
  have hpLp_eq : pLp = Prox[F, hF] xLp := by
    simpa [F, pLp, directSumCoordinatewiseProx] using
      (prox_hilbertSum_eq_coordinatewise_of_mem_gammaZero (φ := f) hf hF xLp).symm
  have hpLp : IsProxPoint F xLp pLp := by
    rw [hpLp_eq]
    simpa [F, xLp] using
      proximityOperator_isProxPoint F
        (hasUniqueProxPoint_of_mem_gammaZero (f := F) hF)
        xLp
  have hp :
      IsProxPoint negativeBurgEntropyFinite x (e pLp) := by
    rw [isProxPoint_iff_forall_inner_add_le negativeBurgEntropyFinite hγ.2]
    intro y
    let yLp := e.symm y
    have hvar :=
      (isProxPoint_iff_forall_inner_add_le F hF.2 xLp pLp).1 hpLp yLp
    have hinner :
        ⟪y - e pLp, x - e pLp⟫_ℝ = ⟪yLp - pLp, xLp - pLp⟫_ℝ := by
      simpa [xLp, yLp, e] using
        (e.inner_map_map (yLp - pLp) (xLp - pLp))
    have hpLp_value :
        (negativeBurgEntropyFinite (e pLp) : EReal) = (F pLp : EReal) := by
      simpa [hF_eq, f, e] using negativeBurgEntropyFinite_asDirectSum (e pLp)
    have hy_value :
        (F yLp : EReal) = (negativeBurgEntropyFinite y : EReal) := by
      simpa [hF_eq, f, yLp, e] using (negativeBurgEntropyFinite_asDirectSum y).symm
    calc
      (⟪y - e pLp, x - e pLp⟫_ℝ : EReal) + (negativeBurgEntropyFinite (e pLp) : EReal)
          = (⟪yLp - pLp, xLp - pLp⟫_ℝ : EReal) + (F pLp : EReal) := by
              rw [hinner, hpLp_value]
      _ ≤ (F yLp : EReal) := hvar
      _ = (negativeBurgEntropyFinite y : EReal) := hy_value
  have hprox :
      e pLp = Prox[negativeBurgEntropyFinite, hγ] x :=
    eq_proximityOperator_of_isProxPoint
      negativeBurgEntropyFinite
      (hasUniqueProxPoint_of_mem_gammaZero (f := negativeBurgEntropyFinite) hγ)
      hp
  simpa [hγ, pLp, e] using hprox.symm

/-- Helper for Example 24.50: the finite-dimensional Burg prox is obtained by applying the scalar
quadratic-root formula coordinatewise. -/
private theorem prox_negativeBurgEntropyFinite_eq_coordinatewise
    (x : EuclideanSpace ℝ (Fin N)) :
    Prox[negativeBurgEntropyFinite, negativeBurgEntropyFinite_mem_gammaZero] x =
      (EuclideanSpace.equiv (Fin N) ℝ).symm
        (fun i : Fin N ↦ (x i + Real.sqrt (x i ^ (2 : ℕ) + 4)) / 2) := by
  -- Reduce the finite-dimensional prox to the canonical scalar Burg prox in each coordinate.
  ext i
  rw [prox_negativeBurgEntropyFinite_eq_directSumCoordinatewiseProx]
  change
    directSumCoordinatewiseProx
      (fun _ : Fin N ↦ negativeBurgEntropyIoi)
      (fun _ : Fin N ↦ negativeBurgEntropyIoi_mem_gammaZero)
      ((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm x) i =
      (x i + Real.sqrt (x i ^ (2 : ℕ) + 4)) / 2
  rw [directSumCoordinatewiseProx_apply]
  simpa [ERealFunction.scaledProximityOperator] using
    congrFun (prox_negativeBurgEntropy_eq (1 : PosReal))
      (((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm x) i)

/-- Helper for Example 24.50: evaluating the finite-dimensional Burg prox in one coordinate gives
the scalar quadratic-root formula. -/
@[simp] private theorem prox_negativeBurgEntropyFinite_eq_coordinatewise_apply
    (x : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    Prox[negativeBurgEntropyFinite, negativeBurgEntropyFinite_mem_gammaZero] x i =
      (x i + Real.sqrt (x i ^ (2 : ℕ) + 4)) / 2 := by
  -- Read the `i`th coordinate of the vector-valued Burg prox formula.
  simpa using congrArg (fun v : EuclideanSpace ℝ (Fin N) ↦ v i)
    (prox_negativeBurgEntropyFinite_eq_coordinatewise x)

/-- Helper for Example 24.50: the scalar Burg quadratic root is always strictly positive. -/
private theorem positiveBurgRoot (a : ℝ) :
    0 < (a + Real.sqrt (a ^ (2 : ℕ) + 4)) / 2 := by
  have hdisc_nonneg : 0 ≤ a ^ (2 : ℕ) + 4 := by
    nlinarith [sq_nonneg a]
  have hdisc_gt : a ^ (2 : ℕ) < a ^ (2 : ℕ) + 4 := by
    nlinarith
  have habs_lt : |a| < Real.sqrt (a ^ (2 : ℕ) + 4) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg a) hdisc_gt
  have hnum_pos : 0 < a + Real.sqrt (a ^ (2 : ℕ) + 4) := by
    nlinarith [neg_abs_le a, habs_lt]
  exact div_pos hnum_pos (by norm_num)

/-- Every point where the finite-dimensional negative Burg entropy has a subgradient lies in the
strict positive orthant. -/
theorem negativeBurgEntropyFinite_subdifferential_dom_subset_strictOrthant :
    SetValuedOperator.dom (∂ negativeBurgEntropyFinite) ⊆
      {p : EuclideanSpace ℝ (Fin N) | ∀ i, 0 < p i} := by
  intro p hp i
  rcases (SetValuedOperator.mem_dom_iff
    (A := ∂ negativeBurgEntropyFinite) (x := p)).mp hp with ⟨u, hu⟩
  have hprox :
      p = Prox[negativeBurgEntropyFinite, negativeBurgEntropyFinite_mem_gammaZero] (p + u) := by
    -- Read the subgradient membership back as the proximal-point identity.
    exact
      (eq_proximityOperator_iff_sub_mem_subdifferential
        (f := negativeBurgEntropyFinite)
        (hf := negativeBurgEntropyFinite_mem_gammaZero)
        (x := p + u)
        (p := p)).2
        (by simpa using hu)
  have hpcoord :
      p i = (((p + u) i) + Real.sqrt (((p + u) i) ^ (2 : ℕ) + 4)) / 2 := by
    calc
      p i =
          (Prox[negativeBurgEntropyFinite, negativeBurgEntropyFinite_mem_gammaZero] (p + u)) i := by
        simpa using congrArg (fun v : EuclideanSpace ℝ (Fin N) ↦ v i) hprox
      _ = (((p + u) i) + Real.sqrt (((p + u) i) ^ (2 : ℕ) + 4)) / 2 :=
        prox_negativeBurgEntropyFinite_eq_coordinatewise_apply (p + u) i
  -- Positivity follows from the scalar Burg root formula.
  rw [hpcoord]
  exact positiveBurgRoot ((p + u) i)

/-- The sum `f + μ ‖·‖₁` from Example 24.50 belongs to `Γ₀(ℝ^N)`. -/
theorem negativeBurgEntropyWithConstantWeightAbsPenalty_mem_gammaZero
    (μ : PosReal) :
    negativeBurgEntropyWithConstantWeightAbsPenalty μ ∈
      Γ₀(EuclideanSpace ℝ (Fin N)) := by
  have hPenalty :
      (constantWeightAbsPenalty μ : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal)) =
        weightedCoordinateAbsPenalty (constantWeightVector μ) := by
    funext x
    apply Subtype.ext
    exact constantWeightAbsPenalty_apply_eq_weightedCoordinateAbsPenalty_constant μ x
  rw [negativeBurgEntropyWithConstantWeightAbsPenalty, hPenalty]
  exact
    add_weightedCoordinateAbsPenalty_mem_gammaZero
      negativeBurgEntropyFinite_mem_gammaZero
      (constantWeightVector μ)
      (constantWeightVector_nonneg μ)

/-- Example 24.50 (1): if `f` is the negative Burg entropy on `ℝ^N` and `μ ∈ ℝ_{++}`, then
`Prox_(f + μ ‖·‖₁)(x)` is given coordinatewise by
`((ξᵢ - μ + sqrt (ξᵢ^2 - 2 μ ξᵢ + μ^2 + 4)) / 2)ᵢ`. -/
theorem prox_negativeBurgEntropyWithConstantWeightAbsPenalty_eq_coordinatewise
    (μ : PosReal) (x : EuclideanSpace ℝ (Fin N)) :
    Prox[
      negativeBurgEntropyWithConstantWeightAbsPenalty μ,
      negativeBurgEntropyWithConstantWeightAbsPenalty_mem_gammaZero μ
    ] x =
      (EuclideanSpace.equiv (Fin N) ℝ).symm
        (fun i : Fin N ↦
          (x i - (μ : ℝ) +
            Real.sqrt
              (x i ^ (2 : ℕ) - 2 * (μ : ℝ) * x i + (μ : ℝ) ^ (2 : ℕ) + 4)) / 2) := by
  let hμγ :
      negativeBurgEntropyWithConstantWeightAbsPenalty μ ∈ Γ₀(EuclideanSpace ℝ (Fin N)) :=
    negativeBurgEntropyWithConstantWeightAbsPenalty_mem_gammaZero μ
  change Prox[
      negativeBurgEntropyWithConstantWeightAbsPenalty μ,
      hμγ
    ] x =
      (EuclideanSpace.equiv (Fin N) ℝ).symm
        (fun i : Fin N ↦
          (x i - (μ : ℝ) +
            Real.sqrt
              (x i ^ (2 : ℕ) - 2 * (μ : ℝ) * x i + (μ : ℝ) ^ (2 : ℕ) + 4)) / 2)
  have hPenalty :
      (constantWeightAbsPenalty μ : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal)) =
        weightedCoordinateAbsPenalty (constantWeightVector μ) := by
    funext z
    apply Subtype.ext
    exact constantWeightAbsPenalty_apply_eq_weightedCoordinateAbsPenalty_constant μ z
  let hfg :
      negativeBurgEntropyFinite + weightedCoordinateAbsPenalty (constantWeightVector μ) ∈
        Γ₀(EuclideanSpace ℝ (Fin N)) :=
    add_weightedCoordinateAbsPenalty_mem_gammaZero
      negativeBurgEntropyFinite_mem_gammaZero
      (constantWeightVector μ)
      (constantWeightVector_nonneg μ)
  have hshift :
      Prox[
        negativeBurgEntropyFinite + weightedCoordinateAbsPenalty (constantWeightVector μ),
        hfg
      ] x =
        Prox[negativeBurgEntropyFinite, negativeBurgEntropyFinite_mem_gammaZero]
          (x - constantWeightVector μ) := by
    simpa [hfg] using
      proximityOperator_add_weightedCoordinateAbsPenalty_eq_proximityOperator_sub_weights
        negativeBurgEntropyFinite
        negativeBurgEntropyFinite_mem_gammaZero
        negativeBurgEntropyFinite_subdifferential_dom_subset_strictOrthant
        (constantWeightVector μ)
        (constantWeightVector_nonneg μ)
        x
  -- Route correction: first rewrite the sum through the canonical weighted-penalty owner,
  -- then expand the shifted scalar Burg formula coordinatewise.
  ext i
  have hdisc :
      (x i - (μ : ℝ)) ^ (2 : ℕ) + 4 =
        x i ^ (2 : ℕ) - 2 * (μ : ℝ) * x i + (μ : ℝ) ^ (2 : ℕ) + 4 := by
    ring_nf
  rw [show
      Prox[
        negativeBurgEntropyWithConstantWeightAbsPenalty μ,
        hμγ
      ] x =
        Prox[
          negativeBurgEntropyFinite + weightedCoordinateAbsPenalty (constantWeightVector μ),
          hfg
        ] x by
          simp [negativeBurgEntropyWithConstantWeightAbsPenalty, hPenalty]]
  rw [hshift, prox_negativeBurgEntropyFinite_eq_coordinatewise]
  simpa [constantWeightVector, hdisc]

/-- Example 24.50 (2): the constant-weight `ℓ¹` penalty `x ↦ μ ‖x‖₁` is the support function
`σ_Ω` of the box `Ω = [-μ, μ]^N`. -/
theorem constantWeightAbsPenalty_asEReal_eq_supportFunction_burgThresholdBox
    (μ : PosReal) :
    (constantWeightAbsPenalty μ).asEReal =
      σ[(burgThresholdBox μ : Set (EuclideanSpace ℝ (Fin N)))] := by
  -- Normalize the scaled `ℓ^∞` ball support function to the dual `ℓ¹` norm.
  have hsupp :
      σ[(burgThresholdBox μ : Set (EuclideanSpace ℝ (Fin N)))] =
        fun x : EuclideanSpace ℝ (Fin N) ↦ (((μ : ℝ) * ‖x‖_[1] : ℝ) : EReal) := by
    funext x
    have hconj : ENNReal.conjExponent (⊤ : ENNReal) = (1 : ENNReal) := by
      simp [ENNReal.conjExponent]
    have hscaled :=
      congrFun
        (supportFunction_comp_pos_smul_eq_mul_supportFunction
          (C := Set.lpClosedUnitBall N ⊤) μ.2)
        x
    calc
      σ[(burgThresholdBox μ : Set (EuclideanSpace ℝ (Fin N)))] x
          = (σ[Set.lpClosedUnitBall N ⊤] ∘ fun u : EuclideanSpace ℝ (Fin N) ↦ (μ : ℝ) • u) x := by
              simpa [burgThresholdBox] using
                (congrFun
                  (supportFunction_comp_smul_eq_supportFunction_smul_set
                    (C := Set.lpClosedUnitBall N ⊤) (ρ := (μ : ℝ)))
                  x).symm
      _ = ((μ : ℝ) : EReal) * σ[Set.lpClosedUnitBall N ⊤] x := by
            simpa using hscaled
      _ = ((μ : ℝ) : EReal) * (((‖x‖_[1] : ℝ) : EReal)) := by
            have hdual :
                σ[Set.lpClosedUnitBall N ⊤] x = (((‖x‖_[1] : ℝ) : EReal)) := by
              simpa [hconj] using
                congrFun (lpDualNorm_eq_lpNorm_conjExponent N ⊤ (by simp)) x
            rw [hdual]
      _ = (((μ : ℝ) * ‖x‖_[1] : ℝ) : EReal) := by
            rw [← EReal.coe_mul]
  funext x
  rw [Function.asEReal_apply, constantWeightAbsPenalty_apply]
  exact (congrFun hsupp x).symm

/-- Example 24.50 (3): for `0 < N`, the proximal map from Example 24.50 is not a proximal
thresholder on the box `Ω = [-μ, μ]^N`. -/
theorem prox_negativeBurgEntropyWithConstantWeightAbsPenalty_not_isProximalThresholderOn
    (hN : 0 < N) (μ : PosReal) :
    ¬ (Prox[
        negativeBurgEntropyWithConstantWeightAbsPenalty μ,
        negativeBurgEntropyWithConstantWeightAbsPenalty_mem_gammaZero μ
      ]).IsProximalThresholderOn
        (burgThresholdBox μ : Set (EuclideanSpace ℝ (Fin N))) := by
  let hμγ :
      negativeBurgEntropyWithConstantWeightAbsPenalty μ ∈ Γ₀(EuclideanSpace ℝ (Fin N)) :=
    negativeBurgEntropyWithConstantWeightAbsPenalty_mem_gammaZero μ
  change ¬ (Prox[
      negativeBurgEntropyWithConstantWeightAbsPenalty μ,
      hμγ
    ]).IsProximalThresholderOn
      (burgThresholdBox μ : Set (EuclideanSpace ℝ (Fin N)))
  intro hT
  have hzero_mem_box : (0 : EuclideanSpace ℝ (Fin N)) ∈ burgThresholdBox μ := by
    rw [mem_burgThresholdBox_iff]
    intro i
    simp [μ.2.le]
  have hzero_mem_preimage :
      (0 : EuclideanSpace ℝ (Fin N)) ∈
        (Prox[
          negativeBurgEntropyWithConstantWeightAbsPenalty μ,
          hμγ
        ]) ⁻¹' ({0} : Set (EuclideanSpace ℝ (Fin N))) := by
    rw [hT.zero_preimage_eq]
    exact hzero_mem_box
  have hzero_fixed :
      Prox[
        negativeBurgEntropyWithConstantWeightAbsPenalty μ,
        hμγ
      ] 0 = 0 := by
    simpa [Set.mem_preimage] using hzero_mem_preimage
  let i : Fin N := ⟨0, hN⟩
  have hpos :
      0 <
        (Prox[
          negativeBurgEntropyWithConstantWeightAbsPenalty μ,
          hμγ
        ] 0) i := by
    have hcoord :
        (Prox[
          negativeBurgEntropyWithConstantWeightAbsPenalty μ,
          hμγ
        ] 0) i =
          ((-(μ : ℝ)) + Real.sqrt ((μ : ℝ) ^ (2 : ℕ) + 4)) / 2 := by
      simpa [pow_two, hμγ] using
        congrArg
          (fun v : EuclideanSpace ℝ (Fin N) ↦ v i)
          (prox_negativeBurgEntropyWithConstantWeightAbsPenalty_eq_coordinatewise
            μ
            (0 : EuclideanSpace ℝ (Fin N)))
    have hroot : 0 < ((-(μ : ℝ)) + Real.sqrt ((μ : ℝ) ^ (2 : ℕ) + 4)) / 2 := by
      simpa [pow_two] using positiveBurgRoot (-(μ : ℝ))
    rw [hcoord]
    exact hroot
  have : False := by
    simpa [hzero_fixed] using hpos
  exact this.elim

end Euclidean

end

end ERealFunction
