import Mathlib.Analysis.InnerProductSpace.PiL2
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap12.Definition_12_16
import BauschkeLean.Chap12.Proposition_12_15
import BauschkeLean.Chap12.ProximityOperator
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap16.Proposition_16_10
import BauschkeLean.Chap16.Proposition_16_44
import BauschkeLean.Chap17.Proposition_17_41

-- Declarations for this item will be appended below by the statement pipeline.

open scoped EuclideanSpace InnerProductSpace Pointwise

namespace ERealFunction

noncomputable section

-- Semantic recall note: `lean_leansearch` did not surface a relevant prox-shift theorem for
-- this weighted absolute-value perturbation, so the owner/API choice here follows the local
-- `Γ₀`, `∂`, and `Prox` surfaces already used across Chapters 9, 12, and 16.

/-- Helper for Proposition 24.17: on `ℝ`, the real inner product is ordinary multiplication. -/
private theorem real_inner_eq_mul (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  simpa using (RCLike.inner_apply' a b)

/-- Helper for Proposition 24.17: the weighted coordinatewise `ℓ¹` penalty
`ξ ↦ ∑ i, μ i * |ξ i|` on `ℝ^N`, packaged as an `]-∞,+∞]`-valued function. -/
def weightedCoordinateAbsPenalty {N : ℕ} (μ : EuclideanSpace ℝ (Fin N)) :
    EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal) :=
  (fun ξ ↦ ∑ i, μ i * |ξ i|).toEReal

/-- Coercing `weightedCoordinateAbsPenalty μ` to `EReal` recovers the weighted coordinatewise
`ℓ¹` formula. -/
@[simp] theorem weightedCoordinateAbsPenalty_apply {N : ℕ}
    (μ ξ : EuclideanSpace ℝ (Fin N)) :
    (weightedCoordinateAbsPenalty μ ξ : EReal) = ((∑ i, μ i * |ξ i| : ℝ) : EReal) := by
  simp [weightedCoordinateAbsPenalty]

/-- If the weights are nonnegative, the weighted coordinatewise `ℓ¹` penalty is the sum of the
canonical scalar kernels `ξ ↦ μ i * |ξ|`. -/
@[simp] theorem weightedCoordinateAbsPenalty_apply_eq_sum_scaledNormKernel {N : ℕ}
    (μ : EuclideanSpace ℝ (Fin N)) (hμ : ∀ i, 0 ≤ μ i) (ξ : EuclideanSpace ℝ (Fin N)) :
    (weightedCoordinateAbsPenalty μ ξ : EReal) =
      ∑ i, (scaledNormKernel ⟨μ i, hμ i⟩ (ξ i) : EReal) := by
  have hsum :
      ∀ s : Finset (Fin N),
        (((s.sum fun i ↦ μ i * |ξ i| : ℝ) : EReal)) =
          s.sum fun i ↦ (((μ i * |ξ i| : ℝ) : EReal)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp
    | insert i s hi hs =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, EReal.coe_add, hs]
  calc
    (weightedCoordinateAbsPenalty μ ξ : EReal) = ((∑ i, μ i * |ξ i| : ℝ) : EReal) :=
      weightedCoordinateAbsPenalty_apply μ ξ
    _ = ∑ i, (((μ i * |ξ i| : ℝ) : EReal)) :=
      hsum Finset.univ
    _ = ∑ i, (scaledNormKernel ⟨μ i, hμ i⟩ (ξ i) : EReal) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp [scaledNormKernel_apply, Real.norm_eq_abs]

/-- Helper for Proposition 24.17: each coordinate penalty
`ξ ↦ μ i * |ξ i|` belongs to `Γ₀(ℝ^N)` when `μ i ≥ 0`. -/
private theorem coordinateAbsPenalty_mem_gammaZero {N : ℕ}
    (μ : EuclideanSpace ℝ (Fin N)) (hμ : ∀ i, 0 ≤ μ i) (i : Fin N) :
    (fun ξ : EuclideanSpace ℝ (Fin N) ↦ μ i * |ξ i|).toEReal ∈
      Γ₀(EuclideanSpace ℝ (Fin N)) := by
  -- Package the coordinatewise absolute-value kernel through the Chapter 12 real-to-`EReal`
  -- owner so the later sum proof can stay at the `Γ₀` level.
  refine real_toEReal_mem_gammaZero_of_continuous_convexOn_univ
    (H := EuclideanSpace ℝ (Fin N))
    (fun ξ : EuclideanSpace ℝ (Fin N) ↦ μ i * |ξ i|) ?_ ?_
  · -- Continuity comes from the coordinate projection, absolute value, and scalar multiplication.
    exact continuous_const.mul (((EuclideanSpace.proj (𝕜 := ℝ) i)).continuous.abs)
  · -- Convexity is the nonnegative scalar multiple of the convex norm on the `i`th coordinate.
    have habs :
        _root_.ConvexOn ℝ Set.univ (fun ξ : EuclideanSpace ℝ (Fin N) ↦ |ξ i|) := by
      simpa [Real.norm_eq_abs] using
        (convexOn_univ_norm : _root_.ConvexOn ℝ Set.univ (fun t : ℝ ↦ ‖t‖)).comp_linearMap
          (EuclideanSpace.projₗ (𝕜 := ℝ) i)
    simpa [smul_eq_mul] using
      (ConvexOn.smul
        (s := Set.univ)
        (f := fun ξ : EuclideanSpace ℝ (Fin N) ↦ |ξ i|)
        (c := μ i)
        (hμ i)
        habs)

/-- Helper for Proposition 24.17: at a point in the strict positive orthant, the real
representative `ξ ↦ ∑ i, μ i * |ξ i|` has gradient `μ`. -/
private theorem hasGradientAt_weightedCoordinateAbsPenalty_of_pos {N : ℕ}
    (μ : EuclideanSpace ℝ (Fin N))
    {p : EuclideanSpace ℝ (Fin N)} (hp : ∀ i, 0 < p i) :
    HasGradientAt (fun ξ : EuclideanSpace ℝ (Fin N) ↦ ∑ i, μ i * |ξ i|) μ p := by
  -- Differentiate each coordinate summand on the positive branch `|ξ i| = ξ i`, then sum the
  -- resulting coordinate projections and identify the total derivative with `toDual μ`.
  have hcoord :
      ∀ i : Fin N,
        HasFDerivAt (fun ξ : EuclideanSpace ℝ (Fin N) ↦ μ i * |ξ i|)
          (μ i • EuclideanSpace.proj (𝕜 := ℝ) i) p := by
    intro i
    have hproj :
        HasFDerivAt (fun ξ : EuclideanSpace ℝ (Fin N) ↦ ξ i)
          (EuclideanSpace.proj (𝕜 := ℝ) i) p :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt
    simpa [smul_eq_mul] using (hproj.abs_of_pos (hp i)).const_smul (μ i)
  have hsum :
      HasFDerivAt (fun ξ : EuclideanSpace ℝ (Fin N) ↦ ∑ i, μ i * |ξ i|)
        (∑ i : Fin N, μ i • EuclideanSpace.proj (𝕜 := ℝ) i) p := by
    simpa using (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ ↦ hcoord i)
  have hderiv_eq :
      (∑ i : Fin N, μ i • EuclideanSpace.proj (𝕜 := ℝ) i) =
        InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin N)) μ := by
    ext ξ
    rw [InnerProductSpace.toDual_apply_apply, PiLp.inner_apply]
    simp [real_inner_eq_mul]
  simpa [hderiv_eq] using hsum.hasGradientAt

/-- Helper for Proposition 24.17: a weighted coordinatewise absolute-value penalty with
nonnegative weights belongs to `Γ₀(ℝ^N)`. -/
theorem weightedCoordinateAbsPenalty_mem_gammaZero {N : ℕ}
    (μ : EuclideanSpace ℝ (Fin N)) (hμ : ∀ i, 0 ≤ μ i) :
    weightedCoordinateAbsPenalty μ ∈ Γ₀(EuclideanSpace ℝ (Fin N)) := by
  -- Package the whole penalty through the real-valued owner `ξ ↦ ∑ i, μ i * |ξ i|`.
  refine real_toEReal_mem_gammaZero_of_continuous_convexOn_univ
    (H := EuclideanSpace ℝ (Fin N))
    (fun ξ : EuclideanSpace ℝ (Fin N) ↦ ∑ i, μ i * |ξ i|) ?_ ?_
  · -- Continuity is preserved under finite sums of the continuous coordinate kernels.
    have hcont_term :
        ∀ i : Fin N, Continuous (fun ξ : EuclideanSpace ℝ (Fin N) ↦ μ i * |ξ i|) := by
      intro i
      exact continuous_const.mul (((EuclideanSpace.proj (𝕜 := ℝ) i)).continuous.abs)
    have hcont_sum :
        ∀ s : Finset (Fin N),
          Continuous
            (fun ξ : EuclideanSpace ℝ (Fin N) ↦ (s.sum fun j : Fin N ↦ μ j * |ξ j|)) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          simpa using (continuous_const : Continuous fun _ : EuclideanSpace ℝ (Fin N) ↦ (0 : ℝ))
      | insert i s hi hs =>
          simpa [Finset.sum_insert, hi] using (hcont_term i).add hs
    simpa using hcont_sum Finset.univ
  · -- Convexity follows by summing the convex coordinate kernels one at a time.
    have hconv_term :
        ∀ i : Fin N,
          _root_.ConvexOn ℝ Set.univ
            (fun ξ : EuclideanSpace ℝ (Fin N) ↦ μ i * |ξ i|) := by
      intro i
      have habs :
          _root_.ConvexOn ℝ Set.univ (fun ξ : EuclideanSpace ℝ (Fin N) ↦ |ξ i|) := by
        simpa [Real.norm_eq_abs] using
          (convexOn_univ_norm : _root_.ConvexOn ℝ Set.univ (fun t : ℝ ↦ ‖t‖)).comp_linearMap
            (EuclideanSpace.projₗ (𝕜 := ℝ) i)
      simpa [smul_eq_mul] using
        (ConvexOn.smul
          (s := Set.univ)
          (f := fun ξ : EuclideanSpace ℝ (Fin N) ↦ |ξ i|)
          (c := μ i)
          (hμ i)
          habs)
    have hconv_sum :
        ∀ s : Finset (Fin N),
          _root_.ConvexOn ℝ Set.univ
            (fun ξ : EuclideanSpace ℝ (Fin N) ↦ (s.sum fun j : Fin N ↦ μ j * |ξ j|)) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          simpa using
            (convexOn_const (𝕜 := ℝ) (s := Set.univ) (c := (0 : ℝ)) convex_univ)
      | insert i s hi hs =>
          simpa [Finset.sum_insert, hi] using (hconv_term i).add hs
    simpa [weightedCoordinateAbsPenalty] using hconv_sum Finset.univ

/-- Helper for Proposition 24.17: adding the weighted coordinatewise absolute-value penalty to a
member of `Γ₀(ℝ^N)` again yields a member of `Γ₀(ℝ^N)`. -/
theorem add_weightedCoordinateAbsPenalty_mem_gammaZero {N : ℕ}
    {f : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(EuclideanSpace ℝ (Fin N)))
    (μ : EuclideanSpace ℝ (Fin N)) (hμ : ∀ i, 0 ≤ μ i) :
    f + weightedCoordinateAbsPenalty μ ∈ Γ₀(EuclideanSpace ℝ (Fin N)) := by
  -- The penalty is finite everywhere, so the effective domains intersect at any effective-domain
  -- point of `f`.
  refine pointwiseAdd_mem_gammaZero f (weightedCoordinateAbsPenalty μ) hf
    (weightedCoordinateAbsPenalty_mem_gammaZero μ hμ) ?_
  rcases hf.2.nonempty with ⟨x, hx⟩
  refine ⟨x, hx, ?_⟩
  simp [weightedCoordinateAbsPenalty, Function.effectiveDomain_toEReal]

/-- Helper for Proposition 24.17: the weighted coordinatewise absolute-value penalty is finite
at every point of `ℝ^N`. -/
private theorem weightedCoordinateAbsPenalty_effectiveDomain_eq_univ {N : ℕ}
    (μ : EuclideanSpace ℝ (Fin N)) :
    effectiveDomain (weightedCoordinateAbsPenalty μ) =
      (Set.univ : Set (EuclideanSpace ℝ (Fin N))) := by
  -- The penalty is a `toEReal` lift of a real-valued function, so its effective domain is all
  -- of `ℝ^N`.
  ext ξ
  simp [weightedCoordinateAbsPenalty]

/-- Helper for Proposition 24.17: at a point whose coordinates are all strictly positive, the
subdifferential of the weighted coordinatewise absolute-value penalty is the singleton `{μ}`. -/
theorem subdifferential_weightedCoordinateAbsPenalty_eq_singleton_of_pos {N : ℕ}
    (μ : EuclideanSpace ℝ (Fin N)) (hμ : ∀ i, 0 ≤ μ i)
    {p : EuclideanSpace ℝ (Fin N)} (hp : ∀ i, 0 < p i) :
    (∂ weightedCoordinateAbsPenalty μ) p = ({μ} : Set (EuclideanSpace ℝ (Fin N))) := by
  -- Identify the subdifferential through the interior-gradient singleton theorem from Chapter 17.
  have hγ : weightedCoordinateAbsPenalty μ ∈ Γ₀(EuclideanSpace ℝ (Fin N)) :=
    weightedCoordinateAbsPenalty_mem_gammaZero μ hμ
  have hgrad :
      HasGradientAt
        (fun ξ : EuclideanSpace ℝ (Fin N) ↦
          (((weightedCoordinateAbsPenalty μ ξ : EReal).toReal) : ℝ))
        μ
        p := by
    simpa [weightedCoordinateAbsPenalty_apply] using
      hasGradientAt_weightedCoordinateAbsPenalty_of_pos μ hp
  have hp_int :
      p ∈ interior (effectiveDomain (weightedCoordinateAbsPenalty μ)) := by
    simp [weightedCoordinateAbsPenalty, Function.effectiveDomain_toEReal]
  simpa using subdifferential_eq_singleton_of_hasGradientAt hγ hp_int hgrad

/-- Helper for Proposition 24.17: at a point in the strict positive orthant, the weight vector
itself is a subgradient of the weighted coordinatewise absolute-value penalty. -/
theorem weights_mem_subdifferential_weightedCoordinateAbsPenalty_of_pos {N : ℕ}
    (μ : EuclideanSpace ℝ (Fin N)) (hμ : ∀ i, 0 ≤ μ i)
    {p : EuclideanSpace ℝ (Fin N)} (hp : ∀ i, 0 < p i) :
    μ ∈ (∂ weightedCoordinateAbsPenalty μ) p := by
  -- Collapse the singleton-valued subdifferential description to the required membership fact.
  rw [subdifferential_weightedCoordinateAbsPenalty_eq_singleton_of_pos μ hμ hp]
  simp

/-- Proposition 24.17: if `f ∈ Γ₀(ℝ^N)`, if `dom (∂ f)` is contained in the strict positive
orthant, and if `g(ξ) = ∑ i, μ i * |ξ i|` with `μ ∈ ℝ_+^N`, then
`Prox_{f + g} x = Prox_f (x - μ)`. -/
theorem proximityOperator_add_weightedCoordinateAbsPenalty_eq_proximityOperator_sub_weights
    {N : ℕ}
    (f : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal))
    (hf : f ∈ Γ₀(EuclideanSpace ℝ (Fin N)))
    (hsubdom :
      SetValuedOperator.dom (∂ f) ⊆
        {p : EuclideanSpace ℝ (Fin N) | ∀ i, 0 < p i})
    (μ : EuclideanSpace ℝ (Fin N))
    (hμ : ∀ i, 0 ≤ μ i)
    (x : EuclideanSpace ℝ (Fin N)) :
    Prox[f + weightedCoordinateAbsPenalty μ,
      add_weightedCoordinateAbsPenalty_mem_gammaZero hf μ hμ] x =
      Prox[f, hf] (x - μ) := by
  let g : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal) := weightedCoordinateAbsPenalty μ
  have hfg : f + g ∈ Γ₀(EuclideanSpace ℝ (Fin N)) :=
    add_weightedCoordinateAbsPenalty_mem_gammaZero hf μ hμ
  let p : EuclideanSpace ℝ (Fin N) := Prox[f, hf] (x - μ)
  -- Route correction: start from the shifted proximal point of `f` and push its residual
  -- forward through the one-sided sum inclusion from Proposition 16.6.
  have hp_resid : (x - μ) - p ∈ (∂ f) p := by
    simpa [p] using
      (eq_proximityOperator_iff_sub_mem_subdifferential hf (x - μ) p).1 rfl
  have hp_domf : p ∈ SetValuedOperator.dom (∂ f) := by
    rw [SetValuedOperator.mem_dom_iff]
    exact ⟨(x - μ) - p, hp_resid⟩
  have hp_pos : ∀ i, 0 < p i := hsubdom hp_domf
  have hμ_sub : μ ∈ (∂ g) p := by
    -- Positivity of the coordinates identifies the penalty subgradient with the weight vector.
    simpa [g] using
      weights_mem_subdifferential_weightedCoordinateAbsPenalty_of_pos μ hμ hp_pos
  have hμ_adjoint :
      μ ∈ ContinuousLinearMap.adjointImageSubdifferential
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin N))) g p := by
    -- For the identity map, the adjoint-image subdifferential is just the original one.
    simpa [ContinuousLinearMap.adjointImageSubdifferential] using hμ_sub
  have hx_sum :
      x - p ∈
        (∂ f) p +
          ContinuousLinearMap.adjointImageSubdifferential
            (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin N))) g p := by
    -- Combine the two component subgradients with the textbook algebra
    -- `((x - μ) - p) + μ = x - p`.
    have hdecomp : ((x - μ) - p) + μ = x - p := by
      abel_nf
    exact Set.mem_add.2 ⟨(x - μ) - p, hp_resid, μ, hμ_adjoint, hdecomp⟩
  have hp_sub : x - p ∈ (∂ (f + g)) p := by
    -- Proposition 16.6 upgrades the pair of component subgradients to a subgradient of `f + g`.
    simpa [Function.comp] using
      (subdifferential_add_adjoint_image_subset_subdifferential_add_comp
        f g (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin N))) p) hx_sum
  have hp_prox : p = Prox[f + g, hfg] x := by
    -- Read the residual condition back as the proximal-point identity for `f + g`.
    exact (eq_proximityOperator_iff_sub_mem_subdifferential hfg x p).2 hp_sub
  simpa [g, p] using hp_prox.symm

end

end ERealFunction
