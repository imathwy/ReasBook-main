import BauschkeLean.Chap06.Proposition_6_20
import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap16.Proposition_16_44
import BauschkeLean.Chap16.Corollary_16_50
import BauschkeLean.Chap16.Theorem_16_3
import BauschkeLean.Chap26.Proposition_26_12

open Set
open Filter
open SetValuedOperator
open scoped BigOperators InnerProductSpace Pointwise SetValuedOperator Topology

universe u

namespace ERealFunction

noncomputable section

-- Source/core/bridge triage:
-- - `source-facing`: Proposition 28.7 is the proximal recursion `(28.30)` for a finite family
--   `f : Fin (n + 2) → Γ₀(H)` together with weak convergence to `Argmin (∑ i, f i).asEReal`.
-- - `core/canonical`: the reusable owners are Corollary 16.50 for the finite-sum
--   subdifferential identity and Proposition 26.12 for the operator-level parallel splitting
--   recursion.
-- - `bridge/view`: the orbit predicate below keeps `(28.30)` on the proximal surface `Prox[γ, f i,
--   hf i]`, and the regularity bridge keeps the source three-way hypothesis while reducing it to
--   the Chapter 16 sum rule, reversing the finite family in the `dom f₁ ∩ ⋂ int (dom fᵢ)` branch.

section ParallelSplittingAlgorithm

variable {n : ℕ}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "ProductSpace" => lp (fun _ : Fin (n + 2) ↦ H) 2

/-- Helper for Proposition 28.7: the scaled proximal map `Prox[γ, f, hf]` is the resolvent of the
subdifferential `∂ f`. -/
private theorem resolventMapSubdifferential_eq_scaledProximityOperator
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (γ : PosReal) :
    SetValuedOperator.resolventMap (∂ f)
      (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf) γ = Prox[γ, f, hf] := by
  -- Compare the resolvent and prox operators on their singleton-valued set-valued realizations.
  have hrealizer :
      (SetValuedOperator.resolventMap (∂ f)
        (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf) γ).toSetValuedOperator =
        (Prox[γ, f, hf]).toSetValuedOperator := by
    calc
      (SetValuedOperator.resolventMap (∂ f)
          (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf) γ).toSetValuedOperator =
          J[((γ : ℝ) • (∂ f : SetValuedOperator H H))] := by
            simpa using
              SetValuedOperator.resolventMap_toSetValuedOperator_eq (∂ f)
                (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf) γ
      _ = (Prox[γ, f, hf]).toSetValuedOperator := by
            rw [← subdifferential_posReal_smul_eq_smul f γ, resolvent_def]
            simpa [scaledProximityOperator] using
              (singleton_proximityOperator_eq_inverse_add_subdifferential
                (smul_mem_gammaZero f hf γ)).symm
  ext x
  -- Evaluating both set-valued operators at `x` reduces to equality of singleton values.
  have hx := congrArg (fun T : SetValuedOperator H H ↦ T x) hrealizer
  simpa [Function.toSetValuedOperator_apply, Set.singleton_eq_singleton_iff] using hx

/-- A quadruple of sequences `p`, `x`, `q`, and `y` satisfies the parallel splitting recursion
`(28.30)` for the finite family `f : Fin (n + 2) → Γ₀(H)`, with relaxation parameters `lam`,
step size `γ`, and initial family `y0`. -/
structure IsParallelSplittingProximalOrbit
    (f : Fin (n + 2) → H → Set.Ioi (⊥ : EReal))
    (hf : ∀ i : Fin (n + 2), f i ∈ Γ₀(H))
    (lam : ℕ → ℝ) (γ : PosReal) (y0 : ProductSpace)
    (p q : ℕ → H) (x y : ℕ → ProductSpace) : Prop where
  /-- The orbit starts from the prescribed family `y0`. -/
  y_zero : y 0 = y0
  /-- The averaged primal family is `p_k = (n + 2)⁻¹ ∑ i, yᵢ,k`. -/
  p_eq (k : ℕ) : p k = ((n + 2 : ℝ)⁻¹) • ∑ i, y k i
  /-- The componentwise proximal step is `xᵢ,k = Prox_{γ fᵢ}(yᵢ,k)`. -/
  x_eq (k : ℕ) (i : Fin (n + 2)) : x k i = Prox[γ, f i, hf i] (y k i)
  /-- The averaged proximal family is `q_k = (n + 2)⁻¹ ∑ i, xᵢ,k`. -/
  q_eq (k : ℕ) : q k = ((n + 2 : ℝ)⁻¹) • ∑ i, x k i
  /-- The relaxed update is `yᵢ,k+1 = yᵢ,k + λ_k (2 q_k - p_k - xᵢ,k)`. -/
  y_succ_eq (k : ℕ) (i : Fin (n + 2)) :
    y (k + 1) i = y k i + lam k • ((2 : ℝ) • q k - p k - x k i)

namespace IsParallelSplittingProximalOrbit

/-- The source proximal recursion `(28.30)` is the Chapter 26 parallel splitting orbit for the
subdifferential family `i ↦ ∂ f i`. -/
theorem toSubdifferentialOrbit
    {f : Fin (n + 2) → H → Set.Ioi (⊥ : EReal)}
    {hf : ∀ i : Fin (n + 2), f i ∈ Γ₀(H)}
    {lam : ℕ → ℝ} {γ : PosReal} {y0 : ProductSpace}
    {p q : ℕ → H} {x y : ℕ → ProductSpace}
    (hOrbit : IsParallelSplittingProximalOrbit f hf lam γ y0 p q x y) :
    SetValuedOperator.IsParallelSplittingOrbit
      (fun i ↦ ∂ f i)
      (fun i ↦ subdifferential_isMaximallyMonotone_of_mem_gammaZero (hf i))
      lam γ y0 p q x y := by
  refine
    ⟨hOrbit.y_zero, (fun k ↦ by simpa using hOrbit.p_eq k), ?_,
      (fun k ↦ by simpa using hOrbit.q_eq k),
      fun k i ↦ hOrbit.y_succ_eq k i⟩
  intro k i
  -- Rewrite each proximal step as the canonical resolvent step for the subdifferential family.
  rw [hOrbit.x_eq k i, ← resolventMapSubdifferential_eq_scaledProximityOperator (hf i) γ]

/-- The Chapter 26 parallel splitting orbit for the subdifferential family specializes back to the
source proximal recursion `(28.30)`. -/
theorem ofSubdifferentialOrbit
    {f : Fin (n + 2) → H → Set.Ioi (⊥ : EReal)}
    {hf : ∀ i : Fin (n + 2), f i ∈ Γ₀(H)}
    {lam : ℕ → ℝ} {γ : PosReal} {y0 : ProductSpace}
    {p q : ℕ → H} {x y : ℕ → ProductSpace}
    (hOrbit : SetValuedOperator.IsParallelSplittingOrbit
      (fun i ↦ ∂ f i)
      (fun i ↦ subdifferential_isMaximallyMonotone_of_mem_gammaZero (hf i))
      lam γ y0 p q x y) :
    IsParallelSplittingProximalOrbit f hf lam γ y0 p q x y := by
  refine
    ⟨hOrbit.y_zero, (fun k ↦ by simpa using hOrbit.p_eq k), ?_,
      (fun k ↦ by simpa using hOrbit.q_eq k),
      fun k i ↦ hOrbit.y_succ_eq k i⟩
  intro k i
  -- Rewrite the resolvent step back to the source proximal update `(28.30)`.
  rw [← resolventMapSubdifferential_eq_scaledProximityOperator (hf i) γ, hOrbit.x_eq k i]

/-- The textbook proximal orbit and the Chapter 26 operator orbit agree for the subdifferential
family `i ↦ ∂ f i`. -/
theorem iff_subdifferentialOrbit
    {f : Fin (n + 2) → H → Set.Ioi (⊥ : EReal)}
    {hf : ∀ i : Fin (n + 2), f i ∈ Γ₀(H)}
    {lam : ℕ → ℝ} {γ : PosReal} {y0 : ProductSpace}
    {p q : ℕ → H} {x y : ℕ → ProductSpace} :
    IsParallelSplittingProximalOrbit f hf lam γ y0 p q x y ↔
      SetValuedOperator.IsParallelSplittingOrbit
        (fun i ↦ ∂ f i)
        (fun i ↦ subdifferential_isMaximallyMonotone_of_mem_gammaZero (hf i))
        lam γ y0 p q x y := by
  constructor
  · exact toSubdifferentialOrbit
  · exact ofSubdifferentialOrbit

end IsParallelSplittingProximalOrbit

/-- The three explicit regularity alternatives from Proposition 28.7 imply the finite-sum
subdifferential identity needed to pass from the minimization problem to the Chapter 26 operator
splitting theorem. -/
theorem subdifferential_sum_eq_sum_of_parallelSplittingRegularity
    (f : Fin (n + 2) → H → Set.Ioi (⊥ : EReal))
    (hf : ∀ i : Fin (n + 2), f i ∈ Γ₀(H))
    (hregular :
      (0 : H) ∈ successiveStrongRelativeInteriorIntersection n
          (fun i ↦ effectiveDomain (f i)) ∨
        (effectiveDomain (f 0) ∩
            ⋂ i : Fin (n + 1), interior (effectiveDomain (f i.succ))).Nonempty ∨
        (FiniteDimensional ℝ H ∧
          (⋂ i : Fin (n + 2), ri (effectiveDomain (f i))).Nonempty)) :
    (∂ (∑ i, f i) : SetValuedOperator H H) = ∑ i, ∂ f i := by
  rcases hregular with hsri | hinter | hri
  · exact
      subdifferential_sum_eq_sum_of_zero_mem_successiveStrongRelativeInteriorIntersection
        n f hf hsri
  · let frev : Fin (n + 2) → H → Set.Ioi (⊥ : EReal) := fun i ↦ f i.rev
    have hfrev : ∀ i : Fin (n + 2), frev i ∈ Γ₀(H) := fun i ↦ hf i.rev
    have hregular_rev :
        successiveDifferenceRegularity n (fun i ↦ effectiveDomain (frev i)) := by
      refine Or.inr <| Or.inr <| Or.inl ?_
      rcases hinter with ⟨x, hx0, hxinterior⟩
      refine ⟨x, ?_, ?_⟩
      · simpa [frev] using hx0
      · rw [Set.mem_iInter]
        intro i
        have hxi := Set.mem_iInter.mp hxinterior i.rev
        simpa [frev, Fin.rev_castSucc] using hxi
    have hsub_rev :
        (∂ (∑ i, frev i) : SetValuedOperator H H) = ∑ i, ∂ frev i :=
      subdifferential_sum_eq_sum_of_successiveDomainRegularity
        n frev hfrev (Or.inr hregular_rev)
    have hsum_rev : (∑ i, frev i) = ∑ i, f i := by
      funext x
      apply Subtype.ext
      simpa [frev] using
        (Equiv.sum_comp
          (Fin.revPerm : Equiv.Perm (Fin (n + 2)))
          (fun i ↦ (f i x : EReal)))
    have hsubsum_rev : (∑ i, ∂ frev i : SetValuedOperator H H) = ∑ i, ∂ f i := by
      funext x
      simpa [frev] using
        (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (n + 2))) (fun i ↦ (∂ f i) x))
    calc
      (∂ (∑ i, f i) : SetValuedOperator H H) = ∂ (∑ i, frev i) := by rw [hsum_rev]
      _ = ∑ i, ∂ frev i := hsub_rev
      _ = ∑ i, ∂ f i := hsubsum_rev
  · let frev : Fin (n + 2) → H → Set.Ioi (⊥ : EReal) := fun i ↦ f i.rev
    have hfrev : ∀ i : Fin (n + 2), frev i ∈ Γ₀(H) := fun i ↦ hf i.rev
    have hregular_rev :
        successiveDifferenceRegularity n (fun i ↦ effectiveDomain (frev i)) := by
      letI : FiniteDimensional ℝ H := hri.1
      refine Or.inr <| Or.inr <| Or.inr ?_
      rcases hri.2 with ⟨x, hxri⟩
      refine ⟨inferInstance, ⟨x, ?_⟩⟩
      rw [Set.mem_iInter]
      intro i
      have hxi := Set.mem_iInter.mp hxri i.rev
      simpa [frev] using hxi
    have hsub_rev :
        (∂ (∑ i, frev i) : SetValuedOperator H H) = ∑ i, ∂ frev i :=
      subdifferential_sum_eq_sum_of_successiveDomainRegularity
        n frev hfrev (Or.inr hregular_rev)
    have hsum_rev : (∑ i, frev i) = ∑ i, f i := by
      funext x
      apply Subtype.ext
      simpa [frev] using
        (Equiv.sum_comp
          (Fin.revPerm : Equiv.Perm (Fin (n + 2)))
          (fun i ↦ (f i x : EReal)))
    have hsubsum_rev : (∑ i, ∂ frev i : SetValuedOperator H H) = ∑ i, ∂ f i := by
      funext x
      simpa [frev] using
        (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (n + 2))) (fun i ↦ (∂ f i) x))
    calc
      (∂ (∑ i, f i) : SetValuedOperator H H) = ∂ (∑ i, frev i) := by rw [hsum_rev]
      _ = ∑ i, ∂ frev i := hsub_rev
      _ = ∑ i, ∂ f i := hsubsum_rev

/-- Proposition 28.7: let `f : Fin (n + 2) → Γ₀(H)` represent the source family
`(f_i)_{i ∈ {1, ..., m}}` with `m = n + 2`, assume the problem `minimize ∑ i, f i` has a
solution, and assume one of the source domain regularity conditions:
`0 ∈ ⋂_{i=2}^m sri (dom f_i - ⋂_{j=1}^{i-1} dom f_j)`,
`dom f_1 ∩ ⋂_{i=2}^m int(dom f_i) ≠ ∅`, or finite-dimensional common relative interior. Let
`lam` take values in `[0, 2]` with `∑ λ_k (2 - λ_k) = +∞`, let `γ ∈ ℝ_{++}`, and let
`p`, `x`, `q`, and `y` satisfy the parallel splitting recursion `(28.30)` from `y0`. Then
`(p_k)` converges weakly to a point of `Argmin (∑ i, f i).asEReal`. -/
theorem parallelSplittingAlgorithm_exists_weakLimit_mem_argmin
    (f : Fin (n + 2) → H → Set.Ioi (⊥ : EReal))
    (hf : ∀ i : Fin (n + 2), f i ∈ Γ₀(H))
    (hargmin : (Argmin (∑ i, f i).asEReal).Nonempty)
    (hregular :
      (0 : H) ∈ successiveStrongRelativeInteriorIntersection n
          (fun i ↦ effectiveDomain (f i)) ∨
        (effectiveDomain (f 0) ∩
            ⋂ i : Fin (n + 1), interior (effectiveDomain (f i.succ))).Nonempty ∨
        (FiniteDimensional ℝ H ∧
          (⋂ i : Fin (n + 2), ri (effectiveDomain (f i))).Nonempty))
    (lam : ℕ → ℝ) (hlam : ∀ k : ℕ, lam k ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N : ℕ ↦
          (Finset.range N).sum
            (fun k : ℕ ↦ lam k * (2 - lam k)))
        atTop atTop)
    (γ : PosReal) (y0 : ProductSpace) {p q : ℕ → H} {x y : ℕ → ProductSpace}
    (hOrbit : IsParallelSplittingProximalOrbit f hf lam γ y0 p q x y) :
    ∃ xbar ∈ Argmin (∑ i, f i).asEReal,
      Tendsto (fun k : ℕ ↦ toWeakSpace ℝ H (p k))
        atTop (𝓝 (toWeakSpace ℝ H xbar)) := by
  have hsub :
      (∂ (∑ i, f i) : SetValuedOperator H H) = ∑ i, ∂ f i :=
    subdifferential_sum_eq_sum_of_parallelSplittingRegularity f hf hregular
  have hzero : (((∑ i, ∂ f i)).zeros).Nonempty := by
    rcases hargmin with ⟨xbar, hxbar⟩
    refine ⟨xbar, ?_⟩
    rw [← hsub, ← argmin_eq_zeros_subdifferential (∑ i, f i)]
    exact hxbar
  have hOrbit' :
      SetValuedOperator.IsParallelSplittingOrbit
        (fun i ↦ ∂ f i)
        (fun i ↦ subdifferential_isMaximallyMonotone_of_mem_gammaZero (hf i))
        lam γ y0 p q x y :=
    hOrbit.toSubdifferentialOrbit
  obtain ⟨xbar, hxbar_zero, hweak⟩ :=
    SetValuedOperator.parallelSplittingAlgorithm_average_tendsto_weakly_to_zeroSet
      (fun i ↦ ∂ f i)
      (Nat.succ_pos (n + 1))
      (fun i ↦ subdifferential_isMaximallyMonotone_of_mem_gammaZero (hf i))
      hzero lam hlam hdiv γ y0 p q x y hOrbit'
  refine ⟨xbar, ?_, hweak⟩
  have hxbar_sub : xbar ∈ (∂ (∑ i, f i)).zeros := by
    simpa [hsub] using hxbar_zero
  simpa [argmin_eq_zeros_subdifferential (∑ i, f i)] using hxbar_sub

end ParallelSplittingAlgorithm

end

end ERealFunction
