import BauschkeLean.Chap22.Example_22_5
import BauschkeLean.Chap26.Proposition_26_5
import BauschkeLean.Chap26.Remark_26_23
import BauschkeLean.Chap26.Theorem_26_11

open Function
open Filter
open SetValuedOperator
open scoped InnerProductSpace Pointwise SetValuedOperator Topology

universe u

namespace ERealFunction

noncomputable section

/- Source/core/bridge triage:
- `source-facing`: Proposition 26.24 is the Douglas--Rachford convergence theorem specialized to
  `A = ∂ f`, with the solution set kept in the Chapter 26 source-facing form
  `variationalInequalityProblem f B`.
- `core/canonical`: the reusable convergence owner is `Theorem_26_11` for
  `primal_inclusion_solution_set A B`.
- `bridge/view`: `Remark_26_23` identifies `variationalInequalityProblem f B` with
  `primal_inclusion_solution_set (∂ f) B`, and `Example_22_5` turns the source uniform-convexity
  alternative for `f` into the canonical uniform-monotonicity hypothesis on `∂ f`. -/
-- Semantic recall: `lean_leansearch` only surfaced generic uniform-convexity owners, so this
-- file specializes the verified local Chapter 26 Douglas--Rachford owners to `A = ∂ f` and keeps
-- the source-facing solution set as `variationalInequalityProblem f B`.

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
variable (B : SetValuedOperator H H)

local notation "VI" => variationalInequalityProblem f B
local notation "hSub" => subdifferential_isMaximallyMonotone_of_mem_gammaZero hf

/-- Helper for Proposition 26.24: the auxiliary Douglas--Rachford sequence
`z_n = J_{γ ∂ f} (2 x_n - y_n)`. -/
private def douglasRachfordAuxiliarySequence
    (A B : SetValuedOperator H H)
    (hA : Maximal SetValuedOperator.IsMonotone A)
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (γ : PosReal) (lam : ℕ → ℝ) (y0 : H) : ℕ → H :=
  fun n ↦
    resolventMap A hA γ
      ((2 : ℝ) • douglasRachfordPrimalSequence A B hA hB γ lam y0 n -
        douglasRachfordIteration A B hA hB γ lam y0 n)

/-- Helper for Proposition 26.24: the Douglas--Rachford dual sequence
`u_n = {}^[γ] B (y_n) = γ⁻¹ (y_n - x_n)`. -/
private def douglasRachfordDualSequence
    (A B : SetValuedOperator H H)
    (hA : Maximal SetValuedOperator.IsMonotone A)
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (γ : PosReal) (lam : ℕ → ℝ) (y0 : H) : ℕ → H :=
  fun n ↦
    yosidaApproximationMap B hB γ
      (douglasRachfordIteration A B hA hB γ lam y0 n)

omit [CompleteSpace H] in
/-- Helper for Proposition 26.24: the source uniform-convexity alternative for `f` converts to
the uniform-monotonicity disjunction required by Theorem 26.11. -/
private theorem subdifferential_uniformMonotoneOnEveryBoundedSubset_or
    (hconv : ConvexOn f (effectiveDomain f))
    (hUniform :
      (∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ f).dom →
          ∃ φ : NNReal → EReal, UniformlyConvexOn f S φ) ∨
        ∀ S : Set H,
          S.Nonempty → Bornology.IsBounded S → S ⊆ B.dom → B.IsUniformlyMonotoneOn S) :
    (∀ S : Set H,
      S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ f).dom →
        (∂ f).IsUniformlyMonotoneOn S) ∨
      ∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ B.dom → B.IsUniformlyMonotoneOn S := by
  rcases hUniform with hUniform | hUniform
  · left
    intro S hS hS_bounded hS_sub
    obtain ⟨φ, hφ⟩ := hUniform S hS hS_bounded hS_sub
    exact
      subdifferential_isUniformlyMonotoneOn_of_convexOn_of_uniformlyConvexOn
        f hconv hS_sub hφ
  · right
    exact hUniform

/-- Helper for Proposition 26.24: a Douglas--Rachford fixed point for `A = ∂ f` yields a point of
the canonical primal inclusion solution set. -/
private theorem subdifferential_primalInclusionSolutionSet_nonempty_of_fixedPoint
    (hB : Maximal SetValuedOperator.IsMonotone B) (γ : PosReal) {y : H}
    (hy :
      y ∈ fixedPoints (reflectedResolventComposition (∂ f) B hSub hB γ)) :
    Set.Nonempty (primal_inclusion_solution_set (∂ f) B) := by
  refine ⟨resolventMap B hB γ y, ?_⟩
  -- Repackage the fixed point through the image description of Proposition 26.1(6).
  rw [primal_inclusion_solution_set_eq_image_resolvent_fixedPoints_reflectedResolventComposition
    (∂ f) B hSub hB γ]
  exact ⟨y, hy, rfl⟩

/-- Helper for Proposition 26.24: a fixed point for the reflected resolvent composition supplies
the canonical graph witnesses `(x, -u) ∈ gra (∂ f)` and `(x, u) ∈ gra B`. -/
private theorem subdifferential_limitGraphData
    (hB : Maximal SetValuedOperator.IsMonotone B) (γ : PosReal) {y : H}
    (hy :
      y ∈ fixedPoints (reflectedResolventComposition (∂ f) B hSub hB γ)) :
    (-yosidaApproximationMap B hB γ y) ∈ (∂ f) (resolventMap B hB γ y) ∧
      yosidaApproximationMap B hB γ y ∈ B (resolventMap B hB γ y) := by
  let x : H := resolventMap B hB γ y
  let u : H := yosidaApproximationMap B hB γ y
  have hu_mem : u ∈ ({}^[γ] B) y := by
    -- The Yosida realizer is the unique point of the singleton Yosida value.
    rw [yosidaApproximation_eq_singleton_yosidaApproximationMap_of_maximal B hB γ y]
    simp [u]
  have hy_decomp : y = x + (γ : ℝ) • u := by
    -- Rewrite the fixed point through the standard resolvent-plus-Yosida decomposition.
    simpa [x, u] using eq_resolventMap_add_smul_yosidaApproximationMap B hB γ y
  have huB : u ∈ B x := by
    -- Transport the Yosida graph witness from `y - γ • u` to the primal point `x`.
    have huB' : u ∈ B (y - (γ : ℝ) • u) :=
      (mem_yosidaApproximation_iff_mem B γ y u).1 hu_mem
    have hbase : y - (γ : ℝ) • u = x := by
      rw [hy_decomp]
      abel_nf
    simpa [hbase] using huB'
  have hargA : (2 : ℝ) • x - y = x - (γ : ℝ) • u := by
    -- Normalize the reflected-resolvent argument to the standard resolvent graph form.
    simpa [x, u] using
      two_smul_resolventMap_sub_eq_sub_smul_yosidaApproximationMap B hB γ y
  have huA : -u ∈ (∂ f) x := by
    -- The fixed-point equation is exactly the resolvent equation for `∂ f` at `x`.
    have hresA : resolventMap (∂ f) hSub γ ((2 : ℝ) • x - y) = x := by
      have hyfix' :=
        (mem_fixedPoints_reflectedResolventComposition_iff_resolventMap_eq
          (∂ f) B hSub hB γ y).1 hy
      simpa [x] using hyfix'
    rw [hargA] at hresA
    exact (resolventMap_sub_smul_eq_iff_neg_mem (∂ f) hSub γ x u).1 hresA
  exact ⟨by simpa [u] using huA, by simpa [x, u] using huB⟩

/-- Helper for Proposition 26.24: the Douglas--Rachford iterates furnish graph data for `B` and
`∂ f` together with the primal-auxiliary residual identity. -/
private theorem subdifferential_graphData
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (lam : ℕ → ℝ) (γ : PosReal) (y0 : H) (n : ℕ) :
    let y_n := douglasRachfordIteration (∂ f) B hSub hB γ lam y0
    let x_n := douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0
    let u_n := douglasRachfordDualSequence (∂ f) B hSub hB γ lam y0
    let z_n := douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0
    let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
    (x_n n, u_n n) ∈ gra B ∧
      (z_n n, w_n n) ∈ gra (∂ f) ∧
      x_n n - z_n n = (γ : ℝ) • (u_n n + w_n n) := by
  let y_n := douglasRachfordIteration (∂ f) B hSub hB γ lam y0
  let x_n := douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0
  let u_n := douglasRachfordDualSequence (∂ f) B hSub hB γ lam y0
  let z_n := douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0
  let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
  have hu_eq : u_n n = (γ : ℝ)⁻¹ • (y_n n - x_n n) := by
    -- Unfold the dual iterate to expose the scaled primal residual formula.
    simp [u_n, x_n, y_n, douglasRachfordDualSequence, douglasRachfordPrimalSequence,
      yosidaApproximationMap_apply]
  have hw_eq : w_n n = (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n n - y_n n - z_n n) := by
    -- The companion term is exactly its defining scaled reflected residual.
    simp [w_n]
  have hxu_mem : u_n n ∈ ({}^[γ] B) (y_n n) := by
    -- The canonical Yosida realizer is the singleton element of the Yosida value.
    rw [yosidaApproximation_eq_singleton_yosidaApproximationMap_of_maximal B hB γ]
    simp [u_n, y_n, douglasRachfordDualSequence, yosidaApproximationMap_apply]
  have hxu_graph : (x_n n, u_n n) ∈ gra B := by
    -- Rewrite the Yosida graph point on `y_n` to the primal point `x_n = J_{γ B} y_n`.
    have hgraph :
        (y_n n - (γ : ℝ) • u_n n, u_n n) ∈ gra B :=
      (mem_yosidaApproximation_iff_mem_graph B γ (y_n n) (u_n n)).1 hxu_mem
    have hbase : y_n n - (γ : ℝ) • u_n n = x_n n := by
      rw [hu_eq]
      simp [x_n, douglasRachfordPrimalSequence, γ.2.ne']
    simpa [hbase] using hgraph
  have hxz_mem : z_n n ∈ J[((γ : ℝ) • (∂ f))] ((2 : ℝ) • x_n n - y_n n) := by
    -- The auxiliary iterate is the canonical resolvent realizer of `∂ f`.
    rw [resolvent_smul_eq_singleton_resolventMap_of_maximal (∂ f) hSub γ
      ((2 : ℝ) • x_n n - y_n n)]
    simp [z_n, x_n, y_n, douglasRachfordAuxiliarySequence]
  have hzw_graph : (z_n n, w_n n) ∈ gra (∂ f) := by
    -- The resolvent graph criterion identifies the companion term `w_n`.
    have hgraph :
        (z_n n, (γ : ℝ)⁻¹ • (((2 : ℝ) • x_n n - y_n n) - z_n n)) ∈ gra (∂ f) :=
      (mem_resolvent_smul_iff_mem_graph (∂ f) γ ((2 : ℝ) • x_n n - y_n n) (z_n n)).1 hxz_mem
    simpa [w_n, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hgraph
  have hresidual :
      x_n n - z_n n = (γ : ℝ) • (u_n n + w_n n) := by
    -- Expanding the Yosida and companion terms collapses to the primal-auxiliary gap.
    have hsplit :
        (y_n n - x_n n) + ((2 : ℝ) • x_n n - y_n n - z_n n) = x_n n - z_n n := by
      simp [two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    calc
      x_n n - z_n n = (y_n n - x_n n) + ((2 : ℝ) • x_n n - y_n n - z_n n) := by
        simpa using hsplit.symm
      _ = (γ : ℝ) • (u_n n + w_n n) := by
        rw [hu_eq, hw_eq]
        simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_add, γ.2.ne']
  exact ⟨hxu_graph, hzw_graph, hresidual⟩

/-- Helper for Proposition 26.24: the Douglas--Rachford residual of the relaxed operator is the
auxiliary-minus-primal gap `z_n - x_n`. -/
private theorem subdifferential_residual_eq_auxiliary_sub_primal
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (γ : PosReal) (lam : ℕ → ℝ) (y0 : H) (n : ℕ) :
    douglasRachfordOperator (resolventMap (∂ f) hSub γ) (resolventMap B hB γ)
        (douglasRachfordIteration (∂ f) B hSub hB γ lam y0 n) -
      douglasRachfordIteration (∂ f) B hSub hB γ lam y0 n =
        douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0 n -
          douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0 n := by
  -- Expand the Douglas--Rachford operator once and cancel the orbit term appearing with both signs.
  simp only [douglasRachfordPrimalSequence, ERealFunction.douglasRachfordAuxiliarySequence]
  rw [douglasRachfordOperator_apply]
  abel_nf

/-- Helper for Proposition 26.24: under the Douglas--Rachford hypotheses, the residual
`x_n - z_n` converges strongly to `0`. -/
private theorem subdifferential_primal_auxiliary_gap_tendsto_zero
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (hzero : Set.Nonempty (primal_inclusion_solution_set (∂ f) B))
    (lam : ℕ → ℝ) (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    (γ : PosReal) (y0 : H) :
    Tendsto
      (fun n ↦
        douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0 n -
          douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0 n)
      atTop (𝓝 (0 : H)) := by
  let T : H → H :=
    douglasRachfordOperator (resolventMap (∂ f) hSub γ) (resolventMap B hB γ)
  have hfix : (fixedPoints T).Nonempty := by
    rcases hzero with ⟨x, hx⟩
    rw [primal_inclusion_solution_set_eq_image_resolvent_fixedPoints_reflectedResolventComposition
      (∂ f) B hSub hB γ] at hx
    rcases hx with ⟨y, hyfix, _⟩
    rw [fixedPoints_douglasRachfordOperator_resolvent_eq_fixedPoints_reflectedResolventComposition
      (∂ f) B hSub hB γ]
    exact ⟨y, hyfix⟩
  have hresidual :
      Tendsto
        (fun n ↦
          douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0 n -
            douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0 n)
        atTop (𝓝 (0 : H)) := by
    have hbase :=
      residual_tendsto_zero_of_relaxedOperatorIteration_of_firmlyNonexpansive
        (douglasRachfordSplittingOperator_firmlyNonexpansive (∂ f) B hSub hB γ)
        hfix lam hlam hdiv y0
    have hresidual_eq :
        (fun n ↦
          T (relaxedOperatorIteration (fun _ ↦ T) lam y0 n) -
            relaxedOperatorIteration (fun _ ↦ T) lam y0 n) =
          (fun n ↦
            douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0 n -
              douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0 n) := by
      funext n
      simpa [T, douglasRachfordIteration] using
        subdifferential_residual_eq_auxiliary_sub_primal hf B hB γ lam y0 n
    -- Proposition 5.16 gives asymptotic regularity of the Douglas--Rachford residual.
    rw [hresidual_eq] at hbase
    exact hbase
  -- Negate the residual limit to match the source orientation `x_n - z_n`.
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hresidual.neg

/-- Helper for Proposition 26.24: a weakly convergent Douglas--Rachford orbit has bounded primal
shadow sequence `x_n = J_{γ B} y_n`. -/
private theorem subdifferential_primalSequence_boundedRange
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (lam : ℕ → ℝ) (γ : PosReal) (y0 : H) {y : H}
    (hy_tendsto :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordIteration (∂ f) B hSub hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H y))) :
    Bornology.IsBounded
      (Set.range (douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0)) := by
  let y_n := douglasRachfordIteration (∂ f) B hSub hB γ lam y0
  let x_n := douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0
  have hy_bounded : Bornology.IsBounded (Set.range y_n) :=
    bounded_range_of_tendsto_weakly hy_tendsto
  have hLip : LipschitzWith 1 (resolventMap B hB γ) := by
    -- Whole-space firm nonexpansiveness implies a `1`-Lipschitz bound.
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    have hfirm' :=
      (firmlyNonexpansiveOn_iff.mp
        (show FirmlyNonexpansiveOn (Set.univ : Set H) (resolventMap B hB γ) by
          simpa using resolventMap_firmlyNonexpansiveOn_univ B hB γ)) x (by simp) y (by simp)
    have hsq : ‖resolventMap B hB γ x - resolventMap B hB γ y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      nlinarith [sq_nonneg ‖(x - resolventMap B hB γ x) - (y - resolventMap B hB γ y)‖]
    have hnorm : ‖resolventMap B hB γ x - resolventMap B hB γ y‖ ≤ ‖x - y‖ := by
      nlinarith [norm_nonneg (resolventMap B hB γ x - resolventMap B hB γ y),
        norm_nonneg (x - y), hsq]
    simpa [dist_eq_norm] using hnorm
  have hrange :
      Set.range x_n = (resolventMap B hB γ) '' Set.range y_n := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨y_n n, ⟨n, rfl⟩, rfl⟩
    · rintro ⟨y', ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
  -- Transport boundedness through the Lipschitz resolvent.
  rw [hrange]
  exact hLip.isBounded_image hy_bounded

omit [CompleteSpace H] in
/-- Helper for Proposition 26.24: subtracting a strongly null residual preserves the weak limit of
a sequence. -/
private theorem subdifferential_tendstoWeaklyOfSubTendstoZeroSeq
    {aSeq bSeq : ℕ → H} {a : H}
    (ha :
      Tendsto (fun n ↦ toWeakSpace ℝ H (aSeq n)) atTop
        (𝓝 (toWeakSpace ℝ H a)))
    (hsub : Tendsto (fun n ↦ aSeq n - bSeq n) atTop (𝓝 (0 : H))) :
    Tendsto (fun n ↦ toWeakSpace ℝ H (bSeq n)) atTop
      (𝓝 (toWeakSpace ℝ H a)) := by
  -- Send the strong residual to `WeakSpace`, then subtract it from the known weak limit.
  have hsubWeak :
      Tendsto (fun n ↦ toWeakSpace ℝ H (aSeq n - bSeq n)) atTop
        (𝓝 (toWeakSpace ℝ H (0 : H))) := by
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      ((toWeakSpaceCLM ℝ H).continuous.tendsto (0 : H)).comp hsub
  simpa [sub_sub_cancel] using ha.sub hsubWeak

/-- Helper for Proposition 26.24: along a primal cluster subsequence, the auxiliary subsequence
has the same weak limit because the primal-auxiliary gap is strongly null. -/
private theorem subdifferential_auxiliary_subsequence_tendsto_weakly
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (hzero : Set.Nonempty (primal_inclusion_solution_set (∂ f) B))
    (lam : ℕ → ℝ) (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    (γ : PosReal) (y0 : H) {z : H} {φ : ℕ → ℕ}
    (hφmono : StrictMono φ)
    (hφx :
      Tendsto
        (fun n ↦
          toWeakSpace ℝ H
            (douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0 (φ n)))
        atTop (𝓝 (toWeakSpace ℝ H z))) :
    Tendsto
      (fun n ↦
        toWeakSpace ℝ H
          (douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0 (φ n)))
      atTop (𝓝 (toWeakSpace ℝ H z)) := by
  let x_n := douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0
  let z_n := douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0
  have hgap :
      Tendsto (fun n ↦ x_n n - z_n n) atTop (𝓝 (0 : H)) := by
    -- Reuse the source-facing residual theorem before restricting to the subsequence.
    simpa [x_n, z_n] using
      subdifferential_primal_auxiliary_gap_tendsto_zero
        hf B hB hzero lam hlam hdiv γ y0
  have hgap_sub :
      Tendsto (fun n ↦ x_n (φ n) - z_n (φ n)) atTop (𝓝 (0 : H)) := by
    -- The primal-auxiliary gap remains strongly null along the extracted subsequence.
    simpa [Function.comp, x_n, z_n] using hgap.comp hφmono.tendsto_atTop
  -- Move the weak cluster limit from the primal subsequence to the auxiliary subsequence.
  exact subdifferential_tendstoWeaklyOfSubTendstoZeroSeq hφx hgap_sub

/-- Helper for Proposition 26.24: along a primal cluster subsequence, the dual subsequence
converges weakly to `γ⁻¹ • (y - z)` by normalizing `u_n = γ⁻¹ • (y_n - x_n)`. -/
private theorem subdifferential_dual_subsequence_tendsto_weakly
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (lam : ℕ → ℝ) (γ : PosReal) (y0 : H) {y z : H} {φ : ℕ → ℕ}
    (hy_tendsto :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordIteration (∂ f) B hSub hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H y)))
    (hφmono : StrictMono φ)
    (hφx :
      Tendsto
        (fun n ↦
          toWeakSpace ℝ H
            (douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0 (φ n)))
        atTop (𝓝 (toWeakSpace ℝ H z))) :
    Tendsto
      (fun n ↦
        toWeakSpace ℝ H
          (douglasRachfordDualSequence (∂ f) B hSub hB γ lam y0 (φ n)))
      atTop (𝓝 (toWeakSpace ℝ H ((γ : ℝ)⁻¹ • (y - z)))) := by
  let y_n := douglasRachfordIteration (∂ f) B hSub hB γ lam y0
  let x_n := douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0
  let u_n := douglasRachfordDualSequence (∂ f) B hSub hB γ lam y0
  have hy_subseq :
      Tendsto (fun n ↦ toWeakSpace ℝ H (y_n (φ n))) atTop (𝓝 (toWeakSpace ℝ H y)) := by
    -- Restrict the weak limit of the Douglas-Rachford orbit to the cluster subsequence.
    simpa [y_n, Function.comp] using hy_tendsto.comp hφmono.tendsto_atTop
  have hdiff :=
    (hy_subseq.sub hφx).const_smul ((γ : ℝ)⁻¹)
  -- Rewrite the dual subsequence through the Yosida residual identity.
  simpa [u_n, y_n, x_n, douglasRachfordDualSequence, yosidaApproximationMap_apply,
    Function.comp, smul_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hdiff

/-- Helper for Proposition 26.24: along a primal cluster subsequence, the dual residual
`w_(φ n) + u_(φ n)` is the scaled primal-auxiliary gap along the extracted subsequence. -/
private theorem subdifferential_dual_residual_subsequence_eq
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (lam : ℕ → ℝ) (γ : PosReal) (y0 : H) {φ : ℕ → ℕ} (n : ℕ) :
    let x_n := douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0
    let u_n := douglasRachfordDualSequence (∂ f) B hSub hB γ lam y0
    let z_n := douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0
    let y_n := douglasRachfordIteration (∂ f) B hSub hB γ lam y0
    let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
    (γ : ℝ)⁻¹ • (x_n (φ n) - z_n (φ n)) = w_n (φ n) + u_n (φ n) := by
  let x_n := douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0
  let u_n := douglasRachfordDualSequence (∂ f) B hSub hB γ lam y0
  let z_n := douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0
  let y_n := douglasRachfordIteration (∂ f) B hSub hB γ lam y0
  let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
  have hgraph := (subdifferential_graphData hf B hB lam γ y0 (φ n)).2.2
  calc
    (γ : ℝ)⁻¹ • (x_n (φ n) - z_n (φ n))
        = (γ : ℝ)⁻¹ • ((γ : ℝ) • (u_n (φ n) + w_n (φ n))) := by
            rw [show x_n (φ n) - z_n (φ n) = (γ : ℝ) • (u_n (φ n) + w_n (φ n)) by
              simpa [x_n, u_n, z_n, w_n] using hgraph]
    _ = u_n (φ n) + w_n (φ n) := by
          simp [smul_smul, γ.2.ne']
    _ = w_n (φ n) + u_n (φ n) := by
          abel_nf

/-- Helper for Proposition 26.24: along a primal cluster subsequence, the dual residual
`w_(φ n) + u_(φ n)` converges strongly to `0`. -/
private theorem subdifferential_dual_residual_subsequence_tendsto_zero
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (hzero : Set.Nonempty (primal_inclusion_solution_set (∂ f) B))
    (lam : ℕ → ℝ) (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    (γ : PosReal) (y0 : H) {φ : ℕ → ℕ}
    (hφmono : StrictMono φ) :
    Tendsto
      (fun n ↦
        let x_n := douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0
        let u_n := douglasRachfordDualSequence (∂ f) B hSub hB γ lam y0
        let z_n := douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0
        let y_n := douglasRachfordIteration (∂ f) B hSub hB γ lam y0
        let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
        w_n (φ n) + u_n (φ n))
      atTop (𝓝 (0 : H)) := by
  let x_n := douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0
  let u_n := douglasRachfordDualSequence (∂ f) B hSub hB γ lam y0
  let z_n := douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0
  let y_n := douglasRachfordIteration (∂ f) B hSub hB γ lam y0
  let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
  have hgap :
      Tendsto (fun n ↦ x_n n - z_n n) atTop (𝓝 (0 : H)) := by
    -- Start from the strong primal-auxiliary gap on the full sequence.
    simpa [x_n, z_n] using
      subdifferential_primal_auxiliary_gap_tendsto_zero
        hf B hB hzero lam hlam hdiv γ y0
  have hgap_sub :
      Tendsto (fun n ↦ x_n (φ n) - z_n (φ n)) atTop (𝓝 (0 : H)) := by
    -- Restrict the strong gap to the extracted subsequence.
    simpa [Function.comp, x_n, z_n] using hgap.comp hφmono.tendsto_atTop
  have hscaled :
      Tendsto (fun n ↦ (γ : ℝ)⁻¹ • (x_n (φ n) - z_n (φ n))) atTop (𝓝 (0 : H)) := by
    -- Normalize the scalar multiple limit back to `0`.
    simpa using hgap_sub.const_smul ((γ : ℝ)⁻¹)
  have hscaled_eq :
      (fun n ↦ (γ : ℝ)⁻¹ • (x_n (φ n) - z_n (φ n))) =
        (fun n ↦ w_n (φ n) + u_n (φ n)) := by
    funext n
    simpa [x_n, u_n, z_n, y_n, w_n] using
      subdifferential_dual_residual_subsequence_eq hf B hB lam γ y0 (φ := φ) n
  rw [← hscaled_eq]
  exact hscaled

/-- Helper for Proposition 26.24: the `∂ f`-graph witnesses persist along any extracted
subsequence. -/
private theorem subdifferentialAuxiliaryGraphSubsequence_mem
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (lam : ℕ → ℝ) (γ : PosReal) (y0 : H) {φ : ℕ → ℕ} :
    ∀ n,
      let x_n := douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0
      let z_n := douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0
      let y_n := douglasRachfordIteration (∂ f) B hSub hB γ lam y0
      let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
      (z_n (φ n), w_n (φ n)) ∈ gra (∂ f) := by
  intro n
  let x_n := douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0
  let z_n := douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0
  let y_n := douglasRachfordIteration (∂ f) B hSub hB γ lam y0
  let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
  -- Read the `∂ f`-graph point directly from the packaged Douglas--Rachford graph data.
  simpa [z_n, w_n] using (subdifferential_graphData hf B hB lam γ y0 (φ n)).2.1

/-- Helper for Proposition 26.24: the `B`-graph witnesses persist along any extracted
subsequence. -/
private theorem subdifferentialPrimalGraphSubsequence_mem
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (lam : ℕ → ℝ) (γ : PosReal) (y0 : H) {φ : ℕ → ℕ} :
    ∀ n,
      let x_n := douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0
      let u_n := douglasRachfordDualSequence (∂ f) B hSub hB γ lam y0
      (x_n (φ n), u_n (φ n)) ∈ gra B := by
  intro n
  let x_n := douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0
  let u_n := douglasRachfordDualSequence (∂ f) B hSub hB γ lam y0
  -- Read the `B`-graph point directly from the packaged Douglas--Rachford graph data.
  simpa [x_n, u_n] using (subdifferential_graphData hf B hB lam γ y0 (φ n)).1

/-- Helper for Proposition 26.24: along any extracted subsequence, the residual in the
`z_(φ n) - x_(φ n)` orientation converges strongly to `0`. -/
private theorem subdifferentialAuxiliaryMinusPrimalSubsequence_tendsto_zero
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (hzero : Set.Nonempty (primal_inclusion_solution_set (∂ f) B))
    (lam : ℕ → ℝ) (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    (γ : PosReal) (y0 : H) {φ : ℕ → ℕ}
    (hφmono : StrictMono φ) :
    Tendsto
      (fun n ↦
        let x_n := douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0
        let z_n := douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0
        z_n (φ n) - x_n (φ n))
      atTop (𝓝 (0 : H)) := by
  let x_n := douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0
  let z_n := douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0
  have hgap :
      Tendsto (fun n ↦ x_n n - z_n n) atTop (𝓝 (0 : H)) := by
    -- Start from the strong primal-auxiliary gap on the full sequence.
    simpa [x_n, z_n] using
      subdifferential_primal_auxiliary_gap_tendsto_zero
        hf B hB hzero lam hlam hdiv γ y0
  have hgap_sub :
      Tendsto (fun n ↦ x_n (φ n) - z_n (φ n)) atTop (𝓝 (0 : H)) := by
    -- Restrict the strong gap to the extracted subsequence.
    simpa [Function.comp, x_n, z_n] using hgap.comp hφmono.tendsto_atTop
  -- Proposition 26.5 uses the residual in the `z_n - x_n` orientation.
  simpa [x_n, z_n, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hgap_sub.neg

/-- Helper for Proposition 26.24: once the subsequence weak limits, graph memberships, and
residual limits are prepared, the `L = id` specialization of Proposition 26.5 closes the
limiting `B`-graph point. -/
private theorem subdifferential_weakClusterPoint_mem_graphBLimit_of_subsequence
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (lam : ℕ → ℝ) (γ : PosReal) (y0 : H) {y z : H} {φ : ℕ → ℕ}
    (hz_subseq :
      let z_n := douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (z_n (φ n)))
        atTop (𝓝 (toWeakSpace ℝ H z)))
    (hu_subseq :
      let u_n := douglasRachfordDualSequence (∂ f) B hSub hB γ lam y0
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (u_n (φ n)))
        atTop (𝓝 (toWeakSpace ℝ H ((γ : ℝ)⁻¹ • (y - z)))))
    (hgraphA :
      let x_n := douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0
      let z_n := douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0
      let y_n := douglasRachfordIteration (∂ f) B hSub hB γ lam y0
      let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
      ∀ n, (z_n (φ n), w_n (φ n)) ∈ gra (∂ f))
    (hgraphB :
      let x_n := douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0
      let u_n := douglasRachfordDualSequence (∂ f) B hSub hB γ lam y0
      ∀ n, (x_n (φ n), u_n (φ n)) ∈ gra B)
    (hresidual :
      let x_n := douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0
      let z_n := douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0
      Tendsto (fun n ↦ z_n (φ n) - x_n (φ n)) atTop (𝓝 (0 : H)))
    (hdualResidual :
      let x_n := douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0
      let u_n := douglasRachfordDualSequence (∂ f) B hSub hB γ lam y0
      let z_n := douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0
      let y_n := douglasRachfordIteration (∂ f) B hSub hB γ lam y0
      let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
      Tendsto (fun n ↦ w_n (φ n) + u_n (φ n)) atTop (𝓝 (0 : H))) :
    (z, (γ : ℝ)⁻¹ • (y - z)) ∈ gra B := by
  let x_n := douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0
  let u_n := douglasRachfordDualSequence (∂ f) B hSub hB γ lam y0
  let z_n := douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0
  let y_n := douglasRachfordIteration (∂ f) B hSub hB γ lam y0
  let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
  -- Route correction: freeze the `L = id` specialization once, then pass only prepared
  -- subsequence facts to the imported graph-limit owner.
  simpa [x_n, u_n, z_n, y_n, w_n] using
    (SetValuedOperator.mem_graph_B_of_weak_primal_dual_residual_zero_id
      (A := ∂ f)
      (B := B)
      (hA := hSub)
      (hB := hB)
      (xSeq := fun n ↦ z_n (φ n))
      (uSeq := fun n ↦ w_n (φ n))
      (ySeq := fun n ↦ x_n (φ n))
      (vSeq := fun n ↦ u_n (φ n))
      (x := z)
      (v := (γ : ℝ)⁻¹ • (y - z))
      hgraphA hgraphB hz_subseq hu_subseq hresidual hdualResidual)

/-- Proposition 26.24: every weak cluster point of the primal sequence determines the limiting
graph point of `B`. -/
private theorem subdifferential_weakClusterPoint_mem_graphBLimit
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (hzero : Set.Nonempty (primal_inclusion_solution_set (∂ f) B))
    (lam : ℕ → ℝ) (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    (γ : PosReal) (y0 : H) {y z : H}
    (hy_tendsto :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordIteration (∂ f) B hSub hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H y)))
    (hz :
      IsSequentialClusterPt
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0 n))
        (toWeakSpace ℝ H z)) :
    (z, (γ : ℝ)⁻¹ • (y - z)) ∈ gra B := by
  rcases hz.exists_subseq_tendsto with ⟨φ, hφmono, hφx⟩
  let y_n := douglasRachfordIteration (∂ f) B hSub hB γ lam y0
  let x_n := douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0
  let u_n := douglasRachfordDualSequence (∂ f) B hSub hB γ lam y0
  let z_n := douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0
  let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
  have hz_subseq :
      Tendsto (fun n ↦ toWeakSpace ℝ H (z_n (φ n))) atTop (𝓝 (toWeakSpace ℝ H z)) := by
    -- Route correction: first transport the weak cluster limit from `x_(φ n)` to `z_(φ n)`.
    simpa [z_n] using
      subdifferential_auxiliary_subsequence_tendsto_weakly
        hf B hB hzero lam hlam hdiv γ y0 hφmono hφx
  have hu_subseq :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (u_n (φ n)))
        atTop (𝓝 (toWeakSpace ℝ H ((γ : ℝ)⁻¹ • (y - z)))) := by
    -- Normalize the dual subsequence via `u_n = γ⁻¹ • (y_n - x_n)`.
    simpa [u_n] using
      subdifferential_dual_subsequence_tendsto_weakly
        hf B hB lam γ y0 hy_tendsto hφmono hφx
  have hgraphA :
      ∀ n, (z_n (φ n), w_n (φ n)) ∈ gra (∂ f) := by
    -- Read the `∂ f`-graph data off the packaged graph witnesses before the final closure.
    simpa [z_n, w_n] using
      (subdifferentialAuxiliaryGraphSubsequence_mem
        hf B hB lam γ y0 (φ := φ))
  have hgraphB :
      ∀ n, (x_n (φ n), u_n (φ n)) ∈ gra B := by
    -- Read the `B`-graph data off the packaged graph witnesses before the final closure.
    simpa [x_n, u_n] using
      (subdifferentialPrimalGraphSubsequence_mem
        hf B hB lam γ y0 (φ := φ))
  have hresidual :
      Tendsto (fun n ↦ z_n (φ n) - x_n (φ n)) atTop (𝓝 (0 : H)) := by
    -- Normalize the residual once so Proposition 26.5 sees the expected orientation.
    simpa [x_n, z_n] using
      subdifferentialAuxiliaryMinusPrimalSubsequence_tendsto_zero
        hf B hB hzero lam hlam hdiv γ y0 (φ := φ) hφmono
  have hdualResidual :
      Tendsto (fun n ↦ w_n (φ n) + u_n (φ n)) atTop (𝓝 (0 : H)) := by
    -- Close the last transport bridge with the already normalized dual residual.
    simpa [w_n, u_n, x_n, y_n, z_n] using
      subdifferential_dual_residual_subsequence_tendsto_zero
        hf B hB hzero lam hlam hdiv γ y0 (φ := φ) hφmono
  -- Route correction: reduce the cluster-point theorem to the fixed-subsequence graph-limit
  -- specialization from the generic Douglas--Rachford proof.
  exact
    subdifferential_weakClusterPoint_mem_graphBLimit_of_subsequence
      hf B hB lam γ y0 (y := y) (z := z) (φ := φ)
      hz_subseq hu_subseq hgraphA hgraphB hresidual hdualResidual

/-- Helper for Proposition 26.24: every weak cluster point of the primal sequence is the
resolvent limit `J_{γ B} y`. -/
private theorem subdifferential_weakClusterPoint_eq_resolventLimit
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (hzero : Set.Nonempty (primal_inclusion_solution_set (∂ f) B))
    (lam : ℕ → ℝ) (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    (γ : PosReal) (y0 : H) {y z : H}
    (hy_tendsto :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordIteration (∂ f) B hSub hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H y)))
    (hz :
      IsSequentialClusterPt
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0 n))
        (toWeakSpace ℝ H z)) :
    z = resolventMap B hB γ y := by
  have hz_graph :
      (z, (γ : ℝ)⁻¹ • (y - z)) ∈ gra B :=
    subdifferential_weakClusterPoint_mem_graphBLimit
      hf B hB hzero lam hlam hdiv γ y0 hy_tendsto hz
  have hz_mem : z ∈ J[((γ : ℝ) • B)] y :=
    (mem_resolvent_smul_iff_mem_graph B γ y z).2 hz_graph
  -- Rewrite the graph point through the singleton-valued resolvent to identify the cluster point.
  rw [resolvent_smul_eq_singleton_resolventMap_of_maximal B hB γ y] at hz_mem
  simpa using hz_mem

/-- Part (1) of Proposition 26.24: if `y ∈ Fix (R_{γ ∂ f} ∘ R_{γ B})`, then `J_{γ B} y` solves the
variational inequality `variationalInequalityProblem f B`. -/
theorem douglasRachfordSubdifferential_limit_mem_variationalInequalityProblem
    (hB : Maximal SetValuedOperator.IsMonotone B) (γ : PosReal) {y : H}
    (hy :
      y ∈ fixedPoints (reflectedResolventComposition (∂ f) B hSub hB γ)) :
    resolventMap B hB γ y ∈ VI := by
  have hVI : VI = primal_inclusion_solution_set (∂ f) B :=
    variationalInequalityProblem_eq_primal_inclusion_solution_set B
  have hy' :
      resolventMap B hB γ y ∈ primal_inclusion_solution_set (∂ f) B :=
    by
      -- Repackage this specific fixed point via the image description of the primal solution set.
      rw [primal_inclusion_solution_set_eq_image_resolvent_fixedPoints_reflectedResolventComposition
        (∂ f) B hSub hB γ]
      exact ⟨y, hy, rfl⟩
  rwa [hVI]

/-- Part (2) of Proposition 26.24: if `variationalInequalityProblem f B` is nonempty and
`∑ λ_n (2 - λ_n) = +∞`, then the Douglas--Rachford orbit
`ySeq = douglasRachfordIteration (∂ f) B γ lam y0` converges weakly to some
`y ∈ Fix (R_{γ ∂ f} ∘ R_{γ B})`. -/
theorem douglasRachfordSubdifferential_exists_limit_tendsto_weakly
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (hsol : Set.Nonempty VI)
    (lam : ℕ → ℝ) (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    (γ : PosReal) (y0 : H) :
    ∃ y ∈ fixedPoints (reflectedResolventComposition (∂ f) B hSub hB γ),
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordIteration (∂ f) B hSub hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H y)) := by
  have hVI : VI = primal_inclusion_solution_set (∂ f) B :=
    variationalInequalityProblem_eq_primal_inclusion_solution_set B
  have hzero : Set.Nonempty (primal_inclusion_solution_set (∂ f) B) := by
    rwa [hVI] at hsol
  have hlam' := hlam
  have hdiv' := hdiv
  exact
    SetValuedOperator.douglasRachfordAlgorithm_exists_fixedPoint_tendsto_weakly
      (∂ f) B hSub hB lam γ y0 hzero hlam' hdiv'

/-- Helper for Proposition 26.24: once the Chapter 26 weak-convergence owner for the primal and
auxiliary Douglas--Rachford sequences is available, both source-facing weak limits follow by
specializing to `A = ∂ f`. -/
private theorem subdifferential_primal_auxiliary_tendsto_weakly
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (lam : ℕ → ℝ) (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    (γ : PosReal) (y0 : H) {y : H}
    (hy :
      y ∈ fixedPoints (reflectedResolventComposition (∂ f) B hSub hB γ))
    (hy_tendsto :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordIteration (∂ f) B hSub hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H y))) :
    Tendsto
      (fun n ↦ toWeakSpace ℝ H (douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0 n))
      atTop (𝓝 (toWeakSpace ℝ H (resolventMap B hB γ y))) ∧
      Tendsto
        (fun n ↦
          toWeakSpace ℝ H (douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H (resolventMap B hB γ y))) := by
  let x_n := douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0
  let z_n := douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0
  have hzero : Set.Nonempty (primal_inclusion_solution_set (∂ f) B) := by
    -- A fixed point already supplies a canonical primal-inclusion solution.
    exact subdifferential_primalInclusionSolutionSet_nonempty_of_fixedPoint hf B hB γ hy
  have hx_bounded : Bornology.IsBounded (Set.range x_n) := by
    -- The weakly convergent orbit has bounded primal shadow through the resolvent.
    exact subdifferential_primalSequence_boundedRange hf B hB lam γ y0 hy_tendsto
  have hunique :
      ∀ z₁ z₂ : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x_n n)) (toWeakSpace ℝ H z₁) →
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x_n n)) (toWeakSpace ℝ H z₂) →
          z₁ = z₂ := by
    intro z₁ z₂ hz₁ hz₂
    calc
      z₁ = resolventMap B hB γ y :=
        subdifferential_weakClusterPoint_eq_resolventLimit
          hf B hB hzero lam hlam hdiv γ y0 hy_tendsto hz₁
      _ = z₂ := by
            symm
            exact
              subdifferential_weakClusterPoint_eq_resolventLimit
                hf B hB hzero lam hlam hdiv γ y0 hy_tendsto hz₂
  rcases
      (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint x_n).2
        ⟨hx_bounded, hunique⟩ with
    ⟨x, hx_tendsto_raw⟩
  have hx_cluster :
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x_n n)) (toWeakSpace ℝ H x) := by
    -- The convergent full primal sequence witnesses its own weak cluster point.
    exact ⟨id, strictMono_id, by simpa using hx_tendsto_raw⟩
  have hx_eq : x = resolventMap B hB γ y := by
    -- The unique weak cluster point is the resolvent limit identified above.
    exact
      subdifferential_weakClusterPoint_eq_resolventLimit
        hf B hB hzero lam hlam hdiv γ y0 hy_tendsto hx_cluster
  have hx_tendsto :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (x_n n))
        atTop (𝓝 (toWeakSpace ℝ H (resolventMap B hB γ y))) := by
    -- Replace the abstract weak limit by the resolvent point selected by the cluster analysis.
    simpa [x_n, hx_eq] using hx_tendsto_raw
  have hgap :
      Tendsto (fun n ↦ x_n n - z_n n) atTop (𝓝 (0 : H)) := by
    -- The strong primal-auxiliary gap transports the primal weak limit to the auxiliary shadow.
    simpa [x_n, z_n] using
      subdifferential_primal_auxiliary_gap_tendsto_zero
        hf B hB hzero lam hlam hdiv γ y0
  have hz_tendsto :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (z_n n))
        atTop (𝓝 (toWeakSpace ℝ H (resolventMap B hB γ y))) := by
    -- Subtract the strongly null gap from the primal weak limit.
    exact subdifferential_tendstoWeaklyOfSubTendstoZeroSeq hx_tendsto hgap
  exact ⟨by simpa [x_n] using hx_tendsto, by simpa [z_n] using hz_tendsto⟩

/-- Part (3) of Proposition 26.24: with
`ySeq = douglasRachfordIteration (∂ f) B γ lam y0` and
`xSeq = douglasRachfordPrimalSequence (∂ f) B γ lam y0`, if `ySeq` converges weakly to
`y ∈ Fix (R_{γ ∂ f} ∘ R_{γ B})`, then `(x_n)` converges weakly to `J_{γ B} y`. -/
theorem douglasRachfordSubdifferential_primal_tendsto_weakly
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (lam : ℕ → ℝ) (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    (γ : PosReal) (y0 : H) {y : H}
    (hy :
      y ∈ fixedPoints (reflectedResolventComposition (∂ f) B hSub hB γ))
    (hy_tendsto :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordIteration (∂ f) B hSub hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H y))) :
    Tendsto
      (fun n ↦ toWeakSpace ℝ H (douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0 n))
      atTop (𝓝 (toWeakSpace ℝ H (resolventMap B hB γ y))) := by
  -- Project the primal weak limit from the shared subdifferential weak-convergence package.
  exact
    (subdifferential_primal_auxiliary_tendsto_weakly
      hf B hB lam hlam hdiv γ y0 hy hy_tendsto).1

/-- Part (4) of Proposition 26.24: with
`ySeq = douglasRachfordIteration (∂ f) B γ lam y0` and
`zSeq = douglasRachfordAuxiliarySequence (∂ f) B γ lam y0`, if `ySeq` converges weakly to
`y ∈ Fix (R_{γ ∂ f} ∘ R_{γ B})`, then `(z_n)` converges weakly to `J_{γ B} y`. -/
theorem douglasRachfordSubdifferential_auxiliary_tendsto_weakly
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (lam : ℕ → ℝ) (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    (γ : PosReal) (y0 : H) {y : H}
    (hy :
      y ∈ fixedPoints (reflectedResolventComposition (∂ f) B hSub hB γ))
    (hy_tendsto :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordIteration (∂ f) B hSub hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H y))) :
    Tendsto
      (fun n ↦ toWeakSpace ℝ H (douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0 n))
      atTop (𝓝 (toWeakSpace ℝ H (resolventMap B hB γ y))) := by
  -- Project the auxiliary weak limit from the shared subdifferential weak-convergence package.
  exact
    (subdifferential_primal_auxiliary_tendsto_weakly
      hf B hB lam hlam hdiv γ y0 hy hy_tendsto).2

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 26.24: if a localized modulus is forced below `0`, then the two
points coincide. -/
private theorem point_eq_of_modulus_le_zero
    {p q : H} {φ : NNReal → EReal}
    (hφ_mono : Monotone φ)
    (hφ_zero : ∀ r : NNReal, φ r = 0 ↔ r = 0)
    (hineq : φ ‖p - q‖₊ ≤ 0) :
    p = q := by
  -- Nonnegativity of the modulus collapses the lower bound to equality at `0`.
  have hφ_nonneg : (0 : EReal) ≤ φ ‖p - q‖₊ := by
    rw [← (hφ_zero 0).2 rfl]
    exact hφ_mono bot_le
  have hφ_eq_zero : φ ‖p - q‖₊ = 0 := le_antisymm hineq hφ_nonneg
  have hdist_zero : ‖p - q‖₊ = 0 := (hφ_zero _).1 hφ_eq_zero
  have hnorm_zero : ‖p - q‖ = 0 := by
    simpa using congrArg (fun r : NNReal ↦ (r : ℝ)) hdist_zero
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)

/-- Helper for Proposition 26.24: under the localized uniform branch, every primal solution of
`(∂ f) + B` equals the resolvent point selected by the fixed point `y`. -/
private theorem subdifferential_primalSolution_eq_resolventLimit_of_uniformBranch
    (hB : Maximal SetValuedOperator.IsMonotone B) (γ : PosReal) {y q : H}
    (hy :
      y ∈ fixedPoints (reflectedResolventComposition (∂ f) B hSub hB γ))
    (hUniform :
      (∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ f).dom →
          (∂ f).IsUniformlyMonotoneOn S) ∨
        ∀ S : Set H,
          S.Nonempty → Bornology.IsBounded S → S ⊆ B.dom → B.IsUniformlyMonotoneOn S)
    (hq : q ∈ primal_inclusion_solution_set (∂ f) B) :
    q = resolventMap B hB γ y := by
  let x : H := resolventMap B hB γ y
  let u : H := yosidaApproximationMap B hB γ y
  rcases
      (mem_primal_inclusion_solution_set_iff_exists_mem_dual_inclusion_solution_set
        (∂ f) B).1 hq with
    ⟨uq, _huqD, hqA, hqB⟩
  have hx_graph := subdifferential_limitGraphData hf B hB γ hy
  have hxA : -u ∈ (∂ f) x := by
    simpa [x, u] using hx_graph.1
  have hxB : u ∈ B x := by
    simpa [x, u] using hx_graph.2
  have hA_mono : (∂ f).IsMonotone := SetValuedOperator.Maximal.isMonotone hSub
  have hB_mono : B.IsMonotone := SetValuedOperator.Maximal.isMonotone hB
  rw [isMonotone_iff] at hA_mono hB_mono
  rcases hUniform with hUniformA | hUniformB
  · let S : Set H := Set.insert x ({q} : Set H)
    have hxS : x ∈ S := by
      exact Set.mem_insert x ({q} : Set H)
    have hqS : q ∈ S := by
      exact Set.mem_insert_of_mem x (by simp)
    have hS_nonempty : S.Nonempty := ⟨x, hxS⟩
    have hS_bounded : Bornology.IsBounded S := by
      exact ((Set.finite_singleton q).insert x).isBounded
    have hS_subA : S ⊆ (∂ f).dom := by
      intro r hr
      rcases Set.mem_insert_iff.mp hr with hr | hr
      · subst r
        exact (SetValuedOperator.mem_dom_iff (∂ f) x).2 ⟨-u, hxA⟩
      · rcases Set.mem_singleton_iff.mp hr with rfl
        exact (SetValuedOperator.mem_dom_iff (∂ f) _).2 ⟨-uq, hqA⟩
    rcases hUniformA S hS_nonempty hS_bounded hS_subA with ⟨φ, hφ⟩
    have hineq :
        φ ‖q - x‖₊ ≤ (0 : EReal) := by
      have hAineq :
          φ ‖q - x‖₊ ≤ (⟪q - x, (-uq) - (-u)⟫_ℝ : EReal) := by
        -- Apply the localized `∂ f` modulus to the primal solution and the limit graph point.
        simpa [x, u] using hφ.ineq hqS hxS hqA hxA
      have hupper_real : ⟪q - x, (-uq) - (-u)⟫_ℝ ≤ 0 := by
        have hpair_nonneg : 0 ≤ ⟪q - x, uq - u⟫_ℝ := hB_mono hqB hxB
        have hneg_eq : ⟪q - x, (-uq) - (-u)⟫_ℝ = -⟪q - x, uq - u⟫_ℝ := by
          have hterm : (-uq) - (-u) = -(uq - u) := by
            abel_nf
          rw [hterm, inner_neg_right]
        rw [hneg_eq]
        linarith
      have hupper : (⟪q - x, (-uq) - (-u)⟫_ℝ : EReal) ≤ 0 := by
        exact_mod_cast hupper_real
      exact le_trans hAineq hupper
    exact point_eq_of_modulus_le_zero hφ.monotone hφ.modulus_eq_zero_iff hineq
  · let S : Set H := Set.insert x ({q} : Set H)
    have hxS : x ∈ S := by
      exact Set.mem_insert x ({q} : Set H)
    have hqS : q ∈ S := by
      exact Set.mem_insert_of_mem x (by simp)
    have hS_nonempty : S.Nonempty := ⟨x, hxS⟩
    have hS_bounded : Bornology.IsBounded S := by
      exact ((Set.finite_singleton q).insert x).isBounded
    have hS_subB : S ⊆ B.dom := by
      intro r hr
      rcases Set.mem_insert_iff.mp hr with hr | hr
      · subst r
        exact (SetValuedOperator.mem_dom_iff B x).2 ⟨u, hxB⟩
      · rcases Set.mem_singleton_iff.mp hr with rfl
        exact (SetValuedOperator.mem_dom_iff B _).2 ⟨uq, hqB⟩
    rcases hUniformB S hS_nonempty hS_bounded hS_subB with ⟨φ, hφ⟩
    have hineq :
        φ ‖q - x‖₊ ≤ (0 : EReal) := by
      have hBineq :
          φ ‖q - x‖₊ ≤ (⟪q - x, uq - u⟫_ℝ : EReal) := by
        -- Apply the localized `B` modulus to the primal solution and the limit graph point.
        simpa [x, u] using hφ.ineq hqS hxS hqB hxB
      have hupper_real : ⟪q - x, uq - u⟫_ℝ ≤ 0 := by
        have hpair_nonneg : 0 ≤ -⟪q - x, uq - u⟫_ℝ := by
          have hpairA : 0 ≤ ⟪q - x, (-uq) - (-u)⟫_ℝ := hA_mono hqA hxA
          have hneg_eq : -⟪q - x, uq - u⟫_ℝ = ⟪q - x, (-uq) - (-u)⟫_ℝ := by
            have hterm : (-(uq - u) : H) = (-uq) - (-u) := by
              abel_nf
            calc
              -⟪q - x, uq - u⟫_ℝ = ⟪q - x, -(uq - u)⟫_ℝ := by
                rw [inner_neg_right]
              _ = ⟪q - x, (-uq) - (-u)⟫_ℝ := by
                rw [hterm]
          rw [hneg_eq]
          exact hpairA
        linarith
      have hupper : (⟪q - x, uq - u⟫_ℝ : EReal) ≤ 0 := by
        exact_mod_cast hupper_real
      exact le_trans hBineq hupper
    exact point_eq_of_modulus_le_zero hφ.monotone hφ.modulus_eq_zero_iff hineq

/-- Helper for Proposition 26.24: under the localized uniform branch, the primal inclusion
solution set is the singleton `{J_{γ B} y}`. -/
private theorem subdifferential_unique_primal_solution_of_uniformBranch
    (hB : Maximal SetValuedOperator.IsMonotone B) (γ : PosReal) {y : H}
    (hy :
      y ∈ fixedPoints (reflectedResolventComposition (∂ f) B hSub hB γ))
    (hUniform :
      (∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ f).dom →
          (∂ f).IsUniformlyMonotoneOn S) ∨
        ∀ S : Set H,
          S.Nonempty → Bornology.IsBounded S → S ⊆ B.dom → B.IsUniformlyMonotoneOn S) :
    primal_inclusion_solution_set (∂ f) B = {resolventMap B hB γ y} := by
  ext q
  constructor
  · intro hq
    -- Every primal solution equals the resolvent point fixed by the uniform branch.
    exact Set.mem_singleton_iff.mpr <|
      subdifferential_primalSolution_eq_resolventLimit_of_uniformBranch
        hf B hB γ hy hUniform hq
  · intro hq
    rcases Set.mem_singleton_iff.mp hq with rfl
    -- The fixed point itself yields the canonical primal solution.
    rw [primal_inclusion_solution_set_eq_image_resolvent_fixedPoints_reflectedResolventComposition
      (∂ f) B hSub hB γ]
    exact ⟨y, hy, rfl⟩

/-- Helper for Proposition 26.24: under the localized uniform branch, both the primal and
auxiliary Douglas-Rachford shadows converge strongly to the limit resolvent point. -/
private theorem subdifferential_primal_auxiliary_tendsto_of_uniform_branch
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (hzero : Set.Nonempty (primal_inclusion_solution_set (∂ f) B))
    (lam : ℕ → ℝ) (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    (γ : PosReal) (y0 : H) {y : H}
    (hy :
      y ∈ fixedPoints (reflectedResolventComposition (∂ f) B hSub hB γ))
    (hy_tendsto :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordIteration (∂ f) B hSub hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H y)))
    (hUniform :
      (∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ f).dom →
          (∂ f).IsUniformlyMonotoneOn S) ∨
        ∀ S : Set H,
          S.Nonempty → Bornology.IsBounded S → S ⊆ B.dom → B.IsUniformlyMonotoneOn S) :
    Tendsto
      (douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0)
      atTop (𝓝 (resolventMap B hB γ y)) ∧
      Tendsto
        (douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0)
        atTop (𝓝 (resolventMap B hB γ y)) := by
  -- Route correction: specialize the canonical Theorem 26.11 owner at `A = ∂ f` instead of
  -- rebuilding the uniform-monotonicity branch inside this proposition.
  -- The only local normalization is the private auxiliary-sequence alias used in this file.
  simpa [ERealFunction.douglasRachfordAuxiliarySequence] using
    douglasRachfordAlgorithm_primal_auxiliary_tendsto_of_uniformlyMonotoneOnEveryBoundedSubset
      (A := ∂ f) (B := B) (hA := hSub) (hB := hB) (hzero := hzero)
      (lam := lam) (hlam := hlam) (hdiv := hdiv) (γ := γ) (y0 := y0)
      (y := y) hy hy_tendsto hUniform

/-- Helper for Proposition 26.24: under the Douglas--Rachford hypotheses and either the source
uniform convexity alternative for `f` or uniform monotonicity of `B`, the primal and auxiliary
sequences converge strongly to the unique solution of `variationalInequalityProblem f B`. -/
theorem subdifferential_primal_auxiliary_tendsto_and_solution_eq_singleton
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (hsol : Set.Nonempty VI)
    (lam : ℕ → ℝ) (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    (γ : PosReal) (y0 : H)
    (hUniform :
      (∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ f).dom →
          ∃ φ : NNReal → EReal, UniformlyConvexOn f S φ) ∨
        ∀ S : Set H,
          S.Nonempty → Bornology.IsBounded S → S ⊆ B.dom → B.IsUniformlyMonotoneOn S) :
    ∃ y ∈ fixedPoints (reflectedResolventComposition (∂ f) B hSub hB γ),
      Tendsto
        (douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0)
        atTop (𝓝 (resolventMap B hB γ y)) ∧
        Tendsto
          (douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0)
          atTop (𝓝 (resolventMap B hB γ y)) ∧
        VI = ({resolventMap B hB γ y} : Set H) := by
  -- Route correction: the closing proof should rewrite `VI` to the primal-inclusion solution set,
  -- extract `⟨y, hy, hy_tendsto⟩` from the weak package above, convert `hUniform` with
  -- `subdifferential_uniformMonotoneOnEveryBoundedSubset_or`. The singleton half is now
  -- localized in this file; only the strong-convergence half still needs the missing owner.
  have hVI : VI = primal_inclusion_solution_set (∂ f) B :=
    variationalInequalityProblem_eq_primal_inclusion_solution_set B
  have hzero : Set.Nonempty (primal_inclusion_solution_set (∂ f) B) := by
    -- Translate the source-facing nonemptiness assumption to the canonical primal inclusion set.
    rwa [hVI] at hsol
  have hUniform' :
      (∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ f).dom →
          (∂ f).IsUniformlyMonotoneOn S) ∨
        ∀ S : Set H,
          S.Nonempty → Bornology.IsBounded S → S ⊆ B.dom → B.IsUniformlyMonotoneOn S :=
    subdifferential_uniformMonotoneOnEveryBoundedSubset_or
      (f := f) (B := B) (mem_gammaZero_iff.mp hf).2 hUniform
  obtain ⟨y, hy, hy_tendsto⟩ :=
    douglasRachfordSubdifferential_exists_limit_tendsto_weakly
      hf B hB hsol lam hlam hdiv γ y0
  have hsingletonPI :
      primal_inclusion_solution_set (∂ f) B = {resolventMap B hB γ y} := by
    -- The localized uniqueness lemma already identifies the canonical solution set.
    exact subdifferential_unique_primal_solution_of_uniformBranch hf B hB γ hy hUniform'
  have hsingletonVI : VI = ({resolventMap B hB γ y} : Set H) := by
    -- Rewrite the canonical singleton conclusion back to the source-facing VI solution set.
    calc
      VI = primal_inclusion_solution_set (∂ f) B := hVI
      _ = ({resolventMap B hB γ y} : Set H) := hsingletonPI
  have hstrong :
      Tendsto
        (douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0)
        atTop (𝓝 (resolventMap B hB γ y)) ∧
        Tendsto
          (douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0)
          atTop (𝓝 (resolventMap B hB γ y)) := by
    -- Route correction: localize the Theorem 26.11(7) modulus-pairing skeleton at `A = ∂ f`.
    exact
      subdifferential_primal_auxiliary_tendsto_of_uniform_branch
        hf B hB hzero lam hlam hdiv γ y0 hy hy_tendsto hUniform'
  exact ⟨y, hy, hstrong.1, hstrong.2, hsingletonVI⟩

/-- Part (5) of Proposition 26.24: assume that either `f` is uniformly convex on every
nonempty bounded subset of `(∂ f).dom`, or `B` is uniformly monotone on every nonempty bounded
subset of `B.dom`.
Then `(x_n)` converges strongly to the unique solution of
`variationalInequalityProblem f B`. -/
theorem
    douglasRachfordSubdifferential_primal_tendsto_to_uniqueSolution_of_uniformHypothesis
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (hsol : Set.Nonempty VI)
    (lam : ℕ → ℝ) (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    (γ : PosReal) (y0 : H)
    (hUniform :
      (∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ f).dom →
          ∃ φ : NNReal → EReal, UniformlyConvexOn f S φ) ∨
        ∀ S : Set H,
          S.Nonempty → Bornology.IsBounded S → S ⊆ B.dom → B.IsUniformlyMonotoneOn S) :
    ∃ y ∈ fixedPoints (reflectedResolventComposition (∂ f) B hSub hB γ),
      Tendsto
        (douglasRachfordPrimalSequence (∂ f) B hSub hB γ lam y0)
        atTop (𝓝 (resolventMap B hB γ y)) ∧
        VI = ({resolventMap B hB γ y} : Set H) := by
  obtain ⟨y, hy, hprimal, _, hsingleton⟩ :=
    subdifferential_primal_auxiliary_tendsto_and_solution_eq_singleton
      hf B hB hsol lam hlam hdiv γ y0 hUniform
  exact ⟨y, hy, hprimal, hsingleton⟩

/-- Part (6) of Proposition 26.24: under the uniform hypothesis of part (5), `(z_n)`
converges strongly to the unique solution of `variationalInequalityProblem f B`. -/
theorem
    douglasRachfordSubdifferential_auxiliary_tendsto_to_uniqueSolution_of_uniformHypothesis
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (hsol : Set.Nonempty VI)
    (lam : ℕ → ℝ) (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    (γ : PosReal) (y0 : H)
    (hUniform :
      (∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ f).dom →
          ∃ φ : NNReal → EReal, UniformlyConvexOn f S φ) ∨
        ∀ S : Set H,
          S.Nonempty → Bornology.IsBounded S → S ⊆ B.dom → B.IsUniformlyMonotoneOn S) :
    ∃ y ∈ fixedPoints (reflectedResolventComposition (∂ f) B hSub hB γ),
      Tendsto
        (douglasRachfordAuxiliarySequence (∂ f) B hSub hB γ lam y0)
        atTop (𝓝 (resolventMap B hB γ y)) ∧
        VI = ({resolventMap B hB γ y} : Set H) := by
  obtain ⟨y, hy, _, hauxiliary, hsingleton⟩ :=
    subdifferential_primal_auxiliary_tendsto_and_solution_eq_singleton
      hf B hB hsol lam hlam hdiv γ y0 hUniform
  exact ⟨y, hy, hauxiliary, hsingleton⟩

end

end ERealFunction
