import BauschkeLean.Chap03.Definition_3_8
import BauschkeLean.Chap04.Corollary_4_51
import BauschkeLean.Chap04.Definition_4_33
import BauschkeLean.Chap04.Proposition_4_9
import BauschkeLean.Chap30.Theorem_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {D : Set H}

/- Source/core/bridge triage:
- `source-facing`: the corollary converges to the metric projection onto the ambient common
  fixed-point set of the finite averaged family on `D`.
- `core/canonical`: the reusable owner for the ordered composition is `finiteComposition T`, with
  `fixedPoints_finiteComposition_eq_iInter_fixedPoints_of_averagedWith` supplying the fixed-point
  identification.
- `bridge/view`: because the operators live on the subtype `D`, the ambient projection target is
  the image `Subtype.val '' (⋂ i, Function.fixedPoints (T i) : Set D)`.
-/

variable {m : ℕ+} (T : Fin m → D → D)

local notation "FixFamily" => (Subtype.val '' (⋂ i, Function.fixedPoints (T i) : Set D) : Set H)
local notation "AmbientMap[" i "]" => (fun x : D ↦ (T i x : H))

/-- Parameters in `]0,1[` also lie in `[0,1]`, which is the interval needed by
`halpernIterationOn`. -/
theorem halpernParams_mem_Icc {lam : ℕ → ℝ}
    (hlam_mem : ∀ n, lam n ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ n, lam n ∈ Set.Icc (0 : ℝ) 1 :=
  fun n ↦ ⟨(hlam_mem n).1.le, (hlam_mem n).2.le⟩

/-- Helper for Corollary 30.3: extend the ordered subtype composition to the ambient Hilbert space
by acting as the composition on `D` and as the identity outside `D`. -/
private noncomputable def ambient_finiteComposition : H → H :=
  fun x ↦
    @dite H (x ∈ D) (Classical.decPred (fun y : H ↦ y ∈ D) x)
      (fun hx ↦ (((finiteComposition T) ⟨x, hx⟩ : D) : H))
      (fun _ ↦ x)

/-- Helper for Corollary 30.3: on `D`, the ambient extension agrees with the ordered subtype
composition. -/
private theorem ambient_finiteComposition_apply {x : H} (hx : x ∈ D) :
    ambient_finiteComposition T x = (((finiteComposition T) ⟨x, hx⟩ : D) : H) := by
  -- On-domain points take the subtype branch of the ambient extension.
  simp [ambient_finiteComposition, hx]

/-- Helper for Corollary 30.3: the ambient extension still maps `D` into itself. -/
private theorem ambient_finiteComposition_mapsTo :
    Set.MapsTo (ambient_finiteComposition T) D D := by
  intro x hx
  -- Reduce the ambient extension to the subtype composition at points of `D`.
  rw [ambient_finiteComposition_apply T hx]
  exact (finiteComposition T ⟨x, hx⟩).2

/-- Helper for Corollary 30.3: every averaged map on `D` is nonexpansive. -/
private theorem lipschitzWith_one_of_averagedWith_local {α : ℝ} {S : D → H}
    (hS : AveragedWith α S) : LipschitzWith 1 S := by
  rcases averagedWith_iff.mp hS with ⟨hα, R, hR, hS_eq⟩
  have hα_nonneg : 0 ≤ α := hα.1.le
  have h_one_sub_nonneg : 0 ≤ 1 - α := sub_nonneg.mpr hα.2.le
  -- Expand the averaged representation and compare with the nonexpansive witness `R`.
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  have hRxy : ‖R x - R y‖ ≤ ‖(x : H) - y‖ := by
    simpa [Subtype.dist_eq, dist_eq_norm] using hR.dist_le_mul x y
  have hxy :
      S x - S y = (1 - α) • ((x : H) - y) + α • (R x - R y) := by
    calc
      S x - S y
          = ((1 - α) • (x : H) + α • R x) - ((1 - α) • (y : H) + α • R y) := by
              rw [hS_eq]
      _ = (1 - α) • ((x : H) - y) + α • (R x - R y) := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  simpa [Subtype.dist_eq, dist_eq_norm, one_mul] using
    calc
      ‖S x - S y‖ = ‖(1 - α) • ((x : H) - y) + α • (R x - R y)‖ := by
        rw [hxy]
      _ ≤ ‖(1 - α) • ((x : H) - y)‖ + ‖α • (R x - R y)‖ := norm_add_le _ _
      _ = (1 - α) * ‖(x : H) - y‖ + α * ‖R x - R y‖ := by
            rw [norm_smul, norm_smul]
            simp [Real.norm_eq_abs, abs_of_nonneg h_one_sub_nonneg, abs_of_nonneg hα_nonneg]
      _ ≤ (1 - α) * ‖(x : H) - y‖ + α * ‖(x : H) - y‖ := by
            nlinarith [hRxy, norm_nonneg ((x : H) - y)]
      _ = ‖(x : H) - y‖ := by
            ring

/-- Helper for Corollary 30.3: the ambient extension is nonexpansive on `D` because each averaged
factor is nonexpansive and finite compositions preserve the Lipschitz constant `1`. -/
private theorem ambient_finiteComposition_lipschitzOnWith_one_of_averaged
    (hAveraged : ∀ i, ∃ α, AveragedWith α (AmbientMap[i])) :
    LipschitzOnWith 1 (ambient_finiteComposition T) D := by
  have hComp : LipschitzWith 1 (finiteComposition T) := by
    refine lipschitzWith_finiteComposition T ?_
    intro i
    rcases hAveraged i with ⟨α, hα⟩
    -- View each averaged factor as a nonexpansive self-map of the subtype `D`.
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    simpa [Subtype.dist_eq, one_mul] using
      (lipschitzWith_one_of_averagedWith_local hα).dist_le_mul x y
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  -- Once both inputs lie in `D`, the ambient extension is exactly the subtype composition.
  simpa [Subtype.dist_eq, one_mul, ambient_finiteComposition_apply T hx,
    ambient_finiteComposition_apply T hy] using hComp.dist_le_mul ⟨x, hx⟩ ⟨y, hy⟩

/-- Helper for Corollary 30.3: the ambient fixed-point set of the extended finite composition is
exactly the ambient image of the common subtype fixed-point set. -/
private theorem fixedPointSetOn_ambient_finiteComposition_eq_commonFixedPoints
    (hAveraged : ∀ i, ∃ α, AveragedWith α (AmbientMap[i]))
    (hFix_nonempty : (⋂ i, Function.fixedPoints (T i) : Set D).Nonempty) :
    fixedPointSetOn D (ambient_finiteComposition T) = FixFamily := by
  have hComp_fixed :
      Function.fixedPoints (finiteComposition T) = ⋂ i, Function.fixedPoints (T i) :=
    fixedPoints_finiteComposition_eq_iInter_fixedPoints_of_averagedWith
      (T := T) hAveraged hFix_nonempty
  ext z
  constructor
  · intro hz
    rcases mem_fixedPointSetOn_iff.mp hz with ⟨hzD, hzfix⟩
    have hzComp : ⟨z, hzD⟩ ∈ Function.fixedPoints (finiteComposition T) := by
      rw [Function.mem_fixedPoints_iff]
      apply Subtype.ext
      -- The ambient fixed-point relation is the subtype one after restricting to `D`.
      simpa [ambient_finiteComposition_apply T hzD] using hzfix
    have hzCommon : ⟨z, hzD⟩ ∈ ⋂ i, Function.fixedPoints (T i) := by
      rwa [hComp_fixed] at hzComp
    exact ⟨⟨z, hzD⟩, hzCommon, rfl⟩
  · rintro ⟨zD, hzCommon, rfl⟩
    have hzComp : zD ∈ Function.fixedPoints (finiteComposition T) := by
      rw [hComp_fixed]
      exact hzCommon
    rw [mem_fixedPointSetOn_iff]
    refine ⟨zD.2, ?_⟩
    have hzfix : finiteComposition T zD = zD := Function.mem_fixedPoints_iff.mp hzComp
    -- Coercing the subtype fixed-point equation yields the ambient one on `D`.
    simpa [ambient_finiteComposition_apply T zD.2] using congrArg Subtype.val hzfix

/-- Helper for Corollary 30.3: a nonempty common fixed-point set of averaged self-maps on a
nonempty closed convex subset of a real Hilbert space is Chebyshev in the ambient space. -/
private theorem isChebyshev_subtypeImage_iInter_fixedPoints_of_nonempty_closed_convex_averaged
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (hAveraged : ∀ i, ∃ α, AveragedWith α (AmbientMap[i]))
    (hFix_nonempty : (⋂ i, Function.fixedPoints (T i) : Set D).Nonempty) :
    IsChebyshev FixFamily := by
  have hFixFamily_nonempty : Set.Nonempty FixFamily := by
    rcases hFix_nonempty with ⟨z, hz⟩
    exact ⟨(z : H), ⟨z, hz, rfl⟩⟩
  have hAmbient_nonexp : LipschitzOnWith 1 (ambient_finiteComposition T) D :=
    ambient_finiteComposition_lipschitzOnWith_one_of_averaged T hAveraged
  have hAmbient_fix_nonempty :
      (fixedPointSetOn D (ambient_finiteComposition T)).Nonempty := by
    -- Transport the common fixed point through the ambient fixed-point-set identification.
    rw [fixedPointSetOn_ambient_finiteComposition_eq_commonFixedPoints T hAveraged hFix_nonempty]
    exact hFixFamily_nonempty
  have hAmbient_closed_convex :
      IsClosed (fixedPointSetOn D (ambient_finiteComposition T)) ∧
        Convex ℝ (fixedPointSetOn D (ambient_finiteComposition T)) :=
    isClosed_and_convex_fixedPointSetOn_of_quasinonexpansive
      hAmbient_nonexp.quasinonexpansiveOn hD_closed hD_convex
  -- Replace the ambient fixed-point set by the common fixed-point image at the end.
  rw [← fixedPointSetOn_ambient_finiteComposition_eq_commonFixedPoints T hAveraged hFix_nonempty]
  exact
    isChebyshev_of_nonempty_isClosed_convex
      hAmbient_fix_nonempty hAmbient_closed_convex.1 hAmbient_closed_convex.2

/-- Helper for Corollary 30.3: the ambient Halpern orbit of the extended finite composition agrees
with the subtype Halpern orbit after coercion. -/
private theorem halpernIteration_ambient_finiteComposition_eq_halpernIterationOn_finiteComposition
    (hD_convex : Convex ℝ D) (x x₀ : D)
    {lam : ℕ → ℝ} (hlam_mem : ∀ n, lam n ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ n,
      halpernIteration (ambient_finiteComposition T) lam (x : H) (x₀ : H) n =
        (halpernIterationOn hD_convex (finiteComposition T) lam
          (halpernParams_mem_Icc hlam_mem) x x₀ n : H) := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ihn =>
      -- Both recursions use the same affine Halpern step once the previous iterates agree.
      rw [halpernIteration_succ, halpernIterationOn_succ, ihn]
      simp [ambient_finiteComposition_apply T
        (halpernIterationOn hD_convex (finiteComposition T) lam
          (halpernParams_mem_Icc hlam_mem) x x₀ n).2]

/-- Corollary 30.3: if `D` is a nonempty closed convex subset of a real Hilbert space, `T 0`,
..., `T (m - 1)` are averaged self-maps of `D` with a common fixed point, and the Halpern
iteration on `D` generated by their ordered composition has parameters `lam`, anchor `x`, and
initial point `x₀`, then it converges strongly to the metric projection of `x` onto the common
fixed-point set. -/
theorem halpern_iteration_tendsto_projection_commonFixedPoints_of_averaged_finiteComposition
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (x x₀ : D)
    (hAveraged : ∀ i, ∃ α, AveragedWith α (AmbientMap[i]))
    (hFix_nonempty : (⋂ i, Function.fixedPoints (T i) : Set D).Nonempty)
    {lam : ℕ → ℝ}
    (hlam_mem : ∀ n, lam n ∈ Set.Ioo (0 : ℝ) 1)
    (hlam_tendsto_zero : Tendsto lam atTop (𝓝 (0 : ℝ)))
    (hlam_sum_diverges : Tendsto (fun N ↦ (Finset.range N).sum (fun n ↦ lam n)) atTop atTop)
    (hlam_successive_diff_summable : Summable (fun n ↦ |lam (n + 1) - lam n|)) :
    Tendsto
      (fun n ↦
        (halpernIterationOn hD_convex (finiteComposition T) lam
          (halpernParams_mem_Icc hlam_mem) x x₀ n : H))
      atTop
      (𝓝
        (P[FixFamily,
          isChebyshev_subtypeImage_iInter_fixedPoints_of_nonempty_closed_convex_averaged
            T hD_closed hD_convex hAveraged hFix_nonempty] (x : H))) := by
  have hAmbient_maps : Set.MapsTo (ambient_finiteComposition T) D D :=
    ambient_finiteComposition_mapsTo T
  have hAmbient_nonexp : LipschitzOnWith 1 (ambient_finiteComposition T) D :=
    ambient_finiteComposition_lipschitzOnWith_one_of_averaged T hAveraged
  have hFixFamily_nonempty : Set.Nonempty FixFamily := by
    rcases hFix_nonempty with ⟨z, hz⟩
    exact ⟨(z : H), ⟨z, hz, rfl⟩⟩
  have hAmbient_fix_nonempty :
      (fixedPointSetOn D (ambient_finiteComposition T)).Nonempty := by
    -- The common subtype fixed point is also an ambient fixed point of the extension.
    rw [fixedPointSetOn_ambient_finiteComposition_eq_commonFixedPoints T hAveraged hFix_nonempty]
    exact hFixFamily_nonempty
  let hAmbient_cheb : IsChebyshev (fixedPointSetOn D (ambient_finiteComposition T)) :=
    isChebyshev_of_nonempty_isClosed_convex
      hAmbient_fix_nonempty
      (isClosed_and_convex_fixedPointSetOn_of_quasinonexpansive
        hAmbient_nonexp.quasinonexpansiveOn hD_closed hD_convex).1
      (isClosed_and_convex_fixedPointSetOn_of_quasinonexpansive
        hAmbient_nonexp.quasinonexpansiveOn hD_closed hD_convex).2
  have hProjection :
      P[fixedPointSetOn D (ambient_finiteComposition T), hAmbient_cheb] (x : H) =
        P[FixFamily,
          isChebyshev_subtypeImage_iInter_fixedPoints_of_nonempty_closed_convex_averaged
            T hD_closed hD_convex hAveraged hFix_nonempty] (x : H) := by
    -- Identify the two projection targets through the common fixed-point-set equality.
    apply eq_projectionPoint_of_isBestApproximation FixFamily
      (isChebyshev_subtypeImage_iInter_fixedPoints_of_nonempty_closed_convex_averaged
        T hD_closed hD_convex hAveraged hFix_nonempty)
    simpa [hAmbient_cheb,
      fixedPointSetOn_ambient_finiteComposition_eq_commonFixedPoints T hAveraged hFix_nonempty] using
      projectionPoint_isBestApproximation
        (fixedPointSetOn D (ambient_finiteComposition T)) hAmbient_cheb (x : H)
  have hOrbit :
      halpernIteration (ambient_finiteComposition T) lam (x : H) (x₀ : H) =
        fun n ↦
          (halpernIterationOn hD_convex (finiteComposition T) lam
            (halpernParams_mem_Icc hlam_mem) x x₀ n : H) := by
    funext n
    exact
      halpernIteration_ambient_finiteComposition_eq_halpernIterationOn_finiteComposition
        T hD_convex x x₀ hlam_mem n
  -- Apply Theorem 30.1 to the ambient extension and rewrite both the orbit and the projection.
  simpa [hOrbit, hProjection] using
    (halpern_iteration_tendsto_projection_fixedPointSetOn
      (hD_closed := hD_closed) (hD_convex := hD_convex)
      (hT_nonexp := hAmbient_nonexp) (hFix_nonempty := hAmbient_fix_nonempty)
      (D := D) (T := ambient_finiteComposition T) (x := (x : H)) (x0 := (x₀ : H)) (lam := lam)
      x.2 hAmbient_maps x₀.2 hlam_mem hlam_tendsto_zero hlam_sum_diverges
      hlam_successive_diff_summable)

end
