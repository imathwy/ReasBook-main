import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0001_Definition_II_1_extra_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped unitInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Path

section Differentiability

/-- Helper for Lemma II.1-extra-3: real affine reparametrizations are `C¹` on any set. -/
lemma contDiffOn_affine_reparam (m c : ℝ) (s : Set ℝ) :
    ContDiffOn ℝ 1 (fun t : ℝ ↦ m * t + c) s := by
  -- Real affine maps are built from the identity by scalar multiplication and translation.
  simpa using
    ((contDiffOn_const : ContDiffOn ℝ 1 (fun _ : ℝ ↦ m) s).mul contDiffOn_id).add
      (contDiffOn_const : ContDiffOn ℝ 1 (fun _ : ℝ ↦ c) s)

/-- Helper for Lemma II.1-extra-3: a straight segment path is globally differentiable. -/
lemma segment_isDifferentiable (x y : E) : (Path.segment x y).IsDifferentiable := by
  -- The extension of a straight segment agrees with the affine line map on `I`.
  rw [Path.IsDifferentiable]
  have hline : ContDiffOn ℝ 1 (ContinuousAffineMap.lineMap (R := ℝ) x y) I :=
    (ContinuousAffineMap.contDiff (ContinuousAffineMap.lineMap (R := ℝ) x y)).contDiffOn
  refine hline.congr ?_
  intro t ht
  simpa using Path.eqOn_extend_segment x y ht

/-- Helper for Lemma II.1-extra-3: straight segments are piecewise differentiable. -/
lemma segment_isPiecewiseDifferentiable (x y : E) :
    (Path.segment x y).IsPiecewiseDifferentiable := by
  -- Promote global differentiability to a one-piece subdivision of `[0,1]`.
  exact (segment_isDifferentiable x y).isPiecewiseDifferentiable

/-- Helper for Lemma II.1-extra-3: appending a differentiable path to a piecewise differentiable
path preserves piecewise differentiability. -/
theorem IsPiecewiseDifferentiable.trans_of_isDifferentiable {x y z : E} {γ₁ : Path x y}
    {γ₂ : Path y z} (hγ₁ : γ₁.IsPiecewiseDifferentiable) (hγ₂ : γ₂.IsDifferentiable) :
    (γ₁.trans γ₂).IsPiecewiseDifferentiable := by
  rcases hγ₁ with ⟨n, subdiv, hsubdiv, h0, h1, hpieces⟩
  let subdiv' : Fin (n + 3) → ℝ := Fin.snoc (fun i : Fin (n + 2) ↦ subdiv i / 2) 1
  have hsubdiv' : StrictMono subdiv' := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    induction i using Fin.lastCases with
    | cast i =>
        have hi : subdiv i.castSucc < subdiv i.succ := hsubdiv Fin.castSucc_lt_succ
        have hscaled : subdiv i.castSucc / 2 < subdiv i.succ / 2 := by
          linarith
        simpa only [subdiv', Fin.snoc_castSucc, Fin.succ_castSucc] using hscaled
    | last =>
        have hlast : subdiv (Fin.last (n + 1)) / 2 < (1 : ℝ) := by
          rw [h1]
          norm_num
        simpa only [subdiv', Fin.snoc_castSucc, Fin.snoc_last, Fin.succ_last, h1] using hlast
  refine ⟨n + 1, subdiv', hsubdiv', ?_, ?_, ?_⟩
  · -- The rescaled subdivision still starts at `0`.
    simp [subdiv', h0]
  · -- The appended final breakpoint is `1`.
    simp [subdiv']
  · intro i
    cases i using Fin.lastCases with
    | cast i =>
        -- On the rescaled old pieces, concatenation follows the first path.
        have hparam :
            ContDiffOn ℝ 1 (fun t : ℝ ↦ 2 * t)
              (Set.Icc (subdiv i.castSucc / 2) (subdiv i.succ / 2)) := by
          simpa using
            contDiffOn_affine_reparam 2 0
              (Set.Icc (subdiv i.castSucc / 2) (subdiv i.succ / 2))
        have hmaps :
            Set.MapsTo (fun t : ℝ ↦ 2 * t)
              (Set.Icc (subdiv i.castSucc / 2) (subdiv i.succ / 2))
              (Set.Icc (subdiv i.castSucc) (subdiv i.succ)) := by
          intro t ht
          rcases ht with ⟨htlo, hthi⟩
          constructor <;> linarith
        have hpiece :
            ContDiffOn ℝ 1 (fun t ↦ γ₁.extend (2 * t))
              (Set.Icc (subdiv i.castSucc / 2) (subdiv i.succ / 2)) :=
          (hpieces i).comp hparam hmaps
        have heq :
            Set.EqOn (γ₁.trans γ₂).extend (fun t ↦ γ₁.extend (2 * t))
              (Set.Icc (subdiv i.castSucc / 2) (subdiv i.succ / 2)) := by
          intro t ht
          have hupper : subdiv i.succ ≤ 1 := by
            calc
              subdiv i.succ ≤ subdiv (Fin.last (n + 1)) := hsubdiv.monotone i.succ.le_last
              _ = 1 := h1
          exact Path.extend_trans_of_le_half γ₁ γ₂ (by linarith [ht.2, hupper])
        simpa only [subdiv', Fin.snoc_castSucc, Fin.succ_castSucc] using hpiece.congr heq
    | last =>
        -- On the last piece `[1/2, 1]`, concatenation follows the appended differentiable path.
        have hparam :
            ContDiffOn ℝ 1 (fun t : ℝ ↦ 2 * t - 1) (Set.Icc (1 / 2 : ℝ) 1) := by
          simpa [sub_eq_add_neg] using contDiffOn_affine_reparam 2 (-1) (Set.Icc (1 / 2 : ℝ) 1)
        have hmaps :
            Set.MapsTo (fun t : ℝ ↦ 2 * t - 1) (Set.Icc (1 / 2 : ℝ) 1) I := by
          intro t ht
          rcases ht with ⟨htlo, hthi⟩
          constructor <;> linarith
        have hpiece :
            ContDiffOn ℝ 1 (fun t ↦ γ₂.extend (2 * t - 1)) (Set.Icc (1 / 2 : ℝ) 1) :=
          hγ₂.contDiffOn.comp hparam hmaps
        have heq :
            Set.EqOn (γ₁.trans γ₂).extend (fun t ↦ γ₂.extend (2 * t - 1))
              (Set.Icc (1 / 2 : ℝ) 1) := by
          intro t ht
          exact Path.extend_trans_of_half_le γ₁ γ₂ ht.1
        simpa only [subdiv', Fin.snoc_castSucc, Fin.snoc_last, Fin.succ_last, h1] using
          hpiece.congr heq

end Differentiability

end Path

/-- Lemma II.1-extra-3: any two points of a connected open subset of a real normed space can be
joined by a piecewise differentiable path contained in that subset. -/
-- Route correction: follow the textbook clopen-reachability argument using local straight
-- segments, rather than the provisional compact-cover sketch.
lemma exists_piecewiseDifferentiable_path_in_of_isOpen_isConnected
    {D : Set E} (hD_open : IsOpen D) (hD_connected : IsConnected D) {a b : E}
    (ha : a ∈ D) (hb : b ∈ D) :
    ∃ γ : Path a b, γ.IsPiecewiseDifferentiable ∧ ∀ t, γ t ∈ D := by
  let ReachD : Set D := {x | ∃ γ : Path a x.1, γ.IsPiecewiseDifferentiable ∧ Set.range γ ⊆ D}
  have hReach_open : IsOpen ReachD := by
    rw [Metric.isOpen_iff]
    intro x hx
    rcases hx with ⟨γ, hγ_piecewise, hγD⟩
    rcases Metric.isOpen_iff.1 hD_open x.1 x.2 with ⟨r, hr_pos, hrD⟩
    refine ⟨r, hr_pos, ?_⟩
    intro y hy
    have hx_ball : x.1 ∈ Metric.ball x.1 r := Metric.mem_ball_self hr_pos
    have hseg_ball : Set.range (Path.segment x.1 y.1) ⊆ Metric.ball x.1 r := by
      rw [Path.range_segment]
      exact (convex_ball x.1 r).segment_subset hx_ball hy
    have hsegD : Set.range (Path.segment x.1 y.1) ⊆ D := Set.Subset.trans hseg_ball hrD
    have htransD : Set.range (γ.trans (Path.segment x.1 y.1)) ⊆ D := by
      rw [Path.trans_range]
      exact Set.union_subset hγD hsegD
    -- Extend the reachable witness by a local straight segment inside the ambient ball.
    refine ⟨γ.trans (Path.segment x.1 y.1), ?_, htransD⟩
    exact hγ_piecewise.trans_of_isDifferentiable (Path.segment_isDifferentiable x.1 y.1)
  have hReach_closed : IsClosed ReachD := by
    apply isOpen_compl_iff.mp
    rw [Metric.isOpen_iff]
    intro x hx
    rcases Metric.isOpen_iff.1 hD_open x.1 x.2 with ⟨r, hr_pos, hrD⟩
    refine ⟨r, hr_pos, ?_⟩
    intro y hy
    show y ∉ ReachD
    intro hyReach
    rcases hyReach with ⟨γ, hγ_piecewise, hγD⟩
    have hy_ball : y.1 ∈ Metric.ball x.1 r := hy
    have hx_ball : x.1 ∈ Metric.ball x.1 r := Metric.mem_ball_self hr_pos
    have hseg_ball : Set.range (Path.segment y.1 x.1) ⊆ Metric.ball x.1 r := by
      rw [Path.range_segment]
      exact (convex_ball x.1 r).segment_subset hy_ball hx_ball
    have hsegD : Set.range (Path.segment y.1 x.1) ⊆ D := Set.Subset.trans hseg_ball hrD
    have htransD : Set.range (γ.trans (Path.segment y.1 x.1)) ⊆ D := by
      rw [Path.trans_range]
      exact Set.union_subset hγD hsegD
    -- Any reachable point in this ball would connect back to `x`, contradicting `x ∉ ReachD`.
    apply hx
    refine ⟨γ.trans (Path.segment y.1 x.1), ?_, htransD⟩
    exact hγ_piecewise.trans_of_isDifferentiable (Path.segment_isDifferentiable y.1 x.1)
  have hReach_nonempty : ReachD.Nonempty := by
    refine ⟨⟨a, ha⟩, ?_⟩
    refine ⟨Path.refl a, Path.isPiecewiseDifferentiable_refl a, ?_⟩
    intro z hz
    rcases hz with ⟨t, rfl⟩
    simpa using ha
  letI : ConnectedSpace D := isConnected_iff_connectedSpace.mp hD_connected
  have hReach_univ : ReachD = Set.univ := IsClopen.eq_univ ⟨hReach_closed, hReach_open⟩ hReach_nonempty
  have hbReach : (⟨b, hb⟩ : D) ∈ ReachD := by
    simp [hReach_univ]
  rcases hbReach with ⟨γ, hγ_piecewise, hγD⟩
  refine ⟨γ, hγ_piecewise, ?_⟩
  intro t
  exact hγD (Set.mem_range_self t)
