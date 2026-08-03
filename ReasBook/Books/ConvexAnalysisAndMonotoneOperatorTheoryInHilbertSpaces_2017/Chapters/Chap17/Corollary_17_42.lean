import BauschkeLean.Chap01.Text_1_0_14
import BauschkeLean.Chap02.Fact_2_62
import BauschkeLean.Chap02.Lemma_2_46
import BauschkeLean.Chap08.Corollary_8_39
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap16.Proposition_16_17
import BauschkeLean.Chap17.Proposition_17_6
import BauschkeLean.Chap17.Proposition_17_39.Index
import BauschkeLean.Chap17.Proposition_17_41

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open InnerProductSpace
open SetValuedOperator
open scoped Gradient InnerProductSpace Topology

universe u

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Corollary 17 42: a Gâteaux derivative within a set already determines the whole-space
Gâteaux derivative, because only the radial-segment witness changes. -/
lemma hasGateauxDerivativeAt_of_hasGateauxDerivativeWithinAt
    {T : H → ℝ} {A : H →L[ℝ] ℝ} {C : Set H} {x : H}
    (hA : HasGateauxDerivativeWithinAt T A C x) :
    HasGateauxDerivativeAt T A x := by
  -- The line-derivative data is unchanged; `Set.univ` supplies the missing radial segments.
  refine ⟨hasRadialSegmentsAt_univ x, hA.2⟩

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 17 42: every point of the open set `D` lies in the interior of the
effective domain once `D ⊆ effectiveDomain f`. -/
lemma mem_interior_effectiveDomain_of_mem_D
    {f : H → Set.Ioi (⊥ : EReal)} {D : Set H} (hD_open : IsOpen D)
    (hD_dom : D ⊆ effectiveDomain f) {x : H} (hx : x ∈ D) :
    x ∈ interior (effectiveDomain f) := by
  -- Openness gives a neighborhood inside `D`, and the domain inclusion pushes it into
  -- `effectiveDomain f`.
  rw [mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset (hD_open.mem_nhds hx) hD_dom

omit [CompleteSpace H] in
/-- Helper for Corollary 17 42: a subgradient at `x` gives the lower affine support inequality in
ordinary real form at every finite point `y`. -/
lemma inner_le_sub_of_mem_subdifferential_real
    {f : H → Set.Ioi (⊥ : EReal)} {x y u : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) (hu : u ∈ (∂ f) x) :
    ⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal := by
  have hxy :
      (⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal) :=
    (mem_subdifferential_iff f x u).1 hu y
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hreal : ⟪y - x, u⟫_ℝ + (f x : EReal).toReal ≤ (f y : EReal).toReal := by
    have hcast :
        (((⟪y - x, u⟫_ℝ + (f x : EReal).toReal : ℝ) : EReal)) ≤
          (((f y : EReal).toReal : ℝ) : EReal) := by
      calc
        (((⟪y - x, u⟫_ℝ + (f x : EReal).toReal : ℝ) : EReal)) =
            (⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) := by
              rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_add]
              simp
        _ ≤ (f y : EReal) := hxy
        _ = (((f y : EReal).toReal : ℝ) : EReal) := by
              exact (EReal.coe_toReal hy_top hy_bot).symm
    exact_mod_cast hcast
  linarith

/-- Helper for Corollary 17 42: every subgradient at an interior effective-domain point is
dominated by the Gâteaux gradient on each direction. -/
lemma subgradient_inner_le_gateauxGradient_of_mem_interior_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x u gradf y : H}
    (hx : x ∈ interior (effectiveDomain f)) (hu : u ∈ (∂ f) x)
    (hgrad :
      HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDualMap ℝ H gradf) x) :
    ⟪y, u⟫_ℝ ≤ ⟪y, gradf⟫_ℝ := by
  have hxeff : x ∈ effectiveDomain f := interior_subset hx
  rcases small_segment_subset_subdifferentialDom hf hx y with ⟨α0, hα0pos, hα0mem⟩
  have hquot_tendsto :
      Tendsto
        (fun α : ℝ ↦
          (((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α : ℝ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ⟪y, gradf⟫_ℝ) := by
    -- The Gâteaux derivative identifies the limiting one-sided secant slope in direction `y`.
    simpa [div_eq_mul_inv, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, real_inner_comm] using
      hgrad.tendsto_directionalDifferenceQuotient y
  have hquot_ge :
      ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ⟪y, u⟫_ℝ ≤
          (((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) := by
    have hlt :
        ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), α < α0 :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hα0pos)
    have hIcc :
        ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), α ∈ Set.Icc (0 : ℝ) α0 := by
      filter_upwards [self_mem_nhdsWithin, hlt] with α hαpos hαlt
      exact ⟨le_of_lt hαpos, hαlt.le⟩
    filter_upwards [self_mem_nhdsWithin, hIcc] with α hαpos hα
    have hαdom : x + α • y ∈ SetValuedOperator.dom (∂ f) := hα0mem α hα
    have hαeff :
        x + α • y ∈ effectiveDomain f :=
      subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hf hαdom
    have hsub :
        inner ℝ ((x + α • y) - x) u ≤
          (f (x + α • y) : EReal).toReal - (f x : EReal).toReal :=
      inner_le_sub_of_mem_subdifferential_real hxeff hαeff hu
    have hscaled :
        α * inner ℝ y u ≤
          (f (x + α • y) : EReal).toReal - (f x : EReal).toReal := by
      -- Expanding the step `x + α • y` isolates the scalar factor `α`.
      simpa [sub_eq_add_neg, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, inner_add_left,
        inner_smul_left, inner_sub_left] using hsub
    exact (le_div_iff₀ hαpos).2 (by simpa [mul_comm] using hscaled)
  -- Passing the subgradient inequality to the limit compares the subgradient with `gradf`.
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hquot_tendsto hquot_ge

/-- Helper for Corollary 17 42: an interior Gâteaux gradient makes the subdifferential fiber a
singleton. -/
lemma subdifferential_eq_singleton_of_hasGateauxDerivativeAt_of_mem_interior_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x gradf : H}
    (hx : x ∈ interior (effectiveDomain f))
    (hgrad :
      HasGateauxDerivativeAt
        (fun z ↦ (f z : EReal).toReal) (InnerProductSpace.toDualMap ℝ H gradf) x) :
    (∂ f) x = ({gradf} : Set H) := by
  have hgrad_mem : gradf ∈ (∂ f) x := by
    -- Proposition 17.6 turns the Gâteaux gradient into an actual subgradient.
    exact gateauxGradient_mem_subdifferential f hf.2 (interior_subset hx) gradf hgrad
  apply Set.Subset.antisymm
  · intro u hu
    have hu_eq : u = gradf := by
      apply ext_inner_left ℝ
      intro y
      have hy_le :
          ⟪y, u⟫_ℝ ≤ ⟪y, gradf⟫_ℝ := by
        exact
          subgradient_inner_le_gateauxGradient_of_mem_interior_effectiveDomain
            hf hx hu hgrad
      have hneg_le :
          ⟪-y, u⟫_ℝ ≤ ⟪-y, gradf⟫_ℝ := by
        exact
          subgradient_inner_le_gateauxGradient_of_mem_interior_effectiveDomain
            hf hx hu hgrad
      have hy_ge :
          ⟪y, gradf⟫_ℝ ≤ ⟪y, u⟫_ℝ := by
        simpa using hneg_le
      exact le_antisymm hy_le hy_ge
    simp [hu_eq]
  · intro u hu
    rw [Set.mem_singleton_iff] at hu
    simpa [hu] using hgrad_mem

/-- Helper for Corollary 17 42: strong convergence of base points and weak convergence of
subgradients preserve subdifferential membership once the subgradients stay bounded. -/
lemma mem_subdifferential_of_tendsto_of_tendsto_toWeakSpace
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {xSeq uSeq : ℕ → H} {x u : H}
    (hx : Tendsto xSeq atTop (𝓝 x))
    (hu : Tendsto (fun n ↦ toWeakSpace ℝ H (uSeq n)) atTop (𝓝 (toWeakSpace ℝ H u)))
    (hub : Bornology.IsBounded (Set.range uSeq))
    (hsub : ∀ n, uSeq n ∈ (∂ f) (xSeq n)) :
    u ∈ (∂ f) x := by
  rw [mem_subdifferential_iff]
  intro y
  have hycoord0 :
      Tendsto (fun n ↦ inner ℝ (uSeq n) (y - x)) atTop (𝓝 (inner ℝ u (y - x))) := by
    simpa using
      ((weakSpace_continuous_inner_right (H := H) (y - x)).tendsto
        (toWeakSpace ℝ H u)).comp hu
  have hycoord :
      Tendsto (fun n ↦ inner ℝ (y - x) (uSeq n)) atTop (𝓝 (inner ℝ (y - x) u)) := by
    simpa [real_inner_comm] using hycoord0
  obtain ⟨R, hR⟩ := hub.subset_closedBall (0 : H)
  have hu_bound : ∀ n, ‖uSeq n‖ ≤ R := by
    intro n
    have hun : uSeq n ∈ Metric.closedBall (0 : H) R := hR (Set.mem_range_self n)
    simpa [Metric.mem_closedBall, dist_eq_norm] using hun
  have hx_zero : Tendsto (fun n ↦ x - xSeq n) atTop (𝓝 (0 : H)) := by
    have hx_zero' : Tendsto (fun n ↦ x - xSeq n) atTop (𝓝 (x - x)) :=
      tendsto_const_nhds.sub hx
    simpa using hx_zero'
  have hbound_zero : Tendsto (fun n ↦ ‖x - xSeq n‖ * R) atTop (𝓝 0) := by
    have hnorm_zero : Tendsto (fun n ↦ ‖x - xSeq n‖) atTop (𝓝 0) := by
      simpa using (continuous_norm.tendsto (0 : H)).comp hx_zero
    simpa [zero_mul] using hnorm_zero.mul_const R
  have hcross :
      Tendsto (fun n ↦ inner ℝ (x - xSeq n) (uSeq n)) atTop (𝓝 0) := by
    have hneg_zero : Tendsto (fun n ↦ -(‖x - xSeq n‖ * R)) atTop (𝓝 0) := by
      simpa using hbound_zero.neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hneg_zero hbound_zero ?_ ?_
    · intro n
      have habs : |⟪x - xSeq n, uSeq n⟫_ℝ| ≤ ‖x - xSeq n‖ * R := by
        calc
          |⟪x - xSeq n, uSeq n⟫_ℝ| ≤ ‖x - xSeq n‖ * ‖uSeq n‖ :=
            abs_real_inner_le_norm _ _
          _ ≤ ‖x - xSeq n‖ * R := by
              gcongr
              exact hu_bound n
      calc
        -(‖x - xSeq n‖ * R) ≤ -|⟪x - xSeq n, uSeq n⟫_ℝ| := by
          linarith
        _ ≤ ⟪x - xSeq n, uSeq n⟫_ℝ := by
          exact neg_abs_le _
    · intro n
      calc
        ⟪x - xSeq n, uSeq n⟫_ℝ ≤ |⟪x - xSeq n, uSeq n⟫_ℝ| := le_abs_self _
        _ ≤ ‖x - xSeq n‖ * R := by
            calc
              |⟪x - xSeq n, uSeq n⟫_ℝ| ≤ ‖x - xSeq n‖ * ‖uSeq n‖ :=
                abs_real_inner_le_norm _ _
              _ ≤ ‖x - xSeq n‖ * R := by
                  gcongr
                  exact hu_bound n
  have hinner :
      Tendsto (fun n ↦ inner ℝ (y - xSeq n) (uSeq n)) atTop (𝓝 (inner ℝ (y - x) u)) := by
    have hsplit :
        (fun n ↦ inner ℝ (y - xSeq n) (uSeq n)) =
          fun n ↦ inner ℝ (y - x) (uSeq n) + inner ℝ (x - xSeq n) (uSeq n) := by
      funext n
      have hdecomp : y - xSeq n = (y - x) + (x - xSeq n) := by
        abel
      rw [hdecomp, inner_add_left]
    rw [hsplit]
    simpa using hycoord.add hcross
  have hinner_ereal :
      Tendsto
        (fun n ↦ ((inner ℝ (y - xSeq n) (uSeq n) : ℝ) : EReal))
        atTop
        (𝓝 (((inner ℝ (y - x) u : ℝ) : EReal))) := by
    exact continuous_coe_real_ereal.tendsto _ |>.comp hinner
  have hvalue :
      (f x : EReal) ≤ Filter.liminf (fun n ↦ (f (xSeq n) : EReal)) atTop := by
    calc
      (f x : EReal) ≤ Filter.liminf (fun z ↦ (f z : EReal)) (𝓝 x) :=
        LowerSemicontinuousAt.le_liminf (hf.1.lowerSemicontinuousAt x)
      _ ≤ Filter.liminf (fun n ↦ (f (xSeq n) : EReal)) atTop :=
        Filter.liminf_le_liminf_of_le hx
  have hsum :
      Filter.liminf
          (fun n ↦
            (((inner ℝ (y - xSeq n) (uSeq n) : ℝ) : EReal) + (f (xSeq n) : EReal)))
          atTop ≤
        (f y : EReal) := by
    have hsup :
        Filter.limsup
            (fun n ↦
              (((inner ℝ (y - xSeq n) (uSeq n) : ℝ) : EReal) + (f (xSeq n) : EReal)))
            atTop ≤
          (f y : EReal) :=
      Filter.limsup_le_of_le
        (by isBoundedDefault)
        (Eventually.of_forall fun n ↦
          (mem_subdifferential_iff (f := f) (x := xSeq n) (u := uSeq n)).1 (hsub n) y)
    exact
      le_trans
        (Filter.liminf_le_limsup
          (u := fun n ↦
            (((inner ℝ (y - xSeq n) (uSeq n) : ℝ) : EReal) + (f (xSeq n) : EReal))))
        hsup
  calc
    ((inner ℝ (y - x) u : ℝ) : EReal) + (f x : EReal)
        =
      Filter.liminf
          (fun n ↦ ((inner ℝ (y - xSeq n) (uSeq n) : ℝ) : EReal))
          atTop +
        (f x : EReal) := by
          rw [hinner_ereal.liminf_eq]
    _ ≤
      Filter.liminf
          (fun n ↦ ((inner ℝ (y - xSeq n) (uSeq n) : ℝ) : EReal))
          atTop +
        Filter.liminf (fun n ↦ (f (xSeq n) : EReal)) atTop := by
          gcongr
    _ ≤
      Filter.liminf
          (fun n ↦
            (((inner ℝ (y - xSeq n) (uSeq n) : ℝ) : EReal) + (f (xSeq n) : EReal)))
          atTop := by
            simpa using
              (EReal.le_liminf_add :
                Filter.liminf
                    (fun n ↦ ((inner ℝ (y - xSeq n) (uSeq n) : ℝ) : EReal))
                    atTop +
                  Filter.liminf (fun n ↦ (f (xSeq n) : EReal)) atTop ≤
                Filter.liminf
                    (fun n ↦
                      (((inner ℝ (y - xSeq n) (uSeq n) : ℝ) : EReal) +
                        (f (xSeq n) : EReal)))
                    atTop)
    _ ≤ (f y : EReal) := hsum

/-- Helper for Corollary 17 42: the prescribed gradient belongs to the subdifferential at every
point of `D`. -/
lemma gradientField_mem_subdifferential_on_D
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {D : Set H}
    (hD_dom : D ⊆ effectiveDomain f) (gradf : H → H)
    (hgrad :
      HasGateauxDerivativeOn (fun y ↦ (f y : EReal).toReal) (fun y ↦ toDual ℝ H (gradf y)) D)
    {y : H} (hy : y ∈ D) :
    gradf y ∈ (∂ f) y := by
  -- Use convex secant inequalities on the segment from `y` to `z` and pass to the Gâteaux limit.
  rw [mem_subdifferential_iff]
  intro z
  have hy_dom : y ∈ effectiveDomain f := hD_dom hy
  have hconv_real : _root_.ConvexOn ℝ (effectiveDomain f) (fun x ↦ (f x : EReal).toReal) :=
    hf.2.toReal_convexOn_effectiveDomain
  by_cases hz : z ∈ effectiveDomain f
  · have hquot_tendsto :
        Filter.Tendsto
          (fun α : ℝ ↦
            (((f (y + α • (z - y)) : EReal).toReal - (f y : EReal).toReal) / α : ℝ))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ⟪z - y, gradf y⟫_ℝ) := by
      simpa [one_div, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, real_inner_comm,
        toDual_apply_eq_toDualMap_apply, toDualMap_apply_apply] using
        (hgrad y hy).tendsto_directionalDifferenceQuotient (z - y)
    have hquot_le :
        ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          (((f (y + α • (z - y)) : EReal).toReal - (f y : EReal).toReal) / α : ℝ) ≤
            (f z : EReal).toReal - (f y : EReal).toReal := by
      have hα_mem :
          ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), α ∈ Set.Ioo (0 : ℝ) 1 := by
        filter_upwards
          [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)] with
          α hα0 hα1
        exact ⟨hα0, hα1⟩
      filter_upwards [hα_mem] with α hα
      have hineq :
          (f (y + α • (z - y)) : EReal).toReal ≤
            α * (f z : EReal).toReal + (1 - α) * (f y : EReal).toReal := by
        simpa [sub_eq_add_neg, smul_add, add_smul, add_assoc, add_left_comm, add_comm, mul_comm,
          mul_left_comm, mul_assoc] using
          hconv_real.2 hz hy_dom hα.1.le (sub_nonneg.mpr hα.2.le) (by linarith)
      refine (div_le_iff₀ hα.1).2 ?_
      linarith
    have hinner_le :
        ⟪z - y, gradf y⟫_ℝ ≤ (f z : EReal).toReal - (f y : EReal).toReal := by
      exact le_of_tendsto_of_tendsto hquot_tendsto tendsto_const_nhds hquot_le
    have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy_dom)
    have hy_bot : (f y : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
    have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz)
    have hz_bot : (f z : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
    have hinner_le_ereal :
        (⟪z - y, gradf y⟫_ℝ : EReal) ≤ (f z : EReal) - (f y : EReal) := by
      rw [← EReal.coe_toReal hz_top hz_bot, ← EReal.coe_toReal hy_top hy_bot, ← EReal.coe_sub]
      exact_mod_cast hinner_le
    calc
      (⟪z - y, gradf y⟫_ℝ : EReal) + (f y : EReal) ≤
          ((f z : EReal) - (f y : EReal)) + (f y : EReal) := by
            simpa [add_assoc, add_left_comm, add_comm] using
              add_le_add_right hinner_le_ereal (f y : EReal)
      _ = (f z : EReal) := by
            have hsum :
                (((f z : EReal).toReal - (f y : EReal).toReal) + (f y : EReal).toReal : ℝ) =
                  (f z : EReal).toReal := by
              linarith
            rw [← EReal.coe_toReal hz_top hz_bot, ← EReal.coe_toReal hy_top hy_bot,
              ← EReal.coe_sub, ← EReal.coe_add]
            exact_mod_cast hsum
  · have hz_top : (f z : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hz))
    change (⟪z - y, gradf y⟫_ℝ : EReal) + (f y : EReal) ≤ (f z : EReal)
    rw [hz_top]
    exact le_top

/-- Helper for Corollary 17 42: every point of `D` belongs to the domain of the subdifferential. -/
lemma mem_subdifferentialDomain_of_mem_D
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {D : Set H}
    (hD_dom : D ⊆ effectiveDomain f) (gradf : H → H)
    (hgrad :
      HasGateauxDerivativeOn (fun y ↦ (f y : EReal).toReal) (fun y ↦ toDual ℝ H (gradf y)) D)
    {y : H} (hy : y ∈ D) :
    y ∈ SetValuedOperator.dom (∂ f) := by
  -- Nonemptiness follows from the explicit subgradient `gradf y`.
  rw [SetValuedOperator.mem_dom_iff]
  exact ⟨gradf y, gradientField_mem_subdifferential_on_D hf hD_dom gradf hgrad hy⟩

/-- Helper for Corollary 17 42: there is a global subdifferential selection that agrees with the
prescribed gradient field on `D`. -/
lemma exists_selection_eq_gradientField_on_D
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {D : Set H}
    (hD_dom : D ⊆ effectiveDomain f) (gradf : H → H)
    (hgrad :
      HasGateauxDerivativeOn (fun y ↦ (f y : EReal).toReal) (fun y ↦ toDual ℝ H (gradf y)) D)
    :
    ∃ G : Selection (∂ f),
      ∀ y : D,
        (G ⟨(y : H), mem_subdifferentialDomain_of_mem_D hf hD_dom gradf hgrad y.2⟩ : H) =
          gradf y := by
  classical
  have hnonempty : ∀ z : (∂ f).dom, Nonempty ((∂ f) z) := by
    intro z
    have hzdom := z.2
    rw [SetValuedOperator.mem_dom_iff] at hzdom
    rcases hzdom with ⟨u, hu⟩
    exact ⟨⟨u, hu⟩⟩
  let G : Selection (∂ f) := fun z ↦
    if hzD : (z : H) ∈ D then
      ⟨gradf z, gradientField_mem_subdifferential_on_D hf hD_dom gradf hgrad hzD⟩
    else
      Classical.choice (hnonempty z)
  refine ⟨G, ?_⟩
  intro y
  simp [G, y.2]

/-
Source/core/bridge triage:
- `source-facing`: Corollary 17.42 is the open-set continuity consequence for a convex gradient
  field.
- `core/canonical`: the owner abstractions are `HasGateauxDerivativeOn`,
  `SelectionContinuousAt`, and ordinary continuity into `WeakSpace ℝ H`.
- `bridge/view`: Propositions 17.39 and 17.41 convert differentiability into continuity of
  subdifferential selections; the given gradient field is the source-facing singleton selection on
  `D`.
-/

-- Proof sketch: for each `y ∈ D`, openness of `D` upgrades the assumed Gâteaux derivative field on
-- `D` to a local gradient around `y`. Local boundedness of nearby subgradients and strong-weak
-- closedness of the subdifferential graph force every weak cluster point of `gradf` along a
-- convergent sequence in `D` to equal the unique subgradient at the limit point.
/-- Corollary 17 42 (1): if `f ∈ Γ₀(H)` admits a Gâteaux gradient field `gradf` on an open set
`D ⊆ effectiveDomain f`, then `gradf` is strong-to-weak continuous on `D`. -/
theorem gradientField_strongToWeakContinuousOn_of_mem_gammaZero_of_hasGateauxDerivativeOn
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {D : Set H} (hD_open : IsOpen D)
    (hD_dom : D ⊆ effectiveDomain f) (gradf : H → H)
    (hgrad :
      HasGateauxDerivativeOn (fun y ↦ (f y : EReal).toReal) (fun y ↦ toDual ℝ H (gradf y)) D) :
    Continuous (fun y : D ↦ toWeakSpace ℝ H (gradf y)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hx_int : (x : H) ∈ interior (effectiveDomain f) :=
    mem_interior_effectiveDomain_of_mem_D hD_open hD_dom x.2
  have hxcont :
      ContinuousAtOnEffectiveDomain f (x : H) :=
    continuousAtOnEffectiveDomain_of_mem_interior_effectiveDomain_of_mem_gammaZero hf hx_int
  have hxcont_in :
      ContinuousAtInEffectiveDomain f (x : H) :=
    continuousPoint_of_mem_interior_effectiveDomain_of_mem_gammaZero hf hx_int
  have hgradAt :
      HasGateauxDerivativeAt (fun y ↦ (f y : EReal).toReal)
        (toDualMap ℝ H (gradf x)) (x : H) := by
    simpa [toDual_apply_eq_toDualMap_apply] using
      hasGateauxDerivativeAt_of_hasGateauxDerivativeWithinAt (hgrad x x.2)
  have hsubx :
      (∂ f) (x : H) = ({gradf x} : Set H) := by
    exact
      subdifferential_eq_singleton_of_hasGateauxDerivativeAt_of_mem_interior_effectiveDomain
        hf hx_int hgradAt
  apply Filter.tendsto_of_seq_tendsto
  intro z hz
  have hz_base : Tendsto (fun n ↦ (z n : H)) atTop (𝓝 (x : H)) := by
    simpa using (continuous_subtype_val.tendsto x).comp hz
  obtain ⟨ρ, hρpos, hbounded⟩ :=
    subdifferential_ball_union_bounded_of_continuousAtOnEffectiveDomain f hf.2 hxcont_in
  have htail : ∀ᶠ n in atTop, (z n : H) ∈ Metric.ball (x : H) ρ := by
    exact hz_base.eventually (Metric.ball_mem_nhds _ hρpos)
  rcases eventually_atTop.mp htail with ⟨N, hN⟩
  let s0 : Set H := (fun n ↦ gradf (z n)) '' {n : ℕ | n < N}
  have hs0_finite : s0.Finite := by
    classical
    simpa [s0] using (Set.finite_lt_nat N).image (fun n ↦ gradf (z n))
  have hrange_subset :
      Set.range (fun n ↦ gradf (z n)) ⊆ s0 ∪ ⋃ y ∈ Metric.ball (x : H) ρ, (∂ f) y := by
    rintro v ⟨n, rfl⟩
    by_cases hn : n < N
    · exact Or.inl ⟨n, hn, rfl⟩
    · exact Or.inr <| Set.mem_iUnion.2 ⟨(z n : H),
        Set.mem_iUnion.2 ⟨hN n (Nat.le_of_not_lt hn),
          gradientField_mem_subdifferential_on_D hf hD_dom gradf hgrad (z n).2⟩⟩
  have hboundedRange :
      Bornology.IsBounded (Set.range fun n ↦ gradf (z n)) := by
    exact (hs0_finite.isBounded.union hbounded).subset hrange_subset
  have hcluster_eq :
      ∀ w : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (gradf (z n)))
          (toWeakSpace ℝ H w) →
        w = gradf x := by
    intro w hw
    rcases hw.exists_subseq_tendsto with ⟨φ, hφ, hφw⟩
    have hzφ :
        Tendsto (fun n ↦ (z (φ n) : H)) atTop (𝓝 (x : H)) :=
      hz_base.comp hφ.tendsto_atTop
    have hboundedSubseq :
        Bornology.IsBounded (Set.range fun n ↦ gradf (z (φ n))) := by
      refine hboundedRange.subset ?_
      rintro v ⟨n, rfl⟩
      exact ⟨φ n, rfl⟩
    have hw_sub :
        w ∈ (∂ f) (x : H) := by
      refine
        mem_subdifferential_of_tendsto_of_tendsto_toWeakSpace
          hf hzφ hφw hboundedSubseq ?_
      intro n
      exact gradientField_mem_subdifferential_on_D hf hD_dom gradf hgrad (z (φ n)).2
    have hw_single : w ∈ ({gradf x} : Set H) := by
      rw [← hsubx]
      exact hw_sub
    simpa using hw_single
  rcases
      (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint
        (fun n ↦ gradf (z n))).2
        ⟨hboundedRange, fun y w hy hw ↦ by
          calc
            y = gradf x := hcluster_eq y hy
            _ = w := (hcluster_eq w hw).symm⟩ with
    ⟨w, hw⟩
  have hw_cluster :
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (gradf (z n)))
        (toWeakSpace ℝ H w) := by
    exact ⟨id, strictMono_id, by simpa using hw⟩
  have hw_eq : w = gradf x := hcluster_eq w hw_cluster
  simpa [hw_eq] using hw

-- Proof sketch: apply Proposition 17.41 at `x` to the subgradient selection induced by `gradf`.
-- The assumed Gâteaux derivative field identifies that selection with the gradient of `f` on `D`,
-- so Fréchet differentiability at `x` is equivalent to continuity of `gradf` within `D` at `x`.
/-- Corollary 17 42 (2): for `x ∈ D`, the finite representative of `f` is Fréchet differentiable
at `x` if and only if the Gâteaux gradient field `gradf` is continuous within `D` at `x`. -/
theorem
    frechetDifferentiableAt_iff_gradientField_continuousWithinAt_of_mem_gammaZero_of_hasGateauxDerivativeOn
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {D : Set H} (hD_open : IsOpen D)
    (hD_dom : D ⊆ effectiveDomain f) (gradf : H → H)
    (hgrad :
      HasGateauxDerivativeOn (fun y ↦ (f y : EReal).toReal) (fun y ↦ toDual ℝ H (gradf y)) D)
    {x : H} (hx : x ∈ D) :
    DifferentiableAt ℝ (fun y ↦ (f y : EReal).toReal) x ↔ ContinuousWithinAt gradf D x := by
  have hx_int : x ∈ interior (effectiveDomain f) :=
    mem_interior_effectiveDomain_of_mem_D hD_open hD_dom hx
  let g : H → ℝ := fun y ↦ (f y : EReal).toReal
  constructor
  · intro hdiff
    let u : H := ∇ g x
    have hgrad_u : HasGradientAt g u x := by
      simpa [g, u] using hdiff.hasGradientAt
    have hu_single : (∂ f) x = ({u} : Set H) := by
      exact
        subdifferential_eq_singleton_of_hasGateauxDerivativeAt_of_mem_interior_effectiveDomain
          hf hx_int <| by
            simpa [g, u] using hgrad_u.hasFDerivAt.hasGateauxDerivativeAt
    have hgradx_sub : gradf x ∈ (∂ f) x :=
      gradientField_mem_subdifferential_on_D hf hD_dom gradf hgrad hx
    have hu_eq : gradf x = u := by
      have : gradf x ∈ ({u} : Set H) := by
        simpa [hu_single] using hgradx_sub
      simpa using this
    obtain ⟨ρ, hρpos, M, hMpos, hMbound⟩ :=
      subgradient_norm_bound_on_small_ball_of_mem_interior_effectiveDomain hf hx_int
    rcases Metric.mem_nhds_iff.mp (hD_open.mem_nhds hx) with ⟨σ, hσpos, hσD⟩
    rw [continuousWithinAt_iff_continuousAt_restrict gradf hx]
    rw [Metric.continuousAt_iff]
    intro ε hε
    let B : ℝ := max 1 (M + ‖u‖)
    have hBpos : 0 < B := by
      dsimp [B]
      exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    let κ : ℝ := ε ^ 2 / (8 * B)
    have hκpos : 0 < κ := by
      dsimp [κ]
      positivity
    rcases frechet_remainder_bound_on_ball (f := f) hgrad_u κ hκpos with ⟨η, hηpos, hηbound⟩
    let δ : ℝ := min (ρ / 2) (min (η / 4) (σ / 4))
    have hδpos : 0 < δ := by
      dsimp [δ]
      positivity
    have hδ_le_rho2 : δ ≤ ρ / 2 := by
      dsimp [δ]
      exact min_le_left _ _
    have hδ_le_eta4 : δ ≤ η / 4 := by
      dsimp [δ]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hδ_le_sigma4 : δ ≤ σ / 4 := by
      dsimp [δ]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hδ_lt_rho : δ < ρ := by
      linarith
    have htwoδ_lt_eta : 2 * δ < η := by
      linarith
    have htwoδ_lt_sigma : 2 * δ < σ := by
      linarith
    refine ⟨δ, hδpos, ?_⟩
    intro y hy
    have hy_ball : (y : H) ∈ Metric.ball x δ := by
      simpa [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] using hy
    have hy_rho : (y : H) ∈ Metric.ball x ρ := by
      rw [Metric.mem_ball] at hy_ball ⊢
      exact lt_of_lt_of_le hy_ball hδ_lt_rho.le
    have hv_sub : gradf y ∈ (∂ f) (y : H) :=
      gradientField_mem_subdifferential_on_D hf hD_dom gradf hgrad y.2
    have hv_norm : ‖gradf y‖ ≤ M := hMbound _ hy_rho _ hv_sub
    have hvu_norm : ‖gradf y - u‖ ≤ B := by
      calc
        ‖gradf y - u‖ ≤ ‖gradf y‖ + ‖u‖ := norm_sub_le _ _
        _ ≤ M + ‖u‖ := by
              gcongr
        _ ≤ B := by
              dsimp [B]
              exact le_max_right _ _
    let zPoint : H := (y : H) + (δ / B) • (gradf y - u)
    have hz_dist :
        dist zPoint x ≤ 2 * δ := by
      simpa [zPoint] using
        step_point_dist_le_two_mul_delta_of_norm_sub_le hy_ball hBpos hvu_norm
    have hz_eta : zPoint ∈ Metric.ball x η := by
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt hz_dist htwoδ_lt_eta
    have hz_sigma : zPoint ∈ Metric.ball x σ := by
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt hz_dist htwoδ_lt_sigma
    have hz_dom : zPoint ∈ effectiveDomain f := hD_dom (hσD hz_sigma)
    have hy_dom : (y : H) ∈ effectiveDomain f := hD_dom y.2
    let R : H → ℝ := fun z ↦ (f z : EReal).toReal - (f x : EReal).toReal - ⟪u, z - x⟫_ℝ
    have hy_nonneg : 0 ≤ R y := by
      have hu_mem_sub : u ∈ (∂ f) x := by
        simp [hu_single]
      simpa [R] using
        (remainder_norm_le_norm_mul_of_two_subgradients
          (x := x) (y := (y : H)) (u := u) (v := gradf y)
          (hD_dom hx) hy_dom hu_mem_sub hv_sub).1
    have hstep :
        (δ / B) * ‖gradf y - u‖ ^ 2 ≤ R zPoint - R y := by
      simpa [R, zPoint] using
        remainder_gap_lower_bound_of_mem_subdifferential_step
          (x := x) (y := (y : H)) (u := u) (v := gradf y) (t := δ / B) hy_dom hz_dom hv_sub
    have hz_remainder :
        R zPoint ≤ κ * ‖zPoint - x‖ := by
      have hz_norm :
          ‖R zPoint‖ ≤ κ * ‖zPoint - x‖ := by
        simpa [R] using hηbound zPoint hz_eta
      exact le_trans (le_abs_self _) hz_norm
    have hmain :
        (δ / B) * ‖gradf y - u‖ ^ 2 ≤ κ * ‖zPoint - x‖ := by
      exact le_trans (le_trans hstep (sub_le_self _ hy_nonneg)) hz_remainder
    have hδ_div_B_pos : 0 < δ / B := div_pos hδpos hBpos
    have hdiv :
        ‖gradf y - u‖ ^ 2 ≤ (κ * ‖zPoint - x‖) / (δ / B) := by
      have hmain' :
          ‖gradf y - u‖ ^ 2 * (δ / B) ≤ κ * ‖zPoint - x‖ := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmain
      exact (le_div_iff₀ hδ_div_B_pos).2 hmain'
    have hnorm_sq :
        ‖gradf y - u‖ ^ 2 ≤ ε ^ 2 / 4 := by
      have hz_small : κ * ‖zPoint - x‖ ≤ κ * (2 * δ) := by
        have hz_dist' : ‖zPoint - x‖ ≤ 2 * δ := by
          simpa [dist_eq_norm] using hz_dist
        exact mul_le_mul_of_nonneg_left hz_dist' (le_of_lt hκpos)
      have hdiv' :
          ‖gradf y - u‖ ^ 2 ≤ (κ * (2 * δ)) / (δ / B) := by
        exact le_trans hdiv <| by
          exact (div_le_div_of_nonneg_right hz_small (le_of_lt hδ_div_B_pos))
      have hrewrite : (κ * (2 * δ)) / (δ / B) = 2 * κ * B := by
        field_simp [hδpos.ne', hBpos.ne']
      have hκ_eval : 2 * κ * B = ε ^ 2 / 4 := by
        dsimp [κ]
        field_simp [hBpos.ne']
        norm_num
      calc
        ‖gradf y - u‖ ^ 2 ≤ (κ * (2 * δ)) / (δ / B) := hdiv'
        _ = 2 * κ * B := hrewrite
        _ = ε ^ 2 / 4 := hκ_eval
    have hnorm_half : ‖gradf y - u‖ ≤ ε / 2 := by
      nlinarith [sq_nonneg ‖gradf y - u‖, hnorm_sq]
    have hnorm_lt : ‖gradf y - u‖ < ε := by
      linarith
    simpa [Metric.mem_ball, dist_eq_norm, hu_eq] using hnorm_lt
  · intro hcont
    have hcontDual :
        ContinuousWithinAt (fun y ↦ toDual ℝ H (gradf y)) D x := by
      have htoDual :
          ContinuousWithinAt (InnerProductSpace.toDual ℝ H) Set.univ (gradf x) := by
        simpa using
          (InnerProductSpace.toDual ℝ H).continuous.continuousAt.continuousWithinAt
      exact htoDual.comp hcont (by intro y hy; simp)
    have hFDeriv :
        HasFDerivAt g (toDual ℝ H (gradf x)) x :=
      hasFDerivAt_of_gateauxDerivative_continuousWithinAt (hD_open.mem_nhds hx) hgrad hcontDual
    simpa [g] using hFDeriv.differentiableAt

end DifferentiabilityOfConvexFunctions

end ERealFunction
