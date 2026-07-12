import DifferentialForms_Cartan_1970.VI.section26.«0016_Exercise_6».CircleDecomposition
import DifferentialForms_Cartan_1970.VI.section26.«0016_Exercise_6».ReflectionLine

open Set
open scoped ComplexConjugate
open EuclideanGeometry

noncomputable section

/-- Helper for Exercise 6: a boundary point of the source arc is a closure point of the target
exterior once the exterior branch is continuous and maps into the target exterior. -/
theorem image_mem_closure_circleExterior_of_boundary_point
    {a α z : ℂ} {r ρ : ℝ} {D Δ : Set ℂ} {f : ℂ → ℂ}
    (hD_open : IsOpen D)
    (hf_cont :
      ContinuousOn f (circleExterior a r D ∪ circleBoundaryArc a r D))
    (hf_maps :
      Set.MapsTo f (circleExterior a r D) (circleExterior α ρ Δ))
    (hz : z ∈ circleBoundaryArc a r D) :
    f z ∈ closure (circleExterior α ρ Δ) := by
  have hz_frontier : z ∈ frontier (circleExterior a r D) :=
    mem_frontier_circleExterior_of_mem_circleBoundaryArc hD_open hz
  have hz_closure : z ∈ closure (circleExterior a r D) :=
    frontier_subset_closure hz_frontier
  have hz_union : z ∈ circleExterior a r D ∪ circleBoundaryArc a r D := Or.inr hz
  have hcontWithin :
      ContinuousWithinAt f (circleExterior a r D) z := by
    -- Restrict the boundary continuity of `f` to the exterior trace that approaches `z`.
    exact (hf_cont z hz_union).mono (by intro w hw; exact Or.inl hw)
  -- Push the exterior closure point through the continuous exterior-side trace of `f`.
  exact hcontWithin.mem_closure hz_closure hf_maps

/-- Helper for Exercise 6: if a closure point of the target exterior is known to stay in `Δ` and
not to lie in the strict exterior, then it lies on the target boundary arc. -/
theorem mem_circleBoundaryArc_of_not_mem_circleExterior_of_mem_closure_circleExterior
    {α w : ℂ} {ρ : ℝ} {Δ : Set ℂ}
    (hΔ_open : IsOpen Δ) (hwΔ : w ∈ Δ)
    (hw_not_exterior : w ∉ circleExterior α ρ Δ)
    (hw_closure : w ∈ closure (circleExterior α ρ Δ)) :
    w ∈ circleBoundaryArc α ρ Δ := by
  have hnorm_ge : ρ ≤ ‖w - α‖ := by
    by_contra hnorm_ge
    have hw_ball : w ∈ Metric.ball α ρ := by
      simpa [Metric.mem_ball, dist_eq_norm] using not_le.mp hnorm_ge
    have h_open : IsOpen (Δ ∩ Metric.ball α ρ) := hΔ_open.inter Metric.isOpen_ball
    have hw_mem : w ∈ Δ ∩ Metric.ball α ρ := ⟨hwΔ, hw_ball⟩
    rcases mem_closure_iff.mp hw_closure (Δ ∩ Metric.ball α ρ) h_open hw_mem with
      ⟨y, hy_mem, hy_exterior⟩
    have hy_not_exterior : y ∉ circleExterior α ρ Δ := by
      rw [mem_circleExterior]
      intro hy_exterior'
      exact (not_lt_of_ge hy_exterior'.2.le) <| by
        simpa [Metric.mem_ball, dist_eq_norm] using hy_mem.2
    exact hy_not_exterior hy_exterior
  have hnorm_le : ‖w - α‖ ≤ ρ := by
    by_contra hnorm_le
    exact hw_not_exterior ((mem_circleExterior).2 ⟨hwΔ, not_le.mp hnorm_le⟩)
  -- The target point lies in `Δ`, is not strictly exterior, and is a closure point of the
  -- exterior, so its radius must be exactly `ρ`.
  refine mem_circleBoundaryArc.2 ⟨hwΔ, ?_⟩
  rw [Metric.mem_sphere, dist_eq_norm]
  exact le_antisymm hnorm_le hnorm_ge

/-- Helper for Exercise 6: when the exterior branch already agrees with a holomorphic isomorphism,
no boundary-arc value can land in the strict target exterior. -/
theorem boundary_value_not_mem_target_exterior_of_exterior_isomorphism
    {a α : ℂ} {r ρ : ℝ} {D Δ : Set ℂ} {f : ℂ → ℂ}
    (hD_open : IsOpen D)
    (hf_cont :
      ContinuousOn f (circleExterior a r D ∪ circleBoundaryArc a r D))
    (e₀ : HolomorphicIsomorph (circleExterior a r D) (circleExterior α ρ Δ))
    (he₀ : Set.EqOn e₀ f (circleExterior a r D)) :
    Set.MapsTo f (circleBoundaryArc a r D) (circleExterior α ρ Δ)ᶜ := by
  intro z hz_boundary hz_target_exterior
  have hz_union : z ∈ circleExterior a r D ∪ circleBoundaryArc a r D := Or.inr hz_boundary
  have hz_frontier : z ∈ frontier (circleExterior a r D) :=
    mem_frontier_circleExterior_of_mem_circleBoundaryArc hD_open hz_boundary
  have hz_closure : z ∈ closure (circleExterior a r D) :=
    frontier_subset_closure hz_frontier
  have hcontWithin :
      ContinuousWithinAt f (circleExterior a r D) z := by
    -- Restrict the given boundary continuity to the exterior branch approaching `z`.
    exact (hf_cont z hz_union).mono (by intro w hw; exact Or.inl hw)
  have hsymm_cont :
      ContinuousAt ((e₀ : OpenPartialHomeomorph ℂ ℂ).symm) (f z) := by
    -- The inverse branch is continuous at every point of the target exterior.
    have hz_target : f z ∈ (e₀ : OpenPartialHomeomorph ℂ ℂ).target := by
      simpa [e₀.target_eq] using hz_target_exterior
    exact (e₀ : OpenPartialHomeomorph ℂ ℂ).continuousAt_symm hz_target
  have hcomp_tendsto :
      Filter.Tendsto (fun w ↦ ((e₀ : OpenPartialHomeomorph ℂ ℂ).symm) (f w))
        (nhdsWithin z (circleExterior a r D))
        (nhds (((e₀ : OpenPartialHomeomorph ℂ ℂ).symm) (f z))) :=
    (hsymm_cont.comp_continuousWithinAt hcontWithin).tendsto
  have hEqOnExterior :
      Set.EqOn
        (fun w ↦ ((e₀ : OpenPartialHomeomorph ℂ ℂ).symm) (f w))
        (fun w ↦ w) (circleExterior a r D) := by
    intro w hw
    -- On the exterior, `f` is literally the biholomorphic branch `e₀`.
    calc
      ((e₀ : OpenPartialHomeomorph ℂ ℂ).symm) (f w)
          = ((e₀ : OpenPartialHomeomorph ℂ ℂ).symm) (e₀ w) := by rw [← he₀ hw]
      _ = w := (e₀ : OpenPartialHomeomorph ℂ ℂ).left_inv <| by simpa [e₀.source_eq] using hw
  have hEqWithin :
      (fun w ↦ ((e₀ : OpenPartialHomeomorph ℂ ℂ).symm) (f w)) =ᶠ[nhdsWithin z
        (circleExterior a r D)]
        (fun w ↦ w) :=
    eventuallyEq_nhdsWithin_of_eqOn hEqOnExterior
  have hId_tendsto :
      Filter.Tendsto (fun w : ℂ ↦ w) (nhdsWithin z (circleExterior a r D)) (nhds z) :=
    continuousWithinAt_id.tendsto
  haveI : Filter.NeBot (nhdsWithin z (circleExterior a r D)) :=
    mem_closure_iff_nhdsWithin_neBot.mp hz_closure
  have hz_eq :
      ((e₀ : OpenPartialHomeomorph ℂ ℂ).symm) (f z) = z := by
    -- The inverse branch agrees with the identity along the exterior approach to `z`.
    exact tendsto_nhds_unique (hcomp_tendsto.congr' hEqWithin) hId_tendsto
  have hz_source : z ∈ (e₀ : OpenPartialHomeomorph ℂ ℂ).source := by
    -- Evaluating the inverse branch at `f z` still lands in the source.
    have hsymm_source :
        ((e₀ : OpenPartialHomeomorph ℂ ℂ).symm) (f z) ∈
          (e₀ : OpenPartialHomeomorph ℂ ℂ).source :=
      (e₀ : OpenPartialHomeomorph ℂ ℂ).map_target <| by
        simpa [e₀.target_eq] using hz_target_exterior
    simpa [hz_eq] using hsymm_source
  have hz_exterior : z ∈ circleExterior a r D := by
    simpa [e₀.source_eq] using hz_source
  have hz_not_interior : z ∉ interior (circleExterior a r D) := hz_frontier.2
  have hExterior_open : IsOpen (circleExterior a r D) := isOpen_circleExterior hD_open
  have hz_interior : z ∈ interior (circleExterior a r D) := by
    exact mem_interior_iff_mem_nhds.2 (hExterior_open.mem_nhds hz_exterior)
  exact hz_not_interior hz_interior

/-- Helper for Exercise 6: each boundary-arc point of an open reflected domain has nearby points
of the same domain lying strictly outside the defining circle. -/
theorem exists_mem_circleExterior_of_mem_circleBoundaryArc
    {a z : ℂ} {r : ℝ} {D : Set ℂ} (hr : 0 < r) (hD_open : IsOpen D)
    (hz : z ∈ circleBoundaryArc a r D) :
    ∃ w ∈ circleExterior a r D, w ∈ Metric.ball z r := by
  rcases mem_circleBoundaryArc.mp hz with ⟨hzD, hzSphere⟩
  have hz_norm : ‖z - a‖ = r := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hzSphere
  rcases Metric.mem_nhds_iff.mp (hD_open.mem_nhds hzD) with ⟨ε, hε_pos, hε_sub⟩
  let t : ℝ := min (ε / (2 * r)) (1 / 2)
  have ht_pos : 0 < t := by
    -- The radial step can be chosen positive because both the openness radius and `r` are positive.
    dsimp [t]
    refine lt_min ?_ (by norm_num)
    positivity
  have ht_nonneg : 0 ≤ t := ht_pos.le
  have ht_le : t ≤ ε / (2 * r) := by
    dsimp [t]
    exact min_le_left _ _
  let w : ℂ := z + t • (z - a)
  have hw_ball_ε : w ∈ Metric.ball z ε := by
    have hw_dist : dist w z = t * r := by
      calc
        dist w z = ‖w - z‖ := by rw [dist_eq_norm]
        _ = ‖t • (z - a)‖ := by
          simp [w, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        _ = ‖t‖ * ‖z - a‖ := norm_smul _ _
        _ = t * r := by
          simp [Real.norm_of_nonneg ht_nonneg, hz_norm]
    have hw_lt : dist w z < ε := by
      rw [hw_dist]
      have htr_le : t * r ≤ ε / 2 := by
        have hmul : t * r ≤ (ε / (2 * r)) * r :=
          mul_le_mul_of_nonneg_right ht_le hr.le
        have hcancel : (ε / (2 * r)) * r = ε / 2 := by
          field_simp [hr.ne']
        simpa [hcancel] using hmul
      have hhalf_lt : ε / 2 < ε := by
        linarith
      exact lt_of_le_of_lt htr_le hhalf_lt
    simpa [Metric.mem_ball] using hw_lt
  have hwD : w ∈ D := hε_sub hw_ball_ε
  have hw_norm : ‖w - a‖ = (1 + t) * r := by
    have hw_sub : w - a = (1 + t) • (z - a) := by
      calc
        w - a = (z - a) + t • (z - a) := by
          simp [w, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        _ = (1 + t) • (z - a) := by
          simp [add_smul, one_smul]
    calc
      ‖w - a‖ = ‖(1 + t) • (z - a)‖ := by rw [hw_sub]
      _ = ‖1 + t‖ * ‖z - a‖ := norm_smul _ _
      _ = (1 + t) * r := by
        have h1t_nonneg : 0 ≤ 1 + t := by linarith
        simp [Real.norm_of_nonneg h1t_nonneg, hz_norm]
  have hw_exterior_norm : r < ‖w - a‖ := by
    rw [hw_norm]
    nlinarith [ht_pos, hr]
  have hw_ball_r : w ∈ Metric.ball z r := by
    have hw_lt : dist w z < r := by
      have hw_dist : dist w z = t * r := by
        calc
          dist w z = ‖w - z‖ := by rw [dist_eq_norm]
          _ = ‖t • (z - a)‖ := by
            simp [w, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          _ = ‖t‖ * ‖z - a‖ := norm_smul _ _
          _ = t * r := by
            simp [Real.norm_of_nonneg ht_nonneg, hz_norm]
      rw [hw_dist]
      have ht_half : t ≤ (1 / 2 : ℝ) := by
        dsimp [t]
        exact min_le_right _ _
      nlinarith [ht_half, hr]
    simpa [Metric.mem_ball] using hw_lt
  -- The radial perturbation stays inside `D` and pushes the point strictly outside the circle.
  exact ⟨w, (mem_circleExterior.2 ⟨hwD, hw_exterior_norm⟩), hw_ball_r⟩

/-- Helper for Exercise 6: a boundary-arc point has source-exterior points in every sufficiently
small neighborhood inside the ambient open domain. -/
theorem exists_mem_circleExterior_mem_ball_of_mem_circleBoundaryArc
    {a z : ℂ} {r ε : ℝ} {D : Set ℂ} (hr : 0 < r) (hε : 0 < ε) (hD_open : IsOpen D)
    (hz : z ∈ circleBoundaryArc a r D) :
    ∃ w ∈ circleExterior a r D, w ∈ Metric.ball z ε := by
  rcases mem_circleBoundaryArc.mp hz with ⟨hzD, hzSphere⟩
  have hz_norm : ‖z - a‖ = r := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hzSphere
  rcases Metric.mem_nhds_iff.mp (hD_open.mem_nhds hzD) with ⟨δ, hδ_pos, hδ_sub⟩
  let η : ℝ := min δ ε
  have hη_pos : 0 < η := by
    dsimp [η]
    exact lt_min hδ_pos hε
  let t : ℝ := min (η / (2 * r)) (1 / 2)
  have ht_pos : 0 < t := by
    -- The radial step is chosen small enough both for the ambient-domain ball and for the
    -- prescribed neighborhood around `z`.
    dsimp [t]
    refine lt_min ?_ (by norm_num)
    positivity
  have ht_nonneg : 0 ≤ t := ht_pos.le
  have ht_le : t ≤ η / (2 * r) := by
    dsimp [t]
    exact min_le_left _ _
  let w : ℂ := z + t • (z - a)
  have hw_ball_η : w ∈ Metric.ball z η := by
    have hw_dist : dist w z = t * r := by
      calc
        dist w z = ‖w - z‖ := by rw [dist_eq_norm]
        _ = ‖t • (z - a)‖ := by
          simp [w, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        _ = ‖t‖ * ‖z - a‖ := norm_smul _ _
        _ = t * r := by
          simp [Real.norm_of_nonneg ht_nonneg, hz_norm]
    have hw_lt : dist w z < η := by
      rw [hw_dist]
      have htr_le : t * r ≤ η / 2 := by
        have hmul : t * r ≤ (η / (2 * r)) * r :=
          mul_le_mul_of_nonneg_right ht_le hr.le
        have hcancel : (η / (2 * r)) * r = η / 2 := by
          field_simp [hr.ne']
        simpa [hcancel] using hmul
      have hhalf_lt : η / 2 < η := by
        linarith
      exact lt_of_le_of_lt htr_le hhalf_lt
    simpa [Metric.mem_ball] using hw_lt
  have hwD : w ∈ D := by
    have hw_ball_δ : w ∈ Metric.ball z δ := by
      have hw_lt_η : dist w z < η := by
        simpa [Metric.mem_ball] using hw_ball_η
      have hη_le_δ : η ≤ δ := by
        dsimp [η]
        exact min_le_left _ _
      simpa [Metric.mem_ball] using lt_of_lt_of_le hw_lt_η hη_le_δ
    exact hδ_sub hw_ball_δ
  have hw_norm : ‖w - a‖ = (1 + t) * r := by
    have hw_sub : w - a = (1 + t) • (z - a) := by
      calc
        w - a = (z - a) + t • (z - a) := by
          simp [w, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        _ = (1 + t) • (z - a) := by
          simp [add_smul, one_smul]
    calc
      ‖w - a‖ = ‖(1 + t) • (z - a)‖ := by rw [hw_sub]
      _ = ‖1 + t‖ * ‖z - a‖ := norm_smul _ _
      _ = (1 + t) * r := by
        have h1t_nonneg : 0 ≤ 1 + t := by linarith
        simp [Real.norm_of_nonneg h1t_nonneg, hz_norm]
  have hw_exterior_norm : r < ‖w - a‖ := by
    rw [hw_norm]
    nlinarith [ht_pos, hr]
  have hw_ball_ε : w ∈ Metric.ball z ε := by
    have hw_lt_η : dist w z < η := by
      simpa [Metric.mem_ball] using hw_ball_η
    have hη_le_ε : η ≤ ε := by
      dsimp [η]
      exact min_le_right _ _
    simpa [Metric.mem_ball] using lt_of_lt_of_le hw_lt_η hη_le_ε
  -- The same radial perturbation can be chosen inside any prescribed small neighborhood.
  exact ⟨w, mem_circleExterior.2 ⟨hwD, hw_exterior_norm⟩, hw_ball_ε⟩

/-- Helper for Exercise 6: the exterior side of the reflected domain is nonempty because the open
boundary arc can be pushed slightly outward. -/
theorem circleExterior_nonempty_of_open_arc
    {a : ℂ} {r : ℝ} {D : Set ℂ} (hr : 0 < r) (hD_open : IsOpen D)
    (hC₀ : IsOpenArcOnCircle a r (circleBoundaryArc a r D)) :
    (circleExterior a r D).Nonempty := by
  rcases hC₀.1.nonempty with ⟨z, hz⟩
  rcases exists_mem_circleExterior_of_mem_circleBoundaryArc hr hD_open hz with ⟨w, hw, _⟩
  exact ⟨w, hw⟩

/-- Helper for Exercise 6: the pole chart based at a circle point `p` is the Möbius map
`z ↦ -(z - p)⁻¹`, which is the normalization used to turn the circle into a reflection line. -/
def poleChart (p z : ℂ) : ℂ :=
  -(z - p)⁻¹

/-- Helper for Exercise 6: the canonical inverse of the pole chart is the punctured-plane map
`w ↦ p - w⁻¹`. -/
def invPoleChart (p w : ℂ) : ℂ :=
  p - w⁻¹


/-- Helper for Exercise 6: evaluating the inverse pole chart after the pole chart recovers the
original point away from the pole. -/
@[simp] theorem invPoleChart_poleChart
    {p z : ℂ} (hz : z ≠ p) :
    invPoleChart p (poleChart p z) = z := by
  -- Collapse the two Möbius inversions before simplifying the remaining subtraction.
  simp [invPoleChart, poleChart, sub_eq_add_neg]

/-- Helper for Exercise 6: evaluating the pole chart after the inverse pole chart recovers the
original punctured-plane coordinate. -/
@[simp] theorem poleChart_invPoleChart
    {p w : ℂ} (hw : w ≠ 0) :
    poleChart p (invPoleChart p w) = w := by
  -- The inverse pole chart lands away from the pole exactly because `w` is nonzero.
  simp [invPoleChart, poleChart, sub_eq_add_neg]

/-- Helper for Exercise 6: away from the pole, the pole chart never vanishes. -/
@[simp] theorem poleChart_ne_zero
    {p z : ℂ} (hz : z ≠ p) :
    poleChart p z ≠ 0 := by
  -- Zero would force `z - p = 0`, contradicting the assumption that `z` is away from the pole.
  simpa [poleChart, ne_eq] using sub_ne_zero.mpr hz

/-- Helper for Exercise 6: away from the puncture, the inverse pole chart never returns the pole
itself. -/
@[simp] theorem invPoleChart_ne_base
    {p w : ℂ} (hw : w ≠ 0) :
    invPoleChart p w ≠ p := by
  -- Returning to the pole would mean `w⁻¹ = 0`, hence `w = 0`.
  simp [invPoleChart, hw]

/-- Helper for Exercise 6: the pole chart and its inverse form an open partial homeomorphism
between the punctured plane at `p` and the punctured plane at `0`. -/
def poleChartPartialHomeomorph (p : ℂ) : OpenPartialHomeomorph ℂ ℂ where
  toPartialEquiv :=
    { toFun := poleChart p
      invFun := invPoleChart p
      source := {z : ℂ | z ≠ p}
      target := {w : ℂ | w ≠ 0}
      map_source' := by
        intro z hz
        simpa using poleChart_ne_zero (p := p) hz
      map_target' := by
        intro w hw
        simpa using invPoleChart_ne_base (p := p) hw
      left_inv' := by
        intro z hz
        simpa using invPoleChart_poleChart (p := p) hz
      right_inv' := by
        intro w hw
        simpa using poleChart_invPoleChart (p := p) hw }
  open_source := by
    simpa using (isOpen_ne : IsOpen ({z : ℂ | z ≠ p}))
  open_target := by
    simpa using (isOpen_ne : IsOpen ({w : ℂ | w ≠ 0}))
  continuousOn_toFun := by
    intro z hz
    -- Away from the pole, the Möbius chart is the composition of subtraction, inversion, and
    -- negation.
    have hsub : ContinuousAt (fun w : ℂ ↦ w - p) z :=
      continuousAt_id.sub continuousAt_const
    have hinv :
        ContinuousAt (fun w : ℂ ↦ (w - p)⁻¹) z :=
      hsub.inv₀ (show z - p ≠ 0 by simpa using sub_ne_zero.mpr hz)
    simpa [poleChart] using hinv.neg.continuousWithinAt
  continuousOn_invFun := by
    intro w hw
    -- On the punctured target, the inverse chart is the translate of ordinary inversion.
    simpa [invPoleChart] using
      (continuousAt_const.sub (continuousAt_inv₀ hw)).continuousWithinAt

/-- Helper for Exercise 6: the explicit pole-chart domain
`{w | w ≠ 0 ∧ invPoleChart p w ∈ s}` is open whenever `s` is open. -/
theorem isOpen_explicitPoleChartDomain
    {p : ℂ} {s : Set ℂ} (hs : IsOpen s) :
    IsOpen {w : ℂ | w ≠ 0 ∧ invPoleChart p w ∈ s} := by
  let t : Set ℂ := {w : ℂ | w ≠ 0}
  have ht : IsOpen t := by
    simpa [t] using (isOpen_ne : IsOpen ({w : ℂ | w ≠ 0}))
  have hcont : ContinuousOn (invPoleChart p) t := by
    intro w hw
    -- On the punctured plane, `w ↦ p - w⁻¹` is continuous because inversion is continuous away
    -- from zero.
    simpa [invPoleChart, t, sub_eq_add_neg] using
      (continuousAt_const.sub (continuousAt_inv₀ hw)).continuousWithinAt
  -- Intersect the punctured-plane openness with the open preimage of `s`.
  simpa [t, Set.setOf_and] using hcont.isOpen_inter_preimage ht hs

/-- Helper for Exercise 6: frontier points of the explicit pole-chart pullback of the source
exterior already lie on the pulled-back boundary arc. -/
theorem explicitPoleExteriorFrontier_subset_boundarySlice
    {a p : ℂ} {r : ℝ} {D : Set ℂ} (hD_open : IsOpen D) (hp_not_mem : p ∉ D) :
    {w : ℂ | w ≠ 0 ∧ invPoleChart p w ∈ D} ∩
        frontier {w : ℂ | w ≠ 0 ∧ invPoleChart p w ∈ circleExterior a r D} ⊆
      {w : ℂ | w ≠ 0 ∧ invPoleChart p w ∈ circleBoundaryArc a r D} := by
  intro w hw
  rcases hw with ⟨⟨hw0, hwD⟩, hwFront⟩
  let e : OpenPartialHomeomorph ℂ ℂ := poleChartPartialHomeomorph p
  have hp_not_mem_exterior : p ∉ circleExterior a r D := by
    intro hpExterior
    exact hp_not_mem (mem_circleExterior.mp hpExterior).1
  have hpreExt :
      {w : ℂ | w ≠ 0 ∧ invPoleChart p w ∈ circleExterior a r D} =
        (poleChartPartialHomeomorph p).symm ⁻¹' circleExterior a r D := by
    ext u
    constructor
    · intro hu
      simpa [Set.mem_preimage, poleChartPartialHomeomorph] using hu.2
    · intro hu
      by_cases hu0 : u = 0
      · exfalso
        have hpExterior : p ∈ circleExterior a r D := by
          simpa [Set.mem_preimage, poleChartPartialHomeomorph, invPoleChart, hu0] using hu
        exact hp_not_mem_exterior hpExterior
      · refine ⟨hu0, ?_⟩
        simpa [Set.mem_preimage, poleChartPartialHomeomorph] using hu
  have hwFront' :
      w ∈ e.symm.source ∩ frontier (e.symm ⁻¹' circleExterior a r D) := by
    refine ⟨?_, ?_⟩
    · simpa [e] using hw0
    · simpa [e, hpreExt] using hwFront
  have hwFront'' :
      w ∈ e.symm.source ∩ e.symm ⁻¹' frontier (circleExterior a r D) := by
    rw [← e.symm.preimage_frontier (circleExterior a r D)] at hwFront'
    exact hwFront'
  have hzFront : invPoleChart p w ∈ frontier (circleExterior a r D) := by
    simpa [e] using hwFront''.2
  -- Transport the frontier classification back to the source domain and apply the circle-cut
  -- boundary lemma there.
  exact ⟨hw0, mem_circleBoundaryArc_of_mem_frontier_circleExterior hD_open hwD hzFront⟩

/-- Helper for Exercise 6: under the pole chart based at `p ∈ sphere a r`, circle inversion in the
source sphere becomes Euclidean reflection in the corresponding reflection line. -/
theorem poleChart_reflects_inversion
    {a p z : ℂ} {r : ℝ} (hr : 0 < r) (hp : p ∈ Metric.sphere a r)
    (hz : z ≠ a) (hzp : z ≠ p) :
    reflection (reflection_line (a - p) (-1) (sub_ne_zero.mpr <| by
      intro hpa
      have hpdist : ‖p - a‖ = r := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hp
      exact hr.ne' <| by simpa [hpa] using hpdist.symm) ) (poleChart p z) =
      poleChart p (inversion a r z) := by
  have hp_ne : p ≠ a := by
    intro hpa
    have hpdist : ‖p - a‖ = r := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hp
    exact hr.ne' <| by simpa [hpa] using hpdist.symm
  have hc' : a - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp_ne)
  have hinv_ne : inversion a r z ≠ a := by
    intro h
    exact hz ((inversion_eq_center hr.ne').1 h)
  have hz_inv : inversion_pair a r z (inversion a r z) := ⟨hz, hinv_ne, rfl⟩
  have hz_ne_pole : (1 : ℂ) * z + (-p) ≠ 0 := by
    simpa [sub_eq_add_neg] using sub_ne_zero.mpr hzp
  have hinvz_ne_pole : (1 : ℂ) * inversion a r z + (-p) ≠ 0 := by
    have hp_inv : inversion a r p = p := inversion_of_mem_sphere hp
    intro hzero
    have hz_eq : inversion a r z = p := by
      exact sub_eq_zero.mp <| by simpa [sub_eq_add_neg] using hzero
    have hzinv := congrArg (inversion a r) hz_eq
    exact hzp <| by simpa [hp_inv, inversion_inversion a hr.ne' z] using hzinv
  -- Route correction: reuse Exercise 5's canonical homography-to-reflection theorem for the
  -- specific pole chart instead of reopening the same inversion algebra locally.
  have hreflect := homographic_maps_inversion_pair_to_reflection_line
    (a := a) (z₁ := z) (z₂ := inversion a r z) (α := 0) (β := -1) (γ := 1) (δ := -p) (r := r)
    (by simp) (by simp) hz_inv hz_ne_pole hinvz_ne_pole
    (by simpa [homographic_pole, div_one, Metric.mem_sphere, abs_of_pos hr] using hp)
  simpa [poleChart, homographic_map, image_reflection_line_eq_reflection_line, image_reflection_coeff,
    image_reflection_const, hc', hp, hp_ne, hr.ne', div_eq_mul_inv, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hreflect

/-- Helper for Exercise 6: a boundary point of the source circle is sent by the pole chart to the
corresponding reflection line. -/
theorem poleChart_memReflectionLine_of_mem_sphere
    {a p z : ℂ} {r : ℝ} (hr : 0 < r) (hp : p ∈ Metric.sphere a r)
    (hzSphere : z ∈ Metric.sphere a r) (hzp : z ≠ p) :
    poleChart p z ∈ reflection_line (a - p) (-1) (sub_ne_zero.mpr <| by
      intro hpa
      have hpdist : ‖p - a‖ = r := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hp
      exact hr.ne' <| by simpa [hpa] using hpdist.symm) := by
  have hp_ne : p ≠ a := by
    intro hpa
    have hpdist : ‖p - a‖ = r := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hp
    exact hr.ne' <| by simpa [hpa] using hpdist.symm
  have hc' : a - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp_ne)
  have hz : z ≠ a := by
    intro hza
    have hzdist : ‖z - a‖ = r := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hzSphere
    exact hr.ne' <| by simpa [hza] using hzdist.symm
  have hfix :
      reflection (reflection_line (a - p) (-1) hc') (poleChart p z) = poleChart p z := by
    have hinv : inversion a r z = z := inversion_of_mem_sphere hzSphere
    simpa [hinv] using poleChart_reflects_inversion (a := a) (p := p) (z := z) hr hp hz hzp
  exact (EuclideanGeometry.reflection_eq_self_iff (s := reflection_line (a - p) (-1) hc')
    (p := poleChart p z)).1 hfix

/-- Helper for Exercise 6: on the explicit inverse-chart domain, reflecting in the pole-chart line
and then returning with `invPoleChart` matches inversion in the original circle. -/
theorem invPoleChart_reflection_eq_inversion
    {a p w : ℂ} {r : ℝ} {D : Set ℂ}
    (hr : 0 < r) (hp : p ∈ Metric.sphere a r) (ha_not_mem : a ∉ D)
    (hw : w ≠ 0) (hwD : invPoleChart p w ∈ D) :
    invPoleChart p
      (reflection (reflection_line (a - p) (-1) (sub_ne_zero.mpr <| by
        intro hpa
        have hpdist : ‖p - a‖ = r := by
          simpa [Metric.mem_sphere, dist_eq_norm] using hp
        exact hr.ne' <| by simpa [hpa] using hpdist.symm)) w) =
      inversion a r (invPoleChart p w) := by
  have hp_ne : p ≠ a := by
    intro hpa
    have hpdist : ‖p - a‖ = r := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hp
    exact hr.ne' <| by simpa [hpa] using hpdist.symm
  let L := reflection_line (a - p) (-1) (sub_ne_zero.mpr (Ne.symm hp_ne))
  have hIw_ne_p : invPoleChart p w ≠ p := invPoleChart_ne_base hw
  have hIw_ne_a : invPoleChart p w ≠ a := by
    -- A point of `D` cannot be the circle center because the reflection identity excludes it.
    intro h
    exact ha_not_mem (h ▸ hwD)
  have hreflect : reflection L w = poleChart p (inversion a r (invPoleChart p w)) := by
    -- Transport the reflection identity through the inverse pole chart point `invPoleChart p w`.
    have htransport :=
      poleChart_reflects_inversion (a := a) (p := p) (z := invPoleChart p w) hr hp hIw_ne_a hIw_ne_p
    simpa [L, poleChart_invPoleChart hw] using htransport
  have htarget_ne_p : inversion a r (invPoleChart p w) ≠ p := by
    intro h
    have h' := congrArg (inversion a r) h
    have hp_fix : inversion a r p = p := inversion_of_mem_sphere hp
    have h'' : invPoleChart p w = p := by
      simpa [hp_fix, inversion_inversion, hr.ne'] using h'
    exact hIw_ne_p h''
  -- Returning with `invPoleChart` cancels the pole chart on the reflected point.
  rw [hreflect]
  exact invPoleChart_poleChart htarget_ne_p

/-- Helper for Exercise 6: a point of the explicit inverse-chart domain lying on the pole-chart
reflection line comes from the source boundary arc. -/
theorem invPoleChart_mem_circleBoundaryArc_of_mem_reflectionLine
    {a p w : ℂ} {r : ℝ} {D : Set ℂ}
    (hr : 0 < r) (hp : p ∈ Metric.sphere a r) (ha_not_mem : a ∉ D)
    (hw : w ≠ 0) (hwD : invPoleChart p w ∈ D)
    (hw_line : w ∈ reflection_line (a - p) (-1) (sub_ne_zero.mpr <| by
      intro hpa
      have hpdist : ‖p - a‖ = r := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hp
      exact hr.ne' <| by simpa [hpa] using hpdist.symm)) :
    invPoleChart p w ∈ circleBoundaryArc a r D := by
  have hp_ne : p ≠ a := by
    intro hpa
    have hpdist : ‖p - a‖ = r := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hp
    exact hr.ne' <| by simpa [hpa] using hpdist.symm
  let L := reflection_line (a - p) (-1) (sub_ne_zero.mpr (Ne.symm hp_ne))
  have htransport :
      invPoleChart p (reflection L w) = inversion a r (invPoleChart p w) :=
    invPoleChart_reflection_eq_inversion (a := a) (p := p) (w := w) (r := r) (D := D)
      hr hp ha_not_mem hw hwD
  have hfix : reflection L w = w := by
    exact (EuclideanGeometry.reflection_eq_self_iff (s := L) (p := w)).2 hw_line
  have hinv_fix : inversion a r (invPoleChart p w) = invPoleChart p w := by
    simpa [L, hfix] using htransport.symm
  -- Fixed points of inversion are exactly the points on the reflecting sphere.
  refine mem_circleBoundaryArc.2 ⟨hwD, ?_⟩
  have hIw_ne_a : invPoleChart p w ≠ a := by
    intro h
    exact ha_not_mem (h ▸ hwD)
  have hdist_eq :
      dist (invPoleChart p w) a = r ^ 2 / dist (invPoleChart p w) a := by
    simpa [hinv_fix] using dist_inversion_center a (invPoleChart p w) r
  have hdist_ne0 : dist (invPoleChart p w) a ≠ 0 := dist_ne_zero.mpr hIw_ne_a
  have hdist_sq : dist (invPoleChart p w) a ^ 2 = r ^ 2 := by
    field_simp [hdist_ne0] at hdist_eq
    nlinarith
  have hdist :
      dist (invPoleChart p w) a = r := by
    have hdist_nonneg : 0 ≤ dist (invPoleChart p w) a := dist_nonneg
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hdist_sq |>.elim id (fun hneg => by
      exfalso
      linarith)
  simpa [Metric.mem_sphere, dist_eq_norm, dist_comm] using hdist
