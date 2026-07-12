import Mathlib
import DifferentialForms_Cartan_1970.VI.section22.«0006_Definition_VI_1_extra_4»

open Set
open scoped ComplexConjugate
open EuclideanGeometry

noncomputable section

-- Domain sampling note: the source-facing geometry here is the reflected circle decomposition of a
-- planar domain. For the geometry, the owner abstraction is mathlib's
-- `EuclideanGeometry.inversion`; for the holomorphic-isomorphism layer, the relevant chapter owner
-- is `HolomorphicIsomorph`, with primitive data supplied by
-- `OpenPartialHomeomorph.IsHolomorphicIsoOn` and the function-level viewpoint treated only as a
-- derived bridge. The theorem statements below therefore reuse `inversion` and
-- `HolomorphicIsomorph` directly, while keeping the source-facing circle decomposition sets
-- explicit.

/-- The part of `D` lying strictly outside the circle of center `a` and radius `r`. -/
def circleExterior (a : ℂ) (r : ℝ) (D : Set ℂ) : Set ℂ :=
  D \ Metric.closedBall a r

/-- Helper for `circleExterior`: membership is the exterior-radius condition inside `D`. -/
theorem mem_circleExterior {a z : ℂ} {r : ℝ} {D : Set ℂ} :
    z ∈ circleExterior a r D ↔ z ∈ D ∧ r < ‖z - a‖ := by
  -- Unfold the exterior cut and rewrite circle membership in terms of the norm radius.
  simp [circleExterior, Metric.mem_closedBall, dist_eq_norm, not_le]

/-- The part of `D` lying strictly inside the circle of center `a` and radius `r`. -/
def circleInterior (a : ℂ) (r : ℝ) (D : Set ℂ) : Set ℂ :=
  D ∩ Metric.ball a r

/-- Helper for `circleInterior`: membership is the interior-radius condition inside `D`. -/
theorem mem_circleInterior {a z : ℂ} {r : ℝ} {D : Set ℂ} :
    z ∈ circleInterior a r D ↔ z ∈ D ∧ ‖z - a‖ < r := by
  -- Unfold the interior cut and rewrite the metric-ball condition as a norm inequality.
  simp [circleInterior, Metric.mem_ball, dist_eq_norm]

/-- The boundary arc cut out from the circle of center `a` and radius `r` by the set `D`. -/
def circleBoundaryArc (a : ℂ) (r : ℝ) (D : Set ℂ) : Set ℂ :=
  D ∩ Metric.sphere a r

/-- Helper for `circleBoundaryArc`: membership means belonging to `D` and to the circle. -/
theorem mem_circleBoundaryArc {a z : ℂ} {r : ℝ} {D : Set ℂ} :
    z ∈ circleBoundaryArc a r D ↔ z ∈ D ∧ z ∈ Metric.sphere a r := by
  -- Unfold the boundary-arc cut; the sphere condition is already the intended boundary datum.
  simp [circleBoundaryArc]

/-- Helper for Exercise 6: if `D` is open, then its circle exterior cut is open as well. -/
theorem isOpen_circleExterior {a : ℂ} {r : ℝ} {D : Set ℂ} (hD_open : IsOpen D) :
    IsOpen (circleExterior a r D) := by
  -- The exterior region is the open domain intersected with the complement of the closed ball.
  simpa [circleExterior, Set.diff_eq] using
    hD_open.inter Metric.isClosed_closedBall.isOpen_compl

/-- Helper for Exercise 6: a point of the open domain lying on the frontier of the exterior cut
must lie on the boundary arc of the defining circle. -/
theorem mem_circleBoundaryArc_of_mem_frontier_circleExterior
    {a z : ℂ} {r : ℝ} {D : Set ℂ} (hD_open : IsOpen D) (hzD : z ∈ D)
    (hzFront : z ∈ frontier (circleExterior a r D)) :
    z ∈ circleBoundaryArc a r D := by
  have hExterior_open : IsOpen (circleExterior a r D) :=
    isOpen_circleExterior hD_open
  have hz_not_exterior : z ∉ circleExterior a r D := by
    -- A frontier point of an open set cannot lie in that open set's interior.
    intro hzExterior
    exact hzFront.2 <| mem_interior_iff_mem_nhds.2 (hExterior_open.mem_nhds hzExterior)
  have hz_le : ‖z - a‖ ≤ r := by
    -- If the radius were already strictly larger than `r`, the point would lie in the exterior.
    by_contra hz_le
    exact hz_not_exterior <| (mem_circleExterior).2 ⟨hzD, not_le.mp hz_le⟩
  have hz_ge : r ≤ ‖z - a‖ := by
    -- If the point were strictly inside the circle, a small ball around it would miss the exterior,
    -- contradicting frontier-membership.
    by_contra hz_ge
    have hz_ball : z ∈ Metric.ball a r := by
      simpa [Metric.mem_ball, dist_eq_norm] using not_le.mp hz_ge
    have hz_lt : ‖z - a‖ < r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz_ball
    let ε : ℝ := (r - ‖z - a‖) / 2
    have hεpos : 0 < ε := by
      dsimp [ε]
      linarith
    rcases Metric.mem_closure_iff.mp hzFront.1 ε hεpos with ⟨w, hwExterior, hwClose⟩
    have hw_ball_a : w ∈ Metric.ball a r := by
      have hwz : dist w z < ε := by
        simpa [ε, dist_comm] using hwClose
      have hdist : dist w a < r := by
        calc
          dist w a ≤ dist w z + dist a z := dist_triangle_right _ _ _
          _ = dist w z + dist z a := by rw [dist_comm a z]
          _ < ε + dist z a := by
            gcongr
          _ = ((r - ‖z - a‖) / 2) + ‖z - a‖ := by simp [ε, dist_eq_norm]
          _ < r := by linarith
      simpa [Metric.mem_ball] using hdist
    have hw_not_exterior : w ∉ circleExterior a r D := by
      rw [mem_circleExterior]
      intro hwExterior'
      exact (not_lt_of_ge hwExterior'.2.le) <| by
        simpa [Metric.mem_ball, dist_eq_norm] using hw_ball_a
    exact hw_not_exterior hwExterior
  have hz_sphere : z ∈ Metric.sphere a r := by
    rw [Metric.mem_sphere, dist_eq_norm]
    exact le_antisymm hz_le hz_ge
  -- Combine the ambient-domain membership with the circle equation.
  exact mem_circleBoundaryArc.2 ⟨hzD, hz_sphere⟩

/-- Helper for Exercise 6: a boundary-arc point lies on the frontier of the corresponding exterior
cut. -/
theorem mem_frontier_circleExterior_of_mem_circleBoundaryArc
    {a z : ℂ} {r : ℝ} {D : Set ℂ} (hD_open : IsOpen D)
    (hz : z ∈ circleBoundaryArc a r D) :
    z ∈ frontier (circleExterior a r D) := by
  rcases mem_circleBoundaryArc.mp hz with ⟨hzD, hzSphere⟩
  have hz_closure_compl : z ∈ closure (Metric.closedBall a r)ᶜ := by
    have hz_front_closedBall : z ∈ frontier (Metric.closedBall a r) := by
      -- The sphere is exactly the frontier of the closed ball.
      simpa [frontier_closedBall' a r] using hzSphere
    have hz_front_compl : z ∈ frontier (Metric.closedBall a r)ᶜ := by
      simpa using hz_front_closedBall
    exact frontier_subset_closure hz_front_compl
  have hz_closure : z ∈ closure (circleExterior a r D) := by
    -- Intersect the complement-side closure with the ambient open domain `D`.
    rw [circleExterior, Set.diff_eq, inter_comm]
    refine mem_closure_iff.2 ?_
    intro o ho hzO
    have hOD_open : IsOpen (o ∩ D) := ho.inter hD_open
    have hzOD : z ∈ o ∩ D := ⟨hzO, hzD⟩
    simpa [inter_assoc, inter_left_comm, inter_comm] using
      (mem_closure_iff.1 hz_closure_compl (o ∩ D) hOD_open hzOD)
  have hz_not_exterior : z ∉ circleExterior a r D := by
    -- A boundary point has radius exactly `r`, so it cannot satisfy the strict exterior inequality.
    rw [mem_circleExterior]
    intro hzExterior
    have hz_eq : ‖z - a‖ = r := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hzSphere
    linarith
  have hz_not_interior : z ∉ interior (circleExterior a r D) := by
    -- Interior points of the exterior certainly belong to the exterior.
    intro hzInterior
    exact hz_not_exterior (interior_subset hzInterior)
  -- A frontier point is exactly a closure point that is not interior.
  rw [frontier]
  exact ⟨hz_closure, hz_not_interior⟩

/-- A subset of `sphere a r` is an open arc if it is a connected proper subset that is open in the
relative topology of the circle. -/
def IsOpenArcOnCircle (a : ℂ) (r : ℝ) (s : Set ℂ) : Prop :=
  IsConnected s ∧ s ⊂ Metric.sphere a r ∧ IsOpen (((↑) : Metric.sphere a r → ℂ) ⁻¹' s)

/-- Helper for `IsOpenArcOnCircle`: every open arc lies on the ambient circle. -/
theorem IsOpenArcOnCircle.subset_sphere {a : ℂ} {r : ℝ} {s : Set ℂ}
    (hs : IsOpenArcOnCircle a r s) :
    s ⊆ Metric.sphere a r :=
  hs.2.1.1

/-- The reflection identity already forces the center to lie outside the reflected set. -/
theorem center_not_mem_of_circleExterior_eq_inversion_image_circleInterior
    {a : ℂ} {r : ℝ} {D : Set ℂ} (hr : 0 < r)
    (hreflect : circleExterior a r D = inversion a r '' circleInterior a r D) :
    a ∉ D := by
  intro haD
  have haInterior : a ∈ circleInterior a r D := by
    rw [mem_circleInterior]
    refine ⟨haD, ?_⟩
    simpa using hr
  have haExterior : a ∈ circleExterior a r D := by
    rw [hreflect]
    exact ⟨a, haInterior, inversion_self a r⟩
  rw [mem_circleExterior] at haExterior
  exact (not_lt_of_ge hr.le) (by simpa using haExterior.2)

/-- The inversion-defined reflection of `f` across the circle of center `a` and radius `r`,
targeting the circle of center `α` and radius `ρ`, uses `f` on the exterior side and on the
boundary arc, and uses the reflected branch `z ↦ inversion α ρ (f (inversion a r z))` on the
interior side. -/
noncomputable def circleReflection
    (a α : ℂ) (r ρ : ℝ) (D : Set ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  let _ : DecidablePred (fun z ↦ z ∈ circleExterior a r D ∪ circleBoundaryArc a r D) :=
    Classical.decPred _
  (circleExterior a r D ∪ circleBoundaryArc a r D).piecewise f
    (fun z ↦ inversion α ρ (f (inversion a r z)))

/-- On the exterior side and on the boundary arc, `circleReflection` agrees with `f`. -/
@[simp] theorem circleReflection_apply_of_mem_exterior_boundary
    {a α z : ℂ} {r ρ : ℝ} {D : Set ℂ} {f : ℂ → ℂ}
    (hz : z ∈ circleExterior a r D ∪ circleBoundaryArc a r D) :
    circleReflection a α r ρ D f z = f z := by
  classical
  simp [circleReflection, hz]

/-- Away from the exterior side and boundary arc, `circleReflection` is given by the reflected
inversion branch. -/
@[simp] theorem circleReflection_apply_of_not_mem_exterior_boundary
    {a α z : ℂ} {r ρ : ℝ} {D : Set ℂ} {f : ℂ → ℂ}
    (hz : z ∉ circleExterior a r D ∪ circleBoundaryArc a r D) :
    circleReflection a α r ρ D f z = inversion α ρ (f (inversion a r z)) := by
  classical
  simp [circleReflection, hz]

/-- `circleReflection` extends `f` on the exterior side together with the boundary arc. -/
theorem circleReflection_eqOn_exterior_boundary (a α : ℂ) (r ρ : ℝ) (D : Set ℂ) (f : ℂ → ℂ) :
    Set.EqOn (circleReflection a α r ρ D f) f (circleExterior a r D ∪ circleBoundaryArc a r D) :=
  fun _ hz ↦ circleReflection_apply_of_mem_exterior_boundary hz

namespace Function

/-- A complex-valued function on `ℂ` is biholomorphic from `D` onto `Δ` when it is realized on `D`
by some chapter-level `HolomorphicIsomorph D Δ`. This is a bridge/view of the owner abstraction,
not a second owner. -/
def IsHolomorphicIsomorphOn (f : ℂ → ℂ) (D Δ : Set ℂ) : Prop :=
  ∃ e : HolomorphicIsomorph D Δ, Set.EqOn e f D

end Function

/-- Helper for Exercise 6: if a function agrees on the source with a holomorphic isomorphism, then
it is analytic on that source. -/
theorem analyticOnNhd_of_eqOn_holomorphicIsomorph
    {D Δ : Set ℂ} {f : ℂ → ℂ} (e : HolomorphicIsomorph D Δ) (he : Set.EqOn e f D) :
    AnalyticOnNhd ℂ f D := by
  -- Replace `f` by the already-holomorphic model `e` on the open source.
  have hD_open : IsOpen D := e.isOpen_source
  simpa using AnalyticOnNhd.congr hD_open e.analyticOn_toFun he

/-- Helper for Exercise 6: if a function agrees on the source with a holomorphic isomorphism, then
it maps the source into the target. -/
theorem mapsTo_target_of_eqOn_holomorphicIsomorph
    {D Δ : Set ℂ} {f : ℂ → ℂ} (e : HolomorphicIsomorph D Δ) (he : Set.EqOn e f D) :
    Set.MapsTo f D Δ := by
  intro z hz
  -- First map `z` into the target through the canonical partial homeomorphism, then rewrite by
  -- the source-side equality `e = f`.
  have hz_source : z ∈ (e : OpenPartialHomeomorph ℂ ℂ).source := by
    simpa [HolomorphicIsomorph.source_eq] using hz
  have hz_target : e z ∈ Δ := by
    simpa [HolomorphicIsomorph.target_eq] using
      (e : OpenPartialHomeomorph ℂ ℂ).map_source hz_source
  simpa [he hz] using hz_target

/-- The source reflection identity sends interior points to exterior points under inversion. -/
theorem inversion_mapsTo_circleExterior
    {a : ℂ} {r : ℝ} {D : Set ℂ}
    (hD_reflect : circleExterior a r D = inversion a r '' circleInterior a r D) :
    Set.MapsTo (inversion a r) (circleInterior a r D) (circleExterior a r D) := by
  intro z hz
  rw [hD_reflect]
  exact ⟨z, hz, rfl⟩

/-- The target reflection identity sends exterior points back to interior points under inversion. -/
theorem inversion_mapsTo_circleInterior
    {a : ℂ} {r : ℝ} {D : Set ℂ}
    (hr : 0 < r)
    (hD_reflect : circleExterior a r D = inversion a r '' circleInterior a r D) :
    Set.MapsTo (inversion a r) (circleExterior a r D) (circleInterior a r D) := by
  intro z hz
  rw [hD_reflect] at hz
  rcases hz with ⟨w, hw, rfl⟩
  simpa [hr.ne'] using hw

/-- Helper for Exercise 6: an open boundary arc omits a point of its ambient circle, so that point
lies outside the ambient domain. -/
theorem exists_sphere_point_not_mem_of_open_arc
    {a : ℂ} {r : ℝ} {D : Set ℂ}
    (hC₀ : IsOpenArcOnCircle a r (circleBoundaryArc a r D)) :
    ∃ p ∈ Metric.sphere a r, p ∉ D := by
  rcases Set.exists_of_ssubset hC₀.2.1 with ⟨p, hpSphere, hpNotArc⟩
  refine ⟨p, hpSphere, ?_⟩
  intro hpD
  exact hpNotArc (mem_circleBoundaryArc.mpr ⟨hpD, hpSphere⟩)
