import Mathlib
import DifferentialForms_Cartan_1970.II.section06.«0013_Corollary_II_2_extra_5»
import DifferentialForms_Cartan_1970.II.section06.«0015_Remark_II_2_extra_6»
import DifferentialForms_Cartan_1970.III.section11.«0009_Proposition_4_2»
import DifferentialForms_Cartan_1970.VI.section22.«0005_Corollary_VI_1_extra_3»
import DifferentialForms_Cartan_1970.VI.section22.«0006_Definition_VI_1_extra_4»

-- Declarations for this item will be appended below by the statement pipeline.

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

/-- Helper for Exercise 6: the textbook line `c * w + conj c * conj w = t` is represented as the
corresponding real affine line in `ℂ`. This local owner is enough for the straightening lemmas used
in the current item, so the broken Exercise 5 import is not needed here. -/
def reflection_line (c : ℂ) (t : ℝ) (hc : c ≠ 0) : AffineSubspace ℝ ℂ :=
  let u : ℂˣ := Units.mk0 c hc
  line[ℝ, ((t / (2 * Complex.normSq (u : ℂ)) : ℝ) : ℂ) * star (u : ℂ),
    ((t / (2 * Complex.normSq (u : ℂ)) : ℝ) : ℂ) * star (u : ℂ) + Complex.I * star (u : ℂ)]

/-- Helper for Exercise 6: every `reflection_line` contains its distinguished base point. -/
instance reflection_line_nonempty (c : ℂ) (t : ℝ) (hc : c ≠ 0) :
    Nonempty (reflection_line c t hc) := by
  refine ⟨⟨((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c, ?_⟩⟩
  exact left_mem_affineSpan_pair ℝ _ _

/-- Helper for Exercise 6: the canonical affine parametrization of `reflection_line c t hc`
straightens that line to the real axis. -/
theorem preimage_reflection_line_eq_real_axis
    {c : ℂ} {t : ℝ} (hc : c ≠ 0) :
    let u : ℂ := ((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c
    let v : ℂ := u + Complex.I * star c
    let A : ℂ → ℂ := fun ζ ↦ u + (v - u) * ζ
    A ⁻¹' (reflection_line c t hc : Set ℂ) = {ζ : ℂ | ζ.im = 0} := by
  dsimp
  let u : ℂ := ((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c
  let v : ℂ := u + Complex.I * star c
  let A : ℂ → ℂ := fun ζ ↦ u + (v - u) * ζ
  have hvsub : v - u = Complex.I * star c := by
    -- The affine step from `u` to `v` is exactly the chosen normal direction.
    simp [u, v]
  have huv : u ≠ v := by
    -- The line is nondegenerate because its second endpoint is displaced by `I * conj c`.
    intro huv_eq
    have hdiff : v - u = 0 := by
      simp [huv_eq]
    have hzero : Complex.I * star c = 0 := by
      simpa [hvsub] using hdiff
    have hstar : star c = 0 := by
      exact (mul_eq_zero.mp hzero).resolve_left Complex.I_ne_zero
    exact hc (by simpa using hstar)
  have hline : reflection_line c t hc = line[ℝ, u, v] := by
    -- Unfold the textbook line model into the affine span of its two defining points.
    simp [reflection_line, u, v]
  -- Replace the packaged reflection line by its explicit affine-span presentation.
  simpa [hline, u, v, A, hvsub] using preimage_affine_line_eq_real_axis_of_ne huv

/-- Helper for Exercise 6: after the same affine straightening, complex conjugation should agree
with Euclidean reflection across `reflection_line c t hc`. -/
theorem reflection_line_straightening_intertwines_conj
    {c : ℂ} {t : ℝ} (hc : c ≠ 0) :
    let u : ℂ := ((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c
    let v : ℂ := u + Complex.I * star c
    let A : ℂ → ℂ := fun ζ ↦ u + (v - u) * ζ
    ∀ ζ : ℂ, A (conj ζ) = reflection (reflection_line c t hc) (A ζ) := by
  dsimp
  let u : ℂ := ((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c
  let v : ℂ := u + Complex.I * star c
  let A : ℂ → ℂ := fun ζ ↦ u + (v - u) * ζ
  have hvsub : v - u = Complex.I * star c := by
    -- The affine chart direction is the chosen imaginary tangent to the reflection line.
    simp [u, v]
  have hline : reflection_line c t hc = line[ℝ, u, v] := by
    -- Unfold the textbook reflection line into the affine line through the chosen base points.
    simp [reflection_line, u, v]
  intro ζ
  let n : ℂ := (-(ζ.im : ℝ)) • star c
  have hbase_mem_line : A (ζ.re : ℂ) ∈ (line[ℝ, u, v] : Set ℂ) := by
    -- The real part parameterizes points on the straightened line.
    simpa [A, hvsub, vadd_eq_add, smul_eq_mul, mul_comm, add_comm, add_left_comm, add_assoc] using
      (smul_vsub_vadd_mem_affineSpan_pair (ζ.re) u v)
  have hbase_mem : A (ζ.re : ℂ) ∈ (reflection_line c t hc : Set ℂ) := by
    simpa [hline] using hbase_mem_line
  have hnormal_line : n ∈ (line[ℝ, u, v] : AffineSubspace ℝ ℂ).directionᗮ := by
    -- The normal vector is a real multiple of `star c`, which is orthogonal to the line direction
    -- `Complex.I * star c`.
    refine Submodule.smul_mem _ _ ?_
    rw [direction_affineSpan, vectorSpan_pair_rev,
      Submodule.mem_orthogonal_singleton_iff_inner_left]
    simpa [hvsub, smul_eq_mul, mul_comm] using
      (real_inner_I_smul_self (𝕜 := ℂ) (E := ℂ) (x := star c))
  have hnormal : n ∈ (reflection_line c t hc).directionᗮ := by
    simpa [hline] using hnormal_line
  have hsplit : ∀ η : ℂ, A η = ((-(η.im : ℝ)) • star c) +ᵥ A (η.re : ℂ) := by
    intro η
    -- Split the affine chart into its real-axis point plus the normal displacement.
    have haux :
        A ((η.re : ℂ) + (η.im : ℂ) * Complex.I) = ((-(η.im : ℝ)) • star c) +ᵥ A (η.re : ℂ) := by
      calc
        A ((η.re : ℂ) + (η.im : ℂ) * Complex.I)
            = u + (Complex.I * star c) * ((η.re : ℂ) + (η.im : ℂ) * Complex.I) := by
                simp [A, hvsub]
        _ = u + (Complex.I * star c) * (η.re : ℂ) +
              ((Complex.I * star c) * ((η.im : ℂ) * Complex.I)) := by
                ring
        _ = u + (Complex.I * (η.re : ℂ) * star c) +
              ((Complex.I * Complex.I) * ((η.im : ℂ) * star c)) := by
                ring
        _ = u + (Complex.I * star c) * (η.re : ℂ) - ((η.im : ℂ) * star c) := by
                simp [Complex.I_mul_I, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]
        _ = ((-(η.im : ℝ)) • star c) +ᵥ A (η.re : ℂ) := by
                simp [A, hvsub, vadd_eq_add, sub_eq_add_neg, smul_eq_mul, add_assoc,
                  add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
    simpa [Complex.re_add_im] using haux
  have hreflect :
      reflection (reflection_line c t hc) (A ζ) = -n +ᵥ A (ζ.re : ℂ) := by
    -- Reflecting flips exactly the orthogonal normal component and fixes the base point on the
    -- line.
    rw [hsplit ζ]
    exact reflection_orthogonal_vadd hbase_mem hnormal
  -- Route correction: rather than unfolding reflection globally, compare both sides through the
  -- same line point `A ζ.re` and opposite normal vectors.
  calc
    A (conj ζ) = ((-((conj ζ).im : ℝ)) • star c) +ᵥ A ((conj ζ).re : ℂ) := hsplit (conj ζ)
    _ = -n +ᵥ A (ζ.re : ℂ) := by
      simp [n, Complex.conj_re, Complex.conj_im]
    _ = reflection (reflection_line c t hc) (A ζ) := hreflect.symm

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

/-- Exercise 6 (1): the inversion-defined reflected map is holomorphic on the full reflected
domain. -/
theorem circle_reflection_extension
    {a α : ℂ} {r ρ : ℝ} {D Δ : Set ℂ} {f : ℂ → ℂ}
    (hr : 0 < r) (hρ : 0 < ρ)
    (hD_open : IsOpen D) (hD_connected : IsConnected D)
    (hΔ_open : IsOpen Δ) (hΔ_connected : IsConnected Δ)
    (hC₀ : IsOpenArcOnCircle a r (circleBoundaryArc a r D))
    (hΓ₀ : IsOpenArcOnCircle α ρ (circleBoundaryArc α ρ Δ))
    (hD_reflect :
      circleExterior a r D = inversion a r '' circleInterior a r D)
    (hΔ_reflect :
      circleExterior α ρ Δ = inversion α ρ '' circleInterior α ρ Δ)
    (hf_cont :
      ContinuousOn f (circleExterior a r D ∪ circleBoundaryArc a r D))
    (hf_holo : AnalyticOnNhd ℂ f (circleExterior a r D))
    (hf_maps :
      Set.MapsTo f (circleExterior a r D) (circleExterior α ρ Δ))
    (hf_boundary :
      Set.MapsTo f (circleBoundaryArc a r D) (circleBoundaryArc α ρ Δ)) :
    AnalyticOnNhd ℂ (circleReflection a α r ρ D f) D := by
  -- TODO: straighten both circles to the real axis by a Möbius chart, transport the reflected map
  -- to `schwarzReflection`, and then apply `schwarzReflection_differentiableOn`.
  sorry

/-- Exercise 6 (1): the inversion-defined reflected map carries the interior side into the target
interior side. -/
theorem circleReflection_mapsTo_interior
    {a α : ℂ} {r ρ : ℝ} {D Δ : Set ℂ} {f : ℂ → ℂ}
    (hρ : 0 < ρ)
    (hD_reflect :
      circleExterior a r D = inversion a r '' circleInterior a r D)
    (hΔ_reflect :
      circleExterior α ρ Δ = inversion α ρ '' circleInterior α ρ Δ)
    (hf_maps :
      Set.MapsTo f (circleExterior a r D) (circleExterior α ρ Δ)) :
    Set.MapsTo (circleReflection a α r ρ D f) (circleInterior a r D) (circleInterior α ρ Δ) :=
  by
    intro z hz
    have hz_not_mem :
        z ∉ circleExterior a r D ∪ circleBoundaryArc a r D := by
      rw [mem_circleInterior] at hz
      intro hz'
      rcases hz' with hz_ext | hz_boundary
      · rw [mem_circleExterior] at hz_ext
        exact (not_lt_of_ge hz.2.le) hz_ext.2
      · rw [mem_circleBoundaryArc] at hz_boundary
        have hz_not_sphere : z ∉ Metric.sphere a r := by
          simpa [Metric.mem_sphere, dist_eq_norm] using (ne_of_lt hz.2)
        exact hz_not_sphere hz_boundary.2
    have hz_exterior : inversion a r z ∈ circleExterior a r D :=
      inversion_mapsTo_circleExterior hD_reflect hz
    have hfz_exterior : f (inversion a r z) ∈ circleExterior α ρ Δ :=
      hf_maps hz_exterior
    have hfz_interior : inversion α ρ (f (inversion a r z)) ∈ circleInterior α ρ Δ :=
      inversion_mapsTo_circleInterior hρ hΔ_reflect hfz_exterior
    simpa [circleReflection_apply_of_not_mem_exterior_boundary hz_not_mem] using hfz_interior

/-- Helper for Exercise 6: every point of the ambient domain lies in exactly one of the exterior,
boundary, or interior circle cuts. -/
theorem mem_circleExterior_or_mem_circleBoundaryArc_or_mem_circleInterior
    {a z : ℂ} {r : ℝ} {D : Set ℂ} (hzD : z ∈ D) :
    z ∈ circleExterior a r D ∨ z ∈ circleBoundaryArc a r D ∨ z ∈ circleInterior a r D := by
  -- Compare the radius `‖z - a‖` with `r` to place `z` in the textbook trichotomy.
  rcases lt_trichotomy ‖z - a‖ r with hz_lt | hz_eq | hz_gt
  · exact Or.inr <| Or.inr <| (mem_circleInterior.2 ⟨hzD, hz_lt⟩)
  · refine Or.inr <| Or.inl <| mem_circleBoundaryArc.2 ?_
    refine ⟨hzD, ?_⟩
    simpa [Metric.mem_sphere, dist_eq_norm] using hz_eq
  · exact Or.inl <| (mem_circleExterior.2 ⟨hzD, hz_gt⟩)

/-- Helper for Exercise 6: under the reflected-extension hypotheses, a point of `D` whose image
lies in the strict target exterior must already lie in the strict source exterior. -/
theorem circleReflection_preimage_targetExterior_subset_sourceExterior
    {a α : ℂ} {r ρ : ℝ} {D Δ : Set ℂ} {f : ℂ → ℂ}
    (hρ : 0 < ρ)
    (hD_reflect :
      circleExterior a r D = inversion a r '' circleInterior a r D)
    (hΔ_reflect :
      circleExterior α ρ Δ = inversion α ρ '' circleInterior α ρ Δ)
    (hf_maps :
      Set.MapsTo f (circleExterior a r D) (circleExterior α ρ Δ))
    (hf_boundary_maps :
      Set.MapsTo f (circleBoundaryArc a r D) (circleBoundaryArc α ρ Δ))
    {z : ℂ} (hzD : z ∈ D)
    (hz_target : circleReflection a α r ρ D f z ∈ circleExterior α ρ Δ) :
    z ∈ circleExterior a r D := by
  rcases mem_circleExterior_or_mem_circleBoundaryArc_or_mem_circleInterior hzD with
    hz_ext | hz_boundary | hz_int
  · exact hz_ext
  · exfalso
    have hz_boundary_image : circleReflection a α r ρ D f z ∈ circleBoundaryArc α ρ Δ := by
      -- On the boundary arc, the reflected extension still agrees with the boundary trace `f`.
      rw [circleReflection_apply_of_mem_exterior_boundary (Or.inr hz_boundary)]
      exact hf_boundary_maps hz_boundary
    rw [mem_circleExterior] at hz_target
    rcases mem_circleBoundaryArc.mp hz_boundary_image with ⟨_, hz_sphere⟩
    have hz_norm : ‖circleReflection a α r ρ D f z - α‖ = ρ := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz_sphere
    exact (not_lt_of_ge hz_norm.le) hz_target.2
  · exfalso
    have hz_int_image :
        circleReflection a α r ρ D f z ∈ circleInterior α ρ Δ :=
      circleReflection_mapsTo_interior hρ hD_reflect hΔ_reflect hf_maps hz_int
    rw [mem_circleExterior] at hz_target
    rw [mem_circleInterior] at hz_int_image
    exact (not_lt_of_ge hz_int_image.2.le) hz_target.2

/-- Helper for Exercise 6: interior points lie outside the exterior-or-boundary cut that controls
the `piecewise` definition of `circleReflection`. -/
theorem not_mem_circleExterior_union_circleBoundaryArc_of_mem_circleInterior
    {a z : ℂ} {r : ℝ} {D : Set ℂ} (hz : z ∈ circleInterior a r D) :
    z ∉ circleExterior a r D ∪ circleBoundaryArc a r D := by
  -- The interior inequality excludes both the strict exterior branch and the boundary circle.
  rw [mem_circleInterior] at hz
  intro hz'
  rcases hz' with hz_ext | hz_boundary
  · rw [mem_circleExterior] at hz_ext
    exact (not_lt_of_ge hz.2.le) hz_ext.2
  · rw [mem_circleBoundaryArc] at hz_boundary
    have hz_not_sphere : z ∉ Metric.sphere a r := by
      simpa [Metric.mem_sphere, dist_eq_norm] using (ne_of_lt hz.2)
    exact hz_not_sphere hz_boundary.2

/-- Exercise 6 (1): any other holomorphic extension from the same exterior and boundary data agrees
with the inversion-defined reflected map on all of `D`. -/
theorem eqOn_circleReflection_of_analyticOnNhd
    {a α : ℂ} {r ρ : ℝ} {D Δ : Set ℂ} {f G : ℂ → ℂ}
    (hr : 0 < r) (hρ : 0 < ρ)
    (hD_open : IsOpen D) (hD_connected : IsConnected D)
    (hΔ_open : IsOpen Δ) (hΔ_connected : IsConnected Δ)
    (hC₀ : IsOpenArcOnCircle a r (circleBoundaryArc a r D))
    (hΓ₀ : IsOpenArcOnCircle α ρ (circleBoundaryArc α ρ Δ))
    (hD_reflect :
      circleExterior a r D = inversion a r '' circleInterior a r D)
    (hΔ_reflect :
      circleExterior α ρ Δ = inversion α ρ '' circleInterior α ρ Δ)
    (hf_cont :
      ContinuousOn f (circleExterior a r D ∪ circleBoundaryArc a r D))
    (hf_holo : AnalyticOnNhd ℂ f (circleExterior a r D))
    (hf_maps :
      Set.MapsTo f (circleExterior a r D) (circleExterior α ρ Δ))
    (hf_boundary :
      Set.MapsTo f (circleBoundaryArc a r D) (circleBoundaryArc α ρ Δ))
    (hG_holo : AnalyticOnNhd ℂ G D)
    (hG_eq : Set.EqOn G f (circleExterior a r D ∪ circleBoundaryArc a r D)) :
    Set.EqOn G (circleReflection a α r ρ D f) D := by
  -- Route correction: once the reflected extension is known to be analytic on `D`, uniqueness no
  -- longer needs the straightening charts. The identity principle on the connected domain `D`
  -- applies directly because `G` and `circleReflection` already agree on the nonempty open
  -- exterior slice.
  have hReflection_holo : AnalyticOnNhd ℂ (circleReflection a α r ρ D f) D :=
    circle_reflection_extension hr hρ hD_open hD_connected hΔ_open hΔ_connected
      hC₀ hΓ₀ hD_reflect hΔ_reflect hf_cont hf_holo hf_maps hf_boundary
  have hEqExterior : Set.EqOn G (circleReflection a α r ρ D f) (circleExterior a r D) := by
    intro z hz
    calc
      G z = f z := hG_eq (Or.inl hz)
      _ = circleReflection a α r ρ D f z := by
        symm
        exact circleReflection_apply_of_mem_exterior_boundary (Or.inl hz)
  rcases circleExterior_nonempty_of_open_arc hr hD_open hC₀ with ⟨z₀, hz₀Ext⟩
  have hz₀D : z₀ ∈ D := (mem_circleExterior.mp hz₀Ext).1
  have heventually : G =ᶠ[nhds z₀] circleReflection a α r ρ D f := by
    -- The exterior slice is open, so the pointwise equality on that slice upgrades to a local
    -- eventual equality at any exterior point.
    filter_upwards [(isOpen_circleExterior hD_open).mem_nhds hz₀Ext] with z hz
    exact hEqExterior hz
  exact hG_holo.eqOn_of_preconnected_of_eventuallyEq
    hReflection_holo hD_connected.isPreconnected hz₀D heventually

/-- Helper for Exercise 6: once the boundary branch is known to be injective, the reflected map is
injective on the whole domain. -/
theorem circleReflection_injOn_domain_of_boundary_inj
    {a α : ℂ} {r ρ : ℝ} {D Δ : Set ℂ} {f : ℂ → ℂ}
    (hr : 0 < r) (hρ : 0 < ρ)
    (hD_reflect :
      circleExterior a r D = inversion a r '' circleInterior a r D)
    (hΔ_reflect :
      circleExterior α ρ Δ = inversion α ρ '' circleInterior α ρ Δ)
    (hf_maps :
      Set.MapsTo f (circleExterior a r D) (circleExterior α ρ Δ))
    (e₀ : HolomorphicIsomorph (circleExterior a r D) (circleExterior α ρ Δ))
    (he₀ : Set.EqOn e₀ f (circleExterior a r D))
    (hf_boundary_maps :
      Set.MapsTo f (circleBoundaryArc a r D) (circleBoundaryArc α ρ Δ))
    (hboundary_inj :
      Set.InjOn (circleReflection a α r ρ D f) (circleBoundaryArc a r D)) :
    Set.InjOn (circleReflection a α r ρ D f) D := by
  let g : ℂ → ℂ := circleReflection a α r ρ D f
  have hExterior_inj : Set.InjOn g (circleExterior a r D) := by
    -- On the exterior branch, `g` agrees with the given holomorphic isomorphism `e₀`.
    have he₀_inj : Set.InjOn (e₀ : ℂ → ℂ) (circleExterior a r D) := by
      simpa [e₀.source_eq] using (e₀ : OpenPartialHomeomorph ℂ ℂ).injOn
    intro z hz w hw hEq
    apply he₀_inj hz hw
    calc
      e₀ z = f z := he₀ hz
      _ = g z := by
        symm
        simpa [g] using
          (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
            (ρ := ρ) (D := D) (f := f) (z := z) (Or.inl hz))
      _ = g w := hEq
      _ = f w := by
        simpa [g] using
          (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
            (ρ := ρ) (D := D) (f := f) (z := w) (Or.inl hw))
      _ = e₀ w := (he₀ hw).symm
  have hInterior_maps :
      Set.MapsTo g (circleInterior a r D) (circleInterior α ρ Δ) :=
    circleReflection_mapsTo_interior hρ hD_reflect hΔ_reflect hf_maps
  intro z hzD w hwD hEq
  have hEqg : g z = g w := by
    simpa [g] using hEq
  rcases mem_circleExterior_or_mem_circleBoundaryArc_or_mem_circleInterior hzD with
    hz_ext | hz_boundary | hz_int
  · rcases mem_circleExterior_or_mem_circleBoundaryArc_or_mem_circleInterior hwD with
      hw_ext | hw_boundary | hw_int
    · exact hExterior_inj hz_ext hw_ext hEq
    · exfalso
      have hgz_eq : g z = f z := by
        simpa [g] using
          (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
            (ρ := ρ) (D := D) (f := f) (z := z) (Or.inl hz_ext))
      have hgz_ext : g z ∈ circleExterior α ρ Δ := by
        rw [hgz_eq]
        exact hf_maps hz_ext
      have hgw_boundary : g w ∈ circleBoundaryArc α ρ Δ := by
        have hgw_eq : g w = f w := by
          simpa [g] using
            (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
              (ρ := ρ) (D := D) (f := f) (z := w) (Or.inr hw_boundary))
        rw [hgw_eq]
        exact hf_boundary_maps hw_boundary
      rw [mem_circleExterior] at hgz_ext
      rcases mem_circleBoundaryArc.mp hgw_boundary with ⟨_, hgw_sphere⟩
      have hgw_norm : ‖g w - α‖ = ρ := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hgw_sphere
      have hgw_gt : ρ < ‖g w - α‖ := by
        rw [← hEqg]
        exact hgz_ext.2
      exact (not_lt_of_ge hgw_norm.le) hgw_gt
    · exfalso
      have hgz_eq : g z = f z := by
        simpa [g] using
          (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
            (ρ := ρ) (D := D) (f := f) (z := z) (Or.inl hz_ext))
      have hgz_ext : g z ∈ circleExterior α ρ Δ := by
        rw [hgz_eq]
        exact hf_maps hz_ext
      have hgw_int : g w ∈ circleInterior α ρ Δ := hInterior_maps hw_int
      rw [mem_circleExterior] at hgz_ext
      rw [mem_circleInterior] at hgw_int
      have hgw_gt : ρ < ‖g w - α‖ := by
        rw [← hEqg]
        exact hgz_ext.2
      exact (not_lt_of_ge hgw_int.2.le) hgw_gt
  · rcases mem_circleExterior_or_mem_circleBoundaryArc_or_mem_circleInterior hwD with
      hw_ext | hw_boundary | hw_int
    · exfalso
      have hgz_boundary : g z ∈ circleBoundaryArc α ρ Δ := by
        have hgz_eq : g z = f z := by
          simpa [g] using
            (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
              (ρ := ρ) (D := D) (f := f) (z := z) (Or.inr hz_boundary))
        rw [hgz_eq]
        exact hf_boundary_maps hz_boundary
      have hgw_eq : g w = f w := by
        simpa [g] using
          (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
            (ρ := ρ) (D := D) (f := f) (z := w) (Or.inl hw_ext))
      have hgw_ext : g w ∈ circleExterior α ρ Δ := by
        rw [hgw_eq]
        exact hf_maps hw_ext
      rw [mem_circleExterior] at hgw_ext
      rcases mem_circleBoundaryArc.mp hgz_boundary with ⟨_, hgz_sphere⟩
      have hgz_norm : ‖g z - α‖ = ρ := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hgz_sphere
      have hgz_gt : ρ < ‖g z - α‖ := by
        rw [hEqg]
        exact hgw_ext.2
      exact (not_lt_of_ge hgz_norm.le) hgz_gt
    · exact hboundary_inj hz_boundary hw_boundary hEq
    · exfalso
      have hgz_boundary : g z ∈ circleBoundaryArc α ρ Δ := by
        have hgz_eq : g z = f z := by
          simpa [g] using
            (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
              (ρ := ρ) (D := D) (f := f) (z := z) (Or.inr hz_boundary))
        rw [hgz_eq]
        exact hf_boundary_maps hz_boundary
      have hgw_int : g w ∈ circleInterior α ρ Δ := hInterior_maps hw_int
      rw [mem_circleInterior] at hgw_int
      rcases mem_circleBoundaryArc.mp hgz_boundary with ⟨_, hgz_sphere⟩
      have hgz_norm : ‖g z - α‖ = ρ := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hgz_sphere
      have hgz_lt : ‖g z - α‖ < ρ := by
        rw [hEqg]
        exact hgw_int.2
      exact (ne_of_lt hgz_lt) hgz_norm
  · rcases mem_circleExterior_or_mem_circleBoundaryArc_or_mem_circleInterior hwD with
      hw_ext | hw_boundary | hw_int
    · exfalso
      have hgz_int : g z ∈ circleInterior α ρ Δ := hInterior_maps hz_int
      have hgw_eq : g w = f w := by
        simpa [g] using
          (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
            (ρ := ρ) (D := D) (f := f) (z := w) (Or.inl hw_ext))
      have hgw_ext : g w ∈ circleExterior α ρ Δ := by
        rw [hgw_eq]
        exact hf_maps hw_ext
      rw [mem_circleExterior] at hgw_ext
      rw [mem_circleInterior] at hgz_int
      have hgz_gt : ρ < ‖g z - α‖ := by
        rw [hEqg]
        exact hgw_ext.2
      exact (not_lt_of_ge hgz_int.2.le) hgz_gt
    · exfalso
      have hgz_int : g z ∈ circleInterior α ρ Δ := hInterior_maps hz_int
      have hgw_boundary : g w ∈ circleBoundaryArc α ρ Δ := by
        have hgw_eq : g w = f w := by
          simpa [g] using
            (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
              (ρ := ρ) (D := D) (f := f) (z := w) (Or.inr hw_boundary))
        rw [hgw_eq]
        exact hf_boundary_maps hw_boundary
      rw [mem_circleInterior] at hgz_int
      rcases mem_circleBoundaryArc.mp hgw_boundary with ⟨_, hgw_sphere⟩
      have hgw_norm : ‖g w - α‖ = ρ := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hgw_sphere
      have hgw_lt : ‖g w - α‖ < ρ := by
        rw [← hEqg]
        exact hgz_int.2
      exact (ne_of_lt hgw_lt) hgw_norm
    · have hz_not_mem :
          z ∉ circleExterior a r D ∪ circleBoundaryArc a r D :=
        not_mem_circleExterior_union_circleBoundaryArc_of_mem_circleInterior hz_int
      have hw_not_mem :
          w ∉ circleExterior a r D ∪ circleBoundaryArc a r D :=
        not_mem_circleExterior_union_circleBoundaryArc_of_mem_circleInterior hw_int
      have hz_pre_ext : inversion a r z ∈ circleExterior a r D :=
        inversion_mapsTo_circleExterior hD_reflect hz_int
      have hw_pre_ext : inversion a r w ∈ circleExterior a r D :=
        inversion_mapsTo_circleExterior hD_reflect hw_int
      have hpre_eq :
          g (inversion a r z) = g (inversion a r w) := by
        have hz_formula : g z = inversion α ρ (f (inversion a r z)) := by
          simpa [g] using
            (circleReflection_apply_of_not_mem_exterior_boundary (a := a) (α := α) (r := r)
              (ρ := ρ) (D := D) (f := f) (z := z) hz_not_mem)
        have hw_formula : g w = inversion α ρ (f (inversion a r w)) := by
          simpa [g] using
            (circleReflection_apply_of_not_mem_exterior_boundary (a := a) (α := α) (r := r)
              (ρ := ρ) (D := D) (f := f) (z := w) hw_not_mem)
        have hinv_eq :
            inversion α ρ (f (inversion a r z)) =
              inversion α ρ (f (inversion a r w)) := by
          calc
            inversion α ρ (f (inversion a r z)) = g z := hz_formula.symm
            _ = g w := hEq
            _ = inversion α ρ (f (inversion a r w)) := hw_formula
        have hvalue_eq : f (inversion a r z) = f (inversion a r w) :=
          (inversion_injective α hρ.ne') hinv_eq
        calc
          g (inversion a r z) = f (inversion a r z) := by
            simpa [g] using
              (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
                (ρ := ρ) (D := D) (f := f) (z := inversion a r z) (Or.inl hz_pre_ext))
          _ = f (inversion a r w) := hvalue_eq
          _ = g (inversion a r w) := by
            symm
            simpa [g] using
              (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
                (ρ := ρ) (D := D) (f := f) (z := inversion a r w) (Or.inl hw_pre_ext))
      have hinv_eq : inversion a r z = inversion a r w :=
        hExterior_inj hz_pre_ext hw_pre_ext hpre_eq
      exact (inversion_injective a hr.ne') hinv_eq

/-- Helper for Exercise 6: the reflected map is surjective onto the target once the exterior branch
and the boundary arc are already surjective. -/
theorem circleReflection_image_eq_target
    {a α : ℂ} {r ρ : ℝ} {D Δ : Set ℂ} {f : ℂ → ℂ}
    (hr : 0 < r) (hρ : 0 < ρ)
    (hD_reflect :
      circleExterior a r D = inversion a r '' circleInterior a r D)
    (hΔ_reflect :
      circleExterior α ρ Δ = inversion α ρ '' circleInterior α ρ Δ)
    (hf_maps :
      Set.MapsTo f (circleExterior a r D) (circleExterior α ρ Δ))
    (e₀ : HolomorphicIsomorph (circleExterior a r D) (circleExterior α ρ Δ))
    (he₀ : Set.EqOn e₀ f (circleExterior a r D))
    (hf_boundary_maps :
      Set.MapsTo f (circleBoundaryArc a r D) (circleBoundaryArc α ρ Δ))
    (hf_boundary_surj :
      Set.SurjOn f (circleBoundaryArc a r D) (circleBoundaryArc α ρ Δ)) :
    (circleReflection a α r ρ D f) '' D = Δ := by
  let g : ℂ → ℂ := circleReflection a α r ρ D f
  have hInterior_maps :
      Set.MapsTo g (circleInterior a r D) (circleInterior α ρ Δ) :=
    circleReflection_mapsTo_interior hρ hD_reflect hΔ_reflect hf_maps
  apply Set.Subset.antisymm
  · rintro y ⟨z, hzD, rfl⟩
    rcases mem_circleExterior_or_mem_circleBoundaryArc_or_mem_circleInterior hzD with
      hz_ext | hz_boundary | hz_int
    · have hgz_eq :
          circleReflection a α r ρ D f z = f z := by
        exact circleReflection_apply_of_mem_exterior_boundary (Or.inl hz_ext)
      rw [hgz_eq]
      exact (hf_maps hz_ext).1
    · have hboundary : g z ∈ circleBoundaryArc α ρ Δ := by
        have hgz_eq : g z = f z := by
          simpa [g] using
            (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
              (ρ := ρ) (D := D) (f := f) (z := z) (Or.inr hz_boundary))
        rw [hgz_eq]
        exact hf_boundary_maps hz_boundary
      exact (mem_circleBoundaryArc.mp hboundary).1
    · exact (mem_circleInterior.mp (hInterior_maps hz_int)).1
  · intro y hyΔ
    rcases mem_circleExterior_or_mem_circleBoundaryArc_or_mem_circleInterior hyΔ with
      hy_ext | hy_boundary | hy_int
    · have hy_target : y ∈ (e₀ : OpenPartialHomeomorph ℂ ℂ).target := by
        simpa [e₀.target_eq] using hy_ext
      refine ⟨((e₀ : OpenPartialHomeomorph ℂ ℂ).symm y), ?_, ?_⟩
      · have hx_ext :
            ((e₀ : OpenPartialHomeomorph ℂ ℂ).symm y) ∈ circleExterior a r D := by
          simpa [e₀.source_eq] using
            (e₀ : OpenPartialHomeomorph ℂ ℂ).map_target hy_target
        exact (mem_circleExterior.mp hx_ext).1
      · have hx_ext :
            ((e₀ : OpenPartialHomeomorph ℂ ℂ).symm y) ∈ circleExterior a r D := by
          simpa [e₀.source_eq] using
            (e₀ : OpenPartialHomeomorph ℂ ℂ).map_target hy_target
        calc
          g ((e₀ : OpenPartialHomeomorph ℂ ℂ).symm y)
              = f ((e₀ : OpenPartialHomeomorph ℂ ℂ).symm y) := by
                  simpa [g] using
                    (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
                      (ρ := ρ) (D := D) (f := f)
                      (z := ((e₀ : OpenPartialHomeomorph ℂ ℂ).symm y)) (Or.inl hx_ext))
          _ = e₀ ((e₀ : OpenPartialHomeomorph ℂ ℂ).symm y) := (he₀ hx_ext).symm
          _ = y := (e₀ : OpenPartialHomeomorph ℂ ℂ).right_inv hy_target
    · rcases hf_boundary_surj hy_boundary with ⟨x, hx_boundary, hxy⟩
      exact ⟨x, (mem_circleBoundaryArc.mp hx_boundary).1, by
        calc
          g x = f x := by
            simpa [g] using
              (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
                (ρ := ρ) (D := D) (f := f) (z := x) (Or.inr hx_boundary))
          _ = y := hxy⟩
    · have hy_ext : inversion α ρ y ∈ circleExterior α ρ Δ :=
        inversion_mapsTo_circleExterior hΔ_reflect hy_int
      have hy_ext_target : inversion α ρ y ∈ (e₀ : OpenPartialHomeomorph ℂ ℂ).target := by
        simpa [e₀.target_eq] using hy_ext
      let xPlus : ℂ := ((e₀ : OpenPartialHomeomorph ℂ ℂ).symm) (inversion α ρ y)
      have hxPlus_ext : xPlus ∈ circleExterior a r D := by
        simpa [xPlus, e₀.source_eq] using
          (e₀ : OpenPartialHomeomorph ℂ ℂ).map_target hy_ext_target
      let x : ℂ := inversion a r xPlus
      have hx_int : x ∈ circleInterior a r D := by
        simpa [x] using inversion_mapsTo_circleInterior hr hD_reflect hxPlus_ext
      have hx_not_mem :
          x ∉ circleExterior a r D ∪ circleBoundaryArc a r D :=
        not_mem_circleExterior_union_circleBoundaryArc_of_mem_circleInterior hx_int
      refine ⟨x, (mem_circleInterior.mp hx_int).1, ?_⟩
      have hx_inv : inversion a r x = xPlus := by
        simpa [x] using (inversion_involutive a hr.ne' xPlus)
      have hx_image : e₀ xPlus = inversion α ρ y := by
        simpa [xPlus] using (e₀ : OpenPartialHomeomorph ℂ ℂ).right_inv hy_ext_target
      calc
        g x = inversion α ρ (f (inversion a r x)) := by
          simpa [g] using
            (circleReflection_apply_of_not_mem_exterior_boundary (a := a) (α := α) (r := r)
              (ρ := ρ) (D := D) (f := f) (z := x) hx_not_mem)
        _ = inversion α ρ (f xPlus) := by rw [hx_inv]
        _ = inversion α ρ (e₀ xPlus) := by rw [(he₀ hxPlus_ext).symm]
        _ = inversion α ρ (inversion α ρ y) := by rw [hx_image]
        _ = y := by simpa using (inversion_involutive α hρ.ne' y)

/-- Helper for Exercise 6: an analytic injective map on an open set with image exactly `Δ`
packages into the chapter's `HolomorphicIsomorph` owner. -/
theorem isHolomorphicIsomorphOn_of_analyticOnNhd_of_injOn_image_eq
    {D Δ : Set ℂ} {g : ℂ → ℂ}
    (hD_open : IsOpen D) (hΔ_open : IsOpen Δ)
    (hg_holo : AnalyticOnNhd ℂ g D)
    (hg_inj : Set.InjOn g D)
    (himage : g '' D = Δ) :
    g.IsHolomorphicIsomorphOn D Δ := by
  have hsurj : Set.SurjOn g D Δ := by
    intro y hy
    rw [← himage] at hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  have hmaps : Set.MapsTo g D Δ := by
    intro z hz
    rw [← himage]
    exact ⟨z, hz, rfl⟩
  have hmaps_inv : Set.MapsTo (Function.invFunOn g D) Δ D :=
    hsurj.mapsTo_invFunOn
  have hleft_inv : Set.LeftInvOn (Function.invFunOn g D) g D :=
    hg_inj.leftInvOn_invFunOn
  have hright_inv : Set.RightInvOn (Function.invFunOn g D) g Δ :=
    hsurj.rightInvOn_invFunOn
  have hInv_holo : AnalyticOnNhd ℂ (Function.invFunOn g D) Δ := by
    simpa [himage] using
      corollary_VI_1_extra_3_invFunOn_analyticOnNhd hg_holo hg_inj hD_open
  have hInv_cont : ContinuousOn (Function.invFunOn g D) Δ := hInv_holo.continuousOn
  refine ⟨?_, ?_⟩
  · exact ⟨{
      toFun := g
      invFun := Function.invFunOn g D
      source := D
      target := Δ
      map_source' := hmaps
      map_target' := hmaps_inv
      left_inv' := hleft_inv
      right_inv' := hright_inv
      open_source := hD_open
      open_target := hΔ_open
      continuousOn_toFun := hg_holo.continuousOn
      continuousOn_invFun := hInv_cont
    }, {
      source_eq := rfl
      target_eq := rfl
      analyticOn_toFun := hg_holo
      analyticOn_symm := hInv_holo
    }⟩
  · intro z hz
    rfl

/-- Helper for Exercise 6: near a source boundary point, the reflected extension cannot be
eventually constant because its exterior trace agrees with an injective biholomorphism. -/
theorem circleReflection_not_eventuallyConst_at_boundary_of_exterior_isomorphism
    {a α : ℂ} {r ρ : ℝ} {D Δ : Set ℂ} {f : ℂ → ℂ} (hr : 0 < r)
    (hD_open : IsOpen D)
    (e₀ : HolomorphicIsomorph (circleExterior a r D) (circleExterior α ρ Δ))
    (he₀ : Set.EqOn e₀ f (circleExterior a r D))
    {z : ℂ} (hz : z ∈ circleBoundaryArc a r D) :
    ¬ Filter.EventuallyConst (circleReflection a α r ρ D f) (nhds z) := by
  let g : ℂ → ℂ := circleReflection a α r ρ D f
  have hExterior_open : IsOpen (circleExterior a r D) := isOpen_circleExterior hD_open
  have he₀_inj : Set.InjOn (e₀ : ℂ → ℂ) (circleExterior a r D) := by
    simpa [e₀.source_eq] using (e₀ : OpenPartialHomeomorph ℂ ℂ).injOn
  intro hconst
  rcases hconst.eventuallyEq_const with ⟨c, hc⟩
  have hzD : z ∈ D := (mem_circleBoundaryArc.mp hz).1
  rcases Metric.mem_nhds_iff.mp (hD_open.mem_nhds hzD) with ⟨εD, hεD_pos, _hεD_subD⟩
  have hconst_set : {w : ℂ | g w = c} ∈ nhds z := by
    simpa using hc
  rcases Metric.mem_nhds_iff.mp hconst_set with ⟨εc, hεc_pos, hεc_sub⟩
  let ε : ℝ := min εD εc
  have hε_pos : 0 < ε := by
    dsimp [ε]
    exact lt_min hεD_pos hεc_pos
  rcases exists_mem_circleExterior_mem_ball_of_mem_circleBoundaryArc
      (a := a) (z := z) (r := r) (ε := ε / 2) hr (half_pos hε_pos) hD_open hz with
    ⟨w₁, hw₁_ext, hw₁_ball⟩
  have hw₁_eq : g w₁ = c := by
    apply hεc_sub
    have hw₁_lt_half : dist w₁ z < ε / 2 := by
      simpa [Metric.mem_ball] using hw₁_ball
    have hhalf_le : ε / 2 ≤ εc := by
      dsimp [ε]
      linarith [min_le_right εD εc]
    simpa [Metric.mem_ball, dist_comm] using lt_of_lt_of_le hw₁_lt_half hhalf_le
  rcases Metric.mem_nhds_iff.mp (hExterior_open.mem_nhds hw₁_ext) with ⟨δext, hδext_pos, hδext_sub⟩
  have hw₁_ball_nhds : Metric.ball z (ε / 2) ∈ nhds w₁ :=
    Metric.isOpen_ball.mem_nhds hw₁_ball
  rcases Metric.mem_nhds_iff.mp hw₁_ball_nhds with ⟨δball, hδball_pos, hδball_sub⟩
  let δ : ℝ := min δext δball
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min hδext_pos hδball_pos
  let w₂ : ℂ := w₁ + (((δ / 2 : ℝ) : ℂ))
  have hw₂_ball_w₁ : w₂ ∈ Metric.ball w₁ δ := by
    have hw₂_dist : dist w₂ w₁ = δ / 2 := by
      calc
        dist w₂ w₁ = ‖w₂ - w₁‖ := by rw [dist_eq_norm]
        _ = ‖(((δ / 2 : ℝ) : ℂ))‖ := by simp [w₂]
        _ = δ / 2 := by
          simp [Complex.norm_real, le_of_lt hδ_pos]
    have hw₂_lt : dist w₂ w₁ < δ := by
      rw [hw₂_dist]
      linarith
    simpa [Metric.mem_ball] using hw₂_lt
  have hw₂_ext : w₂ ∈ circleExterior a r D := by
    apply hδext_sub
    have hw₂_lt : dist w₂ w₁ < δ := by
      simpa [Metric.mem_ball] using hw₂_ball_w₁
    have hδ_le : δ ≤ δext := by
      dsimp [δ]
      exact min_le_left _ _
    simpa [Metric.mem_ball] using lt_of_lt_of_le hw₂_lt hδ_le
  have hw₂_ball : w₂ ∈ Metric.ball z (ε / 2) := by
    apply hδball_sub
    have hw₂_lt : dist w₂ w₁ < δ := by
      simpa [Metric.mem_ball] using hw₂_ball_w₁
    have hδ_le : δ ≤ δball := by
      dsimp [δ]
      exact min_le_right _ _
    simpa [Metric.mem_ball] using lt_of_lt_of_le hw₂_lt hδ_le
  have hw₂_eq : g w₂ = c := by
    apply hεc_sub
    have hw₂_lt_half : dist w₂ z < ε / 2 := by
      simpa [Metric.mem_ball] using hw₂_ball
    have hhalf_le : ε / 2 ≤ εc := by
      dsimp [ε]
      linarith [min_le_right εD εc]
    simpa [Metric.mem_ball, dist_comm] using lt_of_lt_of_le hw₂_lt_half hhalf_le
  have hw₁_value : e₀ w₁ = c := by
    calc
      e₀ w₁ = f w₁ := he₀ hw₁_ext
      _ = g w₁ := by
        symm
        simpa [g] using
          (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
            (ρ := ρ) (D := D) (f := f) (z := w₁) (Or.inl hw₁_ext))
      _ = c := hw₁_eq
  have hw₂_value : e₀ w₂ = c := by
    calc
      e₀ w₂ = f w₂ := he₀ hw₂_ext
      _ = g w₂ := by
        symm
        simpa [g] using
          (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
            (ρ := ρ) (D := D) (f := f) (z := w₂) (Or.inl hw₂_ext))
      _ = c := hw₂_eq
  have hw_eq : w₁ = w₂ := he₀_inj hw₁_ext hw₂_ext (hw₁_value.trans hw₂_value.symm)
  have hw_ne : w₁ ≠ w₂ := by
    intro hw
    have hzero : (((δ / 2 : ℝ) : ℂ)) = 0 := by
      have hsum : w₁ + (((δ / 2 : ℝ) : ℂ)) = w₁ + 0 := by
        simpa [w₂] using hw.symm
      exact add_left_cancel hsum
    have hhalf_ne : (((δ / 2 : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (ne_of_gt (half_pos hδ_pos))
    exact hhalf_ne hzero
  exact hw_ne hw_eq

/-- Helper for Exercise 6: under the exterior-isomorphism hypotheses, Proposition 4.2 supplies
injectivity of the reflected map on the boundary arc. -/
theorem circleReflection_injOn_boundaryArc_of_exterior_isomorphism
    {a α : ℂ} {r ρ : ℝ} {D Δ : Set ℂ} {f : ℂ → ℂ}
    (hr : 0 < r) (hρ : 0 < ρ)
    (hD_open : IsOpen D) (hD_connected : IsConnected D)
    (hΔ_open : IsOpen Δ) (hΔ_connected : IsConnected Δ)
    (hC₀ : IsOpenArcOnCircle a r (circleBoundaryArc a r D))
    (hΓ₀ : IsOpenArcOnCircle α ρ (circleBoundaryArc α ρ Δ))
    (hD_reflect :
      circleExterior a r D = inversion a r '' circleInterior a r D)
    (hΔ_reflect :
      circleExterior α ρ Δ = inversion α ρ '' circleInterior α ρ Δ)
    (hf_cont :
      ContinuousOn f (circleExterior a r D ∪ circleBoundaryArc a r D))
    (e₀ : HolomorphicIsomorph (circleExterior a r D) (circleExterior α ρ Δ))
    (he₀ : Set.EqOn e₀ f (circleExterior a r D))
    (hf_boundary_maps :
      Set.MapsTo f (circleBoundaryArc a r D) (circleBoundaryArc α ρ Δ)) :
    Set.InjOn (circleReflection a α r ρ D f) (circleBoundaryArc a r D) := by
  let g : ℂ → ℂ := circleReflection a α r ρ D f
  have hf_holo : AnalyticOnNhd ℂ f (circleExterior a r D) :=
    analyticOnNhd_of_eqOn_holomorphicIsomorph e₀ he₀
  have hf_maps : Set.MapsTo f (circleExterior a r D) (circleExterior α ρ Δ) :=
    mapsTo_target_of_eqOn_holomorphicIsomorph e₀ he₀
  have hg_holo : AnalyticOnNhd ℂ g D :=
    circle_reflection_extension hr hρ hD_open hD_connected hΔ_open hΔ_connected
      hC₀ hΓ₀ hD_reflect hΔ_reflect hf_cont hf_holo hf_maps hf_boundary_maps
  have he₀_inj : Set.InjOn (e₀ : ℂ → ℂ) (circleExterior a r D) := by
    -- The exterior branch is already a biholomorphism, hence injective on its source.
    simpa [e₀.source_eq] using (e₀ : OpenPartialHomeomorph ℂ ℂ).injOn
  intro z₁ hz₁ z₂ hz₂ hzEq
  by_contra hz_ne
  have hz₁D : z₁ ∈ D := (mem_circleBoundaryArc.mp hz₁).1
  have hz₂D : z₂ ∈ D := (mem_circleBoundaryArc.mp hz₂).1
  have hz₁_value : g z₁ = f z₁ := by
    simpa [g] using
      (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r) (ρ := ρ)
        (D := D) (f := f) (z := z₁) (Or.inr hz₁))
  have hz₂_value : g z₂ = f z₂ := by
    simpa [g] using
      (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r) (ρ := ρ)
        (D := D) (f := f) (z := z₂) (Or.inr hz₂))
  let c : ℂ := g z₁
  have hc_eq₂ : g z₂ = c := by
    simpa [c] using hzEq.symm
  have hc_boundary : c ∈ circleBoundaryArc α ρ Δ := by
    -- On the boundary arc, `g` agrees with `f`, so the common value lies on the target boundary
    -- arc.
    have hc_eq₁ : c = f z₁ := by
      simpa [c] using hz₁_value
    simpa [hc_eq₁] using hf_boundary_maps hz₁
  have hnot_const₁ :
      ¬ Filter.EventuallyConst g (nhds z₁) :=
    circleReflection_not_eventuallyConst_at_boundary_of_exterior_isomorphism hr hD_open e₀ he₀ hz₁
  have hnot_const₂ :
      ¬ Filter.EventuallyConst g (nhds z₂) :=
    circleReflection_not_eventuallyConst_at_boundary_of_exterior_isomorphism hr hD_open e₀ he₀ hz₂
  have horder₁_ne_top : analyticOrderAt (fun w ↦ g w - c) z₁ ≠ ⊤ := by
    -- Route correction: convert the "not eventually constant" statement into finiteness of the
    -- vanishing order of `g - c` at the first boundary point.
    intro htop
    apply hnot_const₁
    refine Filter.eventuallyConst_iff_exists_eventuallyEq.mpr ?_
    refine ⟨c, ?_⟩
    simpa [sub_eq_zero] using (analyticOrderAt_eq_top.mp htop)
  have horder₂_ne_top : analyticOrderAt (fun w ↦ g w - c) z₂ ≠ ⊤ := by
    -- The same finiteness argument applies at the second boundary point.
    intro htop
    apply hnot_const₂
    refine Filter.eventuallyConst_iff_exists_eventuallyEq.mpr ?_
    refine ⟨c, ?_⟩
    simpa [sub_eq_zero] using (analyticOrderAt_eq_top.mp htop)
  have horder₁_ne_zero : analyticOrderAt (fun w ↦ g w - c) z₁ ≠ 0 := by
    -- Since `g z₁ = c`, the shifted function vanishes at `z₁`, so its order is positive.
    rw [analyticOrderAt_ne_zero]
    refine ⟨(hg_holo z₁ hz₁D).sub analyticAt_const, ?_⟩
    simp [c]
  have horder₂_ne_zero : analyticOrderAt (fun w ↦ g w - c) z₂ ≠ 0 := by
    -- Since `g z₂ = c`, the shifted function also vanishes at the second boundary point.
    rw [analyticOrderAt_ne_zero]
    refine ⟨(hg_holo z₂ hz₂D).sub analyticAt_const, ?_⟩
    simp [c, hc_eq₂]
  let k₁ : ℕ := analyticOrderNatAt (fun w ↦ g w - c) z₁
  let k₂ : ℕ := analyticOrderNatAt (fun w ↦ g w - c) z₂
  have hk₁ : analyticOrderAt (fun w ↦ g w - c) z₁ = k₁ := by
    rw [← Nat.cast_analyticOrderNatAt horder₁_ne_top]
  have hk₂ : analyticOrderAt (fun w ↦ g w - c) z₂ = k₂ := by
    rw [← Nat.cast_analyticOrderNatAt horder₂_ne_top]
  have hk₁_pos : 0 < k₁ := by
    have hk₁_ne : k₁ ≠ 0 := by
      intro hk₁_zero
      exact horder₁_ne_zero <| by simpa [k₁, hk₁_zero] using hk₁
    omega
  have hk₂_pos : 0 < k₂ := by
    have hk₂_ne : k₂ ≠ 0 := by
      intro hk₂_zero
      exact horder₂_ne_zero <| by simpa [k₂, hk₂_zero] using hk₂
    omega
  obtain ⟨r₀₁, hr₀₁_pos, hr₀₁⟩ :=
    nearby_level_set_has_k_simple_roots (f := g) (z₀ := z₁) (a := c) (k := k₁) hk₁_pos hk₁
  obtain ⟨r₀₂, hr₀₂_pos, hr₀₂⟩ :=
    nearby_level_set_has_k_simple_roots (f := g) (z₀ := z₂) (a := c) (k := k₂) hk₂_pos hk₂
  obtain ⟨rD₁, hrD₁_pos, hrD₁_subset⟩ := Metric.mem_nhds_iff.mp (hD_open.mem_nhds hz₁D)
  obtain ⟨rD₂, hrD₂_pos, hrD₂_subset⟩ := Metric.mem_nhds_iff.mp (hD_open.mem_nhds hz₂D)
  have hdist_pos : 0 < dist z₁ z₂ := dist_pos.mpr hz_ne
  let r₀ : ℝ := min r₀₁ r₀₂
  let rD : ℝ := min rD₁ rD₂
  let s : ℝ := dist z₁ z₂ / 3
  let r' : ℝ := min rD s
  let rloc : ℝ := min r₀ r'
  have hs_pos : 0 < s := by
    dsimp [s]
    positivity
  have hr₀_pos : 0 < r₀ := by
    dsimp [r₀]
    exact lt_min hr₀₁_pos hr₀₂_pos
  have hr'_pos : 0 < r' := by
    dsimp [r']
    exact lt_min (by dsimp [rD]; exact lt_min hrD₁_pos hrD₂_pos) hs_pos
  have hrloc_pos : 0 < rloc := by
    dsimp [rloc]
    exact lt_min hr₀_pos hr'_pos
  have hrloc_le_r₀₁ : rloc ≤ r₀₁ := by
    exact le_trans (by dsimp [rloc]; exact min_le_left _ _) (by dsimp [r₀]; exact min_le_left _ _)
  have hrloc_le_r₀₂ : rloc ≤ r₀₂ := by
    exact le_trans (by dsimp [rloc]; exact min_le_left _ _) (by dsimp [r₀]; exact min_le_right _ _)
  have hrloc_le_rD₁ : rloc ≤ rD₁ := by
    exact le_trans
      (by dsimp [rloc]; exact min_le_right _ _)
      (le_trans (by dsimp [r']; exact min_le_left _ _) (by dsimp [rD]; exact min_le_left _ _))
  have hrloc_le_rD₂ : rloc ≤ rD₂ := by
    exact le_trans
      (by dsimp [rloc]; exact min_le_right _ _)
      (le_trans (by dsimp [r']; exact min_le_left _ _) (by dsimp [rD]; exact min_le_right _ _))
  have hrloc_le_s : rloc ≤ s := by
    exact le_trans (by dsimp [rloc]; exact min_le_right _ _) (by dsimp [r']; exact min_le_right _ _)
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := hr₀₁ rloc hrloc_pos hrloc_le_r₀₁
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := hr₀₂ rloc hrloc_pos hrloc_le_r₀₂
  let ε : ℝ := min δ₁ δ₂
  have hε_pos : 0 < ε := by
    dsimp [ε]
    exact lt_min hδ₁_pos hδ₂_pos
  obtain ⟨b, hb_ext, hb_ball⟩ :=
    exists_mem_circleExterior_mem_ball_of_mem_circleBoundaryArc
      (a := α) (z := c) (r := ρ) (ε := ε) hρ hε_pos hΔ_open hc_boundary
  have hb_dist₁ : ‖b - c‖ < δ₁ := by
    have hb_dist : dist b c < ε := by
      simpa [Metric.mem_ball] using hb_ball
    exact lt_of_lt_of_le (by simpa [dist_eq_norm] using hb_dist) (by dsimp [ε]; exact min_le_left _ _)
  have hb_dist₂ : ‖b - c‖ < δ₂ := by
    have hb_dist : dist b c < ε := by
      simpa [Metric.mem_ball] using hb_ball
    exact lt_of_lt_of_le (by simpa [dist_eq_norm] using hb_dist) (by dsimp [ε]; exact min_le_right _ _)
  have hb_ne_c : b ≠ c := by
    intro hb_eq
    have hc_ext : c ∈ circleExterior α ρ Δ := by
      simpa [hb_eq] using hb_ext
    rcases mem_circleBoundaryArc.mp hc_boundary with ⟨_, hc_sphere⟩
    rw [mem_circleExterior] at hc_ext
    have hc_norm : ‖c - α‖ = ρ := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hc_sphere
    exact (not_lt_of_ge hc_norm.le) hc_ext.2
  obtain ⟨hroot₁_count, _⟩ := hδ₁ b hb_dist₁ hb_ne_c
  obtain ⟨hroot₂_count, _⟩ := hδ₂ b hb_dist₂ hb_ne_c
  have hroot₁_nonempty :
      ({z : ℂ | z ∈ Metric.ball z₁ rloc ∧ g z = b} : Set ℂ).Nonempty := by
    apply Set.nonempty_of_encard_ne_zero
    rw [hroot₁_count]
    exact_mod_cast hk₁_pos.ne'
  have hroot₂_nonempty :
      ({z : ℂ | z ∈ Metric.ball z₂ rloc ∧ g z = b} : Set ℂ).Nonempty := by
    apply Set.nonempty_of_encard_ne_zero
    rw [hroot₂_count]
    exact_mod_cast hk₂_pos.ne'
  rcases hroot₁_nonempty with ⟨x₁, hx₁_ball, hx₁_value⟩
  rcases hroot₂_nonempty with ⟨x₂, hx₂_ball, hx₂_value⟩
  have hx₁D : x₁ ∈ D := by
    apply hrD₁_subset
    have hx₁_lt : dist x₁ z₁ < rloc := by
      simpa [Metric.mem_ball] using hx₁_ball
    have : dist x₁ z₁ < rD₁ := lt_of_lt_of_le hx₁_lt hrloc_le_rD₁
    simpa [Metric.mem_ball] using this
  have hx₂D : x₂ ∈ D := by
    apply hrD₂_subset
    have hx₂_lt : dist x₂ z₂ < rloc := by
      simpa [Metric.mem_ball] using hx₂_ball
    have : dist x₂ z₂ < rD₂ := lt_of_lt_of_le hx₂_lt hrloc_le_rD₂
    simpa [Metric.mem_ball] using this
  have hx₁_ext : x₁ ∈ circleExterior a r D :=
    circleReflection_preimage_targetExterior_subset_sourceExterior hρ hD_reflect hΔ_reflect hf_maps
      hf_boundary_maps hx₁D <| by simpa [g, hx₁_value] using hb_ext
  have hx₂_ext : x₂ ∈ circleExterior a r D :=
    circleReflection_preimage_targetExterior_subset_sourceExterior hρ hD_reflect hΔ_reflect hf_maps
      hf_boundary_maps hx₂D <| by simpa [g, hx₂_value] using hb_ext
  have hx₁_eval : e₀ x₁ = b := by
    -- On the exterior, the reflected map collapses back to the original biholomorphic branch.
    calc
      e₀ x₁ = f x₁ := he₀ hx₁_ext
      _ = g x₁ := by
        symm
        simpa [g] using
          (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r) (ρ := ρ)
            (D := D) (f := f) (z := x₁) (Or.inl hx₁_ext))
      _ = b := hx₁_value
  have hx₂_eval : e₀ x₂ = b := by
    calc
      e₀ x₂ = f x₂ := he₀ hx₂_ext
      _ = g x₂ := by
        symm
        simpa [g] using
          (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r) (ρ := ρ)
            (D := D) (f := f) (z := x₂) (Or.inl hx₂_ext))
      _ = b := hx₂_value
  have hx_eq : x₁ = x₂ := he₀_inj hx₁_ext hx₂_ext (hx₁_eval.trans hx₂_eval.symm)
  have hballs_disjoint : Disjoint (Metric.ball z₁ rloc) (Metric.ball z₂ rloc) := by
    -- The two root-counting balls were chosen much smaller than the distance between the boundary
    -- points.
    apply Metric.ball_disjoint_ball
    have hsum : rloc + rloc ≤ dist z₁ z₂ := by
      dsimp [s] at hrloc_le_s
      linarith [hrloc_le_s, hdist_pos]
    exact hsum
  have hx₁_in₂ : x₁ ∈ Metric.ball z₂ rloc := by
    simpa [hx_eq] using hx₂_ball
  exact (Set.disjoint_left.mp hballs_disjoint hx₁_ball hx₁_in₂).elim

/-- Exercise 6 (2): if the exterior map is already a holomorphic isomorphism onto the exterior
target and the boundary arc is mapped onto the target arc, then the inversion-defined reflected map
is biholomorphic from `D` onto `Δ`. -/
theorem circle_reflection_extension_isomorphism
    {a α : ℂ} {r ρ : ℝ} {D Δ : Set ℂ} {f : ℂ → ℂ}
    (hr : 0 < r) (hρ : 0 < ρ)
    (hD_open : IsOpen D) (hD_connected : IsConnected D)
    (hΔ_open : IsOpen Δ) (hΔ_connected : IsConnected Δ)
    (hC₀ : IsOpenArcOnCircle a r (circleBoundaryArc a r D))
    (hΓ₀ : IsOpenArcOnCircle α ρ (circleBoundaryArc α ρ Δ))
    (hD_reflect :
      circleExterior a r D = inversion a r '' circleInterior a r D)
    (hΔ_reflect :
      circleExterior α ρ Δ = inversion α ρ '' circleInterior α ρ Δ)
    (hf_cont :
      ContinuousOn f (circleExterior a r D ∪ circleBoundaryArc a r D))
    (e₀ : HolomorphicIsomorph (circleExterior a r D) (circleExterior α ρ Δ))
    (he₀ : Set.EqOn e₀ f (circleExterior a r D))
    (hf_boundary_maps :
      Set.MapsTo f (circleBoundaryArc a r D) (circleBoundaryArc α ρ Δ))
    (hf_boundary_surj :
      Set.SurjOn f (circleBoundaryArc a r D) (circleBoundaryArc α ρ Δ)) :
    (circleReflection a α r ρ D f).IsHolomorphicIsomorphOn D Δ := by
  -- Route correction: reduce the biholomorphic case to part (1) first, so the remaining blocker is
  -- exactly the source-faithful boundary-simplicity and inverse-extension stage.
  have hf_holo : AnalyticOnNhd ℂ f (circleExterior a r D) :=
    analyticOnNhd_of_eqOn_holomorphicIsomorph e₀ he₀
  have hf_maps : Set.MapsTo f (circleExterior a r D) (circleExterior α ρ Δ) :=
    mapsTo_target_of_eqOn_holomorphicIsomorph e₀ he₀
  have hf_boundary_closure :
      Set.MapsTo f (circleBoundaryArc a r D) (closure (circleExterior α ρ Δ)) := by
    intro z hz
    -- Boundary values are limits of exterior values because the source boundary arc is the
    -- frontier of the source exterior cut.
    exact image_mem_closure_circleExterior_of_boundary_point hD_open hf_cont hf_maps hz
  have hf_boundary_not_exterior :
      Set.MapsTo f (circleBoundaryArc a r D) (circleExterior α ρ Δ)ᶜ :=
    boundary_value_not_mem_target_exterior_of_exterior_isomorphism hD_open hf_cont e₀ he₀
  have hf_boundary_of_target_nonexterior :
      Set.MapsTo f (circleBoundaryArc a r D) Δ →
        Set.MapsTo f (circleBoundaryArc a r D) (circleExterior α ρ Δ)ᶜ →
        Set.MapsTo f (circleBoundaryArc a r D) (circleBoundaryArc α ρ Δ) := by
    intro hf_target hf_not_exterior z hz
    -- Route correction: the remaining issue is not the closure/frontier transport anymore; it is
    -- exactly the missing target-side membership and non-exteriority of the boundary values.
    exact mem_circleBoundaryArc_of_not_mem_circleExterior_of_mem_closure_circleExterior
      hΔ_open (hf_target hz) (hf_not_exterior hz) (hf_boundary_closure hz)
  have hf_boundary :
      Set.MapsTo f (circleBoundaryArc a r D) (circleBoundaryArc α ρ Δ) :=
    hf_boundary_maps
  -- The first half of the exercise now gives the analytic extension `g`.
  have hg_holo : AnalyticOnNhd ℂ (circleReflection a α r ρ D f) D :=
    circle_reflection_extension hr hρ hD_open hD_connected hΔ_open hΔ_connected
      hC₀ hΓ₀ hD_reflect hΔ_reflect hf_cont hf_holo hf_maps hf_boundary
  have hboundary_inj :
      Set.InjOn (circleReflection a α r ρ D f) (circleBoundaryArc a r D) :=
    circleReflection_injOn_boundaryArc_of_exterior_isomorphism hr hρ hD_open hD_connected
      hΔ_open hΔ_connected hC₀ hΓ₀ hD_reflect hΔ_reflect hf_cont e₀ he₀ hf_boundary_maps
  have hg_inj : Set.InjOn (circleReflection a α r ρ D f) D :=
    circleReflection_injOn_domain_of_boundary_inj hr hρ hD_reflect hΔ_reflect hf_maps
      e₀ he₀ hf_boundary_maps hboundary_inj
  have himage : (circleReflection a α r ρ D f) '' D = Δ :=
    circleReflection_image_eq_target hr hρ hD_reflect hΔ_reflect hf_maps e₀ he₀
      hf_boundary_maps hf_boundary_surj
  -- Package the analytic bijection and its analytic inverse into the chapter owner.
  exact isHolomorphicIsomorphOn_of_analyticOnNhd_of_injOn_image_eq
    hD_open hΔ_open hg_holo hg_inj himage

/-- Two holomorphic isomorphisms with the same source and target that realize the same function on
the source are unique up to `OpenPartialHomeomorph.EqOnSource`. -/
theorem eqOnSource_of_eqOn_holomorphicIsomorph
    {D Δ : Set ℂ} {g : ℂ → ℂ} {e e' : HolomorphicIsomorph D Δ}
    (he : Set.EqOn e g D) (he' : Set.EqOn e' g D) :
    OpenPartialHomeomorph.EqOnSource
      (e : OpenPartialHomeomorph ℂ ℂ) (e' : OpenPartialHomeomorph ℂ ℂ) := by
  refine ⟨?_, ?_⟩
  · simp [HolomorphicIsomorph.source_eq]
  · intro z hz
    have hzD : z ∈ D := by
      simpa [HolomorphicIsomorph.source_eq] using hz
    exact (he hzD).trans (he' hzD).symm
