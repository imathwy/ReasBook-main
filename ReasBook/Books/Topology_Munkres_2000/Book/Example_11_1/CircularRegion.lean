module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

public section

namespace EuclideanPlane

/-- A circular region in the Euclidean plane, specified by its center and positive radius. -/
structure CircularRegion where
  center : EuclideanSpace ℝ (Fin 2)
  radius : ℝ
  radius_pos : 0 < radius

namespace CircularRegion

/-- The set of points in a circular region. -/
@[expose]
def set (U : CircularRegion) : Set (EuclideanSpace ℝ (Fin 2)) :=
  Metric.ball U.center U.radius

/-- The point set of a circular region is its open metric ball. -/
theorem set_eq_ball (U : CircularRegion) :
    U.set = Metric.ball U.center U.radius := rfl

/-- Membership in a circular region is the metric-ball inequality. -/
theorem mem_set (U : CircularRegion) (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ U.set ↔ dist x U.center < U.radius := by
  -- Unfold the region once and use the metric-ball membership API.
  exact Metric.mem_ball

/-- Circular regions are strictly ordered by proper inclusion of their point sets. -/
instance instLT : LT CircularRegion where
  lt U V := U.set ⊂ V.set

/-- Proper comparison of circular regions is proper inclusion of their point sets. -/
theorem lt_iff (U V : CircularRegion) :
    U < V ↔ U.set ⊂ V.set := Iff.rfl

/-- Proper inclusion is a strict partial order on circular regions. -/
instance instIsStrictOrder : IsStrictOrder CircularRegion (· < ·) := by
  -- Package irreflexivity and transitivity of proper inclusion into the order class.
  let irreflInstance : Std.Irrefl (fun U V : CircularRegion ↦ U < V) :=
    ⟨fun U hU ↦ (ssubset_irrefl U.set) hU⟩
  let transInstance : IsTrans CircularRegion (fun U V ↦ U < V) :=
    ⟨fun U V W hUV hVW ↦ Set.ssubset_iff_subset_ne.mpr ⟨
      (Set.ssubset_iff_subset_ne.mp hUV).1.trans (Set.ssubset_iff_subset_ne.mp hVW).1,
      fun hUW ↦ (Set.ssubset_iff_subset_ne.mp hVW).2
        (Set.Subset.antisymm (Set.ssubset_iff_subset_ne.mp hVW).1
          (hUW ▸ (Set.ssubset_iff_subset_ne.mp hUV).1))⟩⟩
  exact @IsStrictOrder.mk CircularRegion (fun U V ↦ U < V) irreflInstance transInstance

/-- The circular regions centered at the origin. -/
def originCentered : Set CircularRegion :=
  {U | U.center = 0}

/-- A circular region is origin-centered exactly when its center is the origin. -/
theorem mem_originCentered (U : CircularRegion) :
    U ∈ originCentered ↔ U.center = 0 := by
  -- Membership is exactly the defining center equation.
  rfl

/-- The circular regions tangent from the right to the `y`-axis at the origin. -/
def rightTangent : Set CircularRegion :=
  {U | U.center = EuclideanSpace.single 0 U.radius}

/-- Membership in the right-tangent family is the positive-`x`-axis center formula. -/
theorem mem_rightTangent (U : CircularRegion) :
    U ∈ rightTangent ↔ U.center = EuclideanSpace.single 0 U.radius := by
  -- Membership is exactly the defining tangent-center equation.
  rfl

/-- Helper for Example 11.1: inclusion of positive-radius Euclidean balls is controlled by
 the distance between their centers and their radii. -/
lemma ball_subset_iff_dist_add_radius_le
    (c d : EuclideanSpace ℝ (Fin 2)) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Metric.ball c r ⊆ Metric.ball d s ↔ r + dist c d ≤ s := by
  -- The forward direction passes to closed balls and tests the far boundary point.
  constructor
  · intro hsubset
    have hclosed : Metric.closedBall c r ⊆ Metric.closedBall d s := by
      rw [← closure_ball c hr.ne', ← closure_ball d hs.ne']
      exact closure_mono hsubset
    by_cases hcd : c = d
    · subst d
      have hdiam := Metric.diam_mono hsubset Metric.isBounded_ball
      rw [Metric.diam_ball_eq c hr.le, Metric.diam_ball_eq c hs.le] at hdiam
      rw [dist_self, add_zero]
      linarith
    · let u : EuclideanSpace ℝ (Fin 2) := (‖c - d‖⁻¹ : ℝ) • (c - d)
      let z : EuclideanSpace ℝ (Fin 2) := c + r • u
      have hnorm : ‖c - d‖ ≠ 0 := by
        rw [norm_ne_zero_iff]
        exact sub_ne_zero.mpr hcd
      have hu : ‖u‖ = 1 := by
        simp only [u, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
          inv_mul_cancel₀ hnorm]
      have hzc : dist z c = r := by
        rw [dist_eq_norm]
        simp only [z, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu,
          mul_one]
      have hzmem : z ∈ Metric.closedBall c r := Metric.mem_closedBall.mpr hzc.le
      have hzd : dist z d = r + dist c d := by
        rw [dist_eq_norm, dist_eq_norm]
        have hscale : c + r • u - d = (1 + r * ‖c - d‖⁻¹) • (c - d) := by
          simp only [u]
          module
        rw [hscale, norm_smul, Real.norm_eq_abs]
        have hdist : 0 < ‖c - d‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hcd)
        rw [abs_of_pos]
        · field_simp
          ring
        · positivity
      have hzle : dist z d ≤ s := Metric.mem_closedBall.mp (hclosed hzmem)
      rwa [hzd] at hzle
  · intro hbound
    -- The reverse implication is the standard triangle-inequality inclusion estimate.
    exact Metric.ball_subset_ball' hbound

/-- Helper for Example 11.1: two circular regions with equal centers and radii are equal. -/
lemma eq_of_center_eq_radius_eq {U V : CircularRegion}
    (hcenter : U.center = V.center) (hradius : U.radius = V.radius) : U = V := by
  -- The positivity fields are propositions, so the data fields determine the structure.
  cases U
  cases V
  simp only at hcenter hradius
  subst_vars
  rfl

/-- Helper for Example 11.1: proper inclusion of circular regions strictly increases radius. -/
lemma radius_lt_of_lt {U V : CircularRegion} (hUV : U < V) : U.radius < V.radius := by
  -- Ball inclusion gives a weak radius bound; equality would identify the two regions.
  have hsubset : U.set ⊆ V.set := (Set.ssubset_iff_subset_ne.mp hUV).1
  have hbound : U.radius + dist U.center V.center ≤ V.radius :=
    (ball_subset_iff_dist_add_radius_le U.center V.center U.radius_pos V.radius_pos).mp hsubset
  have hdist_nonneg : 0 ≤ dist U.center V.center := dist_nonneg
  have hradius : U.radius ≤ V.radius := by
    linarith
  refine lt_of_le_of_ne hradius ?_
  intro heq
  have hdist : dist U.center V.center = 0 := by
    linarith
  have hcenter : U.center = V.center := dist_eq_zero.mp hdist
  have hUVeq : U = V := eq_of_center_eq_radius_eq hcenter heq
  subst V
  exact (ssubset_irrefl U.set) hUV

/-- Helper for Example 11.1: origin-centered regions are compared exactly by their radii. -/
lemma originCentered_lt_iff_radius_lt {U V : CircularRegion}
    (hU : U ∈ originCentered) (hV : V ∈ originCentered) :
    U < V ↔ U.radius < V.radius := by
  -- With equal centers, strict inclusion is exactly strict comparison of radii.
  constructor
  · exact radius_lt_of_lt
  · intro hradius
    have hcenter : U.center = V.center := by
      rw [(mem_originCentered U).mp hU, (mem_originCentered V).mp hV]
    refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · rw [set_eq_ball, set_eq_ball, hcenter]
      exact Metric.ball_subset_ball hradius.le
    · intro hset
      have hdiam : 2 * U.radius = 2 * V.radius := by
        calc
          2 * U.radius = Metric.diam U.set :=
            (Metric.diam_ball_eq U.center U.radius_pos.le).symm
          _ = Metric.diam V.set := congrArg Metric.diam hset
          _ = 2 * V.radius := Metric.diam_ball_eq V.center V.radius_pos.le
      linarith

/-- Helper for Example 11.1: right-tangent regions are compared exactly by their radii. -/
lemma rightTangent_lt_iff_radius_lt {U V : CircularRegion}
    (hU : U ∈ rightTangent) (hV : V ∈ rightTangent) :
    U < V ↔ U.radius < V.radius := by
  -- The tangent centers move by exactly the difference of the radii.
  constructor
  · exact radius_lt_of_lt
  · intro hradius
    have hdist : dist U.center V.center = V.radius - U.radius := by
      rw [(mem_rightTangent U).mp hU, (mem_rightTangent V).mp hV,
        PiLp.dist_single_same 2 (fun _ : Fin 2 ↦ ℝ) 0 U.radius V.radius, Real.dist_eq,
        abs_of_nonpos (by linarith)]
      linarith
    refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · rw [set_eq_ball, set_eq_ball]
      apply Metric.ball_subset_ball'
      rw [hdist]
      linarith
    · intro hset
      have hdiam : 2 * U.radius = 2 * V.radius := by
        calc
          2 * U.radius = Metric.diam U.set :=
            (Metric.diam_ball_eq U.center U.radius_pos.le).symm
          _ = Metric.diam V.set := congrArg Metric.diam hset
          _ = 2 * V.radius := Metric.diam_ball_eq V.center V.radius_pos.le
      linarith

/-- Helper for Example 11.1: a radius-ordered family with one member of each positive radius is a
 maximal chain of circular regions. -/
lemma isMaxChain_of_radiusOrder (F : Set CircularRegion)
    (hcompare : ∀ ⦃U V⦄, U ∈ F → V ∈ F → (U < V ↔ U.radius < V.radius))
    (hinjective : ∀ ⦃U V⦄, U ∈ F → V ∈ F → U.radius = V.radius → U = V)
    (hrepresent : ∀ U : CircularRegion, ∃ V ∈ F, V.radius = U.radius) :
    IsMaxChain (· < ·) F := by
  -- Radius trichotomy and radius injectivity give chainhood inside the family.
  constructor
  · intro U hU V hV hne
    rcases lt_trichotomy U.radius V.radius with hradius | hradius | hradius
    · exact Or.inl ((hcompare hU hV).mpr hradius)
    · exact (hne (hinjective hU hV hradius)).elim
    · exact Or.inr ((hcompare hV hU).mpr hradius)
  · intro G hG hFG
    -- Any added region is comparable with its same-radius representative, forcing equality.
    apply Set.Subset.antisymm hFG
    intro U hUG
    obtain ⟨V, hVF, hVr⟩ := hrepresent U
    have hVG : V ∈ G := hFG hVF
    by_contra hUF
    have hne : U ≠ V := by
      intro hUV
      exact hUF (hUV ▸ hVF)
    rcases hG hUG hVG hne with hUV | hVU
    · have hradius := radius_lt_of_lt hUV
      linarith
    · have hradius := radius_lt_of_lt hVU
      linarith

end CircularRegion

end EuclideanPlane
