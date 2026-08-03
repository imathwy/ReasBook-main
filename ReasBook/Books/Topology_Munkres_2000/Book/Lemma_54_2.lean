module

public import Topology_Munkres_2000.Book.Definition_54_1.Lifting
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.UnitInterval

open Set

public section

universe u v

/-- Helper for Lemma 54.2: the vertical edge of the unit square at first coordinate `s`. -/
private def unitSquareVerticalEdge (s : unitInterval) :
    C(unitInterval, unitInterval × unitInterval) :=
  (ContinuousMap.const unitInterval s).prodMk (ContinuousMap.id unitInterval)

/-- Helper for Lemma 54.2: evaluation of the vertical-edge inclusion. -/
private lemma unitSquareVerticalEdge_apply (s t : unitInterval) :
    unitSquareVerticalEdge s t = (s, t) := by
  -- Unfolding only this small interface exposes the two coordinates.
  rfl

/-- Helper for Lemma 54.2: a lifted vertical edge is the canonical path lift when
its initial value is prescribed. -/
private lemma verticalEdgeLift_eq_liftPath {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {p : E → B} (hp : IsCoveringMap p)
    (F : C(unitInterval × unitInterval, B))
    (F_lift : C(unitInterval × unitInterval, E)) (s : unitInterval) (e : E)
    (hstart : (F.comp (unitSquareVerticalEdge s)) 0 = p e)
    (hlift : ContinuousMap.IsLift p F F_lift)
    (hzero : (F_lift.comp (unitSquareVerticalEdge s)) 0 = e) :
    F_lift.comp (unitSquareVerticalEdge s) =
      hp.liftPath (F.comp (unitSquareVerticalEdge s)) e hstart := by
  -- Restriction preserves the lifting equation, so path-lift uniqueness applies.
  have edgeLift := hlift.comp (unitSquareVerticalEdge s)
  rw [ContinuousMap.isLift_iff] at edgeLift
  exact (hp.eq_liftPath_iff' hstart).mpr ⟨edgeLift, hzero⟩

/-- Helper for Lemma 54.2: a lifted vertical edge is constant whenever its
projection to the base is constant. -/
private lemma liftConstOnVerticalEdge {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {p : E → B} (hp : IsCoveringMap p)
    (F : C(unitInterval × unitInterval, B))
    (F_lift : C(unitInterval × unitInterval, E))
    (hlift : ContinuousMap.IsLift p F F_lift) (s : unitInterval)
    (hedge : ∀ t, F (s, t) = F (s, 0)) :
    ∀ t, F_lift (s, t) = F_lift (s, 0) := by
  let liftedEdge := F_lift.comp (unitSquareVerticalEdge s)
  -- The given base-edge equality makes the projection of `liftedEdge` constant.
  have projectionConstant : ∀ t t', p (liftedEdge t) = p (liftedEdge t') := by
    intro t t'
    calc
      p (liftedEdge t) = F (s, t) := by
        simpa only [liftedEdge, ContinuousMap.comp_apply, unitSquareVerticalEdge_apply]
          using hlift.apply (s, t)
      _ = F (s, 0) := hedge t
      _ = F (s, t') := (hedge t').symm
      _ = p (liftedEdge t') := by
        simpa only [liftedEdge, ContinuousMap.comp_apply, unitSquareVerticalEdge_apply]
          using (hlift.apply (s, t')).symm
  -- A lift into a covering fiber is constant on the connected unit interval.
  intro t
  simpa only [liftedEdge, ContinuousMap.comp_apply, unitSquareVerticalEdge_apply] using
    hp.const_of_comp liftedEdge.continuous projectionConstant t 0

/-- Lemma 54.2 (1). A map from the unit square lifts uniquely through a covering map
after the value of the lift at `(0, 0)` is prescribed. -/
theorem existsUnique_unitSquare_lift {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {p : E → B} (hp : IsCoveringMap p)
    (F : C(unitInterval × unitInterval, B)) (e₀ : E) (he₀ : p e₀ = F (0, 0)) :
    ∃! F_lift : C(unitInterval × unitInterval, E),
      F_lift (0, 0) = e₀ ∧ ContinuousMap.IsLift p F F_lift := by
  -- First lift the left edge from the prescribed point.
  let leftPath := F.comp (unitSquareVerticalEdge 0)
  have leftPathStart : leftPath 0 = p e₀ := by
    simpa only [leftPath, ContinuousMap.comp_apply, unitSquareVerticalEdge_apply] using he₀.symm
  let leftLift := hp.liftPath leftPath e₀ leftPathStart
  have initialEdgeCompatibility : ∀ t, F (0, t) = p (leftLift t) := by
    intro t
    simpa only [leftPath, leftLift, ContinuousMap.comp_apply, Function.comp_apply,
      unitSquareVerticalEdge_apply]
      using (congrFun (hp.liftPath_lifts leftPath e₀ leftPathStart) t).symm
  -- Extend that edge lift across the square by the homotopy lifting property.
  let squareLift := hp.liftHomotopy F leftLift initialEdgeCompatibility
  refine ⟨squareLift, ?_, ?_⟩
  · constructor
    · calc
        squareLift (0, 0) = leftLift 0 :=
          hp.liftHomotopy_zero F leftLift initialEdgeCompatibility 0
        _ = e₀ := hp.liftPath_zero leftPath e₀ leftPathStart
    · exact ContinuousMap.isLift_iff.mpr
        (hp.liftHomotopy_lifts F leftLift initialEdgeCompatibility)
  · intro competingLift hcompeting
    rcases hcompeting with ⟨hcompetingZero, hcompetingLift⟩
    -- The competing lift agrees with the canonical lift along the entire left edge.
    have competingEdgeZero :
        (competingLift.comp (unitSquareVerticalEdge 0)) 0 = e₀ := by
      simpa only [ContinuousMap.comp_apply, unitSquareVerticalEdge_apply] using hcompetingZero
    have competingEdge : competingLift.comp (unitSquareVerticalEdge 0) = leftLift := by
      exact verticalEdgeLift_eq_liftPath hp F competingLift 0 e₀ leftPathStart
        hcompetingLift competingEdgeZero
    have competingInitialEdge : ∀ t, competingLift (0, t) = leftLift t := by
      intro t
      simpa only [ContinuousMap.comp_apply, unitSquareVerticalEdge_apply] using
        DFunLike.congr_fun competingEdge t
    -- Homotopy-lift uniqueness now promotes edge agreement to square agreement.
    rw [ContinuousMap.isLift_iff] at hcompetingLift
    exact (hp.eq_liftHomotopy_iff' initialEdgeCompatibility competingLift).mpr
      ⟨hcompetingLift, competingInitialEdge⟩

/-- Lemma 54.2 (2). If a map of the unit square is constant on each vertical
endpoint edge, then every lift with prescribed value at `(0, 0)` is also constant
on those edges, and hence is a path homotopy. -/
theorem unitSquare_lift_isPathHomotopy {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {p : E → B} (hp : IsCoveringMap p)
    (F : C(unitInterval × unitInterval, B)) (F_lift : C(unitInterval × unitInterval, E))
    (hlift : ContinuousMap.IsLift p F F_lift)
    (hleft : ∀ t, F (0, t) = F (0, 0)) (hright : ∀ t, F (1, t) = F (1, 0)) :
    (∀ t, F_lift (0, t) = F_lift (0, 0)) ∧
      ∀ t, F_lift (1, t) = F_lift (1, 0) := by
  -- Apply the connected-fiber argument independently to the two endpoint edges.
  constructor
  · exact liftConstOnVerticalEdge hp F F_lift hlift 0 hleft
  · exact liftConstOnVerticalEdge hp F F_lift hlift 1 hright
