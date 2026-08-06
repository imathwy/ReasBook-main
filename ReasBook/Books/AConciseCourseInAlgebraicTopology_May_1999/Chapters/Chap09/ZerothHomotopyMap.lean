import Mathlib.Topology.Homotopy.Equiv
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_1_5

open scoped unitInterval Topology Topology.Homotopy

noncomputable section

universe u v

variable {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]

/-- A continuous map sends path-connected points to path-connected points, so it induces a map on
`ZerothHomotopy`. -/
theorem zerothHomotopyMap_respects (g : C(A, B)) :
    ∀ ⦃a a' : A⦄, Joined a a' → Joined (g a) (g a')
  | _, _, haa' => ⟨haa'.somePath.map g.continuous⟩

/-- A continuous map induces a map on path components. -/
def zerothHomotopyMap (g : C(A, B)) : ZerothHomotopy A → ZerothHomotopy B :=
  Quotient.map g fun _ _ haa' ↦ zerothHomotopyMap_respects g haa'

/-- On a represented path component, `zerothHomotopyMap g` is represented by the image point. -/
@[simp] theorem zerothHomotopyMap_mk (g : C(A, B)) (a : A) :
    zerothHomotopyMap g ⟦a⟧ = ⟦g a⟧ :=
  rfl

/-- Homotopic continuous maps send each point to points in the same path component. -/
private theorem joined_of_homotopic_eval {g h : C(A, B)} (hgh : ContinuousMap.Homotopic g h) :
    ∀ a : A, Joined (g a) (h a) := by
  intro a
  refine ⟨Path.mk
    ((hgh.some.toContinuousMap).comp ((ContinuousMap.id I).prodMk (ContinuousMap.const I a)))
    (by
      change (hgh.some.toContinuousMap) (0, a) = g a
      exact hgh.some.map_zero_left a)
    (by
      change (hgh.some.toContinuousMap) (1, a) = h a
      exact hgh.some.map_one_left a)⟩

/-- Homotopic continuous maps induce the same map on path components. -/
theorem zerothHomotopyMap_eq_of_homotopic {g h : C(A, B)} (hgh : ContinuousMap.Homotopic g h) :
    zerothHomotopyMap g = zerothHomotopyMap h := by
  funext q
  refine Quotient.inductionOn q ?_
  intro a
  exact Quotient.sound (joined_of_homotopic_eval hgh a)

/-- A homotopy equivalence induces an equivalence on path components. -/
noncomputable def zerothHomotopyEquivOfHomotopyEquiv (e : ContinuousMap.HomotopyEquiv A B) :
    ZerothHomotopy A ≃ ZerothHomotopy B where
  toFun := zerothHomotopyMap e.toFun
  invFun := zerothHomotopyMap e.symm.toFun
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro a
    exact Quotient.sound (joined_of_homotopic_eval e.left_inv a)
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro b
    exact Quotient.sound (joined_of_homotopic_eval e.right_inv b)

/-- Applying `zerothHomotopyEquivOfHomotopyEquiv e` amounts to applying the induced map on path
components of the forward map of `e`. -/
@[simp] theorem zerothHomotopyEquivOfHomotopyEquiv_apply
    (e : ContinuousMap.HomotopyEquiv A B) (a : ZerothHomotopy A) :
    zerothHomotopyEquivOfHomotopyEquiv e a = zerothHomotopyMap e.toFun a :=
  rfl

end
