module

public import Mathlib.Topology.Homotopy.Basic

public section

universe u v

namespace ContinuousMap.Homotopic

/-- The setoid on continuous maps whose equivalence relation is ordinary homotopy. -/
protected def setoid (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] :
    Setoid C(X, Y) :=
  ⟨Homotopic, Homotopic.equivalence⟩

/-- The type of ordinary homotopy classes of continuous maps from `X` to `Y`. -/
protected def Quotient (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] :
    Type (max u v) :=
  _root_.Quotient (Homotopic.setoid X Y)

namespace Quotient

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The ordinary homotopy class represented by a continuous map. -/
def mk (f : C(X, Y)) : Homotopic.Quotient X Y :=
  _root_.Quotient.mk (Homotopic.setoid X Y) f

/-- Every ordinary homotopy class has a continuous-map representative. -/
theorem mk_surjective :
    Function.Surjective (mk : C(X, Y) → Homotopic.Quotient X Y) :=
  _root_.Quotient.mk_surjective

/-- Equal represented ordinary homotopy classes have homotopic representatives. -/
theorem exact {f g : C(X, Y)} (h : mk f = mk g) : Homotopic f g :=
  _root_.Quotient.exact h

/-- Two represented ordinary homotopy classes are equal exactly when their maps are homotopic. -/
theorem eq {f g : C(X, Y)} : mk f = mk g ↔ Homotopic f g :=
  _root_.Quotient.eq

/-- To prove a proposition about an ordinary homotopy class, it suffices to prove it for classes
represented by continuous maps. -/
@[induction_eliminator]
protected theorem ind {motive : Homotopic.Quotient X Y → Prop}
    (h : (f : C(X, Y)) → motive (mk f)) (q : Homotopic.Quotient X Y) : motive q :=
  Quot.ind h q

end Quotient

end ContinuousMap.Homotopic
