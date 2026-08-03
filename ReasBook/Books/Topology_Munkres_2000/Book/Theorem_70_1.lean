module

public import Topology_Munkres_2000.Book.Theorem_59_1
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import all Topology_Munkres_2000.Book.Theorem_70_1.FiniteSubdivision
import Topology_Munkres_2000.Book.Theorem_70_1.HomotopyGrid
import all Topology_Munkres_2000.Book.Lemma_55_1.Inclusions

public section

universe u v

open CategoryTheory

namespace FiniteCoveredSubdivision

/-- Helper for Theorem 70.1: a monotone parameter map transports every edge
of a recursive covered subdivision. -/
private def Subdivision.map {P : Type u} {Q : Type v} {K : Type*}
    [LinearOrder P] [LinearOrder Q]
    {Covered : K → P → P → Prop} {Covered' : K → Q → Q → Prop}
    {a b : P} (D : Subdivision Covered a b) (f : P → Q)
    (hf : Monotone f)
    (hcovered : ∀ {k s t}, Covered k s t → Covered' k (f s) (f t)) :
    Subdivision Covered' (f a) (f b) :=
  match D with
  | .single side covered => .single side (hcovered covered)
  | .cons side c left_le right_le covered tail =>
      .cons side (f c) (hf left_le) (hf right_le) (hcovered covered)
        (tail.map f hf hcovered)

/-- Helper for Theorem 70.1: mapped subdivisions preserve their value when
the transported edge weights agree with the original weights. -/
private lemma Subdivision.value_map {P : Type u} {Q : Type v} {K G : Type*}
    [LinearOrder P] [LinearOrder Q] [Group G]
    {Covered : K → P → P → Prop} {Covered' : K → Q → Q → Prop}
    (weight : K → P → P → G) (weight' : K → Q → Q → G)
    {a b : P} (D : Subdivision Covered a b) (f : P → Q)
    (hf : Monotone f)
    (hcovered : ∀ {k s t}, Covered k s t → Covered' k (f s) (f t))
    (hweight : ∀ {k s t} (_ : Covered k s t),
      weight' k (f s) (f t) = weight k s t) :
    (D.map f hf hcovered).value weight' = D.value weight := by
  -- Follow the recursive subdivision and rewrite exactly one edge per step.
  induction D with
  | single side covered =>
      exact hweight covered
  | cons side c left_le right_le covered tail ih =>
      simp only [Subdivision.map, Subdivision.value]
      rw [ih, hweight covered]

/-- Helper for Theorem 70.1: concatenate two recursive subdivisions sharing
their middle endpoint. -/
private def Subdivision.append {P : Type u} {K : Type v} [LinearOrder P]
    {Covered : K → P → P → Prop} {a b c : P}
    (D₁ : Subdivision Covered a b) (D₂ : Subdivision Covered b c)
    (hab : a ≤ b) (hbc : b ≤ c) : Subdivision Covered a c :=
  match D₁ with
  | .single side covered => .cons side b hab hbc covered D₂
  | .cons side d left_le right_le covered tail =>
      .cons side d left_le (right_le.trans hbc) covered
        (tail.append D₂ right_le hbc)

/-- Helper for Theorem 70.1: concatenating recursive subdivisions multiplies
their values in reverse path order. -/
private lemma Subdivision.value_append {P : Type u} {K : Type v} {G : Type*}
    [LinearOrder P] [Group G] {Covered : K → P → P → Prop}
    (weight : K → P → P → G) {a b c : P}
    (D₁ : Subdivision Covered a b) (D₂ : Subdivision Covered b c)
    (hab : a ≤ b) (hbc : b ≤ c) :
    (D₁.append D₂ hab hbc).value weight =
      D₂.value weight * D₁.value weight := by
  -- Peel edges from the first subdivision until the second becomes its tail.
  induction D₁ with
  | single side covered =>
      rfl
  | cons side d left_le right_le covered tail ih =>
      simp only [Subdivision.append, Subdivision.value]
      rw [ih, mul_assoc]

end FiniteCoveredSubdivision

/-- Helper for Theorem 70.1: an endpoint equality determines a constant path. -/
private def pathOfEq {X : Type u} [TopologicalSpace X] {x y : X} (h : x = y) :
    Path x y :=
  (Path.refl x).cast rfl h.symm

/-- Helper for Theorem 70.1: closing an identity arrow with a connector gives the
identity loop at the chosen base object. -/
private lemma basedLoop_id {C : Type u} [Groupoid.{v} C] (b : C)
    (q : ∀ x : C, b ⟶ x) (x : C) :
    End.of (q x ≫ 𝟙 x ≫ Groupoid.inv (q x)) = (1 : End b) := by
  -- Remove the identity arrow, then cancel the connector with its inverse.
  simp

/-- Helper for Theorem 70.1: connector-closed arrows turn categorical composition
into multiplication in the vertex group. -/
private lemma basedLoop_comp {C : Type u} [Groupoid.{v} C] (b : C)
    (q : ∀ x : C, b ⟶ x) {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    End.of (q x ≫ (f ≫ g) ≫ Groupoid.inv (q z)) =
      End.of (q y ≫ g ≫ Groupoid.inv (q z)) *
        End.of (q x ≫ f ≫ Groupoid.inv (q y)) := by
  -- Reassociate the product until the middle connector pair is adjacent.
  simp [End.mul_def, Category.assoc]

/-- Helper for Theorem 70.1: the connector construction respects identity arrows
after applying a vertex-group homomorphism. -/
private lemma basedPathFunctor_map_id {C : Type u} [Groupoid.{v} C]
    {H : Type*} [Group H] (b : C) (q : ∀ x : C, b ⟶ x)
    (k : End b →* H) (x : C) :
    k (End.of (q x ≫ 𝟙 x ≫ Groupoid.inv (q x))) =
      𝟙 (CategoryTheory.SingleObj.star H) := by
  -- The closed identity arrow is the unit in the vertex group.
  rw [basedLoop_id]
  exact k.map_one

/-- Helper for Theorem 70.1: the connector construction respects composition
after applying a vertex-group homomorphism. -/
private lemma basedPathFunctor_map_comp {C : Type u} [Groupoid.{v} C]
    {H : Type*} [Group H] (b : C) (q : ∀ x : C, b ⟶ x)
    (k : End b →* H) {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    k (End.of (q x ≫ (f ≫ g) ≫ Groupoid.inv (q z))) =
      k (End.of (q y ≫ g ≫ Groupoid.inv (q z))) *
        k (End.of (q x ≫ f ≫ Groupoid.inv (q y))) := by
  -- Apply the vertex-group homomorphism to the connector cancellation formula.
  rw [basedLoop_comp, map_mul]

/-- Helper for Theorem 70.1: a homomorphism from one vertex group extends,
using chosen connectors, to a functor into the one-object groupoid. -/
private noncomputable def basedPathFunctor {C : Type u} [Groupoid.{v} C]
    {H : Type*} [Group H] (b : C) (q : ∀ x : C, b ⟶ x)
    (k : End b →* H) : C ⥤ CategoryTheory.SingleObj H :=
  { obj := fun _ ↦ CategoryTheory.SingleObj.star H
    map := fun f ↦ k (End.of (q _ ≫ f ≫ Groupoid.inv (q _)))
    map_id := basedPathFunctor_map_id b q k
    map_comp := basedPathFunctor_map_comp b q k }

/-- Helper for Theorem 70.1: when the connector at the base is the identity,
the connector functor recovers the prescribed homomorphism on every based loop. -/
private lemma basedPathFunctor_map_at_base {C : Type u} [Groupoid.{v} C]
    {H : Type*} [Group H] (b : C) (q : ∀ x : C, b ⟶ x)
    (k : End b →* H) (hq : q b = 𝟙 b) (f : End b) :
    (basedPathFunctor b q k).map f = k f := by
  -- Unfold the map and remove the two identity connectors around the loop.
  simp only [basedPathFunctor]
  rw [hq]
  simp

/-- Helper for Theorem 70.1: the distinguished connector inside `U ∩ V` is
constant at the basepoint and otherwise is supplied by path connectedness. -/
private noncomputable def intersectionConnector {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace (U ∩ V : Set X)]
    (x : (U ∩ V : Set X)) : Path (⟨x₀, hx₀⟩ : (U ∩ V : Set X)) x :=
  @dite (Path (⟨x₀, hx₀⟩ : (U ∩ V : Set X)) x)
    (x = ⟨x₀, hx₀⟩) (Classical.propDecidable _)
    (fun hbase ↦ pathOfEq hbase.symm)
    (fun _ ↦ PathConnectedSpace.somePath ⟨x₀, hx₀⟩ x)

/-- Helper for Theorem 70.1: the connector in `U` uses the distinguished
intersection connector whenever its endpoint also belongs to `V`. -/
private noncomputable def leftConnector {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace (U ∩ V : Set X)]
    (x : U) : Path (⟨x₀, hx₀.1⟩ : U) x :=
  @dite (Path (⟨x₀, hx₀.1⟩ : U) x)
    (x = ⟨x₀, hx₀.1⟩) (Classical.propDecidable _)
    (fun hbase ↦ pathOfEq hbase.symm)
    (fun _ ↦
      @dite (Path (⟨x₀, hx₀.1⟩ : U) x) (x.1 ∈ V)
        (Classical.propDecidable _)
        (fun hxV ↦
          (PathConnectedSpace.somePath
            (⟨x₀, hx₀⟩ : (U ∩ V : Set X)) ⟨x.1, x.2, hxV⟩).map
              (ContinuousMap.inclusion
                (show U ∩ V ⊆ U from Set.inter_subset_left)).continuous)
        (fun _ ↦ PathConnectedSpace.somePath ⟨x₀, hx₀.1⟩ x))

/-- Helper for Theorem 70.1: the connector in `V` uses the distinguished
intersection connector whenever its endpoint also belongs to `U`. -/
private noncomputable def rightConnector {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace V] [PathConnectedSpace (U ∩ V : Set X)]
    (x : V) : Path (⟨x₀, hx₀.2⟩ : V) x :=
  @dite (Path (⟨x₀, hx₀.2⟩ : V) x)
    (x = ⟨x₀, hx₀.2⟩) (Classical.propDecidable _)
    (fun hbase ↦ pathOfEq hbase.symm)
    (fun _ ↦
      @dite (Path (⟨x₀, hx₀.2⟩ : V) x) (x.1 ∈ U)
        (Classical.propDecidable _)
        (fun hxU ↦
          (PathConnectedSpace.somePath
            (⟨x₀, hx₀⟩ : (U ∩ V : Set X)) ⟨x.1, hxU, x.2⟩).map
              (ContinuousMap.inclusion
                (show U ∩ V ⊆ V from Set.inter_subset_right)).continuous)
        (fun _ ↦ PathConnectedSpace.somePath ⟨x₀, hx₀.2⟩ x))

/-- Helper for Theorem 70.1: at an intersection point, the connector in `U`
is the image of the common intersection connector. -/
private lemma leftConnector_intersection {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace (U ∩ V : Set X)]
    (x : (U ∩ V : Set X)) :
    leftConnector U V x₀ hx₀ ⟨x.1, x.2.1⟩ =
      (intersectionConnector U V x₀ hx₀ x).map
        (ContinuousMap.inclusion
          (show U ∩ V ⊆ U from Set.inter_subset_left)).continuous := by
  -- Split only on the distinguished basepoint; all other intersection points
  -- select the shared path by construction.
  by_cases hbase : x = ⟨x₀, hx₀⟩
  · subst x
    simp only [leftConnector, intersectionConnector, dite_true]
    ext t
    rfl
  · have hleft : (⟨x.1, x.2.1⟩ : U) ≠ ⟨x₀, hx₀.1⟩ := by
      intro h
      apply hbase
      exact Subtype.ext (congrArg (fun y : U ↦ y.1) h)
    simp only [leftConnector, intersectionConnector, hbase, hleft, dite_false,
      x.2.2, dite_true]

/-- Helper for Theorem 70.1: at an intersection point, the connector in `V`
is the image of the common intersection connector. -/
private lemma rightConnector_intersection {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace V] [PathConnectedSpace (U ∩ V : Set X)]
    (x : (U ∩ V : Set X)) :
    rightConnector U V x₀ hx₀ ⟨x.1, x.2.2⟩ =
      (intersectionConnector U V x₀ hx₀ x).map
        (ContinuousMap.inclusion
          (show U ∩ V ⊆ V from Set.inter_subset_right)).continuous := by
  -- The symmetric construction in `V` selects the same intersection path.
  by_cases hbase : x = ⟨x₀, hx₀⟩
  · subst x
    simp only [rightConnector, intersectionConnector, dite_true]
    ext t
    rfl
  · have hright : (⟨x.1, x.2.2⟩ : V) ≠ ⟨x₀, hx₀.2⟩ := by
      intro h
      apply hbase
      exact Subtype.ext (congrArg (fun y : V ↦ y.1) h)
    simp only [rightConnector, intersectionConnector, hbase, hright, dite_false,
      x.2.1, dite_true]


/-- Helper for Theorem 70.1: a homomorphism on `π₁(U, x₀)` extends along the
chosen connectors to the fundamental groupoid of `U`. -/
private noncomputable def leftPathFunctor {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace (U ∩ V : Set X)]
    {H : Type v} [Group H]
    (k : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H) :
    FundamentalGroupoid U ⥤ CategoryTheory.SingleObj H :=
  basedPathFunctor (FundamentalGroupoid.mk (⟨x₀, hx₀.1⟩ : U))
    (fun x ↦ ⟦leftConnector U V x₀ hx₀ x.as⟧) k

/-- Helper for Theorem 70.1: a homomorphism on `π₁(V, x₀)` extends along the
chosen connectors to the fundamental groupoid of `V`. -/
private noncomputable def rightPathFunctor {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace V] [PathConnectedSpace (U ∩ V : Set X)]
    {H : Type v} [Group H]
    (k : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H) :
    FundamentalGroupoid V ⥤ CategoryTheory.SingleObj H :=
  basedPathFunctor (FundamentalGroupoid.mk (⟨x₀, hx₀.2⟩ : V))
    (fun x ↦ ⟦rightConnector U V x₀ hx₀ x.as⟧) k

/-- Helper for Theorem 70.1: the chosen connector in `U` represents the
identity arrow at the distinguished basepoint. -/
private lemma leftConnectorClass_at_base {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace (U ∩ V : Set X)] :
    ⟦leftConnector U V x₀ hx₀ ⟨x₀, hx₀.1⟩⟧ =
      𝟙 (FundamentalGroupoid.mk (⟨x₀, hx₀.1⟩ : U)) := by
  -- The distinguished branch is the constant path, whose class is the identity.
  simp only [leftConnector, dite_true, pathOfEq]
  rfl

/-- Helper for Theorem 70.1: the chosen connector in `V` represents the
identity arrow at the distinguished basepoint. -/
private lemma rightConnectorClass_at_base {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace V] [PathConnectedSpace (U ∩ V : Set X)] :
    ⟦rightConnector U V x₀ hx₀ ⟨x₀, hx₀.2⟩⟧ =
      𝟙 (FundamentalGroupoid.mk (⟨x₀, hx₀.2⟩ : V)) := by
  -- The symmetric distinguished branch is likewise the constant path.
  simp only [rightConnector, dite_true, pathOfEq]
  rfl

/-- Helper for Theorem 70.1: the connector functor on `U` recovers the
prescribed homomorphism on the vertex group at `x₀`. -/
private lemma leftPathFunctor_mapEnd_eq {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace (U ∩ V : Set X)]
    {H : Type v} [Group H]
    (k : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H) :
    (leftPathFunctor U V x₀ hx₀ k).mapEnd
        (FundamentalGroupoid.mk (⟨x₀, hx₀.1⟩ : U)) = k := by
  -- Apply the generic basepoint computation using the identity connector class.
  apply MonoidHom.ext
  intro f
  exact basedPathFunctor_map_at_base
    (FundamentalGroupoid.mk (⟨x₀, hx₀.1⟩ : U))
    (fun x ↦ ⟦leftConnector U V x₀ hx₀ x.as⟧) k
    (leftConnectorClass_at_base U V x₀ hx₀) f

/-- Helper for Theorem 70.1: the connector functor on `V` recovers the
prescribed homomorphism on the vertex group at `x₀`. -/
private lemma rightPathFunctor_mapEnd_eq {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace V] [PathConnectedSpace (U ∩ V : Set X)]
    {H : Type v} [Group H]
    (k : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H) :
    (rightPathFunctor U V x₀ hx₀ k).mapEnd
        (FundamentalGroupoid.mk (⟨x₀, hx₀.2⟩ : V)) = k := by
  -- Apply the same basepoint computation to the right connector family.
  apply MonoidHom.ext
  intro f
  exact basedPathFunctor_map_at_base
    (FundamentalGroupoid.mk (⟨x₀, hx₀.2⟩ : V))
    (fun x ↦ ⟦rightConnector U V x₀ hx₀ x.as⟧) k
    (rightConnectorClass_at_base U V x₀ hx₀) f


/-- Helper for Theorem 70.1: at an intersection object, the left connector
class is the image of the common connector class. -/
private lemma leftConnectorClass_intersection {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace (U ∩ V : Set X)]
    (x : (U ∩ V : Set X)) :
    ⟦leftConnector U V x₀ hx₀ ⟨x.1, x.2.1⟩⟧ =
      (FundamentalGroupoid.map
        (ContinuousMap.inclusion Set.inter_subset_left)).map
          ⟦intersectionConnector U V x₀ hx₀ x⟧ := by
  -- Pass the path equality through the homotopy-quotient constructor.
  exact congrArg Path.Homotopic.Quotient.mk
    (leftConnector_intersection U V x₀ hx₀ x)

/-- Helper for Theorem 70.1: at an intersection object, the right connector
class is the image of the common connector class. -/
private lemma rightConnectorClass_intersection {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace V] [PathConnectedSpace (U ∩ V : Set X)]
    (x : (U ∩ V : Set X)) :
    ⟦rightConnector U V x₀ hx₀ ⟨x.1, x.2.2⟩⟧ =
      (FundamentalGroupoid.map
        (ContinuousMap.inclusion Set.inter_subset_right)).map
          ⟦intersectionConnector U V x₀ hx₀ x⟧ := by
  -- Pass the symmetric path equality through the homotopy quotient.
  exact congrArg Path.Homotopic.Quotient.mk
    (rightConnector_intersection U V x₀ hx₀ x)

/-- Helper for Theorem 70.1: equal connector arrows give equal closed
endomorphisms around a fixed middle arrow. -/
private lemma endOf_comp_inv_congr {C : Type*} [Groupoid C]
    {b x y : C} {q q' : b ⟶ x} (p : x ⟶ y) {r r' : b ⟶ y}
    (hq : q = q') (hr : r = r') :
    End.of (q ≫ p ≫ Groupoid.inv r) =
      End.of (q' ≫ p ≫ Groupoid.inv r') := by
  -- Substitute the two connector equalities; the middle arrow is unchanged.
  subst q'
  subst r'
  rfl

/-- Helper for Theorem 70.1: a functor maps a connector-closed arrow to the
connector-closed images of its three constituent arrows. -/
private lemma endOf_map_closedArrow {C D : Type*} [Groupoid C] [Groupoid D]
    (F : C ⥤ D) {b x y : C} (q : b ⟶ x) (p : x ⟶ y) (r : b ⟶ y) :
    End.of (F.map q ≫ F.map p ≫ Groupoid.inv (F.map r)) =
      End.of (F.map (q ≫ p ≫ Groupoid.inv r)) := by
  -- Apply preservation of composition and inverses in the target groupoid.
  simp only [Groupoid.inv_eq_inv, Functor.map_comp, Functor.map_inv]

/-- Helper for Theorem 70.1: the connector functors induced by compatible
homomorphisms assign the same value to every arrow in `U ∩ V`. -/
private lemma pathFunctors_agree_on_intersection {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)] {H : Type v} [Group H]
    (kU : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H)
    (kV : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H)
    (hk : kU.comp (FundamentalGroup.mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩) =
      kV.comp (FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩))
    {x y : FundamentalGroupoid (U ∩ V : Set X)} (p : x ⟶ y) :
    (leftPathFunctor U V x₀ hx₀ kU).map
        ((FundamentalGroupoid.map
          (ContinuousMap.inclusion Set.inter_subset_left)).map p) =
      (rightPathFunctor U V x₀ hx₀ kV).map
        ((FundamentalGroupoid.map
          (ContinuousMap.inclusion Set.inter_subset_right)).map p) := by
  -- Close the arrow by the common intersection connectors.
  let qx : FundamentalGroupoid.mk (⟨x₀, hx₀⟩ : (U ∩ V : Set X)) ⟶ x :=
    ⟦intersectionConnector U V x₀ hx₀ x.as⟧
  let qy : FundamentalGroupoid.mk (⟨x₀, hx₀⟩ : (U ∩ V : Set X)) ⟶ y :=
    ⟦intersectionConnector U V x₀ hx₀ y.as⟧
  let loop : FundamentalGroup (U ∩ V : Set X) ⟨x₀, hx₀⟩ :=
    End.of (qx ≫ p ≫ Groupoid.inv qy)
  -- Align the connector classes at both ends with their inclusion images.
  have hleftX :
      ⟦leftConnector U V x₀ hx₀
          ((FundamentalGroupoid.map
            (ContinuousMap.inclusion Set.inter_subset_left)).obj x).as⟧ =
        (FundamentalGroupoid.map
          (ContinuousMap.inclusion Set.inter_subset_left)).map qx := by
    exact leftConnectorClass_intersection U V x₀ hx₀ x.as
  have hleftY :
      ⟦leftConnector U V x₀ hx₀
          ((FundamentalGroupoid.map
            (ContinuousMap.inclusion Set.inter_subset_left)).obj y).as⟧ =
        (FundamentalGroupoid.map
          (ContinuousMap.inclusion Set.inter_subset_left)).map qy := by
    exact leftConnectorClass_intersection U V x₀ hx₀ y.as
  have hrightX :
      ⟦rightConnector U V x₀ hx₀
          ((FundamentalGroupoid.map
            (ContinuousMap.inclusion Set.inter_subset_right)).obj x).as⟧ =
        (FundamentalGroupoid.map
          (ContinuousMap.inclusion Set.inter_subset_right)).map qx := by
    exact rightConnectorClass_intersection U V x₀ hx₀ x.as
  have hrightY :
      ⟦rightConnector U V x₀ hx₀
          ((FundamentalGroupoid.map
            (ContinuousMap.inclusion Set.inter_subset_right)).obj y).as⟧ =
        (FundamentalGroupoid.map
          (ContinuousMap.inclusion Set.inter_subset_right)).map qy := by
    exact rightConnectorClass_intersection U V x₀ hx₀ y.as
  -- Normalize each connector-closed cover arrow to the mapped intersection loop.
  have hleftClosed :
      End.of
          (⟦leftConnector U V x₀ hx₀
              ((FundamentalGroupoid.map
                (ContinuousMap.inclusion Set.inter_subset_left)).obj x).as⟧ ≫
            (FundamentalGroupoid.map
              (ContinuousMap.inclusion Set.inter_subset_left)).map p ≫
            Groupoid.inv
              ⟦leftConnector U V x₀ hx₀
                ((FundamentalGroupoid.map
                  (ContinuousMap.inclusion Set.inter_subset_left)).obj y).as⟧) =
        FundamentalGroup.mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩ loop := by
    calc
      _ = End.of
          ((FundamentalGroupoid.map
              (ContinuousMap.inclusion Set.inter_subset_left)).map qx ≫
            (FundamentalGroupoid.map
              (ContinuousMap.inclusion Set.inter_subset_left)).map p ≫
            Groupoid.inv
              ((FundamentalGroupoid.map
                (ContinuousMap.inclusion Set.inter_subset_left)).map qy)) :=
        endOf_comp_inv_congr _ hleftX hleftY
      _ = End.of
          ((FundamentalGroupoid.map
            (ContinuousMap.inclusion Set.inter_subset_left)).map
              (qx ≫ p ≫ Groupoid.inv qy)) :=
        endOf_map_closedArrow
          (FundamentalGroupoid.map
            (ContinuousMap.inclusion Set.inter_subset_left)) qx p qy
      _ = _ := rfl
  have hrightClosed :
      End.of
          (⟦rightConnector U V x₀ hx₀
              ((FundamentalGroupoid.map
                (ContinuousMap.inclusion Set.inter_subset_right)).obj x).as⟧ ≫
            (FundamentalGroupoid.map
              (ContinuousMap.inclusion Set.inter_subset_right)).map p ≫
            Groupoid.inv
              ⟦rightConnector U V x₀ hx₀
                ((FundamentalGroupoid.map
                  (ContinuousMap.inclusion Set.inter_subset_right)).obj y).as⟧) =
        FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩ loop := by
    calc
      _ = End.of
          ((FundamentalGroupoid.map
              (ContinuousMap.inclusion Set.inter_subset_right)).map qx ≫
            (FundamentalGroupoid.map
              (ContinuousMap.inclusion Set.inter_subset_right)).map p ≫
            Groupoid.inv
              ((FundamentalGroupoid.map
                (ContinuousMap.inclusion Set.inter_subset_right)).map qy)) :=
        endOf_comp_inv_congr _ hrightX hrightY
      _ = End.of
          ((FundamentalGroupoid.map
            (ContinuousMap.inclusion Set.inter_subset_right)).map
              (qx ≫ p ≫ Groupoid.inv qy)) :=
        endOf_map_closedArrow
          (FundamentalGroupoid.map
            (ContinuousMap.inclusion Set.inter_subset_right)) qx p qy
      _ = _ := rfl
  -- Compatibility evaluated on `loop` finishes the comparison.
  have hcompat :
      kU (FundamentalGroup.mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩ loop) =
        kV (FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩ loop) := by
    exact DFunLike.congr_fun hk loop
  simp only [leftPathFunctor, rightPathFunctor, basedPathFunctor]
  calc
    _ = kU (FundamentalGroup.mapOfSubset Set.inter_subset_left
        ⟨x₀, hx₀⟩ loop) := congrArg kU hleftClosed
    _ = kV (FundamentalGroup.mapOfSubset Set.inter_subset_right
        ⟨x₀, hx₀⟩ loop) := hcompat
    _ = _ := congrArg kV hrightClosed.symm

/-- Helper for Theorem 70.1: compatible homomorphisms determine local
fundamental-groupoid functors with their intersection and basepoint laws. -/
private structure OpenUnionLocalSystem {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) {H : Type v} [Group H]
    (kU : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H)
    (kV : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H) where
  left : FundamentalGroupoid U ⥤ CategoryTheory.SingleObj H
  right : FundamentalGroupoid V ⥤ CategoryTheory.SingleObj H
  agree : ∀ {x y : FundamentalGroupoid (U ∩ V : Set X)} (p : x ⟶ y),
    left.map
        ((FundamentalGroupoid.map
          (ContinuousMap.inclusion Set.inter_subset_left)).map p) =
      right.map
        ((FundamentalGroupoid.map
          (ContinuousMap.inclusion Set.inter_subset_right)).map p)
  left_at_base : left.mapEnd (FundamentalGroupoid.mk ⟨x₀, hx₀.1⟩) = kU
  right_at_base : right.mapEnd (FundamentalGroupoid.mk ⟨x₀, hx₀.2⟩) = kV

/-- Helper for Theorem 70.1: a morphism between arbitrary objects of a
one-object category has a canonical value in its defining monoid. -/
private def singleObjMorphismValue {M : Type*} [Monoid M]
    {x y : CategoryTheory.SingleObj M} (f : x ⟶ y) : M :=
  f

/-- Helper for Theorem 70.1: restricting a path with known range containment to
a subspace is continuous. -/
private lemma pathCodRestrict_continuous {X : Type*} [TopologicalSpace X]
    {A : Set X} {x y : A} (p : Path x.1 y.1) (hp : Set.range p ⊆ A) :
    Continuous (fun t ↦ (⟨p t, hp (Set.mem_range_self t)⟩ : A)) := by
  -- Continuity into a subtype is detected after composing with its inclusion.
  exact p.continuous.subtype_mk _

/-- Helper for Theorem 70.1: the restricted path begins at the prescribed
subspace point. -/
private lemma pathCodRestrict_source {X : Type*} [TopologicalSpace X]
    {A : Set X} {x y : A} (p : Path x.1 y.1) (hp : Set.range p ⊆ A) :
    (⟨p 0, hp (Set.mem_range_self 0)⟩ : A) = x := by
  -- Subtype extensionality reduces the endpoint to the source law of `p`.
  exact Subtype.ext p.source

/-- Helper for Theorem 70.1: the restricted path ends at the prescribed
subspace point. -/
private lemma pathCodRestrict_target {X : Type*} [TopologicalSpace X]
    {A : Set X} {x y : A} (p : Path x.1 y.1) (hp : Set.range p ⊆ A) :
    (⟨p 1, hp (Set.mem_range_self 1)⟩ : A) = y := by
  -- Subtype extensionality reduces the endpoint to the target law of `p`.
  exact Subtype.ext p.target

/-- Helper for Theorem 70.1: an ambient path whose range lies in a set can be
regarded canonically as a path in that subspace. -/
private def pathCodRestrict {X : Type*} [TopologicalSpace X]
    {A : Set X} {x y : A} (p : Path x.1 y.1) (hp : Set.range p ⊆ A) :
    Path x y :=
  { toContinuousMap :=
      ⟨fun t ↦ ⟨p t, hp (Set.mem_range_self t)⟩,
        pathCodRestrict_continuous p hp⟩
    source' := pathCodRestrict_source p hp
    target' := pathCodRestrict_target p hp }

/-- Helper for Theorem 70.1: forgetting the subtype after codomain restriction
recovers the original path value. -/
private lemma pathCodRestrict_coe {X : Type*} [TopologicalSpace X]
    {A : Set X} {x y : A} (p : Path x.1 y.1) (hp : Set.range p ⊆ A)
    (t : unitInterval) :
    ((pathCodRestrict p hp t : A) : X) = p t := by
  -- The restriction changes only the codomain and its membership witness.
  rfl

/-- Helper for Theorem 70.1: restricting a path to a smaller subspace and then
including it into a larger one agrees with direct restriction. -/
private lemma pathCodRestrict_map_inclusion {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h : A ⊆ B) {x y : A} (p : Path x.1 y.1)
    (hp : Set.range p ⊆ A) :
    (pathCodRestrict p hp).map (ContinuousMap.inclusion h).continuous =
      pathCodRestrict
        (x := (⟨x.1, h x.2⟩ : B)) (y := (⟨y.1, h y.2⟩ : B)) p
        (fun _ hz ↦ h (hp hz)) := by
  -- Both paths have the same pointwise values in the larger subtype.
  ext t
  rfl

/-- Helper for Theorem 70.1: a homotopy contained in a subspace is continuous
after restricting its codomain to that subspace. -/
private lemma homotopyCodRestrict_continuous {X : Type*} [TopologicalSpace X]
    {A : Set X} {x y : A} {p q : Path x.1 y.1} (F : Path.Homotopy p q)
    (hF : Set.range F ⊆ A) :
    Continuous (fun z ↦ (⟨F z, hF (Set.mem_range_self z)⟩ : A)) := by
  -- As for paths, continuity into the subtype follows from ambient continuity.
  exact F.continuous.subtype_mk _

/-- Helper for Theorem 70.1: the restricted homotopy starts at the restricted
initial path. -/
private lemma homotopyCodRestrict_zero {X : Type*} [TopologicalSpace X]
    {A : Set X} {x y : A} {p q : Path x.1 y.1} (hp : Set.range p ⊆ A)
    (F : Path.Homotopy p q) (hF : Set.range F ⊆ A) (t : unitInterval) :
    (⟨F (0, t), hF (Set.mem_range_self (0, t))⟩ : A) =
      pathCodRestrict p hp t := by
  -- The ambient equality at homotopy time zero determines the subtype equality.
  exact Subtype.ext (F.apply_zero t)

/-- Helper for Theorem 70.1: the restricted homotopy ends at the restricted
final path. -/
private lemma homotopyCodRestrict_one {X : Type*} [TopologicalSpace X]
    {A : Set X} {x y : A} {p q : Path x.1 y.1} (hq : Set.range q ⊆ A)
    (F : Path.Homotopy p q) (hF : Set.range F ⊆ A) (t : unitInterval) :
    (⟨F (1, t), hF (Set.mem_range_self (1, t))⟩ : A) =
      pathCodRestrict q hq t := by
  -- The ambient equality at homotopy time one determines the subtype equality.
  exact Subtype.ext (F.apply_one t)

/-- Helper for Theorem 70.1: restricting the codomain preserves the fixed
endpoint condition of a path homotopy. -/
private lemma homotopyCodRestrict_fixed {X : Type*} [TopologicalSpace X]
    {A : Set X} {x y : A} {p q : Path x.1 y.1} (hp : Set.range p ⊆ A)
    (F : Path.Homotopy p q) (hF : Set.range F ⊆ A)
    (t s : unitInterval) (hs : s ∈ ({0, 1} : Set unitInterval)) :
    (⟨F (t, s), hF (Set.mem_range_self (t, s))⟩ : A) =
      pathCodRestrict p hp s := by
  -- Fixed endpoints are inherited pointwise from the ambient relative homotopy.
  exact Subtype.ext (F.eq_fst t hs)

/-- Helper for Theorem 70.1: a path homotopy whose image lies in a set lifts
canonically to a path homotopy in that subspace. -/
private def homotopyCodRestrict {X : Type*} [TopologicalSpace X]
    {A : Set X} {x y : A} {p q : Path x.1 y.1} (hp : Set.range p ⊆ A)
    (hq : Set.range q ⊆ A) (F : Path.Homotopy p q)
    (hF : Set.range F ⊆ A) :
    Path.Homotopy (pathCodRestrict p hp) (pathCodRestrict q hq) :=
  { toFun := fun z ↦ ⟨F z, hF (Set.mem_range_self z)⟩
    continuous_toFun := homotopyCodRestrict_continuous F hF
    map_zero_left := homotopyCodRestrict_zero hp F hF
    map_one_left := homotopyCodRestrict_one hq F hF
    prop' := homotopyCodRestrict_fixed hp F hF }

/-- Helper for Theorem 70.1: ambiently homotopic paths have equal homotopy
classes after codomain restriction when the entire homotopy stays in the subspace. -/
private lemma pathCodRestrict_mk_eq_of_homotopy
    {X : Type*} [TopologicalSpace X]
    {A : Set X} {x y : A} {p q : Path x.1 y.1} (hp : Set.range p ⊆ A)
    (hq : Set.range q ⊆ A) (F : Path.Homotopy p q)
    (hF : Set.range F ⊆ A) :
    Path.Homotopic.Quotient.mk (pathCodRestrict p hp) =
      Path.Homotopic.Quotient.mk (pathCodRestrict q hq) := by
  -- Lift the homotopy and invoke the quotient's defining equivalence relation.
  rw [Path.Homotopic.Quotient.eq]
  exact ⟨homotopyCodRestrict hp hq F hF⟩

/-- Helper for Theorem 70.1: an ordered subpath has range contained in every
ordered parent subpath. -/
private lemma rangeSubpath_mono {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) (a c d b : unitInterval) (hac : a ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ b) :
    Set.range (p.subpath c d) ⊆ Set.range (p.subpath a b) := by
  -- Rewrite both ranges as images of ordered parameter intervals.
  rw [Path.range_subpath_of_le p c d hcd,
    Path.range_subpath_of_le p a b (hac.trans (hcd.trans hdb))]
  -- Interval inclusion is preserved by the image of the ambient path.
  exact Set.image_mono fun _ ht ↦ ⟨hac.trans ht.1, ht.2.trans hdb⟩

/-- Helper for Theorem 70.1: every point between the endpoints of a covered
subpath belongs to the covering set. -/
private lemma subpathPoint_mem_of_range_subset
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    (p : Path x y) (a t b : unitInterval) (hat : a ≤ t) (htb : t ≤ b)
    (hp : Set.range (p.subpath a b) ⊆ A) : p t ∈ A := by
  -- The parameter `t` lies in the interval whose image is the parent range.
  apply hp
  rw [Path.range_subpath_of_le p a b (hat.trans htb)]
  exact ⟨t, ⟨hat, htb⟩, rfl⟩

/-- Helper for Theorem 70.1: containment of a parent subpath transports to
every ordered nested subpath. -/
private lemma nestedSubpath_range_subset
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    (p : Path x y) (a c d b : unitInterval) (hac : a ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ b) (hp : Set.range (p.subpath a b) ⊆ A) :
    Set.range (p.subpath c d) ⊆ A := by
  -- First enter the parent range, then apply its cover containment.
  exact fun _ hz ↦ hp (rangeSubpath_mono p a c d b hac hcd hdb hz)

/-- Helper for Theorem 70.1: a parameter in a covered parent interval gives a
canonical point of the covering subspace. -/
private def coveredSubpathPoint
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    (p : Path x y) (a b : unitInterval)
    (hp : Set.range (p.subpath a b) ⊆ A) (t : unitInterval)
    (hat : a ≤ t) (htb : t ≤ b) : A :=
  -- Package the parent-range membership supplied by the interval bounds.
  ⟨p t, subpathPoint_mem_of_range_subset p a t b hat htb hp⟩

/-- Helper for Theorem 70.1: a nested ordered subpath is restricted using
endpoint points and containment inherited from one fixed covered parent. -/
private def codRestrictedNestedSubpath
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    (p : Path x y) (a c d b : unitInterval) (hac : a ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ b) (hp : Set.range (p.subpath a b) ⊆ A) :
    Path
      (coveredSubpathPoint p a b hp c hac (hcd.trans hdb))
      (coveredSubpathPoint p a b hp d (hac.trans hcd) hdb) :=
  -- Restrict the child range through its inclusion in the fixed parent range.
  pathCodRestrict (p.subpath c d)
    (nestedSubpath_range_subset p a c d b hac hcd hdb hp)

/-- Helper for Theorem 70.1: the class of a nested ordered subpath restricted
inside one fixed covered parent interval. -/
private def codRestrictedNestedSubpathClass
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    (p : Path x y) (a c d b : unitInterval) (hac : a ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ b) (hp : Set.range (p.subpath a b) ⊆ A) :
    Path.Homotopic.Quotient
      (coveredSubpathPoint p a b hp c hac (hcd.trans hdb))
      (coveredSubpathPoint p a b hp d (hac.trans hcd) hdb) :=
  -- Pass the canonical restricted path to the path-homotopy quotient.
  Path.Homotopic.Quotient.mk
    (codRestrictedNestedSubpath p a c d b hac hcd hdb hp)

/-- Helper for Theorem 70.1: the auxiliary homotopy which joins two adjacent
subpaths stays inside the range of their parent subpath. -/
private lemma subpathTransSubpathRefl_range_subset
    {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y)
    (a c b : unitInterval) (hac : a ≤ c) (hcb : c ≤ b) :
    Set.range (Path.Homotopy.subpathTransSubpathRefl p a c b) ⊆
      Set.range (p.subpath a b) := by
  -- At every homotopy time, the moving split point remains between `c` and `b`.
  rintro _ ⟨⟨t, s⟩, rfl⟩
  have hcm : c ≤ Set.Icc.convexComb c b t := Set.Icc.le_convexComb hcb t
  have hmb : Set.Icc.convexComb c b t ≤ b := Set.Icc.convexComb_le hcb t
  have hleft :
      Set.range (p.subpath a (Set.Icc.convexComb c b t)) ⊆
        Set.range (p.subpath a b) :=
    rangeSubpath_mono p a a (Set.Icc.convexComb c b t) b le_rfl
      (hac.trans hcm) hmb
  have hright :
      Set.range (p.subpath (Set.Icc.convexComb c b t) b) ⊆
        Set.range (p.subpath a b) :=
    rangeSubpath_mono p a (Set.Icc.convexComb c b t) b b
      (hac.trans hcm) hmb le_rfl
  have hmoving :
      ((p.subpath a (Set.Icc.convexComb c b t)).trans
          (p.subpath (Set.Icc.convexComb c b t) b)) s ∈
        Set.range (p.subpath a b) := by
    -- The two moving pieces are both nested subpaths of the parent.
    have hrange : Set.range
        ((p.subpath a (Set.Icc.convexComb c b t)).trans
          (p.subpath (Set.Icc.convexComb c b t) b)) ⊆
        Set.range (p.subpath a b) := by
      rw [Path.trans_range]
      exact Set.union_subset hleft hright
    exact hrange (Set.mem_range_self s)
  change ((p.subpath a (Set.Icc.convexComb c b t)).trans
      (p.subpath (Set.Icc.convexComb c b t) b)) s ∈
    Set.range (p.subpath a b)
  exact hmoving

/-- Helper for Theorem 70.1: parent-cover containment transports across the
auxiliary adjacent-subpath homotopy. -/
private lemma subpathTransSubpathRefl_subset_of_parent_subset
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    (p : Path x y) (a c b : unitInterval) (hac : a ≤ c) (hcb : c ≤ b)
    (hp : Set.range (p.subpath a b) ⊆ A) :
    Set.range (Path.Homotopy.subpathTransSubpathRefl p a c b) ⊆ A := by
  -- Compose geometric containment with the selected cover member.
  exact fun _ hz ↦ hp
    (subpathTransSubpathRefl_range_subset p a c b hac hcb hz)

/-- Helper for Theorem 70.1: codomain restriction commutes with concatenation,
independently of the supplied range-containment proofs. -/
private lemma pathCodRestrict_trans {X : Type*} [TopologicalSpace X]
    {A : Set X} {x y z : A} (p : Path x.1 y.1) (q : Path y.1 z.1)
    (hp : Set.range p ⊆ A) (hq : Set.range q ⊆ A)
    (hpq : Set.range (p.trans q) ⊆ A) :
    pathCodRestrict (p.trans q) hpq =
      (pathCodRestrict p hp).trans (pathCodRestrict q hq) := by
  -- Pointwise equality forgets only proposition-valued membership witnesses.
  ext t
  simp only [pathCodRestrict_coe, Path.trans_apply]
  split_ifs
  · exact (pathCodRestrict_coe p hp _).symm
  · exact (pathCodRestrict_coe q hq _).symm

/-- Helper for Theorem 70.1: restricting an ambient constant path gives the
constant path in the subspace. -/
private lemma pathCodRestrict_refl {X : Type*} [TopologicalSpace X]
    {A : Set X} (x : A) (hp : Set.range (Path.refl x.1) ⊆ A) :
    pathCodRestrict (x := x) (y := x) (Path.refl x.1) hp = Path.refl x := by
  -- Both constant paths have the same value at every parameter.
  ext t
  rfl

/-- Helper for Theorem 70.1: a contained homotopy from a concatenation to a
path followed by a constant path gives the corresponding quotient composition. -/
private lemma pathCodRestrict_mk_trans_eq_of_homotopy_refl
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y z : A}
    (p : Path x.1 y.1) (q : Path y.1 z.1) (r : Path x.1 z.1)
    (hp : Set.range p ⊆ A) (hq : Set.range q ⊆ A)
    (hr : Set.range r ⊆ A)
    (F : Path.Homotopy (p.trans q) (r.trans (Path.refl z.1)))
    (hF : Set.range F ⊆ A) :
    Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.mk (pathCodRestrict p hp))
        (Path.Homotopic.Quotient.mk (pathCodRestrict q hq)) =
      Path.Homotopic.Quotient.mk (pathCodRestrict r hr) := by
  -- Both boundary concatenations remain in the subspace.
  have hpq : Set.range (p.trans q) ⊆ A := by
    rw [Path.trans_range]
    exact Set.union_subset hp hq
  have hrefl : Set.range (Path.refl z.1) ⊆ A := by
    rw [Path.refl_range, Set.singleton_subset_iff]
    exact z.2
  have hrRefl : Set.range (r.trans (Path.refl z.1)) ⊆ A := by
    rw [Path.trans_range]
    exact Set.union_subset hr hrefl
  have hclasses :=
    pathCodRestrict_mk_eq_of_homotopy hpq hrRefl F hF
  -- Normalize both restricted concatenations, then remove the constant class.
  calc
    _ = Path.Homotopic.Quotient.mk
        ((pathCodRestrict p hp).trans (pathCodRestrict q hq)) :=
      (Path.Homotopic.Quotient.mk_trans _ _).symm
    _ = Path.Homotopic.Quotient.mk (pathCodRestrict (p.trans q) hpq) :=
      congrArg Path.Homotopic.Quotient.mk
        (pathCodRestrict_trans p q hp hq hpq).symm
    _ = Path.Homotopic.Quotient.mk
        (pathCodRestrict (r.trans (Path.refl z.1)) hrRefl) := hclasses
    _ = Path.Homotopic.Quotient.mk
        ((pathCodRestrict r hr).trans (pathCodRestrict (Path.refl z.1) hrefl)) :=
      congrArg Path.Homotopic.Quotient.mk
        (pathCodRestrict_trans r (Path.refl z.1) hr hrefl hrRefl)
    _ = Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.mk (pathCodRestrict r hr))
        (Path.Homotopic.Quotient.mk (pathCodRestrict (Path.refl z.1) hrefl)) :=
      Path.Homotopic.Quotient.mk_trans _ _
    _ = Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.mk (pathCodRestrict r hr))
        (Path.Homotopic.Quotient.refl z) := by
      rw [pathCodRestrict_refl, Path.Homotopic.Quotient.mk_refl]
    _ = Path.Homotopic.Quotient.mk (pathCodRestrict r hr) :=
      Path.Homotopic.Quotient.trans_refl _

/-- Helper for Theorem 70.1: splitting a covered ordered subpath at an
intermediate parameter does not change its path-homotopy class. -/
private lemma pathCodRestrict_subpath_trans
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    (p : Path x y) (a c b : unitInterval) (hac : a ≤ c) (hcb : c ≤ b)
    (hp : Set.range (p.subpath a b) ⊆ A) :
    Path.Homotopic.Quotient.trans
        (codRestrictedNestedSubpathClass p a a c b le_rfl hac hcb hp)
        (codRestrictedNestedSubpathClass p a c b b hac hcb le_rfl hp) =
      codRestrictedNestedSubpathClass p a a b b le_rfl (hac.trans hcb) le_rfl hp := by
  -- Route correction: restrict only the auxiliary homotopy; the quotient unit
  -- law removes its trailing constant path without unfolding `transRefl`.
  let xa := coveredSubpathPoint p a b hp a le_rfl (hac.trans hcb)
  let xc := coveredSubpathPoint p a b hp c hac hcb
  let xb := coveredSubpathPoint p a b hp b (hac.trans hcb) le_rfl
  have hsplit := pathCodRestrict_mk_trans_eq_of_homotopy_refl
    (x := xa) (y := xc) (z := xb)
    (p.subpath a c) (p.subpath c b) (p.subpath a b)
    (nestedSubpath_range_subset p a a c b le_rfl hac hcb hp)
    (nestedSubpath_range_subset p a c b b hac hcb le_rfl hp) hp
    (Path.Homotopy.subpathTransSubpathRefl p a c b)
    (subpathTransSubpathRefl_subset_of_parent_subset p a c b hac hcb hp)
  exact hsplit

/-- Helper for Theorem 70.1: mapping a covered parent subpath through any
fundamental-groupoid functor yields the product of its two adjacent pieces. -/
private lemma codRestrictedSubpathValue_split
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    {H : Type*} [Group H]
    (F : FundamentalGroupoid A ⥤ CategoryTheory.SingleObj H)
    (p : Path x y) (a c b : unitInterval) (hac : a ≤ c) (hcb : c ≤ b)
    (hp : Set.range (p.subpath a b) ⊆ A) :
    F.map
        (codRestrictedNestedSubpathClass p a a b b le_rfl
          (hac.trans hcb) le_rfl hp) =
      F.map (codRestrictedNestedSubpathClass p a c b b hac hcb le_rfl hp) *
        F.map (codRestrictedNestedSubpathClass p a a c b le_rfl hac hcb hp) := by
  -- The quotient split is categorical composition in the fundamental groupoid.
  have hsplit := pathCodRestrict_subpath_trans p a c b hac hcb hp
  calc
    _ = F.map
        (Path.Homotopic.Quotient.trans
          (codRestrictedNestedSubpathClass p a a c b le_rfl hac hcb hp)
          (codRestrictedNestedSubpathClass p a c b b hac hcb le_rfl hp)) :=
      congrArg (fun q ↦ F.map q) hsplit.symm
    _ = F.map (codRestrictedNestedSubpathClass p a a c b le_rfl hac hcb hp) ≫
        F.map (codRestrictedNestedSubpathClass p a c b b hac hcb le_rfl hp) :=
      F.map_comp _ _
    _ = _ := rfl

/-- Helper for Theorem 70.1: evaluate a path contained in `U` with the left
fundamental-groupoid functor. -/
private def openUnionLeftPathValue {X : Type u} [TopologicalSpace X]
    {U V : Set X} {x₀ : X} {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂) {x y : U}
    (p : Path x y) : H :=
  S.left.map ⟦p⟧

/-- Helper for Theorem 70.1: evaluate a path contained in `V` with the right
fundamental-groupoid functor. -/
private def openUnionRightPathValue {X : Type u} [TopologicalSpace X]
    {U V : Set X} {x₀ : X} {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂) {x y : V}
    (p : Path x y) : H :=
  S.right.map ⟦p⟧

/-- Helper for Theorem 70.1: the left local path value sends a constant path
to the identity. -/
private lemma openUnionLeftPathValue_refl {X : Type u} [TopologicalSpace X]
    {U V : Set X} {x₀ : X} {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂) (x : U) :
    openUnionLeftPathValue S (Path.refl x) = 1 := by
  -- Regard the constant path class as the identity arrow and use functoriality.
  exact S.left.map_id (FundamentalGroupoid.mk x)

/-- Helper for Theorem 70.1: the left local value turns path concatenation
into multiplication in reverse categorical order. -/
private lemma openUnionLeftPathValue_trans {X : Type u} [TopologicalSpace X]
    {U V : Set X} {x₀ : X} {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    {x y z : U} (p : Path x y) (q : Path y z) :
    openUnionLeftPathValue S (p.trans q) =
      openUnionLeftPathValue S q * openUnionLeftPathValue S p := by
  -- Concatenation is categorical composition, whose one-object spelling is reversed multiplication.
  exact S.left.map_comp ⟦p⟧ ⟦q⟧

/-- Helper for Theorem 70.1: the right local path value sends a constant path
to the identity. -/
private lemma openUnionRightPathValue_refl {X : Type u} [TopologicalSpace X]
    {U V : Set X} {x₀ : X} {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂) (x : V) :
    openUnionRightPathValue S (Path.refl x) = 1 := by
  -- Regard the constant path class as the identity arrow and use functoriality.
  exact S.right.map_id (FundamentalGroupoid.mk x)

/-- Helper for Theorem 70.1: the right local value turns path concatenation
into multiplication in reverse categorical order. -/
private lemma openUnionRightPathValue_trans {X : Type u} [TopologicalSpace X]
    {U V : Set X} {x₀ : X} {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    {x y z : V} (p : Path x y) (q : Path y z) :
    openUnionRightPathValue S (p.trans q) =
      openUnionRightPathValue S q * openUnionRightPathValue S p := by
  -- The right functor obeys the same categorical composition law.
  exact S.right.map_comp ⟦p⟧ ⟦q⟧

/-- Helper for Theorem 70.1: the two local path values agree on every path in
the intersection. -/
private lemma openUnionPathValue_eq_on_intersection
    {X : Type u} [TopologicalSpace X]
    {U V : Set X} {x₀ : X} {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    {x y : (U ∩ V : Set X)} (p : Path x y) :
    openUnionLeftPathValue S
        (p.map (ContinuousMap.inclusion Set.inter_subset_left).continuous) =
      openUnionRightPathValue S
        (p.map (ContinuousMap.inclusion Set.inter_subset_right).continuous) := by
  -- Forget the irrelevant endpoint objects before normalizing the two mapped arrows.
  have hagree := congrArg singleObjMorphismValue (S.agree ⟦p⟧)
  -- Record each quotient/functor computation separately, avoiding a dependent
  -- rewrite across the two differently spelled endpoint objects.
  have hleft :
      openUnionLeftPathValue S
          (p.map (ContinuousMap.inclusion Set.inter_subset_left).continuous) =
        singleObjMorphismValue
          (S.left.map
            ((FundamentalGroupoid.map
              (ContinuousMap.inclusion Set.inter_subset_left)).map ⟦p⟧)) := by
    rfl
  have hright :
      openUnionRightPathValue S
          (p.map (ContinuousMap.inclusion Set.inter_subset_right).continuous) =
        singleObjMorphismValue
          (S.right.map
            ((FundamentalGroupoid.map
              (ContinuousMap.inclusion Set.inter_subset_right)).map ⟦p⟧)) := by
    rfl
  exact hleft.trans (hagree.trans hright.symm)

/-- Helper for Theorem 70.1: the left and right local values agree for every
ambient path whose entire range lies in `U ∩ V`. -/
private lemma openUnionPathValue_eq_of_range_subset_inter
    {X : Type u} [TopologicalSpace X]
    {U V : Set X} {x₀ : X} {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    {x y : (U ∩ V : Set X)} (p : Path x.1 y.1)
    (hp : Set.range p ⊆ U ∩ V) :
    openUnionLeftPathValue S
        (pathCodRestrict (A := U) (x := ⟨x.1, x.2.1⟩)
          (y := ⟨y.1, y.2.1⟩) p
          (fun z (hz : z ∈ Set.range p) ↦ (hp hz).1)) =
      openUnionRightPathValue S
        (pathCodRestrict (A := V) (x := ⟨x.1, x.2.2⟩)
          (y := ⟨y.1, y.2.2⟩) p
          (fun z (hz : z ∈ Set.range p) ↦ (hp hz).2)) := by
  -- First evaluate the canonical lift of `p` to the intersection.
  let pInter : Path x y := pathCodRestrict p hp
  have hvalue := openUnionPathValue_eq_on_intersection S pInter
  -- Its two inclusion images are the direct lifts to `U` and `V`.
  have hleft :
      pInter.map (ContinuousMap.inclusion Set.inter_subset_left).continuous =
        pathCodRestrict (A := U) (x := ⟨x.1, x.2.1⟩)
          (y := ⟨y.1, y.2.1⟩) p
          (fun z (hz : z ∈ Set.range p) ↦ (hp hz).1) := by
    exact pathCodRestrict_map_inclusion Set.inter_subset_left p hp
  have hright :
      pInter.map (ContinuousMap.inclusion Set.inter_subset_right).continuous =
        pathCodRestrict (A := V) (x := ⟨x.1, x.2.2⟩)
          (y := ⟨y.1, y.2.2⟩) p
          (fun z (hz : z ∈ Set.range p) ↦ (hp hz).2) := by
    exact pathCodRestrict_map_inclusion Set.inter_subset_right p hp
  rw [hleft, hright] at hvalue
  exact hvalue

/-- Helper for Theorem 70.1: the chosen connectors construct the compatible
local system associated to the two prescribed homomorphisms. -/
private noncomputable def compatibleOpenUnionLocalSystem
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)] {H : Type v} [Group H]
    (kU : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H)
    (kV : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H)
    (hk : kU.comp (FundamentalGroup.mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩) =
      kV.comp (FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩)) :
    OpenUnionLocalSystem U V x₀ hx₀ kU kV :=
  ⟨leftPathFunctor U V x₀ hx₀ kU,
    rightPathFunctor U V x₀ hx₀ kV,
    pathFunctors_agree_on_intersection U V x₀ hx₀ kU kV hk,
    leftPathFunctor_mapEnd_eq U V x₀ hx₀ kU,
    rightPathFunctor_mapEnd_eq U V x₀ hx₀ kV⟩

/-- Helper for Theorem 70.1: a finite monotone subdivision of a path whose
successive subpaths each lie in one member of the open cover. -/
private structure OpenUnionPathSubdivision
    {X : Type u} [TopologicalSpace X] (U V : Set X) {x y : X}
    (p : Path x y) where
  n : ℕ
  point : Fin (n + 2) → unitInterval
  start : point 0 = 0
  finish : point (Fin.last (n + 1)) = 1
  monotone : Monotone point
  side : Fin (n + 1) → Bool
  covered : ∀ i, Set.range (p.subpath (point i.castSucc) (point i.succ)) ⊆
    if side i then V else U

/-- Helper for Theorem 70.1: an edge labeled by the left cover member has
range contained in `U`. -/
private lemma OpenUnionPathSubdivision.covered_left
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x y : X}
    {p : Path x y} (D : OpenUnionPathSubdivision U V p)
    (i : Fin (D.n + 1)) (hi : D.side i = false) :
    Set.range (p.subpath (D.point i.castSucc) (D.point i.succ)) ⊆ U := by
  -- Normalize the Boolean label in the subdivision's cover condition.
  simpa only [hi, Bool.false_eq_true, if_false] using D.covered i

/-- Helper for Theorem 70.1: an edge labeled by the right cover member has
range contained in `V`. -/
private lemma OpenUnionPathSubdivision.covered_right
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x y : X}
    {p : Path x y} (D : OpenUnionPathSubdivision U V p)
    (i : Fin (D.n + 1)) (hi : D.side i = true) :
    Set.range (p.subpath (D.point i.castSucc) (D.point i.succ)) ⊆ V := by
  -- Normalize the Boolean label in the subdivision's cover condition.
  simpa only [hi, if_true] using D.covered i

/-- Helper for Theorem 70.1: consecutive subdivision parameters are ordered. -/
private lemma OpenUnionPathSubdivision.point_castSucc_le_point_succ
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x y : X}
    {p : Path x y} (D : OpenUnionPathSubdivision U V p)
    (i : Fin (D.n + 1)) : D.point i.castSucc ≤ D.point i.succ := by
  -- Apply monotonicity to the adjacent indices of the finite subdivision.
  exact D.monotone (Fin.castSucc_le_succ i)

/-- Helper for Theorem 70.1: the ordered-range predicate saying that an edge
lies in its Boolean-selected cover member. -/
private def openUnionEdgeCovered
    {X : Type u} [TopologicalSpace X] (U V : Set X) {x y : X}
    (p : Path x y) (side : Bool) (a b : unitInterval) : Prop :=
  a ≤ b ∧ Set.range (p.subpath a b) ⊆ if side then V else U

/-- Helper for Theorem 70.1: a covered edge has a proof-independent value,
selected only by its cover label and endpoints. -/
private noncomputable def openUnionCoveredEdgeValue
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    {x y : X} (p : Path x y) (side : Bool) (a b : unitInterval) : H :=
  match side with
  | false =>
      @dite H (openUnionEdgeCovered U V p false a b) (Classical.propDecidable _)
        (fun h ↦ S.left.map
          (codRestrictedNestedSubpathClass p a a b b le_rfl h.1 le_rfl h.2))
        (fun _ ↦ 1)
  | true =>
      @dite H (openUnionEdgeCovered U V p true a b) (Classical.propDecidable _)
        (fun h ↦ S.right.map
          (codRestrictedNestedSubpathClass p a a b b le_rfl h.1 le_rfl h.2))
        (fun _ ↦ 1)

/-- Helper for Theorem 70.1: a left-covered edge is evaluated by the left local
fundamental-groupoid functor. -/
private lemma openUnionCoveredEdgeValue_eq_left
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    {x y : X} (p : Path x y) (a b : unitInterval)
    (h : openUnionEdgeCovered U V p false a b) :
    openUnionCoveredEdgeValue S p false a b = S.left.map
      (codRestrictedNestedSubpathClass p a a b b le_rfl h.1 le_rfl h.2) := by
  -- The left label selects the left local functor; containment proofs are irrelevant.
  simp only [openUnionCoveredEdgeValue, h, dite_true]

/-- Helper for Theorem 70.1: a right-covered edge is evaluated by the right
local fundamental-groupoid functor. -/
private lemma openUnionCoveredEdgeValue_eq_right
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    {x y : X} (p : Path x y) (a b : unitInterval)
    (h : openUnionEdgeCovered U V p true a b) :
    openUnionCoveredEdgeValue S p true a b = S.right.map
      (codRestrictedNestedSubpathClass p a a b b le_rfl h.1 le_rfl h.2) := by
  -- The right label selects the right local functor.
  simp only [openUnionCoveredEdgeValue, h, dite_true]

/-- Helper for Theorem 70.1: splitting a left-covered edge at an intermediate
parameter replaces its value by the reverse ordered product of the two pieces. -/
private lemma openUnionLeftCoveredSubpathValue_split
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    {x y : X} (p : Path x y) (a c b : unitInterval)
    (hac : a ≤ c) (hcb : c ≤ b)
    (hp : Set.range (p.subpath a b) ⊆ U) :
    S.left.map
        (codRestrictedNestedSubpathClass p a a b b le_rfl
          (hac.trans hcb) le_rfl hp) =
      S.left.map
          (codRestrictedNestedSubpathClass p a c b b hac hcb le_rfl hp) *
        S.left.map
          (codRestrictedNestedSubpathClass p a a c b le_rfl hac hcb hp) := by
  -- Specialize the generic functorial splitting law to the left local functor.
  exact codRestrictedSubpathValue_split S.left p a c b hac hcb hp

/-- Helper for Theorem 70.1: splitting a right-covered edge at an intermediate
parameter replaces its value by the reverse ordered product of the two pieces. -/
private lemma openUnionRightCoveredSubpathValue_split
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    {x y : X} (p : Path x y) (a c b : unitInterval)
    (hac : a ≤ c) (hcb : c ≤ b)
    (hp : Set.range (p.subpath a b) ⊆ V) :
    S.right.map
        (codRestrictedNestedSubpathClass p a a b b le_rfl
          (hac.trans hcb) le_rfl hp) =
      S.right.map
          (codRestrictedNestedSubpathClass p a c b b hac hcb le_rfl hp) *
        S.right.map
          (codRestrictedNestedSubpathClass p a a c b le_rfl hac hcb hp) := by
  -- Specialize the generic functorial splitting law to the right local functor.
  exact codRestrictedSubpathValue_split S.right p a c b hac hcb hp

/-- Helper for Theorem 70.1: the two local functors assign equal values to an
ordered subpath whose range lies in the intersection. -/
private lemma openUnionCoveredSubpathValues_agree
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    {x y : X} (p : Path x y) (a b : unitInterval) (hab : a ≤ b)
    (hp : Set.range (p.subpath a b) ⊆ U ∩ V) :
    S.left.map
        (codRestrictedNestedSubpathClass p a a b b le_rfl hab le_rfl
          (fun _ hz ↦ (hp hz).1)) =
      S.right.map
        (codRestrictedNestedSubpathClass p a a b b le_rfl hab le_rfl
          (fun _ hz ↦ (hp hz).2)) := by
  -- Apply the established overlap law to the ambient ordered subpath.
  let xa : (U ∩ V : Set X) :=
    coveredSubpathPoint p a b hp a le_rfl hab
  let xb : (U ∩ V : Set X) :=
    coveredSubpathPoint p a b hp b hab le_rfl
  exact openUnionPathValue_eq_of_range_subset_inter S
    (x := xa) (y := xb) (p.subpath a b) hp

/-- Helper for Theorem 70.1: a covered degenerate subpath is sent to the
identity by every fundamental-groupoid functor. -/
private lemma codRestrictedSubpathValue_degenerate
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    {H : Type*} [Group H]
    (F : FundamentalGroupoid A ⥤ CategoryTheory.SingleObj H)
    (p : Path x y) (a : unitInterval)
    (hp : Set.range (p.subpath a a) ⊆ A) :
    F.map
        (codRestrictedNestedSubpathClass p a a a a le_rfl le_rfl le_rfl hp) =
      1 := by
  -- Normalize the ambient subpath and then its codomain restriction to a
  -- constant path before invoking preservation of identity arrows.
  let xa := coveredSubpathPoint p a a hp a le_rfl le_rfl
  have hpath :
      codRestrictedNestedSubpath p a a a a le_rfl le_rfl le_rfl hp =
        Path.refl xa := by
    -- Compare pointwise so the range proof is never transported through a
    -- dependent rewrite of `Path.subpath_self`.
    ext t
    exact congrArg p (Set.Icc.convexComb_eq a t)
  unfold codRestrictedNestedSubpathClass
  rw [hpath, Path.Homotopic.Quotient.mk_refl]
  exact F.map_id (FundamentalGroupoid.mk xa)

/-- Helper for Theorem 70.1: the proof-independent local edge evaluator obeys
the subdivision, splitting, and overlap laws. -/
private lemma openUnionCoveredEdgeLaws
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    {x y : X} (p : Path x y) :
    FiniteCoveredSubdivision.EdgeLaws
      (openUnionEdgeCovered U V p) (openUnionCoveredEdgeValue S p) := by
  -- Subedges inherit both their ordering and their cover containment.
  refine
    { subedge := ?_
      degenerate := ?_
      split := ?_
      agree := ?_ }
  · intro side a b c hab hac hcb
    constructor
    · exact ⟨hac, fun _ hz ↦ hab.2
        (rangeSubpath_mono p a a c b le_rfl hac hcb hz)⟩
    · exact ⟨hcb, fun _ hz ↦ hab.2
        (rangeSubpath_mono p a c b b hac hcb le_rfl hz)⟩
  · intro side a haa
    -- Each Boolean branch reduces to functoriality on a constant path.
    cases side
    · rw [openUnionCoveredEdgeValue_eq_left S p a a haa]
      exact codRestrictedSubpathValue_degenerate S.left p a haa.2
    · rw [openUnionCoveredEdgeValue_eq_right S p a a haa]
      exact codRestrictedSubpathValue_degenerate S.right p a haa.2
  · intro side a b c hab hac hcb
    have hleft : openUnionEdgeCovered U V p side a c :=
      ⟨hac, fun _ hz ↦ hab.2
        (rangeSubpath_mono p a a c b le_rfl hac hcb hz)⟩
    have hright : openUnionEdgeCovered U V p side c b :=
      ⟨hcb, fun _ hz ↦ hab.2
        (rangeSubpath_mono p a c b b hac hcb le_rfl hz)⟩
    -- The existing local splitting formulas have exactly the reverse-product
    -- orientation used by `Subdivision.value`.
    cases side
    · rw [openUnionCoveredEdgeValue_eq_left S p a b hab,
        openUnionCoveredEdgeValue_eq_left S p c b hright,
        openUnionCoveredEdgeValue_eq_left S p a c hleft]
      exact openUnionLeftCoveredSubpathValue_split S p a c b hac hcb hab.2
    · rw [openUnionCoveredEdgeValue_eq_right S p a b hab,
        openUnionCoveredEdgeValue_eq_right S p c b hright,
        openUnionCoveredEdgeValue_eq_right S p a c hleft]
      exact openUnionRightCoveredSubpathValue_split S p a c b hac hcb hab.2
  · intro side₁ side₂ a b h₁ h₂
    -- Equal labels are immediate; opposite labels force the whole edge into
    -- the intersection and invoke compatibility of the two local functors.
    cases side₁ <;> cases side₂
    · rw [openUnionCoveredEdgeValue_eq_left S p a b h₁]
    · rw [openUnionCoveredEdgeValue_eq_left S p a b h₁,
        openUnionCoveredEdgeValue_eq_right S p a b h₂]
      exact openUnionCoveredSubpathValues_agree S p a b h₁.1
        (fun _ hz ↦ ⟨h₁.2 hz, h₂.2 hz⟩)
    · rw [openUnionCoveredEdgeValue_eq_right S p a b h₁,
        openUnionCoveredEdgeValue_eq_left S p a b h₂]
      exact (openUnionCoveredSubpathValues_agree S p a b h₁.1
        (fun _ hz ↦ ⟨h₂.2 hz, h₁.2 hz⟩)).symm
    · rw [openUnionCoveredEdgeValue_eq_right S p a b h₁]

/-- Helper for Theorem 70.1: every recorded subdivision edge satisfies the
proof-independent coverage predicate. -/
private lemma OpenUnionPathSubdivision.edgeCovered
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x y : X}
    {p : Path x y} (D : OpenUnionPathSubdivision U V p)
    (i : Fin (D.n + 1)) :
    openUnionEdgeCovered U V p (D.side i)
      (D.point i.castSucc) (D.point i.succ) := by
  -- Combine monotonicity of adjacent endpoints with the stored cover field.
  exact ⟨D.point_castSucc_le_point_succ i, D.covered i⟩

/-- Helper for Theorem 70.1: convert the concrete finite endpoint sequence to
the recursive subdivision representation used by the refinement theorem. -/
private noncomputable def OpenUnionPathSubdivision.toFinite
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x y : X}
    {p : Path x y} (D : OpenUnionPathSubdivision U V p) :
    FiniteCoveredSubdivision.Subdivision (openUnionEdgeCovered U V p) 0 1 :=
  D.start ▸ D.finish ▸
    FiniteCoveredSubdivision.Subdivision.ofFin D.point D.monotone D.side D.edgeCovered

/-- Helper for Theorem 70.1: evaluate a covered subdivision using the unique
recursive reverse-product representation. -/
private noncomputable def OpenUnionPathSubdivision.value
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    {x y : X} {p : Path x y} (D : OpenUnionPathSubdivision U V p) : H :=
  D.toFinite.value (openUnionCoveredEdgeValue S p)

/-- Helper for Theorem 70.1: transport a covered subdivision along an equality
of ambient paths. -/
private def OpenUnionPathSubdivision.cast
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x y : X}
    {p q : Path x y} (D : OpenUnionPathSubdivision U V p) (h : p = q) :
    OpenUnionPathSubdivision U V q :=
  h ▸ D

/-- Helper for Theorem 70.1: transporting a covered subdivision along a path
equality does not change its proof-independent value. -/
private lemma OpenUnionPathSubdivision.value_cast
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    {x y : X} {p q : Path x y} (D : OpenUnionPathSubdivision U V p)
    (h : p = q) : (D.cast h).value S = D.value S := by
  -- Reflexive path transport leaves the subdivision and its value unchanged.
  cases h
  rfl

/-- Helper for Theorem 70.1: covered-subdivision evaluation is independent of
all subdivision points and cover labels. -/
private lemma OpenUnionPathSubdivision.value_eq
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    {x y : X} {p : Path x y}
    (D₁ D₂ : OpenUnionPathSubdivision U V p) : D₁.value S = D₂.value S := by
  -- Both concrete subdivisions now inhabit the same `0`-to-`1` recursive type.
  exact FiniteCoveredSubdivision.Subdivision.value_eq
    (openUnionCoveredEdgeLaws S p) D₁.toFinite D₂.toFinite

/-- Helper for Theorem 70.1: the value of a concrete covered subdivision is
the reverse finite product of its proof-independent edge values. -/
private lemma OpenUnionPathSubdivision.value_eq_reverseFinProd
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    {x y : X} {p : Path x y} (D : OpenUnionPathSubdivision U V p) :
    D.value S = FiniteCoveredSubdivision.reverseFinProd
      (fun i ↦ openUnionCoveredEdgeValue S p (D.side i)
        (D.point i.castSucc) (D.point i.succ)) := by
  -- Eliminate only the two endpoint transports, then use the owner formula
  -- for `Subdivision.ofFin`.
  unfold OpenUnionPathSubdivision.value OpenUnionPathSubdivision.toFinite
  calc
    _ = (FiniteCoveredSubdivision.Subdivision.ofFin D.point D.monotone
        D.side D.edgeCovered).value (openUnionCoveredEdgeValue S p) :=
      FiniteCoveredSubdivision.Subdivision.value_cast
        (openUnionCoveredEdgeValue S p)
        (FiniteCoveredSubdivision.Subdivision.ofFin D.point D.monotone
          D.side D.edgeCovered) D.start D.finish
    _ = _ := FiniteCoveredSubdivision.Subdivision.value_ofFin
      (openUnionCoveredEdgeValue S p) D.point D.monotone D.side D.edgeCovered

/-- Helper for Theorem 70.1: restricting the time coordinate of a homotopy
preserves continuity. -/
private lemma homotopyTimeSubpath_continuous
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (F : f.Homotopy g) (a b : unitInterval) :
    Continuous (fun z : unitInterval × X ↦
      F (Set.Icc.convexComb a b z.1, z.2)) := by
  -- Compose the original homotopy with affine reparameterization in time.
  exact F.continuous.comp
    (((Set.Icc.continuous_convexComb a b).comp continuous_fst).prodMk
      continuous_snd)

/-- Helper for Theorem 70.1: a homotopy restricted to a time subinterval. -/
private def homotopyTimeSubpath
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (F : f.Homotopy g) (a b : unitInterval) :
    (F.curry a).Homotopy (F.curry b) :=
  { toFun := fun z ↦ F (Set.Icc.convexComb a b z.1, z.2)
    continuous_toFun := homotopyTimeSubpath_continuous F a b
    map_zero_left := fun _ ↦ congrArg (fun t ↦ F (t, _))
      (Set.Icc.convexComb_zero a b)
    map_one_left := fun _ ↦ congrArg (fun t ↦ F (t, _))
      (Set.Icc.convexComb_one a b) }

/-- Helper for Theorem 70.1: opposite broken boundary paths of a reparameterized
homotopy cell are path homotopic. -/
private lemma homotopyCell_boundary_homotopic
    {X : Type*} [TopologicalSpace X] {x y : X} {p q : Path x y}
    (F : Path.Homotopy p q) (a b c d : unitInterval) :
    (((F.eval a).subpath c d).trans
        ((F.toHomotopy.evalAt d).subpath a b)).Homotopic
      (((F.toHomotopy.evalAt c).subpath a b).trans
        ((F.eval b).subpath c d)) := by
  -- Naturality for the restricted map homotopy is precisely the square's two
  -- bottom-right and left-top boundary traversals.
  have h := Path.Homotopic.map_trans_evalAt
    (homotopyTimeSubpath F.toHomotopy a b)
    (unitInterval.path01.subpath c d)
  have hbottom :
      (unitInterval.path01.subpath c d).map
          (map_continuous (F.toHomotopy.curry a)) =
        (F.eval a).subpath c d := by
    ext t
    rfl
  have htop :
      (unitInterval.path01.subpath c d).map
          (map_continuous (F.toHomotopy.curry b)) =
        (F.eval b).subpath c d := by
    ext t
    rfl
  have hleft :
      (homotopyTimeSubpath F.toHomotopy a b).evalAt
          (unitInterval.path01 c) =
        (F.toHomotopy.evalAt c).subpath a b := by
    ext t
    rfl
  have hright :
      (homotopyTimeSubpath F.toHomotopy a b).evalAt
          (unitInterval.path01 d) =
        (F.toHomotopy.evalAt d).subpath a b := by
    ext t
    rfl
  rw [hbottom, htop, hleft, hright] at h
  exact h

/-- Helper for Theorem 70.1: every affine parameter pair in a subordinate
homotopy cell maps into its selected subspace. -/
private lemma homotopyCellPoint_mem
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    {p q : Path x y} (F : Path.Homotopy p q)
    (a b c d : unitInterval) (hab : a ≤ b) (hcd : c ≤ d)
    (hcell : Set.MapsTo F (Set.Icc a b ×ˢ Set.Icc c d) A)
    (z : unitInterval × unitInterval) :
    F (Set.Icc.convexComb a b z.1, Set.Icc.convexComb c d z.2) ∈ A := by
  -- Convex combinations remain in their two coordinate intervals.
  apply hcell
  exact ⟨⟨Set.Icc.le_convexComb hab z.1, Set.Icc.convexComb_le hab z.1⟩,
    ⟨Set.Icc.le_convexComb hcd z.2, Set.Icc.convexComb_le hcd z.2⟩⟩

/-- Helper for Theorem 70.1: the affine reparameterization of a subordinate
homotopy cell is continuous as a map into the selected subspace. -/
private lemma homotopyCellCodRestrict_continuous
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    {p q : Path x y} (F : Path.Homotopy p q)
    (a b c d : unitInterval) (hab : a ≤ b) (hcd : c ≤ d)
    (hcell : Set.MapsTo F (Set.Icc a b ×ˢ Set.Icc c d) A) :
    Continuous (fun z : unitInterval × unitInterval ↦
      (⟨F (Set.Icc.convexComb a b z.1, Set.Icc.convexComb c d z.2),
        homotopyCellPoint_mem F a b c d hab hcd hcell z⟩ : A)) := by
  -- Compose continuity of `F` with both affine coordinate maps, then use the
  -- subtype continuity criterion.
  exact (F.continuous.comp
    (((Set.Icc.continuous_convexComb a b).comp continuous_fst).prodMk
      ((Set.Icc.continuous_convexComb c d).comp continuous_snd))).subtype_mk _

/-- Helper for Theorem 70.1: a subordinate rectangle, affinely
reparameterized to the unit square and restricted to its cover member. -/
private def homotopyCellCodRestrictMap
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    {p q : Path x y} (F : Path.Homotopy p q)
    (a b c d : unitInterval) (hab : a ≤ b) (hcd : c ≤ d)
    (hcell : Set.MapsTo F (Set.Icc a b ×ˢ Set.Icc c d) A) :
    C(unitInterval × unitInterval, A) :=
  ⟨fun z ↦
      ⟨F (Set.Icc.convexComb a b z.1, Set.Icc.convexComb c d z.2),
        homotopyCellPoint_mem F a b c d hab hcd hcell z⟩,
    homotopyCellCodRestrict_continuous F a b c d hab hcd hcell⟩

/-- Helper for Theorem 70.1: the restricted cell is a map homotopy between
its bottom and top horizontal boundary maps. -/
private def homotopyCellCodRestrict
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    {p q : Path x y} (F : Path.Homotopy p q)
    (a b c d : unitInterval) (hab : a ≤ b) (hcd : c ≤ d)
    (hcell : Set.MapsTo F (Set.Icc a b ×ˢ Set.Icc c d) A) :
    ((homotopyCellCodRestrictMap F a b c d hab hcd hcell).curry 0).Homotopy
      ((homotopyCellCodRestrictMap F a b c d hab hcd hcell).curry 1) :=
  { toContinuousMap := homotopyCellCodRestrictMap F a b c d hab hcd hcell
    map_zero_left := fun _ ↦ rfl
    map_one_left := fun _ ↦ rfl }

/-- Helper for Theorem 70.1: a horizontal side of a subordinate cell remains
inside its selected cover member. -/
private lemma homotopyCell_horizontal_range_subset
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    {p q : Path x y} (F : Path.Homotopy p q)
    (a b c d t : unitInterval) (_hab : a ≤ b) (hcd : c ≤ d)
    (ht : t ∈ Set.Icc a b)
    (hcell : Set.MapsTo F (Set.Icc a b ×ˢ Set.Icc c d) A) :
    Set.range ((F.eval t).subpath c d) ⊆ A := by
  -- Rewrite the subpath range and apply cell containment at fixed time `t`.
  rw [Path.range_subpath_of_le _ _ _ hcd]
  rintro _ ⟨s, hs, rfl⟩
  exact hcell ⟨ht, hs⟩

/-- Helper for Theorem 70.1: a vertical side of a subordinate cell remains
inside its selected cover member. -/
private lemma homotopyCell_vertical_range_subset
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    {p q : Path x y} (F : Path.Homotopy p q)
    (a b c d s : unitInterval) (hab : a ≤ b) (_hcd : c ≤ d)
    (hs : s ∈ Set.Icc c d)
    (hcell : Set.MapsTo F (Set.Icc a b ×ˢ Set.Icc c d) A) :
    Set.range ((F.toHomotopy.evalAt s).subpath a b) ⊆ A := by
  -- The same range computation now fixes the path coordinate `s`.
  rw [Path.range_subpath_of_le _ _ _ hab]
  rintro _ ⟨t, ht, rfl⟩
  exact hcell ⟨ht, hs⟩

/-- Helper for Theorem 70.1: a horizontal boundary segment of a subordinate
cell, restricted to the selected subspace. -/
private def homotopyCellHorizontalPath
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    {p q : Path x y} (F : Path.Homotopy p q)
    (a b c d t : unitInterval) (hab : a ≤ b) (hcd : c ≤ d)
    (ht : t ∈ Set.Icc a b)
    (hcell : Set.MapsTo F (Set.Icc a b ×ˢ Set.Icc c d) A) :
    Path
      (coveredSubpathPoint (F.eval t) c d
        (homotopyCell_horizontal_range_subset F a b c d t hab hcd ht hcell)
        c le_rfl hcd)
      (coveredSubpathPoint (F.eval t) c d
        (homotopyCell_horizontal_range_subset F a b c d t hab hcd ht hcell)
        d hcd le_rfl) :=
  pathCodRestrict ((F.eval t).subpath c d)
    (homotopyCell_horizontal_range_subset F a b c d t hab hcd ht hcell)

/-- Helper for Theorem 70.1: a vertical boundary segment of a subordinate
cell, restricted to the selected subspace. -/
private def homotopyCellVerticalPath
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    {p q : Path x y} (F : Path.Homotopy p q)
    (a b c d s : unitInterval) (hab : a ≤ b) (hcd : c ≤ d)
    (hs : s ∈ Set.Icc c d)
    (hcell : Set.MapsTo F (Set.Icc a b ×ˢ Set.Icc c d) A) :
    Path
      (coveredSubpathPoint (F.toHomotopy.evalAt s) a b
        (homotopyCell_vertical_range_subset F a b c d s hab hcd hs hcell)
        a le_rfl hab)
      (coveredSubpathPoint (F.toHomotopy.evalAt s) a b
        (homotopyCell_vertical_range_subset F a b c d s hab hcd hs hcell)
        b hab le_rfl) :=
  pathCodRestrict ((F.toHomotopy.evalAt s).subpath a b)
    (homotopyCell_vertical_range_subset F a b c d s hab hcd hs hcell)

/-- Helper for Theorem 70.1: the bottom horizontal map of a subordinate cell
takes the cell's parameter interval into the selected subspace. -/
private lemma homotopyCellBottomPoint_mem
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    {p q : Path x y} (F : Path.Homotopy p q)
    (a b c d : unitInterval) (hab : a ≤ b)
    (hcell : Set.MapsTo F (Set.Icc a b ×ˢ Set.Icc c d) A)
    (s : Set.Icc c d) : F (a, s.1) ∈ A := by
  -- The bottom time and the interval point lie in the cell rectangle.
  exact hcell ⟨⟨le_rfl, hab⟩, s.2⟩

/-- Helper for Theorem 70.1: the top horizontal map of a subordinate cell
takes the cell's parameter interval into the selected subspace. -/
private lemma homotopyCellTopPoint_mem
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    {p q : Path x y} (F : Path.Homotopy p q)
    (a b c d : unitInterval) (hab : a ≤ b)
    (hcell : Set.MapsTo F (Set.Icc a b ×ˢ Set.Icc c d) A)
    (s : Set.Icc c d) : F (b, s.1) ∈ A := by
  -- The top time and the interval point lie in the same cell rectangle.
  exact hcell ⟨⟨hab, le_rfl⟩, s.2⟩

/-- Helper for Theorem 70.1: the bottom horizontal map into the selected
subspace is continuous. -/
private lemma homotopyCellBottomMap_continuous
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    {p q : Path x y} (F : Path.Homotopy p q)
    (a b c d : unitInterval) (hab : a ≤ b)
    (hcell : Set.MapsTo F (Set.Icc a b ×ˢ Set.Icc c d) A) :
    Continuous (fun s : Set.Icc c d ↦
      (⟨F (a, s.1), homotopyCellBottomPoint_mem F a b c d hab hcell s⟩ : A)) := by
  -- Fix the time coordinate and restrict the continuous slice to the subtype.
  exact (F.continuous.comp
    (continuous_const.prodMk continuous_subtype_val)).subtype_mk _

/-- Helper for Theorem 70.1: the top horizontal map into the selected
subspace is continuous. -/
private lemma homotopyCellTopMap_continuous
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    {p q : Path x y} (F : Path.Homotopy p q)
    (a b c d : unitInterval) (hab : a ≤ b)
    (hcell : Set.MapsTo F (Set.Icc a b ×ˢ Set.Icc c d) A) :
    Continuous (fun s : Set.Icc c d ↦
      (⟨F (b, s.1), homotopyCellTopPoint_mem F a b c d hab hcell s⟩ : A)) := by
  -- Fix the top time coordinate and apply the same subtype criterion.
  exact (F.continuous.comp
    (continuous_const.prodMk continuous_subtype_val)).subtype_mk _

/-- Helper for Theorem 70.1: the bottom horizontal slice of a subordinate
cell, regarded as a continuous map between subspaces. -/
private def homotopyCellBottomMap
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    {p q : Path x y} (F : Path.Homotopy p q)
    (a b c d : unitInterval) (hab : a ≤ b)
    (hcell : Set.MapsTo F (Set.Icc a b ×ˢ Set.Icc c d) A) :
    C(Set.Icc c d, A) :=
  ⟨fun s ↦ ⟨F (a, s.1),
      homotopyCellBottomPoint_mem F a b c d hab hcell s⟩,
    homotopyCellBottomMap_continuous F a b c d hab hcell⟩

/-- Helper for Theorem 70.1: the top horizontal slice of a subordinate cell,
regarded as a continuous map between subspaces. -/
private def homotopyCellTopMap
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    {p q : Path x y} (F : Path.Homotopy p q)
    (a b c d : unitInterval) (hab : a ≤ b)
    (hcell : Set.MapsTo F (Set.Icc a b ×ˢ Set.Icc c d) A) :
    C(Set.Icc c d, A) :=
  ⟨fun s ↦ ⟨F (b, s.1),
      homotopyCellTopPoint_mem F a b c d hab hcell s⟩,
    homotopyCellTopMap_continuous F a b c d hab hcell⟩

/-- Helper for Theorem 70.1: the time-restricted homotopy is continuous on the
cell's parameter interval with values in the selected subspace. -/
private lemma homotopyCellInterval_continuous
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    {p q : Path x y} (F : Path.Homotopy p q)
    (a b c d : unitInterval) (hab : a ≤ b)
    (hcell : Set.MapsTo F (Set.Icc a b ×ˢ Set.Icc c d) A) :
    Continuous (fun z : unitInterval × Set.Icc c d ↦
      (⟨F (Set.Icc.convexComb a b z.1, z.2.1),
        hcell ⟨⟨Set.Icc.le_convexComb hab z.1,
          Set.Icc.convexComb_le hab z.1⟩, z.2.2⟩⟩ : A)) := by
  -- Reparameterize time while leaving the interval-subtype coordinate fixed.
  exact (F.continuous.comp
    (((Set.Icc.continuous_convexComb a b).comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _

/-- Helper for Theorem 70.1: the time-restricted cell homotopy on the exact
parameter interval, avoiding endpoint transports. -/
private def homotopyCellInterval
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    {p q : Path x y} (F : Path.Homotopy p q)
    (a b c d : unitInterval) (hab : a ≤ b)
    (hcell : Set.MapsTo F (Set.Icc a b ×ˢ Set.Icc c d) A) :
    (homotopyCellBottomMap F a b c d hab hcell).Homotopy
      (homotopyCellTopMap F a b c d hab hcell) :=
  { toFun := fun z ↦
      ⟨F (Set.Icc.convexComb a b z.1, z.2.1),
        hcell ⟨⟨Set.Icc.le_convexComb hab z.1,
          Set.Icc.convexComb_le hab z.1⟩, z.2.2⟩⟩
    continuous_toFun := homotopyCellInterval_continuous F a b c d hab hcell
    map_zero_left := fun _ ↦ Subtype.ext (congrArg (fun t ↦ F (t, _))
      (Set.Icc.convexComb_zero a b))
    map_one_left := fun _ ↦ Subtype.ext (congrArg (fun t ↦ F (t, _))
      (Set.Icc.convexComb_one a b)) }

/-- Helper for Theorem 70.1: the canonical path across an ordered parameter
interval has range in that interval subtype. -/
private lemma unitIntervalSubpath_range_subset_Icc
    (c d : unitInterval) (hcd : c ≤ d) :
    Set.range (unitInterval.path01.subpath c d) ⊆ Set.Icc c d := by
  -- The identity path sends the parameter interval to itself.
  rw [Path.range_subpath_of_le _ _ _ hcd]
  rintro _ ⟨s, hs, rfl⟩
  exact hs

/-- Helper for Theorem 70.1: the canonical path from the left to the right
endpoint inside an ordered parameter interval. -/
private def unitIntervalSubpathInIcc (c d : unitInterval) (hcd : c ≤ d) :
    Path (⟨c, le_rfl, hcd⟩ : Set.Icc c d)
      (⟨d, hcd, le_rfl⟩ : Set.Icc c d) :=
  pathCodRestrict (unitInterval.path01.subpath c d)
    (unitIntervalSubpath_range_subset_Icc c d hcd)

/-- Helper for Theorem 70.1: after codomain restriction, the two broken
boundary paths of a subordinate cell remain homotopic. -/
private lemma homotopyCellCodRestricted_boundary_homotopic
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    {p q : Path x y} (F : Path.Homotopy p q)
    (a b c d : unitInterval) (hab : a ≤ b) (hcd : c ≤ d)
    (hcell : Set.MapsTo F (Set.Icc a b ×ˢ Set.Icc c d) A) :
    ((homotopyCellHorizontalPath F a b c d a hab hcd
        ⟨le_rfl, hab⟩ hcell).trans
      (homotopyCellVerticalPath F a b c d d hab hcd
        ⟨hcd, le_rfl⟩ hcell)).Homotopic
      ((homotopyCellVerticalPath F a b c d c hab hcd
          ⟨le_rfl, hcd⟩ hcell).trans
        (homotopyCellHorizontalPath F a b c d b hab hcd
          ⟨hab, le_rfl⟩ hcell)) := by
  let C := homotopyCellInterval F a b c d hab hcell
  let r := unitIntervalSubpathInIcc c d hcd
  have hsquare := Path.Homotopic.map_trans_evalAt C r
  -- Normalize each boundary once, keeping endpoint transports out of the
  -- final cell-value theorem.
  have hbottom :
      r.map (map_continuous (homotopyCellBottomMap F a b c d hab hcell)) =
        homotopyCellHorizontalPath F a b c d a hab hcd
          ⟨le_rfl, hab⟩ hcell := by
    ext t
    rfl
  have htop :
      r.map (map_continuous (homotopyCellTopMap F a b c d hab hcell)) =
        homotopyCellHorizontalPath F a b c d b hab hcd
          ⟨hab, le_rfl⟩ hcell := by
    ext t
    rfl
  have hleft :
      C.evalAt (⟨c, le_rfl, hcd⟩ : Set.Icc c d) =
        homotopyCellVerticalPath F a b c d c hab hcd
          ⟨le_rfl, hcd⟩ hcell := by
    ext t
    rfl
  have hright :
      C.evalAt (⟨d, hcd, le_rfl⟩ : Set.Icc c d) =
        homotopyCellVerticalPath F a b c d d hab hcd
          ⟨hcd, le_rfl⟩ hcell := by
    ext t
    rfl
  change
    ((r.map (map_continuous (homotopyCellBottomMap F a b c d hab hcell))).trans
      (C.evalAt (⟨d, hcd, le_rfl⟩ : Set.Icc c d))).Homotopic
      ((C.evalAt (⟨c, le_rfl, hcd⟩ : Set.Icc c d)).trans
        (r.map (map_continuous
          (homotopyCellTopMap F a b c d hab hcell)))) at hsquare
  rwa [hbottom, htop, hleft, hright] at hsquare

/-- Helper for Theorem 70.1: homotopic broken sides of a square have the
oriented value relation under every one-object-valued groupoid functor. -/
private lemma functorValue_square_of_homotopic
    {A : Type*} [TopologicalSpace A] {H : Type*} [Group H]
    (L : FundamentalGroupoid A ⥤ CategoryTheory.SingleObj H)
    {w x y z : A} (bottom : Path w x) (right : Path x z)
    (left : Path w y) (top : Path y z)
    (hsquare : (bottom.trans right).Homotopic (left.trans top)) :
    singleObjMorphismValue (L.map (Path.Homotopic.Quotient.mk right)) *
        singleObjMorphismValue (L.map (Path.Homotopic.Quotient.mk bottom)) =
      singleObjMorphismValue (L.map (Path.Homotopic.Quotient.mk top)) *
        singleObjMorphismValue (L.map (Path.Homotopic.Quotient.mk left)) := by
  -- First pass the boundary homotopy to path classes.
  have hclasses :
      Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.mk bottom)
          (Path.Homotopic.Quotient.mk right) =
        Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.mk left)
          (Path.Homotopic.Quotient.mk top) := by
    calc
      _ = Path.Homotopic.Quotient.mk (bottom.trans right) :=
        (Path.Homotopic.Quotient.mk_trans bottom right).symm
      _ = Path.Homotopic.Quotient.mk (left.trans top) := by
        rw [Path.Homotopic.Quotient.eq]
        exact hsquare
      _ = _ := Path.Homotopic.Quotient.mk_trans left top
  -- Functoriality reads composition as reverse multiplication in `SingleObj`.
  have hmapped := congrArg
    (fun r ↦ singleObjMorphismValue (L.map r)) hclasses
  calc
    _ = singleObjMorphismValue
        (L.map (Path.Homotopic.Quotient.mk bottom ≫
          Path.Homotopic.Quotient.mk right)) := by
      rw [L.map_comp]
      rfl
    _ = singleObjMorphismValue
        (L.map (Path.Homotopic.Quotient.mk left ≫
          Path.Homotopic.Quotient.mk top)) := hmapped
    _ = _ := by
      rw [L.map_comp]
      rfl

/-- Helper for Theorem 70.1: the value assigned by a groupoid functor to an
ordered ambient subpath restricted to a selected subspace. -/
private def coveredSubpathValue
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    {H : Type*} [Group H]
    (L : FundamentalGroupoid A ⥤ CategoryTheory.SingleObj H)
    (p : Path x y) (a b : unitInterval) (hab : a ≤ b)
    (hp : Set.range (p.subpath a b) ⊆ A) : H :=
  singleObjMorphismValue
    (L.map (codRestrictedNestedSubpathClass p a a b b le_rfl hab le_rfl hp))

/-- Helper for Theorem 70.1: the nested-subpath spelling of a covered value
agrees propositionally with direct codomain restriction. -/
private lemma coveredSubpathValue_eq_restrictedPath
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    {H : Type*} [Group H]
    (L : FundamentalGroupoid A ⥤ CategoryTheory.SingleObj H)
    (p : Path x y) (a b : unitInterval) (hab : a ≤ b)
    (hp : Set.range (p.subpath a b) ⊆ A) :
    coveredSubpathValue L p a b hab hp =
      singleObjMorphismValue
        (L.map (Path.Homotopic.Quotient.mk
          (pathCodRestrict
            (x := coveredSubpathPoint p a b hp a le_rfl hab)
            (y := coveredSubpathPoint p a b hp b hab le_rfl)
            (p.subpath a b) hp))) := by
  -- Push the comparison to path values instead of relying on definitional
  -- equality of the two subtype-membership witnesses.
  unfold coveredSubpathValue codRestrictedNestedSubpathClass
  apply congrArg singleObjMorphismValue
  apply congrArg (fun r ↦ L.map r)
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

/-- Helper for Theorem 70.1: a one-object-valued fundamental-groupoid
functor assigns equal values to paths that agree after forgetting a subtype. -/
private lemma singleObjFunctorPathValue_eq_of_coe
    {X : Type*} [TopologicalSpace X] {A : Set X}
    {H : Type*} [Group H]
    (L : FundamentalGroupoid A ⥤ CategoryTheory.SingleObj H)
    {x y x' y' : A} (p : Path x y) (q : Path x' y')
    (hcoe : ∀ t, (p t : X) = q t) :
    singleObjMorphismValue (L.map (Path.Homotopic.Quotient.mk p)) =
      singleObjMorphismValue (L.map (Path.Homotopic.Quotient.mk q)) := by
  -- Endpoint equality first puts both paths in one hom type; pointwise
  -- subtype extensionality then identifies their quotient representatives.
  have hx : x = x' := by
    apply Subtype.ext
    simpa only [Path.source] using hcoe 0
  have hy : y = y' := by
    apply Subtype.ext
    simpa only [Path.target] using hcoe 1
  subst x'
  subst y'
  have hpq : p = q := by
    ext t
    exact hcoe t
  subst q
  rfl

/-- Helper for Theorem 70.1: a left-covered edge value is the local functor
value of its direct codomain restriction. -/
private lemma openUnionCoveredEdgeValue_eq_left_restricted
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    {x y : X} (p : Path x y) (a b : unitInterval)
    (h : openUnionEdgeCovered U V p false a b) :
    openUnionCoveredEdgeValue S p false a b =
      singleObjMorphismValue
        (S.left.map (Path.Homotopic.Quotient.mk
          (pathCodRestrict
            (x := coveredSubpathPoint p a b h.2 a le_rfl h.1)
            (y := coveredSubpathPoint p a b h.2 b h.1 le_rfl)
            (p.subpath a b) h.2))) := by
  -- First expose the nested-subpath value selected by the edge evaluator,
  -- then use its proof-independent direct-restriction bridge.
  rw [openUnionCoveredEdgeValue_eq_left S p a b h]
  exact coveredSubpathValue_eq_restrictedPath S.left p a b h.1 h.2

/-- Helper for Theorem 70.1: a right-covered edge value is the local functor
value of its direct codomain restriction. -/
private lemma openUnionCoveredEdgeValue_eq_right_restricted
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    {x y : X} (p : Path x y) (a b : unitInterval)
    (h : openUnionEdgeCovered U V p true a b) :
    openUnionCoveredEdgeValue S p true a b =
      singleObjMorphismValue
        (S.right.map (Path.Homotopic.Quotient.mk
          (pathCodRestrict
            (x := coveredSubpathPoint p a b h.2 a le_rfl h.1)
            (y := coveredSubpathPoint p a b h.2 b h.1 le_rfl)
            (p.subpath a b) h.2))) := by
  -- The right branch has the same direct-restriction normal form.
  rw [openUnionCoveredEdgeValue_eq_right S p a b h]
  exact coveredSubpathValue_eq_restrictedPath S.right p a b h.1 h.2

/-- Helper for Theorem 70.1: the midpoint of the unit interval is a valid
subdivision parameter. -/
private lemma openUnionMidpoint_mem : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  -- Both endpoint inequalities are numerical.
  norm_num

/-- Helper for Theorem 70.1: the midpoint used to join the two rescaled
subdivisions. -/
private noncomputable def openUnionMidpoint : unitInterval :=
  ⟨1 / 2, openUnionMidpoint_mem⟩

/-- Helper for Theorem 70.1: halving a unit-interval parameter remains in the
unit interval. -/
private lemma openUnionLeftHalf_mem (t : unitInterval) :
    (t / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  -- Scale the two bounds on `t` by the positive denominator.
  constructor <;> nlinarith [t.property.1, t.property.2]

/-- Helper for Theorem 70.1: affine reparameterization onto the left half of
the unit interval. -/
private noncomputable def openUnionLeftHalf : unitInterval → unitInterval :=
  fun t ↦ ⟨t / 2, openUnionLeftHalf_mem t⟩

/-- Helper for Theorem 70.1: shifting and halving a unit-interval parameter
remains in the unit interval. -/
private lemma openUnionRightHalf_mem (t : unitInterval) :
    ((t + 1) / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  -- Translate the endpoint bounds before scaling by two.
  constructor <;> nlinarith [t.property.1, t.property.2]

/-- Helper for Theorem 70.1: affine reparameterization onto the right half of
the unit interval. -/
private noncomputable def openUnionRightHalf : unitInterval → unitInterval :=
  fun t ↦ ⟨(t + 1) / 2, openUnionRightHalf_mem t⟩

/-- Helper for Theorem 70.1: the left-half affine map is monotone. -/
private lemma openUnionLeftHalf_monotone : Monotone openUnionLeftHalf := by
  -- Division by the positive scalar two preserves order.
  intro a b hab
  change (a : ℝ) / 2 ≤ (b : ℝ) / 2
  exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 hab

/-- Helper for Theorem 70.1: the right-half affine map is monotone. -/
private lemma openUnionRightHalf_monotone : Monotone openUnionRightHalf := by
  -- The same positive affine transformation preserves order.
  intro a b hab
  change ((a : ℝ) + 1) / 2 ≤ ((b : ℝ) + 1) / 2
  apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2
  simpa only [add_comm] using
    add_le_add_right (show (a : ℝ) ≤ (b : ℝ) from hab) 1

/-- Helper for Theorem 70.1: the left-half affine map begins at zero. -/
private lemma openUnionLeftHalf_zero : openUnionLeftHalf 0 = 0 := by
  -- Evaluate the affine formula at the left endpoint.
  exact Subtype.ext (by norm_num [openUnionLeftHalf])

/-- Helper for Theorem 70.1: the left-half affine map ends at the midpoint. -/
private lemma openUnionLeftHalf_one : openUnionLeftHalf 1 = openUnionMidpoint := by
  -- Evaluate the affine formula at the right endpoint.
  exact Subtype.ext (by norm_num [openUnionLeftHalf, openUnionMidpoint])

/-- Helper for Theorem 70.1: the right-half affine map begins at the midpoint. -/
private lemma openUnionRightHalf_zero : openUnionRightHalf 0 = openUnionMidpoint := by
  -- Evaluate the affine formula at the left endpoint.
  exact Subtype.ext (by norm_num [openUnionRightHalf, openUnionMidpoint])

/-- Helper for Theorem 70.1: the right-half affine map ends at one. -/
private lemma openUnionRightHalf_one : openUnionRightHalf 1 = 1 := by
  -- Evaluate the affine formula at the right endpoint.
  exact Subtype.ext (by norm_num [openUnionRightHalf])

/-- Helper for Theorem 70.1: restricting a concatenated path to rescaled
parameters in its left half recovers the corresponding subpath of the first
factor. -/
private lemma trans_subpath_leftHalf_apply
    {X : Type*} [TopologicalSpace X] {x y z : X}
    (p : Path x y) (q : Path y z) (a b t : unitInterval) :
    (p.trans q).subpath (openUnionLeftHalf a) (openUnionLeftHalf b) t =
      p.subpath a b t := by
  -- Move to path extensions, where concatenation has a directed computation
  -- rule on the left half, and normalize the affine parameters once.
  change (p.trans q)
      (Set.Icc.convexComb (openUnionLeftHalf a) (openUnionLeftHalf b) t) =
    p (Set.Icc.convexComb a b t)
  let s := Set.Icc.convexComb (openUnionLeftHalf a) (openUnionLeftHalf b) t
  let r := Set.Icc.convexComb a b t
  have hs : (s : ℝ) ≤ 1 / 2 := by
    simp only [s, Set.Icc.coe_convexComb, openUnionLeftHalf]
    nlinarith [a.property.1, a.property.2, b.property.1, b.property.2,
      t.property.1, t.property.2]
  have hscale : 2 * (s : ℝ) = (r : ℝ) := by
    simp only [s, r, Set.Icc.coe_convexComb, openUnionLeftHalf]
    ring
  rw [← Path.extend_apply (p.trans q) s.property,
    Path.extend_trans_of_le_half p q hs, hscale,
    Path.extend_apply p r.property]

/-- Helper for Theorem 70.1: restricting a concatenated path to rescaled
parameters in its right half recovers the corresponding subpath of the second
factor. -/
private lemma trans_subpath_rightHalf_apply
    {X : Type*} [TopologicalSpace X] {x y z : X}
    (p : Path x y) (q : Path y z) (a b t : unitInterval) :
    (p.trans q).subpath (openUnionRightHalf a) (openUnionRightHalf b) t =
      q.subpath a b t := by
  -- Use the right-half extension rule and reduce its affine expression to the
  -- original subpath parameter.
  change (p.trans q)
      (Set.Icc.convexComb (openUnionRightHalf a) (openUnionRightHalf b) t) =
    q (Set.Icc.convexComb a b t)
  let s := Set.Icc.convexComb (openUnionRightHalf a) (openUnionRightHalf b) t
  let r := Set.Icc.convexComb a b t
  have hs : 1 / 2 ≤ (s : ℝ) := by
    simp only [s, Set.Icc.coe_convexComb, openUnionRightHalf]
    nlinarith [a.property.1, a.property.2, b.property.1, b.property.2,
      t.property.1, t.property.2]
  have hscale : 2 * (s : ℝ) - 1 = (r : ℝ) := by
    simp only [s, r, Set.Icc.coe_convexComb, openUnionRightHalf]
    ring
  rw [← Path.extend_apply (p.trans q) s.property,
    Path.extend_trans_of_half_le p q hs, hscale,
    Path.extend_apply q r.property]

/-- Helper for Theorem 70.1: pointwise equality of two ordered subpaths
transports both cover membership and the proof-independent edge value. -/
private lemma openUnionCoveredEdge_transport
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    {x y x' y' : X} (p : Path x y) (q : Path x' y')
    (side : Bool) (a b c d : unitInterval)
    (hp : openUnionEdgeCovered U V p side a b) (hcd : c ≤ d)
    (hsub : ∀ t, q.subpath c d t = p.subpath a b t) :
    openUnionEdgeCovered U V q side c d ∧
      openUnionCoveredEdgeValue S q side c d =
        openUnionCoveredEdgeValue S p side a b := by
  -- Pointwise equality transports the range containment without rewriting
  -- any dependent proof; the local functor value follows from the same path
  -- comparison after codomain restriction.
  have hqRange : Set.range (q.subpath c d) ⊆ if side then V else U := by
    rintro w ⟨t, rfl⟩
    exact hp.2 ⟨t, (hsub t).symm⟩
  let hq : openUnionEdgeCovered U V q side c d := ⟨hcd, hqRange⟩
  refine ⟨hq, ?_⟩
  cases side
  · rw [openUnionCoveredEdgeValue_eq_left_restricted S q c d hq,
      openUnionCoveredEdgeValue_eq_left_restricted S p a b hp]
    apply singleObjFunctorPathValue_eq_of_coe
    intro t
    exact hsub t
  · rw [openUnionCoveredEdgeValue_eq_right_restricted S q c d hq,
      openUnionCoveredEdgeValue_eq_right_restricted S p a b hp]
    apply singleObjFunctorPathValue_eq_of_coe
    intro t
    exact hsub t

/-- Helper for Theorem 70.1: rescaling a covered edge into the left half of a
concatenated path preserves its cover label and value. -/
private lemma openUnionCoveredEdge_transport_leftHalf
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    {x y z : X} (p : Path x y) (q : Path y z)
    {side : Bool} {a b : unitInterval}
    (hp : openUnionEdgeCovered U V p side a b) :
    openUnionEdgeCovered U V (p.trans q) side
        (openUnionLeftHalf a) (openUnionLeftHalf b) ∧
      openUnionCoveredEdgeValue S (p.trans q) side
          (openUnionLeftHalf a) (openUnionLeftHalf b) =
        openUnionCoveredEdgeValue S p side a b := by
  -- Instantiate the generic transport bridge with the left affine subpath
  -- computation.
  exact openUnionCoveredEdge_transport S p (p.trans q) side a b
    (openUnionLeftHalf a) (openUnionLeftHalf b)
    hp (openUnionLeftHalf_monotone hp.1)
    (trans_subpath_leftHalf_apply p q a b)

/-- Helper for Theorem 70.1: rescaling a covered edge into the right half of a
concatenated path preserves its cover label and value. -/
private lemma openUnionCoveredEdge_transport_rightHalf
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    {x y z : X} (p : Path x y) (q : Path y z)
    {side : Bool} {a b : unitInterval}
    (hq : openUnionEdgeCovered U V q side a b) :
    openUnionEdgeCovered U V (p.trans q) side
        (openUnionRightHalf a) (openUnionRightHalf b) ∧
      openUnionCoveredEdgeValue S (p.trans q) side
          (openUnionRightHalf a) (openUnionRightHalf b) =
        openUnionCoveredEdgeValue S q side a b := by
  -- Instantiate the generic transport bridge with the right affine subpath
  -- computation.
  exact openUnionCoveredEdge_transport S q (p.trans q) side a b
    (openUnionRightHalf a) (openUnionRightHalf b)
    hq (openUnionRightHalf_monotone hq.1)
    (trans_subpath_rightHalf_apply p q a b)

/-- Helper for Theorem 70.1: the abstract covered-subpath value agrees with
the canonical horizontal path chosen for a homotopy cell. -/
private lemma coveredSubpathValue_eq_cellHorizontal
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    {p q : Path x y} {H : Type*} [Group H]
    (L : FundamentalGroupoid A ⥤ CategoryTheory.SingleObj H)
    (F : Path.Homotopy p q) (a b c d t : unitInterval)
    (hab : a ≤ b) (hcd : c ≤ d) (ht : t ∈ Set.Icc a b)
    (hcell : Set.MapsTo F (Set.Icc a b ×ˢ Set.Icc c d) A) :
    coveredSubpathValue L (F.eval t) c d hcd
        (homotopyCell_horizontal_range_subset F a b c d t hab hcd ht hcell) =
      singleObjMorphismValue
        (L.map (Path.Homotopic.Quotient.mk
          (homotopyCellHorizontalPath F a b c d t hab hcd ht hcell))) := by
  -- Use the direct-restriction bridge, then compare the two restricted paths
  -- pointwise so membership proofs do not enter definitional equality.
  rw [coveredSubpathValue_eq_restrictedPath]
  apply congrArg singleObjMorphismValue
  apply congrArg (fun r ↦ L.map r)
  apply congrArg Path.Homotopic.Quotient.mk
  ext s
  rfl

/-- Helper for Theorem 70.1: the abstract covered-subpath value agrees with
the canonical vertical path chosen for a homotopy cell. -/
private lemma coveredSubpathValue_eq_cellVertical
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    {p q : Path x y} {H : Type*} [Group H]
    (L : FundamentalGroupoid A ⥤ CategoryTheory.SingleObj H)
    (F : Path.Homotopy p q) (a b c d s : unitInterval)
    (hab : a ≤ b) (hcd : c ≤ d) (hs : s ∈ Set.Icc c d)
    (hcell : Set.MapsTo F (Set.Icc a b ×ˢ Set.Icc c d) A) :
    coveredSubpathValue L (F.toHomotopy.evalAt s) a b hab
        (homotopyCell_vertical_range_subset F a b c d s hab hcd hs hcell) =
      singleObjMorphismValue
        (L.map (Path.Homotopic.Quotient.mk
          (homotopyCellVerticalPath F a b c d s hab hcd hs hcell))) := by
  -- The vertical case uses the same pointwise bridge.
  rw [coveredSubpathValue_eq_restrictedPath]
  apply congrArg singleObjMorphismValue
  apply congrArg (fun r ↦ L.map r)
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

/-- Helper for Theorem 70.1: applying a one-object-valued groupoid functor to
a subordinate cell gives the oriented square relation. -/
private lemma homotopyCellValue_naturality
    {X : Type*} [TopologicalSpace X] {A : Set X} {x y : X}
    {p q : Path x y} {H : Type*} [Group H]
    (L : FundamentalGroupoid A ⥤ CategoryTheory.SingleObj H)
    (F : Path.Homotopy p q) (a b c d : unitInterval)
    (hab : a ≤ b) (hcd : c ≤ d)
    (hcell : Set.MapsTo F (Set.Icc a b ×ˢ Set.Icc c d) A) :
    coveredSubpathValue L (F.toHomotopy.evalAt d) a b hab
        (homotopyCell_vertical_range_subset F a b c d d hab hcd
          ⟨hcd, le_rfl⟩ hcell) *
      coveredSubpathValue L (F.eval a) c d hcd
        (homotopyCell_horizontal_range_subset F a b c d a hab hcd
          ⟨le_rfl, hab⟩ hcell) =
    coveredSubpathValue L (F.eval b) c d hcd
        (homotopyCell_horizontal_range_subset F a b c d b hab hcd
          ⟨hab, le_rfl⟩ hcell) *
      coveredSubpathValue L (F.toHomotopy.evalAt c) a b hab
        (homotopyCell_vertical_range_subset F a b c d c hab hcd
          ⟨le_rfl, hcd⟩ hcell) := by
  -- The generic functor square lemma now closes the cell equation without
  -- asking the elaborator to normalize all four quotient composites at once.
  calc
    _ = singleObjMorphismValue
          (L.map (Path.Homotopic.Quotient.mk
            (homotopyCellVerticalPath F a b c d d hab hcd
              ⟨hcd, le_rfl⟩ hcell))) *
        singleObjMorphismValue
          (L.map (Path.Homotopic.Quotient.mk
            (homotopyCellHorizontalPath F a b c d a hab hcd
              ⟨le_rfl, hab⟩ hcell))) :=
      congrArg₂ (fun r s : H ↦ r * s)
        (coveredSubpathValue_eq_cellVertical L F a b c d d hab hcd
          ⟨hcd, le_rfl⟩ hcell)
        (coveredSubpathValue_eq_cellHorizontal L F a b c d a hab hcd
          ⟨le_rfl, hab⟩ hcell)
    _ = singleObjMorphismValue
          (L.map (Path.Homotopic.Quotient.mk
            (homotopyCellHorizontalPath F a b c d b hab hcd
              ⟨hab, le_rfl⟩ hcell))) *
        singleObjMorphismValue
          (L.map (Path.Homotopic.Quotient.mk
            (homotopyCellVerticalPath F a b c d c hab hcd
              ⟨le_rfl, hcd⟩ hcell))) := by
      exact functorValue_square_of_homotopic L
          (homotopyCellHorizontalPath F a b c d a hab hcd
            ⟨le_rfl, hab⟩ hcell)
          (homotopyCellVerticalPath F a b c d d hab hcd
            ⟨hcd, le_rfl⟩ hcell)
          (homotopyCellVerticalPath F a b c d c hab hcd
            ⟨le_rfl, hcd⟩ hcell)
          (homotopyCellHorizontalPath F a b c d b hab hcd
            ⟨hab, le_rfl⟩ hcell)
          (homotopyCellCodRestricted_boundary_homotopic
            F a b c d hab hcd hcell)
    _ = _ := congrArg₂ (fun r s : H ↦ r * s)
      (coveredSubpathValue_eq_cellHorizontal L F a b c d b hab hcd
        ⟨hab, le_rfl⟩ hcell).symm
      (coveredSubpathValue_eq_cellVertical L F a b c d c hab hcd
        ⟨le_rfl, hcd⟩ hcell).symm

/-- Helper for Theorem 70.1: a subordinate homotopy cell satisfies the square
relation for the proof-independent open-union edge evaluator. -/
private lemma openUnionHomotopyCellValue_naturality
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    {x y : X} {p q : Path x y} (F : Path.Homotopy p q)
    (side : Bool) (a b c d : unitInterval) (hab : a ≤ b) (hcd : c ≤ d)
    (hcell : Set.MapsTo F (Set.Icc a b ×ˢ Set.Icc c d)
      (if side then V else U)) :
    openUnionCoveredEdgeValue S (F.toHomotopy.evalAt d) side a b *
        openUnionCoveredEdgeValue S (F.eval a) side c d =
      openUnionCoveredEdgeValue S (F.eval b) side c d *
        openUnionCoveredEdgeValue S (F.toHomotopy.evalAt c) side a b := by
  -- Select the local functor and expose all four covered branches.
  cases side
  · simp only [Bool.false_eq_true, if_false] at hcell
    have hright : openUnionEdgeCovered U V (F.toHomotopy.evalAt d) false a b :=
      ⟨hab, homotopyCell_vertical_range_subset F a b c d d hab hcd
        ⟨hcd, le_rfl⟩ hcell⟩
    have hbottom : openUnionEdgeCovered U V (F.eval a) false c d :=
      ⟨hcd, homotopyCell_horizontal_range_subset F a b c d a hab hcd
        ⟨le_rfl, hab⟩ hcell⟩
    have htop : openUnionEdgeCovered U V (F.eval b) false c d :=
      ⟨hcd, homotopyCell_horizontal_range_subset F a b c d b hab hcd
        ⟨hab, le_rfl⟩ hcell⟩
    have hleft : openUnionEdgeCovered U V (F.toHomotopy.evalAt c) false a b :=
      ⟨hab, homotopyCell_vertical_range_subset F a b c d c hab hcd
        ⟨le_rfl, hcd⟩ hcell⟩
    rw [openUnionCoveredEdgeValue_eq_left S _ _ _ hright,
      openUnionCoveredEdgeValue_eq_left S _ _ _ hbottom,
      openUnionCoveredEdgeValue_eq_left S _ _ _ htop,
      openUnionCoveredEdgeValue_eq_left S _ _ _ hleft]
    exact homotopyCellValue_naturality S.left F a b c d hab hcd hcell
  · simp only [if_true] at hcell
    have hright : openUnionEdgeCovered U V (F.toHomotopy.evalAt d) true a b :=
      ⟨hab, homotopyCell_vertical_range_subset F a b c d d hab hcd
        ⟨hcd, le_rfl⟩ hcell⟩
    have hbottom : openUnionEdgeCovered U V (F.eval a) true c d :=
      ⟨hcd, homotopyCell_horizontal_range_subset F a b c d a hab hcd
        ⟨le_rfl, hab⟩ hcell⟩
    have htop : openUnionEdgeCovered U V (F.eval b) true c d :=
      ⟨hcd, homotopyCell_horizontal_range_subset F a b c d b hab hcd
        ⟨hab, le_rfl⟩ hcell⟩
    have hleft : openUnionEdgeCovered U V (F.toHomotopy.evalAt c) true a b :=
      ⟨hab, homotopyCell_vertical_range_subset F a b c d c hab hcd
        ⟨le_rfl, hcd⟩ hcell⟩
    rw [openUnionCoveredEdgeValue_eq_right S _ _ _ hright,
      openUnionCoveredEdgeValue_eq_right S _ _ _ hbottom,
      openUnionCoveredEdgeValue_eq_right S _ _ _ htop,
      openUnionCoveredEdgeValue_eq_right S _ _ _ hleft]
    exact homotopyCellValue_naturality S.right F a b c d hab hcd hcell

/-- Helper for Theorem 70.1: a covered subpath of an ambient constant path is
sent to the identity by a local fundamental-groupoid functor. -/
private lemma codRestrictedSubpathValue_refl
    {X : Type*} [TopologicalSpace X] {A : Set X} {H : Type*} [Group H]
    (L : FundamentalGroupoid A ⥤ CategoryTheory.SingleObj H)
    {x' y' : X} (x : X) (hx : x' = x) (hy : y' = x)
    (a b : unitInterval) (hab : a ≤ b)
    (hp : Set.range (((Path.refl x).cast hx hy).subpath a b) ⊆ A) :
    singleObjMorphismValue
      (L.map (codRestrictedNestedSubpathClass ((Path.refl x).cast hx hy)
        a a b b le_rfl hab le_rfl hp)) = 1 := by
  let r := (Path.refl x).cast hx hy
  let xa := coveredSubpathPoint r a b hp a le_rfl hab
  have hpath :
      codRestrictedNestedSubpath r
          a a b b le_rfl hab le_rfl hp = Path.refl xa := by
    -- Both sides are the constant path at the same subspace point.
    ext t
    rfl
  -- Compare the mapped quotient classes propositionally, avoiding a dependent
  -- rewrite through the two endpoint membership witnesses.
  unfold codRestrictedNestedSubpathClass
  calc
    _ = singleObjMorphismValue
        (L.map (Path.Homotopic.Quotient.mk (Path.refl xa))) :=
      congrArg singleObjMorphismValue
        (congrArg (fun r ↦ L.map (Path.Homotopic.Quotient.mk r)) hpath)
    _ = singleObjMorphismValue (𝟙 (L.obj (FundamentalGroupoid.mk xa))) := by
      exact congrArg singleObjMorphismValue
        (L.map_id (FundamentalGroupoid.mk xa))
    _ = 1 := rfl

/-- Helper for Theorem 70.1: the proof-independent evaluator assigns unit to
a covered edge of an ambient constant path. -/
private lemma openUnionCoveredEdgeValue_refl
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    {x' y' : X} (x : X) (hx : x' = x) (hy : y' = x)
    (side : Bool) (a b : unitInterval)
    (h : openUnionEdgeCovered U V ((Path.refl x).cast hx hy) side a b) :
    openUnionCoveredEdgeValue S ((Path.refl x).cast hx hy) side a b = 1 := by
  -- Select the local functor and apply the constant-subpath computation.
  cases side
  · rw [openUnionCoveredEdgeValue_eq_left S _ _ _ h]
    exact codRestrictedSubpathValue_refl S.left x hx hy a b h.1 h.2
  · rw [openUnionCoveredEdgeValue_eq_right S _ _ _ h]
    exact codRestrictedSubpathValue_refl S.right x hx hy a b h.1 h.2

/-- Helper for Theorem 70.1: the bottom edge of every subordinate grid cell
is covered by that cell's selected open set. -/
private lemma OpenUnionHomotopyGrid.bottomCovered
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x y : X}
    {p q : Path x y} {F : Path.Homotopy p q}
    (G : OpenUnionHomotopyGrid (U := U) (V := V) F)
    (j i : Fin (G.n + 1)) :
    Set.range ((F.eval (G.point j.castSucc)).subpath
      (G.point i.castSucc) (G.point i.succ)) ⊆
        if G.side j i then V else U := by
  -- Fix the lower time coordinate in the stored cell-containment property.
  exact homotopyCell_horizontal_range_subset F
    (G.point j.castSucc) (G.point j.succ)
    (G.point i.castSucc) (G.point i.succ) (G.point j.castSucc)
    (G.monotone (Fin.castSucc_le_succ j))
    (G.monotone (Fin.castSucc_le_succ i))
    ⟨le_rfl, G.monotone (Fin.castSucc_le_succ j)⟩ (G.covered j i)

/-- Helper for Theorem 70.1: the top edge of every subordinate grid cell is
covered by that cell's selected open set. -/
private lemma OpenUnionHomotopyGrid.topCovered
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x y : X}
    {p q : Path x y} {F : Path.Homotopy p q}
    (G : OpenUnionHomotopyGrid (U := U) (V := V) F)
    (j i : Fin (G.n + 1)) :
    Set.range ((F.eval (G.point j.succ)).subpath
      (G.point i.castSucc) (G.point i.succ)) ⊆
        if G.side j i then V else U := by
  -- Fix the upper time coordinate in the same cell-containment property.
  exact homotopyCell_horizontal_range_subset F
    (G.point j.castSucc) (G.point j.succ)
    (G.point i.castSucc) (G.point i.succ) (G.point j.succ)
    (G.monotone (Fin.castSucc_le_succ j))
    (G.monotone (Fin.castSucc_le_succ i))
    ⟨G.monotone (Fin.castSucc_le_succ j), le_rfl⟩ (G.covered j i)

/-- Helper for Theorem 70.1: the left vertical edge of a grid cell is covered
with that cell's label. -/
private lemma OpenUnionHomotopyGrid.leftVerticalCovered
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x y : X}
    {p q : Path x y} {F : Path.Homotopy p q}
    (G : OpenUnionHomotopyGrid (U := U) (V := V) F)
    (j i : Fin (G.n + 1)) :
    openUnionEdgeCovered U V (F.toHomotopy.evalAt (G.point i.castSucc))
      (G.side j i) (G.point j.castSucc) (G.point j.succ) := by
  -- Fix the cell's left spatial coordinate and retain its time interval.
  exact ⟨G.monotone (Fin.castSucc_le_succ j),
    homotopyCell_vertical_range_subset F
      (G.point j.castSucc) (G.point j.succ)
      (G.point i.castSucc) (G.point i.succ) (G.point i.castSucc)
      (G.monotone (Fin.castSucc_le_succ j))
      (G.monotone (Fin.castSucc_le_succ i))
      ⟨le_rfl, G.monotone (Fin.castSucc_le_succ i)⟩ (G.covered j i)⟩

/-- Helper for Theorem 70.1: the right vertical edge of a grid cell is covered
with that cell's label. -/
private lemma OpenUnionHomotopyGrid.rightVerticalCovered
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x y : X}
    {p q : Path x y} {F : Path.Homotopy p q}
    (G : OpenUnionHomotopyGrid (U := U) (V := V) F)
    (j i : Fin (G.n + 1)) :
    openUnionEdgeCovered U V (F.toHomotopy.evalAt (G.point i.succ))
      (G.side j i) (G.point j.castSucc) (G.point j.succ) := by
  -- Fix the cell's right spatial coordinate.
  exact ⟨G.monotone (Fin.castSucc_le_succ j),
    homotopyCell_vertical_range_subset F
      (G.point j.castSucc) (G.point j.succ)
      (G.point i.castSucc) (G.point i.succ) (G.point i.succ)
      (G.monotone (Fin.castSucc_le_succ j))
      (G.monotone (Fin.castSucc_le_succ i))
      ⟨G.monotone (Fin.castSucc_le_succ i), le_rfl⟩ (G.covered j i)⟩

/-- Helper for Theorem 70.1: choose one coherent label for each vertical grid
edge, taking an interior edge's label from the cell immediately to its left. -/
private def OpenUnionHomotopyGrid.verticalSide
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x y : X}
    {p q : Path x y} {F : Path.Homotopy p q}
    (G : OpenUnionHomotopyGrid (U := U) (V := V) F)
    (j : Fin (G.n + 1)) : Fin (G.n + 2) → Bool :=
  Fin.cases (G.side j 0) (fun i ↦ G.side j i)

/-- Helper for Theorem 70.1: every coherently labeled vertical grid edge is
covered by the open set selected for it. -/
private lemma OpenUnionHomotopyGrid.verticalCovered
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x y : X}
    {p q : Path x y} {F : Path.Homotopy p q}
    (G : OpenUnionHomotopyGrid (U := U) (V := V) F)
    (j : Fin (G.n + 1)) (k : Fin (G.n + 2)) :
    openUnionEdgeCovered U V (F.toHomotopy.evalAt (G.point k))
      (G.verticalSide j k) (G.point j.castSucc) (G.point j.succ) := by
  -- At zero use the first cell's left edge; at a successor use the preceding
  -- cell's right edge, which makes adjacent cells share one vertical value.
  refine Fin.cases ?_ (fun i ↦ ?_) k
  · exact G.leftVerticalCovered j 0
  · exact G.rightVerticalCovered j i

/-- Helper for Theorem 70.1: the bottom row of a grid strip is a covered path
subdivision carrying the strip's cell labels. -/
private def OpenUnionHomotopyGrid.bottomSubdivision
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x y : X}
    {p q : Path x y} {F : Path.Homotopy p q}
    (G : OpenUnionHomotopyGrid (U := U) (V := V) F)
    (j : Fin (G.n + 1)) :
    OpenUnionPathSubdivision U V (F.eval (G.point j.castSucc)) :=
  { n := G.n
    point := G.point
    start := G.start
    finish := G.finish
    monotone := G.monotone
    side := G.side j
    covered := G.bottomCovered j }

/-- Helper for Theorem 70.1: the top row of a grid strip is a covered path
subdivision carrying the strip's cell labels. -/
private def OpenUnionHomotopyGrid.topSubdivision
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x y : X}
    {p q : Path x y} {F : Path.Homotopy p q}
    (G : OpenUnionHomotopyGrid (U := U) (V := V) F)
    (j : Fin (G.n + 1)) :
    OpenUnionPathSubdivision U V (F.eval (G.point j.succ)) :=
  { n := G.n
    point := G.point
    start := G.start
    finish := G.finish
    monotone := G.monotone
    side := G.side j
    covered := G.topCovered j }

/-- Helper for Theorem 70.1: the reverse edge products on the bottom and top
of a subordinate homotopy-grid strip are equal. -/
private lemma OpenUnionHomotopyGrid.stripReverseProd_eq
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    {x y : X} {p q : Path x y} {F : Path.Homotopy p q}
    (G : OpenUnionHomotopyGrid (U := U) (V := V) F)
    (j : Fin (G.n + 1)) :
    FiniteCoveredSubdivision.reverseFinProd
        (fun i ↦ openUnionCoveredEdgeValue S (F.eval (G.point j.castSucc))
          (G.side j i) (G.point i.castSucc) (G.point i.succ)) =
      FiniteCoveredSubdivision.reverseFinProd
        (fun i ↦ openUnionCoveredEdgeValue S (F.eval (G.point j.succ))
          (G.side j i) (G.point i.castSucc) (G.point i.succ)) := by
  let bottom : Fin (G.n + 1) → H := fun i ↦
    openUnionCoveredEdgeValue S (F.eval (G.point j.castSucc))
      (G.side j i) (G.point i.castSucc) (G.point i.succ)
  let top : Fin (G.n + 1) → H := fun i ↦
    openUnionCoveredEdgeValue S (F.eval (G.point j.succ))
      (G.side j i) (G.point i.castSucc) (G.point i.succ)
  let vertical : Fin (G.n + 2) → H := fun k ↦
    openUnionCoveredEdgeValue S (F.toHomotopy.evalAt (G.point k))
      (G.verticalSide j k) (G.point j.castSucc) (G.point j.succ)
  -- Each cell square has the shared vertical values selected by `verticalSide`.
  have hcell : ∀ i, vertical i.succ * bottom i = top i * vertical i.castSucc := by
    intro i
    have hsquare := openUnionHomotopyCellValue_naturality S F (G.side j i)
      (G.point j.castSucc) (G.point j.succ)
      (G.point i.castSucc) (G.point i.succ)
      (G.monotone (Fin.castSucc_le_succ j))
      (G.monotone (Fin.castSucc_le_succ i)) (G.covered j i)
    have hleft :
        openUnionCoveredEdgeValue S
            (F.toHomotopy.evalAt (G.point i.castSucc)) (G.side j i)
            (G.point j.castSucc) (G.point j.succ) =
          vertical i.castSucc := by
      exact (openUnionCoveredEdgeLaws S
        (F.toHomotopy.evalAt (G.point i.castSucc))).agree
          (G.leftVerticalCovered j i) (G.verticalCovered j i.castSucc)
    have hright :
        openUnionCoveredEdgeValue S
            (F.toHomotopy.evalAt (G.point i.succ)) (G.side j i)
            (G.point j.castSucc) (G.point j.succ) =
          vertical i.succ := by
      rfl
    rw [hleft, hright] at hsquare
    simpa only [bottom, top, vertical,
      OpenUnionHomotopyGrid.verticalSide] using hsquare
  -- Fixed endpoints make the two outer vertical paths constant.
  have hsourcePath : F.toHomotopy.evalAt 0 =
      (Path.refl x).cast p.source q.source := by
    ext t
    exact F.source t
  have htargetPath :
      F.toHomotopy.evalAt 1 = (Path.refl y).cast p.target q.target := by
    ext t
    exact F.target t
  have hleft : vertical 0 = 1 := by
    have hcovered := G.verticalCovered j 0
    rw [G.start, hsourcePath] at hcovered
    simp only [vertical]
    rw [G.start, hsourcePath]
    exact openUnionCoveredEdgeValue_refl S x p.source q.source
      (G.verticalSide j 0) (G.point j.castSucc) (G.point j.succ) hcovered
  have hright : vertical (Fin.last (G.n + 1)) = 1 := by
    have hcovered := G.verticalCovered j (Fin.last (G.n + 1))
    rw [G.finish, htargetPath] at hcovered
    simp only [vertical]
    rw [G.finish, htargetPath]
    exact openUnionCoveredEdgeValue_refl S y p.target q.target
      (G.verticalSide j (Fin.last (G.n + 1)))
      (G.point j.castSucc) (G.point j.succ) hcovered
  -- The finite telescope cancels all interior vertical values.
  exact FiniteCoveredSubdivision.reverseFinProd_eq_of_squareRelations
    bottom top vertical hcell hleft hright

/-- Helper for Theorem 70.1: a subordinate homotopy-grid strip has equal
covered-subdivision values on its bottom and top rows. -/
private lemma OpenUnionHomotopyGrid.stripValue_eq
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    {x y : X} {p q : Path x y} {F : Path.Homotopy p q}
    (G : OpenUnionHomotopyGrid (U := U) (V := V) F)
    (j : Fin (G.n + 1)) :
    (G.bottomSubdivision j).value S = (G.topSubdivision j).value S := by
  -- Normalize both row values once, then apply the strip telescope.
  rw [(G.bottomSubdivision j).value_eq_reverseFinProd S,
    (G.topSubdivision j).value_eq_reverseFinProd S]
  exact G.stripReverseProd_eq S j

/-- Helper for Theorem 70.1: every path admits a finite subdivision subordinate
to the two-member open cover. -/
private lemma exists_openUnionPathSubdivision
    {X : Type u} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    {x y : X} (p : Path x y) : Nonempty (OpenUnionPathSubdivision U V p) := by
  classical
  -- Pull the open cover back to the compact unit interval.
  let c : Bool → Set unitInterval := fun
    | false => p ⁻¹' U
    | true => p ⁻¹' V
  have hcOpen : ∀ choice, IsOpen (c choice) := by
    intro choice
    cases choice
    · exact hU.preimage p.continuous
    · exact hV.preimage p.continuous
  have hcCover : Set.univ ⊆ ⋃ choice, c choice := by
    intro t _
    have hpt : p t ∈ U ∪ V := by
      rw [hcover]
      exact Set.mem_univ (p t)
    cases hpt with
    | inl hptU =>
        exact Set.mem_iUnion.mpr ⟨false, hptU⟩
    | inr hptV =>
        exact Set.mem_iUnion.mpr ⟨true, hptV⟩
  -- Compactness supplies a monotone sequence eventually equal to one.
  obtain ⟨t, ht0, htmono, ⟨m, hm⟩, htCovered⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hcOpen hcCover
  have hmpositive : 0 < m := by
    by_contra hmnot
    have hmzero : m = 0 := Nat.eq_zero_of_not_pos hmnot
    subst m
    have htone : t 0 = 1 := hm 0 le_rfl
    rw [ht0] at htone
    exact zero_ne_one htone
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpositive)
  let point : Fin (n + 2) → unitInterval := fun i ↦ t i
  choose side hside using fun i : Fin (n + 1) ↦ htCovered i
  have hsubpath : ∀ i, Set.range
      (p.subpath (point i.castSucc) (point i.succ)) ⊆
        if side i then V else U := by
    intro i
    have hstep : point i.castSucc ≤ point i.succ := htmono (Nat.le_succ i)
    rw [Path.range_subpath_of_le p _ _ hstep]
    rintro z ⟨s, hs, rfl⟩
    have hsCover : s ∈ c (side i) := hside i hs
    cases hchoice : side i
    · simpa only [c, hchoice, Bool.false_eq_true, if_false,
        Set.mem_preimage] using hsCover
    · simpa only [c, hchoice, Bool.true_eq, if_true,
        Set.mem_preimage] using hsCover
  -- Truncate the eventual sequence at its first chosen terminal index.
  refine ⟨⟨n, point, ht0, ?_, ?_, side, hsubpath⟩⟩
  · exact hm (n + 1) le_rfl
  · intro i j hij
    exact htmono hij

/-- Helper for Theorem 70.1: covered-subdivision evaluation is invariant under
fixed-endpoint path homotopy. -/
private lemma OpenUnionPathSubdivision.value_eq_of_homotopy
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    {x y : X} {p q : Path x y} (F : Path.Homotopy p q)
    (Dp : OpenUnionPathSubdivision U V p)
    (Dq : OpenUnionPathSubdivision U V q) :
    Dp.value S = Dq.value S := by
  classical
  obtain ⟨G⟩ := exists_openUnionHomotopyGrid U V hU hV hcover F
  let row : ∀ k : Fin (G.n + 2),
      OpenUnionPathSubdivision U V (F.eval (G.point k)) := fun k ↦
    Classical.choice
      (exists_openUnionPathSubdivision U V hU hV hcover (F.eval (G.point k)))
  -- Compare each chosen row to the two canonical rows bounding its strip.
  have hadj : ∀ j : Fin (G.n + 1),
      (row j.castSucc).value S = (row j.succ).value S := by
    intro j
    calc
      (row j.castSucc).value S = (G.bottomSubdivision j).value S :=
        (row j.castSucc).value_eq S (G.bottomSubdivision j)
      _ = (G.topSubdivision j).value S := G.stripValue_eq S j
      _ = (row j.succ).value S :=
        (G.topSubdivision j).value_eq S (row j.succ)
  have hrows : (row 0).value S = (row (Fin.last (G.n + 1))).value S :=
    FiniteCoveredSubdivision.eq_zero_last_of_adjacent
      (fun k ↦ (row k).value S) hadj
  -- The first and last grid rows are the original endpoint paths.
  have hfirst : F.eval (G.point 0) = p := by
    rw [G.start, Path.Homotopy.eval_zero]
  have hlast : F.eval (G.point (Fin.last (G.n + 1))) = q := by
    rw [G.finish, Path.Homotopy.eval_one]
  let firstRow : OpenUnionPathSubdivision U V p := (row 0).cast hfirst
  let lastRow : OpenUnionPathSubdivision U V q :=
    (row (Fin.last (G.n + 1))).cast hlast
  calc
    Dp.value S = firstRow.value S := Dp.value_eq S firstRow
    _ = (row 0).value S := (row 0).value_cast S hfirst
    _ = (row (Fin.last (G.n + 1))).value S := hrows
    _ = lastRow.value S := ((row (Fin.last (G.n + 1))).value_cast S hlast).symm
    _ = Dq.value S := (Dq.value_eq S lastRow).symm

/-- Helper for Theorem 70.1: choose the common covered-subdivision value of an
ambient path. -/
private noncomputable def openUnionPathValue
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    {x y : X} (p : Path x y) : H :=
  (Classical.choice (exists_openUnionPathSubdivision U V hU hV hcover p)).value S

/-- Helper for Theorem 70.1: every covered subdivision computes the chosen
ambient path value. -/
private lemma openUnionPathValue_eq_subdivision
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    {x y : X} {p : Path x y} (D : OpenUnionPathSubdivision U V p) :
    openUnionPathValue S hU hV hcover p = D.value S := by
  -- Subdivision independence compares the chosen witness with `D`.
  exact (Classical.choice
    (exists_openUnionPathSubdivision U V hU hV hcover p)).value_eq S D

/-- Helper for Theorem 70.1: the chosen covered-subdivision value turns path
concatenation into multiplication in reverse categorical order. -/
private lemma openUnionPathValue_trans
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    {x y z : X} (p : Path x y) (q : Path y z) :
    openUnionPathValue S hU hV hcover (p.trans q) =
      openUnionPathValue S hU hV hcover q *
        openUnionPathValue S hU hV hcover p := by
  classical
  let Dp := Classical.choice
    (exists_openUnionPathSubdivision U V hU hV hcover p)
  let Dq := Classical.choice
    (exists_openUnionPathSubdivision U V hU hV hcover q)
  let Dtrans := Classical.choice
    (exists_openUnionPathSubdivision U V hU hV hcover (p.trans q))
  -- Map the two recursive subdivisions into the corresponding halves of the
  -- concatenated path. The transport bridge supplies both required fields.
  let leftRaw : FiniteCoveredSubdivision.Subdivision
      (openUnionEdgeCovered U V (p.trans q))
      (openUnionLeftHalf 0) (openUnionLeftHalf 1) :=
    Dp.toFinite.map openUnionLeftHalf openUnionLeftHalf_monotone
      (fun hp ↦ (openUnionCoveredEdge_transport_leftHalf S p q hp).1)
  let rightRaw : FiniteCoveredSubdivision.Subdivision
      (openUnionEdgeCovered U V (p.trans q))
      (openUnionRightHalf 0) (openUnionRightHalf 1) :=
    Dq.toFinite.map openUnionRightHalf openUnionRightHalf_monotone
      (fun hq ↦ (openUnionCoveredEdge_transport_rightHalf S p q hq).1)
  have hleftRaw :
      leftRaw.value (openUnionCoveredEdgeValue S (p.trans q)) =
        Dp.toFinite.value (openUnionCoveredEdgeValue S p) := by
    -- Structural `value_map` reduces the claim to the edge transport value
    -- equation already proved above.
    simpa only [leftRaw] using
      FiniteCoveredSubdivision.Subdivision.value_map
        (openUnionCoveredEdgeValue S p)
        (openUnionCoveredEdgeValue S (p.trans q)) Dp.toFinite
        openUnionLeftHalf openUnionLeftHalf_monotone
        (fun hp ↦ (openUnionCoveredEdge_transport_leftHalf S p q hp).1)
        (fun hp ↦ (openUnionCoveredEdge_transport_leftHalf S p q hp).2)
  have hrightRaw :
      rightRaw.value (openUnionCoveredEdgeValue S (p.trans q)) =
        Dq.toFinite.value (openUnionCoveredEdgeValue S q) := by
    -- The right half uses the symmetric affine edge transport.
    simpa only [rightRaw] using
      FiniteCoveredSubdivision.Subdivision.value_map
        (openUnionCoveredEdgeValue S q)
        (openUnionCoveredEdgeValue S (p.trans q)) Dq.toFinite
        openUnionRightHalf openUnionRightHalf_monotone
        (fun hq ↦ (openUnionCoveredEdge_transport_rightHalf S p q hq).1)
        (fun hq ↦ (openUnionCoveredEdge_transport_rightHalf S p q hq).2)
  -- Cast endpoints once so the two recursive subdivisions share the named
  -- midpoint literally and can be appended without dependent array plumbing.
  let left : FiniteCoveredSubdivision.Subdivision
      (openUnionEdgeCovered U V (p.trans q)) 0 openUnionMidpoint :=
    openUnionLeftHalf_zero ▸ openUnionLeftHalf_one ▸ leftRaw
  let right : FiniteCoveredSubdivision.Subdivision
      (openUnionEdgeCovered U V (p.trans q)) openUnionMidpoint 1 :=
    openUnionRightHalf_zero ▸ openUnionRightHalf_one ▸ rightRaw
  have hleft : left.value (openUnionCoveredEdgeValue S (p.trans q)) =
      Dp.toFinite.value (openUnionCoveredEdgeValue S p) := by
    calc
      left.value (openUnionCoveredEdgeValue S (p.trans q)) =
          leftRaw.value (openUnionCoveredEdgeValue S (p.trans q)) := by
        simpa only [left] using
          FiniteCoveredSubdivision.Subdivision.value_cast
            (openUnionCoveredEdgeValue S (p.trans q)) leftRaw
              openUnionLeftHalf_zero openUnionLeftHalf_one
      _ = Dp.toFinite.value (openUnionCoveredEdgeValue S p) := hleftRaw
  have hright : right.value (openUnionCoveredEdgeValue S (p.trans q)) =
      Dq.toFinite.value (openUnionCoveredEdgeValue S q) := by
    calc
      right.value (openUnionCoveredEdgeValue S (p.trans q)) =
          rightRaw.value (openUnionCoveredEdgeValue S (p.trans q)) := by
        simpa only [right] using
          FiniteCoveredSubdivision.Subdivision.value_cast
            (openUnionCoveredEdgeValue S (p.trans q)) rightRaw
              openUnionRightHalf_zero openUnionRightHalf_one
      _ = Dq.toFinite.value (openUnionCoveredEdgeValue S q) := hrightRaw
  let combined : FiniteCoveredSubdivision.Subdivision
      (openUnionEdgeCovered U V (p.trans q)) 0 1 :=
    left.append right openUnionMidpoint.property.1 openUnionMidpoint.property.2
  have hcombined :
      combined.value (openUnionCoveredEdgeValue S (p.trans q)) =
        Dq.toFinite.value (openUnionCoveredEdgeValue S q) *
          Dp.toFinite.value (openUnionCoveredEdgeValue S p) := by
    calc
      combined.value (openUnionCoveredEdgeValue S (p.trans q)) =
          right.value (openUnionCoveredEdgeValue S (p.trans q)) *
            left.value (openUnionCoveredEdgeValue S (p.trans q)) := by
        simpa only [combined] using
          FiniteCoveredSubdivision.Subdivision.value_append
            (openUnionCoveredEdgeValue S (p.trans q)) left right
              openUnionMidpoint.property.1 openUnionMidpoint.property.2
      _ = Dq.toFinite.value (openUnionCoveredEdgeValue S q) *
          Dp.toFinite.value (openUnionCoveredEdgeValue S p) := by
        rw [hleft, hright]
  -- Subdivision independence compares the chosen concatenated subdivision
  -- with the appended one; the two map formulas then give the desired product.
  calc
    openUnionPathValue S hU hV hcover (p.trans q) = Dtrans.value S :=
      openUnionPathValue_eq_subdivision S hU hV hcover Dtrans
    _ = Dtrans.toFinite.value
        (openUnionCoveredEdgeValue S (p.trans q)) := rfl
    _ = combined.value (openUnionCoveredEdgeValue S (p.trans q)) :=
      FiniteCoveredSubdivision.Subdivision.value_eq
        (openUnionCoveredEdgeLaws S (p.trans q)) Dtrans.toFinite combined
    _ = Dq.toFinite.value (openUnionCoveredEdgeValue S q) *
        Dp.toFinite.value (openUnionCoveredEdgeValue S p) := hcombined
    _ = Dq.value S * Dp.value S := rfl
    _ = openUnionPathValue S hU hV hcover q *
        openUnionPathValue S hU hV hcover p := by
      rw [openUnionPathValue_eq_subdivision S hU hV hcover Dq,
        openUnionPathValue_eq_subdivision S hU hV hcover Dp]

/-- Helper for Theorem 70.1: the chosen ambient path value depends only on the
fixed-endpoint path-homotopy class. -/
private lemma openUnionPathValue_eq_of_homotopy
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    {x y : X} {p q : Path x y} (F : Path.Homotopy p q) :
    openUnionPathValue S hU hV hcover p =
      openUnionPathValue S hU hV hcover q := by
  -- Apply the grid theorem to the two subdivisions chosen by `pathValue`.
  exact OpenUnionPathSubdivision.value_eq_of_homotopy S hU hV hcover F
    (Classical.choice (exists_openUnionPathSubdivision U V hU hV hcover p))
    (Classical.choice (exists_openUnionPathSubdivision U V hU hV hcover q))

/-- Helper for Theorem 70.1: homotopic ambient paths have the same chosen
covered-subdivision value. -/
private lemma openUnionPathValue_respects_homotopic
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    {x y : X} (p q : Path x y) (h : p.Homotopic q) :
    openUnionPathValue S hU hV hcover p =
      openUnionPathValue S hU hV hcover q := by
  -- Unpack the path homotopy and invoke the finite-grid invariance theorem.
  obtain ⟨F⟩ := h
  exact openUnionPathValue_eq_of_homotopy S hU hV hcover F

/-- Helper for Theorem 70.1: the covered-subdivision value descends to ambient
path-homotopy classes. -/
private noncomputable def openUnionPathClassValue
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    {x y : X} : Path.Homotopic.Quotient x y → H :=
  Quotient.lift (openUnionPathValue S hU hV hcover)
    (openUnionPathValue_respects_homotopic S hU hV hcover)

/-- Helper for Theorem 70.1: the descended value of a represented path class
is its chosen covered-subdivision value. -/
private lemma openUnionPathClassValue_mk
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    {x y : X} (p : Path x y) :
    openUnionPathClassValue S hU hV hcover
        (Path.Homotopic.Quotient.mk p) =
      openUnionPathValue S hU hV hcover p := by
  -- This is the computation rule of the quotient lift.
  rfl

/-- Helper for Theorem 70.1: the chosen value of a constant ambient path is
the identity element. -/
private lemma openUnionPathValue_refl
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (x : X) : openUnionPathValue S hU hV hcover (Path.refl x) = 1 := by
  -- Concatenating the constant path with itself does not change it, so the
  -- composition formula makes its value idempotent; group cancellation
  -- forces that value to be one.
  have h := openUnionPathValue_trans S hU hV hcover
    (Path.refl x) (Path.refl x)
  rw [Path.refl_trans_refl] at h
  exact mul_eq_left.mp h.symm

/-- Helper for Theorem 70.1: the descended path-class value preserves the
identity arrow of the fundamental groupoid. -/
private lemma openUnionPathClassValue_id
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (x : FundamentalGroupoid X) :
    openUnionPathClassValue S hU hV hcover (𝟙 x) =
      𝟙 (CategoryTheory.SingleObj.star H) := by
  -- Both categorical identities compute to the constant path and group unit.
  exact openUnionPathValue_refl S hU hV hcover x.as

/-- Helper for Theorem 70.1: the descended path-class value preserves
fundamental-groupoid composition. -/
private lemma openUnionPathClassValue_comp
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    {x y z : FundamentalGroupoid X} (p : x ⟶ y) (q : y ⟶ z) :
    openUnionPathClassValue S hU hV hcover (p ≫ q) =
      openUnionPathClassValue S hU hV hcover q *
        openUnionPathClassValue S hU hV hcover p := by
  -- Quotient induction exposes path representatives, where the recursive
  -- subdivision concatenation theorem applies directly.
  induction p using Quotient.inductionOn with
  | _ p =>
      induction q using Quotient.inductionOn with
      | _ q =>
          exact openUnionPathValue_trans S hU hV hcover p q

/-- Helper for Theorem 70.1: the global one-object-valued functor obtained
from the subdivision invariant on ambient path classes. -/
private noncomputable def openUnionGlobalPathFunctor
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    FundamentalGroupoid X ⥤ CategoryTheory.SingleObj H :=
  { obj := fun _ ↦ CategoryTheory.SingleObj.star H
    map := fun p ↦ openUnionPathClassValue S hU hV hcover p
    map_id := openUnionPathClassValue_id S hU hV hcover
    map_comp := openUnionPathClassValue_comp S hU hV hcover }

/-- Helper for Theorem 70.1: the two parameters of the one-edge subdivision
are the endpoints of the unit interval. -/
private def openUnionOneEdgePoint : Fin 2 → unitInterval :=
  fun i ↦ Fin.cases 0 (fun _ ↦ 1) i

/-- Helper for Theorem 70.1: the one-edge subdivision begins at zero. -/
private lemma openUnionOneEdgePoint_zero : openUnionOneEdgePoint 0 = 0 := by
  -- Evaluate the endpoint function at its first index.
  rfl

/-- Helper for Theorem 70.1: the one-edge subdivision ends at one. -/
private lemma openUnionOneEdgePoint_last :
    openUnionOneEdgePoint (Fin.last 1) = 1 := by
  -- The last index of `Fin 2` is distinct from zero.
  rfl

/-- Helper for Theorem 70.1: the source index of the unique edge selects the
zero endpoint. -/
private lemma openUnionOneEdgePoint_castSucc (i : Fin 1) :
    openUnionOneEdgePoint i.castSucc = 0 := by
  -- The type `Fin 1` has only its zero index.
  have hi : i = 0 := Subsingleton.elim i 0
  subst i
  rfl

/-- Helper for Theorem 70.1: the target index of the unique edge selects the
one endpoint. -/
private lemma openUnionOneEdgePoint_succ (i : Fin 1) :
    openUnionOneEdgePoint i.succ = 1 := by
  -- Successor sends the unique index to the last index of `Fin 2`.
  have hi : i = 0 := Subsingleton.elim i 0
  subst i
  rfl

/-- Helper for Theorem 70.1: the endpoint function of the one-edge
subdivision is monotone. -/
private lemma openUnionOneEdgePoint_monotone :
    Monotone openUnionOneEdgePoint := by
  -- There are only the ordered endpoint indices zero and one.
  intro i j hij
  fin_cases i
  · fin_cases j
    · exact le_rfl
    · exact zero_le_one
  · fin_cases j
    · norm_num at hij
    · exact le_rfl

/-- Helper for Theorem 70.1: a path contained in `U` satisfies the cover field
of the one-edge subdivision labeled by `U`. -/
private lemma openUnionOneEdgeCovered_left
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x y : X}
    (p : Path x y) (hp : Set.range p ⊆ U) :
    ∀ i : Fin 1, Set.range
        (p.subpath (openUnionOneEdgePoint i.castSucc)
          (openUnionOneEdgePoint i.succ)) ⊆
      if false then V else U := by
  -- The unique edge is the full subpath from zero to one.
  intro i
  have hi : i = 0 := Subsingleton.elim i 0
  subst i
  rw [openUnionOneEdgePoint_castSucc, openUnionOneEdgePoint_succ,
    Path.subpath_zero_one]
  simp only [Bool.false_eq_true, if_false]
  rintro z ⟨t, rfl⟩
  exact hp (Set.mem_range_self t)

/-- Helper for Theorem 70.1: a path contained in `V` satisfies the cover field
of the one-edge subdivision labeled by `V`. -/
private lemma openUnionOneEdgeCovered_right
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x y : X}
    (p : Path x y) (hp : Set.range p ⊆ V) :
    ∀ i : Fin 1, Set.range
        (p.subpath (openUnionOneEdgePoint i.castSucc)
          (openUnionOneEdgePoint i.succ)) ⊆
      if true then V else U := by
  -- The same full subpath is now assigned to the right cover member.
  intro i
  have hi : i = 0 := Subsingleton.elim i 0
  subst i
  rw [openUnionOneEdgePoint_castSucc, openUnionOneEdgePoint_succ,
    Path.subpath_zero_one]
  simp only [if_true]
  rintro z ⟨t, rfl⟩
  exact hp (Set.mem_range_self t)

/-- Helper for Theorem 70.1: a path lying in `U` has a canonical one-edge
covered subdivision labeled by the left cover member. -/
private def openUnionPathSubdivisionLeft
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x y : X}
    (p : Path x y) (hp : Set.range p ⊆ U) :
    OpenUnionPathSubdivision U V p :=
  { n := 0
    point := openUnionOneEdgePoint
    start := openUnionOneEdgePoint_zero
    finish := openUnionOneEdgePoint_last
    monotone := openUnionOneEdgePoint_monotone
    side := fun _ ↦ false
    covered := openUnionOneEdgeCovered_left p hp }

/-- Helper for Theorem 70.1: a path lying in `V` has a canonical one-edge
covered subdivision labeled by the right cover member. -/
private def openUnionPathSubdivisionRight
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x y : X}
    (p : Path x y) (hp : Set.range p ⊆ V) :
    OpenUnionPathSubdivision U V p :=
  { n := 0
    point := openUnionOneEdgePoint
    start := openUnionOneEdgePoint_zero
    finish := openUnionOneEdgePoint_last
    monotone := openUnionOneEdgePoint_monotone
    side := fun _ ↦ true
    covered := openUnionOneEdgeCovered_right p hp }

/-- Helper for Theorem 70.1: the ambient subdivision value of a path in the
left cover member is exactly its value under the left local functor. -/
private lemma openUnionPathValue_map_left
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    {x y : U} (p : Path x y) :
    openUnionPathValue S hU hV hcover
        (p.map continuous_subtype_val) =
      S.left.map (Path.Homotopic.Quotient.mk p) := by
  -- Name the direct subtype-inclusion path so the one-edge computation
  -- remains readable.
  let ambient : Path x.1 y.1 := p.map continuous_subtype_val
  have hrange : Set.range ambient ⊆ U := by
    rintro _ ⟨t, rfl⟩
    exact (p t).property
  let D := openUnionPathSubdivisionLeft (V := V) ambient hrange
  have hcovered : openUnionEdgeCovered U V ambient false 0 1 := by
    refine ⟨zero_le_one, ?_⟩
    simp only [Bool.false_eq_true, if_false]
    rintro _ ⟨t, rfl⟩
    exact hrange (Set.mem_range_self _)
  have hsingle : D.value S =
      openUnionCoveredEdgeValue S ambient false 0 1 := by
    -- A one-edge reverse product consists only of its unique edge value.
    rw [D.value_eq_reverseFinProd S]
    simp only [D, openUnionPathSubdivisionLeft]
    rw [FiniteCoveredSubdivision.reverseFinProd_succ_head]
    simp only [FiniteCoveredSubdivision.reverseFinProd, List.ofFn_zero,
      List.reverse_nil, List.prod_nil, one_mul]
    rw [openUnionOneEdgePoint_castSucc, openUnionOneEdgePoint_succ]
  calc
    openUnionPathValue S hU hV hcover ambient = D.value S :=
      openUnionPathValue_eq_subdivision S hU hV hcover D
    _ = openUnionCoveredEdgeValue S ambient false 0 1 := hsingle
    _ = S.left.map (Path.Homotopic.Quotient.mk p) := by
      rw [openUnionCoveredEdgeValue_eq_left_restricted S ambient 0 1 hcovered]
      apply singleObjFunctorPathValue_eq_of_coe
      intro t
      calc
        _ = ambient.subpath 0 1 t := rfl
        _ = ambient t :=
          congrArg ambient (Set.Icc.convexComb_zero_one t)
        _ = (p t : X) := rfl

/-- Helper for Theorem 70.1: the ambient subdivision value of a path in the
right cover member is exactly its value under the right local functor. -/
private lemma openUnionPathValue_map_right
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    {x y : V} (p : Path x y) :
    openUnionPathValue S hU hV hcover
        (p.map continuous_subtype_val) =
      S.right.map (Path.Homotopic.Quotient.mk p) := by
  -- Repeat the one-edge normalization with the right cover label.
  let ambient : Path x.1 y.1 := p.map continuous_subtype_val
  have hrange : Set.range ambient ⊆ V := by
    rintro _ ⟨t, rfl⟩
    exact (p t).property
  let D := openUnionPathSubdivisionRight (U := U) ambient hrange
  have hcovered : openUnionEdgeCovered U V ambient true 0 1 := by
    refine ⟨zero_le_one, ?_⟩
    simp only [if_true]
    rintro _ ⟨t, rfl⟩
    exact hrange (Set.mem_range_self _)
  have hsingle : D.value S =
      openUnionCoveredEdgeValue S ambient true 0 1 := by
    rw [D.value_eq_reverseFinProd S]
    simp only [D, openUnionPathSubdivisionRight]
    rw [FiniteCoveredSubdivision.reverseFinProd_succ_head]
    simp only [FiniteCoveredSubdivision.reverseFinProd, List.ofFn_zero,
      List.reverse_nil, List.prod_nil, one_mul]
    rw [openUnionOneEdgePoint_castSucc, openUnionOneEdgePoint_succ]
  calc
    openUnionPathValue S hU hV hcover ambient = D.value S :=
      openUnionPathValue_eq_subdivision S hU hV hcover D
    _ = openUnionCoveredEdgeValue S ambient true 0 1 := hsingle
    _ = S.right.map (Path.Homotopic.Quotient.mk p) := by
      rw [openUnionCoveredEdgeValue_eq_right_restricted S ambient 0 1 hcovered]
      apply singleObjFunctorPathValue_eq_of_coe
      intro t
      calc
        _ = ambient.subpath 0 1 t := rfl
        _ = ambient t :=
          congrArg ambient (Set.Icc.convexComb_zero_one t)
        _ = (p t : X) := rfl

/-- Helper for Theorem 70.1: the descended ambient path-class value restricts
to the left local functor on every left-cover arrow. -/
private lemma openUnionPathClassValue_map_left
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    {x y : U} (p : Path.Homotopic.Quotient x y) :
    openUnionPathClassValue S hU hV hcover
        (p.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))) =
      S.left.map p := by
  -- Quotient induction reduces the facet to the one-edge representative
  -- computation above.
  induction p using Quotient.inductionOn with
  | _ p => exact openUnionPathValue_map_left S hU hV hcover p

/-- Helper for Theorem 70.1: the descended ambient path-class value restricts
to the right local functor on every right-cover arrow. -/
private lemma openUnionPathClassValue_map_right
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    {x y : V} (p : Path.Homotopic.Quotient x y) :
    openUnionPathClassValue S hU hV hcover
        (p.map (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X))) =
      S.right.map p := by
  -- The right facet has the identical quotient-induction shape.
  induction p using Quotient.inductionOn with
  | _ p => exact openUnionPathValue_map_right S hU hV hcover p

/-- Helper for Theorem 70.1: the free-product map induced by the two inclusion maps
onto an open union is surjective. -/
private lemma fundamentalGroupCoprodMap_surjective {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace (U ∩ V : Set X)] :
    Function.Surjective
      (Monoid.Coprod.lift
        (FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩)
        (FundamentalGroup.mapOfSubtype V ⟨x₀, hx₀.2⟩)) := by
  -- The coproduct range is the join of the inclusion-map ranges.
  apply MonoidHom.range_eq_top.mp
  rw [Monoid.Coprod.range_lift]
  -- Theorem 59.1 identifies that join with the whole ambient fundamental group.
  exact fundamentalGroupMap_range_sup_range_eq_top U V x₀ hx₀ hU hV hcover

/-- Helper for Theorem 70.1: two homomorphisms agree when they agree on both factors of a
surjective free-product map. -/
private lemma monoidHom_eq_of_coprod_lift_surjective
    {G₁ G₂ K H : Type*} [Monoid G₁] [Monoid G₂] [Monoid K] [Monoid H]
    (f₁ : G₁ →* K) (f₂ : G₂ →* K)
    (hsurjective : Function.Surjective (Monoid.Coprod.lift f₁ f₂))
    {g h : K →* H} (hleft : g.comp f₁ = h.comp f₁)
    (hright : g.comp f₂ = h.comp f₂) : g = h := by
  -- Agreement on the factors gives agreement after precomposition with the coproduct map.
  have hagree : g.comp (Monoid.Coprod.lift f₁ f₂) =
      h.comp (Monoid.Coprod.lift f₁ f₂) := by
    apply Monoid.Coprod.hom_ext
    · simpa only [MonoidHom.comp_assoc, Monoid.Coprod.lift_comp_inl] using hleft
    · simpa only [MonoidHom.comp_assoc, Monoid.Coprod.lift_comp_inr] using hright
  -- Surjectivity then transports that agreement to every element of the target monoid.
  apply MonoidHom.ext
  intro x
  obtain ⟨x', rfl⟩ := hsurjective x
  exact DFunLike.congr_fun hagree x'

/-- Helper for Theorem 70.1: a prescribed map on a free product descends uniquely
through a surjective homomorphism when its kernel contains the kernel of that map. -/
private lemma existsUnique_coprodLift_extension
    {G₁ G₂ K H : Type*} [Group G₁] [Group G₂] [Group K] [Group H]
    (f₁ : G₁ →* K) (f₂ : G₂ →* K) (g₁ : G₁ →* H) (g₂ : G₂ →* H)
    (hsurjective : Function.Surjective (Monoid.Coprod.lift f₁ f₂))
    (hker : (Monoid.Coprod.lift f₁ f₂).ker ≤ (Monoid.Coprod.lift g₁ g₂).ker) :
    ∃! g : K →* H, g.comp f₁ = g₁ ∧ g.comp f₂ = g₂ := by
  let coverToK := Monoid.Coprod.lift f₁ f₂
  let coverToH := Monoid.Coprod.lift g₁ g₂
  let g : K →* H :=
    coverToK.liftOfSurjective hsurjective ⟨coverToH, hker⟩
  -- The quotient construction gives the prescribed map after precomposition.
  have factors : g.comp coverToK = coverToH := by
    simpa only [g, MonoidHom.liftOfSurjective] using
      coverToK.liftOfRightInverse_comp (Function.surjInv hsurjective)
        (Function.rightInverse_surjInv hsurjective) ⟨coverToH, hker⟩
  -- Restrict this factorization along the two coproduct inclusions.
  have restrictsLeft : g.comp f₁ = g₁ := by
    have hfactor := congrArg (fun k ↦ k.comp (Monoid.Coprod.inl : G₁ →* Monoid.Coprod G₁ G₂))
      factors
    simpa only [MonoidHom.comp_assoc, coverToK, coverToH,
      Monoid.Coprod.lift_comp_inl] using hfactor
  have restrictsRight : g.comp f₂ = g₂ := by
    have hfactor := congrArg (fun k ↦ k.comp (Monoid.Coprod.inr : G₂ →* Monoid.Coprod G₁ G₂))
      factors
    simpa only [MonoidHom.comp_assoc, coverToK, coverToH,
      Monoid.Coprod.lift_comp_inr] using hfactor
  -- Surjectivity makes those two restrictions determine the extension.
  refine ExistsUnique.intro g ⟨restrictsLeft, restrictsRight⟩ ?_
  intro k hk
  exact monoidHom_eq_of_coprod_lift_surjective f₁ f₂ hsurjective
    (hk.1.trans restrictsLeft.symm) (hk.2.trans restrictsRight.symm)

/-- Helper for Theorem 70.1: a standard free-product relator lies in the kernel
of a lifted map exactly when its two factor values agree. -/
private lemma coprodRelator_mem_ker_lift_iff
    {A B C K : Type*} [Group A] [Group B] [Group C] [Group K]
    (i₁ : C →* A) (i₂ : C →* B) (f₁ : A →* K) (f₂ : B →* K) (c : C) :
    (Monoid.Coprod.inl (i₁ c) * Monoid.Coprod.inr (i₂ c)⁻¹ : Monoid.Coprod A B) ∈
        (Monoid.Coprod.lift f₁ f₂).ker ↔
      (f₁.comp i₁) c = (f₂.comp i₂) c := by
  -- Evaluate the lift on both letters and cancel the inverse on the right.
  rw [MonoidHom.mem_ker]
  simp only [map_mul, map_inv, Monoid.Coprod.lift_apply_inl,
    Monoid.Coprod.lift_apply_inr, MonoidHom.comp_apply, mul_inv_eq_one]

/-- Helper for Theorem 70.1: `mapOfSubtype` is the fundamental-group map
of the canonical subtype inclusion. -/
private lemma mapOfSubtype_eq_map_subtypeVal {X : Type u} [TopologicalSpace X]
    (A : Set X) (a : A) :
    FundamentalGroup.mapOfSubtype A a =
      FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) a := by
  -- This is the owner definition, exposed as a propositional rewrite rule.
  rfl

/-- Helper for Theorem 70.1: inclusion through a subspace induces the same
fundamental-group map as direct inclusion into the ambient space. -/
private lemma mapOfSubtype_comp_mapOfSubset {X : Type u} [TopologicalSpace X]
    {A U : Set X} (h : A ⊆ U) (a : A) :
    (FundamentalGroup.mapOfSubtype U ⟨a, h a.property⟩).comp
        (FundamentalGroup.mapOfSubset h a) =
      FundamentalGroup.mapOfSubtype A a := by
  -- Expose the subset inclusion, then apply functoriality of path-class mapping.
  ext q
  simp only [MonoidHom.comp_apply]
  rw [FundamentalGroup.mapOfSubset_eq_map_inclusion,
    mapOfSubtype_eq_map_subtypeVal, mapOfSubtype_eq_map_subtypeVal]
  rw [FundamentalGroup.map_apply]
  exact (Path.Homotopic.Quotient.map_comp
    (p := q) (f := ContinuousMap.inclusion h)
    (g := (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)))).symm

/-- Helper for Theorem 70.1: every elementary intersection relator maps trivially
under the free-product map to the ambient fundamental group. -/
private lemma openUnionRelator_mem_coverKernel {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (g : FundamentalGroup (U ∩ V : Set X) ⟨x₀, hx₀⟩) :
    (Monoid.Coprod.inl
          (FundamentalGroup.mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩ g) *
        Monoid.Coprod.inr
          (FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩ g)⁻¹ :
        Monoid.Coprod (FundamentalGroup U ⟨x₀, hx₀.1⟩)
          (FundamentalGroup V ⟨x₀, hx₀.2⟩)) ∈
      (Monoid.Coprod.lift
        (FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩)
        (FundamentalGroup.mapOfSubtype V ⟨x₀, hx₀.2⟩)).ker := by
  -- Both composites simply forget the intersection subtype layer.
  rw [coprodRelator_mem_ker_lift_iff]
  have hleft := mapOfSubtype_comp_mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩
  have hright := mapOfSubtype_comp_mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩
  exact DFunLike.congr_fun (hleft.trans hright.symm) g

/-- Helper for Theorem 70.1: compatibility makes every elementary intersection
relator map trivially under the prescribed free-product homomorphism. -/
private lemma openUnionRelator_mem_prescribedKernel {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) {H : Type v} [Group H]
    (φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H)
    (φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H)
    (hφ : φ₁.comp (FundamentalGroup.mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩) =
      φ₂.comp (FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩))
    (g : FundamentalGroup (U ∩ V : Set X) ⟨x₀, hx₀⟩) :
    (Monoid.Coprod.inl
          (FundamentalGroup.mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩ g) *
        Monoid.Coprod.inr
          (FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩ g)⁻¹ :
        Monoid.Coprod (FundamentalGroup U ⟨x₀, hx₀.1⟩)
          (FundamentalGroup V ⟨x₀, hx₀.2⟩)) ∈
      (Monoid.Coprod.lift φ₁ φ₂).ker := by
  -- The abstract relator criterion reduces the claim to the given compatibility.
  rw [coprodRelator_mem_ker_lift_iff]
  exact DFunLike.congr_fun hφ g

/-- Helper for Theorem 70.1: a descent of compatible local functors consists
of a global fundamental-groupoid functor together with its two cover facets. -/
private structure OpenUnionLocalSystem.Descent
    {X : Type u} [TopologicalSpace X]
    {U V : Set X} {x₀ : X} {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂) where
  global : FundamentalGroupoid X ⥤ CategoryTheory.SingleObj H
  map_left : ∀ {x y : FundamentalGroupoid U} (p : x ⟶ y),
    global.map
        ((FundamentalGroupoid.map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))).map p) =
      S.left.map p
  map_right : ∀ {x y : FundamentalGroupoid V} (p : x ⟶ y),
    global.map
        ((FundamentalGroupoid.map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X))).map p) =
      S.right.map p

/-- Helper for Theorem 70.1: compatible one-object-valued functors on two
open cover members descend to the ambient fundamental groupoid. -/
private lemma OpenUnionLocalSystem.exists_descent
    {X : Type u} [TopologicalSpace X]
    {U V : Set X} {x₀ : X} {hx₀ : x₀ ∈ U ∩ V} {H : Type v} [Group H]
    {φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H}
    {φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H}
    (S : OpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    Nonempty S.Descent := by
  -- Route correction: the blocked Fin-indexed concatenation was replaced by
  -- recursive affine maps and append. Its value law now supplies the global
  -- functor, while one-edge subdivisions prove the two cover facets.
  refine ⟨{ global := openUnionGlobalPathFunctor S hU hV hcover,
              map_left := ?_,
              map_right := ?_ }⟩
  · intro x y p
    exact openUnionPathClassValue_map_left S hU hV hcover p
  · intro x y p
    exact openUnionPathClassValue_map_right S hU hV hcover p

/-- Helper for Theorem 70.1: compatible local homomorphisms admit a global
extension across a path-connected open union. -/
private lemma existsOpenUnionExtension {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)] {H : Type v} [Group H]
    (φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H)
    (φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H)
    (hφ : φ₁.comp (FundamentalGroup.mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩) =
      φ₂.comp (FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩)) :
    ∃ Φ : FundamentalGroup X x₀ →* H,
      Φ.comp (FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩) = φ₁ ∧
      Φ.comp (FundamentalGroup.mapOfSubtype V ⟨x₀, hx₀.2⟩) = φ₂ := by
  -- Route correction: descend the verified local functors first, then take the
  -- vertex-group homomorphism of the resulting ambient groupoid functor.
  let localSystem := compatibleOpenUnionLocalSystem U V x₀ hx₀ φ₁ φ₂ hφ
  obtain ⟨descent⟩ := localSystem.exists_descent hU hV hcover
  let Φ := descent.global.mapEnd (FundamentalGroupoid.mk x₀)
  -- Each restriction follows from the matching descent facet and the local
  -- system's computation at the distinguished base object.
  refine ⟨Φ, ?_, ?_⟩
  · apply MonoidHom.ext
    intro f
    simp only [Φ, MonoidHom.comp_apply, mapOfSubtype_eq_map_subtypeVal]
    calc
      _ = localSystem.left.map f := descent.map_left f
      _ = φ₁ f := DFunLike.congr_fun localSystem.left_at_base f
  · apply MonoidHom.ext
    intro f
    simp only [Φ, MonoidHom.comp_apply, mapOfSubtype_eq_map_subtypeVal]
    calc
      _ = localSystem.right.map f := descent.map_right f
      _ = φ₂ f := DFunLike.congr_fun localSystem.right_at_base f

/-- Helper for Theorem 70.1: compatibility on the intersection supplies the kernel
inclusion needed to descend the prescribed free-product homomorphism. -/
private lemma openUnionCoprod_ker_le {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)] {H : Type v} [Group H]
    (φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H)
    (φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H)
    (hφ : φ₁.comp (FundamentalGroup.mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩) =
      φ₂.comp (FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩)) :
    (Monoid.Coprod.lift
      (FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩)
      (FundamentalGroup.mapOfSubtype V ⟨x₀, hx₀.2⟩)).ker ≤
      (Monoid.Coprod.lift φ₁ φ₂).ker := by
  -- Route correction: obtain the global map from the covered-path invariant, then
  -- deduce the kernel relation purely by free-product factorization.
  obtain ⟨Φ, hΦU, hΦV⟩ :=
    existsOpenUnionExtension U V x₀ hx₀ hU hV hcover φ₁ φ₂ hφ
  let coverToX := Monoid.Coprod.lift
    (FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩)
    (FundamentalGroup.mapOfSubtype V ⟨x₀, hx₀.2⟩)
  let coverToH := Monoid.Coprod.lift φ₁ φ₂
  -- Agreement on both factors identifies the two maps from the free product.
  have hfactor : Φ.comp coverToX = coverToH := by
    apply Monoid.Coprod.hom_ext
    · simpa only [MonoidHom.comp_assoc, coverToX, coverToH,
        Monoid.Coprod.lift_comp_inl] using hΦU
    · simpa only [MonoidHom.comp_assoc, coverToX, coverToH,
        Monoid.Coprod.lift_comp_inr] using hΦV
  -- A word killed by the ambient map is therefore killed by the prescribed map.
  intro w hw
  rw [MonoidHom.mem_ker] at hw ⊢
  have hwFactor := DFunLike.congr_fun hfactor w
  rw [MonoidHom.comp_apply, hw, map_one] at hwFactor
  exact hwFactor.symm

/-- Theorem 70.1 (Seifert-van Kampen theorem): Compatible homomorphisms from the
fundamental groups of two path-connected open subsets uniquely extend to the fundamental
group of their union. -/
theorem seifertVanKampen {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)] {H : Type v} [Group H]
    (φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H)
    (φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H)
    (hφ : φ₁.comp (FundamentalGroup.mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩) =
      φ₂.comp (FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩)) :
    ∃! Φ : FundamentalGroup X x₀ →* H,
      Φ.comp (FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩) = φ₁ ∧
      Φ.comp (FundamentalGroup.mapOfSubtype V ⟨x₀, hx₀.2⟩) = φ₂ := by
  -- Route correction: descend the prescribed coproduct map directly through the
  -- surjective map onto the ambient fundamental group.
  let inclusionFromU := FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩
  let inclusionFromV := FundamentalGroup.mapOfSubtype V ⟨x₀, hx₀.2⟩
  -- Theorem 59.1 says that the free-product map onto the ambient fundamental group is onto.
  have coverToXSurjective :
      Function.Surjective (Monoid.Coprod.lift inclusionFromU inclusionFromV) := by
    simpa only [inclusionFromU, inclusionFromV] using
      fundamentalGroupCoprodMap_surjective U V x₀ hx₀ hU hV hcover
  -- The covered-path argument supplies precisely the remaining descent condition.
  have coverKernelLe :
      (Monoid.Coprod.lift inclusionFromU inclusionFromV).ker ≤
        (Monoid.Coprod.lift φ₁ φ₂).ker := by
    simpa only [inclusionFromU, inclusionFromV] using
      openUnionCoprod_ker_le U V x₀ hx₀ hU hV hcover φ₁ φ₂ hφ
  -- The algebraic descent lemma now gives both existence and uniqueness.
  exact existsUnique_coprodLift_extension inclusionFromU inclusionFromV φ₁ φ₂
    coverToXSurjective coverKernelLe

/-- Helper for Theorem 70.1: close a groupoid arrow by independently chosen
connectors at its source and target. -/
private lemma basedLoop_comp_connectors {C : Type u} [Groupoid.{v} C]
    (b : C) {x y z : C} (qx : b ⟶ x) (qy : b ⟶ y) (qz : b ⟶ z)
    (f : x ⟶ y) (g : y ⟶ z) :
    End.of (qx ≫ (f ≫ g) ≫ Groupoid.inv qz) =
      End.of (qy ≫ g ≫ Groupoid.inv qz) *
        End.of (qx ≫ f ≫ Groupoid.inv qy) := by
  -- Reassociate until the middle connector cancels with its inverse.
  simp [End.mul_def, Category.assoc]

/-- Helper for Theorem 70.1: a based homomorphism assigns a value to arrows in
the base component and the identity to arrows in every other component. -/
private noncomputable def componentBasedPathMap {C : Type u} [Groupoid.{v} C]
    {H : Type*} [Group H] (b : C)
    (q : ∀ (x : C), Nonempty (b ⟶ x) → (b ⟶ x)) (k : End b →* H)
    {x y : C} (f : x ⟶ y) : H :=
  @dite H (Nonempty (b ⟶ x)) (Classical.propDecidable _)
    (fun hx ↦
      k (End.of (q x hx ≫ f ≫ Groupoid.inv (q y ⟨q x hx ≫ f⟩))))
    (fun _ ↦ 1)

/-- Helper for Theorem 70.1: the componentwise based-arrow assignment preserves
identity arrows. -/
private lemma componentBasedPathMap_id {C : Type u} [Groupoid.{v} C]
    {H : Type*} [Group H] (b : C)
    (q : ∀ (x : C), Nonempty (b ⟶ x) → (b ⟶ x)) (k : End b →* H)
    (x : C) :
    componentBasedPathMap b q k (CategoryStruct.id x) =
      𝟙 (CategoryTheory.SingleObj.star H) := by
  -- On the base component the connector cancels; off it the value is defined as one.
  by_cases hx : Nonempty (b ⟶ x)
  · have hq : q x ⟨q x hx ≫ 𝟙 x⟩ = q x hx := by
      exact congrArg (q x) (Subsingleton.elim _ _)
    simp only [componentBasedPathMap, dif_pos hx]
    rw [hq]
    have hloop : End.of (q x hx ≫ 𝟙 x ≫ Groupoid.inv (q x hx)) =
        (1 : End b) := by
      simp
    rw [hloop, map_one]
    rfl
  · simp only [componentBasedPathMap, dif_neg hx]
    rfl

/-- Helper for Theorem 70.1: the componentwise based-arrow assignment preserves
composition. -/
private lemma componentBasedPathMap_comp {C : Type u} [Groupoid.{v} C]
    {H : Type*} [Group H] (b : C)
    (q : ∀ (x : C), Nonempty (b ⟶ x) → (b ⟶ x)) (k : End b →* H)
    {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    componentBasedPathMap b q k (f ≫ g) =
      componentBasedPathMap b q k g * componentBasedPathMap b q k f := by
  -- A morphism cannot cross groupoid components, so both cases are stable under composition.
  by_cases hx : Nonempty (b ⟶ x)
  · let qx := q x hx
    have hy : Nonempty (b ⟶ y) := ⟨qx ≫ f⟩
    simp only [componentBasedPathMap, dif_pos hx, dif_pos hy]
    rw [basedLoop_comp_connectors, map_mul]
  · have hy : ¬ Nonempty (b ⟶ y) := by
      rintro ⟨qy⟩
      exact hx ⟨qy ≫ Groupoid.inv f⟩
    simp only [componentBasedPathMap, dif_neg hx, dif_neg hy, mul_one]

/-- Helper for Theorem 70.1: a homomorphism on one vertex group extends to the
whole groupoid by using connectors on its component and trivial values elsewhere. -/
private noncomputable def componentBasedPathFunctor {C : Type u} [Groupoid.{v} C]
    {H : Type*} [Group H] (b : C)
    (q : ∀ (x : C), Nonempty (b ⟶ x) → (b ⟶ x)) (k : End b →* H) :
    C ⥤ CategoryTheory.SingleObj H :=
  { obj := fun _ ↦ CategoryTheory.SingleObj.star H
    map := fun f ↦ componentBasedPathMap b q k f
    map_id := componentBasedPathMap_id b q k
    map_comp := componentBasedPathMap_comp b q k }

/-- Helper for Theorem 70.1: identity normalization of the base connector makes
the componentwise functor recover the prescribed vertex-group homomorphism. -/
private lemma componentBasedPathFunctor_map_at_base
    {C : Type u} [Groupoid.{v} C] {H : Type*} [Group H] (b : C)
    (q : ∀ (x : C), Nonempty (b ⟶ x) → (b ⟶ x)) (k : End b →* H)
    (hq : ∀ h : Nonempty (b ⟶ b), q b h = 𝟙 b) (f : End b) :
    (componentBasedPathFunctor b q k).map f = k f := by
  -- Both connectors around a based loop are identities.
  simp only [componentBasedPathFunctor, componentBasedPathMap,
    dif_pos (⟨𝟙 b⟩ : Nonempty (b ⟶ b))]
  rw [hq]
  have hloop : End.of (𝟙 b ≫ End.asHom f ≫ Groupoid.inv (𝟙 b)) = f := by
    simp
  rw [hloop]

/-- Helper for Theorem 70.1: the base-component connector in `U` uses the
common intersection connector whenever its endpoint lies in `V`. -/
private noncomputable def leftComponentConnector
    {X : Type u} [TopologicalSpace X] (U V : Set X) (x₀ : X)
    (hx₀ : x₀ ∈ U ∩ V) [PathConnectedSpace (U ∩ V : Set X)]
    (x : FundamentalGroupoid U)
    (h : Nonempty
      (FundamentalGroupoid.mk (⟨x₀, hx₀.1⟩ : U) ⟶ x)) :
    FundamentalGroupoid.mk (⟨x₀, hx₀.1⟩ : U) ⟶ x :=
  @dite
    (FundamentalGroupoid.mk (⟨x₀, hx₀.1⟩ : U) ⟶ x)
    (x.as.1 ∈ V) (Classical.propDecidable _)
    (fun hxV ↦
      (FundamentalGroupoid.map
        (ContinuousMap.inclusion Set.inter_subset_left)).map
          ⟦intersectionConnector U V x₀ hx₀ ⟨x.as.1, x.as.2, hxV⟩⟧)
    (fun _ ↦ Classical.choice h)

/-- Helper for Theorem 70.1: the base-component connector in `V` uses the
common intersection connector whenever its endpoint lies in `U`. -/
private noncomputable def rightComponentConnector
    {X : Type u} [TopologicalSpace X] (U V : Set X) (x₀ : X)
    (hx₀ : x₀ ∈ U ∩ V) [PathConnectedSpace (U ∩ V : Set X)]
    (x : FundamentalGroupoid V)
    (h : Nonempty
      (FundamentalGroupoid.mk (⟨x₀, hx₀.2⟩ : V) ⟶ x)) :
    FundamentalGroupoid.mk (⟨x₀, hx₀.2⟩ : V) ⟶ x :=
  @dite
    (FundamentalGroupoid.mk (⟨x₀, hx₀.2⟩ : V) ⟶ x)
    (x.as.1 ∈ U) (Classical.propDecidable _)
    (fun hxU ↦
      (FundamentalGroupoid.map
        (ContinuousMap.inclusion Set.inter_subset_right)).map
          ⟦intersectionConnector U V x₀ hx₀ ⟨x.as.1, hxU, x.as.2⟩⟧)
    (fun _ ↦ Classical.choice h)

/-- Helper for Theorem 70.1: the component connector in `U` is the identity at
the distinguished basepoint. -/
private lemma leftComponentConnector_at_base
    {X : Type u} [TopologicalSpace X] (U V : Set X) (x₀ : X)
    (hx₀ : x₀ ∈ U ∩ V) [PathConnectedSpace (U ∩ V : Set X)]
    (h : Nonempty
      (FundamentalGroupoid.mk (⟨x₀, hx₀.1⟩ : U) ⟶
        FundamentalGroupoid.mk (⟨x₀, hx₀.1⟩ : U))) :
    leftComponentConnector U V x₀ hx₀
        (FundamentalGroupoid.mk (⟨x₀, hx₀.1⟩ : U)) h =
      𝟙 (FundamentalGroupoid.mk (⟨x₀, hx₀.1⟩ : U)) := by
  -- The intersection connector chooses the constant path at the basepoint.
  simp only [leftComponentConnector, hx₀.2, dite_true,
    intersectionConnector, pathOfEq]
  rfl

/-- Helper for Theorem 70.1: the component connector in `V` is the identity at
the distinguished basepoint. -/
private lemma rightComponentConnector_at_base
    {X : Type u} [TopologicalSpace X] (U V : Set X) (x₀ : X)
    (hx₀ : x₀ ∈ U ∩ V) [PathConnectedSpace (U ∩ V : Set X)]
    (h : Nonempty
      (FundamentalGroupoid.mk (⟨x₀, hx₀.2⟩ : V) ⟶
        FundamentalGroupoid.mk (⟨x₀, hx₀.2⟩ : V))) :
    rightComponentConnector U V x₀ hx₀
        (FundamentalGroupoid.mk (⟨x₀, hx₀.2⟩ : V)) h =
      𝟙 (FundamentalGroupoid.mk (⟨x₀, hx₀.2⟩ : V)) := by
  -- The symmetric intersection connector is also constant at the basepoint.
  simp only [rightComponentConnector, hx₀.1, dite_true,
    intersectionConnector, pathOfEq]
  rfl

/-- Helper for Theorem 70.1: on an intersection object, the `U` component
connector is the image of the common connector. -/
private lemma leftComponentConnector_intersection
    {X : Type u} [TopologicalSpace X] (U V : Set X) (x₀ : X)
    (hx₀ : x₀ ∈ U ∩ V) [PathConnectedSpace (U ∩ V : Set X)]
    (x : (U ∩ V : Set X))
    (h : Nonempty
      (FundamentalGroupoid.mk (⟨x₀, hx₀.1⟩ : U) ⟶
        FundamentalGroupoid.mk (⟨x.1, x.2.1⟩ : U))) :
    leftComponentConnector U V x₀ hx₀
        (FundamentalGroupoid.mk (⟨x.1, x.2.1⟩ : U)) h =
      (FundamentalGroupoid.map
        (ContinuousMap.inclusion Set.inter_subset_left)).map
          ⟦intersectionConnector U V x₀ hx₀ x⟧ := by
  -- Membership in the other cover member selects the common branch.
  simp only [leftComponentConnector, x.2.2, dite_true]

/-- Helper for Theorem 70.1: on an intersection object, the `V` component
connector is the image of the common connector. -/
private lemma rightComponentConnector_intersection
    {X : Type u} [TopologicalSpace X] (U V : Set X) (x₀ : X)
    (hx₀ : x₀ ∈ U ∩ V) [PathConnectedSpace (U ∩ V : Set X)]
    (x : (U ∩ V : Set X))
    (h : Nonempty
      (FundamentalGroupoid.mk (⟨x₀, hx₀.2⟩ : V) ⟶
        FundamentalGroupoid.mk (⟨x.1, x.2.2⟩ : V))) :
    rightComponentConnector U V x₀ hx₀
        (FundamentalGroupoid.mk (⟨x.1, x.2.2⟩ : V)) h =
      (FundamentalGroupoid.map
        (ContinuousMap.inclusion Set.inter_subset_right)).map
          ⟦intersectionConnector U V x₀ hx₀ x⟧ := by
  -- Membership in the left cover member selects the symmetric common branch.
  simp only [rightComponentConnector, x.2.1, dite_true]

/-- Helper for Theorem 70.1: a homomorphism on the based fundamental group of
`U` extends componentwise to its fundamental groupoid. -/
private noncomputable def leftComponentPathFunctor
    {X : Type u} [TopologicalSpace X] (U V : Set X) (x₀ : X)
    (hx₀ : x₀ ∈ U ∩ V) [PathConnectedSpace (U ∩ V : Set X)]
    {H : Type v} [Group H]
    (k : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H) :
    FundamentalGroupoid U ⥤ CategoryTheory.SingleObj H :=
  componentBasedPathFunctor
    (FundamentalGroupoid.mk (⟨x₀, hx₀.1⟩ : U))
    (leftComponentConnector U V x₀ hx₀) k

/-- Helper for Theorem 70.1: a homomorphism on the based fundamental group of
`V` extends componentwise to its fundamental groupoid. -/
private noncomputable def rightComponentPathFunctor
    {X : Type u} [TopologicalSpace X] (U V : Set X) (x₀ : X)
    (hx₀ : x₀ ∈ U ∩ V) [PathConnectedSpace (U ∩ V : Set X)]
    {H : Type v} [Group H]
    (k : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H) :
    FundamentalGroupoid V ⥤ CategoryTheory.SingleObj H :=
  componentBasedPathFunctor
    (FundamentalGroupoid.mk (⟨x₀, hx₀.2⟩ : V))
    (rightComponentConnector U V x₀ hx₀) k

/-- Helper for Theorem 70.1: the componentwise functor on `U` recovers its
prescribed homomorphism at the basepoint. -/
private lemma leftComponentPathFunctor_mapEnd_eq
    {X : Type u} [TopologicalSpace X] (U V : Set X) (x₀ : X)
    (hx₀ : x₀ ∈ U ∩ V) [PathConnectedSpace (U ∩ V : Set X)]
    {H : Type v} [Group H]
    (k : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H) :
    (leftComponentPathFunctor U V x₀ hx₀ k).mapEnd
        (FundamentalGroupoid.mk (⟨x₀, hx₀.1⟩ : U)) = k := by
  -- Use the generic basepoint computation and the normalized connector.
  apply MonoidHom.ext
  intro f
  exact componentBasedPathFunctor_map_at_base
    (FundamentalGroupoid.mk (⟨x₀, hx₀.1⟩ : U))
    (leftComponentConnector U V x₀ hx₀) k
    (leftComponentConnector_at_base U V x₀ hx₀) f

/-- Helper for Theorem 70.1: the componentwise functor on `V` recovers its
prescribed homomorphism at the basepoint. -/
private lemma rightComponentPathFunctor_mapEnd_eq
    {X : Type u} [TopologicalSpace X] (U V : Set X) (x₀ : X)
    (hx₀ : x₀ ∈ U ∩ V) [PathConnectedSpace (U ∩ V : Set X)]
    {H : Type v} [Group H]
    (k : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H) :
    (rightComponentPathFunctor U V x₀ hx₀ k).mapEnd
        (FundamentalGroupoid.mk (⟨x₀, hx₀.2⟩ : V)) = k := by
  -- Apply the same basepoint computation on the right.
  apply MonoidHom.ext
  intro f
  exact componentBasedPathFunctor_map_at_base
    (FundamentalGroupoid.mk (⟨x₀, hx₀.2⟩ : V))
    (rightComponentConnector U V x₀ hx₀) k
    (rightComponentConnector_at_base U V x₀ hx₀) f

/-- Helper for Theorem 70.1: componentwise connector functors induced by
compatible homomorphisms agree on every arrow of `U ∩ V`. -/
private lemma componentPathFunctors_agree_on_intersection
    {X : Type u} [TopologicalSpace X] (U V : Set X) (x₀ : X)
    (hx₀ : x₀ ∈ U ∩ V) [PathConnectedSpace (U ∩ V : Set X)]
    {H : Type v} [Group H]
    (kU : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H)
    (kV : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H)
    (hk : kU.comp (FundamentalGroup.mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩) =
      kV.comp (FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩))
    {x y : FundamentalGroupoid (U ∩ V : Set X)} (p : x ⟶ y) :
    (leftComponentPathFunctor U V x₀ hx₀ kU).map
        ((FundamentalGroupoid.map
          (ContinuousMap.inclusion Set.inter_subset_left)).map p) =
      (rightComponentPathFunctor U V x₀ hx₀ kV).map
        ((FundamentalGroupoid.map
          (ContinuousMap.inclusion Set.inter_subset_right)).map p) := by
  -- Close the arrow with the common intersection connectors.
  let qx : FundamentalGroupoid.mk (⟨x₀, hx₀⟩ : (U ∩ V : Set X)) ⟶ x :=
    ⟦intersectionConnector U V x₀ hx₀ x.as⟧
  let qy : FundamentalGroupoid.mk (⟨x₀, hx₀⟩ : (U ∩ V : Set X)) ⟶ y :=
    ⟦intersectionConnector U V x₀ hx₀ y.as⟧
  let loop : FundamentalGroup (U ∩ V : Set X) ⟨x₀, hx₀⟩ :=
    End.of (qx ≫ p ≫ Groupoid.inv qy)
  let leftInclusion :
      FundamentalGroupoid (U ∩ V : Set X) ⥤ FundamentalGroupoid U :=
    FundamentalGroupoid.map (ContinuousMap.inclusion Set.inter_subset_left)
  let rightInclusion :
      FundamentalGroupoid (U ∩ V : Set X) ⥤ FundamentalGroupoid V :=
    FundamentalGroupoid.map (ContinuousMap.inclusion Set.inter_subset_right)
  have hleftConnected : Nonempty
      (FundamentalGroupoid.mk (⟨x₀, hx₀.1⟩ : U) ⟶ leftInclusion.obj x) :=
    ⟨leftInclusion.map qx⟩
  have hrightConnected : Nonempty
      (FundamentalGroupoid.mk (⟨x₀, hx₀.2⟩ : V) ⟶ rightInclusion.obj x) :=
    ⟨rightInclusion.map qx⟩
  have hleftX (h : Nonempty
      (FundamentalGroupoid.mk (⟨x₀, hx₀.1⟩ : U) ⟶ leftInclusion.obj x)) :
      leftComponentConnector U V x₀ hx₀ (leftInclusion.obj x) h =
        leftInclusion.map qx := by
    exact leftComponentConnector_intersection U V x₀ hx₀ x.as h
  have hleftY (h : Nonempty
      (FundamentalGroupoid.mk (⟨x₀, hx₀.1⟩ : U) ⟶ leftInclusion.obj y)) :
      leftComponentConnector U V x₀ hx₀ (leftInclusion.obj y) h =
        leftInclusion.map qy := by
    exact leftComponentConnector_intersection U V x₀ hx₀ y.as h
  have hrightX (h : Nonempty
      (FundamentalGroupoid.mk (⟨x₀, hx₀.2⟩ : V) ⟶ rightInclusion.obj x)) :
      rightComponentConnector U V x₀ hx₀ (rightInclusion.obj x) h =
        rightInclusion.map qx := by
    exact rightComponentConnector_intersection U V x₀ hx₀ x.as h
  have hrightY (h : Nonempty
      (FundamentalGroupoid.mk (⟨x₀, hx₀.2⟩ : V) ⟶ rightInclusion.obj y)) :
      rightComponentConnector U V x₀ hx₀ (rightInclusion.obj y) h =
        rightInclusion.map qy := by
    exact rightComponentConnector_intersection U V x₀ hx₀ y.as h
  -- Each closed cover arrow is the corresponding image of the intersection loop.
  have hleftClosed :
      End.of
          (leftInclusion.map qx ≫ leftInclusion.map p ≫
            Groupoid.inv (leftInclusion.map qy)) =
        FundamentalGroup.mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩ loop := by
    calc
      _ = End.of (leftInclusion.map
          (qx ≫ p ≫ Groupoid.inv qy)) :=
        endOf_map_closedArrow leftInclusion qx p qy
      _ = _ := rfl
  have hrightClosed :
      End.of
          (rightInclusion.map qx ≫ rightInclusion.map p ≫
            Groupoid.inv (rightInclusion.map qy)) =
        FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩ loop := by
    calc
      _ = End.of (rightInclusion.map
          (qx ≫ p ≫ Groupoid.inv qy)) :=
        endOf_map_closedArrow rightInclusion qx p qy
      _ = _ := rfl
  have hcompat :
      kU (FundamentalGroup.mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩ loop) =
        kV (FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩ loop) := by
    exact DFunLike.congr_fun hk loop
  simp only [leftComponentPathFunctor, rightComponentPathFunctor,
    componentBasedPathFunctor, componentBasedPathMap]
  dsimp only [leftInclusion, rightInclusion] at hleftConnected hrightConnected
  rw [dif_pos hleftConnected, dif_pos hrightConnected]
  rw [hleftX, hleftY, hrightX, hrightY]
  calc
    _ = kU (FundamentalGroup.mapOfSubset Set.inter_subset_left
        ⟨x₀, hx₀⟩ loop) := congrArg kU hleftClosed
    _ = kV (FundamentalGroup.mapOfSubset Set.inter_subset_right
        ⟨x₀, hx₀⟩ loop) := hcompat
    _ = _ := congrArg kV hrightClosed.symm

/-- Helper for Theorem 70.1: compatible based homomorphisms define local
fundamental-groupoid functors without requiring the cover members themselves
to be path connected. -/
private noncomputable def compatibleOpenUnionComponentLocalSystem
    {X : Type u} [TopologicalSpace X] (U V : Set X) (x₀ : X)
    (hx₀ : x₀ ∈ U ∩ V) [PathConnectedSpace (U ∩ V : Set X)]
    {H : Type v} [Group H]
    (kU : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H)
    (kV : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H)
    (hk : kU.comp (FundamentalGroup.mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩) =
      kV.comp (FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩)) :
    OpenUnionLocalSystem U V x₀ hx₀ kU kV :=
  { left := leftComponentPathFunctor U V x₀ hx₀ kU
    right := rightComponentPathFunctor U V x₀ hx₀ kV
    agree := componentPathFunctors_agree_on_intersection U V x₀ hx₀ kU kV hk
    left_at_base := leftComponentPathFunctor_mapEnd_eq U V x₀ hx₀ kU
    right_at_base := rightComponentPathFunctor_mapEnd_eq U V x₀ hx₀ kV }

/-- Helper for Theorem 70.1: compatible based homomorphisms extend uniquely
across an open union once the intersection is path connected. -/
private lemma existsOpenUnionExtension_of_intersection_pathConnected
    {X : Type u} [TopologicalSpace X] (U V : Set X) (x₀ : X)
    (hx₀ : x₀ ∈ U ∩ V)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace (U ∩ V : Set X)] {H : Type v} [Group H]
    (kU : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H)
    (kV : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H)
    (hk : kU.comp (FundamentalGroup.mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩) =
      kV.comp (FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩)) :
    ∃ Φ : FundamentalGroup X x₀ →* H,
      Φ.comp (FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩) = kU ∧
      Φ.comp (FundamentalGroup.mapOfSubtype V ⟨x₀, hx₀.2⟩) = kV := by
  -- Descend the coherent componentwise local functors, then take the base vertex group.
  let localSystem :=
    compatibleOpenUnionComponentLocalSystem U V x₀ hx₀ kU kV hk
  obtain ⟨descent⟩ := localSystem.exists_descent hU hV hcover
  let Φ := descent.global.mapEnd (FundamentalGroupoid.mk x₀)
  refine ⟨Φ, ?_, ?_⟩
  · apply MonoidHom.ext
    intro f
    simp only [Φ, MonoidHom.comp_apply, mapOfSubtype_eq_map_subtypeVal]
    calc
      _ = localSystem.left.map f := descent.map_left f
      _ = kU f := DFunLike.congr_fun localSystem.left_at_base f
  · apply MonoidHom.ext
    intro f
    simp only [Φ, MonoidHom.comp_apply, mapOfSubtype_eq_map_subtypeVal]
    calc
      _ = localSystem.right.map f := descent.map_right f
      _ = kV f := DFunLike.congr_fun localSystem.right_at_base f

namespace FundamentalGroup

/-- Helper for Theorem 70.1: the fundamental-group square of an open cover is a
pushout in the category of groups. -/
theorem isPushoutOfOpenUnion_of_pathConnected {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)] :
    IsPushout
      (GrpCat.ofHom (mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩))
      (GrpCat.ofHom (mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩))
      (GrpCat.ofHom (mapOfSubtype U ⟨x₀, hx₀.1⟩))
      (GrpCat.ofHom (mapOfSubtype V ⟨x₀, hx₀.2⟩)) := by
  -- The two composites are both induced by the direct subtype inclusion.
  apply IsPushout.mk'
  · rw [← GrpCat.ofHom_comp, ← GrpCat.ofHom_comp]
    exact congrArg GrpCat.ofHom
      ((mapOfSubtype_comp_mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩).trans
        (mapOfSubtype_comp_mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩).symm)
  · intro T φ φ' hφU hφV
    let inclusionFromU := mapOfSubtype U ⟨x₀, hx₀.1⟩
    let inclusionFromV := mapOfSubtype V ⟨x₀, hx₀.2⟩
    let prescribedU := φ.hom.comp inclusionFromU
    let prescribedV := φ.hom.comp inclusionFromV
    have hcompatible :
        prescribedU.comp (mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩) =
          prescribedV.comp (mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩) := by
      dsimp only [prescribedU, prescribedV, inclusionFromU, inclusionFromV]
      rw [MonoidHom.comp_assoc, MonoidHom.comp_assoc]
      exact congrArg (fun k ↦ φ.hom.comp k)
        ((mapOfSubtype_comp_mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩).trans
          (mapOfSubtype_comp_mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩).symm)
    obtain ⟨Φ, _, hΦ_unique⟩ :=
      seifertVanKampen U V x₀ hx₀ hU hV hcover prescribedU prescribedV hcompatible
    have hφU_hom : φ'.hom.comp inclusionFromU = prescribedU := by
      exact (congrArg GrpCat.Hom.hom hφU).symm
    have hφV_hom : φ'.hom.comp inclusionFromV = prescribedV := by
      exact (congrArg GrpCat.Hom.hom hφV).symm
    apply GrpCat.hom_ext
    exact (hΦ_unique φ.hom ⟨rfl, rfl⟩).trans
      (hΦ_unique φ'.hom ⟨hφU_hom, hφV_hom⟩).symm
  · intro T a b hab
    have hcompatible :
        a.hom.comp (mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩) =
          b.hom.comp (mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩) := by
      exact congrArg GrpCat.Hom.hom hab
    obtain ⟨Φ, hΦ, _⟩ :=
      seifertVanKampen U V x₀ hx₀ hU hV hcover a.hom b.hom hcompatible
    refine ⟨GrpCat.ofHom Φ, ?_, ?_⟩
    · rw [← GrpCat.ofHom_comp, hΦ.1]
      rfl
    · rw [← GrpCat.ofHom_comp, hΦ.2]
      rfl

/-- The pushout form of Theorem 70.1 for an open union whose intersection is
path connected; disconnected components of the two cover members do not affect
the based fundamental groups. -/
theorem isPushoutOfOpenUnion {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace (U ∩ V : Set X)] :
    IsPushout
      (GrpCat.ofHom (mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩))
      (GrpCat.ofHom (mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩))
      (GrpCat.ofHom (mapOfSubtype U ⟨x₀, hx₀.1⟩))
      (GrpCat.ofHom (mapOfSubtype V ⟨x₀, hx₀.2⟩)) := by
  -- The square commutes because both composites are the direct inclusion map.
  apply IsPushout.mk'
  · rw [← GrpCat.ofHom_comp, ← GrpCat.ofHom_comp]
    exact congrArg GrpCat.ofHom
      ((mapOfSubtype_comp_mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩).trans
        (mapOfSubtype_comp_mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩).symm)
  · intro T φ φ' hφU hφV
    let inclusionFromU := mapOfSubtype U ⟨x₀, hx₀.1⟩
    let inclusionFromV := mapOfSubtype V ⟨x₀, hx₀.2⟩
    have hsurjective :
        Function.Surjective
          (Monoid.Coprod.lift inclusionFromU inclusionFromV) := by
      simpa only [inclusionFromU, inclusionFromV] using
        fundamentalGroupCoprodMap_surjective U V x₀ hx₀ hU hV hcover
    apply GrpCat.hom_ext
    apply monoidHom_eq_of_coprod_lift_surjective
      inclusionFromU inclusionFromV hsurjective
    · exact congrArg GrpCat.Hom.hom hφU
    · exact congrArg GrpCat.Hom.hom hφV
  · intro T a b hab
    have hcompatible :
        a.hom.comp (mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩) =
          b.hom.comp (mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩) := by
      exact congrArg GrpCat.Hom.hom hab
    obtain ⟨Φ, hΦU, hΦV⟩ :=
      existsOpenUnionExtension_of_intersection_pathConnected
        U V x₀ hx₀ hU hV hcover a.hom b.hom hcompatible
    refine ⟨GrpCat.ofHom Φ, ?_, ?_⟩
    · rw [← GrpCat.ofHom_comp, hΦU]
      rfl
    · rw [← GrpCat.ofHom_comp, hΦV]
      rfl

end FundamentalGroup
