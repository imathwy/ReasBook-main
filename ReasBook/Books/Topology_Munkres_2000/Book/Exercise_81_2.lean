module

public import Topology_Munkres_2000.Book.Definition_53_5.FigureEight
public import Topology_Munkres_2000.Book.Definition_81_1.CoveringTransformation
public import Topology_Munkres_2000.Book.Definition_81_4.Regular
public import Topology_Munkres_2000.Book.Theorem_53_1.CircleMap
public import Mathlib.Topology.Constructions

public section

open Function Set

/-- The two edge labels of the figure-eight graph. -/
inductive TwoCircleLabel
  | A
  | B
  deriving DecidableEq

/-- The discrete topology on the finite set of edge labels. -/
instance TwoCircleLabel.instTopologicalSpace : TopologicalSpace TwoCircleLabel := ⊥

namespace TwoCirclePermutationCover

/-- The closed unit interval used to realize each directed edge. -/
abbrev UnitInterval := Set.Icc (0 : ℝ) 1

/-- Zero belongs to the closed unit interval. -/
theorem zero_mem_unitInterval : (0 : ℝ) ∈ UnitInterval := sorry

/-- One belongs to the closed unit interval. -/
theorem one_mem_unitInterval : (1 : ℝ) ∈ UnitInterval := sorry

/-- The disjoint union of directed `A`- and `B`-edges before their endpoints are glued. -/
abbrev Raw (Vertex : Type) := TwoCircleLabel × Vertex × UnitInterval

/-- The initial endpoint of a directed edge. -/
def start {Vertex : Type} (label : TwoCircleLabel) (vertex : Vertex) : Raw Vertex :=
  (label, vertex, ⟨0, zero_mem_unitInterval⟩)

/-- The terminal endpoint of a directed edge. -/
def finish {Vertex : Type} (label : TwoCircleLabel) (vertex : Vertex) : Raw Vertex :=
  (label, vertex, ⟨1, one_mem_unitInterval⟩)

/-- The generating endpoint identifications determined by two sheet permutations. -/
inductive Gluing {Vertex : Type} (aNext bNext : Vertex ≃ Vertex) :
    Raw Vertex → Raw Vertex → Prop
  | vertex (v : Vertex) : Gluing aNext bNext (start .A v) (start .B v)
  | aEdge (v : Vertex) : Gluing aNext bNext (finish .A v) (start .A (aNext v))
  | bEdge (v : Vertex) : Gluing aNext bNext (finish .B v) (start .B (bNext v))

/-- The topological graph obtained by gluing the directed edges according to two permutations. -/
abbrev Total {Vertex : Type} (aNext bNext : Vertex ≃ Vertex) :=
  Quot (Gluing aNext bNext)

/-- The quotient topology on a permutation-cover total space. -/
instance instTopologicalSpaceTotal {Vertex : Type} [TopologicalSpace Vertex]
    (aNext bNext : Vertex ≃ Vertex) :
    TopologicalSpace (Total aNext bNext) := inferInstance

/-- Points on the circle `A` of the figure eight. -/
theorem circleA_mem (z : Circle) : (z, 1) ∈ FigureEight.carrier := sorry

/-- Points on the circle `A` of the figure eight. -/
noncomputable def circleA (z : Circle) : FigureEight :=
  ⟨(z, 1), circleA_mem z⟩

/-- Points on the circle `B` of the figure eight. -/
theorem circleB_mem (z : Circle) : (1, z) ∈ FigureEight.carrier := sorry

/-- Points on the circle `B` of the figure eight. -/
noncomputable def circleB (z : Circle) : FigureEight :=
  ⟨(1, z), circleB_mem z⟩

/-- The projection before passing to the endpoint quotient. -/
noncomputable def rawProjection {Vertex : Type} : Raw Vertex → FigureEight
  | (.A, _, t) => circleA (Circle.turnExp t)
  | (.B, _, t) => circleB (Circle.turnExp t)

/-- The raw projection respects every generating endpoint identification. -/
theorem rawProjection_respects {Vertex : Type} {aNext bNext : Vertex ≃ Vertex}
    {x y : Raw Vertex} (hxy : Gluing aNext bNext x y) :
    rawProjection x = rawProjection y := sorry

/-- The projection of a permutation cover onto the figure eight. -/
noncomputable def proj {Vertex : Type} (aNext bNext : Vertex ≃ Vertex) :
    Total aNext bNext → FigureEight :=
  Quot.lift rawProjection fun _ _ hxy ↦ rawProjection_respects hxy

/-- An `A`-edge projects to the circle `A` with its interval coordinate. -/
theorem proj_A {Vertex : Type} (aNext bNext : Vertex ≃ Vertex)
    (vertex : Vertex) (t : UnitInterval) :
    proj aNext bNext (Quot.mk _ (.A, vertex, t)) = circleA (Circle.turnExp t) := sorry

/-- A `B`-edge projects to the circle `B` with its interval coordinate. -/
theorem proj_B {Vertex : Type} (aNext bNext : Vertex ≃ Vertex)
    (vertex : Vertex) (t : UnitInterval) :
    proj aNext bNext (Quot.mk _ (.B, vertex, t)) = circleB (Circle.turnExp t) := sorry

/-- The permutation-cover projection is a covering map. -/
theorem proj_isCoveringMap {Vertex : Type} [TopologicalSpace Vertex] [DiscreteTopology Vertex]
    (aNext bNext : Vertex ≃ Vertex) :
    IsCoveringMap (proj aNext bNext) := sorry

/-- Every permutation-cover projection is onto the figure eight. -/
theorem proj_surjective {Vertex : Type} [TopologicalSpace Vertex] [Nonempty Vertex]
    (aNext bNext : Vertex ≃ Vertex) :
    Surjective (proj aNext bNext) := sorry

/-- The connected covering bundled from a path-connected permutation cover. -/
noncomputable def covering {Vertex : Type} [TopologicalSpace Vertex] [DiscreteTopology Vertex]
    [Nonempty Vertex]
    (aNext bNext : Vertex ≃ Vertex) [PathConnectedSpace (Total aNext bNext)]
    [LocallyPathConnectedSpace (Total aNext bNext)] : ConnectedCovering FigureEight where
  Total := TopCat.of (Total aNext bNext)
  proj := proj aNext bNext
  isCoveringMap := proj_isCoveringMap aNext bNext
  surjective := proj_surjective aNext bNext
  pathConnected := inferInstance
  locallyPathConnected := inferInstance

end TwoCirclePermutationCover

namespace Figure814Cover

/-- The sheet permutation induced by the arc labeled `A` in Figure 81.4. -/
def aNext : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

/-- The sheet permutation induced by the two loops labeled `B` in Figure 81.4. -/
def bNext : Fin 2 ≃ Fin 2 := Equiv.refl _

/-- The total graph of the covering in Figure 81.4. -/
abbrev Total := TwoCirclePermutationCover.Total aNext bNext

/-- The total graph of Figure 81.4 is path connected. -/
instance instPathConnectedSpace : PathConnectedSpace Total := sorry

/-- The total graph of Figure 81.4 is locally path connected. -/
instance instLocallyPathConnectedSpace : LocallyPathConnectedSpace Total := sorry

/-- The connected covering pictured in Figure 81.4. -/
noncomputable def covering : ConnectedCovering FigureEight :=
  TwoCirclePermutationCover.covering aNext bNext

end Figure814Cover

namespace Figure815Cover

/-- The sheet permutation induced by the arcs labeled `A` in Figure 81.5. -/
def aNext : Fin 3 ≃ Fin 3 := Equiv.swap 0 1

/-- The sheet permutation induced by the arcs labeled `B` in Figure 81.5. -/
def bNext : Fin 3 ≃ Fin 3 := Equiv.swap 1 2

/-- The total graph of the covering in Figure 81.5. -/
abbrev Total := TwoCirclePermutationCover.Total aNext bNext

/-- The total graph of Figure 81.5 is path connected. -/
instance instPathConnectedSpace : PathConnectedSpace Total := sorry

/-- The total graph of Figure 81.5 is locally path connected. -/
instance instLocallyPathConnectedSpace : LocallyPathConnectedSpace Total := sorry

/-- The connected covering pictured in Figure 81.5. -/
noncomputable def covering : ConnectedCovering FigureEight :=
  TwoCirclePermutationCover.covering aNext bNext

end Figure815Cover

namespace Figure816Cover

/-- The sheet permutation induced by the arcs labeled `A` in Figure 81.6. -/
def aNext : Fin 4 ≃ Fin 4 := (Equiv.swap 0 1).trans (Equiv.swap 2 3)

/-- The sheet permutation induced by the arcs labeled `B` in Figure 81.6. -/
def bNext : Fin 4 ≃ Fin 4 := Equiv.swap 1 2

/-- The total graph of the covering in Figure 81.6. -/
abbrev Total := TwoCirclePermutationCover.Total aNext bNext

/-- The total graph of Figure 81.6 is path connected. -/
instance instPathConnectedSpace : PathConnectedSpace Total := sorry

/-- The total graph of Figure 81.6 is locally path connected. -/
instance instLocallyPathConnectedSpace : LocallyPathConnectedSpace Total := sorry

/-- The connected covering pictured in Figure 81.6. -/
noncomputable def covering : ConnectedCovering FigureEight :=
  TwoCirclePermutationCover.covering aNext bNext

/-- Reflection of the four sheet vertices in Figure 81.6. -/
def vertexReflection : Fin 4 ≃ Fin 4 := (Equiv.swap 0 3).trans (Equiv.swap 1 2)

/-- Reflection of represented edge points before passing to the quotient. -/
def rawReflection : TwoCirclePermutationCover.Raw (Fin 4) →
    TwoCirclePermutationCover.Raw (Fin 4)
  | (label, vertex, t) => (label, vertexReflection vertex, t)

/-- Raw reflection respects the endpoint identifications of Figure 81.6. -/
theorem rawReflection_respects {x y : TwoCirclePermutationCover.Raw (Fin 4)}
    (hxy : TwoCirclePermutationCover.Gluing aNext bNext x y) :
    TwoCirclePermutationCover.Gluing aNext bNext (rawReflection x) (rawReflection y) := sorry

/-- Reflection twice is the identity on the Figure 81.6 total space. -/
theorem quotReflection_involutive :
    Function.Involutive
      (Quot.map rawReflection fun _ _ hxy ↦ rawReflection_respects hxy) := sorry

/-- Reflection is continuous on the Figure 81.6 total space. -/
theorem continuous_quotReflection :
    Continuous (Quot.map rawReflection fun _ _ hxy ↦ rawReflection_respects hxy) := sorry

/-- The reflection covering transformation of Figure 81.6. -/
def reflection : covering.Total ≃ₜ covering.Total where
  toFun := Quot.map rawReflection fun _ _ hxy ↦ rawReflection_respects hxy
  invFun := Quot.map rawReflection fun _ _ hxy ↦ rawReflection_respects hxy
  left_inv := quotReflection_involutive
  right_inv := quotReflection_involutive
  continuous_toFun := continuous_quotReflection
  continuous_invFun := continuous_quotReflection

/-- Reflection commutes with the Figure 81.6 projection. -/
theorem reflection_mem_group :
    reflection ∈ CoveringTransformation.group covering.proj := sorry

/-- The reflection of Figure 81.6 is not the identity homeomorphism. -/
theorem reflection_ne_one : reflection ≠ 1 := sorry

/-- The reflection of Figure 81.6 has order two. -/
theorem reflection_sq : reflection * reflection = 1 := sorry

end Figure816Cover

namespace Figure817Cover

/-- The sheet permutation induced by the horizontal arcs labeled `A` in Figure 81.7. -/
def aNext : ℤ ≃ ℤ := Equiv.addRight 1

/-- The sheet permutation induced by the loops labeled `B` in Figure 81.7. -/
def bNext : ℤ ≃ ℤ := Equiv.refl _

/-- The total graph of the covering in Figure 81.7. -/
abbrev Total := TwoCirclePermutationCover.Total aNext bNext

/-- The total graph of Figure 81.7 is path connected. -/
instance instPathConnectedSpace : PathConnectedSpace Total := sorry

/-- The total graph of Figure 81.7 is locally path connected. -/
instance instLocallyPathConnectedSpace : LocallyPathConnectedSpace Total := sorry

/-- The connected covering pictured in Figure 81.7. -/
noncomputable def covering : ConnectedCovering FigureEight :=
  TwoCirclePermutationCover.covering aNext bNext

/-- Translation of the sheet coordinate before passing to the quotient. -/
def rawTranslation (k : ℤ) : TwoCirclePermutationCover.Raw ℤ →
    TwoCirclePermutationCover.Raw ℤ
  | (label, vertex, t) => (label, vertex + k, t)

/-- Raw translations respect the endpoint identifications of Figure 81.7. -/
theorem rawTranslation_respects (k : ℤ) {x y : TwoCirclePermutationCover.Raw ℤ}
    (hxy : TwoCirclePermutationCover.Gluing aNext bNext x y) :
    TwoCirclePermutationCover.Gluing aNext bNext (rawTranslation k x) (rawTranslation k y) := sorry

/-- Translation followed by its negative is the identity on the Figure 81.7 total space. -/
theorem rawTranslation_leftInverse (k : ℤ) :
    LeftInverse
      (Quot.map (rawTranslation (-k)) fun _ _ hxy ↦ rawTranslation_respects (-k) hxy)
      (Quot.map (rawTranslation k) fun _ _ hxy ↦ rawTranslation_respects k hxy) := sorry

/-- Translation by the negative followed by translation is the identity. -/
theorem rawTranslation_rightInverse (k : ℤ) :
    RightInverse
      (Quot.map (rawTranslation (-k)) fun _ _ hxy ↦ rawTranslation_respects (-k) hxy)
      (Quot.map (rawTranslation k) fun _ _ hxy ↦ rawTranslation_respects k hxy) := sorry

/-- Integer translation is continuous on the Figure 81.7 total space. -/
theorem continuous_quotTranslation (k : ℤ) :
    Continuous (Quot.map (rawTranslation k) fun _ _ hxy ↦ rawTranslation_respects k hxy) := sorry

/-- Translation by an integer is a self-homeomorphism of the Figure 81.7 total space. -/
def translation (k : ℤ) : covering.Total ≃ₜ covering.Total where
  toFun := Quot.map (rawTranslation k) fun _ _ hxy ↦ rawTranslation_respects k hxy
  invFun := Quot.map (rawTranslation (-k)) fun _ _ hxy ↦ rawTranslation_respects (-k) hxy
  left_inv := rawTranslation_leftInverse k
  right_inv := rawTranslation_rightInverse k
  continuous_toFun := continuous_quotTranslation k
  continuous_invFun := continuous_quotTranslation (-k)

/-- Integer translations commute with the Figure 81.7 projection. -/
theorem translation_mem_group (k : ℤ) :
    translation k ∈ CoveringTransformation.group covering.proj := sorry

/-- Integer translation as an element of the covering-transformation group. -/
def deckTranslation (k : ℤ) : CoveringTransformation.group covering.proj :=
  ⟨translation k, translation_mem_group k⟩

/-- Translation by zero is the identity covering transformation. -/
theorem deckTranslation_zero : deckTranslation 0 = 1 := sorry

/-- Translation converts integer addition into composition of covering transformations. -/
theorem deckTranslation_add (k l : ℤ) :
    deckTranslation (k + l) = deckTranslation k * deckTranslation l := sorry

/-- Integer translations define a homomorphism into the covering-transformation group. -/
def translationHom : Multiplicative ℤ →* CoveringTransformation.group covering.proj where
  toFun k := deckTranslation k.toAdd
  map_one' := deckTranslation_zero
  map_mul' k l := deckTranslation_add k.toAdd l.toAdd

/-- Every covering transformation of Figure 81.7 is a unique integer translation. -/
theorem translationHom_bijective : Bijective translationHom := sorry

end Figure817Cover

/-- Exercise 81.2 (1): The covering pictured in Figure 81.4 is regular. -/
instance figure814Regular : Figure814Cover.covering.IsRegular := sorry

/-- Exercise 81.2 (2): The covering-transformation group of Figure 81.5 is trivial. -/
theorem figure815TransformationGroup :
    CoveringTransformation.group Figure815Cover.covering.proj = ⊥ := sorry

/-- Exercise 81.2 (3): The covering pictured in Figure 81.5 is not regular. -/
theorem figure815NotRegular : ¬ Figure815Cover.covering.IsRegular := sorry

/-- Exercise 81.2 (4): The covering-transformation group of Figure 81.6 is generated
by the reflection reversing its chain of four vertices. -/
theorem figure816TransformationGroup :
    CoveringTransformation.group Figure816Cover.covering.proj =
      Subgroup.closure {Figure816Cover.reflection} := sorry

/-- Exercise 81.2 (5): The covering pictured in Figure 81.6 is not regular. -/
theorem figure816NotRegular : ¬ Figure816Cover.covering.IsRegular := sorry

/-- Exercise 81.2 (6): Integer translations bijectively parametrize the
covering-transformation group of Figure 81.7. -/
theorem figure817TransformationGroup : Bijective Figure817Cover.translationHom := sorry

/-- Exercise 81.2 (7): The covering pictured in Figure 81.7 is regular. -/
instance figure817Regular : Figure817Cover.covering.IsRegular := sorry
