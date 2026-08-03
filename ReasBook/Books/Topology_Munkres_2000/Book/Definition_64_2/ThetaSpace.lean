module

public import Mathlib.Topology.UnitInterval

public section

open Set

universe u v

namespace Topology

/-- An explicit presentation of a theta space by three arcs with common endpoints. -/
structure ThetaPresentation (X : Type u) [TopologicalSpace X] where
  /-- The common initial endpoint of the three arcs. -/
  initial : X
  /-- The common terminal endpoint of the three arcs. -/
  terminal : X
  /-- The three parameterized arcs. -/
  arc : Fin 3 → C(unitInterval, X)
  /-- Each parameterized arc is an embedding. -/
  isEmbedding (i : Fin 3) : IsEmbedding (arc i)
  /-- Every arc maps the initial endpoint of `unitInterval` to `initial`. -/
  map_zero (i : Fin 3) : arc i 0 = initial
  /-- Every arc maps the terminal endpoint of `unitInterval` to `terminal`. -/
  map_one (i : Fin 3) : arc i 1 = terminal
  /-- The three arcs cover the space. -/
  iUnion_range : ⋃ i, Set.range (arc i) = Set.univ
  /-- Two distinct arcs intersect exactly in their common endpoints. -/
  range_inter_range (i j : Fin 3) (hij : i ≠ j) :
    Set.range (arc i) ∩ Set.range (arc j) = {initial, terminal}

namespace ThetaPresentation

variable {X : Type u} [TopologicalSpace X]

/-- Construct a theta presentation from three parameterized arcs with common endpoints. -/
def ofArcs (initial terminal : X) (arc : Fin 3 → C(unitInterval, X))
    (isEmbedding : ∀ i, IsEmbedding (arc i))
    (map_zero : ∀ i, arc i 0 = initial) (map_one : ∀ i, arc i 1 = terminal)
    (iUnion_range : ⋃ i, Set.range (arc i) = Set.univ)
    (range_inter_range : ∀ i j, i ≠ j →
      Set.range (arc i) ∩ Set.range (arc j) = {initial, terminal}) :
    ThetaPresentation X where
  initial := initial
  terminal := terminal
  arc := arc
  isEmbedding := isEmbedding
  map_zero := map_zero
  map_one := map_one
  iUnion_range := iUnion_range
  range_inter_range := range_inter_range

/-- The `i`th arc of a theta presentation, viewed as a subset of the ambient space. -/
def edge (P : ThetaPresentation X) (i : Fin 3) : Set X :=
  Set.range (P.arc i)

/-- The intrinsic edge is the range of its parameterized arc. -/
theorem edge_eq_range (P : ThetaPresentation X) (i : Fin 3) :
    P.edge i = Set.range (P.arc i) := by
  -- This is the public computation rule for the opaque edge definition.
  rfl

/-- The common endpoints of a theta presentation are distinct. -/
theorem endpoint_ne (P : ThetaPresentation X) : P.initial ≠ P.terminal := by
  intro h
  have h01 : (0 : unitInterval) ≠ 1 := by
    intro h'
    have := congrArg Subtype.val h'
    norm_num at this
  apply h01
  apply (P.isEmbedding 0).injective
  rw [P.map_zero, P.map_one, h]

/-- The three edges of a theta presentation cover the ambient space. -/
theorem iUnion_edge (P : ThetaPresentation X) : ⋃ i, P.edge i = Set.univ := P.iUnion_range

/-- Distinct edges of a theta presentation intersect exactly in the common endpoints. -/
theorem edge_inter_edge (P : ThetaPresentation X) (i j : Fin 3) (hij : i ≠ j) :
    P.edge i ∩ P.edge j = {P.initial, P.terminal} := P.range_inter_range i j hij

/-- Helper for Definition 64.2: postcomposing the three arcs with a homeomorphism still covers
the codomain. -/
lemma iUnion_range_comp_homeomorph {Y : Type v} [TopologicalSpace Y]
    (P : ThetaPresentation X) (e : X ≃ₜ Y) :
    ⋃ i, Set.range ((e : C(X, Y)).comp (P.arc i)) = Set.univ := by
  -- Rewrite the transported ranges as images, then transport the original covering equality.
  simp only [ContinuousMap.coe_comp, ContinuousMap.coe_coe, Set.range_comp]
  rw [← Set.image_iUnion, P.iUnion_range, Set.image_univ_of_surjective e.surjective]

/-- Helper for Definition 64.2: distinct arcs postcomposed with a homeomorphism meet precisely
at the transported endpoints. -/
lemma range_inter_range_comp_homeomorph {Y : Type v} [TopologicalSpace Y]
    (P : ThetaPresentation X) (e : X ≃ₜ Y) (i j : Fin 3) (hij : i ≠ j) :
    Set.range ((e : C(X, Y)).comp (P.arc i)) ∩
        Set.range ((e : C(X, Y)).comp (P.arc j)) =
      {e P.initial, e P.terminal} := by
  -- Injectivity lets image commute with intersection, exposing the original presentation field.
  simp only [ContinuousMap.coe_comp, ContinuousMap.coe_coe, Set.range_comp]
  rw [← Set.image_inter e.injective, P.range_inter_range i j hij, Set.image_pair]

/-- Helper for Definition 64.2: a theta presentation transports along a homeomorphism. -/
theorem nonempty_of_homeomorph {Y : Type v} [TopologicalSpace Y]
    (P : ThetaPresentation X) (e : X ≃ₜ Y) : Nonempty (ThetaPresentation Y) := by
  -- Assemble the transported presentation from postcomposed arcs and the two set interfaces.
  refine ⟨?_⟩
  apply ofArcs (e P.initial) (e P.terminal)
      (fun i ↦ (e : C(X, Y)).comp (P.arc i))
  · intro i
    exact e.isEmbedding.comp (P.isEmbedding i)
  · intro i
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_apply, P.map_zero]
  · intro i
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_apply, P.map_one]
  · exact P.iUnion_range_comp_homeomorph e
  · intro i j hij
    exact P.range_inter_range_comp_homeomorph e i j hij

end ThetaPresentation

/-- A Hausdorff space admitting a presentation by three arcs that meet pairwise only at their
common endpoints. -/
class IsThetaSpace (X : Type u) [TopologicalSpace X] : Prop extends T2Space X where
  /-- A presentation of the space by three arcs. -/
  presentation : Nonempty (ThetaPresentation X)

namespace IsThetaSpace

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Every theta space is Hausdorff. -/
instance instT2Space [h : IsThetaSpace X] : T2Space X := h.toT2Space

/-- A space is a theta space exactly when it is Hausdorff and has a theta presentation. -/
theorem iff_nonempty_presentation :
    IsThetaSpace X ↔ T2Space X ∧ Nonempty (ThetaPresentation X) := by
  constructor
  · intro h
    exact ⟨h.toT2Space, h.presentation⟩
  · rintro ⟨hT2, hP⟩
    exact { toT2Space := hT2, presentation := hP }

/-- A theta presentation of a Hausdorff space makes it a theta space. -/
theorem ofPresentation [T2Space X] (P : ThetaPresentation X) : IsThetaSpace X :=
  { toT2Space := inferInstance, presentation := ⟨P⟩ }

end IsThetaSpace

end Topology

end
