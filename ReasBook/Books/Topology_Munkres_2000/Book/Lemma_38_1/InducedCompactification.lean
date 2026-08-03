module

public import Topology_Munkres_2000.Book.Definition_29_2.Compactification
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.DenseEmbedding

open Set

@[expose] public section

universe u v

/-- The compactification induced by a map `h : X → Z`, realized as the closure of its range. -/
def InducedCompactification {X : Type u} {Z : Type v} [TopologicalSpace Z] (h : X → Z) :=
  closure (Set.range h)

namespace InducedCompactification

variable {X : Type u} {Z : Type v} [TopologicalSpace Z]

/-- The canonical map from `X` into the compactification induced by `h`. -/
def ofMap (h : X → Z) : X → InducedCompactification h :=
  fun x ↦ ⟨h x, subset_closure (Set.mem_range_self x)⟩

/-- The canonical inclusion of the compactification induced by `h` into `Z`. -/
def inclusion (h : X → Z) : InducedCompactification h → Z :=
  Subtype.val

/-- The closure of the range of a map into a compact space is compact. -/
instance instCompactSpace [CompactSpace Z] (h : X → Z) :
    CompactSpace (InducedCompactification h) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact

/-- An embedding has dense image in its induced compactification. -/
theorem isDenseEmbedding_ofMap [TopologicalSpace X] {h : X → Z}
    (hh : Topology.IsEmbedding h) :
    IsDenseEmbedding (ofMap h) := by
  -- Restrict the original embedding to the closure of its range.
  have hembedding : Topology.IsEmbedding (ofMap h) :=
    hh.codRestrict (closure (Set.range h)) fun x ↦
      subset_closure (Set.mem_range_self x)
  refine { toIsInducing := hembedding.toIsInducing, injective := hembedding.injective, dense := ?_ }
  -- The restricted range is dense because its ambient closure is the defining subtype.
  unfold DenseRange
  rw [dense_iff_closure_eq]
  ext y
  simp only [Set.mem_univ, iff_true]
  rw [closure_subtype]
  have hrange : Subtype.val '' Set.range (ofMap h) = Set.range h := by
    ext z
    simp only [Set.mem_image, Set.mem_range, ofMap]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨ofMap h x, ⟨x, rfl⟩, rfl⟩
  rw [hrange]
  exact y.property

/-- Package the closure-of-range construction as a compactification of `X`. -/
def compactification [TopologicalSpace X] [CompactSpace Z] [T2Space Z]
    (h : X → Z) (hh : Topology.IsEmbedding h) : Compactification X :=
  Compactification.of (InducedCompactification h) (ofMap h) (isDenseEmbedding_ofMap hh)

/-- The map stored by the induced compactification is its canonical map from `X`. -/
theorem compactification_apply [TopologicalSpace X] [CompactSpace Z] [T2Space Z]
    (h : X → Z) (hh : Topology.IsEmbedding h) (x : X) :
    compactification h hh x = ofMap h x := by
  -- The `Compactification.of` constructor stores the supplied dense embedding unchanged.
  exact Compactification.of_apply _ _ _ x

/-- The canonical inclusion of an induced compactification is an embedding. -/
theorem isEmbedding_inclusion (h : X → Z) : Topology.IsEmbedding (inclusion h) := by
  -- This is the standard embedding of a subtype into its ambient space.
  exact Topology.IsEmbedding.subtypeVal

/-- The canonical inclusion extends the original map. -/
@[simp]
theorem inclusion_ofMap (h : X → Z) (x : X) : inclusion h (ofMap h x) = h x := by
  -- Both maps compute to the ambient value `h x`.
  rfl

/-- The ambient inclusion of the induced compactification extends the original embedding. -/
@[simp]
theorem inclusion_compactification [TopologicalSpace X] [CompactSpace Z] [T2Space Z]
    (h : X → Z) (hh : Topology.IsEmbedding h) (x : X) :
    inclusion h (compactification h hh x) = h x := by
  -- Reduce the packaged map to `ofMap`, then use the inclusion computation rule.
  rw [compactification_apply]
  exact inclusion_ofMap h x


end InducedCompactification

end
