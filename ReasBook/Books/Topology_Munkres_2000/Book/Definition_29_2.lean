module

public import Mathlib.Topology.Category.CompHaus.Basic
public import Mathlib.Topology.DenseEmbedding

@[expose] public section

universe u v

/-- A compactification of `X`, given by a compact Hausdorff target and a dense embedding into it. -/
structure Compactification (X : Type u) [TopologicalSpace X] where
  toCompHaus : CompHaus.{v}
  toFun : X → toCompHaus
  isDenseEmbedding : IsDenseEmbedding toFun

namespace Compactification

variable {X : Type u} [TopologicalSpace X]

/-- A compactification coerces to its compact Hausdorff target. -/
instance instCoeSort : CoeSort (Compactification.{u, v} X) (Type v) where
  coe C := C.toCompHaus

/-- A compactification acts on `X` by its stored dense embedding. -/
instance instCoeFun : CoeFun (Compactification.{u, v} X) (fun C ↦ X → C) where
  coe C := C.toFun

/-- Construct a compactification from a compact Hausdorff space and a dense embedding into it. -/
def of (Y : Type v) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (i : X → Y) (hi : IsDenseEmbedding i) : Compactification X where
  toCompHaus := CompHaus.of Y
  toFun := i
  isDenseEmbedding := hi

/-- The compact Hausdorff target stored by `of Y i hi` is `CompHaus.of Y`. -/
theorem of_toCompHaus (Y : Type v) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (i : X → Y) (hi : IsDenseEmbedding i) :
    (of Y i hi).toCompHaus = CompHaus.of Y := by
  -- Unfolding the constructor exposes its compact Hausdorff target field.
  rfl

/-- The embedding stored by `of Y i hi` is the original map `i`. -/
theorem of_apply (Y : Type v) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (i : X → Y) (hi : IsDenseEmbedding i) (x : X) :
    of Y i hi x = i x := by
  -- The function coercion selects the map stored by the constructor.
  rfl

/-- The constructor `of` retains the supplied dense-embedding property. -/
theorem of_isDenseEmbedding (Y : Type v) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (i : X → Y) (hi : IsDenseEmbedding i) :
    IsDenseEmbedding (of Y i hi) := by
  -- After coercion normalization, the goal is precisely the supplied hypothesis.
  exact hi

/-- A compactification is proper when its embedded copy of the original space is not the
whole target. -/
def IsProper (C : Compactification.{u, v} X) : Prop :=
  Set.range C ≠ Set.univ

/-- Properness of a compactification is equivalent to nonsurjectivity of its embedding. -/
theorem isProper_iff (C : Compactification.{u, v} X) :
    C.IsProper ↔ ¬Function.Surjective C := by
  -- A range is the whole target exactly when its defining function is surjective.
  unfold IsProper
  constructor
  · intro hproper hsurjective
    exact hproper (Set.range_eq_univ.mpr hsurjective)
  · intro hnonsurjective hrange
    exact hnonsurjective (Set.range_eq_univ.mp hrange)

end Compactification

/- Definition 29.2 (1): A compactification has a compact Hausdorff target in which the original
space is embedded as a proper dense subspace. -/
/-- Definition 29.2: A compactification whose embedded image is a proper dense subspace of its
compact Hausdorff target. -/
abbrev ProperCompactification (X : Type u) [TopologicalSpace X] :=
  { C : Compactification.{u, v} X // C.IsProper }

namespace Compactification

variable {X : Type u} [TopologicalSpace X]

/- Definition 29.2 (2): A one-point compactification has a singleton complement to its embedded
image. -/
/-- Definition 29.2 (2): A compactification is one-point when the complement of its embedded
image is a singleton. -/
def IsOnePoint (C : Compactification.{u, v} X) : Prop :=
  ∃ y : C, (Set.range C)ᶜ = {y}

/-- A compactification is one-point exactly when its range is the complement of one point. -/
theorem isOnePoint_iff (C : Compactification.{u, v} X) :
    C.IsOnePoint ↔ ∃ y : C, Set.range C = {y}ᶜ := by
  -- Both orientations say that the range and the singleton are complementary sets.
  constructor
  · rintro ⟨y, hy⟩
    use y
    exact eq_compl_iff_isCompl.mpr (compl_eq_iff_isCompl.mp hy)
  · rintro ⟨y, hy⟩
    use y
    exact compl_eq_iff_isCompl.mpr (eq_compl_iff_isCompl.mp hy)

/-- Every one-point compactification is proper. -/
theorem IsOnePoint.isProper {C : Compactification.{u, v} X} :
    C.IsOnePoint → C.IsProper := by
  intro h
  -- The singleton complement supplies a point omitted by the embedding.
  obtain ⟨y, hy⟩ := h
  rw [isProper_iff]
  intro hsurjective
  obtain ⟨x, hx⟩ := hsurjective y
  have hy_mem : y ∈ (Set.range C)ᶜ := by
    rw [hy]
    exact Set.mem_singleton y
  have hy_not_mem : y ∉ Set.range C :=
    (Set.mem_compl_iff (Set.range C) y).mp hy_mem
  -- Surjectivity places the omitted point back in the range, a contradiction.
  exact hy_not_mem ⟨x, hx⟩

end Compactification


end
