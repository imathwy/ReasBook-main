import StacksProject_2024.Chap05.Definition_5_10_5
import StacksProject_2024.Chap29.Definition_29_28_4

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace

namespace AlgebraicGeometry
namespace Scheme.Hom

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the nearby canonical owner
  `AlgebraicGeometry.IsSmoothOfRelativeDimension`, but there is no existing generic mathlib owner
  for arbitrary morphisms whose fibres all have a fixed relative dimension;
- local project precedent already exposes the pointwise fibre-dimension invariant as
  `Scheme.Hom.fiberDimensionAt` in `Chap29/Definition_29_28_4.lean`;
- the fibrewise equidimensionality clause is therefore stated directly with the existing topological
  owner `TopologicalSpace.EquidimensionalSpace` from `Chap05/Definition_5_10_5.lean`.
-/

universe u

variable {X S : Scheme.{u}}

/-- Definition 29.29.1 (1): a morphism `f : X ⟶ S` is of relative dimension at most `d` at
`x : X` if the fibre dimension of `f` at `x` is at most `d`. -/
def RelativeDimensionLEAt (f : X ⟶ S) (d : ℕ) (x : X) : Prop :=
  f.fiberDimensionAt x ≤ (d : WithBot ℕ∞)

/-- The pointwise relative-dimension-at-most predicate is exactly the canonical fibre-dimension
inequality. -/
theorem relativeDimensionLEAt_iff (f : X ⟶ S) (d : ℕ) (x : X) :
    RelativeDimensionLEAt f d x ↔ f.fiberDimensionAt x ≤ (d : WithBot ℕ∞) := by
  rfl

/-- Definition 29.29.1 (1) in pointwise form. -/
theorem relativeDimensionLEAt_def (f : X ⟶ S) (d : ℕ) (x : X) :
    RelativeDimensionLEAt f d x = (f.fiberDimensionAt x ≤ (d : WithBot ℕ∞)) :=
  rfl

/- The locally-finite-type hypothesis enters only at the global owner `RelativeDimensionLE`. -/

/-- Definition 29.29.1 (2): a locally finite type morphism `f : X ⟶ S` is of relative dimension
at most `d` if the fibre dimension at every point of `X` is at most `d`. -/
class RelativeDimensionLE (f : X ⟶ S) (d : ℕ) : Prop extends LocallyOfFiniteType f where
  relativeDimensionLEAt (x : X) : RelativeDimensionLEAt f d x

/-- A locally finite type morphism has relative dimension at most `d` exactly when every point of
the source has fiber dimension at most `d`. -/
theorem relativeDimensionLE_iff (f : X ⟶ S) (d : ℕ) :
    RelativeDimensionLE f d ↔
      LocallyOfFiniteType f ∧ ∀ x : X, RelativeDimensionLEAt f d x := by
  constructor
  · intro h
    exact ⟨inferInstance, h.relativeDimensionLEAt⟩
  · rintro ⟨hft, hdim⟩
    exact
      { toLocallyOfFiniteType := hft
        relativeDimensionLEAt := hdim }

/-- A locally finite type morphism has relative dimension at most `d` exactly when every point of
the source has fibre dimension at most `d`. -/
theorem relativeDimensionLE_iff_fiberDimensionAt_le (f : X ⟶ S) (d : ℕ) :
    RelativeDimensionLE f d ↔
      LocallyOfFiniteType f ∧ ∀ x : X, f.fiberDimensionAt x ≤ (d : WithBot ℕ∞) := by
  rw [relativeDimensionLE_iff]
  constructor
  · rintro ⟨hft, hdim⟩
    exact ⟨hft, fun x ↦ (relativeDimensionLEAt_iff f d x).1 (hdim x)⟩
  · rintro ⟨hft, hdim⟩
    exact ⟨hft, fun x ↦ (relativeDimensionLEAt_iff f d x).2 (hdim x)⟩

/-- A morphism of relative dimension at most `d` carries the source's locally finite type
hypothesis. -/
theorem locallyOfFiniteType_of_relativeDimensionLE (f : X ⟶ S) (d : ℕ)
    [RelativeDimensionLE f d] : LocallyOfFiniteType f :=
  inferInstance

/-- If `f` is of relative dimension at most `d`, then it is of relative dimension at most `d` at
every point of the source. -/
theorem relativeDimensionLEAt_of_relativeDimensionLE (f : X ⟶ S) (d : ℕ)
    [RelativeDimensionLE f d] (x : X) :
    RelativeDimensionLEAt f d x :=
  RelativeDimensionLE.relativeDimensionLEAt x

/-- If `f` is of relative dimension at most `d`, then the fibre dimension at every point is at
most `d`. -/
theorem fiberDimensionAt_le_of_relativeDimensionLE (f : X ⟶ S) (d : ℕ)
    [RelativeDimensionLE f d] (x : X) :
    f.fiberDimensionAt x ≤ (d : WithBot ℕ∞) :=
  (relativeDimensionLEAt_iff f d x).1 (relativeDimensionLEAt_of_relativeDimensionLE f d x)

/-- A relative-dimension-at-most bound places every point of the source in the corresponding
fibre-dimension locus. -/
theorem mem_fiberDimensionLELocus_of_relativeDimensionLE (f : X ⟶ S) (d : ℕ)
    [RelativeDimensionLE f d] (x : X) :
    x ∈ f.fiberDimensionLELocus d :=
  (mem_fiberDimensionLELocus f d x).2 (fiberDimensionAt_le_of_relativeDimensionLE f d x)

/-- Definition 29.29.1 (3): a locally finite type morphism `f : X ⟶ S` is of relative dimension
`d` if every nonempty fibre `X_s` is equidimensional of topological Krull dimension `d`. -/
class RelativeDimension (f : X ⟶ S) (d : ℕ) : Prop extends LocallyOfFiniteType f where
  equidimensionalSpace_fiber (s : S) (_ : Nonempty (f.fiber s)) :
    EquidimensionalSpace (f.fiber s)
  topologicalKrullDim_fiber (s : S) (_ : Nonempty (f.fiber s)) :
    topologicalKrullDim (f.fiber s) = d

/-- A locally finite type morphism has relative dimension `d` exactly when every nonempty fiber is
equidimensional of topological Krull dimension `d`. -/
theorem relativeDimension_iff (f : X ⟶ S) (d : ℕ) :
    RelativeDimension f d ↔
      LocallyOfFiniteType f ∧
        (∀ (s : S) (_ : Nonempty (f.fiber s)), EquidimensionalSpace (f.fiber s)) ∧
        ∀ (s : S) (_ : Nonempty (f.fiber s)), topologicalKrullDim (f.fiber s) = d := by
  constructor
  · intro h
    exact
      ⟨h.toLocallyOfFiniteType, h.equidimensionalSpace_fiber,
        h.topologicalKrullDim_fiber⟩
  · rintro ⟨hft, hequidim, hdim⟩
    exact
      { toLocallyOfFiniteType := hft
        equidimensionalSpace_fiber := hequidim
        topologicalKrullDim_fiber := hdim }

/-- A morphism of relative dimension `d` carries the source's locally finite type hypothesis. -/
theorem locallyOfFiniteType_of_relativeDimension (f : X ⟶ S) (d : ℕ)
    [RelativeDimension f d] : LocallyOfFiniteType f :=
  inferInstance

/-- For a morphism of relative dimension `d`, every nonempty fibre is equidimensional. -/
theorem equidimensionalSpace_fiber_of_relativeDimension (f : X ⟶ S) (d : ℕ)
    [h : RelativeDimension f d] (s : S) (hs : Nonempty (f.fiber s)) :
    EquidimensionalSpace (f.fiber s) :=
  h.equidimensionalSpace_fiber s hs

/-- For a morphism of relative dimension `d`, every nonempty fibre has topological Krull
dimension `d`. -/
theorem topologicalKrullDim_fiber_eq_of_relativeDimension (f : X ⟶ S) (d : ℕ)
    [h : RelativeDimension f d] (s : S) (hs : Nonempty (f.fiber s)) :
    topologicalKrullDim (f.fiber s) = d :=
  h.topologicalKrullDim_fiber s hs

end Scheme.Hom
end AlgebraicGeometry
