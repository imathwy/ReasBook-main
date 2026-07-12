import Mathlib
import StacksProject_2024.Chap04.Definition_4_32_1
import StacksProject_2024.Chap04.Definition_4_33_5

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open BasedFunctor
open Functor IsHomLift IsStronglyCartesian
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {X Y : BasedCategory C}

/- Domain-style sampling for Lemma 4.33.8:
- primary domain: fibered categories over a fixed base, and invariance of strong cartesianness /
  fibredness under equivalence in `Cat/C`;
- sampled owner API:
  `BasedFunctor.IsEquivalenceOverBase`,
  `Functor.IsStronglyCartesian`,
  `Functor.IsFibered`,
  `Functor.isFibered_iff_exists_isStronglyCartesian`,
  `BasedCategory` and `BasedFunctor`;
- best owner abstractions: `BasedFunctor.IsEquivalenceOverBase` for equivalences in `Cat/C`,
  together with `Functor.IsStronglyCartesian` and `Functor.IsFibered` for the transported owner
  properties.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma that a based equivalence over `C` preserves fibredness;
- `core/canonical`: `BasedFunctor.IsEquivalenceOverBase`, `Functor.IsStronglyCartesian`, and
  `Functor.IsFibered`;
- `bridge/view`: the explicit `EquivalenceOverBase` data attached to an owner-level
  `IsEquivalenceOverBase` hypothesis, used to transport strongly cartesian lifts across the
  quasi-inverse and the vertical unit/counit isomorphisms.

Primitive-vs-derived split:
- primitive data: the based categories `X`, `Y`, the based functor `F : X ⥤ᵇ Y`, the owner
  predicate `F.IsEquivalenceOverBase`, and the upstream owner predicates on the projection
  functors `X.p` and `Y.p`;
- derived API: the transport theorem for strongly cartesian morphisms and the resulting
  equivalence-invariance statement for fibredness. -/

namespace BasedFunctor

/-- An equivalence over the base category sends strongly cartesian morphisms to strongly
cartesian morphisms. The base map is taken in the owner form from the source morphism `φ`. -/
theorem isStronglyCartesian_map_of_isEquivalenceOverBase
    (F : X ⥤ᵇ Y) (hF : F.IsEquivalenceOverBase)
    {x y : X.obj} (φ : x ⟶ y)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ) :
    Y.p.IsStronglyCartesian (Y.p.map (F.map φ)) (F.map φ) := by
  letI := hF
  sorry

/-- Lemma 4.33.8: if `F : X ⥤ᵇ Y` is an equivalence over `C`, then `X` is fibred over `C` if and
only if `Y` is fibred over `C`. -/
theorem isFibered_iff_of_equivalence_over_base
    (F : X ⥤ᵇ Y) (hF : F.IsEquivalenceOverBase) :
    X.p.IsFibered ↔ Y.p.IsFibered := by
  sorry

end BasedFunctor

end CategoryTheory
