import Mathlib
import StacksProject_2024.Chap29.Definition_29_50_1
import StacksProject_2024.Chap29.Remark_29_49_13

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owners
`LocallyQuasiFinite`, `LocallyOfFiniteType`, and finite scheme fibers. Local Chapter 29
precedent supplies `genericPointsOfIrreducibleComponents` and
`Scheme.HasFiniteIrreducibleComponentsOnCompactOpens`. The Stacks tag evidence agrees on
`073A`. -/

/-- Remark 29.51.10 (1): in the ambient locally-finite-type setup, the target-local possible
definition of a generically finite morphism asks that every fiber over a generic point of an
irreducible component of the target be finite. The finite-components-on-quasi-compact-opens
hypothesis on the target is the intended setting for this requirement, although the displayed
condition itself is meaningful without it. -/
@[stacks 073A]
class GenericallyFiniteOnTarget {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  /-- Every generic point of an irreducible component of the target has finite inverse image. -/
  finiteGenericFiber :
    ∀ η : Y, η ∈ genericPointsOfIrreducibleComponents Y →
      ({x : X | f.base x = η} : Set X).Finite

/-- A morphism is target-locally generically finite exactly when all fibers over generic points of
irreducible components of the target are finite. -/
@[stacks 073A]
theorem genericallyFiniteOnTarget_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    f.GenericallyFiniteOnTarget ↔
      ∀ η : Y, η ∈ genericPointsOfIrreducibleComponents Y →
        ({x : X | f.base x = η} : Set X).Finite := sorry

/-- The finite-generic-fiber condition exposed by the target-local definition. -/
@[stacks 073A]
theorem GenericallyFiniteOnTarget.finiteGenericFiber.spec
    {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : f.GenericallyFiniteOnTarget) :
    ∀ η : Y, η ∈ genericPointsOfIrreducibleComponents Y →
      ({x : X | f.base x = η} : Set X).Finite := sorry

/-- For a target-locally generically finite morphism, the fiber over each generic point of an
irreducible component is finite as a subtype. -/
@[stacks 073A, instance]
instance instFiniteGenericFiberSubtypeOfGenericallyFiniteOnTarget
    {X Y : Scheme.{u}} (f : X ⟶ Y) [f.GenericallyFiniteOnTarget]
    (η : Y) [Fact (η ∈ genericPointsOfIrreducibleComponents Y)] :
    Finite {x : X // f.base x = η} := sorry

/-- Remark 29.51.10 (2): in the ambient locally-finite-type setup, the source-local possible
definition of a generically finite morphism asks for a dense open subscheme of the source on which
the induced morphism to the target is locally quasi-finite. -/
@[stacks 073A]
class GenericallyFiniteOnSource {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  /-- There is a dense open subset of the source whose induced map to the target is locally
  quasi-finite. -/
  existsDenseOpenLocallyQuasiFinite :
    ∃ U : X.Opens, Dense (U : Set X) ∧ LocallyQuasiFinite (U.ι ≫ f)

/-- A morphism is source-locally generically finite exactly when some dense open of the source
maps locally quasi-finitely to the target. -/
@[stacks 073A]
theorem genericallyFiniteOnSource_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    f.GenericallyFiniteOnSource ↔
      ∃ U : X.Opens, Dense (U : Set X) ∧ LocallyQuasiFinite (U.ι ≫ f) := sorry

/-- The dense-open locally-quasi-finite condition exposed by the source-local definition. -/
@[stacks 073A]
theorem GenericallyFiniteOnSource.existsDenseOpenLocallyQuasiFinite.spec
    {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : f.GenericallyFiniteOnSource) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ LocallyQuasiFinite (U.ι ≫ f) := sorry

/-- The source-local definition gives the target-local definition under the hypotheses of
Remark 29.51.10, registered as a typeclass bridge. -/
@[stacks 073A, instance]
instance instGenericallyFiniteOnTargetOfGenericallyFiniteOnSource
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y] [f.GenericallyFiniteOnSource] :
    f.GenericallyFiniteOnTarget := sorry

/-- A locally quasi-finite morphism is source-locally generically finite, using the whole source
as the dense open. -/
@[stacks 073A, instance]
instance instGenericallyFiniteOnSourceOfLocallyQuasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] :
    f.GenericallyFiniteOnSource := sorry

/-- Remark 29.51.10 (3): for a quasi-compact locally finite type morphism whose target has
finitely many irreducible components on quasi-compact opens, the source-local dense-open
locally-quasi-finite requirement implies that all fibers over generic points of irreducible
components of the target are finite. -/
@[stacks 073A]
theorem genericallyFiniteOnTarget_of_genericallyFiniteOnSource
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y]
    (hf : f.GenericallyFiniteOnSource) :
    f.GenericallyFiniteOnTarget := sorry

end Scheme.Hom
end AlgebraicGeometry
