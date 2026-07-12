import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v₁ v₂ u₁ u₂

/- Domain-style sampling for 21.3.0.2:
- primary domain: higher right derived functors in abelian categories with injective resolutions;
- sampled canonical/project declarations:
  `Functor.rightDerived`,
  `Functor.rightDerivedNatIso`,
  `Functor.IsRightDerivedFunctor`,
  `InjectiveResolution.isoRightDerivedObj`,
  `Functor.rightDerived_map_eq`;
- best owner abstraction: `CategoryTheory.Functor.rightDerived`;
- primitive data: an additive functor `F : 𝒜 ⥤ ℬ` and a degree `i : ℕ`;
- derived API: the source-facing bridge to a chosen total right derived functor, together with
  injective-resolution computations and naturality for `R^i F`.

Source/core/bridge triage:
- `source-facing`: the `i`-th right derived functor `R^iF` and its textbook realization through a
  chosen total right derived functor;
- `core/canonical`: `CategoryTheory.Functor.rightDerived`;
- `bridge/view`: for a chosen total right derived functor `RF : D(𝒜) ⥤ D(ℬ)`, the canonical
  comparison to the total right derived functor is owned by `Functor.rightDerivedNatIso` /
  `Functor.rightDerivedUnique`, and the textbook formula `R^iF(A) = H^i(RF(A[0]))` is the
  resulting source-facing companion view.

This item therefore should not keep a local owner-level bridge built from an arbitrary `RF`. The
canonical Chapter 21 owner is already `CategoryTheory.Functor.rightDerived`, the total
right-derived comparison belongs to `Functor.rightDerivedNatIso` / `Functor.rightDerivedUnique`,
and the source-facing formula is a companion interpretation of that owner. -/

/- 21.3.0.2: the `i`-th right derived functor of an additive functor `F` is canonically
`F.rightDerived i`; the source-facing notation for this owner is `R^i F`. This corresponds to the
textbook description `R^iF(A) = H^i(RF(A[0]))` after choosing a total right derived functor
`RF : D(𝒜) ⥤ D(ℬ)`. -/
recall Functor.rightDerived

namespace CategoryTheory

/-
Textbook surface notation for the `i`-th right derived functor `R^iF`.
This is the source-facing layer over the canonical owner `Functor.rightDerived`.
-/
scoped notation3:max "R^" i:max F:max => Functor.rightDerived F i

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
variable [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
variable [Abelian 𝒜] [HasInjectiveResolutions 𝒜] [Abelian ℬ]
variable (F : 𝒜 ⥤ ℬ) [F.Additive] (i : ℕ)

namespace Functor

/-- 21.3.0.2: the `i`-th right derived functor of `F`, denoted `R^i F`.
This is the canonical owner `Functor.rightDerived F i`; after choosing a total right derived
functor `RF : D(𝒜) ⥤ D(ℬ)`, the source equation identifies it with
`A ↦ H^i(RF(A[0]))`. -/
@[stacks 05U6]
noncomputable abbrev higherRightDerivedFunctor : 𝒜 ⥤ ℬ := R^i F

/-- Companion to 21.3.0.2: the source-facing abbreviation `higherRightDerivedFunctor F i` is exactly the
canonical `i`-th right derived functor `R^i F`. -/
@[stacks 05U6, simp]
theorem higherRightDerivedFunctor_def :
    higherRightDerivedFunctor F i = R^i F := rfl

end Functor

/- The standard injective-resolution computation of a right-derived value remains part of the
canonical API for `R^i F`; this is owned by
`InjectiveResolution.isoRightDerivedObj`. -/
recall InjectiveResolution.isoRightDerivedObj

/- Naturality of the `i`-th right derived functor is likewise part of the canonical owner API,
through `Functor.rightDerived_map_eq`. -/
recall Functor.rightDerived_map_eq

end

end CategoryTheory
