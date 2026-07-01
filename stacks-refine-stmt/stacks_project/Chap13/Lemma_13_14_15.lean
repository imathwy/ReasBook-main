import Mathlib
import stacks_project.Chap04.Definition_4_27_20
import stacks_project.Chap13.Lemma_13_14_14

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.MorphismProperty

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

section

/-
Domain-style sampling for Lemma 13.14.15:
- primary domain: pointwise existence of derived functors with respect to a localization class,
  using object-property/cofinality criteria;
- sampled owner declarations in the project:
  `Functor.ComputesRightDerivedAt` / `Functor.ComputesLeftDerivedAt`,
  `Functor.hasPointwiseRightDerivedFunctor_of_exists_computesRightDerivedAt` /
  `Functor.hasPointwiseLeftDerivedFunctor_of_exists_computesLeftDerivedAt`;
- best owner abstraction: the canonical ambient owner for the localization class is
  `S.IsSaturatedMultiplicativeSystem`, and the public targets of this file are the category-level
  owner predicates `Functor.ComputesRightDerivedAt`, `Functor.ComputesLeftDerivedAt`,
  `Functor.HasPointwiseRightDerivedFunctor`, and `Functor.HasPointwiseLeftDerivedFunctor`.
  The source-facing “subset of good objects” should therefore be represented by
  `ObjectProperty D`, the existing owner for predicates on objects.

Source/core/bridge triage:
- `source-facing`: the Stacks cofinality criteria using object properties `I` and `P`;
- `core/canonical`: `S.IsSaturatedMultiplicativeSystem` together with the derived-functor owner
  predicates `ComputesRightDerivedAt`, `ComputesLeftDerivedAt`,
  `HasPointwiseRightDerivedFunctor`, and `HasPointwiseLeftDerivedFunctor`;
- `bridge/view`: the four theorems in this file, which turn the source-facing subset hypotheses
  into those canonical owner predicates.

Primitive data:
- the functor `F`,
- the saturated multiplicative system structure on `S`,
- the source-facing reachability and isomorphism hypotheses on the chosen object properties.

Derived API:
- the localization transport lemmas on pointwise derivability,
- the pointwise and global derived-functor existence predicates for `F`.
-/

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)
  [S.IsSaturatedMultiplicativeSystem]

section Right

variable (I : ObjectProperty D)
variable
  (hI_reaches : ∀ X : D, ∃ (X' : D) (s : X ⟶ X'), I X' ∧ S s)
  (hI_isIso :
    ∀ {X X' : D} (s : X ⟶ X'), I X → I X' → S s → IsIso (F.map s))

include hI_reaches hI_isIso

-- Proof sketch: for `X ∈ I`, the full subcategory of `X / S` consisting of denominators landing
-- in `I` contains the identity denominator of `X`, is cofinal in the full indexing category by
-- the same reachability argument, and all of its transition maps are sent to isomorphisms by
-- `hI_isIso`. Hence the pointwise right-derived diagram is essentially constant with value
-- `F.obj X`, so `X` computes the right derived functor directly, with no extra global
-- derivability hypothesis.
/-- Lemma 13.14.15 (2): under the same hypotheses, any object `X ∈ I` computes the right derived
functor of `F` with respect to `S`. -/
theorem computesRightDerivedAt_of_mem_subset
    {X : D} (hX : I X) :
    F.ComputesRightDerivedAt S X := sorry

-- Proof sketch: apply the canonical Chapter 13 bridge from existence of enough objects computing
-- the right derived functor. The source-facing content here is precisely that every `X` reaches
-- some `X' ∈ I`, and those `X'` compute `RF` by the previous theorem.
/-- Lemma 13.14.15 (1): if every object of `D` admits an arrow in `S` to an object of `I`, and
if `F` sends arrows of `S` between objects of `I` to isomorphisms, then the right derived
functor of `F` with respect to `S` is everywhere defined. -/
theorem hasPointwiseRightDerivedFunctor_of_subset :
    F.HasPointwiseRightDerivedFunctor S :=
  F.hasPointwiseRightDerivedFunctor_of_exists_computesRightDerivedAt S fun X ↦ by
    rcases hI_reaches X with ⟨X', s, hX', hs⟩
    exact ⟨X', s, hs,
      computesRightDerivedAt_of_mem_subset F S I hI_reaches hI_isIso hX'⟩

omit hI_reaches hI_isIso

end Right

section Left

variable (P : ObjectProperty D)
variable
  (hP_reaches : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s)
  (hP_isIso :
    ∀ {X X' : D} (s : X ⟶ X'), P X → P X' → S s → IsIso (F.map s))

include hP_reaches hP_isIso

-- Proof sketch: for `X ∈ P`, the full subcategory of `S \ X` consisting of denominators with
-- source in `P` contains the identity denominator of `X`, is cofinal by `hP_reaches`, and all
-- of its transition maps are sent to isomorphisms by `hP_isIso`. Thus the pointwise left-derived
-- diagram is essentially constant with value `F.obj X`, so `X` computes the left derived
-- functor directly.
/-- Lemma 13.14.15 (4): under the dual hypotheses, any object `X ∈ P` computes the left derived
functor of `F` with respect to `S`. -/
theorem computesLeftDerivedAt_of_mem_subset
    {X : D} (hX : P X) :
    F.ComputesLeftDerivedAt S X := sorry

-- Proof sketch: this is the left-derived dual of part `(1)`, using the canonical bridge from
-- enough objects computing the left derived functor to everywhere-defined pointwise existence.
/-- Lemma 13.14.15 (3): dually, if every object of `D` receives an arrow in `S` from an object
of `P`, and if `F` sends arrows of `S` between objects of `P` to isomorphisms, then the left
derived functor of `F` with respect to `S` is everywhere defined. -/
theorem hasPointwiseLeftDerivedFunctor_of_subset :
    F.HasPointwiseLeftDerivedFunctor S :=
  F.hasPointwiseLeftDerivedFunctor_of_exists_computesLeftDerivedAt S fun X ↦ by
    rcases hP_reaches X with ⟨X', s, hX', hs⟩
    exact ⟨X', s, hs,
      computesLeftDerivedAt_of_mem_subset F S P hP_reaches hP_isIso hX'⟩

omit hP_reaches hP_isIso

end Left

end

end Functor

end CategoryTheory
