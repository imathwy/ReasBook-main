import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/- Domain-style sampling for Lemma 12.29.1:
- primary domain: adjunctions, exact functors, monomorphism preservation, and injective-object
  preservation in abelian and preadditive categories;
- sampled owner declarations:
  * `exactFunctor_iff`
  * `Functor.preservesHomology_of_preservesMonos_and_cokernels`
  * `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`
  * `Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects`
- best owner abstraction: an adjunction `adj : v ⊣ u` together with the owner predicates
  `exactFunctor _ _ v`, `v.PreservesMonomorphisms`, and `u.PreservesInjectiveObjects`;
- primitive data: only the adjunction `adj`; additivity and exactness/mono/injective preservation
  remain owner-level properties rather than bundled local data;
- derived API: the source-facing bridges in parts `(1)` and `(2)`, and the direct owner recall in
  part `(3)`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma relating exactness of an additive left adjoint to preservation
  of monomorphisms, and then deducing preservation of injective objects for the right adjoint;
- `core/canonical`: `exactFunctor`, `Functor.PreservesMonomorphisms`,
  `Functor.PreservesInjectiveObjects`, and the owner adjunction criteria in mathlib;
- `bridge/view`: parts `(1)` and `(2)` below, which restate the textbook implications directly in
  terms of the owner predicates, while part `(3)` is the canonical owner theorem recalled as-is.
-/

section

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

variable {u : A ⥤ B} {v : B ⥤ A} [v.Additive]

/-- Lemma 12.29.1 (1): for additive functors `v ⊣ u` between abelian categories, `v` preserves
monomorphisms if and only if `v` is exact. -/
-- Proof sketch: a left adjoint preserves finite colimits by
-- `Adjunction.leftAdjoint_preservesColimits`. If `v` preserves monomorphisms, then this right
-- exactness, together with additivity and
-- `Functor.preservesHomology_of_preservesMonos_and_cokernels`, shows that `v` preserves finite
-- limits as well, hence is exact by `exactFunctor_iff`. Conversely, an exact functor preserves
-- finite limits, hence preserves monomorphisms.
theorem preservesMonomorphisms_iff_exact_of_leftAdjoint
    (adj : v ⊣ u)
    : v.PreservesMonomorphisms ↔ exactFunctor _ _ v := by
  constructor
  · intro hv
    letI : v.PreservesMonomorphisms := hv
    letI : PreservesColimits v := adj.leftAdjoint_preservesColimits
    letI : v.PreservesHomology := v.preservesHomology_of_preservesMonos_and_cokernels
    exact (exactFunctor_iff v).2 ⟨v.preservesFiniteLimits_of_preservesHomology, inferInstance⟩
  · intro hExact
    letI : PreservesFiniteLimits v := (exactFunctor_iff v).1 hExact |>.1
    infer_instance

end

section

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {u : A ⥤ B} {v : B ⥤ A}

/-- Lemma 12.29.1 (2): if the left adjoint `v` is exact, then the right adjoint `u` preserves
injective objects. -/
-- Proof sketch: by part (1), exactness of the left adjoint `v` implies that `v` preserves
-- monomorphisms. Then
-- `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms` applied to
-- `adj : v ⊣ u` shows that `u` maps injective objects to injective objects.
theorem preservesInjectiveObjects_of_exact_leftAdjoint
    (adj : v ⊣ u)
    (hExact : exactFunctor _ _ v) :
    u.PreservesInjectiveObjects := by
  letI : v.PreservesMonomorphisms := by
    letI : PreservesFiniteLimits v := (exactFunctor_iff v).1 hExact |>.1
    infer_instance
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj

end

/- Lemma 12.29.1 (3): if `A` has enough injectives and the right adjoint `u` preserves injective
objects, then the left adjoint `v` preserves monomorphisms. This is exactly the canonical
adjunction criterion `Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects`.
-/
recall Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects

end CategoryTheory
