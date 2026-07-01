import Mathlib
import stacks_project.Chap12.Lemma_12_10_7
import stacks_project.Chap12.Lemma_12_29_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/-
Domain-style sampling for Lemma 12.29.3:
- primary domain: adjunctions, exact functors, faithfulness / reflected monomorphisms, and enough
  injectives in abelian categories;
- sampled owner declarations:
  * `EnoughInjectives.of_adjunction`
  * `preservesMonomorphisms_iff_exact_of_leftAdjoint`
  * `Functor.faithful_of_exact_of_kernel_le_isZero`
  * the canonical instance `Functor.ReflectsMonomorphisms` from faithfulness;
- best owner abstraction: the adjunction `adj : v ⊣ u` together with the owner predicates
  `v.PreservesMonomorphisms`, `v.Faithful`, and `EnoughInjectives`;
- primitive data: `adj`, monomorphism preservation for `v`, and the source-facing zero-object
  detection hypothesis `hzero`;
- derived API: internally, exactness and faithfulness of `v`, with reflected monomorphisms coming
  from the canonical faithful-functor instance before applying `EnoughInjectives.of_adjunction`.

Source/core/bridge triage:
- `source-facing`: the Stacks criterion transferring enough injectives across an adjunction under
  the extra zero-object detection hypothesis;
- `core/canonical`: `EnoughInjectives.of_adjunction`;
- `bridge/view`: the internal derivation of `v.Faithful` from `hzero`.
-/

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable {u : A ⥤ B} {v : B ⥤ A} [v.Additive]

/-- Lemma 12.29.3: if `u` is right adjoint to `v`, if `v` preserves monomorphisms, if `A` has
enough injectives, and if `v.obj X` being zero forces `X` to be zero, then `B` has enough
injectives. -/
-- Proof sketch: by Lemma 12.29.1 (1), the left adjoint `v` is exact. Exactness together with the
-- zero-detection hypothesis makes `v` faithful by
-- `Functor.faithful_of_exact_of_kernel_le_isZero`; the canonical faithful-functor instance then
-- gives `v.ReflectsMonomorphisms`. The owner theorem `EnoughInjectives.of_adjunction adj`
-- transfers enough injectives from `A` to `B`.
lemma enoughInjectives_of_rightAdjoint_of_preservesMonomorphisms
    (adj : v ⊣ u) [v.PreservesMonomorphisms] [EnoughInjectives A]
    (hzero : ∀ X : B, IsZero (v.obj X) → IsZero X) :
    EnoughInjectives B := by
  let hExact : exactFunctor B A v :=
    (preservesMonomorphisms_iff_exact_of_leftAdjoint adj).1 inferInstance
  letI : PreservesFiniteLimits v := (exactFunctor_iff v).1 hExact |>.1
  letI : PreservesFiniteColimits v := (exactFunctor_iff v).1 hExact |>.2
  letI : v.Faithful :=
    Functor.faithful_of_exact_of_kernel_le_isZero v <| show v.kernel ≤ IsZero from hzero
  exact EnoughInjectives.of_adjunction adj

end CategoryTheory
