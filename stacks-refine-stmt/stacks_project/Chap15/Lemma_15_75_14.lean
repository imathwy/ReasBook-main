import Mathlib
import stacks_project.Chap10.Definition_10_110_7
import stacks_project.Chap15.Definition_15_75_1

noncomputable section

open CategoryTheory
open DerivedCategory.TStructure

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} [CommRing R] [IsRegularRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "Bounded" => (t.bounded : ObjectProperty DMod)
local notation:max "H^" i:max => DerivedCategory.homologyFunctor (ModuleCat R) i

/- Domain-style sampling for Lemma 15.75.14:
- primary domain: perfect objects in derived categories of modules over a regular ring;
- sampled owner declarations:
  `ModuleCat.IsPerfect`,
  `DerivedCategory.IsPerfect`,
  `t.bounded`,
  `DerivedCategory.homologyFunctor`;
- best owner abstraction:
  part `(1)` is `source-facing` at the module level, while part `(2)` is `source-facing` on
  `D(R)` with boundedness read through the canonical owner `t.bounded`
  and cohomology read through the canonical owner `DerivedCategory.homologyFunctor`;
- primitive vs. derived:
  primitive data are a module `M` or a derived object `K`;
  derived API is perfectness, boundedness, and the degreewise finiteness condition on the
  cohomology modules;
- source/core/bridge triage:
  `source-facing`: the two equivalences below;
  `core/canonical`: `ModuleCat.IsPerfect`, `DerivedCategory.IsPerfect`, and
    `t.bounded`;
  `bridge/view`: the cohomology functors `H^i` landing in `ModuleCat R`.

This file should therefore keep the textbook equivalences, but phrase boundedness through the
canonical `t`-structure owner directly and avoid depending on the later parallel bounded-derived
API file.
-/

namespace ModuleCat

-- Proof sketch: for the forward implication, unwind perfection to a bounded finite-projective
-- representative and note that its degree-zero homology is finite over the Noetherian ring `R`.
-- For the converse, apply Lemma `15.75.3` together with regularity of `R` to obtain a finite
-- projective resolution of a finite module, hence a perfect representative.
/-- Lemma 15.75.14 (1): over a regular ring `R`, an `R`-module is perfect if and only if it is a
finite `R`-module. -/
theorem isPerfect_iff_finite (M : ModuleCat R) :
    M.IsPerfect ↔ Module.Finite R M := sorry

end ModuleCat

-- Proof sketch: if `K` is perfect, represent it by a bounded complex of finite projective
-- modules; this gives bounded cohomology and finite homology modules. Conversely, if `K` lies in
-- `D^b(R)` with finite cohomology, apply part `(1)` degreewise to see that each `H^i(K)` is a
-- perfect module, then use Lemma `15.75.7` to recover perfection of `K`.
/-- Lemma 15.75.14 (2): over a regular ring `R`, a derived `R`-complex is perfect if and only if
it belongs to `D^b(R)` and each cohomology module is finite. -/
theorem isPerfect_iff_bounded_and_finite_homology
    (K : DMod) :
    K.IsPerfect ↔
      Bounded K ∧
        ∀ i : ℤ, Module.Finite R ((H^i).obj K) := sorry

end
