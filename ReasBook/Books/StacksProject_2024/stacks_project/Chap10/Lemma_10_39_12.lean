import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.Equalizer
import StacksProject_2024.stacks_project.Chap10.Definition_10_82_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory MonoidalCategory
open LinearMap

namespace CategoryTheory.ShortComplex.ShortExact

section

variable {R : Type u} [CommRing R]

/- Domain triage:
- primary domain: flat modules and tensor exactness for short complexes of `R`-modules;
- sampled owner declarations: `CategoryTheory.ShortComplex.UniversallyExact`,
  `LinearMap.UniversallyInjective`, `Module.Flat.iff_lTensor_exact`, and `ShortComplex.map`;
- owner choice: universal exactness of a short complex is the canonical owner-level statement, and
  short exactness after tensoring with a fixed module is the source-facing companion statement.
-/

-- Proof sketch: exactness and flatness of the cokernel give universal injectivity of `S.f` via
-- `LinearMap.lTensor_injective_of_exact_of_flat`, so `S` is universally exact in the owner sense.
/-- Lemma 10.39.12, owner form: a short exact sequence of `R`-modules with flat cokernel is
universally exact. -/
theorem universallyExact_of_flat_X₃ {S : ShortComplex (ModuleCat R)}
    (hS : S.ShortExact) [Module.Flat R S.X₃] :
    ShortComplex.UniversallyExact S := sorry

-- Proof sketch: combine the owner form `universallyExact_of_flat_X₃` with right exactness of
-- tensor products and the universal injectivity of the first map.
/-- Lemma 10.39.12: if `0 ⟶ M'' ⟶ M' ⟶ M ⟶ 0` is a short exact sequence of `R`-modules and
`M` is flat, then for every `R`-module `N` the tensor sequence
`0 ⟶ N ⊗[R] M'' ⟶ N ⊗[R] M' ⟶ N ⊗[R] M ⟶ 0` is short exact. -/
theorem tensorLeft_of_flat_cokernel {S : ShortComplex (ModuleCat R)}
    (hS : S.ShortExact) [Module.Flat R S.X₃] (N : ModuleCat R) :
    (S.map (tensorLeft N)).ShortExact := sorry

end

end CategoryTheory.ShortComplex.ShortExact
