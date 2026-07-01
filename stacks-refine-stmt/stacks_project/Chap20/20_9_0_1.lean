import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Tactic.Recall

open CategoryTheory CategoryTheory.Limits AlgebraicTopology TopologicalSpace
open CategoryTheory.Limits.CompleteLattice

universe w v v' u u'

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
variable {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
variable {ι : Type w} (U : ι → C)

/-- The lattice of open subsets of a topological space has a top element. -/
abbrev opensOrderTop (X : TopCat.{u}) : OrderTop (Opens X) where
  top := ⟨Set.univ, isOpen_univ⟩
  le_top := by
    intro U x hx
    trivial

/-- The category of open subsets of a topological space has finite products, given by finite
intersections. -/
theorem opensHasFiniteProducts (X : TopCat.{u}) : HasFiniteProducts (Opens X) := by
  letI : OrderTop (Opens X) := opensOrderTop X
  letI : HasFiniteLimits (Opens X) := hasFiniteLimits_of_semilatticeInf_orderTop
  infer_instance

/- Domain-style sampling for 20.9.0.1:
- primary domain: Čech cochain complexes and their alternating-coface differentials;
- sampled owner API:
  `AlternatingCofaceMapComplex.objD`,
  `FormalCoproduct.cochainComplexFunctor`,
  `cechComplexFunctor`;
- best owner abstraction: `cechComplexFunctor U` for the full Čech cochain complex, with
  `AlternatingCofaceMapComplex.objD` as the differential owner and
  `FormalCoproduct.cochainComplexFunctor` as the canonical intermediate bridge from the Čech
  cosimplicial object in `FormalCoproduct C` to a cochain complex.

Source/core/bridge triage:
- `source-facing`: the alternating Čech coboundary and the resulting Čech cochain complex;
- `core/canonical`: `cechComplexFunctor U`;
- `bridge/view`: specialization of `AlternatingCofaceMapComplex.objD` through
  `FormalCoproduct.cochainComplexFunctor`.

Primitive data versus derived API:
- primitive data: only the family `U : ι → C`;
- derived API: the differential, cochain terms, and full cochain complex, all already derived by
  the canonical owners above.

This item should therefore remain a recall-only bridge file, not a place for a parallel local Čech
complex implementation. -/
/- Bridge recall: the displayed Čech differential is the canonical alternating-coface differential
on the underlying cosimplicial object. -/
recall AlternatingCofaceMapComplex.objD

/- Intermediate recall: the Čech cosimplicial object in `FormalCoproduct C` is sent to its
cochain complex by the canonical owner `FormalCoproduct.cochainComplexFunctor`. -/
recall FormalCoproduct.cochainComplexFunctor

/- Core recall: the full Čech cochain complex attached to the family `U` is the canonical
functorial owner `cechComplexFunctor U`. -/
recall cechComplexFunctor
