import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Topology.Sheaves.Presheaf
import stacks_project.Chap20.«20_9_0_1»

open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.Limits

universe u v

variable {X : TopCat.{u}} {ι : Type v}
variable (𝒰 : ι → Opens X) (ℱ : X.Presheaf AddCommGrpCat.{max u v})

local instance : HasFiniteProducts (Opens X) := opensHasFiniteProducts X

/- Domain-style sampling for Definition 20.23.1:
- primary domain: Čech cochain complexes of abelian presheaves on the lattice of opens of a
  topological space;
- sampled owner API:
  `AlternatingCofaceMapComplex.objD`,
  `FormalCoproduct.cochainComplexFunctor`,
  `cechComplexFunctor`;
- best owner abstraction: `cechComplexFunctor 𝒰`.

Source/core/bridge triage:
- `source-facing`: the alternating Čech complex attached to the cover `𝒰` and presheaf `ℱ`;
- `core/canonical`: `(cechComplexFunctor 𝒰).obj ℱ`;
- `bridge/view`: the tuplewise Čech-term and differential formulas developed later as coordinate API.

Primitive data versus derived API:
- primitive data: only the indexed family `𝒰` and the abelian presheaf `ℱ`;
- derived API: the cochain terms, differentials, and full complex structure, all already supplied
  by `cechComplexFunctor`.

This numbered definition is therefore recall-only: it should not keep a parallel local alias for
the canonical owner. -/

/- Core recall: the alternating Čech complex of `ℱ` for the cover `𝒰` is the canonical
specialization `(cechComplexFunctor 𝒰).obj ℱ`. -/
recall cechComplexFunctor

/- Specialized check for Definition 20.23.1. -/
#check ((cechComplexFunctor 𝒰).obj ℱ : CochainComplex AddCommGrpCat.{max u v} ℕ)
