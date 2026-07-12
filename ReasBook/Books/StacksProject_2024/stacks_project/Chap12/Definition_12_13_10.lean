import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v u

variable {V : Type u} [Category.{v} V] [Abelian V]

/- Domain-style sampling for Definition 12.13.10:
- primary domain: quasi-isomorphisms and acyclic cochain complexes;
- sampled canonical owner declarations:
  `QuasiIso`,
  `quasiIso_iff`,
  `quasiIsoAt_iff_isIso_homologyMap`,
  `HomologicalComplex.Acyclic`,
  `HomologicalComplex.acyclic_iff`,
  `HomologicalComplex.exactAt_iff_isZero_homology`;
- source/core/bridge triage:
  `core/canonical`: `QuasiIso f` and `K.Acyclic`,
  `bridge/view`: the owner characterizations `quasiIso_iff`,
  `quasiIsoAt_iff_isIso_homologyMap`, `HomologicalComplex.acyclic_iff`, and
  `HomologicalComplex.exactAt_iff_isZero_homology`.

Primitive data are already owned by `QuasiIso` and `HomologicalComplex.Acyclic`. The source-facing
criteria are therefore best exposed by direct recall of the owner predicates and their canonical
characterization lemmas, rather than by introducing a cochain-specific chapter-local wrapper.
-/

/- Definition 12.13.10 (1): a morphism of cochain complexes is a quasi-isomorphism exactly when it
satisfies the canonical predicate `QuasiIso`; equivalently, each induced cohomology map is an
isomorphism. -/
recall QuasiIso
recall quasiIso_iff
recall quasiIsoAt_iff_isIso_homologyMap

/- Definition 12.13.10 (2): a cochain complex is acyclic when it is exact in every degree; mathlib
packages this canonical notion by `HomologicalComplex.Acyclic`, and in an abelian category this is
equivalent to vanishing of all cohomology objects. -/
recall HomologicalComplex.Acyclic
recall HomologicalComplex.acyclic_iff
recall HomologicalComplex.exactAt_iff_isZero_homology
