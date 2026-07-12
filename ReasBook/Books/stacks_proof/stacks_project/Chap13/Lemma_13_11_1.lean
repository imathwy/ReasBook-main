import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape

universe v u

variable (A : Type u) [Category.{v} A] [Abelian A]

local notation "H" => HomotopyCategory.homologyFunctor A (up ℤ)

/- Domain-style sampling for Lemma 13.11.1:
- primary domain: homological functors on the homotopy category of cochain complexes in an
  abelian category;
- sampled owner declarations:
  `Functor.IsHomological`,
  `Functor.IsHomological.mk'`,
  `Functor.map_distinguished_exact`,
  `HomotopyCategory.homologyFunctor`,
  the canonical instance
    `(homologyFunctor C (ComplexShape.up ℤ) n).IsHomological`;
- best owner abstraction: the canonical functor `H 0` together with its
  `Functor.IsHomological` instance;
- source/core/bridge triage:
  `source-facing`: the degree-zero homology functor `H^0 : K(\mathcal A) ⥤ \mathcal A`;
  `core/canonical`: `Functor.IsHomological`;
  `bridge/view`: none, because the source statement is already the canonical owner instance.

Primitive data are only the ambient abelian category and the homology functor. Homologicality is
derived API supplied upstream, so this file should use the existing owner declarations directly
rather than introduce a one-off local alias or parallel theorem.
-/

/- Companion recall: the degree-`n` homology functor on the homotopy category is the canonical
owner `HomotopyCategory.homologyFunctor`. -/
recall HomotopyCategory.homologyFunctor

/- Lemma 13.11.1: for an abelian category `\mathcal A`, the degree-zero homology functor
`H^0 : K(\mathcal A) ⥤ \mathcal A` is homological. This is the canonical instance on `H 0`. -/
#check (inferInstance : (H 0).IsHomological)
