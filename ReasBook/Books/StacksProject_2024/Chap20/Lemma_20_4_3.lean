import Mathlib
import StacksProject_2024.Chap21.Lemma_21_4_3

open CategoryTheory TopologicalSpace

universe u

section

variable {X : TopCat.{u}}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u + 1} (X.Sheaf AddCommGrpCat.{u})]
variable (ℋ : X.Sheaf AddCommGrpCat.{u})

/- Domain-style sampling for Lemma 20.4.3:
- primary domain: abelian sheaf torsors and first sheaf cohomology on the topological site of a
  space;
- sampled owner declarations:
  `AbelianSheafTorsor`,
  `AbelianSheafTorsor.IsoClasses`,
  `abelianSheafTorsor_isoClasses_equiv_H1`,
  `Opens.grothendieckTopology`;
- best owner abstraction: the site-level torsor-classification theorem
  `abelianSheafTorsor_isoClasses_equiv_H1`, specialized to the Grothendieck topology on `X`;
- primitive data: the topological site `Opens.grothendieckTopology X`, the abelian sheaf `ℋ`, and
  the canonical sheafification/Ext infrastructure;
- derived API: the topological-space specialization
  `Nonempty (AbelianSheafTorsor.IsoClasses ℋ ≃ ℋ.H 1)`.

Primitive-vs-derived split:
- primitive data are already owned by the site-level theorem;
- the Chapter 20 statement is only the specialization to a topological site, so it should not keep
  a parallel local theorem with the exact same interface.

Source/core/bridge triage:
- `source-facing`: the classification of `ℋ`-torsors on a topological space `X`;
- `core/canonical`: `abelianSheafTorsor_isoClasses_equiv_H1` on an arbitrary site;
- `bridge/view`: the specialization from the site-level owner to `Opens.grothendieckTopology X`.
-/

/- Lemma 20.4.3: for a topological space `X` and an abelian sheaf `ℋ` on `X`, the set of
isomorphism classes of `ℋ`-torsors on `X` is canonically in bijection with `H^1(X, ℋ)`. This is
the specialization of the site-level owner theorem to `Opens.grothendieckTopology X`. -/
#check (abelianSheafTorsor_isoClasses_equiv_H1 ℋ :
  Nonempty (AbelianSheafTorsor.IsoClasses ℋ ≃ ℋ.H 1))

end
