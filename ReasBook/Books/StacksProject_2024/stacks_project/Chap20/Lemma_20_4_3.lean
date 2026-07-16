import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap21.Lemma_21_4_3

open TopologicalSpace

universe u

namespace CategoryTheory

section

variable {X : TopCat.{u}}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u + 1} (X.Sheaf AddCommGrpCat.{u})]
variable (ℋ : X.Sheaf AddCommGrpCat.{u})

/- Domain-style sampling for Lemma 20.4.3:
- primary domain: abelian sheaf torsors and first sheaf cohomology on the opens site of a
  topological space;
- sampled owner declarations:
  `abelianSheafTorsor_isoClasses_to_H1`,
  `abelianSheafTorsor_isoClasses_to_H1_bijective`,
  `abelianSheafTorsor_isoClasses_to_H1_trivial`,
  `abelianSheafTorsor_isoClasses_equiv_H1`,
  `Sheaf.toSheafOfGroups`,
  `Sheaf.Torsor.trivial`;
- best owner abstraction:
  `source-facing`: the topological-site specialization of the normalized torsor/H¹ classification
    equivalence for `ℋ`;
  `core/canonical`: the site-level Chapter 21 comparison map
  `abelianSheafTorsor_isoClasses_to_H1`, with bijectivity/equivalence companions
    `abelianSheafTorsor_isoClasses_to_H1_bijective`,
    `abelianSheafTorsor_isoClasses_to_H1_trivial`, and
    `abelianSheafTorsor_isoClasses_equiv_H1`;
  `bridge/view`: specialization to `Opens.grothendieckTopology X`.

This item adds no new local theorem: the faithful refinement is to recall the Chapter 21 torsor/H¹
classification theorem directly at the opens site of `X`, while keeping the canonical comparison
map and its normalization/bijectivity theorems as typed companions.
-/

/- Lemma 20.4.3: for a topological space `X` and an abelian sheaf `ℋ` on `X`, isomorphism
classes of `ℋ`-torsors are in bijection with `H¹(X, ℋ)`, and the trivial torsor class
corresponds to `0`. The source-facing statement is exactly the Chapter 21 theorem
`abelianSheafTorsor_isoClasses_equiv_H1` specialized to `Opens.grothendieckTopology X`; the
comparison map and its normalization/bijectivity theorems remain companion API. -/
recall abelianSheafTorsor_isoClasses_equiv_H1

/- Companion specialization: the canonical comparison map from `ℋ`-torsor isomorphism classes
to `H¹(X, ℋ)`. -/
#check (abelianSheafTorsor_isoClasses_to_H1 ℋ :
  Sheaf.Torsor.IsoClasses (Sheaf.toSheafOfGroups ℋ) → ℋ.H 1)

/- Companion specialization: the canonical comparison map is bijective. -/
#check (abelianSheafTorsor_isoClasses_to_H1_bijective ℋ :
  Function.Bijective (abelianSheafTorsor_isoClasses_to_H1 ℋ))

/- Companion specialization: the trivial `ℋ`-torsor class maps to `0`. -/
#check (abelianSheafTorsor_isoClasses_to_H1_trivial ℋ :
  abelianSheafTorsor_isoClasses_to_H1 ℋ
      (_root_.Quotient.mk'' (Sheaf.Torsor.trivial (Sheaf.toSheafOfGroups ℋ))) = 0)

end

end CategoryTheory
