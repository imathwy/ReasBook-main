import Mathlib
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap13.Definition_13_8_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_10_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

universe v u

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroObject 𝒜]
  [Preadditive 𝒜] [HasBinaryBiproducts 𝒜]

/- Domain-style sampling:
- primary domain: distinguished triangles in homotopy categories of cochain complexes;
- sampled owner declarations in this domain:
  `Pretriangulated.distinguishedTriangles`,
  `distTriang (K(𝒜))`,
  `HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`,
  `distTriang (K⁺(𝒜))`,
  the bounded homotopy-category owners from `Definition_13_8_1`;
- source/core/bridge triage:
  `source-facing`: the Stacks definition of distinguished triangles on `K(\mathcal A)` and on the
    bounded homotopy categories `K^+(\mathcal A)`, `K^-(\mathcal A)`, `K^b(\mathcal A)`;
  `core/canonical`: the owner `Pretriangulated.distinguishedTriangles`, surfaced as `distTriang`
    on each pretriangulated homotopy category;
  `bridge/view`: the degreewise-split characterization theorem on `K(\mathcal A)` and the
    bounded full-subcategory views from `Definition_13_8_1`; once the triangulated full-subcategory
    instances from Lemma 13.10.5 are in scope, their inclusions use the canonical reflection
    theorem `Functor.map_distinguished_iff`.

Primitive data is only the ambient homotopy category together with its canonical pretriangulated
structure. The degreewise-split description and the bounded full-subcategory descriptions are
derived API around that owner, so this file should recall the existing owner directly rather than
introduce any parallel local predicate or wrapper.
-/

/- Definition 13.10.1: on the homotopy category `K(\mathcal A) = HomotopyCategory 𝒜
(ComplexShape.up ℤ)`, distinguished triangles are given by the canonical owner
`distTriang (K(𝒜))`, i.e. the specialization of `Pretriangulated.distinguishedTriangles` to the
pretriangulated homotopy category. Equivalently, by
`HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`, a triangle is distinguished
exactly when it is isomorphic to the triangle attached to a termwise split exact sequence of
cochain complexes as in Definition 13.9.9. The same canonical owner is used for
`K^{+}(\mathcal A)`, `K^{-}(\mathcal A)`, and `K^{b}(\mathcal A)`. -/
#check (distTriang (K(𝒜)))

/- Companion recall: the characterization of distinguished triangles in the homotopy category by
termwise split exact sequences of cochain complexes is exactly the canonical mathlib theorem
`HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`. -/
recall HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit

/- Definition 13.10.1 on the bounded homotopy categories uses the same canonical owner
`distTriang` on `K^{+}(\mathcal A)`, `K^{-}(\mathcal A)`, and `K^{b}(\mathcal A)`. -/
#check (distTriang (K⁺(𝒜)))
#check (distTriang (K⁻(𝒜)))
#check (distTriang (Kᵇ(𝒜)))

/- Companion recall: the source-facing description of distinguished triangles in these bounded
homotopy categories is that the inclusion into `K(\mathcal A)` reflects distinguished triangles;
this is exactly the canonical theorem `Functor.map_distinguished_iff` applied to the full
faithful exact inclusions `ObjectProperty.ι (HomotopyCategory.plus 𝒜)`,
`ObjectProperty.ι (HomotopyCategory.minus 𝒜)`, and
`ObjectProperty.ι (HomotopyCategory.bounded 𝒜)`. -/
recall Functor.map_distinguished_iff

end
