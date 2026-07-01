import Mathlib.Tactic.Recall
import stacks_project.Chap06.Lemma_6_26_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry

universe u

/- Domain-style sampling for subsheaf generation by local sections:
- primary domain: subobjects of `\mathcal O_X`-module sheaves on a ringed space;
- sampled owner declarations:
  `CategoryTheory.Subobject`,
  `CategoryTheory.Subobject.arrow`,
  `CategoryTheory.Subobject.sInf`,
  `CategoryTheory.Subobject.sInf_le`,
  `CategoryTheory.Subobject.le_sInf`,
  `RingedSpace.Modules`,
  `subsheaf_contains_local_sections`;
- source-facing layer: existence and uniqueness of the smallest subsheaf containing prescribed
  local sections;
- core/canonical owner abstraction: the complete lattice `Subobject ℱ`, with the generated
  subsheaf defined in the next item as the infimum of all subsheaves containing the prescribed
  local sections;
- bridge/view layer here: the direct source-facing existence/uniqueness theorem.

Primitive-vs-derived split:
- primitive data: a ringed space `X`, an `\mathcal O_X`-module sheaf `ℱ`, opens `U i`, and
  sections `s i`;
- derived API: the containment predicate and the unique-minimality theorem below.
-/

namespace AlgebraicGeometry

variable {X : RingedSpace}
variable {I : Type u}

/-- A subsheaf contains the indexed local sections `s i` when each `s i` lifts to a section of that
subsheaf over `U i`. -/
def subsheaf_contains_local_sections
    (ℱ : RingedSpace.Modules X) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    (G : Subobject ℱ) : Prop :=
  ∀ i, ∃ t : (G : RingedSpace.Modules X).val.obj (op (U i)),
    (SheafOfModules.Hom.val G.arrow).app (op (U i)) t = s i

/-- Lemma 17.4.4: for a ringed space `X`, an `\mathcal O_X`-module sheaf `ℱ`, and local sections
`s i ∈ ℱ(U i)`, there exists a unique smallest subsheaf of `ℱ` containing all the `s i`. -/
theorem existsUnique_subsheaf_generated_by_local_sections
    (ℱ : RingedSpace.Modules X) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i))) :
    ∃! G : Subobject ℱ,
      subsheaf_contains_local_sections ℱ U s G ∧
        ∀ H : Subobject ℱ,
          subsheaf_contains_local_sections ℱ U s H →
            G ≤ H := by
  sorry

end AlgebraicGeometry
