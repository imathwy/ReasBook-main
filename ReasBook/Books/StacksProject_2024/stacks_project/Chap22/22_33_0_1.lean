import Mathlib.Tactic.Recall
import StacksProject_2024.Chap22.Lemma_22_26_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DifferentialGradedCategory

universe u v w

-- Source/core/bridge triage:
-- * source-facing: the displayed tensor-by-bimodule functor on differential graded modules;
-- * core/canonical: the Chapter 22 DG owner `tensorWithN : DgFunctor ...`;
-- * bridge/view: the induced ordinary functor `tensorWithN.mapComp` on closed
--   degree-`0` morphisms.

/- The source item adds no new owner beyond Lemma `22.26.5`: once tensoring with the
differential graded `(A, B)`-bimodule `N` is recorded as a DG functor `tensorWithN`, the
displayed functor on differential graded modules is exactly the canonical underlying functor
`tensorWithN.mapComp` on closed degree-`0` morphisms. -/
recall DgFunctor.mapComp

section

variable {R : Type u} [CommRing R]
variable {ModdgA : Type v} {ModdgB : Type w}
variable [DifferentialGradedCategory R ModdgA] [DifferentialGradedCategory R ModdgB]
variable (tensorWithN : DgFunctor R ModdgA ModdgB)
variable (M : Comp R ModdgA) {M' : Comp R ModdgA} (f : M ⟶ M')

/- 22.33.0.1
Recall: for differential graded algebras `(A, d)` and `(B, d)` and a differential graded
`(A, B)`-bimodule `N`, the source item displays the functor
`Mod_{(A, d)} ⥤ Mod_{(B, d)}`, `M ↦ M ⊗_A N`.

In the current Chapter 22 API, this tensor construction is recorded at the differential graded
level by the DG functor `tensorWithN`. The displayed functor on differential graded modules is the
induced ordinary functor `tensorWithN.mapComp` from Lemma `22.26.5`, obtained by passing
to closed degree-`0` morphisms. -/
#check tensorWithN
#check (tensorWithN.mapComp : Comp R ModdgA ⥤ Comp R ModdgB)
#check ((tensorWithN.mapComp).obj M : Comp R ModdgB)
#check DgFunctor.mapComp_obj tensorWithN M

/- Companion recall: the displayed tensor construction is intended to be functorial on morphisms of
differential graded modules as well, via the induced functor `tensorWithN.mapComp`. -/
#check ((tensorWithN.mapComp).map f :
    (tensorWithN.mapComp).obj M ⟶ (tensorWithN.mapComp).obj M')

end
