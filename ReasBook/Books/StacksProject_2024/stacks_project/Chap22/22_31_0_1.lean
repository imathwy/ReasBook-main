import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap22.Lemma_22_26_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DifferentialGradedCategory

universe u v w

-- Source/core/bridge triage:
-- * source-facing: the displayed functor `Hom_B(N, -)` on differential graded modules;
-- * core/canonical: the DG internal-Hom functor `homOverBFromN`;
-- * bridge/view: the induced ordinary functor `homOverBFromN.mapComp` on closed degree-`0`
--   morphisms from Lemma `22.26.5`.

/- Companion recall: Lemma `22.26.5` already exports the canonical DG-to-underlying-category
bridge `DgFunctor.mapComp`, so this item should specialize that owner directly rather than
introduce a local alias. -/
recall DgFunctor.mapComp

section

variable {R : Type u} [CommRing R]
variable {DGModB : Type v} {DGModA : Type w}
variable [DifferentialGradedCategory R DGModB] [DifferentialGradedCategory R DGModA]
variable (homOverBFromN : DgFunctor R DGModB DGModA)
variable (M : Comp R DGModB) {M' : Comp R DGModB} (f : M ⟶ M')

/- 22.31.0.1
Recall: for differential graded algebras `(A, d)` and `(B, d)` and a differential graded
`(A, B)`-bimodule `N`, the source item displays the functor
`Hom_{Mod^{dg}_{(B, d)}}(N, -) : Mod_{(B, d)} ⥤ Mod_{(A, d)}`.

In the current Chapter 22 API, the represented internal-Hom construction attached to `N` is
recorded at the DG level by `homOverBFromN`, and the displayed functor on differential graded
modules is the induced functor on closed degree-`0` morphisms `homOverBFromN.mapComp` from
Lemma `22.26.5`. -/
#check homOverBFromN
#check (homOverBFromN.mapComp : Comp R DGModB ⥤ Comp R DGModA)
#check ((homOverBFromN.mapComp).obj M : Comp R DGModA)
#check DgFunctor.mapComp_obj homOverBFromN M

/- Companion recall: the displayed internal-Hom construction is intended to be functorial on
morphisms of differential graded `B`-modules as well, via the induced functor
`homOverBFromN.mapComp`. -/
#check ((homOverBFromN.mapComp).map f :
    (homOverBFromN.mapComp).obj M ⟶ (homOverBFromN.mapComp).obj M')

end
