import Mathlib.Tactic.Recall
import StacksProject_2024.Chap22.Lemma_22_26_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DifferentialGradedCategory

universe u v w

-- Source/core/bridge triage:
-- * source-facing: the tensor-by-bimodule functor on differential graded modules;
-- * core/canonical: the Chapter 22 DG owner `tensorWithN : DgFunctor ...`;
-- * bridge/view: the induced ordinary and homotopy-category functors
--   `tensorWithN.mapComp` and `tensorWithN.mapK`.

/-
Lemma 22.29.1 adds no new owner beyond Lemma `22.26.5`: once the tensor-by-bimodule construction
has been formalized as a DG functor, the induced functors on closed degree-`0` morphisms and on
the homotopy category are exactly the canonical DG-category owners `DgFunctor.mapComp` and
`DgFunctor.mapK`. The faithful refinement is therefore to recall those owners directly, and then
check their specialization to the tensor functor.
-/
recall DgFunctor.mapComp
recall DgFunctor.mapK

section

variable {R : Type u} [CommRing R]
variable {ModdgA : Type v} {ModdgB : Type w}
variable [DA : DifferentialGradedCategory R ModdgA]
variable [DB : DifferentialGradedCategory R ModdgB]
variable (tensorWithN : DgFunctor R ModdgA ModdgB)
variable (M : Comp R ModdgA) {M' : Comp R ModdgA} (f : M ⟶ M')
variable (X : K R ModdgA)

/- Lemma 22.29.1: let `R` be a ring, let `(A, d)` and `(B, d)` be differential graded algebras
over `R`, and let `N` be a differential graded `(A, B)`-bimodule. Once the tensor-by-bimodule
construction is formalized as a DG functor
`tensorWithN : Mod^{dg}_{(A, d)} ⥤ Mod^{dg}_{(B, d)}`,
the induced functor on the underlying category of closed degree-`0` morphisms is
`tensorWithN.mapComp`, and the induced functor on the homotopy category is
`tensorWithN.mapK`, exactly as in Lemma `22.26.5`. We also expose the objectwise and morphismwise
surfaces reused later in Chapter `22`. -/
#check tensorWithN
#check (tensorWithN.mapComp : Comp R ModdgA ⥤ Comp R ModdgB)
#check ((tensorWithN.mapComp).obj M : Comp R ModdgB)
#check DgFunctor.mapComp_obj tensorWithN M
#check (tensorWithN.mapK : K R ModdgA ⥤ K R ModdgB)
#check ((tensorWithN.mapK).obj X : K R ModdgB)
#check DgFunctor.mapK_obj tensorWithN X

/- Companion recall: the induced action on homotopy classes is the canonical one obtained by first
applying `tensorWithN.mapComp` to a closed degree-`0` morphism and then passing to `K`. -/
#check ((tensorWithN.mapComp).map f :
    (tensorWithN.mapComp).obj M ⟶ (tensorWithN.mapComp).obj M')
#check DgFunctor.mapK_map_inK tensorWithN f

end
