import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_32_8

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X X' S S' : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced the ring-level base-change theorem
-- `KaehlerDifferential.isBaseChange`; local Section 29.32 precedent represents the scheme-level
-- comparison map by the unique local-section characterization of Lemma 29.32.8.

/-- Lemma 29.32.10: for a base-change square of schemes, the morphism
`(g')^* Ω_{X/S} ⟶ Ω_{X'/S'}` characterized in Lemma 29.32.8 is an isomorphism. -/
@[stacks 01V0]
theorem isIso_schemePullbackDifferentialsComparison_of_isPullback
    (f : X ⟶ S) (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hpb : IsPullback g' f' f g)
    (τ : (RingedSpace.Hom.pullback g'.toShHom).obj Ω[f.toShHom] ⟶ Ω[f'.toShHom])
    (hτ :
      ∀ {U : (Opens X)ᵒᵖ} (t : X.presheaf.obj U),
        let U' := (Opens.map g'.base).op.obj U
        let φg' := g'.toRingCatSheafHom
        let g'SharpU := φg'.hom.app U
        ((((SheafOfModules.pullbackPushforwardAdjunction
              φg').homEquiv _ _)
            τ).val.app U)
          (((d[f.toShHom]).app U).d t) =
          ((d[f'.toShHom]).app U').d (g'SharpU t)) :
    IsIso τ := sorry

end AlgebraicGeometry
