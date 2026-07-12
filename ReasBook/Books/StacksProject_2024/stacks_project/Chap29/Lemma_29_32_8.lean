import Mathlib
import StacksProject_2024.Chap29.Definition_29_32_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X X' S S' : Scheme.{u}}
variable (f : X' ⟶ X) (g : S' ⟶ S) (h : X ⟶ S) (h' : X' ⟶ S')

-- Semantic recall: `lean_leansearch` surfaced the Kähler-differential functoriality API, and
-- local Chapter 29 precedent fixes the source-facing scheme owners as `Ω[h.toShHom]` and
-- `d[h.toShHom]`. The item is stated directly as the unique comparison morphism characterized
-- by the local-section formula, avoiding a choice-based public definition of the canonical map.

/-- Lemma 29.32.8: for a commutative square of schemes, there is a unique
`\mathcal O_{X'}`-module morphism
`c_f : f^* \Omega_{X/S} \to \Omega_{X'/S'}`
whose adjoint sends `d_{X/S}(t)` to `d_{X'/S'}(f^\sharp t)` on every local section `t` of
`\mathcal O_X`. -/
@[stacks 01UV]
theorem existsUnique_schemePullbackDifferentialsComparison
    (sq : CommSq f h' h g) :
    ∃! τ : (RingedSpace.Hom.pullback f.toShHom).obj Ω[h.toShHom] ⟶ Ω[h'.toShHom],
      ∀ {U : (Opens X)ᵒᵖ} (t : X.presheaf.obj U),
        let U' := (Opens.map f.base).op.obj U
        let φf := f.toRingCatSheafHom
        let fSharpU := φf.hom.app U
        ((((SheafOfModules.pullbackPushforwardAdjunction
              φf).homEquiv _ _)
            τ).val.app U)
          (((d[h.toShHom]).app U).d t) =
          ((d[h'.toShHom]).app U').d (fSharpU t) := sorry

end AlgebraicGeometry
