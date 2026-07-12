import Mathlib
import StacksProject_2024.Chap29.Lemma_29_32_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}}

-- Semantic search note: `lean_leansearch` was unavailable in this tool session; local Chapter 29
-- precedent fixes the scheme-level differential sheaves as `Ω[f.toShHom]`, and Lemma 29.32.9
-- supplies the source-facing transitivity maps by their universal-derivation formulas.

/-- Helper for Lemma 29.34.16: the left map in the transitivity sequence is characterized by
sending `d_{Y/S}(t)` to `d_{X/S}(f^\sharp t)` after the pullback-pushforward adjunction. -/
private def leftRelativeDifferentialsTransitivityMapSpec
    (f : X ⟶ Y) (g : Y ⟶ S)
    (φ : (RingedSpace.Hom.pullback f.toShHom).obj Ω[g.toShHom] ⟶ Ω[(f ≫ g).toShHom]) :
    Prop :=
  ∀ {U : (Opens Y)ᵒᵖ} (t : Y.presheaf.obj U),
    let U' := (Opens.map f.base).op.obj U
    let φf := f.toRingCatSheafHom
    let fSharpU := φf.hom.app U
    ((((SheafOfModules.pullbackPushforwardAdjunction
          φf).homEquiv _ _)
        φ).val.app U)
      (((d[g.toShHom]).app U).d t) =
      ((d[(f ≫ g).toShHom]).app U').d (fSharpU t)

/-- Helper for Lemma 29.34.16: the right map in the transitivity sequence is characterized by
sending `d_{X/S}(t)` to `d_{X/Y}(t)` on local sections. -/
private def rightRelativeDifferentialsTransitivityMapSpec
    (f : X ⟶ Y) (g : Y ⟶ S)
    (ψ : Ω[(f ≫ g).toShHom] ⟶ Ω[f.toShHom]) : Prop :=
  ∀ {U : (Opens X)ᵒᵖ} (t : X.presheaf.obj U),
    ψ.val.app U (((d[(f ≫ g).toShHom]).app U).d t) =
      ((d[f.toShHom]).app U).d t

/-- Helper for Lemma 29.34.16: the two comparison maps satisfy the source-facing formulas
of the transitivity sequence from Lemma 29.32.9. -/
private def relativeDifferentialsTransitivityMapSpecs
    (f : X ⟶ Y) (g : Y ⟶ S)
    (φ : (RingedSpace.Hom.pullback f.toShHom).obj Ω[g.toShHom] ⟶ Ω[(f ≫ g).toShHom])
    (ψ : Ω[(f ≫ g).toShHom] ⟶ Ω[f.toShHom]) : Prop :=
  leftRelativeDifferentialsTransitivityMapSpec f g φ ∧
    rightRelativeDifferentialsTransitivityMapSpec f g ψ

/-- Lemma 29.34.16: let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes. If `f` is smooth,
then the transitivity sequence
`0 ⟶ f^* Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0`
from Lemma 29.32.9 is short exact. -/
@[stacks 02K4]
theorem exists_shortExact_relativeDifferentialsTransitivitySequence_of_smooth
    (f : X ⟶ Y) (g : Y ⟶ S) (hf : Smooth f) :
    ∃ φ : (RingedSpace.Hom.pullback f.toShHom).obj Ω[g.toShHom] ⟶ Ω[(f ≫ g).toShHom],
      ∃ ψ : Ω[(f ≫ g).toShHom] ⟶ Ω[f.toShHom],
        relativeDifferentialsTransitivityMapSpecs f g φ ψ ∧
          ∃ hφψ : φ ≫ ψ = 0, (ShortComplex.mk φ ψ hφψ).ShortExact := sorry

end AlgebraicGeometry
