import Mathlib
import StacksProject_2024.Chap29.Lemma_29_32_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced the `ShortComplex` exactness/epi API, and local
-- Chapter 29 precedent records canonical comparison morphisms by the unique-existence theorem
-- `existsUnique_schemePullbackDifferentialsComparison` from Lemma 29.32.8. The source-facing
-- theorem keeps the existential comparison maps explicit, with helper predicates separating the
-- map characterizations from exactness at the final `0`.

/-- Helper for Lemma 29.32.9: the left map in the transitivity sequence is characterized by
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

/-- Helper for Lemma 29.32.9: the right map in the transitivity sequence is characterized by
sending `d_{X/S}(t)` to `d_{X/Y}(t)` on local sections. -/
private def rightRelativeDifferentialsTransitivityMapSpec
    (f : X ⟶ Y) (g : Y ⟶ S)
    (ψ : Ω[(f ≫ g).toShHom] ⟶ Ω[f.toShHom]) : Prop :=
  ∀ {U : (Opens X)ᵒᵖ} (t : X.presheaf.obj U),
    ψ.val.app U (((d[(f ≫ g).toShHom]).app U).d t) =
      ((d[f.toShHom]).app U).d t

/-- Helper for Lemma 29.32.9: the two comparison maps satisfy their source-facing
characterizing formulas. -/
private def relativeDifferentialsTransitivityMapSpecs
    (f : X ⟶ Y) (g : Y ⟶ S)
    (φ : (RingedSpace.Hom.pullback f.toShHom).obj Ω[g.toShHom] ⟶ Ω[(f ≫ g).toShHom])
    (ψ : Ω[(f ≫ g).toShHom] ⟶ Ω[f.toShHom]) : Prop :=
  leftRelativeDifferentialsTransitivityMapSpec f g φ ∧
    rightRelativeDifferentialsTransitivityMapSpec f g ψ

/-- Helper for Lemma 29.32.9: the displayed three-term complex is exact and continues to `0`. -/
private def relativeDifferentialsTransitivityExactToZero
    (f : X ⟶ Y) (g : Y ⟶ S)
    (φ : (RingedSpace.Hom.pullback f.toShHom).obj Ω[g.toShHom] ⟶ Ω[(f ≫ g).toShHom])
    (ψ : Ω[(f ≫ g).toShHom] ⟶ Ω[f.toShHom]) : Prop :=
  ∃ hφψ : φ ≫ ψ = 0, (ShortComplex.mk φ ψ hφψ).Exact ∧ Epi ψ

/-- Lemma 29.32.9: for morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ S`, the canonical
transitivity sequence
`f^* \Omega_{Y/S} \to \Omega_{X/S} \to \Omega_{X/Y} \to 0`
is exact. The two maps are the canonical comparison maps characterized by the two applications of
Lemma 29.32.8. -/
@[stacks 01UX]
theorem exists_exact_relativeDifferentialsTransitivitySequence
    (f : X ⟶ Y) (g : Y ⟶ S) :
    ∃ φ : (RingedSpace.Hom.pullback f.toShHom).obj Ω[g.toShHom] ⟶ Ω[(f ≫ g).toShHom],
      ∃ ψ : Ω[(f ≫ g).toShHom] ⟶ Ω[f.toShHom],
        relativeDifferentialsTransitivityMapSpecs f g φ ψ ∧
          relativeDifferentialsTransitivityExactToZero f g φ ψ := sorry

end AlgebraicGeometry
