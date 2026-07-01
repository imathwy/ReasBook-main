import Mathlib
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import stacks_project.Chap17.Definition_17_14_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "𝒪X" => 𝟙_ ModX

variable (ℱ 𝒢 : ModX)
variable [MonoidalCategory (RingedSpace.Modules X)]

/- Domain-style sampling for Lemma 17.18.2:
- primary domain: duality for `\mathcal O_X`-modules, expressed by a chosen left-dual pairing and
  the resulting comparison with the internal Hom into the structure sheaf;
- inspected owner declarations:
  `CategoryTheory.ExactPairing`,
  `CategoryTheory.ExactPairing.evaluation`,
  notation `ε_`,
  `CategoryTheory.MonoidalClosed.curry`,
  `CategoryTheory.Adjunction.rightAdjointUniq`,
  `CategoryTheory.MonoidalClosed.uncurry`,
  notation `A ⟶[C] B`;
- best owner abstraction: the duality datum is owned by `ExactPairing 𝒢 ℱ`, while the comparison
  with `\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal O_X)` is the canonical bridge
  `MonoidalClosed.curry (ExactPairing.evaluation 𝒢 ℱ)`, written on the theorem surface as
  `MonoidalClosed.curry (ε_ 𝒢 ℱ) : 𝒢 ⟶ ℱ ⟶[ModX] 𝒪X`;
- primitive data: a chosen monoidal structure on `ModX`, a chosen closed structure when internal
  Hom is used, and an exact pairing `ExactPairing 𝒢 ℱ`;
- derived API: the local direct-summand consequence and the curried/uncurried comparison with
  `ℱ ⟶[ModX] 𝒪X`.

Source/core/bridge triage:
- `source-facing`: the local direct-summand conclusion for a left dual and the textbook
  comparison with `\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal O_X)`;
- `core/canonical`: `ExactPairing 𝒢 ℱ`, `ε_`, `MonoidalClosed.curry`, `MonoidalClosed.uncurry`,
  and `ℱ ⟶[ModX] 𝒪X`;
- `bridge/view`: the specific morphism
  `MonoidalClosed.curry (ε_ 𝒢 ℱ) : 𝒢 ⟶ ℱ ⟶[ModX] 𝒪X`.
-/

-- Proof sketch: on an open neighbourhood of each point, write the coevaluation section as a finite
-- sum `∑ fᵢ ⊗ gᵢ`; the induced map from a finite free sheaf to `ℱ` then factors the identity via
-- the triangle identity, exhibiting `ℱ` locally as a retract of a finite free module sheaf.
/-- Lemma 17.18.2: if `𝒢` is a left dual of `ℱ` in the monoidal category of
`\mathcal O_X`-modules, then `ℱ` is locally a direct summand of a finite free
`\mathcal O_X`-module. -/
theorem exactPairing_locallyDirectSummandOfFiniteFree
    [ExactPairing 𝒢 ℱ] :
    ℱ.IsLocallyDirectSummandOfFiniteFree := sorry

variable [MonoidalClosed (RingedSpace.Modules X)]

/-- Companion: uncurrying the canonical curried evaluation morphism recovers the evaluation
pairing. -/
theorem uncurry_curry_exactPairingEvaluation
    (ℱ 𝒢 : ModX) [ExactPairing 𝒢 ℱ] :
    MonoidalClosed.uncurry (MonoidalClosed.curry (ε_ 𝒢 ℱ)) = ε_ 𝒢 ℱ := by
  simp

private noncomputable def leftDualIhomIso
    (ℱ 𝒢 : ModX) [ExactPairing 𝒢 ℱ] :
    tensorLeft 𝒢 ≅ ihom ℱ :=
  Adjunction.rightAdjointUniq (tensorLeftAdjunction 𝒢 ℱ) (ihom.adjunction ℱ)

private theorem curry_exactPairingEvaluation_eq_rightAdjointUniqHom
    (ℱ 𝒢 : ModX) [ExactPairing 𝒢 ℱ] :
    MonoidalClosed.curry (ε_ 𝒢 ℱ) = (ρ_ 𝒢).inv ≫ (leftDualIhomIso ℱ 𝒢).hom.app 𝒪X := by
  let e : tensorLeft 𝒢 ≅ ihom ℱ := leftDualIhomIso ℱ 𝒢
  have hCounit :
      ℱ ◁ e.hom.app 𝒪X ≫ (ihom.ev ℱ).app 𝒪X =
        (tensorLeftAdjunction 𝒢 ℱ).counit.app 𝒪X := by
    simpa [leftDualIhomIso, e] using
      (Adjunction.rightAdjointUniq_hom_app_counit
        (tensorLeftAdjunction 𝒢 ℱ) (ihom.adjunction ℱ) 𝒪X)
  have hUncurry :
      MonoidalClosed.uncurry ((ρ_ 𝒢).inv ≫ e.hom.app 𝒪X) =
        ε_ 𝒢 ℱ := by
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_eq]
    calc
      ℱ ◁ (ρ_ 𝒢).inv ≫ ℱ ◁ e.hom.app 𝒪X ≫ (ihom.ev ℱ).app 𝒪X =
          ℱ ◁ (ρ_ 𝒢).inv ≫ (tensorLeftAdjunction 𝒢 ℱ).counit.app 𝒪X := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ ℱ ◁ (ρ_ 𝒢).inv ≫ k) hCounit
      _ = ε_ 𝒢 ℱ := by
        change
          ℱ ◁ (ρ_ 𝒢).inv ≫
              (ℱ ◁ (𝟙 (𝒢 ⊗ 𝒪X)) ≫
                (α_ ℱ 𝒢 𝒪X).inv ≫
                  ε_ 𝒢 ℱ ▷ 𝒪X ≫
                    (λ_ 𝒪X).hom) =
            ε_ 𝒢 ℱ
        simp only [whiskerLeft_rightUnitor_inv, whiskerLeft_id, whiskerRight_id, Category.assoc,
          Category.id_comp, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
        have hUnitors : (ρ_ 𝒪X).inv = (λ_ 𝒪X).inv := by
          simpa using
            (show (ρ_ 𝒪X).inv = (λ_ 𝒪X).inv from unitors_inv_equal.symm)
        rw [hUnitors]
        simp
  apply MonoidalClosed.uncurry_injective
  simpa using hUncurry.symm

/-- Lemma 17.18.2 (2): the canonical morphism
`\mathcal G \to \mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal O_X)` obtained by
currying the evaluation pairing is an isomorphism. Equivalently, its inverse is the textbook map
`e : \mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal O_X) \to \mathcal G`. -/
theorem isIso_curry_exactPairingEvaluation
    (ℱ 𝒢 : ModX) [ExactPairing 𝒢 ℱ] :
    IsIso (MonoidalClosed.curry (ε_ 𝒢 ℱ)) := by
  rw [curry_exactPairingEvaluation_eq_rightAdjointUniqHom ℱ 𝒢]
  let _ : IsIso ((leftDualIhomIso ℱ 𝒢).hom.app 𝒪X) := by
    infer_instance
  refine ⟨⟨inv ((leftDualIhomIso ℱ 𝒢).hom.app 𝒪X) ≫ (ρ_ 𝒢).hom, ?_, ?_⟩⟩ <;> simp

instance instIsIsoCurryExactPairingEvaluation
    (ℱ 𝒢 : ModX) [ExactPairing 𝒢 ℱ] :
    IsIso (MonoidalClosed.curry (ε_ 𝒢 ℱ)) :=
  isIso_curry_exactPairingEvaluation ℱ 𝒢

end AlgebraicGeometry.RingedSpace
