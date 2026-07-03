import Mathlib
import StacksProject_2024.Chap18.Example_18_29_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat}

/- Domain-style sampling for Lemma 18.29.2:
- primary domain: uniqueness of left duals for modules on a ringed site, expressed through the
  canonical internal-Hom dual from Example 18.29.1;
- inspected owner declarations:
  `ringedSiteModuleCategory`,
  `IsLocallyDirectSummandOfFiniteFree`,
  `ringedSiteModuleDual`,
  `CategoryTheory.ExactPairing`,
  `CategoryTheory.ExactPairing.evaluation`,
  `MonoidalClosed.curry`,
  `CategoryTheory.tensorLeftAdjunction`,
  `CategoryTheory.ihom.adjunction`,
  `CategoryTheory.Adjunction.rightAdjointUniq`;
- best owner abstraction: `ExactPairing 𝒢 ℱ`, with `𝒢` the left dual and `ℱ` the underlying
  module; the source-facing bridge to the canonical internal-Hom dual `ringedSiteModuleDual ℱ` is
  the curried evaluation morphism `MonoidalClosed.curry (ExactPairing.evaluation 𝒢 ℱ)`, obtained
  from the canonical uniqueness isomorphism between the two right adjoints `tensorLeft 𝒢` and
  `ihom ℱ` of `tensorLeft ℱ`;
- primitive data: a chosen left dual pairing `[ExactPairing 𝒢 ℱ]`;
- derived API: the local direct-summand property, the `IsIso` statement for the canonical
  comparison morphism, and the uncurrying formula recovering the evaluation pairing.

Source/core/bridge triage:
- `source-facing`: the textbook map from a chosen left dual to the internal-Hom dual and the local
  direct-summand consequence;
- `core/canonical`: `ExactPairing 𝒢 ℱ` and the owner declarations imported from
  Example 18.29.1;
- `bridge/view`: the currying/uncurrying comparison between the evaluation pairing
  `ℱ ⊗ 𝒢 ⟶ 𝟙` and the canonical morphism `𝒢 ⟶ ringedSiteModuleDual ℱ`.

This file therefore reuses the Example 18.29.1 owners directly instead of repeating the local
direct-summand predicate or the internal-Hom dual under parallel local names.
-/

section LeftDualComparison

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

section LocalDirectSummand

variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]

-- Proof sketch: mimic the ringed-space argument locally on the slice site `(C/U, \mathcal O_U)`.
-- The coevaluation section becomes a finite sum after passing to a covering, which factors the
-- identity of `ℱ|_{U_i}` through a finite free module and hence exhibits a local retract.
/-- Lemma 18.29.2 (1): if `𝒢` is a left dual of `ℱ` in the monoidal category of
`\mathcal O`-modules on a ringed site, then `ℱ` is locally a direct summand of a finite free
`\mathcal O`-module. -/
theorem leftDual_isLocallyDirectSummandOfFiniteFree
    {ℱ 𝒢 : ringedSiteModuleCategory J 𝒪} [ExactPairing 𝒢 ℱ] :
    IsLocallyDirectSummandOfFiniteFree ℱ := sorry

end LocalDirectSummand

section ClosedDuality

variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]
variable (ℱ 𝒢 : ringedSiteModuleCategory J 𝒪) [ExactPairing 𝒢 ℱ]

/-- The canonical morphism from a left dual `𝒢` of `ℱ` to the internal-Hom dual
`\mathcal H\!\mathit{om}_\mathcal O(\mathcal F, \mathcal O)`, obtained by currying the
evaluation pairing. This is the inverse of the textbook map `e`. -/
noncomputable def leftDualToRingedSiteModuleDual :
    𝒢 ⟶ ringedSiteModuleDual ℱ :=
  MonoidalClosed.curry (ExactPairing.evaluation 𝒢 ℱ)

-- Proof sketch: `leftDualToRingedSiteModuleDual ℱ 𝒢` was defined by currying the evaluation
-- pairing, so uncurrying it recovers the original evaluation map.
/-- Lemma 18.29.2 (3): uncurrying the canonical map
`𝒢 \to \mathcal H\!\mathit{om}_\mathcal O(\mathcal F, \mathcal O)` recovers the evaluation
pairing `\mathcal F \otimes \mathcal G \to \mathcal O`. -/
theorem uncurry_leftDualToRingedSiteModuleDual :
    MonoidalClosed.uncurry (leftDualToRingedSiteModuleDual ℱ 𝒢) =
      ExactPairing.evaluation 𝒢 ℱ := by
  simp [leftDualToRingedSiteModuleDual]

-- Proof sketch: `tensorLeft ℱ` has two right adjoints, namely `tensorLeft 𝒢` from the exact
-- pairing and `ihom ℱ` from the closed structure. The uniqueness isomorphism between those right
-- adjoints, evaluated at the tensor unit, is exactly `leftDualToRingedSiteModuleDual ℱ 𝒢`.

/-- Lemma 18.29.2 (2): the canonical map
`𝒢 \to \mathcal H\!\mathit{om}_\mathcal O(\mathcal F, \mathcal O)` is an isomorphism;
equivalently, the textbook map `e : \mathcal H\!\mathit{om}_\mathcal O(\mathcal F, \mathcal O)
\to 𝒢` is an isomorphism. -/
theorem isIso_leftDualToRingedSiteModuleDual :
    IsIso (leftDualToRingedSiteModuleDual ℱ 𝒢) := by
  let e : tensorLeft 𝒢 ≅ ihom ℱ :=
    Adjunction.rightAdjointUniq (tensorLeftAdjunction 𝒢 ℱ) (ihom.adjunction ℱ)
  have hCounit :
      ℱ ◁ e.hom.app (𝟙_ (ringedSiteModuleCategory J 𝒪)) ≫
        (ihom.ev ℱ).app (𝟙_ (ringedSiteModuleCategory J 𝒪)) =
        (tensorLeftAdjunction 𝒢 ℱ).counit.app (𝟙_ (ringedSiteModuleCategory J 𝒪)) := by
    simpa [e] using
      (Adjunction.rightAdjointUniq_hom_app_counit
        (tensorLeftAdjunction 𝒢 ℱ) (ihom.adjunction ℱ)
        (𝟙_ (ringedSiteModuleCategory J 𝒪)))
  have hUncurry :
      MonoidalClosed.uncurry
          ((ρ_ 𝒢).inv ≫ e.hom.app (𝟙_ (ringedSiteModuleCategory J 𝒪))) =
        ExactPairing.evaluation 𝒢 ℱ := by
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_eq]
    calc
      ℱ ◁ (ρ_ 𝒢).inv ≫
          ℱ ◁ e.hom.app (𝟙_ (ringedSiteModuleCategory J 𝒪)) ≫
            (ihom.ev ℱ).app (𝟙_ (ringedSiteModuleCategory J 𝒪)) =
        ℱ ◁ (ρ_ 𝒢).inv ≫
          (tensorLeftAdjunction 𝒢 ℱ).counit.app
            (𝟙_ (ringedSiteModuleCategory J 𝒪)) := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ ℱ ◁ (ρ_ 𝒢).inv ≫ k) hCounit
      _ = ExactPairing.evaluation 𝒢 ℱ := by
        change
          ℱ ◁ (ρ_ 𝒢).inv ≫
            (ℱ ◁ (𝟙 (𝒢 ⊗ 𝟙_ (ringedSiteModuleCategory J 𝒪))) ≫
              (α_ ℱ 𝒢 (𝟙_ (ringedSiteModuleCategory J 𝒪))).inv ≫
                ExactPairing.evaluation 𝒢 ℱ ▷
                  (𝟙_ (ringedSiteModuleCategory J 𝒪)) ≫
                    (λ_ (𝟙_ (ringedSiteModuleCategory J 𝒪))).hom) =
            ExactPairing.evaluation 𝒢 ℱ
        simp
        have hUnitors :
            (ρ_ (𝟙_ (ringedSiteModuleCategory J 𝒪))).inv =
              (λ_ (𝟙_ (ringedSiteModuleCategory J 𝒪))).inv := by
          simpa using
            (show (ρ_ (𝟙_ (ringedSiteModuleCategory J 𝒪))).inv =
                (λ_ (𝟙_ (ringedSiteModuleCategory J 𝒪))).inv from
              unitors_inv_equal.symm)
        rw [hUnitors]
        simp
  have hComparison :
      (ρ_ 𝒢).inv ≫ e.hom.app (𝟙_ (ringedSiteModuleCategory J 𝒪)) =
        leftDualToRingedSiteModuleDual ℱ 𝒢 := by
    apply MonoidalClosed.uncurry_injective
    simpa [leftDualToRingedSiteModuleDual] using hUncurry
  have hIsoComparison :
      IsIso ((ρ_ 𝒢).inv ≫ e.hom.app (𝟙_ (ringedSiteModuleCategory J 𝒪))) := by
    let _ : IsIso (e.hom.app (𝟙_ (ringedSiteModuleCategory J 𝒪))) := by
      infer_instance
    refine ⟨⟨inv (e.hom.app (𝟙_ (ringedSiteModuleCategory J 𝒪))) ≫ (ρ_ 𝒢).hom, ?_, ?_⟩⟩ <;>
      simp
  simpa [hComparison] using hIsoComparison
end ClosedDuality

end LeftDualComparison
end SheafOfModules.RingedSite
