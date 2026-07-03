import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_18_29_1 (from Chap18) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat}

/- Domain-style sampling for Example 18.29.1:
- primary domain: duality for sheaves of modules on a ringed site, expressed through the canonical
  tensor/internal-Hom comparison and the resulting left-duality datum;
- inspected owner declarations:
  `ringedSiteModuleCategory`,
  `ihom.ev`,
  `MonoidalClosed.uncurry`,
  `CategoryTheory.Retract`,
  `CategoryTheory.ExactPairing`,
  `CategoryTheory.BraidedCategory.exactPairing_swap`;
- best owner abstraction: the ambient owner is `ringedSiteModuleCategory J 𝒪`, the source-facing
  local hypothesis is the local retract owner below, the tensor-to-endomorphism comparison is
  induced directly by the closed-structure evaluation, and the left-duality datum is the braided
  bridge packaged by `ExactPairing (ringedSiteModuleDual ℱ) ℱ`;
- primitive data: a module `ℱ : ringedSiteModuleCategory J 𝒪`, the local retract condition on
  iterated slice sites, and the canonical internal-Hom object `(ihom ℱ).obj (𝟙_ _)`;
- derived API: the source-facing explicit split-map reformulation, the tensor-to-endomorphism
  comparison, its isomorphism statement, and the induced exact pairing.

Source/core/bridge triage:
- `source-facing`: the local direct-summand hypothesis and the textbook tensor-to-endomorphism
  statement;
- `core/canonical`: `ringedSiteModuleCategory J 𝒪`, `Retract`, `ihom`, and `ExactPairing`;
- `bridge/view`: the explicit split-map companion theorem and the exact pairing obtained by
  swapping the canonical right-dual-style pairing.

The local direct-summand owner therefore uses `Retract` as primitive data, matching the chapter 17
owner style, while the explicit maps `ι` and `π` remain a companion view rather than the main
public owner.
-/

/-- The underlying `RingCat`-valued structure sheaf of the ringed site `(\mathcal C, \mathcal O)`,
used internally for iterated localizations. -/
private abbrev ringedSiteStructureSheaf : Sheaf J RingCat :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪

/-- The category of `\mathcal O_V`-modules on the iterated localization `((C/U)/V, \mathcal O_V)`.
-/
private abbrev iteratedLocalizedRingedSiteModules {U : C} (V : Over U) :=
  SheafOfModules (((@ringedSiteStructureSheaf C _ J _ 𝒪).over U).over V)

/-- A ringed-site module is locally a direct summand of a finite free module if, after passing to a
covering of every object `U`, each restriction `\mathcal F|_{U_i}` is a retract of a finite free
`\mathcal O_{U_i}`-module. -/
class IsLocallyDirectSummandOfFiniteFree (ℱ : ringedSiteModuleCategory J 𝒪) : Prop where
  /-- Every object admits a covering on which the restriction of `ℱ` is a retract of a finite free
  module. -/
  exists_cover_retract_free (U : C) :
    ∃ (I : Type (max u v)) (Ui : I → Over U), (J.over U).CoversTop Ui ∧
      ∀ i : I,
        ∃ α : Type (max u v), Finite α ∧
          Nonempty
            (Retract
              ((ℱ.over U).over (Ui i))
              (SheafOfModules.free α : iteratedLocalizedRingedSiteModules (Ui i)))

-- Proof sketch: unpack each local retract into its inclusion and retraction maps, and conversely
-- package explicit split morphisms into `Retract`.
/-- Unfolding `IsLocallyDirectSummandOfFiniteFree` gives the explicit local split-map data on each
localized ringed site. -/
theorem isLocallyDirectSummandOfFiniteFree_iff
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsLocallyDirectSummandOfFiniteFree ℱ ↔
      ∀ U : C,
        ∃ (I : Type (max u v)) (Ui : I → Over U), (J.over U).CoversTop Ui ∧
          ∀ i : I,
            ∃ α : Type (max u v), Finite α ∧
              ∃ ι :
                  (ℱ.over U).over (Ui i) ⟶
                    (SheafOfModules.free α :
                      iteratedLocalizedRingedSiteModules (Ui i)),
                ∃ π :
                    (SheafOfModules.free α : iteratedLocalizedRingedSiteModules (Ui i)) ⟶
                      (ℱ.over U).over (Ui i),
                  ι ≫ π = 𝟙 ((ℱ.over U).over (Ui i)) := sorry

section Duality

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]

/-- The internal-Hom dual `\mathcal H\!om_\mathcal O(\mathcal F, \mathcal O)` of an
`\mathcal O`-module on a ringed site. -/
abbrev ringedSiteModuleDual (ℱ : ringedSiteModuleCategory J 𝒪) :=
  (ihom ℱ).obj (𝟙_ (ringedSiteModuleCategory J 𝒪))

/-- The canonical tensor-to-endomorphism morphism
`\mathcal F \otimes_\mathcal O \mathcal H\!om_\mathcal O(\mathcal F, \mathcal O) \to
\mathcal H\!om_\mathcal O(\mathcal F, \mathcal F)`. -/
noncomputable def ringedSiteModuleDualTensorToEnd (ℱ : ringedSiteModuleCategory J 𝒪) :
    ℱ ⊗ ringedSiteModuleDual ℱ ⟶ (ihom ℱ).obj ℱ :=
  MonoidalClosed.curry
    ((ℱ ◁ MonoidalClosed.uncurry (𝟙 (ringedSiteModuleDual ℱ))) ≫
      (ρ_ ℱ).hom)

section IsLocallyDirectSummandOfFiniteFree

variable {ℱ : ringedSiteModuleCategory J 𝒪}

-- Proof sketch: the statement is local on the ringed site. On a cover where `ℱ` is a retract of a
-- finite free module, the comparison is an isomorphism for the finite free module and hence also
-- for its retract; then descend the local isomorphisms.
/-- Example 18.29.1: if every local restriction of `\mathcal F` becomes a direct summand of a
finite free module on a covering, then the canonical map
`\mathcal F \otimes_\mathcal O \mathcal H\!om_\mathcal O(\mathcal F, \mathcal O) \to
\mathcal H\!om_\mathcal O(\mathcal F, \mathcal F)` is an isomorphism. -/
theorem ringedSiteModuleDualTensorToEnd_isIso_of_locallyDirectSummandOfFiniteFree
    [IsLocallyDirectSummandOfFiniteFree ℱ] :
    IsIso (ringedSiteModuleDualTensorToEnd ℱ) := sorry

/-- The coevaluation morphism
`\eta : \mathcal O \to \mathcal F \otimes_\mathcal O \mathcal H\!om_\mathcal O(\mathcal F,
\mathcal O)` obtained by transporting the identity endomorphism of `\mathcal F` across the
canonical tensor-to-endomorphism isomorphism. -/
private noncomputable def ringedSiteModuleDualCoevaluation
    [IsIso (ringedSiteModuleDualTensorToEnd ℱ)] :
    𝟙_ (ringedSiteModuleCategory J 𝒪) ⟶ ℱ ⊗ ringedSiteModuleDual ℱ :=
  MonoidalClosed.curry' (𝟙 ℱ) ≫
    inv (ringedSiteModuleDualTensorToEnd ℱ)

section ExactPairingBridge

variable [BraidedCategory (ringedSiteModuleCategory J 𝒪)]

/-- The braided transpose of the canonical closed-structure evaluation, used only to build the
exact-pairing bridge from the tensor-to-endomorphism isomorphism. -/
private abbrev ringedSiteModuleDualEvaluation (ℱ : ringedSiteModuleCategory J 𝒪) :
    ringedSiteModuleDual ℱ ⊗ ℱ ⟶ 𝟙_ (ringedSiteModuleCategory J 𝒪) :=
  (β_ _ _).hom ≫ MonoidalClosed.uncurry (𝟙 (ringedSiteModuleDual ℱ))

-- Proof sketch: after applying the tensor-to-endomorphism isomorphism, the first triangle
-- identity becomes the statement that the coevaluation corresponds to the identity of the dual.
private theorem ringedSiteModuleDual_coevaluation_evaluation
    [IsIso (ringedSiteModuleDualTensorToEnd ℱ)] :
    ringedSiteModuleDual ℱ ◁ ringedSiteModuleDualCoevaluation ≫
        (α_ _ _ _).inv ≫
        ringedSiteModuleDualEvaluation ℱ ▷ ringedSiteModuleDual ℱ =
      (ρ_ (ringedSiteModuleDual ℱ)).hom ≫
        (λ_ (ringedSiteModuleDual ℱ)).inv := sorry

-- Proof sketch: transporting the identity of `ℱ` across the same tensor-to-endomorphism
-- isomorphism yields the second triangle identity.
private theorem ringedSiteModuleDual_evaluation_coevaluation
    [IsIso (ringedSiteModuleDualTensorToEnd ℱ)] :
    ringedSiteModuleDualCoevaluation ▷ ℱ ≫
        (α_ _ _ _).hom ≫
        ℱ ◁ ringedSiteModuleDualEvaluation ℱ =
      (λ_ ℱ).hom ≫ (ρ_ ℱ).inv := sorry

@[reducible] private noncomputable def ringedSiteModuleDualExactPairingOfIsIso
    [IsIso (ringedSiteModuleDualTensorToEnd ℱ)] :
    ExactPairing (ringedSiteModuleDual ℱ) ℱ :=
  letI : ExactPairing ℱ (ringedSiteModuleDual ℱ) :=
    { coevaluation' := ringedSiteModuleDualCoevaluation
      evaluation' := ringedSiteModuleDualEvaluation ℱ
      coevaluation_evaluation' := ringedSiteModuleDual_coevaluation_evaluation
      evaluation_coevaluation' := ringedSiteModuleDual_evaluation_coevaluation }
  BraidedCategory.exactPairing_swap _ _

/-- Example 18.29.1 also yields that
`\mathcal H\!om_\mathcal O(\mathcal F, \mathcal O)` is a left dual of `\mathcal F`. In Lean this
left-duality datum is packaged by `CategoryTheory.ExactPairing`. -/
noncomputable instance ringedSiteModuleDual_exactPairing
    [IsLocallyDirectSummandOfFiniteFree ℱ] :
    ExactPairing (ringedSiteModuleDual ℱ) ℱ :=
  letI : IsIso (ringedSiteModuleDualTensorToEnd ℱ) :=
    ringedSiteModuleDualTensorToEnd_isIso_of_locallyDirectSummandOfFiniteFree
  ringedSiteModuleDualExactPairingOfIsIso

end ExactPairingBridge
end IsLocallyDirectSummandOfFiniteFree
end Duality

end SheafOfModules.RingedSite

/-! ### Lemma_18_29_2 (from Chap18) -/
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

/-! ### Lemma_18_29_3 (from Chap18) -/
open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat}

/- Domain-style sampling for Lemma 18.29.3:
- primary domain: finitely presented flat sheaves of modules on a ringed site and their local
  finite-free splitting behavior on iterated slice sites;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.RingedSite.IsFinitePresentation`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.free`;
- best owner abstraction: the chapter owner `ringedSiteModuleCategory J 𝒪`, with the source
  hypotheses carried by the ringed-site owners `IsFinitePresentation` and `IsFlat`;
- primitive data: a module `ℱ : ringedSiteModuleCategory J 𝒪`, the localized restrictions
  `ℱ.over U` and `((ℱ.over U).over V)`, and finite free modules on the iterated localized site
  `((J.over U).over V, ((𝒪.over U).over V))`;
- derived API: the local split inclusion/retraction maps exhibiting each iterated restriction as a
  direct summand of a finite free module.

Source/core/bridge triage:
- `source-facing`: the local direct-summand criterion for finitely presented flat modules on a
  ringed site;
- `core/canonical`: `ringedSiteModuleCategory J 𝒪`,
  `SheafOfModules.RingedSite.IsFinitePresentation`,
  `SheafOfModules.RingedSite.IsFlat`, and `SheafOfModules.free`;
- `bridge/view`: the explicit split maps on the iterated slice sites.

The chapter owner for the local direct-summand condition is already
`IsLocallyDirectSummandOfFiniteFree` from Example `18.29.1`, with
`isLocallyDirectSummandOfFiniteFree_iff` as its explicit split-map companion. This file therefore
keeps the owner theorem primary and derives the textbook split-map form from that owner instead of
maintaining a parallel coordinate-level public API.
-/

-- Proof sketch: finite presentation is local on the ringed site, so after restricting to each
-- object `U` and refining by a cover one obtains a finite global presentation of `ℱ.over U`.
-- Apply the local factorization criterion for flat modules to the relation morphism and the
-- resulting surjection; after refining once more, the surjection factors through a finite free
-- module with zero composite from the relations, so the induced surjection admits a section and
-- `ℱ` becomes locally a direct summand of a finite free module.
/-- Lemma 18.29.3: a finitely presented flat `\mathcal O`-module on a ringed site is locally a
direct summand of a finite free module. -/
theorem isLocallyDirectSummandOfFiniteFree_of_isFinitePresentation_of_flat
    (ℱ : ringedSiteModuleCategory J 𝒪)
    [ℱ.IsFinitePresentation] [IsFlat 𝒪 ℱ] :
    IsLocallyDirectSummandOfFiniteFree ℱ := sorry

-- Proof sketch: apply the owner theorem above and then unpack the owner through
-- `isLocallyDirectSummandOfFiniteFree_iff`.
/-- Unfolding Lemma 18.29.3 recovers the explicit local split-map data on a covering of each
object. -/
theorem exists_cover_directSummandOfFiniteFree_of_isFinitePresentation_of_flat
    (ℱ : ringedSiteModuleCategory J 𝒪)
    [ℱ.IsFinitePresentation] [IsFlat 𝒪 ℱ]
    (U : C) :
    ∃ (I : Type (max u v)) (Ui : I → Over U), (J.over U).CoversTop Ui ∧
      ∀ i : I,
        ∃ (α : Type (max u v)) (_ : Finite α),
          ∃ ι :
              (ℱ.over U).over (Ui i) ⟶
                (SheafOfModules.free α :
                  ringedSiteModuleCategory ((J.over U).over (Ui i))
                    ((𝒪.over U).over (Ui i))),
            ∃ π :
                (SheafOfModules.free α :
                  ringedSiteModuleCategory ((J.over U).over (Ui i))
                    ((𝒪.over U).over (Ui i))) ⟶
                  (ℱ.over U).over (Ui i),
              ι ≫ π = 𝟙 ((ℱ.over U).over (Ui i)) := by
  letI : IsLocallyDirectSummandOfFiniteFree ℱ :=
    isLocallyDirectSummandOfFiniteFree_of_isFinitePresentation_of_flat ℱ
  rcases (isLocallyDirectSummandOfFiniteFree_iff ℱ).mp inferInstance U with
    ⟨I, Ui, hUi, hsplit⟩
  refine ⟨I, Ui, hUi, ?_⟩
  intro i
  rcases hsplit i with ⟨α, hα, ι, π, hπ⟩
  exact ⟨α, hα, ι, π, hπ⟩

end SheafOfModules.RingedSite
