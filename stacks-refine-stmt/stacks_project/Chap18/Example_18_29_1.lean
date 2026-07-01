import Mathlib
import stacks_project.Chap18.Lemma_18_19_2

-- Declarations for this item will be appended below by the statement pipeline.

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
