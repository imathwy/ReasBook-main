import Mathlib
import stacks_project.Chap17.Definition_17_4_1
import stacks_project.Chap17.Lemma_17_18_2
import stacks_project.Chap17.Lemma_17_22_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Example 17.18.1:
- primary domain: duality for sheaves of modules on a ringed space, expressed through the
  canonical tensor/internal-Hom comparison and the resulting left-duality datum;
- inspected owner declarations:
  `SheafOfModules.IsLocallyDirectSummandOfFiniteFree`,
  `AlgebraicGeometry.RingedSpace.stalkModuleCat`,
  `CategoryTheory.ExactPairing`,
  `CategoryTheory.BraidedCategory.exactPairing_swap`,
  `CategoryTheory.ihom.ev`,
  `CategoryTheory.MonoidalClosed.curry`,
  notation `ε_`,
  `CategoryTheory.MonoidalClosed.internalHomAdjunction₂`;
- best owner abstraction: the ambient owner is `(RingedSpace.Modules X)`, with the intrinsic dual object
  given by the internal Hom into the tensor unit and the left-duality datum packaged by
  `ExactPairing`, over the braided monoidal closed structure actually used by the comparison map;
- primitive data: a sheaf `ℱ : (RingedSpace.Modules X)`, the canonical internal-Hom object
  `(ihom ℱ).obj (𝟙_ (RingedSpace.Modules X))`, and the owner predicate
  `SheafOfModules.IsLocallyDirectSummandOfFiniteFree ℱ`;
- derived API: the tensor-to-endomorphism morphism, the induced coevaluation map, the evaluation
  map reused from `ihom.ev`, and
  the resulting exact pairing.

Source/core/bridge triage:
- `source-facing`: the local direct-summand hypothesis and the textbook tensor-to-endomorphism
  statement;
- `core/canonical`: `(RingedSpace.Modules X)`, `ihom`, and `ExactPairing`;
- `bridge/view`: the canonical morphism
  `ℱ ⊗ (ihom ℱ).obj (𝟙_ (RingedSpace.Modules X)) ⟶ (ihom ℱ).obj ℱ` and the exact pairing built from its
  inverse.

This file therefore reuses the chapter owner
`SheafOfModules.IsLocallyDirectSummandOfFiniteFree` instead of repeating its local neighborhood
data. The public surface is the sheaf-level tensor/internal-Hom comparison, while the left-dual
packaging is the canonical `ExactPairing ((ihom ℱ).obj (𝟙_ (RingedSpace.Modules X))) ℱ` companion derived
from that canonical map. -/

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [BraidedCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X

/-- The canonical tensor-to-endomorphism morphism
`\mathcal F \otimes \mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal O_X) \to
\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal F)`. -/
noncomputable def unitInternalHomTensorToEnd (ℱ : ModX) :
    ℱ ⊗ (ihom ℱ).obj (𝟙_ ModX) ⟶ (ihom ℱ).obj ℱ :=
  MonoidalClosed.curry
    ((ℱ ◁ (ihom.ev ℱ).app (𝟙_ ModX)) ≫ (ρ_ ℱ).hom)

section IsLocallyDirectSummandOfFiniteFree

-- Proof sketch: the statement is local on `X`. On a neighborhood where `ℱ` is a retract of a
-- finite free module sheaf, the comparison is an isomorphism for the finite free module and hence
-- for its retract; these local isomorphisms glue to the global one.
/-- Example 17.18.1: if `\mathcal F` is locally a direct summand of a finite free
`\mathcal O_X`-module, then the canonical morphism
`\mathcal F \otimes_{\mathcal O_X} \mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F,
\mathcal O_X) \to \mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal F)` is an
isomorphism. -/
theorem isIso_unitInternalHomTensorToEnd_of_locallyDirectSummandOfFiniteFree
    (ℱ : ModX)
    [ℱ.IsLocallyDirectSummandOfFiniteFree] :
    IsIso (unitInternalHomTensorToEnd ℱ) := sorry

private noncomputable def unitInternalHomCoevaluation
    (ℱ : ModX)
    [IsIso (unitInternalHomTensorToEnd ℱ)] :
    𝟙_ ModX ⟶ ℱ ⊗ (ihom ℱ).obj (𝟙_ ModX) :=
  MonoidalClosed.curry' (𝟙 ℱ) ≫
    inv (unitInternalHomTensorToEnd ℱ)

private abbrev unitInternalHomEvaluation (ℱ : ModX) :
    ((ihom ℱ).obj (𝟙_ ModX)) ⊗ ℱ ⟶ 𝟙_ ModX :=
  (β_ _ _).hom ≫ (ihom.ev ℱ).app (𝟙_ ModX)

-- Proof sketch: after transporting through the tensor-to-endomorphism isomorphism, the composite
-- becomes the identity of the dual object, which is exactly the first triangle identity.
private theorem unitInternalHom_coevaluation_evaluation
    (ℱ : ModX)
    [IsIso (unitInternalHomTensorToEnd ℱ)] :
    ((ihom ℱ).obj (𝟙_ ModX)) ◁ unitInternalHomCoevaluation ℱ ≫
        (α_ _ _ _).inv ≫
        unitInternalHomEvaluation ℱ ▷ (ihom ℱ).obj (𝟙_ ModX) =
      (ρ_ ((ihom ℱ).obj (𝟙_ ModX))).hom ≫
        (λ_ ((ihom ℱ).obj (𝟙_ ModX))).inv := sorry

-- Proof sketch: transporting the identity of `ℱ` across the same tensor-to-endomorphism
-- isomorphism yields the second triangle identity.
private theorem unitInternalHom_evaluation_coevaluation
    (ℱ : ModX)
    [IsIso (unitInternalHomTensorToEnd ℱ)] :
    unitInternalHomCoevaluation ℱ ▷ ℱ ≫
        (α_ _ _ _).hom ≫
        ℱ ◁ unitInternalHomEvaluation ℱ =
      (λ_ ℱ).hom ≫ (ρ_ ℱ).inv := sorry

@[reducible] private noncomputable def unitInternalHomExactPairingOfIsIso
    (ℱ : ModX)
    [IsIso (unitInternalHomTensorToEnd ℱ)] :
    ExactPairing ((ihom ℱ).obj (𝟙_ ModX)) ℱ :=
  letI : ExactPairing ℱ ((ihom ℱ).obj (𝟙_ ModX)) :=
    { coevaluation' := unitInternalHomCoevaluation ℱ
      evaluation' := unitInternalHomEvaluation ℱ
      coevaluation_evaluation' := unitInternalHom_coevaluation_evaluation ℱ
      evaluation_coevaluation' := unitInternalHom_evaluation_coevaluation ℱ }
  BraidedCategory.exactPairing_swap ℱ ((ihom ℱ).obj (𝟙_ ModX))

/-- Example 17.18.1 also yields that
`\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal O_X)` is a left dual of
`\mathcal F`, with coevaluation `\eta` and evaluation `\epsilon` induced by the canonical
tensor-to-endomorphism isomorphism. In Lean this left-duality datum is packaged by
`CategoryTheory.ExactPairing`. -/
noncomputable instance
    (ℱ : ModX)
    [ℱ.IsLocallyDirectSummandOfFiniteFree] :
    ExactPairing ((ihom ℱ).obj (𝟙_ ModX)) ℱ :=
  letI : IsIso (unitInternalHomTensorToEnd ℱ) :=
    isIso_unitInternalHomTensorToEnd_of_locallyDirectSummandOfFiniteFree ℱ
  unitInternalHomExactPairingOfIsIso ℱ

end IsLocallyDirectSummandOfFiniteFree

end AlgebraicGeometry.RingedSpace
