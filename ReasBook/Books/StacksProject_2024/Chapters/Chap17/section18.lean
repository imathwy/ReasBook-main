import Mathlib
import Mathlib.CategoryTheory.Monoidal.Closed.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_17_18_1 (from Chap17) -/
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

/-! ### Lemma_17_18_2 (from Chap17) -/
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

/-! ### Lemma_17_18_3 (from Chap17) -/
open CategoryTheory TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.18.3:
- primary domain: flat sheaves of modules of finite presentation on a ringed space, with local
  finite-free retracts as the canonical output;
- inspected owner declarations:
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.IsFinitePresentation`,
  `SheafOfModules.IsLocallyDirectSummandOfFiniteFree`,
  `CategoryTheory.Retract`;
- best owner abstraction: `SheafOfModules.IsLocallyDirectSummandOfFiniteFree` is the chapter-level
  owner for the local retract condition, while explicit maps `ι` and `π` are derived local data;
- primitive data: a sheaf `ℱ : (RingedSpace.Modules X)` together with flatness and finite presentation;
- derived API: the pointwise neighborhood statement extracted from the owner class via
  `exists_open_neighborhood_retract_free`.

Source/core/bridge triage:
- `source-facing`: the neighborhood-wise direct-summand formulation around a chosen point;
- `core/canonical`: `SheafOfModules.IsLocallyDirectSummandOfFiniteFree`;
- `bridge/view`: the companion theorem below unpacking a local `Retract` into maps `ι` and `π`.

This file should therefore make the owner theorem primary and derive the pointwise textbook shape
from it, rather than keeping the raw split-morphism data as the only public API.
-/

-- Proof sketch: choose finite local presentations and use Lemma `17.17.11` to kill the relation
-- map after shrinking. The resulting surjection from a finite free sheaf splits, so the local
-- restriction is a retract of a finite free sheaf.
/-- Lemma 17.18.3: a flat `\mathcal O_X`-module of finite presentation on a ringed space is
locally a direct summand of a finite free `\mathcal O_X`-module. -/
theorem isLocallyDirectSummandOfFiniteFree_of_isFinitePresentation_of_flat
    {X : RingedSpace.{u}} (ℱ : (RingedSpace.Modules X))
    [ℱ.IsFinitePresentation] [SheafOfModules.RingedSite.IsFlat X.sheaf ℱ] :
    ℱ.IsLocallyDirectSummandOfFiniteFree := sorry

-- Proof sketch: apply the owner theorem to get a local retract `Retract (ℱ.over U) (free I)` and
-- then unpack its canonical inclusion and retraction maps.
/-- Lemma 17.18.3: if `\mathcal F` is a flat `\mathcal O_X`-module of finite presentation on a
ringed space `(X, \mathcal O_X)`, then around any point `x : X` there is an open neighbourhood
`U` such that `\mathcal F|_U` is a direct summand of a finite free `\mathcal O_U`-module. -/
theorem exists_open_neighborhood_direct_summand_of_finite_free_of_isFinitePresentation_of_flat
    {X : RingedSpace.{u}} (ℱ : (RingedSpace.Modules X))
    [ℱ.IsFinitePresentation] [SheafOfModules.RingedSite.IsFlat X.sheaf ℱ] (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U) (I : Type u) (_ : Finite I)
      (ι : ℱ.over U ⟶ SheafOfModules.free.{u} I)
      (π : SheafOfModules.free.{u} I ⟶ ℱ.over U),
        ι ≫ π = 𝟙 (ℱ.over U) := by
  letI : ℱ.IsLocallyDirectSummandOfFiniteFree :=
    isLocallyDirectSummandOfFiniteFree_of_isFinitePresentation_of_flat ℱ
  rcases
      (inferInstance : ℱ.IsLocallyDirectSummandOfFiniteFree).exists_open_neighborhood_retract_free
        x with
    ⟨U, hxU, I, hI, hretract⟩
  rcases hretract with ⟨R⟩
  exact ⟨U, hxU, I, hI, R.i, R.r, R.retract⟩

end AlgebraicGeometry.RingedSpace
