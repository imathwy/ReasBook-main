import Mathlib
import stacks_project.Chap10.Lemma_10_133_6
import stacks_project.Chap17.Lemma_17_28_4
import stacks_project.Chap17.Lemma_17_29_5
import stacks_project.Chap18.Lemma_18_26_1

open CategoryTheory MonoidalCategory TopologicalSpace
open PresheafOfModules.DifferentialsConstruction
open TopCat.Sheaf

noncomputable section

universe u

section

variable {X : TopCat.{u}}
variable {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X}
variable (varphi : 𝒪₁ ⟶ 𝒪₂)
variable (ℱ : SheafOfModules (ringSheaf 𝒪₂))
local infixr:70 " ⊗ " => _root_.moduleTensor

/-- The morphism `𝒪₁(U) → 𝒪₂(U)` on an open set, viewed as an algebra structure. -/
private abbrev sectionAlgebra (U : (Opens X)ᵒᵖ) :
    Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) :=
  RingHom.toAlgebra (varphi.hom.app U).hom

/-- The `𝒪₁(U)`-module structure on `ℱ(U)` induced by restriction of scalars along
`𝒪₁(U) → 𝒪₂(U)`. -/
private abbrev sectionModule (U : (Opens X)ᵒᵖ) :
    Module (𝒪₁.obj.obj U) (ℱ.val.obj U) :=
  Module.compHom (ℱ.val.obj U) (((ringSheafMap varphi).hom.app U).hom)

/- Domain-style sampling for Lemma 17.29.6:
- primary domain: the first principal-parts exact sequence for sheaves of modules over a morphism
  of sheaves of commutative rings;
- sampled owner declarations:
  `TopCat.Sheaf.principalParts`,
  `TopCat.Sheaf.principalParts_is_principal_parts_module_of_order`,
  `TopCat.Sheaf.relativeDifferentials`,
  `_root_.moduleTensor`,
  `Module.principalPartsSequence`;
- best owner abstraction: the source-facing owner is the sheaf of first principal parts
  `P^{1}_[varphi](ℱ)`, with the principal-parts sequence and its naturality maps attached as
  derived API on that owner;
- primitive data versus derived API: the only genuinely new primitive map is the left comparison
  `Ω(varphi) ⊗ ℱ ⟶ P^{1}_[varphi](ℱ)`, while the projection to `ℱ`, the short complex, and the
  induced maps on principal parts and on the resulting short complex are all derived from the
  existing owner `TopCat.Sheaf.principalParts`.

Source/core/bridge triage:
- `source-facing`: the principal-parts short exact sequence attached to `P^{1}_[varphi](ℱ)`;
- `core/canonical`: `TopCat.Sheaf.principalParts`, `Ω(varphi)`, `_root_.moduleTensor`,
  `Functor.CorepresentableBy`, and `ShortComplex`;
- `bridge/view`: the sheafified cotangent comparison map and the naturality morphisms it induces.
-/

namespace TopCat.Sheaf.principalParts

-- Proof sketch: the identity on `ℱ`, viewed after restriction of scalars along
-- `ringSheafMap varphi`, is sectionwise `\mathcal O_2`-linear and hence an order-one
-- differential operator.
private theorem id_isDifferentialOperatorOfOrder_one :
    IsDifferentialOperatorOfOrder varphi
      (𝟙 ((SheafOfModules.restrictScalars (ringSheafMap varphi)).obj ℱ)) 1 := by
  sorry

/-- The canonical projection `P^1_{𝒪₂/𝒪₁}(ℱ) \to ℱ`, obtained from the representing property of
`P^{1}_[varphi](ℱ)` by evaluating at the identity differential operator of `ℱ`. -/
noncomputable def projection :
    P^{1}_[varphi](ℱ) ⟶ ℱ :=
  ((principalParts_is_principal_parts_module_of_order varphi ℱ 1).homEquiv).symm
    ⟨𝟙 ((SheafOfModules.restrictScalars (ringSheafMap varphi)).obj ℱ),
      id_isDifferentialOperatorOfOrder_one varphi ℱ⟩

/-- The universal order-one differential operator
`ℱ → P^{1}_[varphi](ℱ)` represented by first principal parts. -/
private noncomputable abbrev universalDifferentialOperator
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) :
    (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj ℱ ⟶
      (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj (P^{1}_[varphi](ℱ)) :=
  ((principalParts_is_principal_parts_module_of_order varphi ℱ 1).homEquiv
    (𝟙 (P^{1}_[varphi](ℱ)))).1

private theorem universalDifferentialOperator_isDifferentialOperatorOfOrder
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) :
    IsDifferentialOperatorOfOrder varphi
      (universalDifferentialOperator varphi ℱ) 1 :=
  ((principalParts_is_principal_parts_module_of_order varphi ℱ 1).homEquiv
    (𝟙 (P^{1}_[varphi](ℱ)))).2

/-- The objectwise tensor-source presheaf
`U ↦ Ω[𝒪₂(U)⁄𝒪₁(U)] ⊗_{𝒪₂(U)} ℱ(U)` underlying the sheaf map to principal parts. -/
private abbrev tensorSourcePresheaf :
    PresheafOfModules (ringSheaf 𝒪₂).obj :=
  PresheafOfModules.Monoidal.tensorObj (relativeDifferentials' varphi.hom) ℱ.val

/-- The sectionwise canonical map
`Ω[𝒪₂(U)⁄𝒪₁(U)] ⊗_{𝒪₂(U)} ℱ(U) → P^1_{𝒪₂(U)/𝒪₁(U)}(ℱ(U))`,
assembled into a morphism of presheaves. -/
private noncomputable def cotangentToPresheaf :
    tensorSourcePresheaf varphi ℱ ⟶ principalPartsPresheaf varphi ℱ 1 where
  app U := by
    letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
    letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
    letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
      IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
    change
      ModuleCat.of (𝒪₂.obj.obj U)
          (TensorProduct (𝒪₂.obj.obj U)
            (KaehlerDifferential (𝒪₁.obj.obj U) (𝒪₂.obj.obj U)) (ℱ.val.obj U)) ⟶
        ModuleCat.of (𝒪₂.obj.obj U)
          (principal_parts_module (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) 1)
    exact
      ModuleCat.ofHom
        (principalPartsCotangentToPrincipalParts
          (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U))
  naturality := by
    intro U V i
    sorry

/-- The inverse of the sheafification counit for the underlying presheaf of `ℱ`. -/
private noncomputable abbrev sheafificationCounitInv :
    ℱ ⟶ (moduleSheafification 𝒪₂).obj ℱ.val :=
  by
    let e := asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒪₂).obj)).counit
    exact (e.symm.app ℱ).hom

/-- The canonical left map
`\Omega_{\mathcal O_2/\mathcal O_1} \otimes_{\mathcal O_2} \mathcal F
  \to \mathcal P^1_{\mathcal O_2/\mathcal O_1}(\mathcal F)`,
obtained by sheafifying the sectionwise algebraic map from Lemma `10.133.6`. -/
noncomputable def cotangentTo :
    Ω(varphi) ⊗ ℱ ⟶ P^{1}_[varphi](ℱ) :=
  moduleTensorMap (𝟙 (Ω(varphi))) (sheafificationCounitInv ℱ) ≫
    (moduleSheafificationTensorIso 𝒪₂ (relativeDifferentials' varphi.hom) ℱ.val).hom ≫
    (moduleSheafification 𝒪₂).map (cotangentToPresheaf varphi ℱ)

-- Proof sketch: objectwise this is exactly the algebraic identity
-- `principalPartsCotangentToPrincipalParts ≫ principalPartsProjection = 0` from
-- Lemma `10.133.6`, transported through the sheafification/tensor comparisons above.
@[reassoc]
theorem cotangentTo_comp_projection :
    cotangentTo varphi ℱ ≫ projection varphi ℱ = 0 := by
  sorry

/-- The canonical short complex
`\Omega_{\mathcal O_2/\mathcal O_1} \otimes_{\mathcal O_2} \mathcal F
  \to \mathcal P^1_{\mathcal O_2/\mathcal O_1}(\mathcal F) \to \mathcal F`
attached to first principal parts. -/
noncomputable def sequence :
    ShortComplex (SheafOfModules (ringSheaf 𝒪₂)) :=
  ShortComplex.mk
    (cotangentTo varphi ℱ)
    (projection varphi ℱ)
    (cotangentTo_comp_projection varphi ℱ)

-- Proof sketch: apply the sectionwise short exact principal-parts sequence from
-- Lemma `10.133.6`, transport the source and middle terms through Lemmas `17.28.4` and `17.29.5`,
-- and identify the resulting right map with `projection`.
/-- Lemma 17.29.6: there is a canonical short exact sequence
`0 ⟶ \Omega_{\mathcal O_2/\mathcal O_1} \otimes_{\mathcal O_2} \mathcal F
  ⟶ \mathcal P^1_{\mathcal O_2/\mathcal O_1}(\mathcal F) ⟶ \mathcal F ⟶ 0`,
called the sequence of principal parts. -/
theorem sequence_shortExact :
    (sequence varphi ℱ).ShortExact := by
  sorry

/-- The canonical map on first principal-parts sheaves induced by a morphism of
`\mathcal O_2`-module sheaves. -/
noncomputable def map
    {ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪₂)} (α : ℱ ⟶ 𝒢) :
    P^{1}_[varphi](ℱ) ⟶ P^{1}_[varphi](𝒢) :=
  ((principalParts_is_principal_parts_module_of_order varphi ℱ 1).homEquiv).symm
    ⟨(SheafOfModules.restrictScalars (ringSheafMap varphi)).map α ≫
        universalDifferentialOperator varphi 𝒢,
      by
        simpa [Nat.zero_add] using
          isDifferentialOperatorOfOrder_comp varphi
            (isDifferentialOperatorOfOrder_restrictScalars_map varphi α)
            (universalDifferentialOperator_isDifferentialOperatorOfOrder varphi 𝒢)⟩

-- Proof sketch: both sides are the sheafified version of the sectionwise naturality of
-- `Module.principalPartsProjection`.
@[reassoc]
theorem projection_naturality
    {ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪₂)} (α : ℱ ⟶ 𝒢) :
    map varphi α ≫ projection varphi 𝒢 =
      projection varphi ℱ ≫ α := by
  sorry

-- Proof sketch: both sides are the sheafified version of the sectionwise naturality of
-- `Module.principalPartsCotangentToPrincipalParts`.
@[reassoc]
theorem cotangentTo_naturality
    {ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪₂)} (α : ℱ ⟶ 𝒢) :
    moduleTensorMap (𝟙 (Ω(varphi))) α ≫ cotangentTo varphi 𝒢 =
      cotangentTo varphi ℱ ≫ map varphi α := by
  sorry

/-- The canonical morphism of principal-parts sequences induced by a morphism of
`\mathcal O_2`-module sheaves. -/
noncomputable def sequenceMap
    {ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪₂)} (α : ℱ ⟶ 𝒢) :
    sequence varphi ℱ ⟶ sequence varphi 𝒢 :=
  ShortComplex.homMk
    (moduleTensorMap (𝟙 (Ω(varphi))) α)
    (map varphi α)
    α
    (cotangentTo_naturality varphi α)
    (projection_naturality varphi α)

end TopCat.Sheaf.principalParts

end
