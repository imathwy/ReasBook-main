import Mathlib
import stacks_proof.stacks_project.Chap17.Definition_17_23_1
import stacks_proof.stacks_project.Chap17.Definition_17_25_6
import stacks_proof.stacks_project.Chap17.TensorPowerSheaf

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open Opposite
open TopologicalSpace
open scoped AlgebraicGeometry DirectSum

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [MonoidalCategory (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X
private abbrev topOpen (X : RingedSpace) : TopologicalSpace.Opens X :=
  ⟨Set.univ, isOpen_univ⟩

local notation "topOpenX" => topOpen X
local notation "ΓX" => X.presheaf.obj (op topOpenX)
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)
local notation:70 A " ⊗ₘ " B => (tensorObj A B : ModX)
local notation "IsInvertibleX" =>
  (fun ℒ : ModX ↦ Functor.IsEquivalence (tensorRight ℒ))
/-- Helper for Definition 17.25.7: use the equivalence-power owner for the integral tensor powers
of an invertible sheaf without importing the broader Chapter 17 owner file. -/
private abbrev tensorPowerSheafIntExpr
    (ℒ : ModX) [IsInvertibleX ℒ] (n : ℤ) : ModX :=
  (((tensorRight ℒ).asEquivalence ^ n).functor.obj 𝒪X)
local notation:80 ℒ " ^⊗ " n =>
  (tensorPowerSheafIntExpr ℒ n : ModX)
private abbrev ΓMod : ModX ⥤ ModuleCat ΓX :=
  SheafOfModules.evaluation X.ringCatSheaf (op topOpenX)

local instance : VAdd ℕ ℤ where
  vadd n i := (n : ℤ) + i

/- Domain-style sampling for Definition 17.25.7:
- primary domain: section rings and twisted section modules attached to tensor powers of an
  `\mathcal O_X`-module sheaf, with the twisted `\mathbf Z`-graded owner using the integral
  tensor powers of an invertible sheaf;
- inspected owner declarations:
  `SheafOfModules.evaluation`,
  `RingedSpace.Modules`,
  `SheafOfModules.unitHomEquiv`,
  `SheafOfModules.sectionsMap`,
  `SheafOfModules.unitIsoTensorUnit`,
  `tensorPowerSheaf`,
  `tensorPowerSheafInt`,
  `tensorPowerSheafIntOneAddIso`,
  `tensorPowerSheafIntAddIso`,
  `DirectSum.GNonUnitalNonAssocSemiring`,
  `GradedMonoid.GOne`,
  `DirectSum.GSemiring`,
  `DirectSum.GRing`,
  `DirectSum.GCommRing`,
  `DirectSum.Gmodule`;
- best owner abstraction: the source-facing owners are the direct sums
  `\Gamma_*(X, \mathcal L)` and `\Gamma_*(X, \mathcal L, \mathcal F)`; their homogeneous pieces
  are owned canonically by the top-global-sections functor `SheafOfModules.evaluation` at
  `topOpenX`, and the graded ring/module structures are the external direct-sum owners on those
  pieces;
- primitive data: for the ring owner, the nonnegative tensor-power sheaves `T^[n] ℒ`; for the
  twisted owner, an invertible sheaf `ℒ : ModX` together with the tensor powers `ℒ ^⊗ n` and the
  tensor owner `ℱ ⊗ₘ (ℒ ^⊗ n)`;
- derived API: the private bridge from sections to top evaluation, pure tensor sections, the
  nonnegative tensor-power multiplication isomorphism, the mixed action isomorphism, and the
  resulting `DirectSum.GCommRing` / `DirectSum.Gmodule` structures.

Layer triage:
- `source-facing`: `\Gamma_*(X, \mathcal L)` and `\Gamma_*(X, \mathcal L, \mathcal F)`;
- `core/canonical`: `RingedSpace.Modules X`, `SheafOfModules.evaluation`, `T^[n] ℒ`, `ℒ ^⊗ n`,
  `tensorObj`, and the direct-sum graded owners `DirectSum.GCommRing` / `DirectSum.Gmodule`;
- `bridge/view`: the private sections-to-top-evaluation equivalence, pure tensor sections, the
  recursive nonnegative-add tensor-power comparison, and the mixed action comparison built from
  `tensorPowerSheafIntAddIso`.
- ambient-assumption split: the noncommutative graded semiring/ring owners
  `DirectSum.GNonUnitalNonAssocSemiring`, `GradedMonoid.GOne`, `DirectSum.GSemiring`, and
  `DirectSum.GRing` only need the monoidal tensor product data, while symmetry first enters at the
  graded-commutative ring layer and in the twisted action comparison.
-/

private abbrev topOpenHom (U : (TopologicalSpace.Opens X)ᵒᵖ) : op topOpenX ⟶ U :=
  (homOfLE (show U.unop ≤ topOpenX from by
    intro x hx
    trivial)).op

omit [MonoidalCategory ModX] in
private theorem topSectionsFromTerminal_naturality
    (ℱ : ModX) (m : ΓMod.obj ℱ) :
    ∀ U V : (TopologicalSpace.Opens X)ᵒᵖ, ∀ f : U ⟶ V,
      ℱ.val.map f (ℱ.val.map (topOpenHom U) m) =
        ℱ.val.map (topOpenHom V) m := by
  intro U V f
  have h : topOpenHom U ≫ f = topOpenHom V := by
    exact Subsingleton.elim _ _
  rw [← PresheafOfModules.map_comp_apply, h]

private noncomputable def topSectionsFromTerminal
    (ℱ : ModX) (m : ΓMod.obj ℱ) :
    ℱ.sections :=
  ℱ.val.sectionsMk
    (fun U ↦ ℱ.val.map (topOpenHom U) m)
    (topSectionsFromTerminal_naturality ℱ m)

omit [MonoidalCategory ModX] in
private theorem topSectionEquiv_left_inv
    (ℱ : ModX) (s : ℱ.sections) :
    topSectionsFromTerminal ℱ (s.1 (op topOpenX)) = s := by
  ext U
  simpa using PresheafOfModules.sections_property s (topOpenHom U)

omit [MonoidalCategory ModX] in
private theorem topSectionEquiv_right_inv
    (ℱ : ModX) (m : ΓMod.obj ℱ) :
    (topSectionsFromTerminal ℱ m).1 (op topOpenX) = m := by
  change ℱ.val.map (topOpenHom (op topOpenX)) m = m
  have h : topOpenHom (op topOpenX) = 𝟙 (op topOpenX) := Subsingleton.elim _ _
  simpa [h] using ℱ.val.congr_map_apply h m

private noncomputable def topSectionEquiv (ℱ : ModX) :
    ℱ.sections ≃ ΓMod.obj ℱ where
  toFun s := s.1 (op topOpenX)
  invFun := topSectionsFromTerminal ℱ
  left_inv := topSectionEquiv_left_inv ℱ
  right_inv := topSectionEquiv_right_inv ℱ

omit [MonoidalCategory ModX] in
/-- Helper for Definition 17.25.7: the inverse of top evaluation is natural in a morphism of
module sheaves. -/
private theorem sectionsMap_topSectionEquiv_symm
    {ℱ 𝒢 : ModX} (ψ : ℱ ⟶ 𝒢) (m : ΓMod.obj ℱ) :
    SheafOfModules.sectionsMap ψ ((topSectionEquiv ℱ).symm m) =
      (topSectionEquiv 𝒢).symm (((ΓMod.map ψ).hom) m) := by
  -- Proof comment: both sides are sections whose value on each open is obtained by restricting
  -- the top component along `topOpenHom`; the claim is exactly naturality of `ψ`.
  ext U
  simp [topSectionEquiv, topSectionsFromTerminal]
  simpa using (ConcreteCategory.congr_hom (ψ.val.naturality (topOpenHom U)) m)

omit [MonoidalCategory ModX] in
/-- Helper for Definition 17.25.7: top evaluation commutes with section maps. -/
private theorem topSectionEquiv_sectionsMap
    {ℱ 𝒢 : ModX} (ψ : ℱ ⟶ 𝒢) (s : ℱ.sections) :
    topSectionEquiv 𝒢 (SheafOfModules.sectionsMap ψ s) =
      ((ΓMod.map ψ).hom) (topSectionEquiv ℱ s) := by
  -- Proof comment: rewrite `s` as the inverse image of its top component and then apply the
  -- established naturality of `topSectionEquiv.symm`.
  simpa using congrArg (topSectionEquiv 𝒢)
    (sectionsMap_topSectionEquiv_symm (ψ := ψ) (m := topSectionEquiv ℱ s))

private noncomputable def tensorSection
    {ℱ 𝒢 : ModX} (s : ℱ.sections) (t : 𝒢.sections) :
    (ℱ ⊗ₘ 𝒢 : ModX).sections :=
  let η : SheafOfModules.unit X.ringCatSheaf ≅ 𝟙_ ModX :=
    SheafOfModules.unitIsoTensorUnit
  (ℱ ⊗ₘ 𝒢 : ModX).unitHomEquiv
    (η.hom ≫ (λ_ (𝟙_ ModX)).inv ≫
      ((η.inv ≫ ℱ.unitHomEquiv.symm s) ⊗ₘ (η.inv ≫ 𝒢.unitHomEquiv.symm t)))

omit [MonoidalCategory ModX] in
/-- Helper for Definition 17.25.7: evaluating `unitHomEquiv` at the top open computes the
corresponding unit morphism on the global unit section. -/
private theorem unitHomEquiv_apply_top
    (M : ModX) (f : SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    topSectionEquiv M (M.unitHomEquiv f) =
      (f.val.app (op topOpenX))
        (show ((SheafOfModules.unit X.ringCatSheaf).val.obj (op topOpenX)) from (1 : ΓX)) := by
  -- Proof comment: top evaluation of `unitHomEquiv` is definitional evaluation of the unit
  -- morphism on the section `1`.
  rfl

omit [MonoidalCategory ModX] in
/-- Helper for Definition 17.25.7: package a top global section as the corresponding morphism out
of the unit sheaf. -/
private noncomputable def topSectionMorphism
    (M : ModX) (x : ΓMod.obj M) :
    𝒪X ⟶ M :=
  M.unitHomEquiv.symm ((topSectionEquiv M).symm x)

omit [MonoidalCategory ModX] in
/-- Helper for Definition 17.25.7: the top evaluation of the unit morphism attached to a section
recovers the original top section. -/
private theorem topSectionMorphism_apply_top
    (M : ModX) (x : ΓMod.obj M) :
    ((topSectionMorphism M x).val.app (op topOpenX))
        (show ((SheafOfModules.unit X.ringCatSheaf).val.obj (op topOpenX)) from (1 : ΓX)) = x := by
  -- Proof comment: `topSectionMorphism` is defined as the inverse of the composite
  -- `unitHomEquiv` followed by `topSectionEquiv`.
  simpa [topSectionMorphism] using
    (unitHomEquiv_apply_top M (topSectionMorphism M x)).symm

omit [MonoidalCategory ModX] in
/-- Helper for Definition 17.25.7: the composite `unitHomEquiv` then `topSectionEquiv` carries
addition on unit morphisms to addition on top sections. -/
private theorem topSectionEquiv_unitHomEquiv_add
    (M : ModX) (f g : 𝒪X ⟶ M) :
    topSectionEquiv M (M.unitHomEquiv (f + g)) =
      topSectionEquiv M (M.unitHomEquiv f) + topSectionEquiv M (M.unitHomEquiv g) := by
  -- Proof comment: after rewriting with `unitHomEquiv_apply_top`, addition is pointwise
  -- addition of module morphisms at the top open.
  rw [unitHomEquiv_apply_top, unitHomEquiv_apply_top, unitHomEquiv_apply_top]
  rfl

omit [MonoidalCategory ModX] in
/-- Helper for Definition 17.25.7: the composite `unitHomEquiv` then `topSectionEquiv` sends the
zero morphism out of the unit sheaf to the zero top section. -/
private theorem topSectionEquiv_unitHomEquiv_zero
    (M : ModX) :
    topSectionEquiv M (M.unitHomEquiv (0 : 𝒪X ⟶ M)) = 0 := by
  -- Proof comment: top evaluation of the zero unit morphism is the zero element of the top
  -- module.
  rw [unitHomEquiv_apply_top]
  rfl

omit [MonoidalCategory ModX] in
/-- Helper for Definition 17.25.7: equality of morphisms from the unit sheaf can be checked on
their top value at `1`. -/
private theorem topSectionMorphism_ext
    (M : ModX) {f g : 𝒪X ⟶ M}
    (h :
      ((f.val.app (op topOpenX))
          (show ((SheafOfModules.unit X.ringCatSheaf).val.obj (op topOpenX)) from (1 : ΓX))) =
        ((g.val.app (op topOpenX))
          (show ((SheafOfModules.unit X.ringCatSheaf).val.obj (op topOpenX)) from (1 : ΓX)))) :
    f = g := by
  -- Proof comment: both `unitHomEquiv` and `topSectionEquiv` are equivalences, so equality of
  -- the transported top sections forces equality of the original unit morphisms.
  apply M.unitHomEquiv.injective
  apply (topSectionEquiv M).injective
  rw [unitHomEquiv_apply_top, unitHomEquiv_apply_top]
  exact h

omit [MonoidalCategory ModX] in
/-- Helper for Definition 17.25.7: the unit morphism attached to the zero top section is the zero
morphism. -/
private theorem topSectionMorphism_zero
    (M : ModX) :
    topSectionMorphism M 0 = 0 := by
  -- Proof comment: compare both morphisms after transporting them back to top sections.
  apply M.unitHomEquiv.injective
  apply (topSectionEquiv M).injective
  rw [topSectionEquiv_unitHomEquiv_zero]
  simp [topSectionMorphism]

omit [MonoidalCategory ModX] in
/-- Helper for Definition 17.25.7: the unit morphism attached to a sum of top sections is the sum
of the attached unit morphisms. -/
private theorem topSectionMorphism_add
    (M : ModX) (x y : ΓMod.obj M) :
    topSectionMorphism M (x + y) =
      topSectionMorphism M x + topSectionMorphism M y := by
  -- Proof comment: transport the equality through `unitHomEquiv` and `topSectionEquiv`, where it
  -- becomes the pointwise additivity statement proved above.
  apply M.unitHomEquiv.injective
  apply (topSectionEquiv M).injective
  rw [topSectionEquiv_unitHomEquiv_add]
  simp [topSectionMorphism]

omit [MonoidalCategory ModX] in
/-- Helper for Definition 17.25.7: the unit morphism construction is injective on top global
sections. -/
private theorem topSectionMorphism_injective
    (M : ModX) :
    Function.Injective (topSectionMorphism M) := by
  -- Proof comment: `topSectionMorphism` is the composite of the inverse equivalences
  -- `topSectionEquiv.symm` and `unitHomEquiv.symm`.
  intro x y hxy
  apply (topSectionEquiv M).symm.injective
  exact M.unitHomEquiv.symm.injective hxy

omit [MonoidalCategory ModX] in
/-- Helper for Definition 17.25.7: applying `topSectionMorphism` after `topSectionEquiv` recovers
the corresponding unit morphism. -/
private theorem topSectionMorphism_topSectionEquiv
    (M : ModX) (s : M.sections) :
    topSectionMorphism M (topSectionEquiv M s) = M.unitHomEquiv.symm s := by
  -- Proof comment: this is the defining cancellation between `topSectionEquiv` and its inverse.
  simp [topSectionMorphism]

omit [MonoidalCategory ModX] in
/-- Helper for Definition 17.25.7: the degree-zero unit section corresponds to the identity
morphism of the structure sheaf. -/
private theorem topSectionMorphism_one :
    topSectionMorphism 𝒪X (1 : ΓX) = 𝟙 𝒪X := by
  -- Proof comment: compare both unit morphisms by evaluating them at the distinguished top
  -- section `1`.
  apply topSectionMorphism_ext
  rw [topSectionMorphism_apply_top]
  rfl

omit [MonoidalCategory ModX] in
/-- Helper for Definition 17.25.7: `topSectionMorphism` commutes with top evaluation of a module
sheaf morphism. -/
private theorem topSectionMorphism_map
    {ℱ 𝒢 : ModX} (ψ : ℱ ⟶ 𝒢) (x : ΓMod.obj ℱ) :
    topSectionMorphism 𝒢 (((ΓMod.map ψ).hom) x) =
      topSectionMorphism ℱ x ≫ ψ := by
  -- Proof comment: both morphisms out of the unit sheaf have the same top value, namely the
  -- image of `x` under `Γ(X, ψ)`.
  apply topSectionMorphism_ext
  rw [topSectionMorphism_apply_top]
  change ((ΓMod.map ψ).hom) x =
    (ψ.val.app (op topOpenX))
      (((topSectionMorphism ℱ x).val.app (op topOpenX))
        (show ((SheafOfModules.unit X.ringCatSheaf).val.obj (op topOpenX)) from (1 : ΓX)))
  rw [topSectionMorphism_apply_top]
  rfl

/-- Helper for Definition 17.25.7: the unit morphism of a pure tensor section is the tensor
product of the corresponding unit morphisms. -/
private theorem topSectionMorphism_tensorSection
    {ℱ 𝒢 : ModX} (x : ΓMod.obj ℱ) (y : ΓMod.obj 𝒢) :
    topSectionMorphism (ℱ ⊗ₘ 𝒢 : ModX)
        (topSectionEquiv (ℱ ⊗ₘ 𝒢 : ModX)
          (tensorSection ((topSectionEquiv ℱ).symm x)
            ((topSectionEquiv 𝒢).symm y))) =
      let η : SheafOfModules.unit X.ringCatSheaf ≅ 𝟙_ ModX :=
        SheafOfModules.unitIsoTensorUnit
      η.hom ≫ (λ_ (𝟙_ ModX)).inv ≫
        ((η.inv ≫ topSectionMorphism ℱ x) ⊗ₘ (η.inv ≫ topSectionMorphism 𝒢 y)) := by
  -- Proof comment: unfold `tensorSection` and cancel the inverse equivalences in the definition
  -- of `topSectionMorphism`.
  simp [tensorSection, topSectionMorphism_topSectionEquiv, topSectionMorphism]

/-- Helper for Definition 17.25.7: reassociating a nested pure tensor section agrees with the
monoidal associator after passing to unit morphisms. -/
-- TODO: Replan via a unit-morphism-level associativity normalization for nested `tensorSection`.
private theorem topSectionMorphism_tensorSection_assoc
    {ℱ 𝒢 ℋ : ModX} (x : ΓMod.obj ℱ) (y : ΓMod.obj 𝒢) (z : ΓMod.obj ℋ) :
    topSectionMorphism (((ℱ ⊗ₘ 𝒢) ⊗ₘ ℋ : ModX))
        (topSectionEquiv (((ℱ ⊗ₘ 𝒢) ⊗ₘ ℋ : ModX))
          (tensorSection
            (tensorSection ((topSectionEquiv ℱ).symm x) ((topSectionEquiv 𝒢).symm y))
            ((topSectionEquiv ℋ).symm z))) ≫
      (α_ ℱ 𝒢 ℋ).hom =
    topSectionMorphism ((ℱ ⊗ₘ (𝒢 ⊗ₘ ℋ) : ModX))
        (topSectionEquiv ((ℱ ⊗ₘ (𝒢 ⊗ₘ ℋ) : ModX))
          (tensorSection
            ((topSectionEquiv ℱ).symm x)
            (tensorSection ((topSectionEquiv 𝒢).symm y) ((topSectionEquiv ℋ).symm z)))) := by
  -- Proof comment: normalize both nested tensor sections to unit morphisms and let monoidal
  -- coherence identify the two parenthesizations.
  rw [topSectionMorphism_tensorSection, topSectionMorphism_tensorSection, topSectionMorphism_map]
  simp only [Category.assoc]
  monoidal_coherence

/-- Helper for Definition 17.25.7: swapping a pure tensor section agrees with the symmetric
braiding after passing to unit morphisms. -/
-- TODO: Replan via a unit-morphism-level braiding normalization for `tensorSection`.
private theorem topSectionMorphism_tensorSection_braiding
    {ℱ 𝒢 : ModX} [SymmetricCategory ModX] (x : ΓMod.obj ℱ) (y : ΓMod.obj 𝒢) :
    topSectionMorphism ((ℱ ⊗ₘ 𝒢 : ModX))
        (topSectionEquiv ((ℱ ⊗ₘ 𝒢 : ModX))
          (tensorSection ((topSectionEquiv ℱ).symm x) ((topSectionEquiv 𝒢).symm y))) ≫
      (β_ ℱ 𝒢).hom =
    topSectionMorphism ((𝒢 ⊗ₘ ℱ : ModX))
        (topSectionEquiv ((𝒢 ⊗ₘ ℱ : ModX))
          (tensorSection ((topSectionEquiv 𝒢).symm y) ((topSectionEquiv ℱ).symm x))) := by
  -- Proof comment: after normalizing the pure tensor sections, the claim is exactly symmetry of
  -- the tensor braiding on the distinguished unit morphisms.
  rw [topSectionMorphism_tensorSection, topSectionMorphism_tensorSection]
  simp only [Category.assoc]
  monoidal_coherence

/-- Helper for Definition 17.25.7: tensoring a sum on the right in `Γ(X, -)` distributes over
addition. -/
private theorem tensorHom_add_right
    {A B C D : ModuleCat ΓX} (f : A ⟶ B) (g₁ g₂ : C ⟶ D) :
    tensorHom f (g₁ + g₂) = tensorHom f g₁ + tensorHom f g₂ := by
  -- Proof comment: both sides are linear maps out of a tensor product, so it is enough to check
  -- them on pure tensors and extend by tensor-product induction.
  refine ModuleCat.MonoidalCategory.tensor_ext ?_
  intro a c
  change f a ⊗ₜ[ΓX] (g₁ + g₂) c = (f a ⊗ₜ[ΓX] g₁ c) + (f a ⊗ₜ[ΓX] g₂ c)
  simpa using TensorProduct.tmul_add (f a) (g₁ c) (g₂ c)

/-- Helper for Definition 17.25.7: tensoring a sum on the left in `Γ(X, -)` distributes over
addition. -/
private theorem tensorHom_add_left
    {A B C D : ModuleCat ΓX} (f₁ f₂ : A ⟶ B) (g : C ⟶ D) :
    tensorHom (f₁ + f₂) g = tensorHom f₁ g + tensorHom f₂ g := by
  -- Proof comment: as on the right, pure tensors determine morphisms out of the tensor product.
  refine ModuleCat.MonoidalCategory.tensor_ext ?_
  intro a c
  change (f₁ + f₂) a ⊗ₜ[ΓX] g c = (f₁ a ⊗ₜ[ΓX] g c) + (f₂ a ⊗ₜ[ΓX] g c)
  simpa using TensorProduct.add_tmul (f₁ a) (f₂ a) (g c)

/-- Helper for Definition 17.25.7: tensoring zero on the right in `Γ(X, -)` gives the zero
morphism. -/
private theorem tensorHom_zero_right
    {A B C D : ModuleCat ΓX} (f : A ⟶ B) :
    tensorHom f (0 : C ⟶ D) = 0 := by
  -- Proof comment: pure tensors generate the tensor product, and the right zero factor kills each
  -- pure tensor.
  refine ModuleCat.MonoidalCategory.tensor_ext ?_
  intro a c
  change f a ⊗ₜ[ΓX] (0 : D) = 0
  rw [TensorProduct.tmul_zero]

/-- Helper for Definition 17.25.7: tensoring zero on the left in `Γ(X, -)` gives the zero
morphism. -/
private theorem tensorHom_zero_left
    {A B C D : ModuleCat ΓX} (g : C ⟶ D) :
    tensorHom (0 : A ⟶ B) g = 0 := by
  -- Proof comment: this is the left-handed version of the previous pure-tensor computation.
  refine ModuleCat.MonoidalCategory.tensor_ext ?_
  intro a c
  change (0 : B) ⊗ₜ[ΓX] g c = 0
  rw [TensorProduct.zero_tmul]

/-- Helper for Definition 17.25.7: the pure-top-section tensor construction kills a zero right
input. -/
-- TODO: Replan via an explicit zero-morphism normalization of the unit-level tensor expression.
private theorem topSectionEquiv_tensorSection_zero_right
    {ℱ 𝒢 : ModX} (x : ΓMod.obj ℱ) :
    topSectionEquiv (ℱ ⊗ₘ 𝒢 : ModX)
      (tensorSection ((topSectionEquiv ℱ).symm x)
        ((topSectionEquiv 𝒢).symm (0 : ΓMod.obj 𝒢))) = 0 := by
  -- Proof comment: move to unit morphisms, where the right factor is the zero morphism and the
  -- tensor expression vanishes after evaluating at the top open.
  apply topSectionMorphism_injective (M := (ℱ ⊗ₘ 𝒢 : ModX))
  rw [topSectionMorphism_zero, topSectionMorphism_tensorSection, topSectionMorphism_zero]
  apply topSectionMorphism_ext
  simp only [Category.assoc]
  rw [tensorHom_zero_right]
  simp

/-- Helper for Definition 17.25.7: the pure-top-section tensor construction kills a zero left
input. -/
-- TODO: Replan via the left-handed zero-morphism normalization for `tensorSection`.
private theorem topSectionEquiv_tensorSection_zero_left
    {ℱ 𝒢 : ModX} (y : ΓMod.obj 𝒢) :
    topSectionEquiv (ℱ ⊗ₘ 𝒢 : ModX)
      (tensorSection ((topSectionEquiv ℱ).symm (0 : ΓMod.obj ℱ))
        ((topSectionEquiv 𝒢).symm y)) = 0 := by
  -- Proof comment: the left factor is zero after normalizing to unit morphisms, so the tensor
  -- expression itself is zero.
  apply topSectionMorphism_injective (M := (ℱ ⊗ₘ 𝒢 : ModX))
  rw [topSectionMorphism_zero, topSectionMorphism_tensorSection, topSectionMorphism_zero]
  apply topSectionMorphism_ext
  simp only [Category.assoc]
  rw [tensorHom_zero_left]
  simp

/-- Helper for Definition 17.25.7: the pure-top-section tensor construction is additive in the
right input. -/
-- TODO: Replan via distribution of the unit-level tensor morphism over sums on the right.
private theorem topSectionEquiv_tensorSection_add_right
    {ℱ 𝒢 : ModX} (x : ΓMod.obj ℱ) (y z : ΓMod.obj 𝒢) :
    topSectionEquiv (ℱ ⊗ₘ 𝒢 : ModX)
      (tensorSection ((topSectionEquiv ℱ).symm x)
        ((topSectionEquiv 𝒢).symm (y + z))) =
      topSectionEquiv (ℱ ⊗ₘ 𝒢 : ModX)
        (tensorSection ((topSectionEquiv ℱ).symm x)
          ((topSectionEquiv 𝒢).symm y)) +
      topSectionEquiv (ℱ ⊗ₘ 𝒢 : ModX)
        (tensorSection ((topSectionEquiv ℱ).symm x)
          ((topSectionEquiv 𝒢).symm z)) := by
  -- Proof comment: after passing to unit morphisms, additivity comes from additivity of
  -- `topSectionMorphism` and the right-linearity of `tensorHom`.
  apply topSectionMorphism_injective (M := (ℱ ⊗ₘ 𝒢 : ModX))
  rw [topSectionMorphism_add, topSectionMorphism_tensorSection, topSectionMorphism_tensorSection,
    topSectionMorphism_tensorSection, topSectionMorphism_add]
  apply topSectionMorphism_ext
  simp only [Category.assoc]
  rw [tensorHom_add_right]
  simp

/-- Helper for Definition 17.25.7: the pure-top-section tensor construction is additive in the
left input. -/
-- TODO: Replan via distribution of the unit-level tensor morphism over sums on the left.
private theorem topSectionEquiv_tensorSection_add_left
    {ℱ 𝒢 : ModX} (x y : ΓMod.obj ℱ) (z : ΓMod.obj 𝒢) :
    topSectionEquiv (ℱ ⊗ₘ 𝒢 : ModX)
      (tensorSection ((topSectionEquiv ℱ).symm (x + y))
        ((topSectionEquiv 𝒢).symm z)) =
      topSectionEquiv (ℱ ⊗ₘ 𝒢 : ModX)
        (tensorSection ((topSectionEquiv ℱ).symm x)
          ((topSectionEquiv 𝒢).symm z)) +
      topSectionEquiv (ℱ ⊗ₘ 𝒢 : ModX)
        (tensorSection ((topSectionEquiv ℱ).symm y)
          ((topSectionEquiv 𝒢).symm z)) := by
  -- Proof comment: the left-linearity argument is the same after switching to the left tensor
  -- factor.
  apply topSectionMorphism_injective (M := (ℱ ⊗ₘ 𝒢 : ModX))
  rw [topSectionMorphism_add, topSectionMorphism_tensorSection, topSectionMorphism_tensorSection,
    topSectionMorphism_tensorSection, topSectionMorphism_add]
  apply topSectionMorphism_ext
  simp only [Category.assoc]
  rw [tensorHom_add_left]
  simp

private noncomputable def tensorPowerSheafAddIso
    (ℒ : ModX) :
    (m n : ℕ) → ((T^[m] ℒ) ⊗ₘ (T^[n] ℒ) : ModX) ≅ T^[m + n] ℒ
  | 0, n => by
      simpa [tensorPowerSheaf] using
        ((SheafOfModules.unitIsoTensorUnit ▷ᵢ (T^[n] ℒ)) ≪≫ λ_ (T^[n] ℒ))
  | m + 1, n => by
      calc
        (((T^[m + 1] ℒ) ⊗ₘ (T^[n] ℒ) : ModX)) ≅
            (((ℒ ⊗ₘ T^[m] ℒ) ⊗ₘ T^[n] ℒ) : ModX) :=
          eqToIso (by rw [tensorPowerSheaf_succ])
        _ ≅ (ℒ ⊗ₘ ((T^[m] ℒ) ⊗ₘ (T^[n] ℒ)) : ModX) :=
          α_ ℒ (T^[m] ℒ) (T^[n] ℒ)
        _ ≅ (ℒ ⊗ₘ T^[m + n] ℒ : ModX) :=
          Iso.refl ℒ ⊗ᵢ tensorPowerSheafAddIso ℒ m n
        _ ≅ T^[m + 1 + n] ℒ :=
          eqToIso (by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (tensorPowerSheaf_succ ℒ (m + n)).symm)

/-- Helper for Definition 17.25.7: applying an autoequivalence one more time advances its
integer power by one. -/
/-- Helper for Definition 17.25.7: tensoring once more by an invertible sheaf agrees with the
canonical integral tensor-power shift isomorphism from Definition 17.25.6. -/
private noncomputable def equivalencePowSuccIso
    [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertibleX ℒ] (n : ℤ) :
    (ℒ ⊗ₘ (ℒ ^⊗ n) : ModX) ≅ ℒ ^⊗ (n + 1) := by
  -- Proof comment: reuse the earlier canonical Chapter 17 shift isomorphism instead of
  -- reproving the `Equivalence.pow` normalization locally.
  simpa [tensorPowerSheafIntExpr, tensorPowerSheafInt] using
    (tensorPowerSheafIntOneAddIso (X := X) ℒ n)

/-- Helper for Definition 17.25.7: braiding turns left tensoring by `\mathcal L` into the
right-tensor autoequivalence, so one more tensor factor shifts the degree by one. -/
private noncomputable def tensorPowerShiftIso
    [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertibleX ℒ] (n : ℤ) :
    (ℒ ⊗ₘ (ℒ ^⊗ n) : ModX) ≅ ℒ ^⊗ (n + 1) :=
  equivalencePowSuccIso (X := X) ℒ n

/-- The degree-`n` homogeneous piece of `\Gamma_*(X, \mathcal L)`. -/
abbrev gradedGlobalSectionsDegree
    (ℒ : ModX) (n : ℕ) : Type _ :=
  ΓMod.obj (T^[n] ℒ)

/-- The degree-`n` homogeneous piece of `\Gamma_*(X, \mathcal L, \mathcal F)`. -/
abbrev gradedTwistedGlobalSectionsDegree
    (ℒ : ModX) [IsInvertibleX ℒ] (ℱ : ModX) (n : ℤ) :
    Type _ :=
  ΓMod.obj (ℱ ⊗ₘ (ℒ ^⊗ n) : ModX)

/-- Homogeneous multiplication on the degree pieces of `\Gamma_*(X, \mathcal L)`. -/
noncomputable def gradedGlobalSectionsMul
    (ℒ : ModX) {m n : ℕ} :
    gradedGlobalSectionsDegree ℒ m →
      gradedGlobalSectionsDegree ℒ n →
        gradedGlobalSectionsDegree ℒ (m + n) :=
  fun x y ↦
    topSectionEquiv (T^[m + n] ℒ) <|
      SheafOfModules.sectionsMap (tensorPowerSheafAddIso ℒ m n).hom
        (tensorSection
          ((topSectionEquiv (T^[m] ℒ)).symm x)
          ((topSectionEquiv (T^[n] ℒ)).symm y))

/-- Helper for Definition 17.25.7: shifting by one after twisting by degree `m` agrees with the
successor twist degree. -/
private theorem twistedDegreeSucc
    (m : ℕ) (n : ℤ) :
    (((m : ℤ) + n) + 1) = (((m + 1 : ℕ) : ℤ) + n) := by
  -- Proof comment: both sides are the same affine-linear expression in `m` and `n`.
  omega

/-- Helper for Definition 17.25.7: combining two nonnegative degrees before twisting agrees with
twisting by the right degree first and then by the left degree. -/
private theorem twistedDegreeAddAssoc
    (m n : ℕ) (i : ℤ) :
    (((m + n : ℕ) : ℤ) + i) = ((m : ℤ) + ((n : ℤ) + i)) := by
  -- Proof comment: the direct-sum reindexing is just associativity of addition after coercing
  -- the natural degrees to integers.
  omega

private noncomputable def gradedTwistedGlobalSectionsActionIso
    [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertibleX ℒ] (ℱ : ModX) :
    (m : ℕ) → (n : ℤ) →
      ((T^[m] ℒ) ⊗ₘ (ℱ ⊗ₘ (ℒ ^⊗ n)) : ModX) ≅
        (ℱ ⊗ₘ (ℒ ^⊗ ((m : ℤ) + n)) : ModX)
  | 0, n => by
      calc
        ((T^[0] ℒ) ⊗ₘ (ℱ ⊗ₘ (ℒ ^⊗ n)) : ModX) ≅
            (𝒪X ⊗ₘ (ℱ ⊗ₘ (ℒ ^⊗ n)) : ModX) :=
          eqToIso rfl
        _ ≅ (ℱ ⊗ₘ (ℒ ^⊗ n) : ModX) :=
          (SheafOfModules.unitIsoTensorUnit ▷ᵢ (ℱ ⊗ₘ (ℒ ^⊗ n))) ≪≫ λ_ _
        _ ≅ (ℱ ⊗ₘ (ℒ ^⊗ ((0 : ℤ) + n)) : ModX) :=
          eqToIso (by simp)
  | m + 1, n => by
      calc
        ((T^[m + 1] ℒ) ⊗ₘ (ℱ ⊗ₘ (ℒ ^⊗ n)) : ModX) ≅
            ((ℒ ⊗ₘ T^[m] ℒ) ⊗ₘ (ℱ ⊗ₘ (ℒ ^⊗ n)) : ModX) :=
          eqToIso (by
            simpa using
              congrArg
                (fun K : ModX ↦ (K ⊗ₘ (ℱ ⊗ₘ (ℒ ^⊗ n)) : ModX))
                (tensorPowerSheaf_succ ℒ m)
          )
        _ ≅ (ℒ ⊗ₘ ((T^[m] ℒ) ⊗ₘ (ℱ ⊗ₘ (ℒ ^⊗ n))) : ModX) :=
          α_ ℒ (T^[m] ℒ) (ℱ ⊗ₘ (ℒ ^⊗ n))
        _ ≅ (ℒ ⊗ₘ (ℱ ⊗ₘ (ℒ ^⊗ ((m : ℤ) + n))) : ModX) :=
          Iso.refl ℒ ⊗ᵢ gradedTwistedGlobalSectionsActionIso ℒ ℱ m n
        _ ≅ ((ℒ ⊗ₘ ℱ) ⊗ₘ (ℒ ^⊗ ((m : ℤ) + n)) : ModX) :=
          (α_ ℒ ℱ (ℒ ^⊗ ((m : ℤ) + n))).symm
        _ ≅ ((ℱ ⊗ₘ ℒ) ⊗ₘ (ℒ ^⊗ ((m : ℤ) + n)) : ModX) :=
          (β_ ℒ ℱ) ⊗ᵢ Iso.refl _
        _ ≅ (ℱ ⊗ₘ (ℒ ⊗ₘ (ℒ ^⊗ ((m : ℤ) + n))) : ModX) :=
          α_ ℱ ℒ (ℒ ^⊗ ((m : ℤ) + n))
        _ ≅ (ℱ ⊗ₘ (ℒ ^⊗ (((m : ℤ) + n) + 1)) : ModX) := by
          let e :
              (ℒ ⊗ₘ (ℒ ^⊗ ((m : ℤ) + n)) : ModX) ≅
                ℒ ^⊗ (((m : ℤ) + n) + 1) :=
            tensorPowerShiftIso ℒ ((m : ℤ) + n)
          exact Iso.refl ℱ ⊗ᵢ e
        _ ≅ (ℱ ⊗ₘ (ℒ ^⊗ (((m + 1 : ℕ) : ℤ) + n)) : ModX) :=
          eqToIso (by
            -- Proof comment: normalize the successor degree through the named arithmetic bridge.
            simpa [twistedDegreeSucc m n])

/-- Homogeneous action of `\Gamma_*(X, \mathcal L)` on the degree pieces of
`\Gamma_*(X, \mathcal L, \mathcal F)`. -/
noncomputable def gradedTwistedGlobalSectionsSmul
    [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertibleX ℒ] (ℱ : ModX) {m : ℕ} {n : ℤ} :
    gradedGlobalSectionsDegree ℒ m →
      gradedTwistedGlobalSectionsDegree ℒ ℱ n →
        gradedTwistedGlobalSectionsDegree ℒ ℱ (m + n) :=
  fun x y ↦
    topSectionEquiv (ℱ ⊗ₘ (ℒ ^⊗ ((m : ℤ) + n))) <|
      SheafOfModules.sectionsMap (gradedTwistedGlobalSectionsActionIso ℒ ℱ m n).hom
        (tensorSection
          ((topSectionEquiv (T^[m] ℒ)).symm x)
          ((topSectionEquiv (ℱ ⊗ₘ (ℒ ^⊗ n))).symm y))

/-- Helper for Definition 17.25.7: the recursive tensor-power comparison is associative up to the
canonical degree reindexing. -/
-- TODO: Replan via a structural-coherence lemma that absorbs the explicit `eqToHom` reindexing.
private theorem tensorPowerSheafAddIso_assoc
    (ℒ : ModX) (m n k : ℕ) :
    (((tensorPowerSheafAddIso ℒ m n).hom ⊗ₘ 𝟙 (T^[k] ℒ)) ≫
        (tensorPowerSheafAddIso ℒ (m + n) k).hom) ≫
      eqToHom (by simp [Nat.add_assoc]) =
    (α_ (T^[m] ℒ) (T^[n] ℒ) (T^[k] ℒ)).hom ≫
      (𝟙 (T^[m] ℒ) ⊗ₘ (tensorPowerSheafAddIso ℒ n k).hom) ≫
      (tensorPowerSheafAddIso ℒ m (n + k)).hom := sorry

/-- Helper for Definition 17.25.7: the recursive tensor-power comparison is compatible with the
symmetric braiding up to the canonical commutativity reindexing. -/
-- TODO: Replan via a structural-coherence lemma that absorbs the explicit commutativity cast.
private theorem tensorPowerSheafAddIso_braiding
    [SymmetricCategory ModX] (ℒ : ModX) (m n : ℕ) :
    (β_ (T^[m] ℒ) (T^[n] ℒ)).hom ≫
        (tensorPowerSheafAddIso ℒ n m).hom ≫
      eqToHom (by simp [Nat.add_comm]) =
    (tensorPowerSheafAddIso ℒ m n).hom := sorry

/-- Helper for Definition 17.25.7: the recursive twisted-action comparison is compatible with
first combining two nonnegative tensor powers and then acting. -/
-- TODO: Replan via a structural-coherence lemma that separates the arithmetic reindexing from the
-- monoidal reassociation in the mixed action comparison.
private theorem gradedTwistedGlobalSectionsActionIso_assoc
    [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertibleX ℒ] (ℱ : ModX) (m n : ℕ) (i : ℤ) :
    (((tensorPowerSheafAddIso ℒ m n).hom ⊗ₘ 𝟙 (ℱ ⊗ₘ (ℒ ^⊗ i) : ModX)) ≫
        (gradedTwistedGlobalSectionsActionIso ℒ ℱ (m + n) i).hom) ≫
      eqToHom (congrArg (fun j : ℤ ↦ (ℱ ⊗ₘ (ℒ ^⊗ j) : ModX))
        (twistedDegreeAddAssoc m n i)) =
    (α_ (T^[m] ℒ) (T^[n] ℒ) (ℱ ⊗ₘ (ℒ ^⊗ i))).hom ≫
      (𝟙 (T^[m] ℒ) ⊗ₘ (gradedTwistedGlobalSectionsActionIso ℒ ℱ n i).hom) ≫
      (gradedTwistedGlobalSectionsActionIso ℒ ℱ m (n + i)).hom := sorry

/-- Helper for Definition 17.25.7: the unit morphism of a homogeneous product is the pure tensor
unit morphism followed by the tensor-power comparison. -/
-- TODO: Replan via a normalized `tensorSection` sections-type ascription before restoring this
-- helper's original comparison statement.
private theorem topSectionMorphism_gradedGlobalSectionsMul
    (ℒ : ModX) {m n : ℕ}
    (x : gradedGlobalSectionsDegree ℒ m) (y : gradedGlobalSectionsDegree ℒ n) :
    topSectionMorphism (T^[m + n] ℒ) (gradedGlobalSectionsMul ℒ x y) =
      topSectionMorphism ((T^[m] ℒ) ⊗ₘ (T^[n] ℒ) : ModX)
          (topSectionEquiv ((T^[m] ℒ) ⊗ₘ (T^[n] ℒ) : ModX)
            (tensorSection
              ((topSectionEquiv (T^[m] ℒ)).symm x)
              ((topSectionEquiv (T^[n] ℒ)).symm y))) ≫
        (tensorPowerSheafAddIso ℒ m n).hom := by
  -- Proof comment: commute `topSectionMorphism` past `sectionsMap`, exposing the pure tensor
  -- section before the recursive tensor-power comparison.
  rw [gradedGlobalSectionsMul, topSectionEquiv_sectionsMap]
  simpa using
    (topSectionMorphism_map (tensorPowerSheafAddIso ℒ m n).hom
      (topSectionEquiv ((T^[m] ℒ) ⊗ₘ (T^[n] ℒ) : ModX)
        (tensorSection
          ((topSectionEquiv (T^[m] ℒ)).symm x)
          ((topSectionEquiv (T^[n] ℒ)).symm y))))

/-- Helper for Definition 17.25.7: the unit morphism of a homogeneous action is the pure tensor
unit morphism followed by the recursive twisted-action comparison. -/
private theorem topSectionMorphism_gradedTwistedGlobalSectionsSmul
    [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertibleX ℒ] (ℱ : ModX) {m : ℕ} {n : ℤ}
    (x : gradedGlobalSectionsDegree ℒ m)
    (y : gradedTwistedGlobalSectionsDegree ℒ ℱ n) :
    topSectionMorphism (ℱ ⊗ₘ (ℒ ^⊗ ((m : ℤ) + n))) (gradedTwistedGlobalSectionsSmul ℒ ℱ x y) =
      topSectionMorphism ((T^[m] ℒ) ⊗ₘ (ℱ ⊗ₘ (ℒ ^⊗ n)) : ModX)
          (topSectionEquiv ((T^[m] ℒ) ⊗ₘ (ℱ ⊗ₘ (ℒ ^⊗ n)) : ModX)
            (tensorSection
              ((topSectionEquiv (T^[m] ℒ)).symm x)
              ((topSectionEquiv (ℱ ⊗ₘ (ℒ ^⊗ n) : ModX)).symm y))) ≫
        (gradedTwistedGlobalSectionsActionIso ℒ ℱ m n).hom := by
  -- Proof comment: as for multiplication, move `topSectionMorphism` across `sectionsMap` and
  -- expose the pure tensor section before the recursive action isomorphism.
  rw [gradedTwistedGlobalSectionsSmul, topSectionEquiv_sectionsMap]
  simpa using
    (topSectionMorphism_map (gradedTwistedGlobalSectionsActionIso ℒ ℱ m n).hom
      (topSectionEquiv ((T^[m] ℒ) ⊗ₘ (ℱ ⊗ₘ (ℒ ^⊗ n)) : ModX)
        (tensorSection
          ((topSectionEquiv (T^[m] ℒ)).symm x)
          ((topSectionEquiv (ℱ ⊗ₘ (ℒ ^⊗ n) : ModX)).symm y))))

/-- Definition 17.25.7 (1): `\Gamma_*(X, \mathcal L)` is the direct sum of the nonnegative
tower of global sections, equipped below with its canonical graded ring structure. -/
@[stacks 01CV]
abbrev gradedGlobalSections
    (ℒ : ModX) : Type _ :=
  ⨁ n : ℕ, gradedGlobalSectionsDegree ℒ n

/-- Definition 17.25.7 (2): `\Gamma_*(X, \mathcal L, \mathcal F)` is the direct sum of the
integer-indexed twisted global sections, equipped below with its canonical graded
`Γ_*(X, \mathcal L)`-module structure. -/
@[stacks 01CV]
abbrev gradedTwistedGlobalSections
    (ℒ : ModX) [IsInvertibleX ℒ] (ℱ : ModX) : Type _ :=
  ⨁ n : ℤ, gradedTwistedGlobalSectionsDegree ℒ ℱ n

/-- Textbook notation for the graded ring of global sections `\Gamma_*(X, \mathcal L)`. -/
scoped[AlgebraicGeometry] notation3:max "Γ_*(" ℒ ")" =>
  AlgebraicGeometry.RingedSpace.gradedGlobalSections ℒ

/-- Textbook notation for the graded module of twisted global sections
`\Gamma_*(X, \mathcal L, \mathcal F)`. -/
scoped[AlgebraicGeometry] notation3:max "Γ_*(" ℒ ", " ℱ ")" =>
  AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSections ℒ ℱ

noncomputable instance gradedGlobalSections_gNonUnitalNonAssocSemiring
    (ℒ : ModX) :
    DirectSum.GNonUnitalNonAssocSemiring (gradedGlobalSectionsDegree ℒ) where
  mul := fun {m n} x y ↦ gradedGlobalSectionsMul ℒ x y
  mul_zero := by
    -- Proof comment: move the tensor-power comparison through top evaluation and then use the
    -- zero-right simplification for the pure tensor section.
    intro m n x
    simpa [gradedGlobalSectionsMul, topSectionEquiv_sectionsMap] using
      congrArg ((ΓMod.map (tensorPowerSheafAddIso ℒ m n).hom).hom)
        (topSectionEquiv_tensorSection_zero_right
          (ℱ := T^[m] ℒ) (𝒢 := T^[n] ℒ) x)
  zero_mul := by
    -- Proof comment: the same argument with the zero factor on the left gives the second zero law.
    intro m n y
    simpa [gradedGlobalSectionsMul, topSectionEquiv_sectionsMap] using
      congrArg ((ΓMod.map (tensorPowerSheafAddIso ℒ m n).hom).hom)
        (topSectionEquiv_tensorSection_zero_left
          (ℱ := T^[m] ℒ) (𝒢 := T^[n] ℒ) y)
  mul_add := by
    -- Proof comment: after commuting `sectionsMap` with top evaluation, additivity is exactly the
    -- right-additivity of the pure-top-section tensor construction.
    intro m n x y z
    simpa [gradedGlobalSectionsMul, topSectionEquiv_sectionsMap] using
      congrArg ((ΓMod.map (tensorPowerSheafAddIso ℒ m n).hom).hom)
        (topSectionEquiv_tensorSection_add_right
          (ℱ := T^[m] ℒ) (𝒢 := T^[n] ℒ) x y z)
  add_mul := by
    -- Proof comment: left additivity is the same computation using the left-additivity tensor
    -- helper.
    intro m n x y z
    simpa [gradedGlobalSectionsMul, topSectionEquiv_sectionsMap] using
      congrArg ((ΓMod.map (tensorPowerSheafAddIso ℒ m n).hom).hom)
        (topSectionEquiv_tensorSection_add_left
          (ℱ := T^[m] ℒ) (𝒢 := T^[n] ℒ) x y z)

noncomputable instance gradedGlobalSections_gOne
    (ℒ : ModX) :
    GradedMonoid.GOne (gradedGlobalSectionsDegree ℒ) where
  one := by
    simpa [gradedGlobalSectionsDegree, tensorPowerSheaf] using (1 : ΓX)

noncomputable instance gradedGlobalSections_gSemiring
    (ℒ : ModX) :
    DirectSum.GSemiring (gradedGlobalSectionsDegree ℒ) := sorry

noncomputable instance gradedGlobalSections_gRing
    (ℒ : ModX) :
    DirectSum.GRing (gradedGlobalSectionsDegree ℒ) := sorry

noncomputable instance gradedGlobalSections_gCommRing
    [SymmetricCategory ModX] (ℒ : ModX) :
    DirectSum.GCommRing (gradedGlobalSectionsDegree ℒ) := sorry

noncomputable instance gradedGlobalSections_commRing
    [SymmetricCategory ModX] (ℒ : ModX) :
    CommRing Γ_*(ℒ) := by
  infer_instance

noncomputable instance gradedTwistedGlobalSections_gMulAction
    [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertibleX ℒ] (ℱ : ModX) :
    GradedMonoid.GMulAction
      (gradedGlobalSectionsDegree ℒ)
      (gradedTwistedGlobalSectionsDegree ℒ ℱ) := sorry

noncomputable instance gradedTwistedGlobalSections_gdistribMulAction
    [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertibleX ℒ] (ℱ : ModX) :
    DirectSum.GdistribMulAction
      (gradedGlobalSectionsDegree ℒ)
      (gradedTwistedGlobalSectionsDegree ℒ ℱ) := sorry

noncomputable instance gradedTwistedGlobalSections_gmodule
    [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertibleX ℒ] (ℱ : ModX) :
    DirectSum.Gmodule
      (gradedGlobalSectionsDegree ℒ)
      (gradedTwistedGlobalSectionsDegree ℒ ℱ) := sorry

noncomputable instance gradedTwistedGlobalSections_module
    [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertibleX ℒ] (ℱ : ModX) :
    Module Γ_*(ℒ) Γ_*(ℒ, ℱ) := sorry

@[simp]
theorem gradedTwistedGlobalSections_of_smul_of
    [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertibleX ℒ] (ℱ : ModX) {m : ℕ} {n : ℤ}
    (x : gradedGlobalSectionsDegree ℒ m)
    (y : gradedTwistedGlobalSectionsDegree ℒ ℱ n) :
    DirectSum.of (gradedGlobalSectionsDegree ℒ) m x •
        DirectSum.of (gradedTwistedGlobalSectionsDegree ℒ ℱ) n y =
      DirectSum.of (gradedTwistedGlobalSectionsDegree ℒ ℱ) (m + n)
        (gradedTwistedGlobalSectionsSmul ℒ ℱ x y) := sorry

end RingedSpace

end AlgebraicGeometry
