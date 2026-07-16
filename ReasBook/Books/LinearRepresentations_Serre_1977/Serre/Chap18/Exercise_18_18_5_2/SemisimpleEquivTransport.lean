import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_5_2.LinearCharacters
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_5_2.OrdinaryExplicitModels
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_5_2.SemisimpleS4Irreducible

/-!
# Characteristic-uniform irreducibility transport (support for Exercise 18.5.2)

This file ports to an *arbitrary* field `F` the irreducibility-transport infrastructure that the
`ℂ`-only file `OrdinaryExplicitModels.lean` provides only over `ℂ`:

* `isIrreducible_of_equiv_overField` — irreducibility transports across a `Representation.Equiv`;
* `isIrreducible_comp_of_mulEquiv_overField` — precomposing with a group equivalence preserves it;
* `ulift_group_carrier_representation_isIrreducible_iff_overField` — `ULift`-lifting both the group
  and the carrier preserves irreducibility;
* `tprod_unitCharacter_preserves_isIrreducible_overField` — tensoring by a one-dimensional
  (unit-valued) character preserves irreducibility.

These supersede the `ℂ`-only `OrdinaryExplicitModels` versions for the semisimple branch
`ringChar k ∉ {2, 3}` of the completeness statement, where the five explicit models must be shown
irreducible over the algebraically closed coefficient field `k` (of arbitrary characteristic).
-/

attribute [-instance] Field.henselian

noncomputable section

open Representation

namespace Representation

section

local notation "S3" => Equiv.Perm (Fin 3)
local notation "S4" => Equiv.Perm (Fin 4)

universe w

/-- Helper for Exercise 18-18.5-2: a representation equivalence induces an order isomorphism on
subrepresentations (field-general port of `subrepresentationOrderIso_oem`). -/
noncomputable def subrepresentationOrderIso_overField
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V' : Type*} [AddCommGroup V'] [Module F V']
    {W' : Type*} [AddCommGroup W'] [Module F W']
    {ρ : Representation F G V'} {σ : Representation F G W'} (e : ρ.Equiv σ) :
    Subrepresentation ρ ≃o Subrepresentation σ where
  toFun U :=
    { toSubmodule := U.toSubmodule.map e.toLinearMap
      apply_mem_toSubmodule := by
        intro g x hx
        rcases hx with ⟨y, hy, rfl⟩
        refine ⟨ρ g y, U.apply_mem_toSubmodule g hy, ?_⟩
        simp [e.isIntertwining] }
  invFun U :=
    { toSubmodule := U.toSubmodule.map e.symm.toLinearMap
      apply_mem_toSubmodule := by
        intro g x hx
        rcases hx with ⟨y, hy, rfl⟩
        refine ⟨σ g y, U.apply_mem_toSubmodule g hy, ?_⟩
        simp [e.symm.isIntertwining] }
  left_inv U := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have : y = e x := by simpa using congrArg e hxy
      subst this
      simpa using hy
    · intro hx
      change x ∈ Submodule.map e.symm.toLinearMap (Submodule.map e.toLinearMap U.toSubmodule)
      exact ⟨e x, ⟨x, hx, rfl⟩, by simp⟩
  right_inv U := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have : y = e.symm x := by simpa using congrArg e.symm hxy
      subst this
      simpa using hy
    · intro hx
      change x ∈ Submodule.map e.toLinearMap (Submodule.map e.symm.toLinearMap U.toSubmodule)
      exact ⟨e.symm x, ⟨x, hx, rfl⟩, by simp⟩
  map_rel_iff' := by
    intro U U'
    constructor
    · intro h x hx
      have hx' : e x ∈ U.toSubmodule.map e.toLinearMap := ⟨x, hx, rfl⟩
      rcases h hx' with ⟨y, hy, hxy⟩
      have : y = x := by
        apply e.toLinearEquiv.injective
        simp [hxy]
      simpa [this] using hy
    · intro h x hx
      rcases hx with ⟨y, hy, rfl⟩
      exact ⟨y, h hy, rfl⟩

/-- Helper for Exercise 18-18.5-2: irreducibility transports across a representation equivalence
(field-general port of `isIrreducible_of_equiv_oem`). -/
lemma isIrreducible_of_equiv_overField
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V' : Type*} [AddCommGroup V'] [Module F V']
    {W' : Type*} [AddCommGroup W'] [Module F W']
    {ρ : Representation F G V'} {σ : Representation F G W'}
    [ρ.IsIrreducible] (e : ρ.Equiv σ) : σ.IsIrreducible :=
  (subrepresentationOrderIso_overField e).isSimpleOrder_iff.mp inferInstance

/-- Helper for Exercise 18-18.5-2: precomposing an irreducible representation with a group
equivalence preserves irreducibility (field-general port). -/
lemma isIrreducible_comp_of_mulEquiv_overField
    {F : Type*} [Field F] {G H : Type*} [Group G] [Group H]
    {W : Type*} [AddCommGroup W] [Module F W]
    (e : G ≃* H) (σ : Representation F H W) [σ.IsIrreducible] :
    Representation.IsIrreducible (σ.comp e.toMonoidHom) := by
  classical
  letI : Nontrivial (Subrepresentation (σ.comp e.toMonoidHom)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation σ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using congrArg Subrepresentation.toSubmodule h
    exact IsSimpleOrder.bot_ne_top h'
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro U hU
  let U' : Subrepresentation σ :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := by
        intro h x hx
        simpa using U.apply_mem_toSubmodule (e.symm h) hx }
  have hU'_ne_bot : U' ≠ ⊥ := by
    intro hU'
    apply hU
    apply Subrepresentation.toSubmodule_injective
    simpa [U'] using congrArg Subrepresentation.toSubmodule hU'
  have hU'_top : U' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U').resolve_left hU'_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [U'] using congrArg Subrepresentation.toSubmodule hU'_top

/-- Helper for Exercise 18-18.5-2: lifting the carrier by `ULift` yields an equivalent
representation on the original carrier (field-general port of `ulift_carrier_representation_equiv`). -/
noncomputable def ulift_carrier_representation_equiv_overField
    {F : Type w} [Field F] {G : Type*} [Monoid G]
    {W : Type w} [AddCommGroup W] [Module F W]
    (ρ : Representation F G W) :
    (ulift_carrier_representation ρ).Equiv ρ :=
  Representation.Equiv.mk ULift.moduleEquiv <| by
    intro g
    ext x
    rfl

/-- Helper for Exercise 18-18.5-2: simultaneously lifting the group and carrier preserves
irreducibility over an arbitrary field (field-general port of the `ℂ`-only iff). -/
lemma ulift_group_carrier_representation_isIrreducible_iff_overField
    {F : Type w} [Field F] {G : Type*} [Group G]
    {W : Type w} [AddCommGroup W] [Module F W]
    (ρ : Representation F G W) :
    (ulift_group_carrier_representation ρ).IsIrreducible ↔ ρ.IsIrreducible := by
  constructor
  · intro hρ
    let ρcomp : Representation F (ULift G) W := ρ.comp (MulEquiv.ulift.toMonoidHom)
    letI : (ulift_group_carrier_representation ρ).IsIrreducible := hρ
    have hcomp : ρcomp.IsIrreducible :=
      isIrreducible_of_equiv_overField
        (ρ := ulift_group_carrier_representation ρ)
        (σ := ρcomp)
        (ulift_carrier_representation_equiv_overField ρcomp)
    letI : ρcomp.IsIrreducible := hcomp
    simpa [ρcomp] using
      (isIrreducible_comp_of_mulEquiv_overField (e := MulEquiv.ulift.symm) (σ := ρcomp))
  · intro hρ
    let ρcomp : Representation F (ULift G) W := ρ.comp (MulEquiv.ulift.toMonoidHom)
    letI : ρ.IsIrreducible := hρ
    have hcomp : ρcomp.IsIrreducible := by
      simpa [ρcomp] using
        (isIrreducible_comp_of_mulEquiv_overField (e := MulEquiv.ulift) (σ := ρ))
    letI : ρcomp.IsIrreducible := hcomp
    exact
      isIrreducible_of_equiv_overField
        (ρ := ρcomp)
        (σ := ulift_group_carrier_representation ρ)
        (ulift_carrier_representation_equiv_overField ρcomp).symm

/-- Helper for Exercise 18-18.5-2: the same-carrier twist of a representation by a linear
character (field-general port of `unitCharacterTwistRepresentation`). -/
abbrev unitCharacterTwistRepresentation_overField
    {F : Type*} [Field F] {G : Type*} [Group G]
    {W : Type*} [AddCommGroup W] [Module F W]
    (β : G →* Fˣ) (σ : Representation F G W) :
    Representation F G W where
  toFun g := ((β g : Fˣ) : F) • σ g
  map_one' := by
    apply LinearMap.ext; intro x; simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    have hβ : ((β (g * h) : Fˣ) : F) = ((β g : Fˣ) : F) * ((β h : Fˣ) : F) := by simp
    rw [hβ]
    simp [smul_smul, mul_comm]

/-- Helper for Exercise 18-18.5-2: the tensor product with a degree-`1` character is equivalent to
the corresponding same-carrier scalar twist (field-general port). -/
noncomputable def unitCharacterTensorTwistEquiv_overField
    {F : Type*} [Field F] {G : Type*} [Group G]
    {W : Type*} [AddCommGroup W] [Module F W]
    (β : G →* Fˣ) (σ : Representation F G W) :
    ((unitCharacterRepresentation β).tprod σ).Equiv
      (unitCharacterTwistRepresentation_overField β σ) := by
  refine Representation.Equiv.mk (_root_.TensorProduct.lid F W) ?_
  intro g
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro c w
    simp [TensorProduct.lid_tmul, unitCharacterRepresentation,
      unitCharacterTwistRepresentation_overField, LinearMap.lsmul_apply, smul_smul, mul_comm]
  · intro z₁ z₂ hz₁ hz₂
    simpa [map_add] using congrArg₂ HAdd.hAdd hz₁ hz₂

/-- Helper for Exercise 18-18.5-2: the same-carrier scalar twist of an irreducible representation
is again irreducible (field-general port). -/
lemma unitCharacterTwistRepresentation_isIrreducible_overField
    {F : Type*} [Field F] {G : Type*} [Group G]
    {W : Type*} [AddCommGroup W] [Module F W]
    (β : G →* Fˣ) (σ : Representation F G W) [σ.IsIrreducible] :
    Representation.IsIrreducible (unitCharacterTwistRepresentation_overField β σ) := by
  letI : Nontrivial (Subrepresentation (unitCharacterTwistRepresentation_overField β σ)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation σ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using congrArg Subrepresentation.toSubmodule h
    exact IsSimpleOrder.bot_ne_top h'
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro U hU
  let U' : Subrepresentation σ :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := by
        intro g x hx
        have hxTwist : ((unitCharacterTwistRepresentation_overField β σ) g) x ∈ U.toSubmodule :=
          U.apply_mem_toSubmodule g hx
        have hxScaled :
            (((((β g : Fˣ) : F))⁻¹) • (((unitCharacterTwistRepresentation_overField β σ) g) x)) ∈
              U.toSubmodule :=
          U.toSubmodule.smul_mem _ hxTwist
        simpa [unitCharacterTwistRepresentation_overField, smul_smul] using hxScaled }
  have hU'_ne_bot : U' ≠ ⊥ := by
    intro hU'
    apply hU
    apply Subrepresentation.toSubmodule_injective
    simpa [U'] using congrArg Subrepresentation.toSubmodule hU'
  have hU'_top : U' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U').resolve_left hU'_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [U'] using congrArg Subrepresentation.toSubmodule hU'_top

/-- Helper for Exercise 18-18.5-2: tensoring an irreducible representation with a unit-valued
character preserves irreducibility (field-general port). -/
lemma tprod_unitCharacter_preserves_isIrreducible_overField
    {F : Type*} [Field F] {G : Type*} [Group G]
    {W : Type*} [AddCommGroup W] [Module F W]
    (β : G →* Fˣ) (σ : Representation F G W) [σ.IsIrreducible] :
    Representation.IsIrreducible ((unitCharacterRepresentation β).tprod σ) := by
  letI : Representation.IsIrreducible (unitCharacterTwistRepresentation_overField β σ) :=
    unitCharacterTwistRepresentation_isIrreducible_overField β σ
  exact isIrreducible_of_equiv_overField
    (ρ := unitCharacterTwistRepresentation_overField β σ)
    (σ := (unitCharacterRepresentation β).tprod σ)
    (unitCharacterTensorTwistEquiv_overField β σ).symm

end

end Representation
