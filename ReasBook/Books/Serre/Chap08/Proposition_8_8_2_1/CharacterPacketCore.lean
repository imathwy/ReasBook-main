import Mathlib
import Serre.Chap02.Theorem_2_2_3_5

open CategoryTheory

universe u v w x

namespace Representation

noncomputable section

section SemidirectAbelian

variable {A : Type u} [CommGroup A]
variable {H : Type v} [Group H]
variable (φ : H →* MulAut A)

/-- Internal helper: the canonical contragredient `H`-action on the character group of `A`,
obtained from mathlib's precomposition action on monoid homomorphisms. -/
abbrev characterActionHom : H →* Hᵈᵐᵃ :=
  show H →* Hᵈᵐᵃ from (MulEquiv.inv' H).toMonoidHom

abbrev characterMulAction : MulAction H (A →* ℂˣ) := by
  let _ : MulAction H A := MulAction.compHom A φ
  let _ : MulDistribMulAction H A := MulDistribMulAction.compHom A φ
  let _ : MulAction Hᵈᵐᵃ (A →* ℂˣ) := inferInstance
  exact MulAction.compHom (A →* ℂˣ) characterActionHom

@[simp] theorem smul_character_apply
    (h : H) (χ : A →* ℂˣ) (a : A) :
    let _ := characterMulAction φ
    (h • χ : A →* ℂˣ) a = χ ((MulEquiv.symm (φ h)) a) := by
  let _ : MulAction H A := MulAction.compHom A φ
  let _ : MulDistribMulAction H A := MulDistribMulAction.compHom A φ
  let _ : MulAction Hᵈᵐᵃ (A →* ℂˣ) := inferInstance
  change ((characterActionHom h) • χ : A →* ℂˣ) a = χ ((MulEquiv.symm (φ h)) a)
  rw [DomMulAct.smul_monoidHom_apply]
  change χ ((φ h⁻¹) a) = χ ((MulEquiv.symm (φ h)) a)
  simp

/-- A chosen family `χ` is a complete set of representatives for the `H`-orbits in the character
group of `A`. -/
def HasCharacterOrbitRepresentatives (φ : H →* MulAut A) {ι : Type w} (χ : ι → A →* ℂˣ) : Prop :=
  let _ := characterMulAction φ
  Function.Bijective
    (fun i ↦ (Quotient.mk'' (χ i) : MulAction.orbitRel.Quotient H (A →* ℂˣ)))

namespace HasCharacterOrbitRepresentatives

/-- For finite `A`, a complete set of orbit representatives for the `H`-action on the character
group of `A` has a finite index type. -/
theorem finiteIndex [Finite A] {ι : Type w} {χ : ι → A →* ℂˣ}
    (hχ : HasCharacterOrbitRepresentatives φ χ) : Finite ι := by
  classical
  let _ := characterMulAction φ
  exact Finite.of_injective
    (fun i ↦ (Quotient.mk'' (χ i) : MulAction.orbitRel.Quotient H (A →* ℂˣ)))
    hχ.injective

/-- The canonical `Fintype` structure on a complete set of orbit representatives for the
`H`-action on the character group of `A`. -/
noncomputable abbrev fintypeIndex [Finite A] {ι : Type w} {χ : ι → A →* ℂˣ}
    (hχ : HasCharacterOrbitRepresentatives φ χ) : Fintype ι :=
  let _ : Finite ι := finiteIndex φ hχ
  Fintype.ofFinite ι

end HasCharacterOrbitRepresentatives

/-- The stabilizer of the linear character `χ` for the `H`-action induced by `φ`. -/
abbrev characterStabilizer (χ : A →* ℂˣ) : Subgroup H :=
  let _ := characterMulAction φ
  MulAction.stabilizer H χ

scoped notation:max "H_[" φ "; " χ "]" => Representation.characterStabilizer φ χ

open scoped Representation

/-- The restricted action of `H_[φ; χ]` on `A`. -/
abbrev stabilizerAction (χ : A →* ℂˣ) :
    H_[φ; χ] →* MulAut A :=
  φ.comp (Subgroup.subtype H_[φ; χ])

/-- Elements of `H_[φ; χ]` fix the character `χ` after transporting through the action `φ`. -/
theorem characterStabilizer_apply
    (χ : A →* ℂˣ) (h : H_[φ; χ]) (a : A) :
    χ (φ h a) = χ a := by
  let _ := characterMulAction φ
  have hη := congrArg (fun η : A →* ℂˣ ↦ η (φ h a)) h.property
  simpa using hη.symm

/-- The canonical inclusion `A ⋊ H_[φ; χ] → A ⋊ H`. -/
abbrev stabilizerInclusion (χ : A →* ℂˣ) :
    A ⋊[stabilizerAction φ χ] H_[φ; χ] →* A ⋊[φ] H :=
  SemidirectProduct.map (MonoidHom.id A) (Subgroup.subtype H_[φ; χ])
    (fun h ↦ by
      ext a
      rfl)

/-- The extension of `χ` to the subgroup `A ⋊ H_[φ; χ]`, trivial on the second factor. -/
def stabilizerCharacter (χ : A →* ℂˣ) :
    A ⋊[stabilizerAction φ χ] H_[φ; χ] →* ℂˣ :=
  SemidirectProduct.lift χ 1 fun h ↦ by
    ext a
    simp [characterStabilizer_apply φ χ h a]

@[simp] theorem stabilizerCharacter_apply (χ : A →* ℂˣ)
    (x : A ⋊[stabilizerAction φ χ] H_[φ; χ]) :
    stabilizerCharacter φ χ x = χ x.left := by
  change χ x.left * (1 : H_[φ; χ] →* ℂˣ) x.right = χ x.left
  simp

/-- The `A ⋊ H_[φ; χ]`-representation obtained by letting `A` act through `χ` and
`H_[φ; χ]` act through `ρ`. -/
noncomputable def stabilizerRepresentation (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ]) :
    Rep.{w} ℂ (A ⋊[stabilizerAction φ χ] H_[φ; χ]) :=
  Rep.of <| {
    toFun := fun x ↦ (stabilizerCharacter φ χ x : ℂ) • ρ.ρ x.right
    map_one' := by
      ext v
      simp [stabilizerCharacter]
    map_mul' := by
      intro x y
      ext v
      rw [SemidirectProduct.mul_def, map_mul]
      simp [stabilizerCharacter_apply, smul_smul, mul_assoc, characterStabilizer_apply, mul_comm]
  }

/-- Helper for Proposition 8-8.2-1: the packet source on `A ⋊ H_[φ; χ]` is already irreducible,
because the normal `A`-factor acts only by nonzero scalars and does not create new stable
subspaces beyond the `H_[φ; χ]`-stable subspaces of `ρ`. -/
theorem stabilizerRepresentation_isIrreducible
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ]) [ρ.ρ.IsIrreducible] :
    (stabilizerRepresentation φ χ ρ).ρ.IsIrreducible := by
  classical
  let e : Subrepresentation ρ.ρ ≃o
      Subrepresentation (stabilizerRepresentation φ χ ρ).ρ :=
    {
    toFun U :=
      { toSubmodule := U.toSubmodule
        apply_mem_toSubmodule := by
          intro g x hx
          change ((stabilizerCharacter φ χ g : ℂ) • ρ.ρ g.right x) ∈ U.toSubmodule
          exact Submodule.smul_mem _ _ (U.apply_mem_toSubmodule g.right hx) }
    invFun U :=
      { toSubmodule := U.toSubmodule
        apply_mem_toSubmodule := by
          intro h x hx
          have hx' :
              (stabilizerRepresentation φ χ ρ).ρ ⟨1, h⟩ x ∈ U.toSubmodule :=
            U.apply_mem_toSubmodule ⟨1, h⟩ hx
          have hEqx :
              (stabilizerRepresentation φ χ ρ).ρ ⟨1, h⟩ x = ρ.ρ h x := by
            change ((stabilizerCharacter φ χ (SemidirectProduct.inr h) : ℂ) • ρ.ρ h x) =
              ρ.ρ h x
            simp [stabilizerCharacter_apply]
          exact hEqx ▸ hx' }
    left_inv U := by
      rfl
    right_inv U := by
      rfl
    map_rel_iff' := by
      intro U V
      rfl
    }
  exact e.isSimpleOrder_iff.mp inferInstance

/-- Serre's representation `θ_{χ,ρ}` on `A ⋊[φ] H`, obtained by inducing the representation of
`A ⋊ H_[φ; χ]` defined by the character `χ` and the irreducible representation `ρ` of
`H_[φ; χ]`. -/
noncomputable abbrev theta (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ]) :
    Rep.{max u v w} ℂ (A ⋊[φ] H) :=
  Rep.ind (stabilizerInclusion φ χ) (stabilizerRepresentation φ χ ρ)

scoped notation:max "θ[" φ "; " χ ", " ρ "]" => Representation.theta φ χ ρ

end SemidirectAbelian

end

end Representation
