import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.FieldDenominatorPrelude

noncomputable section

open scoped Representation.ExternalTensor

universe u v w

namespace Representation

open CategoryTheory

namespace Exercise_12_12_2_6

section FieldLift

variable {L : Type w} [Field L] [CharZero L]
variable {G0 : Type v} [Group G0] [Finite G0]
variable {V : Type*} [AddCommGroup V] [Module L V] [FiniteDimensional L V]

/-- Helper for Exercise 12-12.2-6: precomposing with a group equivalence preserves irreducibility
without forcing the field and group into the same universe. -/
private theorem isIrreducible_comp_of_mulEquiv_univ_local
    {H : Type*} [Group H]
    (e : G0 ≃* H)
    (σ : Representation L H V)
    [σ.IsIrreducible] :
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
  intro W hW
  let W' : Subrepresentation σ :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        intro h x hx
        simpa using W.apply_mem_toSubmodule (e.symm h) hx }
  have hW'_ne_bot : W' ≠ ⊥ := by
    intro hW'
    apply hW
    apply Subrepresentation.toSubmodule_injective
    simpa [W'] using congrArg Subrepresentation.toSubmodule hW'
  have hW'_top : W' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W').resolve_left hW'_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [W'] using congrArg Subrepresentation.toSubmodule hW'_top

/-- Helper for Exercise 12-12.2-6: conjugating by a linear equivalence preserves the identity
operator even when the group lives in a different universe from the field. -/
private theorem conjRepresentation_map_one_univ_local
    {H : Type*} [Group H]
    {V1 : Type*} {W1 : Type*}
    [AddCommGroup V1] [Module L V1] [AddCommGroup W1] [Module L W1]
    (e : V1 ≃ₗ[L] W1) (ρ : Representation L H V1) :
    e.conj (ρ 1) = 1 := by
  calc
    e.conj (ρ 1) = e.conj 1 := by rw [map_one]
    _ = 1 := LinearEquiv.conj_id e

/-- Helper for Exercise 12-12.2-6: conjugating by a linear equivalence preserves the
representation law across the universe-separated coordinate model. -/
private theorem conjRepresentation_map_mul_univ_local
    {H : Type*} [Group H]
    {V1 : Type*} {W1 : Type*}
    [AddCommGroup V1] [Module L V1] [AddCommGroup W1] [Module L W1]
    (e : V1 ≃ₗ[L] W1) (ρ : Representation L H V1) (g h : H) :
    e.conj (ρ (g * h)) = e.conj (ρ g) * e.conj (ρ h) := by
  rw [map_mul]
  ext x
  simp [LinearEquiv.conj_apply_apply]

/-- Helper for Exercise 12-12.2-6: move a finite-dimensional representation to finite-basis
coordinates without assuming the field and group share a universe. -/
private def finBasisRepresentation_univ_local
    {H : Type*} [Group H]
    {V1 : Type*} [AddCommGroup V1] [Module L V1] [FiniteDimensional L V1]
    (ρ : Representation L H V1) :
    Representation L H (Fin (Module.finrank L V1) → L) :=
  let e := (Module.finBasis L V1).equivFun
  { toFun := fun g ↦ e.conj (ρ g)
    map_one' := conjRepresentation_map_one_univ_local (L := L) e ρ
    map_mul' := fun g h ↦ conjRepresentation_map_mul_univ_local (L := L) e ρ g h }

/-- Helper for Exercise 12-12.2-6: first lift only the group through `ULift`, keeping the
original field and carrier so the source irreducibility route stays visible. -/
def rho_ulift_group_local (ρ : Representation L G0 V) :
    Representation L (ULift.{max v w} G0) V :=
  ρ.comp ((MulEquiv.ulift : ULift.{max v w} G0 ≃* G0).toMonoidHom)

attribute [local instance] ULift.algebra'

/-- Helper for Exercise 12-12.2-6: restriction of scalars along `ULift.algebra'` turns an
`L`-representation into a `ULift L`-representation without changing the action operators. -/
def restrictScalars_rep_local
    {H : Type*} [Group H]
    {W1 : Type*} [AddCommGroup W1] [Module L W1]
    (ρ : Representation L H W1) :
    Representation (ULift.{max v w} L) H W1 where
  toFun g := (ρ g).restrictScalars (ULift.{max v w} L)
  map_one' := by
    -- Restriction of scalars does not change the underlying function.
    ext x
    simp
  map_mul' g h := by
    -- The multiplication law is inherited verbatim after restricting scalars.
    ext x
    simp [map_mul]

/-- Helper for Exercise 12-12.2-6: `ULift L` still has characteristic zero, so the Chapter 3
owner lemmas over the lifted field type can be applied directly. -/
private instance uliftCharZero_local : CharZero (ULift.{max v w} L) where
  cast_injective n m h := by
    apply Nat.cast_injective (R := L)
    simpa using congrArg ULift.down h

/-- Helper for Exercise 12-12.2-6: restricting scalars along `ULift L → L` preserves
irreducibility because `ULift L`-stable subrepresentations are the same underlying invariant
submodules. -/
private theorem restrictScalars_rep_isIrreducible_local
    {H : Type*} [Group H]
    {W1 : Type*} [AddCommGroup W1] [Module L W1]
    (π : Representation L H W1)
    [π.IsIrreducible] :
    Representation.IsIrreducible (restrictScalars_rep_local (L := L) (ρ := π)) := by
  classical
  letI : Nontrivial (Subrepresentation (restrictScalars_rep_local (L := L) (ρ := π))) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation π) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      ext x
      change x ∈ ((⊥ : Subrepresentation (restrictScalars_rep_local (L := L) (ρ := π))).toSubmodule) ↔
        x ∈ ((⊤ : Subrepresentation (restrictScalars_rep_local (L := L) (ρ := π))).toSubmodule)
      simpa using congrArg (fun W => x ∈ W.toSubmodule) h
    exact IsSimpleOrder.bot_ne_top h'
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro W hW
  let W' : Subrepresentation π :=
    { toSubmodule :=
        { carrier := W.toSubmodule
          zero_mem' := W.toSubmodule.zero_mem'
          add_mem' := W.toSubmodule.add_mem'
          smul_mem' := by
            intro a x hx
            change ((show ULift L from ⟨a⟩) • x) ∈ W.toSubmodule
            exact W.toSubmodule.smul_mem (show ULift L from ⟨a⟩) hx }
      apply_mem_toSubmodule := by
        intro h x hx
        simpa [restrictScalars_rep_local] using W.apply_mem_toSubmodule h hx }
  have hW'_ne_bot : W' ≠ ⊥ := by
    intro hW'
    apply hW
    apply Subrepresentation.toSubmodule_injective
    ext x
    change x ∈ W.toSubmodule ↔ x ∈ ((⊥ : Subrepresentation π).toSubmodule)
    simpa [W'] using congrArg (fun U => x ∈ U.toSubmodule) hW'
  have hW'_top : W' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W').resolve_left hW'_ne_bot
  apply Subrepresentation.toSubmodule_injective
  ext x
  constructor
  · intro _
    exact Submodule.mem_top
  · intro _
    have hx : x ∈ (W' : Subrepresentation π).toSubmodule := by
      simpa [hW'_top] using (show x ∈ ((⊤ : Subrepresentation π).toSubmodule) from Submodule.mem_top)
    simpa [W'] using hx

/-- Helper for Exercise 12-12.2-6: restricting scalars along `ULift L → L` also reflects
irreducibility, so once the lifted-field owner is reduced back to the restricted public tensor we
may return to the original `L`-representation without reopening the submodule argument. -/
theorem restrictScalars_rep_reflects_irreducible_local
    {H : Type*} [Group H]
    {W1 : Type*} [AddCommGroup W1] [Module L W1]
    (π : Representation L H W1)
    (hπ :
      Representation.IsIrreducible
        (restrictScalars_rep_local (L := L) (ρ := π))) :
    Representation.IsIrreducible π := by
  classical
  letI : Representation.IsIrreducible
      (restrictScalars_rep_local (L := L) (ρ := π)) := hπ
  letI : Nontrivial (Subrepresentation π) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation (restrictScalars_rep_local (L := L) (ρ := π))) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      ext x
      change x ∈ ((⊥ : Subrepresentation π).toSubmodule) ↔
        x ∈ ((⊤ : Subrepresentation π).toSubmodule)
      simpa using congrArg (fun W => x ∈ W.toSubmodule) h
    exact IsSimpleOrder.bot_ne_top h'
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro W hW
  let W' : Subrepresentation (restrictScalars_rep_local (L := L) (ρ := π)) :=
    { toSubmodule :=
        { carrier := W.toSubmodule
          zero_mem' := W.toSubmodule.zero_mem'
          add_mem' := W.toSubmodule.add_mem'
          smul_mem' := by
            intro a x hx
            exact W.toSubmodule.smul_mem a.down hx }
      apply_mem_toSubmodule := by
        intro h x hx
        simpa [restrictScalars_rep_local] using W.apply_mem_toSubmodule h hx }
  have hW'_ne_bot : W' ≠ ⊥ := by
    intro hW'
    apply hW
    apply Subrepresentation.toSubmodule_injective
    ext x
    change x ∈ W.toSubmodule ↔ x ∈ ((⊥ : Subrepresentation (restrictScalars_rep_local (L := L) (ρ := π))).toSubmodule)
    simpa [W'] using congrArg (fun U => x ∈ U.toSubmodule) hW'
  have hW'_top : W' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W').resolve_left hW'_ne_bot
  apply Subrepresentation.toSubmodule_injective
  ext x
  constructor
  · intro _
    exact Submodule.mem_top
  · intro _
    have hx : x ∈ (W' : Subrepresentation (restrictScalars_rep_local (L := L) (ρ := π))).toSubmodule := by
      rw [hW'_top]
      exact Submodule.mem_top
    simpa [W'] using hx

/-- Helper for Exercise 12-12.2-6: the finite-basis coordinate model is equivariantly the same
representation, so irreducibility survives this carrier transport. -/
private theorem finBasisRepresentation_univ_isIrreducible_local
    {H : Type*} [Group H]
    {V1 : Type*} [AddCommGroup V1] [Module L V1] [FiniteDimensional L V1]
    (ρ : Representation L H V1)
    [ρ.IsIrreducible] :
    Representation.IsIrreducible (finBasisRepresentation_univ_local (L := L) (ρ := ρ)) := by
  -- The chosen finite basis gives a representation equivalence with the coordinate model.
  exact
    isIrreducible_of_nonempty_equiv
      (ρ := ρ)
      (σ := finBasisRepresentation_univ_local (L := L) (ρ := ρ))
      ⟨Representation.Equiv.mk (Module.finBasis L V1).equivFun fun g => by
        ext x i
        simp [finBasisRepresentation_univ_local, LinearEquiv.conj_apply_apply]⟩

/-- Helper for Exercise 12-12.2-6: the final coefficientwise `ULift` on the coordinate field is
again just a conjugation by a linear equivalence, so irreducibility is preserved. -/
private theorem lifted_field_coordinate_rep_isIrreducible_local
    {H : Type*} [Group H]
    {n : ℕ}
    (π : Representation (ULift.{max v w} L) H (Fin n → L))
    [π.IsIrreducible] :
    let e : (Fin n → L) ≃ₗ[ULift.{max v w} L] (Fin n → ULift.{max v w} L) :=
      LinearEquiv.piCongrRight fun _ =>
        (ULift.moduleEquiv.symm : L ≃ₗ[ULift.{max v w} L] ULift.{max v w} L)
    let πu :
        Representation (ULift.{max v w} L) H (Fin n → ULift.{max v w} L) :=
      { toFun := fun g ↦ e.conj (π g)
        map_one' := conjRepresentation_map_one_univ_local (L := ULift.{max v w} L) e π
        map_mul' := fun g h ↦ conjRepresentation_map_mul_univ_local
          (L := ULift.{max v w} L) e π g h }
    Representation.IsIrreducible πu := by
  classical
  dsimp
  -- This last transport is again an explicit representation equivalence.
  exact
    isIrreducible_of_nonempty_equiv
      (ρ := π)
      (σ := {
        toFun := fun g ↦
          (LinearEquiv.piCongrRight fun _ =>
            (ULift.moduleEquiv.symm : L ≃ₗ[ULift.{max v w} L] ULift.{max v w} L)).conj (π g)
        map_one' := conjRepresentation_map_one_univ_local (L := ULift.{max v w} L)
          (LinearEquiv.piCongrRight fun _ =>
            (ULift.moduleEquiv.symm : L ≃ₗ[ULift.{max v w} L] ULift.{max v w} L)) π
        map_mul' := fun g h ↦ conjRepresentation_map_mul_univ_local (L := ULift.{max v w} L)
          (LinearEquiv.piCongrRight fun _ =>
            (ULift.moduleEquiv.symm : L ≃ₗ[ULift.{max v w} L] ULift.{max v w} L)) π g h })
      ⟨Representation.Equiv.mk
        (LinearEquiv.piCongrRight fun _ =>
          (ULift.moduleEquiv.symm : L ≃ₗ[ULift.{max v w} L] ULift.{max v w} L))
        fun g => by
          ext x i
          rfl⟩

/-- Helper for Exercise 12-12.2-6: the same-universe lifted-field owner used to feed Chapter 3
`externalTensor_simple`. The owner is now bundled from an explicit coordinate representation,
separating the scalar transport from the final `FDRep.of` step. -/
noncomputable def lifted_field_basis_fdRep_local
    (ρ : Representation L G0 V) :
    FDRep (ULift.{max v w} L) (ULift.{max v w} G0) :=
  let π : Representation (ULift.{max v w} L) (ULift.{max v w} G0)
      (Fin (Module.finrank L V) → L) :=
    restrictScalars_rep_local (L := L)
      (ρ := finBasisRepresentation_univ_local (L := L)
        (ρ := rho_ulift_group_local (L := L) (G0 := G0) (V := V) ρ))
  let e : (Fin (Module.finrank L V) → L) ≃ₗ[ULift.{max v w} L]
      (Fin (Module.finrank L V) → ULift.{max v w} L) :=
    LinearEquiv.piCongrRight fun _ =>
      (ULift.moduleEquiv.symm : L ≃ₗ[ULift.{max v w} L] ULift.{max v w} L)
  let πu :
      Representation (ULift.{max v w} L) (ULift.{max v w} G0)
        (Fin (Module.finrank L V) → ULift.{max v w} L) :=
    { toFun := fun g ↦ e.conj (π g)
      map_one' := conjRepresentation_map_one_local (K := ULift.{max v w} L)
        (G := ULift.{max v w} G0) e π
      map_mul' := fun g h ↦ conjRepresentation_map_mul_local (K := ULift.{max v w} L)
        (G := ULift.{max v w} G0) e π g h }
  -- Route correction: the owner itself is now explicit; the remaining proof debt is only the
  -- irreducibility/simplicity bridge for this transported coordinate model.
  FDRep.of πu

/-- Helper for Exercise 12-12.2-6: the last coefficientwise `ULift` in
`lifted_field_basis_fdRep_local` is only a carrier conjugation, so the lifted owner is
equivariantly the same as the scalar-restricted finite-basis model. -/
noncomputable def lifted_field_basis_to_restrictScalars_finBasis_equiv_local
    (ρ : Representation L G0 V) :
    Representation.Equiv
      (lifted_field_basis_fdRep_local (L := L) (G0 := G0) (V := V) ρ).ρ
      (restrictScalars_rep_local (L := L)
        (ρ := finBasisRepresentation_univ_local (L := L)
          (ρ := rho_ulift_group_local (L := L) (G0 := G0) (V := V) ρ))) := by
  let π₁ : Representation L (ULift.{max v w} G0) V :=
    rho_ulift_group_local (L := L) (G0 := G0) (V := V) ρ
  let π₂ : Representation L (ULift.{max v w} G0) (Fin (Module.finrank L V) → L) :=
    finBasisRepresentation_univ_local (L := L) (ρ := π₁)
  let π₃ : Representation (ULift.{max v w} L) (ULift.{max v w} G0)
      (Fin (Module.finrank L V) → L) :=
    restrictScalars_rep_local (L := L) (ρ := π₂)
  let e : (Fin (Module.finrank L V) → L) ≃ₗ[ULift.{max v w} L]
      (Fin (Module.finrank L V) → ULift.{max v w} L) :=
    LinearEquiv.piCongrRight fun _ =>
      (ULift.moduleEquiv.symm : L ≃ₗ[ULift.{max v w} L] ULift.{max v w} L)
  -- The final owner stage is just conjugation by the coefficientwise `ULift` linear equivalence.
  refine Representation.Equiv.mk e.symm ?_
  intro g
  ext x i
  rfl

/-- Helper for Exercise 12-12.2-6: after undoing the coordinate conjugation, the remaining
finite-basis model is equivariantly the same as the restricted public group-`ULift`
representation. -/
noncomputable def lifted_field_basis_to_restrictScalars_group_ulift_equiv_local
    (ρ : Representation L G0 V) :
    Representation.Equiv
      (lifted_field_basis_fdRep_local (L := L) (G0 := G0) (V := V) ρ).ρ
      (restrictScalars_rep_local (L := L)
        (ρ := rho_ulift_group_local (L := L) (G0 := G0) (V := V) ρ)) := by
  let π₁ : Representation L (ULift.{max v w} G0) V :=
    rho_ulift_group_local (L := L) (G0 := G0) (V := V) ρ
  let π₂ : Representation L (ULift.{max v w} G0) (Fin (Module.finrank L V) → L) :=
    finBasisRepresentation_univ_local (L := L) (ρ := π₁)
  let π₃ : Representation (ULift.{max v w} L) (ULift.{max v w} G0)
      (Fin (Module.finrank L V) → L) :=
    restrictScalars_rep_local (L := L) (ρ := π₂)
  let eBasis :
      (Fin (Module.finrank L V) → L) ≃ₗ[ULift.{max v w} L] V :=
    ((Module.finBasis L V).equivFun.symm).restrictScalars (ULift.{max v w} L)
  have hcoeff :
      Representation.Equiv
        (lifted_field_basis_fdRep_local (L := L) (G0 := G0) (V := V) ρ).ρ
        π₃ :=
    lifted_field_basis_to_restrictScalars_finBasis_equiv_local
      (L := L) (G0 := G0) (V := V) ρ
  have hbasis : Representation.Equiv π₃ (restrictScalars_rep_local (L := L) (ρ := π₁)) := by
    -- The finite-basis representation is defined by conjugation with `Module.finBasis.equivFun`,
    -- so the inverse basis equivalence returns to the public carrier.
    refine Representation.Equiv.mk eBasis ?_
    intro g
    ext x
    simp [π₁, π₂, π₃, eBasis, finBasisRepresentation_univ_local, restrictScalars_rep_local]
  exact hcoeff.trans hbasis

/-- Helper for Exercise 12-12.2-6: scalar restriction along `ULift L → L` commutes with external
tensor products after the canonical tensor identification. -/
noncomputable def restrictScalars_externalTensor_equiv_local
    {H : Type v} [Group H]
    {W : Type*} [AddCommGroup W] [Module L W]
    (σ : Representation L G0 V) (τ : Representation L H W) :
    Representation.Equiv
      (Representation.tprod
        ((restrictScalars_rep_local (L := L) (ρ := σ)).comp (MonoidHom.fst G0 H))
        ((restrictScalars_rep_local (L := L) (ρ := τ)).comp (MonoidHom.snd G0 H)))
      (restrictScalars_rep_local (L := L)
        (ρ := Representation.tprod
          (σ.comp (MonoidHom.fst G0 H))
          (τ.comp (MonoidHom.snd G0 H)))) := by
  let f : TensorProduct (ULift.{max v w} L) V W →ₗ[ULift.{max v w} L] TensorProduct L V W :=
    TensorProduct.lift <|
      LinearMap.mk₂ (ULift.{max v w} L) (fun v w ↦ TensorProduct.tmul L v w)
        (fun v₁ v₂ w ↦ TensorProduct.add_tmul v₁ v₂ w)
        (fun a v w ↦ by
          change (a.down • v) ⊗ₜ[L] w = a.down • (v ⊗ₜ[L] w)
          exact (TensorProduct.smul_tmul' a.down v w).symm)
        (fun v w₁ w₂ ↦ TensorProduct.tmul_add v w₁ w₂)
        (fun a v w ↦ by
          change v ⊗ₜ[L] (a.down • w) = a.down • (v ⊗ₜ[L] w)
          exact (TensorProduct.tmul_smul a.down v w).trans rfl)
  let gL : TensorProduct L V W →ₗ[L] TensorProduct (ULift.{max v w} L) V W :=
    TensorProduct.lift <|
      LinearMap.mk₂ L (fun v w ↦ TensorProduct.tmul (ULift.{max v w} L) v w)
        (fun v₁ v₂ w ↦ TensorProduct.add_tmul v₁ v₂ w)
        (fun a v w ↦ by
          change (a • v) ⊗ₜ[ULift.{max v w} L] w = a • (v ⊗ₜ[ULift.{max v w} L] w)
          exact (TensorProduct.smul_tmul' a v w).symm)
        (fun v w₁ w₂ ↦ TensorProduct.tmul_add v w₁ w₂)
        (fun a v w ↦ by
          change v ⊗ₜ[ULift.{max v w} L] (a • w) = a • (v ⊗ₜ[ULift.{max v w} L] w)
          exact (TensorProduct.tmul_smul a v w).trans rfl)
  let g :
      TensorProduct L V W →ₗ[ULift.{max v w} L] TensorProduct (ULift.{max v w} L) V W :=
    { toFun := gL
      map_add' := gL.map_add
      map_smul' := by
        intro a x
        refine TensorProduct.induction_on x ?_ ?_ ?_
        · simp [gL]
        · intro v w
          change (a.down • v) ⊗ₜ[ULift.{max v w} L] w =
              a.down • (v ⊗ₜ[ULift.{max v w} L] w)
          exact (TensorProduct.smul_tmul' a.down v w).symm
        · intro x y _ _
          simp [gL] }
  let e : TensorProduct (ULift.{max v w} L) V W ≃ₗ[ULift.{max v w} L] TensorProduct L V W :=
    LinearEquiv.ofLinear f g
      (by
        ext x : 1
        ext v w : 2
        rfl)
      (by
        ext x : 1
        ext v w : 2
        rfl)
  refine Representation.Equiv.mk e ?_
  intro g0
  -- On pure tensors, both restricted actions are still the original tensor action.
  ext x y
  rfl

/-- Helper for Exercise 12-12.2-6: after lifting each factor group by `ULift`, their external
tensor product is the visible public tensor representation over the product `ULift` group. -/
noncomputable def rho_ulift_externalTensor_local
    {H : Type v} [Group H] [Finite H]
    {W : Type*} [AddCommGroup W] [Module L W] [FiniteDimensional L W]
    (σ : Representation L G0 V) (τ : Representation L H W) :
    Representation L (ULift.{max v w} G0 × ULift.{max v w} H) (TensorProduct L V W) :=
  (rho_ulift_group_local (L := L) (G0 := G0) (V := V) σ) ⊠
    (rho_ulift_group_local (L := L) (G0 := H) (V := W) τ)

/-- Helper for Exercise 12-12.2-6: tensoring the factorwise lifted-owner descents packages the
entire same-universe external tensor back to the restricted public tensor in one step. -/
noncomputable def lifted_field_basis_externalTensor_to_restricted_public_tensor_equiv_local
    {H : Type v} [Group H] [Finite H]
    {W : Type*} [AddCommGroup W] [Module L W] [FiniteDimensional L W]
    (σ : Representation L G0 V) (τ : Representation L H W) :
    Representation.Equiv
      (Representation.tprod
        ((lifted_field_basis_fdRep_local (L := L) (G0 := G0) (V := V) σ).ρ.comp
          (MonoidHom.fst (ULift.{max v w} G0) (ULift.{max v w} H)))
        ((lifted_field_basis_fdRep_local (L := L) (G0 := H) (V := W) τ).ρ.comp
          (MonoidHom.snd (ULift.{max v w} G0) (ULift.{max v w} H))))
      (restrictScalars_rep_local (L := L)
        (ρ := rho_ulift_externalTensor_local σ τ)) := by
  let eσ :
      Representation.Equiv
        (lifted_field_basis_fdRep_local (L := L) (G0 := G0) (V := V) σ).ρ
        (restrictScalars_rep_local (L := L)
          (ρ := rho_ulift_group_local (L := L) (G0 := G0) (V := V) σ)) :=
    lifted_field_basis_to_restrictScalars_group_ulift_equiv_local
      (L := L) (G0 := G0) (V := V) σ
  let eτ :
      Representation.Equiv
        (lifted_field_basis_fdRep_local (L := L) (G0 := H) (V := W) τ).ρ
        (restrictScalars_rep_local (L := L)
          (ρ := rho_ulift_group_local (L := L) (G0 := H) (V := W) τ)) :=
    lifted_field_basis_to_restrictScalars_group_ulift_equiv_local
      (L := L) (G0 := H) (V := W) τ
  let htensor :
      Representation.Equiv
        (Representation.tprod
          ((lifted_field_basis_fdRep_local (L := L) (G0 := G0) (V := V) σ).ρ.comp
            (MonoidHom.fst (ULift.{max v w} G0) (ULift.{max v w} H)))
          ((lifted_field_basis_fdRep_local (L := L) (G0 := H) (V := W) τ).ρ.comp
            (MonoidHom.snd (ULift.{max v w} G0) (ULift.{max v w} H))))
        (Representation.tprod
          ((restrictScalars_rep_local (L := L)
              (ρ := rho_ulift_group_local (L := L) (G0 := G0) (V := V) σ)).comp
            (MonoidHom.fst (ULift.{max v w} G0) (ULift.{max v w} H)))
          ((restrictScalars_rep_local (L := L)
              (ρ := rho_ulift_group_local (L := L) (G0 := H) (V := W) τ)).comp
            (MonoidHom.snd (ULift.{max v w} G0) (ULift.{max v w} H)))) :=
    by
      refine Representation.Equiv.mk (TensorProduct.congr eσ.toLinearEquiv eτ.toLinearEquiv) ?_
      intro g
      ext x y
      have hσg := by
        simpa using
          congrArg
            (fun f :
              (Fin (Module.finrank L V) → ULift.{max v w} L) →ₗ[ULift.{max v w} L] V ↦ f x)
            (eσ.isIntertwining' g.1)
      have hτg := by
        simpa using
          congrArg
            (fun f :
              (Fin (Module.finrank L W) → ULift.{max v w} L) →ₗ[ULift.{max v w} L] W ↦ f y)
            (eτ.isIntertwining' g.2)
      -- On pure tensors, the external tensor action is the tensor product of the factor actions.
      simpa [Representation.tprod_apply] using
        congrArg₂
          (fun a b ↦ a ⊗ₜ[ULift.{max v w} L] b)
          hσg hτg
  exact htensor.trans (restrictScalars_externalTensor_equiv_local
    (L := L)
    (σ := rho_ulift_group_local (L := L) (G0 := G0) (V := V) σ)
    (τ := rho_ulift_group_local (L := L) (G0 := H) (V := W) τ))

/-- Helper for Exercise 12-12.2-6: the explicit lifted-field owner remains irreducible after the
four source-faithful transports: group `ULift`, finite-basis coordinates, scalar restriction, and
the final coefficientwise `ULift` on scalars. -/
private theorem lifted_field_basis_representation_isIrreducible_local
    (ρ : Representation L G0 V)
    [ρ.IsIrreducible] :
    Representation.IsIrreducible
      (lifted_field_basis_fdRep_local (L := L) (G0 := G0) (V := V) ρ).ρ := by
  let π₁ : Representation L (ULift.{max v w} G0) V :=
    rho_ulift_group_local (L := L) (G0 := G0) (V := V) ρ
  have hπ₁ : Representation.IsIrreducible π₁ := by
    -- First lift only the group variable, which is an isomorphic source route.
    simpa [π₁, rho_ulift_group_local] using
      (isIrreducible_comp_of_mulEquiv_univ_local
        (L := L)
        (e := (MulEquiv.ulift : ULift.{max v w} G0 ≃* G0))
        (σ := ρ))
  let π₂ : Representation L (ULift.{max v w} G0) (Fin (Module.finrank L V) → L) :=
    finBasisRepresentation_univ_local (L := L) (ρ := π₁)
  have hπ₂ : Representation.IsIrreducible π₂ := by
    -- Next move to a finite-basis coordinate model.
    letI : Representation.IsIrreducible π₁ := hπ₁
    simpa [π₂] using
      (finBasisRepresentation_univ_isIrreducible_local (L := L) (ρ := π₁) :
        Representation.IsIrreducible
          (finBasisRepresentation_univ_local (L := L) (ρ := π₁)))
  let π₃ : Representation (ULift.{max v w} L) (ULift.{max v w} G0)
      (Fin (Module.finrank L V) → L) :=
    restrictScalars_rep_local (L := L) (ρ := π₂)
  have hπ₃ : Representation.IsIrreducible π₃ := by
    -- Then restrict scalars to the lifted field without changing the invariant submodules.
    letI : Representation.IsIrreducible π₂ := hπ₂
    simpa [π₃] using
      (restrictScalars_rep_isIrreducible_local (L := L) (π := π₂) :
        Representation.IsIrreducible (restrictScalars_rep_local (L := L) (ρ := π₂)))
  let e : (Fin (Module.finrank L V) → L) ≃ₗ[ULift.{max v w} L]
      (Fin (Module.finrank L V) → ULift.{max v w} L) :=
    LinearEquiv.piCongrRight fun _ =>
      (ULift.moduleEquiv.symm : L ≃ₗ[ULift.{max v w} L] ULift.{max v w} L)
  let π₄ :
      Representation (ULift.{max v w} L) (ULift.{max v w} G0)
        (Fin (Module.finrank L V) → ULift.{max v w} L) :=
    { toFun := fun g ↦ e.conj (π₃ g)
      map_one' := conjRepresentation_map_one_univ_local (L := ULift.{max v w} L) e π₃
      map_mul' := fun g h ↦ conjRepresentation_map_mul_univ_local
        (L := ULift.{max v w} L) e π₃ g h }
  have hπ₄ : Representation.IsIrreducible π₄ := by
    -- Finally lift the coefficient field pointwise by `ULift`.
    letI : Representation.IsIrreducible π₃ := hπ₃
    simpa [π₄, e] using
      (lifted_field_coordinate_rep_isIrreducible_local (L := L) (π := π₃) :
        Representation.IsIrreducible π₄)
  -- The bundled owner is exactly `FDRep.of π₄`.
  simpa [lifted_field_basis_fdRep_local, π₁, π₂, π₃, π₄, e] using hπ₄

/-- Helper for Exercise 12-12.2-6: irreducibility of `ρ` should make the lifted-field owner
simple, providing the exact Chapter 3 hypothesis for the external tensor route. -/
theorem lifted_field_basis_fdRep_simple_local
    (ρ : Representation L G0 V)
    [ρ.IsIrreducible] :
    Simple (lifted_field_basis_fdRep_local ρ) := by
  letI :
      Representation.IsIrreducible
        (lifted_field_basis_fdRep_local (L := L) (G0 := G0) (V := V) ρ).ρ :=
    lifted_field_basis_representation_isIrreducible_local (L := L) (G0 := G0) (V := V) ρ
  -- The owner is now explicit, so Chapter 2 upgrades irreducibility to simplicity directly.
  exact FDRep.simple_of_isIrreducible (lifted_field_basis_fdRep_local ρ)

end FieldLift

end Exercise_12_12_2_6

end Representation
