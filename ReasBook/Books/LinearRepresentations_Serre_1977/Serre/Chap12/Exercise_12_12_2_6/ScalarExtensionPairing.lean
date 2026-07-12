import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Proposition_2_2_2_1
import LinearRepresentations_Serre_1977.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Chap06.Corollary_6_6_5_4
import LinearRepresentations_Serre_1977.Chap06.Proposition_6_6_5_5
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_3.API
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.CharacterBasisCoefficients
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.ComplexMinimalRealization
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.FieldDenominatorDescent
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.FieldTensorCenterBridge
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.ScalarExtensionConstituents
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_2_1

noncomputable section

open scoped BigOperators
open scoped Representation
open scoped Representation.ExternalTensor
open scoped SubgroupInduction

universe u v w

namespace Representation

open CategoryTheory
open Exercise_12_12_2_6

attribute [local instance] ULift.algebra'

section FieldPart

variable {K : Type u} [Field K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]

local instance instFintypeGExercise_12_12_2_6_pairing : Fintype G := Fintype.ofFinite G
/-- Helper for Exercise 12-12.2-6: over an algebraically closed field, the center acts on an
irreducible representation through a multiplicative scalar character. -/
theorem center_scalar_action_hom_over_algClosed_local
    {L : Type w} [Field L] [CharZero L] [IsAlgClosed L]
    {V : Type*} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (ρ : Representation L G V) [ρ.IsIrreducible] :
    ∃ μ : Subgroup.center G →* Lˣ, ∀ s : Subgroup.center G,
      ρ (s : G) = (μ s : L) • (1 : Module.End L V) := by
  classical
  letI : Module (MonoidAlgebra L G) V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule (MonoidAlgebra L G) V :=
    (irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  letI : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra L G) V
  let exists_smul_id_of_mem_center :
      ∀ s : G, s ∈ Submonoid.center G → ∃ z : L, ρ s = z • (1 : Module.End L V) :=
    fun s hs ↦ by
      obtain ⟨z, hz⟩ := intertwiningMap_eq_smul_id ρ
        (Representation.IntertwiningMap.centralMul ρ s hs)
      refine ⟨z, ?_⟩
      simpa using congrArg Representation.IntertwiningMap.toLinearMap hz
  let scalar : Subgroup.center G → L := fun s ↦
    Classical.choose <| exists_smul_id_of_mem_center (s : G)
      (show (s : G) ∈ Submonoid.center G from by
        simpa [Subgroup.center_toSubmonoid] using s.2)
  have hscalar (s : Subgroup.center G) :
      ρ (s : G) = scalar s • (1 : Module.End L V) := by
    -- Schur's lemma identifies each central action with a unique scalar homothety.
    simpa [scalar] using
      (Classical.choose_spec <| exists_smul_id_of_mem_center (s : G)
        (show (s : G) ∈ Submonoid.center G from by
          simpa [Subgroup.center_toSubmonoid] using s.2))
  have hsmul_injective : Function.Injective fun z : L ↦ z • (1 : Module.End L V) := by
    -- A scalar multiple of the identity is determined by its value on any nonzero vector.
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    intro z w hzw
    have hvw : z • v = w • v := by
      simpa using congrArg (fun f : Module.End L V ↦ f v) hzw
    have hsub : (z - w) • v = 0 := by
      rw [sub_smul, hvw, sub_self]
    rcases smul_eq_zero.mp hsub with hzero | hzero
    · exact sub_eq_zero.mp hzero
    · exact (hv hzero).elim
  have hscalar_ne_zero (s : Subgroup.center G) : scalar s ≠ 0 := by
    intro hz
    have hzero : ρ (s : G) = 0 := by
      simpa [hscalar s, hz]
    have hone : (1 : Module.End L V) = 0 := by
      calc
        (1 : Module.End L V) = ρ (s : G) * ρ ((s : G)⁻¹) := by
          simpa using ρ.map_mul (s : G) ((s : G)⁻¹)
        _ = 0 := by
          rw [hzero]
          simp
    exact one_ne_zero hone
  let μ : Subgroup.center G →* Lˣ :=
    { toFun := fun s ↦ Units.mk0 (scalar s) (hscalar_ne_zero s)
      map_one' := by
        -- The identity element acts trivially, so its scalar is `1`.
        apply Units.ext
        apply hsmul_injective
        calc
          scalar 1 • (1 : Module.End L V) = ρ (1 : G) := (hscalar 1).symm
          _ = (1 : L) • (1 : Module.End L V) := by
                simp
      map_mul' := by
        intro s t
        -- Multiplicativity of the representation law transfers to the scalar action.
        apply Units.ext
        apply hsmul_injective
        calc
          scalar (s * t) • (1 : Module.End L V) = ρ (s * t : G) := (hscalar (s * t)).symm
          _ = ρ (s : G) * ρ (t : G) := by
                simp
          _ = (scalar s * scalar t) • (1 : Module.End L V) := by
                rw [hscalar s, hscalar t]
                calc
                  (scalar s • (1 : Module.End L V)) * (scalar t • (1 : Module.End L V))
                      = scalar s • ((1 : Module.End L V) * (scalar t • (1 : Module.End L V))) := by
                          rw [smul_mul_assoc]
                  _ = scalar s • (scalar t • (1 : Module.End L V)) := by
                        simp
                  _ = (scalar s * scalar t) • (1 : Module.End L V) := by
                        rw [smul_smul] }
  refine ⟨μ, ?_⟩
  intro s
  simpa [μ] using hscalar s

/-- Helper for Exercise 12-12.2-6: pulling an irreducible representation back along a larger
`ULift` of the source group preserves irreducibility. -/
theorem isIrreducible_comp_ulift_large_field_local
    {L : Type w} [Field L]
    {G0 : Type u} [Group G0] [Finite G0]
    {V : Type v} [AddCommGroup V] [Module L V]
    (ρ : Representation L G0 V)
    [ρ.IsIrreducible] :
    Representation.IsIrreducible
      (ρ.comp (MulEquiv.ulift : ULift.{max (max u v) w} G0 ≃* G0).toMonoidHom) := by
  -- The larger `ULift` only changes the group owner by a multiplicative equivalence.
  simpa using
    (_root_.Representation.isIrreducible_comp_of_mulEquiv_field_local
      (G := ULift.{max (max u v) w} G0) (e := MulEquiv.ulift) (σ := ρ))

/-- Helper for Exercise 12-12.2-6: after fixing a larger ambient universe, lifting the carrier by
`ULift` still preserves irreducibility. -/
theorem isIrreducible_ulift_carrier_large_field_local
    {L : Type w} [Field L]
    {G0 : Type u} [Group G0]
    {V : Type v} [AddCommGroup V] [Module L V]
    (ρ : Representation L G0 V)
    [ρ.IsIrreducible] :
    Representation.IsIrreducible
      ((_root_.Representation.ulift_carrier_representation_local (ρ := ρ)) :
        Representation L G0 (ULift.{max (max u v) w} V)) := by
  -- The carrier `ULift` is an explicit representation equivalence with the original action.
  simpa using
    (_root_.Representation.isIrreducible_ulift_carrier_representation_max_local
      (ρ := ρ))

/-- Helper for Exercise 12-12.2-6: restricting scalars along `ULift.algebra'` does not change the
underlying tensor-product carrier, only the coefficient owner. This packages the resulting
`ULift L`-linear identification between the two tensor products. -/
theorem tensorProduct_restrictScalars_ulift_equiv_nonempty_local
    {L : Type w} [Field L]
    {V : Type*} [AddCommGroup V] [Module L V]
    {W : Type*} [AddCommGroup W] [Module L W] :
    Nonempty
      ((TensorProduct (ULift.{max u w} L) V W) ≃ₗ[ULift.{max u w} L]
        TensorProduct L V W) := by
  let f : TensorProduct (ULift.{max u w} L) V W →ₗ[ULift.{max u w} L] TensorProduct L V W :=
    TensorProduct.lift <|
      LinearMap.mk₂ (ULift.{max u w} L) (fun v w ↦ TensorProduct.tmul L v w)
        (fun v₁ v₂ w ↦ TensorProduct.add_tmul v₁ v₂ w)
        (fun a v w ↦ by
          change (a.down • v) ⊗ₜ[L] w = a.down • (v ⊗ₜ[L] w)
          exact (TensorProduct.smul_tmul' a.down v w).symm)
        (fun v w₁ w₂ ↦ TensorProduct.tmul_add v w₁ w₂)
        (fun a v w ↦ by
          change v ⊗ₜ[L] (a.down • w) = a.down • (v ⊗ₜ[L] w)
          exact (TensorProduct.tmul_smul a.down v w).trans rfl)
  let gL : TensorProduct L V W →ₗ[L] TensorProduct (ULift.{max u w} L) V W :=
    TensorProduct.lift <|
      LinearMap.mk₂ L (fun v w ↦ TensorProduct.tmul (ULift.{max u w} L) v w)
        (fun v₁ v₂ w ↦ TensorProduct.add_tmul v₁ v₂ w)
        (fun a v w ↦ by
          change (a • v) ⊗ₜ[ULift.{max u w} L] w = a • (v ⊗ₜ[ULift.{max u w} L] w)
          exact (TensorProduct.smul_tmul' a v w).symm)
        (fun v w₁ w₂ ↦ TensorProduct.tmul_add v w₁ w₂)
        (fun a v w ↦ by
          change v ⊗ₜ[ULift.{max u w} L] (a • w) = a • (v ⊗ₜ[ULift.{max u w} L] w)
          exact (TensorProduct.tmul_smul a v w).trans rfl)
  let g :
      TensorProduct L V W →ₗ[ULift.{max u w} L] TensorProduct (ULift.{max u w} L) V W :=
    { toFun := gL
      map_add' := gL.map_add
      map_smul' := by
        intro a x
        refine TensorProduct.induction_on x ?_ ?_ ?_
        · simp [gL]
        · intro v w
          change (a.down • v) ⊗ₜ[ULift.{max u w} L] w =
              a.down • (v ⊗ₜ[ULift.{max u w} L] w)
          exact (TensorProduct.smul_tmul' a.down v w).symm
        · intro x y _ _
          simp [gL] }
  refine ⟨LinearEquiv.ofLinear f g ?_ ?_⟩
  · ext x : 1
    ext v w : 2
    rfl
  · ext x : 1
    ext v w : 2
    rfl

/-- Helper for Exercise 12-12.2-6: local scalar restriction along `ULift L → L` keeps the same
underlying action operators on the carrier. -/
def restrictScalars_rep_bridge_local
    {L : Type w} [Field L]
    {H : Type*} [Group H]
    {W1 : Type*} [AddCommGroup W1] [Module L W1]
    (ρ : Representation L H W1) :
    Representation (ULift.{max u w} L) H W1 where
  toFun g := (ρ g).restrictScalars (ULift.{max u w} L)
  map_one' := by
    -- Restricting scalars leaves the underlying identity operator unchanged.
    ext x
    simp
  map_mul' g h := by
    -- The multiplication law is inherited verbatim after restricting scalars.
    ext x
    simp [map_mul]

/-- Helper for Exercise 12-12.2-6: the scalar-restriction bridge commutes with external tensor
products after the canonical `ULift`-scalar tensor identification. -/
noncomputable def restrictScalars_externalTensor_equiv_local
    {L : Type w} [Field L]
    {H : Type u} [Group H]
    {V : Type*} [AddCommGroup V] [Module L V]
    {W : Type*} [AddCommGroup W] [Module L W]
    (σ : Representation L G V) (τ : Representation L H W) :
    Representation.Equiv
      ((restrictScalars_rep_bridge_local (L := L) (ρ := σ)) ⊠
        (restrictScalars_rep_bridge_local (L := L) (ρ := τ)))
      (restrictScalars_rep_bridge_local (L := L) (ρ := (σ ⊠ τ))) := by
  let f : TensorProduct (ULift.{max u w} L) V W →ₗ[ULift.{max u w} L] TensorProduct L V W :=
    TensorProduct.lift <|
      LinearMap.mk₂ (ULift.{max u w} L) (fun v w ↦ TensorProduct.tmul L v w)
        (fun v₁ v₂ w ↦ TensorProduct.add_tmul v₁ v₂ w)
        (fun a v w ↦ by
          change (a.down • v) ⊗ₜ[L] w = a.down • (v ⊗ₜ[L] w)
          exact (TensorProduct.smul_tmul' a.down v w).symm)
        (fun v w₁ w₂ ↦ TensorProduct.tmul_add v w₁ w₂)
        (fun a v w ↦ by
          change v ⊗ₜ[L] (a.down • w) = a.down • (v ⊗ₜ[L] w)
          exact (TensorProduct.tmul_smul a.down v w).trans rfl)
  let gL : TensorProduct L V W →ₗ[L] TensorProduct (ULift.{max u w} L) V W :=
    TensorProduct.lift <|
      LinearMap.mk₂ L (fun v w ↦ TensorProduct.tmul (ULift.{max u w} L) v w)
        (fun v₁ v₂ w ↦ TensorProduct.add_tmul v₁ v₂ w)
        (fun a v w ↦ by
          change (a • v) ⊗ₜ[ULift.{max u w} L] w = a • (v ⊗ₜ[ULift.{max u w} L] w)
          exact (TensorProduct.smul_tmul' a v w).symm)
        (fun v w₁ w₂ ↦ TensorProduct.tmul_add v w₁ w₂)
        (fun a v w ↦ by
          change v ⊗ₜ[ULift.{max u w} L] (a • w) = a • (v ⊗ₜ[ULift.{max u w} L] w)
          exact (TensorProduct.tmul_smul a v w).trans rfl)
  let g :
      TensorProduct L V W →ₗ[ULift.{max u w} L] TensorProduct (ULift.{max u w} L) V W :=
    { toFun := gL
      map_add' := gL.map_add
      map_smul' := by
        intro a x
        refine TensorProduct.induction_on x ?_ ?_ ?_
        · simp [gL]
        · intro v w
          change (a.down • v) ⊗ₜ[ULift.{max u w} L] w =
              a.down • (v ⊗ₜ[ULift.{max u w} L] w)
          exact (TensorProduct.smul_tmul' a.down v w).symm
        · intro x y _ _
          simp [gL] }
  let e : TensorProduct (ULift.{max u w} L) V W ≃ₗ[ULift.{max u w} L] TensorProduct L V W :=
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
  intro g
  -- On pure tensors, both restricted actions are still the original tensor action.
  ext x y
  rfl

/-- Helper for Exercise 12-12.2-6: over an algebraically closed field, the external tensor
product of two irreducible finite-dimensional representations is irreducible. -/
theorem externalTensor_simple_ulift_adapter_local
    {L : Type w} [Field L] [CharZero L] [IsAlgClosed L]
    {G0 : Type u} [Group G0] [Finite G0]
    {H0 : Type u} [Group H0] [Finite H0]
    (σfd : FDRep (ULift.{max u w} L) (ULift.{max u w} G0))
    (hσsimple : Simple σfd)
    (τfd : FDRep (ULift.{max u w} L) (ULift.{max u w} H0))
    (hτsimple : Simple τfd) :
    Simple (FDRep.of (σfd.ρ ⊠ τfd.ρ)) := by
  letI : Fintype (ULift.{max u w} G0) := Fintype.ofFinite (ULift.{max u w} G0)
  letI : Fintype (ULift.{max u w} H0) := Fintype.ofFinite (ULift.{max u w} H0)
  letI : NeZero (Nat.card (ULift.{max u w} G0) : ULift.{max u w} L) := by
    -- The lifted source group is still finite, so its cardinality remains nonzero in the field.
    refine ⟨Nat.cast_ne_zero.mpr (Nat.card_pos (α := ULift.{max u w} G0)).ne'⟩
  letI : NeZero (Nat.card (ULift.{max u w} H0) : ULift.{max u w} L) := by
    -- The same cardinality argument supplies the second factor needed by Chapter 3.
    refine ⟨Nat.cast_ne_zero.mpr (Nat.card_pos (α := ULift.{max u w} H0)).ne'⟩
  -- Route correction: isolate the lifted-cardinality instances once, then reuse Chapter 3
  -- without altering the tensor-product proof route downstream.
  exact FDRep.externalTensor_simple σfd hσsimple τfd hτsimple

/-- Helper for Exercise 12-12.2-6: over an algebraically closed field, the external tensor
product of two irreducible finite-dimensional representations is irreducible. -/
theorem isIrreducible_externalTensor_field_local
    {L : Type w} [Field L] [CharZero L] [IsAlgClosed L]
    {H : Type u} [Group H] [Finite H]
    {V : Type*} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    {W : Type*} [AddCommGroup W] [Module L W] [FiniteDimensional L W]
    (σ : Representation L G V) (τ : Representation L H W)
    [σ.IsIrreducible] [τ.IsIrreducible] :
    Representation.IsIrreducible (σ ⊠ τ) := by
  let σfd := lifted_field_basis_fdRep_local (L := L) (G0 := G) (V := V) σ
  let τfd := lifted_field_basis_fdRep_local (L := L) (G0 := H) (V := W) τ
  have hσsimple : Simple σfd := by
    -- The lifted owner for `σ` is simple, so Chapter 3 applies to it directly.
    simpa [σfd] using
      (lifted_field_basis_fdRep_simple_local (L := L) (G0 := G) (V := V) σ)
  have hτsimple : Simple τfd := by
    -- The same source-faithful owner construction works for `τ`.
    simpa [τfd] using
      (lifted_field_basis_fdRep_simple_local (L := L) (G0 := H) (V := W) τ)
  have htensor_simple : Simple (FDRep.of (σfd.ρ ⊠ τfd.ρ)) := by
    -- Chapter 3 gives simplicity of the lifted external tensor over the common ambient universe.
    exact externalTensor_simple_ulift_adapter_local σfd hσsimple τfd hτsimple
  have htensor_irreducible :
      Representation.IsIrreducible (σfd.ρ ⊠ τfd.ρ) := by
    -- Convert the simple `FDRep` owner back to irreducibility of its underlying representation.
    letI : Simple (FDRep.of (σfd.ρ ⊠ τfd.ρ)) := htensor_simple
    simpa [σfd, τfd] using
      (FDRep.isIrreducible_of_simple (FDRep.of (σfd.ρ ⊠ τfd.ρ)))
  let πpublic :
      Representation L (ULift.{max u w} G × ULift.{max u w} H) (TensorProduct L V W) :=
    ((σ.comp (MulEquiv.ulift.toMonoidHom)) ⊠ (τ.comp (MulEquiv.ulift.toMonoidHom)))
  let πrestricted :
      Representation (ULift.{max u w} L) (ULift.{max u w} G × ULift.{max u w} H)
        (TensorProduct L V W) :=
    restrictScalars_rep_local (L := L) (ρ := πpublic)
  have htransport : Representation.Equiv (σfd.ρ ⊠ τfd.ρ) πrestricted := by
    -- Package the entire owner descent before asking Lean to transport irreducibility.
    simpa [πpublic, πrestricted] using
      (lifted_field_basis_externalTensor_to_restricted_public_tensor_equiv_local
        (L := L) (G0 := G) (V := V) (H := H) (W := W) (σ := σ) (τ := τ))
  have hrestricted :
      Representation.IsIrreducible πrestricted := by
    -- Route correction: the tensor descent is now exported factorwise, so the lifted owner tensor
    -- can be transported to the visible restricted public tensor in one equivalence step.
    exact isIrreducible_of_nonempty_equiv (ρ := σfd.ρ ⊠ τfd.ρ) (σ := πrestricted) ⟨htransport⟩
  have hulift :
      Representation.IsIrreducible πpublic := by
    -- Reflect irreducibility across the scalar restriction before removing the group `ULift`.
    simpa [πpublic, πrestricted] using
      restrictScalars_rep_reflects_irreducible_local
        (L := L)
        (π := πpublic)
        hrestricted
  -- The remaining transport is exactly the public group-`ULift` equivalence from the helper file.
  exact
    (isIrreducible_externalTensor_group_ulift_iff_local
      (L := L) (G := G) (H := H) (σ := σ) (τ := τ)).2 (by simpa [πpublic] using hulift)

/-- Helper for Exercise 12-12.2-6: every positive tensor power of an irreducible representation
over an algebraically closed field is irreducible. -/
theorem tensor_power_rep_is_irreducible_field_local
    {L : Type w} [Field L] [CharZero L] [IsAlgClosed L]
    {V : Type*} [AddCommGroup V] [Module L V]
    (ρ : Representation L G V)
    [ρ.IsIrreducible]
    (n : ℕ) :
    Representation.IsIrreducible
      (_root_.Representation.tensorPowerRep_field_local (G := G) ρ (n + 1)) := by
  letI : FiniteDimensional L V := IsIrreducible.finiteDimensional_of_finite ρ
  letI : FiniteDimensional L (TensorPower L 1 V) :=
    FiniteDimensional.of_injective
      (PiTensorProduct.subsingletonEquiv (R := L) (s := fun _ : Fin 1 ↦ V) 0).toLinearMap
      (PiTensorProduct.subsingletonEquiv (R := L) (s := fun _ : Fin 1 ↦ V) 0).injective
  have hOne :
      Representation.IsIrreducible
        (_root_.Representation.tensorPowerRep_field_local (G := G) ρ 1) := by
    letI : Representation.IsIrreducible
        (ρ.comp finOneMulEquiv.toMonoidHom) :=
      _root_.Representation.isIrreducible_comp_of_mulEquiv_field_local (G := Fin 1 → G)
        (e := finOneMulEquiv) ρ
    -- The one-fold tensor power is just the original representation after reindexing `Fin 1`.
    exact isIrreducible_of_nonempty_equiv
      ⟨(_root_.Representation.tensorPowerRepOneEquiv_field_local (G := G) (ρ := ρ)).symm⟩
  induction n with
  | zero =>
      exact hOne
  | succ n ih =>
      letI : Representation.IsIrreducible
          (_root_.Representation.tensorPowerRep_field_local (G := G) ρ (n + 1)) := ih
      letI : FiniteDimensional L (TensorPower L (n + 1) V) :=
        IsIrreducible.finiteDimensional_of_finite
          (_root_.Representation.tensorPowerRep_field_local (G := G) ρ (n + 1))
      letI : Representation.IsIrreducible
          (_root_.Representation.tensorPowerRep_field_local (G := G) ρ 1) := hOne
      let π :
          Representation L ((Fin (n + 1) → G) × (Fin 1 → G))
            (TensorProduct L (TensorPower L (n + 1) V) (TensorPower L 1 V)) :=
        (_root_.Representation.tensorPowerRep_field_local (G := G) ρ (n + 1)) ⊠
          (_root_.Representation.tensorPowerRep_field_local (G := G) ρ 1)
      letI : Representation.IsIrreducible π :=
        isIrreducible_externalTensor_field_local
          (G := Fin (n + 1) → G) (H := Fin 1 → G)
          (σ := _root_.Representation.tensorPowerRep_field_local (G := G) ρ (n + 1))
          (τ := _root_.Representation.tensorPowerRep_field_local (G := G) ρ 1)
      let e : (Fin (n + 1 + 1) → G) ≃* (Fin (n + 1) → G) × (Fin 1 → G) :=
        finAppendMulEquiv (n + 1) 1
      let πsplit :
          Representation L (Fin (n + 1 + 1) → G)
            (TensorProduct L (TensorPower L (n + 1) V) (TensorPower L 1 V)) :=
        π.comp e.toMonoidHom
      have hπsplit : Representation.IsIrreducible πsplit := by
        -- Precomposition by the tuple-splitting equivalence preserves irreducibility.
        simpa [πsplit, e] using
          (_root_.Representation.isIrreducible_comp_of_mulEquiv_field_local
            (G := Fin (n + 2) → G) (e := e) π)
      letI : Representation.IsIrreducible πsplit := hπsplit
      -- The successor tensor power is equivalent to the split external tensor.
      exact isIrreducible_of_nonempty_equiv
        ⟨(_root_.Representation.tensorPowerRepSuccEquiv_field_local
          (G := G) (ρ := ρ) (n := n + 1)).symm⟩

/-- Helper for Exercise 12-12.2-6: scalar extension to the algebraic closure just applies the
coefficient map to the source character. -/
theorem scalarExtension_character_eq_map_algClosure_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [FiniteDimensional K' ρ] :
    (Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ).character =
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character := by
  -- Trace is preserved by base change, so the scalar-extension character is the coefficientwise
  -- image of the original one.
  ext g
  exact LinearMap.trace_baseChange (ρ.ρ g) (AlgebraicClosure K')

/-- Helper for Exercise 12-12.2-6: normalized class-function pairing is unchanged after
precomposition with a multiplicative equivalence. -/
theorem groupFunctionPairingOverField_precomp_mulEquiv_local
    {L : Type*} [Field L]
    {H : Type*} [Group H] [Finite H]
    (e : H ≃* G) (φ ψ : G → L) :
    Representation.groupFunctionPairingOverField L
        (fun h : H ↦ φ (e h))
        (fun h : H ↦ ψ (e h)) =
      Representation.groupFunctionPairingOverField L φ ψ := by
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype G := Fintype.ofFinite G
  have hcard : Fintype.card H = Fintype.card G := Fintype.card_congr e.toEquiv
  rw [Representation.groupFunctionPairingOverField, Representation.groupFunctionPairingOverField,
    hcard]
  congr 1
  simpa [MulEquiv.map_inv] using
    (Equiv.sum_comp e.toEquiv (fun g : G ↦ φ g⁻¹ * ψ g))

/-- Helper for Exercise 12-12.2-6: precomposing a character-ring element with a multiplicative
equivalence keeps it inside the corresponding character ring. -/
theorem mem_characterRingOverField_precomp_mulEquiv_local
    {K' : Type*} [Field K']
    {G₀ : Type*} [Group G₀] [Finite G₀]
    {H : Type*} [Group H] [Finite H]
    (e : H ≃* G₀) {χ : G₀ → K'} (hχ : χ ∈ R[K'](G₀)) :
    (fun h : H ↦ χ (e h)) ∈ R[K'](H) := by
  -- Transport each honest character generator through the multiplicative equivalence `e`,
  -- then close under the algebra operations generating the character ring.
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, -, rfl⟩
    letI : FiniteDimensional K' ρ := hρfd
    let τρ : Representation K' H ρ := ρ.ρ.comp e.toMonoidHom
    have hτρ :
        τρ.character = fun h : H ↦ ρ.ρ.character (e h) := by
      -- Character transport across precomposition is pointwise definitional.
      ext h
      rfl
    exact hτρ ▸
      rep_character_mem_characterRingOverField_universe_local
        (K' := K') (H := H) (ρ := τρ)
  · intro n
    exact (R[K'](H)).algebraMap_mem n
  · intro f g _ _ hf hg
    simpa using (R[K'](H)).add_mem hf hg
  · intro f g _ _ hf hg
    simpa using (R[K'](H)).mul_mem hf hg

/-- Helper for Exercise 12-12.2-6: the algebraic-closure character-ring element can be moved to
the same-universe `ULift` field/group owner needed for the pairing transport. -/
theorem mem_characterRingOverAlgClosure_ulift_owner_local
    {K' : Type v} [Field K'] [CharZero K']
    (χ : R[AlgebraicClosure K'](G)) :
    (((IsScalarTower.toAlgHom ℤ (AlgebraicClosure K')
          (ULift.{max u v} (AlgebraicClosure K'))).compLeft (ULift.{max u v} G))
        (fun h : ULift.{max u v} G ↦ (χ : G → AlgebraicClosure K') h.down)) ∈
      R[ULift.{max u v} (AlgebraicClosure K')](ULift.{max u v} G) := by
  have hpre :
      (fun h : ULift.{max u v} G ↦ (χ : G → AlgebraicClosure K') h.down) ∈
        R[AlgebraicClosure K'](ULift.{max u v} G) := by
    -- First move only the group variable to the public `ULift` owner.
    simpa using
      (mem_characterRingOverField_precomp_mulEquiv_local
        (K' := AlgebraicClosure K')
        (G₀ := G) (H := ULift.{max u v} G)
        (e := (MulEquiv.ulift : ULift.{max u v} G ≃* G))
        (hχ := χ.2))
  -- Then lift coefficients to the same-universe field owner by coefficientwise base change.
  exact
    map_mem_characterRingOverField_local
      (G := ULift.{max u v} G)
      (F := AlgebraicClosure K')
      (E := ULift.{max u v} (AlgebraicClosure K'))
      (f := IsScalarTower.toAlgHom ℤ (AlgebraicClosure K')
        (ULift.{max u v} (AlgebraicClosure K')))
      (χ := fun h : ULift.{max u v} G ↦ (χ : G → AlgebraicClosure K') h.down)
      hpre

/-- Helper for Exercise 12-12.2-6: restricting scalars along `ULift L → L` preserves traces after
applying `ULift.down`. -/
theorem trace_restrictScalars_ulift_down_eq_local
    {L : Type*} [Field L] [CharZero L]
    {W : Type*} [AddCommGroup W] [Module L W] [FiniteDimensional L W]
    (f : Module.End L W) :
    ((LinearMap.trace (ULift L) W)
        (LinearMap.restrictScalars (ULift L) f)).down =
      (LinearMap.trace L W) f := by
  let bA : Module.Basis Unit (ULift L) L :=
    (Module.Basis.singleton Unit (ULift L)).map
      (ULift.moduleEquiv : ULift L ≃ₗ[ULift L] L)
  let bW := Module.finBasis L W
  -- Express both traces in coordinates over the one-dimensional `ULift L`-basis of `L`.
  rw [LinearMap.trace_eq_matrix_trace (ULift L) (bA.smulTower' bW)]
  rw [LinearMap.trace_eq_matrix_trace L bW]
  rw [LinearMap.restrictScalars_toMatrix
    (R := ULift L) (A := L) (bA := bA) (bM := bW) f]
  simp [Matrix.trace, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, bA]
  have hsumFin (s : Finset (Fin (Module.finrank L W))) :
      (s.sum fun x ↦ (⟨(bW.repr (f (bW x))) x⟩ : ULift L)).down =
        s.sum fun x ↦ (bW.repr (f (bW x))) x := by
    -- The remaining coefficientwise `ULift` disappears term by term in the finite diagonal sum.
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro x s hx hs
      simp [hx, hs]
  rw [Fintype.sum_prod_type]
  simpa using (hsumFin Finset.univ)

/-- Helper for Exercise 12-12.2-6: after lifting the group and restricting scalars, the visible
character is just the coefficientwise `ULift` of the original character. -/
theorem restrictScalars_rho_ulift_character_down_eq_local
    {K' : Type v} [Field K'] [CharZero K']
    {V : Type*} [AddCommGroup V] [Module (AlgebraicClosure K') V]
    [FiniteDimensional (AlgebraicClosure K') V]
    (σ : Representation (AlgebraicClosure K') G V)
    (h : ULift.{max u v} G) :
    ((restrictScalars_rep_local (L := AlgebraicClosure K')
        (ρ := rho_ulift_group_local (L := AlgebraicClosure K') (G0 := G) (V := V) σ)).character
        h).down =
      σ.character h.down := by
  -- Evaluate both characters as traces of the same operator before and after scalar restriction.
  rw [Representation.character, Representation.character]
  simp [restrictScalars_rep_local, rho_ulift_group_local]
  simpa using
    trace_restrictScalars_ulift_down_eq_local
      (L := AlgebraicClosure K') (W := V) (f := σ (MulEquiv.ulift h))

/-- Helper for Exercise 12-12.2-6: the normalized pairing on the lifted owner is exactly the
visible pairing after applying `ULift.down`. -/
theorem groupFunctionPairingOverField_ulift_owner_eq_local
    {K' : Type v} [Field K'] [CharZero K']
    (φ ψ : G → AlgebraicClosure K') :
    ULift.down
      (Representation.groupFunctionPairingOverField
        (ULift.{max u v} (AlgebraicClosure K'))
        (fun h : ULift.{max u v} G ↦ (⟨φ h.down⟩ : ULift.{max u v} (AlgebraicClosure K')))
        (fun h : ULift.{max u v} G ↦ (⟨ψ h.down⟩ : ULift.{max u v} (AlgebraicClosure K')))) =
      Representation.groupFunctionPairingOverField (AlgebraicClosure K') φ ψ := by
  let H := ULift.{max u v} G
  let L := ULift.{max u v} (AlgebraicClosure K')
  have hpre :
      Representation.groupFunctionPairingOverField L
          (fun h : H ↦ (⟨φ h.down⟩ : L))
          (fun h : H ↦ (⟨ψ h.down⟩ : L)) =
        Representation.groupFunctionPairingOverField L
          (fun g : G ↦ (⟨φ g⟩ : L))
          (fun g : G ↦ (⟨ψ g⟩ : L)) := by
    -- First remove the group `ULift`; only the coefficientwise `ULift` remains afterwards.
    -- `hII` normalizes the (`Subsingleton`-equal) `Fintype H` instances: the lemma's internally
    -- chosen `Fintype.ofFinite H` vs the goal's `ULift.fintype G`.
    have hII : ∀ (i1 : Fintype H) (φ' ψ' : H → L),
        @Representation.groupFunctionPairingOverField L H _ _ i1 φ' ψ' =
          @Representation.groupFunctionPairingOverField L H _ _ (Fintype.ofFinite H) φ' ψ' :=
      fun i1 φ' ψ' => by rw [Subsingleton.elim i1 (Fintype.ofFinite H)]
    simpa [H, L, hII] using
      groupFunctionPairingOverField_precomp_mulEquiv_local
        (G := G) (H := H) (e := (MulEquiv.ulift : H ≃* G))
        (φ := fun g : G ↦ (⟨φ g⟩ : L))
        (ψ := fun g : G ↦ (⟨ψ g⟩ : L))
  rw [hpre]
  rw [Representation.groupFunctionPairingOverField, Representation.groupFunctionPairingOverField]
  -- Then descend the coefficientwise `ULift` through the scalar prefactor and the finite sum.
  change
    (ULift.ringEquiv : L ≃+* AlgebraicClosure K')
        (((Fintype.card G : L)⁻¹) *
          ∑ s : G, (⟨φ s⁻¹⟩ : L) * (⟨ψ s⟩ : L)) =
      (Fintype.card G : AlgebraicClosure K')⁻¹ * ∑ s : G, φ s⁻¹ * ψ s
  rw [map_mul, map_sum]
  congr 1

/-- Helper for Exercise 12-12.2-6: pairing an algebraic-closure character-ring element with an
irreducible algebraic-closure character always produces an integer. -/
theorem pairing_eq_int_of_mem_characterRingOverAlgClosure_local
    {K' : Type v} [Field K'] [CharZero K']
    (χ : R[AlgebraicClosure K'](G))
    {V : Type*} [AddCommGroup V] [Module (AlgebraicClosure K') V]
    (σ : Representation (AlgebraicClosure K') G V)
    [FiniteDimensional (AlgebraicClosure K') V] [σ.IsIrreducible] :
    ∃ z : ℤ, ⟪(χ : G → AlgebraicClosure K'), σ.character⟫ = (z : AlgebraicClosure K') := by
  let L := ULift.{max u v} (AlgebraicClosure K')
  let H := ULift.{max u v} G
  let χu : H → L :=
    ((IsScalarTower.toAlgHom ℤ (AlgebraicClosure K') L).compLeft H)
      (fun h : H ↦ (χ : G → AlgebraicClosure K') h.down)
  have hχu : χu ∈ R[L](H) := by
    -- Move the source-side algebraic-closure witness to the same-universe owner where the
    -- irreducible-character basis argument can run without further transport debt.
    simpa [L, H, χu] using
      mem_characterRingOverAlgClosure_ulift_owner_local (G := G) χ
  obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_local (K := L) (G := H)
  letI : Fintype ι := inferInstance
  have howner_simple :
      Simple
        (lifted_field_basis_fdRep_local (L := AlgebraicClosure K') (G0 := G) (V := V) σ) := by
    -- The lifted-field owner is still simple because all intermediate transports preserve
    -- irreducibility.
    exact
      lifted_field_basis_fdRep_simple_local
        (L := AlgebraicClosure K') (G0 := G) (V := V) σ
  obtain ⟨i, hi⟩ :=
    hπ_complete.exists_iso
      (lifted_field_basis_fdRep_local (L := AlgebraicClosure K') (G0 := G) (V := V) σ)
      howner_simple
  let x : R[L](H) := ⟨χu, hχu⟩
  let c : ℤ :=
    (irreducible_characters_basis_of_complete_family L π hπ_pairwise hπ_complete).repr x i
  -- Instance irrelevance for the pairing's `Fintype H` argument: `Fintype` is a `Subsingleton`,
  -- so any `Fintype H` instance (the caller's `ULift.fintype G`, an external lemma's own instance)
  -- gives the same pairing.  Normalizing every occurrence to `Fintype.ofFinite H` lets the
  -- same-universe transport lemmas match up regardless of how each side synthesized `Fintype H`.
  have hII : ∀ (i1 : Fintype H) (φ ψ : H → L),
      @Representation.groupFunctionPairingOverField L H _ _ i1 φ ψ =
        @Representation.groupFunctionPairingOverField L H _ _ (Fintype.ofFinite H) φ ψ :=
    fun i1 φ ψ => by rw [Subsingleton.elim i1 (Fintype.ofFinite H)]
  have hpair_basis :
      ⟪(x : H → L), (π i).character⟫ =
        (((c : ℤ) : L) * ⟪(π i).character, (π i).character⟫) := by
    -- Pairing with the `i`-th basis character reads off exactly the `i`-th integral basis
    -- coefficient.  `hII` in the simp set normalizes the (`Subsingleton`-equal) `Fintype H`
    -- instances so the external lemma matches.
    simpa [c, hII] using
      basis_coefficient_pairing_eq_local
        (K := L) (G := H) (π := π) hπ_pairwise hπ_complete x i
  have hself_pair : ⟪(π i).character, (π i).character⟫ = (1 : L) := by
    have hcard_ne : (Nat.card H : L) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    letI : Invertible (Nat.card H : L) := invertibleOfNonzero hcard_ne
    letI : Simple (π i) := hπ_complete.isSimple i
    letI : Representation.IsIrreducible (π i).ρ := FDRep.isIrreducible_of_simple (π i)
    have hfinrank :
        Module.finrank L (Representation.IntertwiningMap (π i).ρ (π i).ρ) = 1 := by
      -- Over the algebraically closed same-universe owner, Schur's lemma makes the
      -- self-intertwining space one-dimensional.
      simpa using Representation.IsIrreducible.finrank_intertwiningMap_self (ρ := (π i).ρ)
    -- The normalized self-pairing is the dimension of the endomorphism space.  (`hII` normalizes
    -- the `Subsingleton`-equal `Fintype H` instance, as in `hpair_basis`.)
    simpa [hII, hfinrank] using
      (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
        L (π i).ρ (π i).ρ)
  have howner_pair :
      ⟪(x : H → L),
        (lifted_field_basis_fdRep_local (L := AlgebraicClosure K') (G0 := G) (V := V) σ).character⟫ =
          (c : L) := by
    have hchar :
        (lifted_field_basis_fdRep_local (L := AlgebraicClosure K') (G0 := G) (V := V) σ).character =
          (π i).character :=
      FDRep.char_iso hi.some
    -- Replace the lifted owner by the chosen complete-family representative, then collapse the
    -- self-pairing to `1`.
    calc
      ⟪(x : H → L),
          (lifted_field_basis_fdRep_local (L := AlgebraicClosure K') (G0 := G) (V := V) σ).character⟫
          = ⟪(x : H → L), (π i).character⟫ := by
              simpa using congrArg (fun ψ : H → L ↦ ⟪(x : H → L), ψ⟫) hchar
      _ = (((c : ℤ) : L) * ⟪(π i).character, (π i).character⟫) := hpair_basis
      _ = (c : L) := by simp [hself_pair]
  have htransport :
      ULift.down
        (⟪χu,
          (lifted_field_basis_fdRep_local (L := AlgebraicClosure K') (G0 := G) (V := V) σ).character⟫) =
        ⟪(χ : G → AlgebraicClosure K'), σ.character⟫ := by
    have hpublic_char :
        (restrictScalars_rep_local (L := AlgebraicClosure K')
            (ρ := rho_ulift_group_local (L := AlgebraicClosure K') (G0 := G) (V := V) σ)).character =
          fun h : H ↦ (⟨σ.character h.down⟩ : L) := by
      -- The restricted public owner has exactly the lifted visible character.
      ext h
      simpa [H, L] using
        restrictScalars_rho_ulift_character_down_eq_local
          (G := G) (K' := K') (V := V) σ h
    have howner_char :
        (lifted_field_basis_fdRep_local (L := AlgebraicClosure K') (G0 := G) (V := V) σ).character =
          fun h : H ↦ (⟨σ.character h.down⟩ : L) := by
      -- Route correction: the remaining transport debt is only the explicit owner-character
      -- rewrite, so we first descend along the public representation equivalence.
      calc
        (lifted_field_basis_fdRep_local
            (L := AlgebraicClosure K') (G0 := G) (V := V) σ).character =
            (restrictScalars_rep_local (L := AlgebraicClosure K')
              (ρ := rho_ulift_group_local (L := AlgebraicClosure K')
                (G0 := G) (V := V) σ)).character := by
              exact
                Representation.char_iso
                  (lifted_field_basis_to_restrictScalars_group_ulift_equiv_local
                    (L := AlgebraicClosure K') (G0 := G) (V := V) σ)
        _ = fun h : H ↦ (⟨σ.character h.down⟩ : L) := hpublic_char
    have hχu_eq :
        χu = fun h : H ↦ (⟨(χ : G → AlgebraicClosure K') h.down⟩ : L) := by
      -- The coefficient lift defining `χu` is pointwise just `ULift.up`.
      ext h
      rfl
    -- After the character rewrite, the pairing is literally the visible pairing pulled back
    -- through the group `ULift`.
    calc
      ULift.down
          (⟪χu,
            (lifted_field_basis_fdRep_local
              (L := AlgebraicClosure K') (G0 := G) (V := V) σ).character⟫) =
        ULift.down
          (Representation.groupFunctionPairingOverField L
            (fun h : H ↦ (⟨(χ : G → AlgebraicClosure K') h.down⟩ : L))
            (fun h : H ↦ (⟨σ.character h.down⟩ : L))) := by
              simpa [L, hχu_eq, howner_char]
      _ = ⟪(χ : G → AlgebraicClosure K'), σ.character⟫ := by
            simpa [L] using
              groupFunctionPairingOverField_ulift_owner_eq_local
                (G := G) (K' := K')
                (φ := (χ : G → AlgebraicClosure K')) (ψ := σ.character)
  refine ⟨c, ?_⟩
  -- Descend the same-universe integral coefficient through the explicit pairing transport.
  calc
    ⟪(χ : G → AlgebraicClosure K'), σ.character⟫
        = ULift.down
            (⟪χu,
              (lifted_field_basis_fdRep_local (L := AlgebraicClosure K') (G0 := G) (V := V) σ).character⟫) := by
                simpa [L, H, χu] using htransport.symm
    _ = ULift.down (c : L) := by
          rw [howner_pair]
    _ = (c : AlgebraicClosure K') := rfl

end FieldPart

end Representation
