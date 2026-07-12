import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_6_1.FixedConstituentCycleNormalization

universe u v w x

open scoped TensorProduct

namespace Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [HenselianLocalRing A]
variable [CharP (IsLocalRing.ResidueField A) p]
variable {h : ℕ}
variable {G : Type v} [Group G] [Finite G]
variable {V : Type x} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]
variable [FiniteDimensional (IsLocalRing.ResidueField A) V]

local notation "k" => IsLocalRing.ResidueField A
private noncomputable instance theorem171761TargetModule : Module A V :=
  Module.compHom V (algebraMap A k)
private instance theorem171761TargetScalarTower : IsScalarTower A k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.6-1: a kernel-fiber element `u ∈ U₁` whose reduction fixes `S̄`
pointwise already reduces to the identity intertwining endomorphism. This is the generic
`U₁` version of the cycle-specific argument used earlier for Serre's section cycles. -/
theorem fixed_constituent_transport_kernel_reduction_eq_id_of_comp_eq
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
      (u :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (1 : G))
      (hcomp : red_S.comp u.toLinearMap = red_S) :
    fixed_constituent_endAlgHom
        (A := A) (G := G) (V := V) (I := I) (ρ := ρ) (Sbar := Sbar)
        ρA_I red_S hLiftSbar
          (fixed_constituent_transport_kernel_intertwiningEnd
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) u) =
        Representation.IntertwiningMap.id Sbar.toRepresentation := by
    letI : Module (MonoidAlgebra A I) P_S := representationCarrierGroupAlgebraModule ρA_I
    letI : IsScalarTower A (MonoidAlgebra A I) P_S :=
      representationCarrierGroupAlgebraIsScalarTower ρA_I
    letI : Module (MonoidAlgebra k I) Sbar.toSubmodule :=
      representationCarrierGroupAlgebraModule Sbar.toRepresentation
    letI : IsScalarTower k (MonoidAlgebra k I) Sbar.toSubmodule :=
      representationCarrierGroupAlgebraIsScalarTower Sbar.toRepresentation
    have hred : red_S.IsResidueFieldReduction I := by
      simpa using hLiftSbar
    apply Representation.IntertwiningMap.ext
    ext y
    obtain ⟨x, rfl⟩ :=
      fixed_constituent_reduction_surjective (A := A) (H := I) hred y
    -- Evaluate on a lift of the chosen reduced vector and use the hypothesis `red_S ∘ u = red_S`.
    have happly :
        fixed_constituent_endAlgHom
            (A := A) (G := G) (V := V) (I := I) (ρ := ρ) (Sbar := Sbar)
            ρA_I red_S hLiftSbar
            (fixed_constituent_transport_kernel_intertwiningEnd
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) u) (red_S x) =
          red_S x := by
      calc
        fixed_constituent_endAlgHom
            (A := A) (G := G) (V := V) (I := I) (ρ := ρ) (Sbar := Sbar)
            ρA_I red_S hLiftSbar
            (fixed_constituent_transport_kernel_intertwiningEnd
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) u) (red_S x) =
          red_S (u x) := by
            exact
              fixed_constituent_endAlgHom_comp_apply
                (A := A) (G := G) (V := V) (I := I) (ρ := ρ) (Sbar := Sbar)
                ρA_I red_S hLiftSbar
                (fixed_constituent_transport_kernel_intertwiningEnd
                  (A := A) (G := G) (I := I) (ρA_I := ρA_I) u) x
        _ = red_S x := by
            simpa [LinearMap.comp_apply] using LinearMap.congr_fun hcomp x
    simpa using happly

/-- Helper for Theorem 17-17.6-1: if a kernel-fiber element `u ∈ U₁` reduces to the identity on
`S̄`, then its determinant has residue `1`. This packages the scalar-kernel argument in the exact
form needed for the remaining normalized-determinant upgrade. -/
theorem fixed_constituent_transport_fiber_det_residue_eq_one_of_reduction_eq_id
    [IsAlgClosed k]
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I (1 : G))
    (hcomp : red_S.comp u.toLinearMap = red_S) :
    Units.map (residueUnitHom (A := A))
        (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) u) = 1 := by
  have hscalar :
      ∀ f : ρA_I.IntertwiningMap ρA_I,
        ∃ a : A, f = a • Representation.IntertwiningMap.id ρA_I := by
    -- Schur's lemma on the fixed lift still identifies every equivariant endomorphism as scalar.
    intro f
    exact
      fixed_constituent_lift_equivariant_endomorphism_scalar
        (A := A) (G := G) (V := V) hp I hIcop (ρ := ρ) (Sbar := Sbar)
        hSbar_irred ρA_I red_S hLiftSbar f
  obtain ⟨a, ha⟩ :=
    fixed_constituent_transport_kernel_eq_unit_smul_id_of_endomorphism_scalar
      (A := A) (G := G) (I := I) ρA_I hscalar u
  have hkernel_scalar :
      fixed_constituent_transport_kernel_intertwiningEnd
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) u =
        (a : A) • Representation.IntertwiningMap.id ρA_I := by
    -- Re-read the scalar classification of the kernel element on the endomorphism side.
    apply Representation.IntertwiningMap.ext
    ext x
    simpa [fixed_constituent_transport_kernel_intertwiningEnd] using
      congrArg (fun e : P_S ≃ₗ[A] P_S => (e : P_S →ₗ[A] P_S) x) ha
  have hkernel_map :
      fixed_constituent_endAlgHom
          (A := A) (G := G) (V := V) (I := I) (ρ := ρ) (Sbar := Sbar)
          ρA_I red_S hLiftSbar
          (fixed_constituent_transport_kernel_intertwiningEnd
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) u) =
        (IsLocalRing.residue A (a : A)) •
          Representation.IntertwiningMap.id Sbar.toRepresentation := by
    rw [hkernel_scalar]
    simpa using
      fixed_constituent_endAlgHom_scalar_id_transport
        (A := A) (G := G) (V := V) (I := I) (ρ := ρ) (Sbar := Sbar)
        ρA_I red_S hLiftSbar (a : A)
  have hred_id :
      fixed_constituent_endAlgHom
          (A := A) (G := G) (V := V) (I := I) (ρ := ρ) (Sbar := Sbar)
          ρA_I red_S hLiftSbar
          (fixed_constituent_transport_kernel_intertwiningEnd
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) u) =
        Representation.IntertwiningMap.id Sbar.toRepresentation := by
    -- The reduction hypothesis identifies the kernel endomorphism with the identity on `S̄`.
    exact
      fixed_constituent_transport_kernel_reduction_eq_id_of_comp_eq
        (A := A) (G := G) (V := V) (I := I) (ρ := ρ) (Sbar := Sbar)
        ρA_I red_S hLiftSbar u hcomp
  have hres_eq :
      IsLocalRing.residue A (a : A) = 1 := by
    have hscalar_id :
        (IsLocalRing.residue A (a : A)) • Representation.IntertwiningMap.id
            Sbar.toRepresentation =
          Representation.IntertwiningMap.id Sbar.toRepresentation := by
      calc
        (IsLocalRing.residue A (a : A)) •
            Representation.IntertwiningMap.id Sbar.toRepresentation =
          fixed_constituent_endAlgHom
            (A := A) (G := G) (V := V) (I := I) (ρ := ρ) (Sbar := Sbar)
            ρA_I red_S hLiftSbar
            (fixed_constituent_transport_kernel_intertwiningEnd
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) u) := by
                symm
                exact hkernel_map
        _ = Representation.IntertwiningMap.id Sbar.toRepresentation := hred_id
    letI : Sbar.toRepresentation.IsIrreducible := hSbar_irred
    letI : Nontrivial Sbar.toSubmodule :=
      not_subsingleton_iff_nontrivial.mp fun hsub ↦
        (show (⊥ : Subrepresentation Sbar.toRepresentation) ≠ ⊤ from
          IsSimpleOrder.bot_ne_top) <|
            top_unique <| by
              intro x hx
              change x = 0
              exact hsub.elim x 0
    obtain ⟨y, hy⟩ := exists_ne (0 : Sbar.toSubmodule)
    have hy_eq :
        (IsLocalRing.residue A (a : A)) • y = y := by
      simpa using
        congrArg
          (fun f : Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation => f y)
          hscalar_id
    have hy_zero : (((IsLocalRing.residue A (a : A)) - 1 : k) • y) = 0 := by
      rw [sub_smul, one_smul, hy_eq, sub_self]
    rcases smul_eq_zero.mp hy_zero with hzero | hzero
    · exact sub_eq_zero.mp hzero
    · exact False.elim (hy hzero)
  have hres_unit :
      Units.map (residueUnitHom (A := A)) a = 1 := by
    apply Units.ext
    simpa [residueUnitHom, hres_eq]
  -- The determinant is the `d`-th power of the scalar unit attached to `u`, and that scalar
  -- has residue `1`.
  calc
    Units.map (residueUnitHom (A := A))
        (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) u) =
      Units.map (residueUnitHom (A := A)) (a ^ Module.finrank A P_S) := by
        rw [fixed_constituent_transport_kernel_det_eq_unit_pow
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) ha]
    _ = (Units.map (residueUnitHom (A := A)) a) ^ Module.finrank A P_S := by
        rw [MonoidHom.map_pow]
    _ = 1 := by
        rw [hres_unit, one_pow]

end

end Representation
