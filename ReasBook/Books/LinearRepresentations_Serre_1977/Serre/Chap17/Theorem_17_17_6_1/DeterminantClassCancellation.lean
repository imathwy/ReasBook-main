import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_6_1.SectionDeterminantClasses

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

/-- Helper for Theorem 17-17.6-1: for `q ∈ N̄`, the raw quotient-out representative `q.1.out`
and the chosen Hall-kernel correction contribute the same determinant class modulo `d`-th powers.
This is the correction-specific replacement for the earlier existential class statement. -/
theorem kernel_out_representative_det_residue_class_eq_correction_residue_class
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    [IsAlgClosed k]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    QuotientGroup.mk'
        ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)
        (Units.map (IsLocalRing.residue A)
          (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) q.1.out.1.2)) =
      fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I
        ⟨fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (fixed_constituent_transport_fiber_of_hall_kernel_element
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)
              (normalized_kernel_representative_correction
                (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q)),
            normalized_kernel_representative_correction_det_mem_determinant_subgroup
              (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q⟩ := by
  let corr : I :=
    normalized_kernel_representative_correction
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  let raw :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I q.1.out.1.1 :=
    q.1.out.1.2
  let hall :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I (corr : G) :=
    fixed_constituent_transport_fiber_of_hall_kernel_element
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) corr
  have hcorr_index : (corr : G) = q.1.out.1.1 := by
    simpa [corr, fixed_constituent_transport_total_space_proj_hom,
      fixed_constituent_transport_total_space_proj] using
      normalized_kernel_representative_correction_val_eq_out_proj
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  let hall' :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I q.1.out.1.1 :=
    fixed_constituent_transport_fiber_reindex
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) hcorr_index hall
  let detRaw : Aˣ :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw
  let detHall : Aˣ :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) hall
  let d := Module.finrank A P_S
  let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
  let res : Aˣ →* kˣ := Units.map (IsLocalRing.residue A).toMonoidHom
  have hkernel :
      ∀ u :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (1 : G),
        ∃ a : Aˣ, u.toLinearEquiv = a • LinearEquiv.refl A P_S := by
    intro u
    exact
      fixed_constituent_transport_kernel_eq_unit_smul_id_of_endomorphism_scalar
        (A := A) (G := G) (I := I) ρA_I
        (fun f ↦
          fixed_constituent_lift_equivariant_endomorphism_scalar
            (A := A) (G := G) (V := V) hp I hIcop (ρ := ρ) (Sbar := Sbar)
            hSbar_irred ρA_I red_S hLiftSbar f)
        u
  obtain ⟨a, ha⟩ :=
    hkernel
      (fixed_constituent_transport_fiber_ratio
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw hall')
  have hhall'_det :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) hall' =
        detHall := by
    simpa [hall', detHall] using
      fixed_constituent_transport_fiber_det_reindex_eq
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) hcorr_index hall
  have hratio_det :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_transport_fiber_ratio
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw hall') =
        a ^ d := by
    exact
      fixed_constituent_transport_kernel_det_eq_unit_pow
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) ha
  have hdetRaw : detRaw = detHall * a ^ d := by
    simpa [detRaw, hhall'_det, hratio_det, d] using
      fixed_constituent_transport_fiber_det_eq_ratio_mul
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw hall'
  have hres : res detRaw = res detHall * (res a) ^ d := by
    simpa only [res, map_mul, map_pow] using congrArg res hdetRaw
  have hpow_class : QuotientGroup.mk' Qd ((res a) ^ d) = 1 := by
    exact
      (QuotientGroup.eq_one_iff ((res a) ^ d)).2
        ⟨res a, rfl⟩
  calc
    QuotientGroup.mk'
        ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)
        (Units.map (IsLocalRing.residue A)
          (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) q.1.out.1.2)) =
      QuotientGroup.mk' Qd (res detRaw) := by
        simp only [detRaw, raw, Qd, d, res]
        rfl
    _ = QuotientGroup.mk' Qd (res detHall * (res a) ^ d) := by
        exact congrArg (QuotientGroup.mk' Qd) hres
    _ = QuotientGroup.mk' Qd (res detHall) := by
        simpa [hpow_class] using
          (map_mul (QuotientGroup.mk' Qd) (res detHall) ((res a) ^ d))
    _ =
      fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I
        ⟨fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (fixed_constituent_transport_fiber_of_hall_kernel_element
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)
              (normalized_kernel_representative_correction
                (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q)),
          normalized_kernel_representative_correction_det_mem_determinant_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q⟩ := by
        simp only [fixed_constituent_determinant_subgroup_residue_class, corr, hall, detHall,
          Qd, d, res]

/-- Helper for Theorem 17-17.6-1: the determinant of Serre's normalized representative is the
determinant of the raw quotient-out representative multiplied by the inverse determinant of the
chosen Hall-kernel correction. This keeps the later kernel calculation transport-stable. -/
theorem normalized_kernel_representative_det_eq_raw_det_mul_correction_inv
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2 =
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) q.1.out.1.2 *
        (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_transport_fiber_of_hall_kernel_element
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (normalized_kernel_representative_correction
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q)))⁻¹ := by
  let corr : I :=
    normalized_kernel_representative_correction
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  let hall :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I (corr : G) :=
    fixed_constituent_transport_fiber_of_hall_kernel_element
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) corr
  let rawTotal :
      fixed_constituent_transport_total_space
        (A := A) (G := G) I ρA_I :=
    q.1.out.1
  let hallTotal :
      fixed_constituent_transport_total_space
        (A := A) (G := G) I ρA_I :=
    fixed_constituent_transport_total_space_embed_hall_kernel
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) corr
  have hdet :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          ((rawTotal * hallTotal⁻¹).2) =
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) rawTotal.2 *
          (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) hall)⁻¹ := by
    change
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_transport_fiber_comp
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            rawTotal.2
            (fixed_constituent_transport_fiber_inv
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) hallTotal.2)) =
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) rawTotal.2 *
          (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) hall)⁻¹
    rw [fixed_constituent_transport_fiber_det_comp]
    rw [fixed_constituent_transport_fiber_det_inv]
    simp [hallTotal, hall]
    ac_rfl
  simpa [normalized_kernel_representative, corr, hall, rawTotal, hallTotal,
    fixed_constituent_generated_cover_embed_hall_kernel,
    fixed_constituent_transport_total_space_embed_hall_kernel] using hdet

/-- Helper for Theorem 17-17.6-1: after cancelling the raw quotient-out determinant against the
literal Hall-kernel correction chosen in the normalized representative, the residual determinant
class in `kˣ / (kˣ)^d` is trivial. This isolates the quotient-level cancellation before the later
upstairs subgroup argument. -/
theorem normalized_kernel_determinant_class_eq_one
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    [IsAlgClosed k]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    QuotientGroup.mk'
        ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)
        (Units.map (IsLocalRing.residue A)
          (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (normalized_kernel_representative
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2)) =
      1 := by
  let corr : I :=
    normalized_kernel_representative_correction
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  let detRaw : Aˣ :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) q.1.out.1.2
  let detHall : Aˣ :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      (fixed_constituent_transport_fiber_of_hall_kernel_element
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) corr)
  let detNorm : Aˣ :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2
  let d := Module.finrank A P_S
  let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
  let res : Aˣ →* kˣ := Units.map (IsLocalRing.residue A).toMonoidHom
  have hraw_class :
      QuotientGroup.mk' Qd (res detRaw) =
        QuotientGroup.mk' Qd (res detHall) := by
    simpa [detRaw, detHall, corr, Qd, d, res,
      fixed_constituent_determinant_subgroup_residue_class] using
      kernel_out_representative_det_residue_class_eq_correction_residue_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hdet_norm : detNorm = detRaw * detHall⁻¹ := by
    simpa [detNorm, detRaw, detHall, corr] using
      normalized_kernel_representative_det_eq_raw_det_mul_correction_inv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hres_norm : res detNorm = res detRaw * (res detHall)⁻¹ := by
    simpa only [res, map_mul, map_inv] using congrArg res hdet_norm
  calc
    QuotientGroup.mk'
        ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)
        (Units.map (IsLocalRing.residue A)
          (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (normalized_kernel_representative
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2)) =
      QuotientGroup.mk' Qd (res detNorm) := by
        simp only [detNorm, Qd, d, res]
        rfl
    _ = QuotientGroup.mk' Qd (res detRaw * (res detHall)⁻¹) := by
        exact congrArg (QuotientGroup.mk' Qd) hres_norm
    _ = QuotientGroup.mk' Qd (res detRaw) * (QuotientGroup.mk' Qd (res detHall))⁻¹ := by
        rw [map_mul, map_inv]
    _ = 1 := by
        rw [hraw_class]
        simp

/-- Helper for Theorem 17-17.6-1: the quotient-trivial determinant class of Serre's normalized
representative is already witnessed by an explicit `d`-th power in the residue-field units. This
freezes the quotient-level endpoint in a rewrite-friendly form before the remaining literal
determinant-subgroup upgrade. -/
theorem normalized_kernel_representative_det_residue_eq_dth_power
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    [IsAlgClosed k]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    ∃ b : kˣ,
      Units.map (IsLocalRing.residue A)
          (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (normalized_kernel_representative
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2) =
        b ^ Module.finrank A P_S := by
  let detNorm : Aˣ :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2
  let d := Module.finrank A P_S
  let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
  let res : Aˣ →* kˣ := Units.map (IsLocalRing.residue A).toMonoidHom
  have hclass :
      QuotientGroup.mk' Qd (res detNorm) = 1 := by
    simpa [detNorm, Qd, d, res] using
      normalized_kernel_determinant_class_eq_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hmem : res detNorm ∈ Qd := by
    exact (QuotientGroup.eq_one_iff (N := Qd) (res detNorm)).mp hclass
  obtain ⟨b, hb⟩ := hmem
  refine ⟨b, ?_⟩
  simpa [detNorm, d, res] using hb.symm

end

end Representation
