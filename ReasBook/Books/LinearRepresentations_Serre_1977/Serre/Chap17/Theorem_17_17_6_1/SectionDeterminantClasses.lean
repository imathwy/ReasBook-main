import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_6_1.KernelScalarUnit

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

/-- Helper for Theorem 17-17.6-1: the determinant of the embedded Hall-kernel element attached to
`x ∈ I` is exactly the determinant generator used to define Serre's subgroup `C`. -/
theorem fixed_constituent_transport_fiber_det_of_hall_kernel_element
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (x : I) :
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_fiber_of_hall_kernel_element
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) x) =
      fixed_constituent_action_det (A := A) (G := G) I ρA_I x := by
  apply Units.ext
  simp [fixed_constituent_transport_fiber_det,
    fixed_constituent_transport_fiber_of_hall_kernel_element,
    fixed_constituent_action_det, LinearEquiv.coe_det, IsUnit.unit_spec]
  rfl

/-- Helper for Theorem 17-17.6-1: the determinant contributed by the Hall-kernel correction used
to normalize a class `q ∈ N̄` already lies in Serre's determinant subgroup `C`. -/
theorem normalized_kernel_representative_correction_det_mem_determinant_subgroup
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
        (fixed_constituent_transport_fiber_of_hall_kernel_element
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (normalized_kernel_representative_correction
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q)) ∈
      fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I := by
  rw [fixed_constituent_transport_fiber_det_of_hall_kernel_element]
  exact
    Subgroup.subset_closure
      ⟨normalized_kernel_representative_correction
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q,
        rfl⟩

/-- Helper for Theorem 17-17.6-1: when Serre's chosen section is evaluated on an element of the
Hall kernel `I`, its determinant class already agrees modulo `d`-th powers with the corresponding
generator from the determinant subgroup `C`. -/
theorem section_determinant_class_eq_determinant_subgroup_residue_class_of_mem_I
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
    (x : I) :
    fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x =
      fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I
        ⟨fixed_constituent_action_det (A := A) (G := G) I ρA_I x,
          Subgroup.subset_closure ⟨x, rfl⟩⟩ := by
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let detSec : Aˣ :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec (x : G)).2
  let detI : Aˣ := fixed_constituent_action_det (A := A) (G := G) I ρA_I x
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
  obtain ⟨a, hdet⟩ :=
    fixed_constituent_transport_fiber_det_eq_section_det_mul_unit_pow_of_kernel_scalar
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel
      (x : G)
      (fixed_constituent_transport_fiber_of_hall_kernel_element
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) x)
  have hdetI :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_transport_fiber_of_hall_kernel_element
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) x) =
        detI := by
    exact
      fixed_constituent_transport_fiber_det_of_hall_kernel_element
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) x
  have hres : res detI = res detSec * (res a) ^ d := by
    simpa only [detSec, detI, sec, d, res, map_mul, map_pow] using
      congrArg res (hdetI.symm.trans hdet)
  have hpow_class : QuotientGroup.mk' Qd ((res a) ^ d) = 1 := by
    exact
      (QuotientGroup.eq_one_iff ((res a) ^ d)).2
        ⟨res a, rfl⟩
  calc
    fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x =
      QuotientGroup.mk' Qd (res detSec) := by
        simp only [fixed_constituent_section_determinant_class, sec, detSec, Qd, d, res]
    _ = QuotientGroup.mk' Qd (res detSec * (res a) ^ d) := by
        simpa [hpow_class] using
          (map_mul (QuotientGroup.mk' Qd) (res detSec) ((res a) ^ d)).symm
    _ = QuotientGroup.mk' Qd (res detI) := by
        exact congrArg (QuotientGroup.mk' Qd) hres.symm
    _ =
      fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I
        ⟨fixed_constituent_action_det (A := A) (G := G) I ρA_I x,
          Subgroup.subset_closure ⟨x, rfl⟩⟩ := by
        simp only [fixed_constituent_determinant_subgroup_residue_class, detI, Qd, d, res]

/-- Helper for Theorem 17-17.6-1: Serre's section determinant classes multiply in the quotient
`kˣ / (kˣ)^d`. This is the algebraic source-side owner behind the later quotient-by-`C` route:
the discrepancy between `sec (s * t)` and `sec s * sec t` lies in `U₁`, hence contributes only a
`d`-th power to the determinant class. -/
theorem fixed_constituent_section_determinant_class_mul
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
    (s t : G) :
    fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (s * t) =
      fixed_constituent_section_determinant_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s *
        fixed_constituent_section_determinant_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift t := by
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let detST : Aˣ :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec (s * t)).2
  let detS : Aˣ :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2
  let detT : Aˣ :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec t).2
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
  obtain ⟨a, hdet⟩ :=
    fixed_constituent_section_det_mul_eq_unit_pow
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel s t
  have hres : res detST = res detS * res detT * (res a) ^ d := by
    simpa only [detST, detS, detT, sec, d, res, map_mul, map_pow] using congrArg res hdet
  have hpow_class : QuotientGroup.mk' Qd ((res a) ^ d) = 1 := by
    exact
      (QuotientGroup.eq_one_iff ((res a) ^ d)).2
        ⟨res a, rfl⟩
  calc
    fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (s * t) =
      QuotientGroup.mk' Qd (res detST) := by
        simp only [fixed_constituent_section_determinant_class, sec, detST, Qd, d, res]
    _ = QuotientGroup.mk' Qd ((res detS * res detT) * (res a) ^ d) := by
        simpa [mul_assoc] using congrArg (QuotientGroup.mk' Qd) hres
    _ = QuotientGroup.mk' Qd (res detS * res detT) := by
        simpa [hpow_class] using
          (map_mul (QuotientGroup.mk' Qd) (res detS * res detT) ((res a) ^ d))
    _ = QuotientGroup.mk' Qd (res detS) * QuotientGroup.mk' Qd (res detT) := by
        exact map_mul (QuotientGroup.mk' Qd) (res detS) (res detT)
    _ =
      fixed_constituent_section_determinant_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s *
        fixed_constituent_section_determinant_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift t := by
        simp only [fixed_constituent_section_determinant_class, sec, detS, detT, Qd, d, res]

/-- Helper for Theorem 17-17.6-1: the section determinant class at `1` is the neutral element of
`kˣ / (kˣ)^d`. Together with multiplicativity, this packages Serre's chosen section determinants
as a genuine monoid morphism before quotienting by the determinant subgroup image. -/
theorem fixed_constituent_section_determinant_class_one
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
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (1 : G) =
      1 := by
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let detOne : Aˣ :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      (fixed_constituent_transport_fiber_one (A := A) (G := G) I ρA_I)
  let detSec : Aˣ :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec (1 : G)).2
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
  obtain ⟨a, hdet⟩ :=
    fixed_constituent_transport_fiber_det_eq_section_det_mul_unit_pow_of_kernel_scalar
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel
      (1 : G)
      (fixed_constituent_transport_fiber_one (A := A) (G := G) I ρA_I)
  have hdetOne : detOne = 1 := by
    simp [detOne, fixed_constituent_transport_fiber_det, fixed_constituent_transport_fiber_one,
      Representation.Equiv.mk]
    change LinearEquiv.det (LinearEquiv.refl A P_S) = 1
    simp
  have hdetSec : detSec = (a⁻¹) ^ d := by
    have hdet' : detSec * a ^ d = 1 := by
      simpa only [detOne, detSec, sec, d, hdetOne] using hdet.symm
    calc
      detSec = (detSec * a ^ d) * (a ^ d)⁻¹ := by simp [mul_assoc]
      _ = (a ^ d)⁻¹ := by rw [hdet']; simp
      _ = (a⁻¹) ^ d := by simp [inv_pow]
  have hres : res detSec = (res a⁻¹) ^ d := by
    simpa only [res, map_pow] using congrArg res hdetSec
  have hclass_one : QuotientGroup.mk' Qd (res detSec) = 1 := by
    rw [hres]
    exact
      (QuotientGroup.eq_one_iff ((res a⁻¹) ^ d)).2
        ⟨res a⁻¹, rfl⟩
  calc
    fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (1 : G) =
      QuotientGroup.mk' Qd (res detSec) := by
        simp only [fixed_constituent_section_determinant_class, sec, detSec, Qd, d, res]
    _ = 1 := hclass_one

/-- Helper for Theorem 17-17.6-1: the chosen section determinants define a multiplicative map
`G → kˣ / (kˣ)^d`. This freezes the source-side algebra needed for the literal-cover pivot before
passing to the quotient by the determinant subgroup image. -/
noncomputable def fixed_constituent_section_determinant_class_hom
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
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    G →* (kˣ ⧸ ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)) where
  toFun :=
    fixed_constituent_section_determinant_class
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  map_one' :=
    fixed_constituent_section_determinant_class_one
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  map_mul' :=
    fixed_constituent_section_determinant_class_mul
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift

/-- Helper for Theorem 17-17.6-1: the quotient-out representative `q.1.out` of a class
`q ∈ N̄ = ker(pi₂)` already contributes no new determinant class modulo `d`-th powers; its class
comes from Serre's determinant subgroup `C`. -/
theorem kernel_out_representative_det_residue_class_mem_determinant_subgroup
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
    ∃ c :
        fixed_constituent_determinant_subgroup
          (A := A) (G := G) (I := I) ρA_I,
      QuotientGroup.mk'
          ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)
          (Units.map (IsLocalRing.residue A)
            (fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) q.1.out.1.2)) =
        fixed_constituent_determinant_subgroup_residue_class
          (A := A) (G := G) (I := I) ρA_I c := by
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
  refine
    ⟨⟨detHall,
        normalized_kernel_representative_correction_det_mem_determinant_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q⟩, ?_⟩
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
        ⟨detHall,
          normalized_kernel_representative_correction_det_mem_determinant_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q⟩ := by
        simp only [fixed_constituent_determinant_subgroup_residue_class, detHall, Qd, d, res]

end

end Representation
