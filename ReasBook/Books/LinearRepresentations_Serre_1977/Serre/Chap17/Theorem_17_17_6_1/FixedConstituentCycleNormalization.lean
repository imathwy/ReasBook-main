import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_6_1.FixedConstituentCycleGeometry

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

/-- Helper for Theorem 17-17.6-1: casting an equivalence of representations along an equality of
the source representation leaves the underlying linear map unchanged. -/
private theorem representationEquiv_cast_source_toLinearMap_apply
    {K : Type u} [CommRing K]
    {Γ : Type v} [Monoid Γ]
    {M : Type x} [AddCommGroup M] [Module K M]
    {N : Type w} [AddCommGroup N] [Module K N]
    {σ σ' : Representation K Γ M} {τ : Representation K Γ N}
    (h : σ = σ') (e : σ.Equiv τ) (m : M) :
    ((cast (congrArg (fun υ : Representation K Γ M => υ.Equiv τ) h) e :
        σ'.Equiv τ).toLinearMap m) =
      e.toLinearMap m := by
  cases h
  rfl

/-- Helper for Theorem 17-17.6-1: at `s = 1`, the chosen lifted transport reduces to the
canonical transported-constituent comparison at the identity. This records the exact normalization
gap: with an arbitrary section of the nonempty fibers `U_s`, the reduced transport is not
definitionally the normalized identity comparison on `S̄`. -/
theorem fixed_constituent_transport_aut_of_lift_reduction_one
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
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    (((hTransport (1 : G)).some.toLinearMap.restrictScalars A).comp red_S).comp
        (fixed_constituent_transport_aut_of_lift
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
          (1 : G)).toLinearMap =
      ((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (1 : G)).toLinearMap.restrictScalars A).comp
        red_S := by
  simpa using
    fixed_constituent_transport_aut_of_lift_reduction
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
      (1 : G)

/-- Helper for Theorem 17-17.6-1: the section determinant class is independent of the selected
point in each reduced transport fiber, because two points in the same fiber differ by a scalar
kernel transport and hence by a `d`-th power on determinants. -/
private theorem fixed_constituent_section_determinant_class_eq_of_transport_choice
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
    (hTransport' :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift' :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport' s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G) :
    fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport' hTransportLift' s =
      fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s := by
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
  let sec' :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport' hTransportLift'
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let det' : Aˣ :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec' s).2
  let det : Aˣ :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2
  let d := Module.finrank A P_S
  let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
  let res : Aˣ →* kˣ := Units.map (IsLocalRing.residue A).toMonoidHom
  obtain ⟨a, hdet⟩ :=
    fixed_constituent_transport_fiber_det_eq_section_det_mul_unit_pow_of_kernel_scalar
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel
      s (sec' s).2
  have hres :
      res det' = res det * (res a) ^ d := by
    simpa only [det', det, sec', sec, d, res, map_mul, map_pow] using congrArg res hdet
  have hpow_mem : (res a) ^ d ∈ Qd := by
    refine ⟨res a, ?_⟩
    rfl
  have hpow_class :
      QuotientGroup.mk' Qd ((res a) ^ d) = 1 :=
    (QuotientGroup.eq_one_iff ((res a) ^ d)).2 hpow_mem
  calc
    fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport' hTransportLift' s =
      QuotientGroup.mk' Qd (res det') := by
        simp only [fixed_constituent_section_determinant_class, sec', det', Qd, d, res]
    _ = QuotientGroup.mk' Qd (res det * (res a) ^ d) := by
        exact congrArg (QuotientGroup.mk' Qd) hres
    _ = QuotientGroup.mk' Qd (res det) := by
        simpa [hpow_class] using
          (map_mul (QuotientGroup.mk' Qd) (res det) ((res a) ^ d))
    _ =
      fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s := by
        simp only [fixed_constituent_section_determinant_class, sec, det, Qd, d, res]

/-- Helper for Theorem 17-17.6-1: normalize the reduced-side transport family by composing every
chosen comparison with the inverse of the comparison at `1`. The normalized family is stated as
actual equivalences, rather than as `Nonempty` witnesses, so the identity comparison is a genuine
component of the data instead of an uncontrolled classical choice. -/
theorem fixed_constituent_transport_family_normalization
    (I : Subgroup G) [I.Normal]
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
              (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    ∃ eTransport0 :
        ∀ s : G,
          Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation,
        (∀ s : G,
          IsResidueFieldLift
            (transportedSubrepresentation ρ Sbar s).toRepresentation
            ρA_I
            (((eTransport0 s).toLinearMap.restrictScalars A).comp red_S)) ∧
          eTransport0 (1 : G) =
            transportedSubrepresentation_rep_equiv_local_one (I := I) (ρ := ρ) Sbar := by
  classical
  let eTransport0 :
      ∀ s : G,
        Sbar.toRepresentation.Equiv
          (transportedSubrepresentation ρ Sbar s).toRepresentation :=
    fun s =>
      if hs : s = 1 then
        hs ▸ transportedSubrepresentation_rep_equiv_local_one (I := I) (ρ := ρ) Sbar
      else
        (hTransport s).some
  have hTransportLift0 :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((eTransport0 s).toLinearMap.restrictScalars A).comp red_S) := by
    intro s
    by_cases hs : s = 1
    · subst hs
      let e := transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (1 : G)
      have hsource :
          Sbar.toRepresentation.comp (MulAut.conjNormal ((1 : G)⁻¹)).toMonoidHom =
            Sbar.toRepresentation := by
        ext a y
        simp
      have hone_eq :
          transportedSubrepresentation_rep_equiv_local_one (I := I) (ρ := ρ) Sbar =
            (cast
              (congrArg
                (fun τ : Representation k I Sbar.toSubmodule =>
                  τ.Equiv (transportedSubrepresentation ρ Sbar (1 : G)).toRepresentation)
                hsource) e :
              Sbar.toRepresentation.Equiv
                (transportedSubrepresentation ρ Sbar (1 : G)).toRepresentation) := by
        unfold transportedSubrepresentation_rep_equiv_local_one
        dsimp [e]
        congr
      have hred_eq :
          (((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (1 : G)).toLinearMap.restrictScalars
            A).comp red_S) =
            (((transportedSubrepresentation_rep_equiv_local_one
              (I := I) (ρ := ρ) Sbar).toLinearMap.restrictScalars A).comp red_S) := by
        ext z
        rw [hone_eq]
        exact
          congrArg Subtype.val
            (representationEquiv_cast_source_toLinearMap_apply hsource e (red_S z)).symm
      have hA :
          ρA_I.comp (MulAut.conjNormal ((1 : G)⁻¹)).toMonoidHom = ρA_I := by
        ext a z
        simp
      have hcanonical :
          IsResidueFieldLift
            (transportedSubrepresentation ρ Sbar (1 : G)).toRepresentation
            ρA_I
            (((transportedSubrepresentation_rep_equiv_local_one
              (I := I) (ρ := ρ) Sbar).toLinearMap.restrictScalars A).comp red_S) := by
        have hbase :=
          transported_fixed_constituent_lift_of_conjugation
            (A := A) (G := G) (V := V) I ρ Sbar ρA_I red_S hLiftSbar (1 : G)
        rw [hA, hred_eq] at hbase
        exact hbase
      simpa [eTransport0] using hcanonical
    · simpa [eTransport0, hs] using hTransportLift s
  refine ⟨eTransport0, hTransportLift0, ?_⟩
  simp [eTransport0]

/-- Helper for Theorem 17-17.6-1: the normalized identity comparison sends a vector of `S̄` to
the same ambient vector, equivalently to the action of `ρ 1`. -/
theorem transportedSubrepresentation_rep_equiv_local_one_subtype_apply
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (x : Sbar.toSubmodule) :
    (transportedSubrepresentation ρ Sbar (1 : G)).toSubmodule.subtype
        ((transportedSubrepresentation_rep_equiv_local_one (I := I) (ρ := ρ) Sbar).toLinearMap x) =
      (ρ (1 : G)) (Sbar.toSubmodule.subtype x) := by
  let e := transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (1 : G)
  have hsource :
      Sbar.toRepresentation.comp (MulAut.conjNormal ((1 : G)⁻¹)).toMonoidHom =
        Sbar.toRepresentation := by
    ext a y
    simp
  have hone_eq :
      transportedSubrepresentation_rep_equiv_local_one (I := I) (ρ := ρ) Sbar =
        (cast
          (congrArg
            (fun τ : Representation k I Sbar.toSubmodule =>
              τ.Equiv (transportedSubrepresentation ρ Sbar (1 : G)).toRepresentation)
            hsource) e :
          Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar (1 : G)).toRepresentation) := by
    unfold transportedSubrepresentation_rep_equiv_local_one
    dsimp [e]
    congr
  have hlin :
      ((transportedSubrepresentation_rep_equiv_local_one
          (I := I) (ρ := ρ) Sbar).toLinearMap x) =
        e.toLinearMap x := by
    rw [hone_eq]
    exact representationEquiv_cast_source_toLinearMap_apply hsource e x
  rw [hlin]
  exact
    LinearMap.congr_fun
      (transportedSubrepresentation_rep_equiv_local_subtype
        (I := I) (ρ := ρ) (Sbar := Sbar) (1 : G)) x

/-- Helper for Theorem 17-17.6-1: once the reduced-side section has been normalized so that the
chosen comparison at `1` is the canonical one, Serre's literal `|G|`-cycle in the kernel fiber
`U₁` should reduce to the identity endomorphism of the fixed constituent `S̄`. Isolating this
bridge keeps the remaining section-normalization blocker separate from the later roots-of-unity
packaging. -/
theorem fixed_constituent_section_cycle_reduction_in_ambient_zero
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
    (hTransportOne :
      (hTransport (1 : G)).some =
        transportedSubrepresentation_rep_equiv_local_one (I := I) (ρ := ρ) Sbar)
    (s : G) :
    (((transportedSubrepresentation ρ Sbar (s ^ 0)).toSubmodule.subtype.restrictScalars A).comp
        ((((hTransport (s ^ 0)).some.toLinearMap.restrictScalars A).comp red_S).comp
          (fixed_constituent_section_cycle_fiber
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s 0).toLinearMap)) =
      ((((ρ (s ^ 0)).comp Sbar.toSubmodule.subtype).restrictScalars A).comp red_S) := by
  -- At `n = 0`, the cycle is the identity and normalization at `1` makes the endpoint
  -- comparison literally the canonical transport.
  ext z
  let cycle0 :=
    fixed_constituent_section_cycle_fiber
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s 0
  have hcycle_apply :
      cycle0 z = z := by
    simp [cycle0, fixed_constituent_section_cycle_fiber,
      fixed_constituent_transport_fiber_one, Representation.Equiv.mk]
    rfl
  have hdrop :
      ((((transportedSubrepresentation ρ Sbar (s ^ 0)).toSubmodule.subtype.restrictScalars A).comp
          ((((hTransport (s ^ 0)).some.toLinearMap.restrictScalars A).comp red_S).comp
            cycle0.toLinearMap)) z) =
        ((((transportedSubrepresentation ρ Sbar (s ^ 0)).toSubmodule.subtype.restrictScalars A).comp
          (((hTransport (s ^ 0)).some.toLinearMap.restrictScalars A).comp red_S)) z) := by
    simpa [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars] using
      congrArg (fun y : P_S => (hTransport (s ^ 0)).some.toLinearMap (red_S y))
        hcycle_apply
  have htransport :
      ((((transportedSubrepresentation ρ Sbar (s ^ 0)).toSubmodule.subtype.restrictScalars A).comp
          (((hTransport (s ^ 0)).some.toLinearMap.restrictScalars A).comp red_S)) z) =
        (((((ρ (s ^ 0)).comp Sbar.toSubmodule.subtype).restrictScalars A).comp red_S) z) := by
    rw [pow_zero]
    rw [hTransportOne]
    simpa [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      Submodule.subtype_apply] using
      transportedSubrepresentation_rep_equiv_local_one_subtype_apply
        (I := I) (ρ := ρ) (Sbar := Sbar) (red_S z)
  simpa [cycle0] using hdrop.trans htransport

/-- Helper for Theorem 17-17.6-1: once the reduced-side section has been normalized so that the
chosen comparison at `1` is canonical, Serre's literal `n`-step section cycle reduces to the
canonical ambient transport over `s ^ n`. The normalization hypothesis is necessary already at
`n = 0`, where the empty cycle forces the endpoint comparison at `1` to be the canonical one. -/
theorem fixed_constituent_section_step_reduction_in_ambient
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
    (s : G) :
    let sec :=
      fixed_constituent_transport_total_space_section
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    (((transportedSubrepresentation ρ Sbar s).toSubmodule.subtype.restrictScalars A).comp
        ((((hTransport s).some.toLinearMap.restrictScalars A).comp red_S).comp
          (sec s).2.toLinearMap)) =
      ((((ρ s).comp Sbar.toSubmodule.subtype).restrictScalars A).comp red_S) := by
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  have hred :=
    fixed_constituent_transport_aut_of_lift_reduction
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s
  have hred' :=
    congrArg
      (fun f : P_S →ₗ[A] (transportedSubrepresentation ρ Sbar s).toSubmodule =>
        ((transportedSubrepresentation ρ Sbar s).toSubmodule.subtype.restrictScalars A).comp f)
      hred
  -- Compose the chosen section reduction into ambient `V`, then rewrite the canonical transport
  -- as the literal ambient action of `ρ s` on the fixed constituent.
  calc
    (((transportedSubrepresentation ρ Sbar s).toSubmodule.subtype.restrictScalars A).comp
        ((((hTransport s).some.toLinearMap.restrictScalars A).comp red_S).comp
          (sec s).2.toLinearMap)) =
      (((transportedSubrepresentation ρ Sbar s).toSubmodule.subtype.restrictScalars A).comp
        (((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s).toLinearMap.restrictScalars A).comp
          red_S)) := by
            simpa [sec, LinearMap.comp_assoc] using hred'
    _ =
      ((((ρ s).comp Sbar.toSubmodule.subtype).restrictScalars A).comp red_S) := by
            simpa [LinearMap.comp_assoc] using
              congrArg
                (fun f : Sbar.toSubmodule →ₗ[k] V => (f.restrictScalars A).comp red_S)
                (transportedSubrepresentation_rep_equiv_local_subtype
                  (I := I) (ρ := ρ) (Sbar := Sbar) s)

end

end Representation
