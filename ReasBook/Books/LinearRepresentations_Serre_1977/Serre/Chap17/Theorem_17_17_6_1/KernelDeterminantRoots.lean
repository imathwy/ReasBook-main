import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_6_1.DeterminantClassCancellation

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
variable [IsAlgClosed (IsLocalRing.ResidueField A)]

local notation "k" => IsLocalRing.ResidueField A
private noncomputable instance theorem171761TargetModule : Module A V :=
  Module.compHom V (algebraMap A k)
private instance theorem171761TargetScalarTower : IsScalarTower A k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.6-1: casting a representation equivalence along an equality of
source representations leaves its underlying linear map unchanged. -/
private theorem representationEquivCastSource_toLinearMap_apply
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

/-- Helper for Theorem 17-17.6-1: the determinant of the scalar-normalized representative gives a
trivial class in `kˣ / (kˣ)^d` even after rewriting that determinant as `kernelScalar(q)^d`. This
records the exact verified endpoint of the current quotient-level calculation. -/
theorem kernel_scalar_pow_residue_class_eq_one
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
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    QuotientGroup.mk'
        ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)
        (Units.map (IsLocalRing.residue A).toMonoidHom
          ((kernel_scalar_unit
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q) ^
            Module.finrank A P_S)) =
      1 := by
  let d := Module.finrank A P_S
  let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
  let res : Aˣ →* kˣ := Units.map (IsLocalRing.residue A).toMonoidHom
  let a : Aˣ :=
    kernel_scalar_unit
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  change QuotientGroup.mk' Qd (res (a ^ d)) = 1
  refine (QuotientGroup.eq_one_iff (N := Qd) (res (a ^ d))).2 ?_
  refine ⟨res a, ?_⟩
  simp [res, map_pow]

/-- Helper for Theorem 17-17.6-1: in the notation of Serre's finite kernel package, every
`q ∈ N̄ = ker(pi₂)` already satisfies the quotient-side scalar identity
`res((kernelScalar q)^d) = 1` in `kˣ / (kˣ)^d`. This repackages the scalar rewrite theorem at the
actual kernel object used later in the projective-extension package. -/
theorem kernel_scalar_pow_residue_class_eq_one_on_kernel_subgroup
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
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let I2 :=
      fixed_constituent_generated_cover_hall_kernel_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let pi2 : G2 ⧸ I2 →* G ⧸ I :=
      generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let Nbar : Subgroup (G2 ⧸ I2) := pi2.ker
    let kernelScalar : Nbar →* Aˣ :=
      kernel_scalar_unit
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
    ∀ q : Nbar,
      QuotientGroup.mk'
          ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)
          (Units.map (IsLocalRing.residue A).toMonoidHom
            (kernelScalar q ^ Module.finrank A P_S)) =
        1 := by
  dsimp
  intro q
  exact
    kernel_scalar_pow_residue_class_eq_one
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q

/-- Helper for Theorem 17-17.6-1: the normalized determinant of a kernel representative is already
an actual `d`-th power in `Aˣ`. This packages the Hensel-lifting step separately from the later
literal-membership argument in Serre's determinant subgroup `C`. -/
theorem normalized_kernel_representative_det_exists_dth_root
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
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    ∃ a : Aˣ,
      a ^ Module.finrank A P_S =
        fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (normalized_kernel_representative
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2 := by
  refine
    ⟨kernel_scalar_unit
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q,
      ?_⟩
  exact
    (normalized_kernel_representative_det_eq_kernel_scalar_pow
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q).symm

/-- Helper for Theorem 17-17.6-1: once the normalized representatives of `N̄ = ker(pi₂)` are
rewritten as literal scalar points `(1, a • id)`, their classes commute with the whole quotient
`G₂ ⧸ I₂`. This closes the centrality half of Serre's finite kernel package. -/
theorem kernel_subgroup_central_of_normalized_representatives
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
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    (generated_cover_proj_to_quotient_descends
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker ≤
      Subgroup.center
        ((fixed_constituent_generated_cover_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) ⧸
          fixed_constituent_generated_cover_hall_kernel_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) := by
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let I2 :=
    fixed_constituent_generated_cover_hall_kernel_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi2 : G2 ⧸ I2 →* G ⧸ I :=
    generated_cover_proj_to_quotient_descends
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  intro q hq
  rw [Subgroup.mem_center_iff]
  intro y
  rcases QuotientGroup.mk'_surjective I2 y with ⟨g, rfl⟩
  let qN : pi2.ker := ⟨q, hq⟩
  let rep :=
    normalized_kernel_representative
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift qN
  let a : Aˣ :=
    kernel_scalar_unit
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift qN
  have hmk : QuotientGroup.mk' I2 rep = q := by
    simpa [G2, I2, pi2, qN, rep] using
      normalized_kernel_representative_mk_eq
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift qN
  have hrep_scalar :
      rep.1 =
        ⟨1, scalar_transport_fiber_one (A := A) (G := G) (I := I) ρA_I a⟩ := by
    simpa [rep, a] using
      normalized_kernel_representative_eq_scalar_total_space
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
        hTransportLift qN
  have hcomm_total : g.1 * rep.1 = rep.1 * g.1 := by
    rw [hrep_scalar]
    rw [fixed_constituent_transport_total_space_mul_eq]
    rw [fixed_constituent_transport_total_space_mul_eq]
    exact
      (scalar_transport_total_space_commutes
        (A := A) (G := G) (I := I) ρA_I a g.1).symm
  have hcomm : g * rep = rep * g := by
    apply Subtype.ext
    exact hcomm_total
  calc
    QuotientGroup.mk' I2 g * q =
        QuotientGroup.mk' I2 g * QuotientGroup.mk' I2 rep := by
          rw [hmk]
    _ = QuotientGroup.mk' I2 (g * rep) := by
          rw [map_mul]
    _ = QuotientGroup.mk' I2 (rep * g) := by
          rw [hcomm]
    _ = QuotientGroup.mk' I2 rep * QuotientGroup.mk' I2 g := by
          rw [map_mul]
    _ = q * QuotientGroup.mk' I2 g := by
          rw [hmk]

/-- Helper for Theorem 17-17.6-1: when the transport fiber element is the distinguished lift-side
automorphism `fixed_constituent_transport_aut_of_lift s`, the chosen reduction equivalence on
`S̄` is exactly Serre's fixed comparison `hTransport s`. This freezes the cover-side source
transport before the later `G₂`-action on the multiplicity space. -/
theorem fixed_constituent_transport_fiber_reduction_equiv_eq_chosen_transport
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
    (s : G) :
    fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s
        (fixed_constituent_transport_aut_of_lift
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s) =
      (hTransport s).some := by
  apply
    fixed_constituent_transport_fiber_reduction_equiv_unique
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (fixed_constituent_transport_aut_of_lift
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s)
  · exact
      fixed_constituent_transport_fiber_reduction_equiv_spec
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s
        (fixed_constituent_transport_aut_of_lift
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s)
  · exact
      fixed_constituent_transport_aut_of_lift_reduction
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s

/-- Helper for Theorem 17-17.6-1: for the literal identity element of the lift-side fiber `U₁`,
the chosen reduced comparison is the canonical transport at `1`. This isolates the precise
`g = 1` source normalization before the future cover action on `Hom^I(S̄, V)` is checked. -/
theorem fixed_constituent_transport_fiber_reduction_equiv_eq_identity_transport
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
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (1 : G)
        (fixed_constituent_transport_fiber_one
          (A := A) (G := G) (I := I) ρA_I) =
      transportedSubrepresentation_rep_equiv_local_one (I := I) (ρ := ρ) Sbar := by
  apply
    fixed_constituent_transport_fiber_reduction_equiv_unique
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (fixed_constituent_transport_fiber_one
        (A := A) (G := G) (I := I) ρA_I)
  · exact
      fixed_constituent_transport_fiber_reduction_equiv_spec
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (1 : G)
        (fixed_constituent_transport_fiber_one
          (A := A) (G := G) (I := I) ρA_I)
  · let e := transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (1 : G)
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
    ext z
    have hlin :
        (transportedSubrepresentation_rep_equiv_local_one
            (I := I) (ρ := ρ) Sbar).toLinearMap (red_S z) =
          e.toLinearMap (red_S z) := by
      rw [hone_eq]
      exact representationEquivCastSource_toLinearMap_apply hsource e (red_S z)
    simpa [fixed_constituent_transport_fiber_one, Representation.Equiv.mk, e] using hlin

/-- Helper for Theorem 17-17.6-1: precomposing Serre's multiplicity space by the reduction
equivalence attached to the distinguished lift-side transport automorphism agrees with the
earlier transported-constituent linear equivalence. This packages the exact source-side
identification needed before defining the upstairs `G₂`-action on `Hom^I(S̄, V)`. -/
theorem
    chosen_transport_fixed_isotypic_multiplicity_space_linearEquiv_eq_transport
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
    (s : G) :
    fixed_isotypic_multiplicity_space_precompose_linearEquiv
        (I := I) (ρ := ρ)
        (fixed_constituent_transport_fiber_reduction_equiv
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s
          (fixed_constituent_transport_aut_of_lift
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s)) =
      transported_fixed_isotypic_multiplicity_space_linearEquiv
        (I := I) (ρ := ρ) Sbar s (hTransport s).some := by
  rw [fixed_constituent_transport_fiber_reduction_equiv_eq_chosen_transport
    (p := p) (A := A) (G := G) (V := V)
    hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s]
  rfl

/-- Helper for Theorem 17-17.6-1: comparing the reduction equivalence attached to an arbitrary
cover fiber element with the fixed chosen transport over the same `s : G` gives an honest
`I`-equivariant automorphism of the fixed constituent `S̄`. This isolates the source-side
correction term that must be inserted before defining the `G₂`-action on `Hom^I(S̄, V)`. -/
noncomputable def fixed_isotypic_cover_source_correction_equiv
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
    (s : G)
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s) :
    Sbar.toRepresentation.Equiv Sbar.toRepresentation :=
  (fixed_constituent_transport_fiber_reduction_equiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s u).trans
    ((hTransport s).some.symm)

/-- Helper for Theorem 17-17.6-1: for the distinguished lift-side transport element over `s`,
the source-correction automorphism is the identity. This records that only non-section fiber
choices contribute a genuine correction term. -/
theorem fixed_isotypic_cover_source_correction_equiv_section_eq_refl
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
    (s : G) :
    fixed_isotypic_cover_source_correction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s
        (fixed_constituent_transport_aut_of_lift
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s) =
      Representation.Equiv.mk (LinearEquiv.refl k Sbar.toSubmodule) (by
        intro a
        ext x
        rfl) := by
  rw [fixed_isotypic_cover_source_correction_equiv,
    fixed_constituent_transport_fiber_reduction_equiv_eq_chosen_transport
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s]
  apply Representation.Equiv.ext
  funext x
  simp

/-- Helper for Theorem 17-17.6-1: precomposing multiplicity maps by the source-correction
automorphism attached to a cover fiber element yields a canonical linear self-equivalence of
`Hom^I(S̄, V)`. This is the exact source-side factor that remains after freezing the chosen
transport. -/
noncomputable def fixed_isotypic_cover_source_correction_multiplicity_linearEquiv
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
    (s : G)
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s) :
    fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar ≃ₗ[k]
      fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar :=
  fixed_isotypic_multiplicity_space_precompose_linearEquiv
    (I := I) (ρ := ρ)
    (fixed_isotypic_cover_source_correction_equiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s u)

/-- Helper for Theorem 17-17.6-1: the multiplicity-space source correction is trivial on the
distinguished chosen lift-side transport. This is the exact normalization needed when the future
`G₂`-action is checked first on the section generators of the generated cover. -/
theorem fixed_isotypic_cover_source_correction_multiplicity_linearEquiv_section_eq_refl
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
    (s : G) :
    fixed_isotypic_cover_source_correction_multiplicity_linearEquiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s
        (fixed_constituent_transport_aut_of_lift
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s) =
      LinearEquiv.refl k
        (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) := by
  rw [fixed_isotypic_cover_source_correction_multiplicity_linearEquiv,
    fixed_isotypic_cover_source_correction_equiv_section_eq_refl
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s]
  ext f x
  rfl

/-- Helper for Theorem 17-17.6-1: for the literal identity cover element, the multiplicity-space
source correction is exactly the precomposition operator induced by the canonical comparison
between the chosen reduced transport at `1` and the user-supplied comparison `hTransport 1`.
This records the entire `g = 1` source-side discrepancy in one reusable linear equivalence. -/
theorem fixed_isotypic_cover_source_correction_multiplicity_linearEquiv_identity_fiber
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
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    fixed_isotypic_cover_source_correction_multiplicity_linearEquiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (1 : G)
        (fixed_constituent_transport_fiber_one
          (A := A) (G := G) (I := I) ρA_I) =
      fixed_isotypic_multiplicity_space_precompose_linearEquiv
        (I := I) (ρ := ρ)
        ((transportedSubrepresentation_rep_equiv_local_one (I := I) (ρ := ρ) Sbar).trans
          ((hTransport (1 : G)).some.symm)) := by
  rw [fixed_isotypic_cover_source_correction_multiplicity_linearEquiv,
    fixed_isotypic_cover_source_correction_equiv,
    fixed_constituent_transport_fiber_reduction_equiv_eq_identity_transport
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift]

end

end Representation
