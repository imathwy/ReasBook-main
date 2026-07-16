import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_6_1.NormalizedKernelRepresentatives

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

/-- Helper for Theorem 17-17.6-1: choose the scalar unit attached to the normalized
representative of a class `q ∈ N̄`. -/
noncomputable def kernel_scalar_unit_value
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
    Aˣ :=
  Classical.choose <|
    normalized_kernel_scalar_exists
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q

/-- Helper for Theorem 17-17.6-1: the chosen scalar unit represents the normalized
representative as a homothety. -/
theorem kernel_scalar_unit_value_spec
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
    (normalized_kernel_representative
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2.toLinearEquiv =
        kernel_scalar_unit_value
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q •
          LinearEquiv.refl A P_S :=
  Classical.choose_spec <|
    normalized_kernel_scalar_exists
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q

/-- Helper for Theorem 17-17.6-1: the scalar attached to the identity kernel class is `1`. -/
theorem kernel_scalar_unit_value_one
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
    kernel_scalar_unit_value
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (1 :
          (generated_cover_proj_to_quotient_descends
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) =
      1 := by
  let qOne :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker := 1
  have hvalue :
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift qOne).1.2.toLinearEquiv =
        kernel_scalar_unit_value
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
            qOne • LinearEquiv.refl A P_S :=
    kernel_scalar_unit_value_spec
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift qOne
  have hone :
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift qOne).1.2.toLinearEquiv =
        (1 : Aˣ) • LinearEquiv.refl A P_S := by
    rw [normalized_kernel_representative_one
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift]
    change
      (fixed_constituent_transport_fiber_one
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)).toLinearEquiv =
        (1 : Aˣ) • LinearEquiv.refl A P_S
    simp [fixed_constituent_transport_fiber_one, Equiv.toLinearEquiv_mk']
    ext x
    simp
  exact
    normalized_kernel_scalar_unique
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      qOne hvalue hone

/-- Helper for Theorem 17-17.6-1: the chosen scalar unit is multiplicative on `N̄`. -/
theorem kernel_scalar_unit_value_mul
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
    (q₁ q₂ :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    kernel_scalar_unit_value
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (q₁ * q₂) =
      kernel_scalar_unit_value
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q₁ *
        kernel_scalar_unit_value
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q₂ := by
  let a₁ : Aˣ :=
    kernel_scalar_unit_value
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q₁
  let a₂ : Aˣ :=
    kernel_scalar_unit_value
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q₂
  let a₁₂ : Aˣ :=
    kernel_scalar_unit_value
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (q₁ * q₂)
  have h₁ :
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁).1.2.toLinearEquiv =
        a₁ • LinearEquiv.refl A P_S := by
    simpa [a₁] using
      kernel_scalar_unit_value_spec
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q₁
  have h₂ :
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₂).1.2.toLinearEquiv =
        a₂ • LinearEquiv.refl A P_S := by
    simpa [a₂] using
      kernel_scalar_unit_value_spec
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q₂
  have h₁₂ :
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
        (q₁ * q₂)).1.2.toLinearEquiv =
        a₁₂ • LinearEquiv.refl A P_S := by
    simpa [a₁₂] using
      kernel_scalar_unit_value_spec
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (q₁ * q₂)
  have hprod :
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
        (q₁ * q₂)).1.2.toLinearEquiv =
        (a₁ * a₂) • LinearEquiv.refl A P_S := by
    calc
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
        (q₁ * q₂)).1.2.toLinearEquiv =
          ((normalized_kernel_representative
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
            q₂).1.2.toLinearEquiv).trans
            ((normalized_kernel_representative
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
              q₁).1.2.toLinearEquiv) := by
            exact
              normalized_kernel_second_coordinate_mul
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁ q₂
      _ = (a₂ • LinearEquiv.refl A P_S).trans (a₁ • LinearEquiv.refl A P_S) := by
            rw [h₂, h₁]
      _ = (a₂ * a₁) • LinearEquiv.refl A P_S := by
            exact unit_smul_linearEquiv_refl_trans (A := A) a₂ a₁
      _ = (a₁ * a₂) • LinearEquiv.refl A P_S := by
            rw [mul_comm]
  have ha :=
    normalized_kernel_scalar_unique
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (q₁ * q₂) h₁₂ hprod
  simpa [a₁, a₂, a₁₂] using ha

/-- Helper for Theorem 17-17.6-1: the scalar extracted from the normalized representative of
`q ∈ N̄` is multiplicative. This packages Serre's kernel object `U₁ = Aˣ` as an actual monoid
homomorphism on `N̄`, ready for the later residue-class comparison. -/
noncomputable def kernel_scalar_unit
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
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker →* Aˣ where
  toFun :=
    kernel_scalar_unit_value
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  map_one' :=
    kernel_scalar_unit_value_one
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  map_mul' :=
    kernel_scalar_unit_value_mul
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift

/-- Helper for Theorem 17-17.6-1: the monoid hom `kernel_scalar_unit` records the actual scalar
chosen for each normalized representative of `q ∈ N̄`. This keeps later residue-class arguments
from reopening the underlying `Classical.choose` witness. -/
theorem kernel_scalar_unit_spec
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
    (normalized_kernel_representative
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2.toLinearEquiv =
        kernel_scalar_unit
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q •
          LinearEquiv.refl A P_S := by
  exact
    kernel_scalar_unit_value_spec
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q

/-- Helper for Theorem 17-17.6-1: transport-fiber equivalences over equal group elements are
heterogeneously equal when their underlying linear equivalences agree. -/
private theorem transport_fiber_heq_of_toLinearEquiv_eq
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    {s t : G} (hst : s = t)
    {u : fixed_constituent_transport_fiber (A := A) (G := G) I ρA_I s}
    {v : fixed_constituent_transport_fiber (A := A) (G := G) I ρA_I t}
    (h : u.toLinearEquiv = v.toLinearEquiv) :
    HEq u v := by
  subst t
  apply heq_of_eq
  exact Equiv.toLinearEquiv_injective h

/-- Helper for Theorem 17-17.6-1: once the candidate determinant subgroup is placed inside the
bounded roots-of-unity owner `D̄`, the remaining work is the literal Serre package
`G₂`, `I₂`, `N̄`, `τ`, and tensor descent. This keeps the final blocker separate from the already
formalized closure step. -/
theorem candidate_subgroup_cyclic_and_coprime_of_bounded_containment
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
    (hcandidate_le :
      let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
      let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
      let Dbar := (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map (QuotientGroup.mk' Qd)
      fixed_constituent_projective_extension_candidate_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift ≤
        Dbar) :
      IsCyclic
          (fixed_constituent_projective_extension_candidate_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) ∧
        Nat.Coprime p
          (Nat.card
            (fixed_constituent_projective_extension_candidate_subgroup
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)) := by
  let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
  let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
  let n := Nat.lcm (Nat.card G) (Nat.card C)
  let Dbar := (rootsOfUnity n k).map (QuotientGroup.mk' Qd)
  let Candidate :=
    fixed_constituent_projective_extension_candidate_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  have hn : n ≠ 0 := by
    exact
      (Nat.lcm_pos
        (Nat.card_pos (α := G))
        (Nat.card_pos (α := C))).ne'
  letI : NeZero n := ⟨hn⟩
  have hle : Candidate ≤ Dbar := by
    simpa [Candidate, Dbar, n, C, Qd] using hcandidate_le
  have hroots_cyclic : IsCyclic (rootsOfUnity n k) :=
    finite_subgroup_of_residue_units_isCyclic (A := A) (D := rootsOfUnity n k)
  have hDbar_cyclic : IsCyclic Dbar := by
    letI : IsCyclic (rootsOfUnity n k) := hroots_cyclic
    exact
      isCyclic_of_surjective
        ((QuotientGroup.mk' Qd).subgroupMap (rootsOfUnity n k))
        ((QuotientGroup.mk' Qd).subgroupMap_surjective (rootsOfUnity n k))
  have hroots_coprime : Nat.Coprime p (Nat.card (rootsOfUnity n k)) :=
    roots_of_unity_card_coprime_charP (A := A) hp hn
  have hDbar_card_dvd : Nat.card Dbar ∣ Nat.card (rootsOfUnity n k) := by
    simpa [Dbar] using
      (Subgroup.card_map_dvd
        (H := rootsOfUnity n k)
        (f := QuotientGroup.mk' Qd))
  have hDbar_coprime : Nat.Coprime p (Nat.card Dbar) :=
    hroots_coprime.of_dvd_right hDbar_card_dvd
  have hCandidate_coprime : Nat.Coprime p (Nat.card Candidate) :=
    hDbar_coprime.of_dvd_right (Subgroup.card_dvd_of_le hle)
  constructor
  · exact @Subgroup.isCyclic_of_le (kˣ ⧸ Qd) _ Candidate Dbar hle hDbar_cyclic
  · simpa [Candidate] using hCandidate_coprime

/-- Helper for Theorem 17-17.6-1: every residue class coming from Serre's determinant subgroup
`C` has order dividing the cardinal of the explicit candidate subgroup. This freezes the
finite-order input needed before converting quotient-level determinant identities into literal
upstairs statements. -/
theorem fixed_constituent_determinant_subgroup_residue_class_pow_card_eq_one
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
    (c : fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I) :
    let Candidate :=
      fixed_constituent_projective_extension_candidate_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
      let n := Nat.card Candidate
      (fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I c) ^ n = 1 := by
  let Candidate :=
    fixed_constituent_projective_extension_candidate_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let n := Nat.card Candidate
  haveI : Finite Candidate :=
    fixed_constituent_projective_extension_candidate_finite
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  let x : Candidate :=
    ⟨fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I c,
      fixed_constituent_determinant_subgroup_residue_class_mem_candidate
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift c⟩
  have hx : x ^ n = 1 := by
    simpa [n] using (pow_card_eq_one' (x := x))
  exact congrArg (fun y : Candidate => (y : kˣ ⧸ (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)) hx

/-- Helper for Theorem 17-17.6-1: the determinant of the Hall-kernel transport fiber is the
determinant generator attached to the underlying element of `I`. -/
private theorem hallKernel_transport_fiber_det_eq_action_det
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

/-- Helper for Theorem 17-17.6-1: the Hall-kernel correction used to normalize a kernel class has
determinant in Serre's determinant subgroup `C`. -/
private theorem normalized_kernel_correction_det_mem_determinant_subgroup
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
  rw [hallKernel_transport_fiber_det_eq_action_det]
  exact
    Subgroup.subset_closure
      ⟨normalized_kernel_representative_correction
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q,
        rfl⟩

/-- Helper for Theorem 17-17.6-1: the raw quotient representative determinant class agrees with
the determinant class of its Hall-kernel correction. -/
private theorem kernel_out_det_class_eq_correction_det_class
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
        normalized_kernel_correction_det_mem_determinant_subgroup
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
          normalized_kernel_correction_det_mem_determinant_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q⟩ := by
        simp only [fixed_constituent_determinant_subgroup_residue_class, detHall, Qd, d, res]

/-- Helper for Theorem 17-17.6-1: the raw determinant class of the quotient-out representative of
`q ∈ N̄` also has order dividing the cardinal of the candidate subgroup, because it agrees with
the literal Hall-kernel correction class in Serre's determinant subgroup `C`. -/
theorem kernel_out_representative_det_residue_class_pow_card_eq_one
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
    let Candidate :=
      fixed_constituent_projective_extension_candidate_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let n := Nat.card Candidate
    let d := Module.finrank A P_S
    let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
    (QuotientGroup.mk' Qd
      (Units.map (IsLocalRing.residue A)
        (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) q.1.out.1.2))) ^ n = 1 := by
  let Candidate :=
    fixed_constituent_projective_extension_candidate_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let n := Nat.card Candidate
  let d := Module.finrank A P_S
  let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
  obtain ⟨c, hc⟩ :=
    kernel_out_det_class_eq_correction_det_class
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hc' :
      QuotientGroup.mk' Qd
          (Units.map (IsLocalRing.residue A)
            (fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) q.1.out.1.2)) =
        fixed_constituent_determinant_subgroup_residue_class
          (A := A) (G := G) (I := I) ρA_I c := by
    simpa [Qd, d] using hc
  have hpow :
      (fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I c) ^ n = 1 := by
    simpa [Candidate, n] using
      fixed_constituent_determinant_subgroup_residue_class_pow_card_eq_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift c
  calc
    (QuotientGroup.mk' Qd
        (Units.map (IsLocalRing.residue A)
          (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) q.1.out.1.2))) ^ n =
      (fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I c) ^ n := by
        rw [hc']
    _ = 1 := hpow

/-- Helper for Theorem 17-17.6-1: the normalized scalar attached to `q ∈ N̄` determines `q`
itself. This packages the already normalized representative-level uniqueness into an injective
map `N̄ → Aˣ`, leaving only the bounded-image step before Serre's cyclic prime-to-`p` kernel
package closes. -/
theorem kernel_scalar_unit_injective
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
      Function.Injective
        (kernel_scalar_unit
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift) := by
  intro q₁ q₂ hscalar
  let rep :=
    normalized_kernel_representative
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let kernelScalar :=
    kernel_scalar_unit
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  let I2 :=
    fixed_constituent_generated_cover_hall_kernel_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  have hproj (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
      (rep q).1.1 = 1 := by
    simpa [rep, fixed_constituent_transport_total_space_proj_hom,
      fixed_constituent_transport_total_space_proj] using
      normalized_kernel_representative_proj_eq_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hrep_eq : rep q₁ = rep q₂ := by
    apply Subtype.ext
    apply Sigma.ext
    · exact (hproj q₁).trans (hproj q₂).symm
    · refine
        transport_fiber_heq_of_toLinearEquiv_eq
          (A := A) (G := G) I ρA_I
          ((hproj q₁).trans (hproj q₂).symm) ?_
      have hlin₁ :
          (rep q₁).1.2.toLinearEquiv =
            kernelScalar q₁ • LinearEquiv.refl A P_S := by
        simpa [rep, kernelScalar] using
          kernel_scalar_unit_spec
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
            hTransportLift q₁
      have hlin₂ :
          (rep q₂).1.2.toLinearEquiv =
            kernelScalar q₂ • LinearEquiv.refl A P_S := by
        simpa [rep, kernelScalar] using
          kernel_scalar_unit_spec
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
            hTransportLift q₂
      calc
        (rep q₁).1.2.toLinearEquiv =
            kernelScalar q₁ • LinearEquiv.refl A P_S := hlin₁
        _ = kernelScalar q₂ • LinearEquiv.refl A P_S := by rw [hscalar]
        _ = (rep q₂).1.2.toLinearEquiv := hlin₂.symm
  apply Subtype.ext
  have hmk₁ :
      QuotientGroup.mk' I2 (rep q₁) = q₁.1 := by
    simpa [I2, rep] using
      normalized_kernel_representative_mk_eq
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁
  have hmk₂ :
      QuotientGroup.mk' I2 (rep q₂) = q₂.1 := by
    simpa [I2, rep] using
      normalized_kernel_representative_mk_eq
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₂
  calc
    q₁.1 = QuotientGroup.mk' I2 (rep q₁) := hmk₁.symm
    _ = QuotientGroup.mk' I2 (rep q₂) := by rw [hrep_eq]
    _ = q₂.1 := hmk₂

/-- Helper for Theorem 17-17.6-1: a scalar homothety on the fixed lifted constituent is an
element of Serre's kernel fiber `U₁`. This keeps the later centrality argument at the literal
total-space level instead of reopening the transport normalization data each time. -/
theorem scalar_transport_fiber_one_isIntertwining
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (a : Aˣ) :
    Representation.IsIntertwiningMap
      (ρA_I.comp (MulAut.conjNormal (1 : G)⁻¹).toMonoidHom)
      ρA_I
      (((a • LinearEquiv.refl A P_S : P_S ≃ₗ[A] P_S) : P_S →ₗ[A] P_S)) := by
  -- The source action is unchanged after conjugating by `1`, and scalar homotheties commute
  -- with every `A`-linear operator.
  refine Representation.IsIntertwiningMap.mk ?_
  intro g x
  simp

/-- Helper for Theorem 17-17.6-1: package a scalar unit as the corresponding element of the
kernel fiber `U₁` in Serre's transport total space. -/
noncomputable def scalar_transport_fiber_one
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (a : Aˣ) :
    fixed_constituent_transport_fiber
      (A := A) (G := G) I ρA_I (1 : G) :=
  Representation.Equiv.mk (a • LinearEquiv.refl A P_S)
    fun g ↦ by
      ext x
      exact (scalar_transport_fiber_one_isIntertwining
        (A := A) (G := G) (I := I) ρA_I a).isIntertwining g x

/-- Helper for Theorem 17-17.6-1: scalar elements in Serre's kernel fiber commute with every
element of the transport total space. This is the literal source-level reason that the later
kernel subgroup is central after quotienting by the embedded Hall kernel. -/
theorem scalar_transport_total_space_commutes
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (a : Aˣ)
    (g : fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I) :
      fixed_constituent_transport_total_space_mul
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          ⟨1, scalar_transport_fiber_one (A := A) (G := G) (I := I) ρA_I a⟩ g =
        fixed_constituent_transport_total_space_mul
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          g ⟨1, scalar_transport_fiber_one (A := A) (G := G) (I := I) ρA_I a⟩ := by
  rcases g with ⟨s, u⟩
  apply Sigma.ext
  · simp [fixed_constituent_transport_total_space_mul]
  · refine
      transport_fiber_heq_of_toLinearEquiv_eq
        (A := A) (G := G) I ρA_I
        ((one_mul s).trans (mul_one s).symm) ?_
    ext x
    simp [fixed_constituent_transport_total_space_mul,
      fixed_constituent_transport_fiber_comp, scalar_transport_fiber_one,
      Equiv.toLinearEquiv_mk', smul_smul]

/-- Helper for Theorem 17-17.6-1: every normalized representative of a class in `N̄` is literally
the scalar point `(1, a • id)` in Serre's transport total space. This is the transport-stable
form of the scalar extraction used in the centrality argument. -/
theorem normalized_kernel_representative_eq_scalar_total_space
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
    (normalized_kernel_representative
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1 =
        ⟨1,
          scalar_transport_fiber_one
            (A := A) (G := G) (I := I) ρA_I
            (kernel_scalar_unit
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q)⟩ := by
  let rep :=
    normalized_kernel_representative
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  let a : Aˣ :=
    kernel_scalar_unit
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hproj : rep.1.1 = 1 := by
    simpa [rep, fixed_constituent_transport_total_space_proj_hom,
      fixed_constituent_transport_total_space_proj] using
      normalized_kernel_representative_proj_eq_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hlin : rep.1.2.toLinearEquiv = a • LinearEquiv.refl A P_S := by
    simpa [rep, a] using
      kernel_scalar_unit_spec
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hscalar :
      (scalar_transport_fiber_one
        (A := A) (G := G) (I := I) ρA_I a).toLinearEquiv =
        a • LinearEquiv.refl A P_S := by
    simp [scalar_transport_fiber_one, Equiv.toLinearEquiv_mk']
  change
    rep.1 =
      ⟨1, scalar_transport_fiber_one (A := A) (G := G) (I := I) ρA_I a⟩
  apply Sigma.ext
  · exact hproj
  · exact
      transport_fiber_heq_of_toLinearEquiv_eq
        (A := A) (G := G) I ρA_I hproj (hlin.trans hscalar.symm)

/-- Helper for Theorem 17-17.6-1: the second coordinate of the normalized representative is
already the scalar kernel-fiber element classified by `kernel_scalar_unit`. This keeps later
kernel calculations at the fiber level instead of reopening the total-space first coordinate. -/
theorem normalized_kernel_representative_eq_scalar_fiber
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
    HEq
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2
        (scalar_transport_fiber_one
        (A := A) (G := G) (I := I) ρA_I
        (kernel_scalar_unit
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q)) := by
  let rep :=
    normalized_kernel_representative
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  let a : Aˣ :=
    kernel_scalar_unit
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hproj : rep.1.1 = 1 := by
    simpa [rep, fixed_constituent_transport_total_space_proj_hom,
      fixed_constituent_transport_total_space_proj] using
      normalized_kernel_representative_proj_eq_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hlin : rep.1.2.toLinearEquiv = a • LinearEquiv.refl A P_S := by
    simpa [rep, a] using
      kernel_scalar_unit_spec
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hscalar :
      (scalar_transport_fiber_one
        (A := A) (G := G) (I := I) ρA_I a).toLinearEquiv =
        a • LinearEquiv.refl A P_S := by
    simp [scalar_transport_fiber_one, Equiv.toLinearEquiv_mk']
  simpa [rep, a] using
    transport_fiber_heq_of_toLinearEquiv_eq
      (A := A) (G := G) I ρA_I hproj (hlin.trans hscalar.symm)

/-- Helper for Theorem 17-17.6-1: after rewriting a normalized kernel representative as the
literal scalar point `(1, a • id)`, its determinant is exactly `a^d`. This isolates the scalar
determinant computation before the remaining comparison with Serre's determinant subgroup `C`. -/
theorem normalized_kernel_representative_det_eq_kernel_scalar_pow
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
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2 =
        kernel_scalar_unit
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q ^
          Module.finrank A P_S := by
  unfold fixed_constituent_transport_fiber_det
  rw [kernel_scalar_unit_spec
    (p := p) (A := A) (G := G) (V := V)
    hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q]
  exact
    linearEquiv_det_unit_smul_refl
      (A := A) (M := P_S)
      (kernel_scalar_unit
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q)

/-- Helper for Theorem 17-17.6-1: the determinant-membership goal for a normalized kernel
representative is exactly the source statement that the attached scalar `kernelScalar(q)` has
`d`-th power in Serre's determinant subgroup `C`. -/
theorem normalized_kernel_representative_det_mem_determinant_subgroup_iff_kernel_scalar_pow_mem
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
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2 ∈
      fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I ↔
      kernel_scalar_unit
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q ^
        Module.finrank A P_S ∈
          fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I := by
  rw [normalized_kernel_representative_det_eq_kernel_scalar_pow
    (p := p) (A := A) (G := G) (V := V)
    hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q]

end

end Representation
