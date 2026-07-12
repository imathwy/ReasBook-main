import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_6_1.GeneratedCoverKernelPackaging

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

/-- Helper for Theorem 17-17.6-1: for a fixed class `q ∈ N̄ = ker(pi₂)`, the representative in
`G₂` lying over `1 ∈ G` is unique. This is the structural step in Serre's source route that makes
the later scalar unit attached to `q` independent of choices. -/
theorem normalized_kernel_representative_unique
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
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker)
    {g₁ g₂ :
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift}
    (hg₁ :
      QuotientGroup.mk'
          (fixed_constituent_generated_cover_hall_kernel_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
          g₁ =
        q.1)
    (hg₂ :
      QuotientGroup.mk'
          (fixed_constituent_generated_cover_hall_kernel_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
          g₂ =
        q.1)
    (hg₁_one :
      ((fixed_constituent_transport_total_space_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype
          (fixed_constituent_generated_cover_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift))) g₁ =
        1)
    (hg₂_one :
      ((fixed_constituent_transport_total_space_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype
            (fixed_constituent_generated_cover_subgroup
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift))) g₂ =
          1) :
      g₁ = g₂ := by
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let I2 :=
    fixed_constituent_generated_cover_hall_kernel_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi : G2 →* G :=
    (fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp (Subgroup.subtype G2)
  have hquot : QuotientGroup.mk' I2 g₁ = QuotientGroup.mk' I2 g₂ := by
    rw [hg₁, hg₂]
  have hdiff_mem : g₁⁻¹ * g₂ ∈ I2 := by
    exact (QuotientGroup.eq).mp hquot
  rcases hdiff_mem with ⟨x, hx⟩
  have hg₁_pi : pi g₁ = 1 := by
    simpa [pi, G2] using hg₁_one
  have hg₂_pi : pi g₂ = 1 := by
    simpa [pi, G2] using hg₂_one
  have hpi_diff : pi (g₁⁻¹ * g₂) = 1 := by
    calc
      pi (g₁⁻¹ * g₂) = (pi g₁)⁻¹ * pi g₂ := by simp
      _ = 1 := by
        simp [hg₁_pi, hg₂_pi]
  have hx_val : (x : G) = 1 := by
    have hxpi :
        pi
            (fixed_constituent_generated_cover_embed_hall_kernel
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x) =
          1 := by
      rw [hx]
      exact hpi_diff
    simpa [pi, G2, fixed_constituent_generated_cover_embed_hall_kernel,
      fixed_constituent_transport_total_space_embed_hall_kernel,
      fixed_constituent_transport_total_space_proj_hom,
      fixed_constituent_transport_total_space_proj] using hxpi
  have hx_one : x = 1 := Subtype.ext hx_val
  have hdiff_one : g₁⁻¹ * g₂ = 1 := by
    rw [← hx, hx_one]
    simp
  exact inv_mul_eq_one.mp hdiff_one

/-- Helper for Theorem 17-17.6-1: the quotient-out representative of a kernel class in `N̄`
already represents that class in `G₂ ⧸ I₂`. This lets the later normalized representative be
defined as literal data rather than by carrying witnesses through the main package proof. -/
theorem normalized_kernel_out_represents_class
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
    QuotientGroup.mk'
        (fixed_constituent_generated_cover_hall_kernel_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
        q.1.out =
      q.1 := by
  -- This is the canonical quotient representative used in the normalized kernel package.
  simpa using QuotientGroup.out_eq' q.1

/-- Helper for Theorem 17-17.6-1: choose the Hall-kernel correction that moves the quotient-out
representative of `q ∈ N̄` into the fiber over `1 ∈ G`. -/
noncomputable def normalized_kernel_representative_correction
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
    I :=
  Classical.choose <|
    generated_cover_kernel_has_normalized_representative
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q q.1.out
      (normalized_kernel_out_represents_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q)

/-- Helper for Theorem 17-17.6-1: the Hall-kernel correction chosen to normalize `q.1.out`
is exactly the projection of that quotient-out representative to `I`. This isolates the
source-faithful same-fiber comparison used later when the raw representative is divided by its
Hall-kernel correction. -/
theorem normalized_kernel_representative_correction_val_eq_out_proj
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
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let pi : G2 →* G :=
      (fixed_constituent_transport_total_space_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype G2)
    (normalized_kernel_representative_correction
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q : G) =
      pi q.1.out := by
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi : G2 →* G :=
    (fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype G2)
  have hspec :=
    Classical.choose_spec <|
      generated_cover_kernel_has_normalized_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q q.1.out
        (normalized_kernel_out_represents_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q)
  -- Read off the first component of the chosen normalization witness.
  simpa [G2, pi, normalized_kernel_representative_correction] using hspec.1.symm

/-- Helper for Theorem 17-17.6-1: choose the unique normalized representative of a kernel class
`q ∈ N̄`, i.e. the literal element of `G₂` representing `q` whose projection to `G` is `1`. -/
noncomputable def normalized_kernel_representative
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
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift :=
  q.1.out *
    (fixed_constituent_generated_cover_embed_hall_kernel
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
      (normalized_kernel_representative_correction
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q))⁻¹

/-- Helper for Theorem 17-17.6-1: the chosen normalized representative lies over `1 ∈ G`. This
is the exact source normalization needed before extracting a scalar from the `U₁ = Aˣ` fiber. -/
theorem normalized_kernel_representative_proj_eq_one
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
    ((fixed_constituent_transport_total_space_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype
        (fixed_constituent_generated_cover_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)))
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q) =
      1 := by
  have hspec :=
    Classical.choose_spec <|
      generated_cover_kernel_has_normalized_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q q.1.out
        (normalized_kernel_out_represents_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q)
  -- Read off the second component of the normalization witness for the chosen correction.
  simpa [normalized_kernel_representative, normalized_kernel_representative_correction] using
    hspec.2.1

/-- Helper for Theorem 17-17.6-1: the chosen normalized representative still represents the
original class `q ∈ N̄` in `G₂ ⧸ I₂`. -/
theorem normalized_kernel_representative_mk_eq
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
    QuotientGroup.mk'
        (fixed_constituent_generated_cover_hall_kernel_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q) =
      q.1 := by
  have hspec :=
    Classical.choose_spec <|
      generated_cover_kernel_has_normalized_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q q.1.out
        (normalized_kernel_out_represents_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q)
  -- The Hall-kernel correction does not change the quotient class.
  simpa [normalized_kernel_representative, normalized_kernel_representative_correction] using
    hspec.2.2

/-- Helper for Theorem 17-17.6-1: the fiber coordinate of the normalized representative lies in
Serre's kernel fiber `U₁ = Aˣ`, so the existing scalar-classification theorem already produces a
unit homothety for it. This is the first scalar bridge needed for the later kernel package on
`N̄`. -/
theorem normalized_kernel_scalar_exists
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
    ∃ a : Aˣ,
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2.toLinearEquiv =
        a • LinearEquiv.refl A P_S := by
  let uG2 :=
    normalized_kernel_representative
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  change ∃ a : Aˣ, uG2.1.2.toLinearEquiv = a • LinearEquiv.refl A P_S
  have hu_proj :
      ((fixed_constituent_transport_total_space_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype
          (fixed_constituent_generated_cover_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift))) uG2 =
        1 := by
    simpa [uG2] using
      normalized_kernel_representative_proj_eq_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hu_index : uG2.1.1 = 1 := by
    simpa [fixed_constituent_transport_total_space_proj_hom,
      fixed_constituent_transport_total_space_proj] using hu_proj
  cases hrep : uG2.1 with
  | mk s us =>
      have hs : s = 1 := by
        simpa [hrep] using hu_index
      subst s
      simpa [hrep] using
        fixed_constituent_transport_kernel_eq_unit_smul_id_of_endomorphism_scalar
          (A := A) (G := G) (I := I) ρA_I
          (fun f ↦
            fixed_constituent_lift_equivariant_endomorphism_scalar
              (A := A) (G := G) (V := V) hp I hIcop (ρ := ρ) (Sbar := Sbar)
              hSbar_irred ρA_I red_S hLiftSbar f)
          us

/-- Helper for Theorem 17-17.6-1: on a nontrivial free finite module, a scalar homothety is
determined by its underlying linear equivalence. This is the uniqueness bridge needed when the
normalized kernel representative is rewritten as a scalar unit. -/
theorem unit_smul_linearEquiv_refl_injective
    {M : Type*} [AddCommGroup M] [Module A M]
    [Module.Free A M] [Module.Finite A M] [Nontrivial M]
    {a b : Aˣ}
    (h : (a • LinearEquiv.refl A M : M ≃ₗ[A] M) = b • LinearEquiv.refl A M) :
    a = b := by
  let basis := Module.finBasis A M
  have hfinrank_pos : 0 < Module.finrank A M :=
    (Module.finrank_pos_iff_of_free (R := A) (M := M)).2 inferInstance
  have hidx : Nonempty (Fin (Module.finrank A M)) :=
    Fin.pos_iff_nonempty.mp hfinrank_pos
  let i : Fin (Module.finrank A M) := Classical.choice hidx
  -- Evaluate the two homotheties on one basis vector and read off its `i`-th coordinate.
  have hcoord :
      basis.repr (((a • LinearEquiv.refl A M : M ≃ₗ[A] M) (basis i))) i =
        basis.repr (((b • LinearEquiv.refl A M : M ≃ₗ[A] M) (basis i))) i := by
    exact congrArg (fun x ↦ basis.repr x i) (LinearEquiv.congr_fun h (basis i))
  have hab : (a : A) = (b : A) := by
    simpa [basis, smul_eq_mul] using hcoord
  exact Units.ext hab

/-- Helper for Theorem 17-17.6-1: the normalized representative of the identity kernel class is
the identity element of `G₂`. This pins down the base point before the scalar map is assembled. -/
theorem normalized_kernel_representative_one
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
      normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift 1 =
        1 := by
  refine
    normalized_kernel_representative_unique
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
      (q := 1) ?_ ?_ ?_ ?_
  · simpa using
      normalized_kernel_representative_mk_eq
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
        (1 :
          (generated_cover_proj_to_quotient_descends
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker)
  · rfl
  · simpa using
      normalized_kernel_representative_proj_eq_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
        (1 :
          (generated_cover_proj_to_quotient_descends
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker)
  · rfl

/-- Helper for Theorem 17-17.6-1: normalized representatives multiply exactly as their classes in
`N̄ = ker(pi₂)`. This is the structural pivot that makes the later scalar assignment multiplicative
without reopening the Hall-kernel correction bookkeeping. -/
theorem normalized_kernel_representative_mul
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
    (q₁ q₂ :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (q₁ * q₂) =
        normalized_kernel_representative
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁ *
          normalized_kernel_representative
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₂ := by
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let I2 :=
    fixed_constituent_generated_cover_hall_kernel_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi : G2 →* G :=
    (fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp (Subgroup.subtype G2)
  let rep :=
    normalized_kernel_representative
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  refine
    normalized_kernel_representative_unique
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
      (q := q₁ * q₂) ?_ ?_ ?_ ?_
  · simpa [rep] using
      normalized_kernel_representative_mk_eq
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
        (q₁ * q₂)
  · have hq₁ :
        QuotientGroup.mk' I2 (rep q₁) = q₁.1 := by
      simpa [I2, rep] using
        normalized_kernel_representative_mk_eq
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁
    have hq₂ :
        QuotientGroup.mk' I2 (rep q₂) = q₂.1 := by
      simpa [I2, rep] using
        normalized_kernel_representative_mk_eq
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₂
    calc
      QuotientGroup.mk' I2 (rep q₁ * rep q₂) =
          QuotientGroup.mk' I2 (rep q₁) * QuotientGroup.mk' I2 (rep q₂) := by
            simp
      _ = q₁.1 * q₂.1 := by
            rw [hq₁, hq₂]
      _ = (q₁ * q₂).1 := rfl
  · simpa [rep] using
      normalized_kernel_representative_proj_eq_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
        (q₁ * q₂)
  · have hq₁_proj : pi (rep q₁) = 1 := by
      simpa [pi, G2, rep] using
        normalized_kernel_representative_proj_eq_one
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁
    have hq₂_proj : pi (rep q₂) = 1 := by
      simpa [pi, G2, rep] using
        normalized_kernel_representative_proj_eq_one
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₂
    change pi (rep q₁ * rep q₂) = 1
    simp [hq₁_proj, hq₂_proj]

/-- Helper for Theorem 17-17.6-1: after normalizing representatives inside `N̄ = ker(pi₂)`,
their second coordinates compose exactly as Serre's total-space multiplication says they should.
This is the transport-stable bridge from representative multiplication to scalar multiplication on
the fixed lifted constituent carrier. -/
theorem normalized_kernel_second_coordinate_mul
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
    (q₁ q₂ :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    (normalized_kernel_representative
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (q₁ * q₂)).1.2.toLinearEquiv =
      ((normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₂).1.2.toLinearEquiv).trans
        ((normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁).1.2.toLinearEquiv) := by
  let rep :=
    normalized_kernel_representative
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  have hmul : rep (q₁ * q₂) = rep q₁ * rep q₂ := by
    simpa [rep] using
      normalized_kernel_representative_mul
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁ q₂
  change
    (rep (q₁ * q₂)).1.2.toLinearEquiv =
      (rep q₂).1.2.toLinearEquiv.trans (rep q₁).1.2.toLinearEquiv
  rw [hmul]
  change
    (fixed_constituent_transport_fiber_comp
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      (rep q₁).1.2 (rep q₂).1.2).toLinearEquiv =
        (rep q₂).1.2.toLinearEquiv.trans (rep q₁).1.2.toLinearEquiv
  rfl

/-- Helper for Theorem 17-17.6-1: the scalar unit attached to a normalized kernel representative
is unique once the lift carrier is known to have positive rank. This is the bridge from
representative-level uniqueness to the later monoid-hom construction on `N̄`. -/
theorem normalized_kernel_scalar_unique
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
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker)
    {a b : Aˣ}
    (ha :
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2.toLinearEquiv =
        a • LinearEquiv.refl A P_S)
    (hb :
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2.toLinearEquiv =
        b • LinearEquiv.refl A P_S) :
    a = b := by
  have hfinrank_ne_zero : Module.finrank A P_S ≠ 0 :=
    fixed_constituent_lift_finrank_ne_zero
      (A := A) (G := G) (I := I) hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar
  have hfinrank_pos : 0 < Module.finrank A P_S :=
    Nat.pos_of_ne_zero hfinrank_ne_zero
  letI : Nontrivial P_S := Module.nontrivial_of_finrank_pos (R := A) hfinrank_pos
  -- Once the two scalar homotheties are identified as the same transport operator, the unit is
  -- forced.
  exact
    unit_smul_linearEquiv_refl_injective
      (A := A) (M := P_S) (ha.symm.trans hb)

/-- Helper for Theorem 17-17.6-1: scalar homotheties on a free module compose by multiplying the
underlying units. This is the linear-algebra normalization needed when Serre's kernel
representatives are multiplied upstairs in `G₂`. -/
theorem unit_smul_linearEquiv_refl_trans
    {M : Type*} [AddCommGroup M] [Module A M]
    (a b : Aˣ) :
    (a • LinearEquiv.refl A M).trans (b • LinearEquiv.refl A M) =
      (a * b) • LinearEquiv.refl A M := by
  -- Both sides act on each vector by the same scalar multiplication.
  ext x
  simp [smul_smul, mul_assoc]

end

end Representation
