import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_6_1.NormalizedSectionDeterminants

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

/-- Helper for Theorem 17-17.6-1: Serre's finite-cover subgroup `G₂` is the closure of the chosen
section image together with the embedded Hall kernel inside the total-space cover `G₁`. Naming
this subgroup isolates the literal source generators before quotienting by `I₂`. -/
noncomputable def fixed_constituent_generated_cover_subgroup
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
    Subgroup
      (fixed_constituent_transport_total_space
        (A := A) (G := G) I ρA_I) :=
  Subgroup.closure
    (Set.range
        (fixed_constituent_transport_total_space_section
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) ∪
      Set.range
        (fixed_constituent_transport_total_space_embed_hall_kernel
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)))

/-- Helper for Theorem 17-17.6-1: every chosen section value lies in the generated-cover subgroup
`G₂`. This is the source-faithful surjectivity witness for the later quotient map `G₂ → G`. -/
theorem fixed_constituent_section_mem_generated_cover
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
    fixed_constituent_transport_total_space_section
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s ∈
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift := by
  -- The chosen section image is one of the literal generators used to define `G₂`.
  exact
    Subgroup.subset_closure <|
      Or.inl
        ⟨s, rfl⟩

/-- Helper for Theorem 17-17.6-1: the embedded Hall-kernel copy lies in the generated-cover
subgroup `G₂`. This is the second source generator family in Serre's definition of `G₂`. -/
theorem fixed_constituent_embed_hall_kernel_mem_generated_cover
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
    (x : I) :
    fixed_constituent_transport_total_space_embed_hall_kernel
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) x ∈
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift := by
  -- The embedded Hall kernel is the other generator family in the defining closure of `G₂`.
  exact
    Subgroup.subset_closure <|
      Or.inr
        ⟨x, rfl⟩

/-- Helper for Theorem 17-17.6-1: restricting the total-space projection `G₁ → G` to the
generated-cover subgroup `G₂` is still surjective, because the chosen section values already lie
in `G₂`. This is the first structural fact needed before passing to `G₂ / I₂`. -/
theorem fixed_constituent_generated_cover_proj_surjective
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
    Function.Surjective
      ((fixed_constituent_transport_total_space_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype
          (fixed_constituent_generated_cover_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift))) := by
  intro s
  refine
    ⟨⟨fixed_constituent_transport_total_space_section
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s,
      fixed_constituent_section_mem_generated_cover
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s⟩, ?_⟩
  rfl

/-- Helper for Theorem 17-17.6-1: the literal Hall-kernel embedding `I → G₁` restricts to the
generated-cover subgroup `G₂`. This is the canonical source-faithful map used to define Serre's
subgroup `I₂ ≤ G₂`. -/
noncomputable def fixed_constituent_generated_cover_embed_hall_kernel
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
    I →*
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift :=
  MonoidHom.codRestrict
    (fixed_constituent_transport_total_space_embed_hall_kernel
      (A := A) (G := G) (I := I) (ρA_I := ρA_I))
    (fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
    (fun x ↦
      fixed_constituent_embed_hall_kernel_mem_generated_cover
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x)

/-- Helper for Theorem 17-17.6-1: the embedded Hall-kernel point inside `G₂` still projects to
the original Hall-kernel element in `G`. This fixes the projection formula before quotienting by
`I₂`. -/
@[simp] private theorem fixed_constituent_generated_cover_proj_apply_embed_hall_kernel
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
    (x : I) :
    ((fixed_constituent_transport_total_space_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype
        (fixed_constituent_generated_cover_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)))
      (fixed_constituent_generated_cover_embed_hall_kernel
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x) =
      x := by
  -- The codomain restriction to `G₂` leaves the original Hall-kernel embedding unchanged.
  rfl

/-- Helper for Theorem 17-17.6-1: Serre's subgroup `I₂ ≤ G₂` is the range of the embedded
Hall-kernel copy. Naming it now isolates the first quotient object in the finite-cover package. -/
noncomputable def fixed_constituent_generated_cover_hall_kernel_subgroup
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
    Subgroup
      (fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) :=
  (fixed_constituent_generated_cover_embed_hall_kernel
    (p := p) (A := A) (G := G) (V := V)
    hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).range

omit [HenselianLocalRing A] [CharP (IsLocalRing.ResidueField A) p] [Finite G] in
/-- Helper for Theorem 17-17.6-1: transport-fiber elements over equal group elements are
heterogeneously equal when their underlying maps on the fixed lift carrier agree. -/
private theorem fixed_constituent_generated_cover_transport_fiber_heq_of_apply_eq
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    {s t : G} (hst : s = t)
    {u : fixed_constituent_transport_fiber (A := A) (G := G) I ρA_I s}
    {v : fixed_constituent_transport_fiber (A := A) (G := G) I ρA_I t}
    (h : ∀ z : P_S, u z = v z) :
    HEq u v := by
  subst t
  apply heq_of_eq
  ext z
  exact h z

/-- Helper for Theorem 17-17.6-1: the Hall-kernel copy in Serre's transport total space is
stable under conjugation by total-space elements, with conjugation computed on the ambient group
coordinate. -/
private theorem fixed_constituent_transport_total_space_conj_embed_hall_kernel
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (g : fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I)
    (x : I) :
    g * fixed_constituent_transport_total_space_embed_hall_kernel
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) x * g⁻¹ =
      fixed_constituent_transport_total_space_embed_hall_kernel
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        ⟨g.1 * (x : G) * g.1⁻¹,
          (Subgroup.Normal.conj_mem (H := I) inferInstance (x : G) x.property g.1)⟩ := by
  let y : I :=
    ⟨g.1 * (x : G) * g.1⁻¹,
      (Subgroup.Normal.conj_mem (H := I) inferInstance (x : G) x.property g.1)⟩
  change g * fixed_constituent_transport_total_space_embed_hall_kernel
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) x * g⁻¹ =
      fixed_constituent_transport_total_space_embed_hall_kernel
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) y
  apply Sigma.ext
  · rfl
  · refine fixed_constituent_generated_cover_transport_fiber_heq_of_apply_eq I ρA_I rfl ?_
    intro z
    change
      (fixed_constituent_transport_fiber_comp
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_fiber_comp
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          g.2
          (fixed_constituent_transport_fiber_of_hall_kernel_element
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) x))
        (fixed_constituent_transport_fiber_inv
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) g.2)) z =
      (fixed_constituent_transport_fiber_of_hall_kernel_element
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) y) z
    unfold fixed_constituent_transport_fiber_comp
    rw [Representation.Equiv.trans_apply]
    rw [Representation.Equiv.trans_apply]
    unfold fixed_constituent_transport_fiber_inv
    unfold fixed_constituent_transport_fiber_of_hall_kernel_element
    simp only [Representation.Equiv.mk_apply, LinearEquiv.ofBijective_apply]
    change g.2 ((ρA_I x) (g.2.symm z)) = (ρA_I y) z
    have hy : (MulEquiv.symm (MulAut.conjNormal g.1)) y = x := by
      ext
      simp [y, mul_assoc]
    have happly : g.2 (g.2.symm z) = z := by
      exact Representation.Equiv.apply_symm_apply g.2 z
    have hraw := LinearMap.congr_fun (g.2.isIntertwining' y) (g.2.symm z)
    have h :
        g.2 ((ρA_I x) (g.2.symm z)) =
          (ρA_I y) (g.2 (g.2.symm z)) := by
      simpa [hy] using hraw
    rw [happly] at h
    exact h

/-- Helper for Theorem 17-17.6-1: Serre's embedded Hall-kernel subgroup `I₂` is normal in
the generated cover `G₂`, so quotienting `G₂` by `I₂` has the usual group structure. -/
instance fixed_constituent_generated_cover_hall_kernel_subgroup_normal
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
    (fixed_constituent_generated_cover_hall_kernel_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).Normal := by
  refine Subgroup.Normal.mk ?_
  intro n hn g
  rcases hn with ⟨x, rfl⟩
  let y : I :=
    ⟨g.1.1 * (x : G) * g.1.1⁻¹,
      (Subgroup.Normal.conj_mem (H := I) inferInstance (x : G) x.property g.1.1)⟩
  refine ⟨y, ?_⟩
  apply Subtype.ext
  symm
  change
    g.1 * fixed_constituent_transport_total_space_embed_hall_kernel
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) x * g.1⁻¹ =
    fixed_constituent_transport_total_space_embed_hall_kernel
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) y
  exact
    fixed_constituent_transport_total_space_conj_embed_hall_kernel
      (A := A) (G := G) (I := I) ρA_I g.1 x

/-- Helper for Theorem 17-17.6-1: after restricting Serre's total-space projection to `G₂`,
quotienting by `I` on the `G`-side yields the source map `G₂ → G ⧸ I` used before introducing
the kernel `N̄`. -/
noncomputable def fixed_constituent_generated_cover_proj_to_quotient
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
    fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift →*
      G ⧸ I :=
  (QuotientGroup.mk' I).comp
    ((fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype
        (fixed_constituent_generated_cover_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)))

/-- Helper for Theorem 17-17.6-1: the restricted projection `G₂ → G` is still surjective after
passing to `G ⧸ I`, so Serre's literal map `G₂ → G ⧸ I` already hits every quotient class. -/
theorem fixed_constituent_generated_cover_proj_to_quotient_surjective
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
    Function.Surjective
      (fixed_constituent_generated_cover_proj_to_quotient
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) := by
  intro q
  rcases QuotientGroup.mk'_surjective I q with ⟨s, rfl⟩
  obtain ⟨g, hg⟩ :=
    fixed_constituent_generated_cover_proj_surjective
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s
  refine ⟨g, ?_⟩
  change
    QuotientGroup.mk' I
        (((fixed_constituent_transport_total_space_proj_hom
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
          (Subgroup.subtype
            (fixed_constituent_generated_cover_subgroup
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift))) g) =
      QuotientGroup.mk' I s
  rw [hg]

/-- Helper for Theorem 17-17.6-1: the embedded Hall-kernel copy `I₂` lies in the kernel of the
literal quotient projection `G₂ → G ⧸ I`. This is the first concrete kernel containment in the
`G₂ / I₂ / N̄` package. -/
theorem fixed_constituent_generated_cover_hall_kernel_subgroup_le_ker_proj_to_quotient
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
    fixed_constituent_generated_cover_hall_kernel_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift ≤
      (fixed_constituent_generated_cover_proj_to_quotient
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker := by
  rintro y ⟨x, rfl⟩
  change QuotientGroup.mk' I (x : G) = 1
  exact (QuotientGroup.eq_one_iff (x : G)).2 x.2

/-- Helper for Theorem 17-17.6-1: Serre's literal quotient map `G₂ → G ⧸ I` descends through the
embedded Hall-kernel subgroup `I₂`, yielding the source-faithful map `pi₂ : G₂ ⧸ I₂ → G ⧸ I`
that defines the later kernel `N̄`. -/
noncomputable def generated_cover_proj_to_quotient_descends
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
    (fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift ⧸
      fixed_constituent_generated_cover_hall_kernel_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) →*
      G ⧸ I :=
  QuotientGroup.lift
    (fixed_constituent_generated_cover_hall_kernel_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
    (fixed_constituent_generated_cover_proj_to_quotient
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
    (fixed_constituent_generated_cover_hall_kernel_subgroup_le_ker_proj_to_quotient
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)

/-- Helper for Theorem 17-17.6-1: the descended quotient map `pi₂ : G₂ ⧸ I₂ → G ⧸ I` is
surjective, because the unreduced map `G₂ → G ⧸ I` was already surjective before quotienting by
`I₂`. -/
theorem generated_cover_proj_to_quotient_descends_surjective
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
    Function.Surjective
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) := by
  exact
    QuotientGroup.lift_surjective_of_surjective
      (fixed_constituent_generated_cover_hall_kernel_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
      (fixed_constituent_generated_cover_proj_to_quotient
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
      (fixed_constituent_generated_cover_proj_to_quotient_surjective
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
      (fixed_constituent_generated_cover_hall_kernel_subgroup_le_ker_proj_to_quotient
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)

/-- Helper for Theorem 17-17.6-1: once the first quotient map `pi₂ : G₂ ⧸ I₂ → G ⧸ I` is fixed,
the quotient by its kernel is formally identified with `G ⧸ I`. This closes the purely
quotient-theoretic half of Serre's `G₂ / I₂ / N̄` package before any kernel normalization. -/
noncomputable def generated_cover_kernel_quotient_equiv
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
    (((fixed_constituent_generated_cover_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift ⧸
        fixed_constituent_generated_cover_hall_kernel_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) ⧸
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) ≃*
      (G ⧸ I)) :=
  QuotientGroup.quotientKerEquivOfSurjective
    (generated_cover_proj_to_quotient_descends
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
    (generated_cover_proj_to_quotient_descends_surjective
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)

/-- Helper for Theorem 17-17.6-1: every element of `N̄ = ker(pi₂)` admits a representative in
`G₂` whose projection to `G` lies in `I`, and dividing by that embedded Hall-kernel point
produces a representative lying over `1`. This isolates the source-faithful normalization step
before defining any scalar-class invariant on `N̄`. -/
theorem generated_cover_kernel_normalized_representative_exists
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
    (g :
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
    (hg :
      QuotientGroup.mk'
          (fixed_constituent_generated_cover_hall_kernel_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
          g =
        q.1) :
    ∃ x : I,
      ((fixed_constituent_transport_total_space_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype
          (fixed_constituent_generated_cover_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift))) g =
        x ∧
      ((fixed_constituent_transport_total_space_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype
          (fixed_constituent_generated_cover_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)))
          (g *
            (fixed_constituent_generated_cover_embed_hall_kernel
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x)⁻¹) =
        1 ∧
      QuotientGroup.mk'
          (fixed_constituent_generated_cover_hall_kernel_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
          (g *
            (fixed_constituent_generated_cover_embed_hall_kernel
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x)⁻¹) =
        q.1 := by
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
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype G2)
  let f : G2 →* G ⧸ I :=
    fixed_constituent_generated_cover_proj_to_quotient
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi2 : G2 ⧸ I2 →* G ⧸ I :=
    generated_cover_proj_to_quotient_descends
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  have hmk_ker : pi2 (QuotientGroup.mk' I2 g) = 1 := by
    rw [hg]
    exact q.2
  have hfg : f g = 1 := by
    simpa [pi2, generated_cover_proj_to_quotient_descends, f, I2] using hmk_ker
  have hproj_mem : pi g ∈ I := by
    have hmk_one : QuotientGroup.mk' I (pi g) = 1 := by
      simpa [f, fixed_constituent_generated_cover_proj_to_quotient, pi, G2] using hfg
    exact (QuotientGroup.eq_one_iff (pi g)).1 hmk_one
  let x : I := ⟨pi g, hproj_mem⟩
  refine ⟨x, ?_, ?_, ?_⟩
  · rfl
  · have hproj_embed :
        pi
            (fixed_constituent_generated_cover_embed_hall_kernel
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x) =
          x := by
      rfl
    calc
      pi
          (g *
            (fixed_constituent_generated_cover_embed_hall_kernel
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x)⁻¹) =
          pi g *
            (pi
              (fixed_constituent_generated_cover_embed_hall_kernel
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x))⁻¹ := by
            simp
      _ = 1 := by
            rw [hproj_embed]
            simp [x]
  · have hx_mem : fixed_constituent_generated_cover_embed_hall_kernel
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x ∈ I2 := by
      exact ⟨x, rfl⟩
    have hx_mk_one :
        QuotientGroup.mk' I2
            (fixed_constituent_generated_cover_embed_hall_kernel
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x) =
          1 := by
      exact (QuotientGroup.eq_one_iff _).2 hx_mem
    calc
      QuotientGroup.mk' I2
          (g *
            (fixed_constituent_generated_cover_embed_hall_kernel
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x)⁻¹) =
          QuotientGroup.mk' I2 g *
            (QuotientGroup.mk' I2
              (fixed_constituent_generated_cover_embed_hall_kernel
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x))⁻¹ := by
            simp
      _ = q.1 := by
            simpa [hx_mk_one] using hg

/-- Helper for Theorem 17-17.6-1: an element of the actual projection kernel in `G₂` gives an
element of Serre's quotient kernel `N̄` after applying the quotient map `G₂ → G₂ / I₂`. -/
theorem generated_cover_kernel_mk_mem_nbar
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
    let pi : G2 →* G :=
      (fixed_constituent_transport_total_space_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype G2)
    ∀ z : pi.ker, QuotientGroup.mk' I2 z.1 ∈ pi2.ker := by
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
  let pi : G2 →* G :=
    (fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype G2)
  change ∀ z : pi.ker, QuotientGroup.mk' I2 z.1 ∈ pi2.ker
  intro z
  let f : G2 →* G ⧸ I :=
    fixed_constituent_generated_cover_proj_to_quotient
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  have hfz : f z.1 = 1 := by
    have hmk_one : QuotientGroup.mk' I (pi z.1) = 1 := by
      rw [z.2]
      exact (QuotientGroup.eq_one_iff (1 : G)).2 I.one_mem
    simpa [f, fixed_constituent_generated_cover_proj_to_quotient, pi, G2] using hmk_one
  change pi2 (QuotientGroup.mk' I2 z.1) = 1
  simpa [pi2, generated_cover_proj_to_quotient_descends, f, I2] using hfz

/-- Helper for Theorem 17-17.6-1: the quotient map `G₂ → G₂ / I₂` restricts to a homomorphism
from the actual projection kernel `ker(pi)` to Serre's quotient kernel `N̄`. -/
noncomputable def generated_cover_kernel_to_nbar_hom
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
    let pi : G2 →* G :=
      (fixed_constituent_transport_total_space_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype G2)
    pi.ker →* Nbar :=
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
  let pi : G2 →* G :=
    (fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype G2)
  MonoidHom.codRestrict
    ((QuotientGroup.mk' I2).comp (Subgroup.subtype pi.ker))
    pi2.ker
    (generated_cover_kernel_mk_mem_nbar
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)

/-- Helper for Theorem 17-17.6-1: the restricted quotient map from `ker(pi)` to `N̄` is
bijective; injectivity uses the Hall-kernel projection formula, and surjectivity is exactly the
normalized representative construction. -/
theorem generated_cover_kernel_to_nbar_bijective
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
    Function.Bijective
      (generated_cover_kernel_to_nbar_hom
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
  let pi : G2 →* G :=
    (fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype G2)
  let toNbar :=
    generated_cover_kernel_to_nbar_hom
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  constructor
  · intro z₁ z₂ h
    apply Subtype.ext
    have hmk :
        QuotientGroup.mk' I2 z₁.1 = QuotientGroup.mk' I2 z₂.1 := by
      exact congrArg Subtype.val h
    have hdiff_mem : z₁.1⁻¹ * z₂.1 ∈ I2 := by
      exact (QuotientGroup.eq).1 (by simpa [QuotientGroup.mk'_apply] using hmk)
    rcases hdiff_mem with ⟨x, hx⟩
    have hproj_diff : pi (z₁.1⁻¹ * z₂.1) = 1 := by
      have hz₁ : pi z₁.1 = 1 := z₁.2
      have hz₂ : pi z₂.1 = 1 := z₂.2
      simp [hz₁, hz₂]
    have hproj_embed :
        pi
            (fixed_constituent_generated_cover_embed_hall_kernel
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x) =
          x := by
      rfl
    have hx_val : (x : G) = 1 := by
      rw [hx] at hproj_embed
      rw [hproj_diff] at hproj_embed
      exact hproj_embed.symm
    have hx_one : x = 1 := Subtype.ext hx_val
    have hdiff_one : z₁.1⁻¹ * z₂.1 = 1 := by
      rw [← hx, hx_one]
      simp
    exact (inv_mul_eq_one).1 hdiff_one
  · intro q
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective I2 q.1
    obtain ⟨x, _hproj, hnorm, hmk⟩ :=
      generated_cover_kernel_normalized_representative_exists
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q g hg
    let z : pi.ker :=
      ⟨g *
          (fixed_constituent_generated_cover_embed_hall_kernel
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x)⁻¹,
        hnorm⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    change QuotientGroup.mk' I2 z.1 = q.1
    exact hmk

/-- Helper for Theorem 17-17.6-1: the actual kernel of `pi : G₂ → G` is identified with
Serre's quotient kernel `N̄ = ker(pi₂)` by quotienting by `I₂` and normalizing representatives
back over `1 ∈ G`. -/
noncomputable def generated_cover_kernel_equiv_nbar
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
    let pi : G2 →* G :=
      (fixed_constituent_transport_total_space_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype G2)
    pi.ker ≃* Nbar :=
  MulEquiv.ofBijective
    (generated_cover_kernel_to_nbar_hom
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
    (generated_cover_kernel_to_nbar_bijective
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)

/-- Helper for Theorem 17-17.6-1: once the candidate determinant subgroup is placed inside the
bounded roots-of-unity owner `D̄`, the remaining work is the literal Serre package
`G₂`, `I₂`, `N̄`, `τ`, and tensor descent. This keeps the final blocker separate from the already
formalized closure step. -/
theorem generated_cover_kernel_has_normalized_representative
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
    ∀ g :
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift,
      QuotientGroup.mk'
          (fixed_constituent_generated_cover_hall_kernel_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
          g =
        q.1 →
        ∃ x : I,
          ((fixed_constituent_transport_total_space_proj_hom
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
            (Subgroup.subtype
              (fixed_constituent_generated_cover_subgroup
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift))) g =
            x ∧
          ((fixed_constituent_transport_total_space_proj_hom
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
            (Subgroup.subtype
              (fixed_constituent_generated_cover_subgroup
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)))
              (g *
                (fixed_constituent_generated_cover_embed_hall_kernel
                  (p := p) (A := A) (G := G) (V := V)
                  hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x)⁻¹) =
            1 ∧
          QuotientGroup.mk'
              (fixed_constituent_generated_cover_hall_kernel_subgroup
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
              (g *
                (fixed_constituent_generated_cover_embed_hall_kernel
                  (p := p) (A := A) (G := G) (V := V)
                  hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x)⁻¹) =
            q.1 := by
  intro g hg
  -- Delegate the normalization to the explicit representative-level lemma above.
  exact
    generated_cover_kernel_normalized_representative_exists
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q g hg

end

end Representation
