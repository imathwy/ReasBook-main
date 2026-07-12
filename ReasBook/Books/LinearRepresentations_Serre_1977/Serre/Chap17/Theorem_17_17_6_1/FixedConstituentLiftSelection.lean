import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_6_1.HallKernelInductionBranch

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

/-- Helper for Theorem 17-17.6-1: since the Hall kernel `I` has order prime to `p`, the chosen
constituent `S̄` already admits an `A[I]`-lift. This supplies the lifted constituent that Serre
uses before constructing the finite projective cover `G₂`. -/
theorem exists_residueFieldLift_of_fixed_constituent
    (hp : Nat.Prime p)
    (I : Subgroup G)
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    [Sbar.toRepresentation.IsIrreducible] :
    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A I P)
      (red : P →ₗ[A] Sbar.toSubmodule),
        IsResidueFieldLift Sbar.toRepresentation ρA red := by
  have hIndvd : ¬ p ∣ Nat.card I := hp.coprime_iff_not_dvd.mp hIcop
  -- This is the prime-to-`p` lifting step for the fixed constituent itself.
  exact
    exists_residueFieldLift_of_non_dvd_card_witness
      (A := A) (p := p) (G' := I) (V' := Sbar.toSubmodule) hIndvd Sbar.toRepresentation

/-- Helper for Theorem 17-17.6-1: precomposing an irreducible representation with a group
equivalence preserves irreducibility. -/
theorem isIrreducible_comp_of_mulEquiv_c17
    {K : Type*} [Field K]
    {G₁ : Type*} [Group G₁] {G₂ : Type*} [Group G₂]
    {W : Type*} [AddCommGroup W] [Module K W]
    (e : G₁ ≃* G₂) (σ : Representation K G₂ W) [σ.IsIrreducible] :
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
  intro U hU
  let U' : Subrepresentation σ :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := by
        intro g x hx
        simpa using U.apply_mem_toSubmodule (e.symm g) hx }
  have hU'_ne_bot : U' ≠ ⊥ := by
    intro hU'
    apply hU
    apply Subrepresentation.toSubmodule_injective
    simpa [U'] using congrArg Subrepresentation.toSubmodule hU'
  have hU'_top : U' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U').resolve_left hU'_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [U'] using congrArg Subrepresentation.toSubmodule hU'_top

/-- Helper for Theorem 17-17.6-1: pulling back an irreducible representation along a surjective
group homomorphism preserves irreducibility. This isolates the formal `ρ.comp π` step that will
be reused when the finite cover `G₂` is compared back to `G`. -/
theorem isIrreducible_comp_of_surjective
    {K : Type*} [Field K]
    {G₁ : Type*} [Group G₁] {G₂ : Type*} [Group G₂]
    {W : Type*} [AddCommGroup W] [Module K W]
    (π : G₁ →* G₂) (hπ : Function.Surjective π)
    (σ : Representation K G₂ W) [σ.IsIrreducible] :
    Representation.IsIrreducible (σ.comp π) := by
  classical
  letI : Nontrivial (Subrepresentation (σ.comp π)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation σ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using congrArg Subrepresentation.toSubmodule h
    exact IsSimpleOrder.bot_ne_top h'
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro U hU
  let U' : Subrepresentation σ :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := by
        intro g x hx
        obtain ⟨g', rfl⟩ := hπ g
        simpa using U.apply_mem_toSubmodule g' hx }
  have hU'_ne_bot : U' ≠ ⊥ := by
    intro hU'
    apply hU
    apply Subrepresentation.toSubmodule_injective
    simpa [U'] using congrArg Subrepresentation.toSubmodule hU'
  have hU'_top : U' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U').resolve_left hU'_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [U'] using congrArg Subrepresentation.toSubmodule hU'_top

/-- Helper for Theorem 17-17.6-1: if the Hall-kernel restriction is isotypic of type `S̄`, then
every conjugate transport of `S̄` is equivariantly isomorphic to `S̄` itself. This is Serre's
`U_s ≠ ∅` checkpoint before the finite projective extension is built. -/
theorem transported_constituent_equiv_of_isotypic_component_top
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      @isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module = ⊤) :
    ∀ s : G,
      Nonempty (Sbar.toRepresentation.Equiv (transportedSubrepresentation ρ Sbar s).toRepresentation) := by
  let ρI : Representation k I V := ρ.comp I.subtype
  letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
  intro s
  let T : Subrepresentation ρI := transportedSubrepresentation ρ Sbar s
  let ρT : Representation k I T.toSubmodule := T.toRepresentation
  letI : Module (MonoidAlgebra k I) ρT.asModule := ρT.instModuleMonoidAlgebraAsModule
  letI : Module (MonoidAlgebra k I) T.toRepresentation.asModule :=
    T.toRepresentation.instModuleMonoidAlgebraAsModule
  letI : IsSemisimpleModule (MonoidAlgebra k I) V :=
    isSemisimpleModule_restrict_of_coprime_card hp I hIcop ρ
  letI hSbarSimple :
      @IsSimpleModule (MonoidAlgebra k I) inferInstance Sbar.asSubmodule inferInstance
        Sbar.asSubmodule.module :=
    chosen_constituent_owner_simple (I := I) (ρ := ρ) (Sbar := Sbar) hSbar_irred
  have hType :
      @IsIsotypicOfType (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module := by
    -- The hypothesis says the entire restricted module lies in the `S̄`-isotypic block.
    exact
      (@isotypicComponent_eq_top_iff (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module
        hSbarSimple inferInstance).mp hSbar_top
  have hT_irred : T.toRepresentation.IsIrreducible := by
    letI : Sbar.toRepresentation.IsIrreducible := hSbar_irred
    letI :
        Representation.IsIrreducible
          (Sbar.toRepresentation.comp (MulAut.conjNormal s⁻¹).toMonoidHom) := by
      exact
        (conjugatedSubrepresentationOrderIso_local_c17 (σ := Sbar.toRepresentation) s).isSimpleOrder_iff.mpr
          inferInstance
    -- Transport identifies the conjugated constituent with the literal subrepresentation `sS̄`.
    exact
      isIrreducible_of_equiv_local_c17
        (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s)
  have hT_simple :
      @IsSimpleModule (MonoidAlgebra k I) inferInstance T.asSubmodule T.asSubmodule.addCommGroup
        T.asSubmodule.module := by
    -- Convert irreducibility of the transported intrinsic constituent back to the owner module.
    exact
      @IsSimpleModule.congr (MonoidAlgebra k I) inferInstance T.asSubmodule
        T.asSubmodule.addCommGroup T.asSubmodule.module
        ρT.asModule ρT.instAddCommGroupAsModule ρT.instModuleMonoidAlgebraAsModule
        (subrepresentation_owner_intrinsic_linearEquiv_local_c17 (ρ := ρI) T).symm
        ((Representation.irreducible_iff_isSimpleModule_asModule ρT).mp hT_irred)
  have hOwnerEquiv : Nonempty (T.asSubmodule ≃ₗ[MonoidAlgebra k I] Sbar.asSubmodule) := by
    exact @hType T.asSubmodule hT_simple
  -- Upgrade the owner-module comparison back to a representation equivalence on the bundled
  -- subrepresentations.
  exact
    ⟨(subrepresentation_equiv_of_asSubmoduleLinearEquiv_local_c17 T Sbar hOwnerEquiv.some).symm⟩

/-- Helper for Theorem 17-17.6-1: once a quotient already has height `h`, Serre's bookkeeping can
always pad it to height `h + 1` by inserting the trivial normal subgroup. -/
lemma isPSolvableOfHeight_succ_of_isPSolvableOfHeight
    {G' : Type*} [Group G'] [Finite G']
    (hG' : IsPSolvableOfHeight p h G') :
    IsPSolvableOfHeight p (Nat.succ h) G' := by
  -- Insert the trivial subgroup as a vacuous first step in the height tower.
  have hquotBot : IsPSolvableOfHeight p h (G' ⧸ (⊥ : Subgroup G')) := by
    exact IsPSolvableOfHeight.of_equiv (QuotientGroup.quotientBot (G := G')).symm hG'
  exact
    IsPSolvableOfHeight.succ_iff.mpr
      ⟨⊥, inferInstance, Or.inl (by simpa using Nat.coprime_one_right p), hquotBot⟩

/-- Helper for Theorem 17-17.6-1: Serre's transported constituent lift can be compared to the
conjugated fixed lift by Chapter `15` uniqueness, producing an actual `A`-linear automorphism on
the chosen lift carrier `P_S`. -/
theorem conjugated_fixed_constituent_lift
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S) :
    ∀ s : G,
      IsResidueFieldLift
        (Sbar.toRepresentation.comp (MulAut.conjNormal s⁻¹).toMonoidHom)
        (ρA_I.comp (MulAut.conjNormal s⁻¹).toMonoidHom)
        red_S := by
  intro s
  let c_s : I →* I := (MulAut.conjNormal s⁻¹).toMonoidHom
  let ρS_conj : Representation k I Sbar.toSubmodule := Sbar.toRepresentation.comp c_s
  let ρA_conj : Representation A I P_S := ρA_I.comp c_s
  -- Restrict Serre's fixed lift along the conjugation hom before transporting the target.
  change IsResidueFieldLift ρS_conj ρA_conj red_S
  simpa [c_s, ρS_conj, ρA_conj] using
    (Representation.isResidueFieldLift_comp hLiftSbar c_s)

/-- Helper for Theorem 17-17.6-1: the conjugated fixed lift becomes a lift of the literal
transported constituent once we retarget along the canonical transport equivalence. -/
theorem transported_fixed_constituent_lift_of_conjugation
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S) :
    ∀ s : G,
      IsResidueFieldLift
        (transportedSubrepresentation ρ Sbar s).toRepresentation
        (ρA_I.comp (MulAut.conjNormal s⁻¹).toMonoidHom)
        (((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s).toLinearMap.restrictScalars A).comp
          red_S) := by
  intro s
  -- First restrict the fixed lift by conjugation, then transport the target to the literal `sS̄`.
  exact
    residueFieldLift_of_equiv_target_local
      (A := A)
      (hLift :=
        conjugated_fixed_constituent_lift
          (A := A) (G := G) (V := V) I ρ Sbar ρA_I red_S hLiftSbar s)
      (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s)

/-- Helper for Theorem 17-17.6-1: Serre's transported constituent lift can be compared to the
conjugated fixed lift by Chapter `15` uniqueness, producing an actual `A`-linear automorphism on
the chosen lift carrier `P_S`. -/
theorem exists_fixed_constituent_transport_aut_of_lift
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
    ∀ s : G,
      ∃ u : Representation.Equiv
        (ρA_I.comp (MulAut.conjNormal s⁻¹).toMonoidHom) ρA_I,
        (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S).comp u.toLinearMap =
          ((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s).toLinearMap.restrictScalars A).comp
            red_S := by
  have hI_ndvd : ¬ p ∣ Nat.card I := hp.coprime_iff_not_dvd.mp hIcop
  intro s
  let T_s : Subrepresentation (ρ.comp I.subtype) := transportedSubrepresentation ρ Sbar s
  let ρT : Representation k I T_s.toSubmodule := T_s.toRepresentation
  let ρA_conj : Representation A I P_S := ρA_I.comp (MulAut.conjNormal s⁻¹).toMonoidHom
  let ρA_fixed : Representation A I P_S := ρA_I
  let red_conj : P_S →ₗ[A] T_s.toSubmodule :=
    ((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s).toLinearMap.restrictScalars A).comp
      red_S
  let red_transport : P_S →ₗ[A] T_s.toSubmodule :=
    (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)
  -- Build the first lift of the literal transported constituent by conjugating the fixed lift.
  have hConjLift_source :
      IsResidueFieldLift
        (transportedSubrepresentation ρ Sbar s).toRepresentation
        (ρA_I.comp (MulAut.conjNormal s⁻¹).toMonoidHom)
        (((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s).toLinearMap.restrictScalars A).comp
          red_S) :=
    transported_fixed_constituent_lift_of_conjugation
      (A := A) (G := G) (V := V) I ρ Sbar ρA_I red_S hLiftSbar s
  have hConjLift :
      IsResidueFieldLift
        ρT
        ρA_conj
        red_conj := by
    simpa [T_s, ρT, ρA_conj, red_conj] using hConjLift_source
  have hLiteralTransport :
      IsResidueFieldLift ρT ρA_fixed red_transport := by
    simpa [T_s, ρT, ρA_fixed, red_transport] using hTransportLift s
  have hSmallI : Small.{u} I := by
    obtain ⟨n, ⟨efin⟩⟩ := Finite.exists_equiv_fin I
    exact Small.mk' (efin.trans Equiv.ulift.symm)
  letI : Small.{u} I := hSmallI
  let eShrink : Shrink.{u} I ≃* I := Shrink.mulEquiv
  have hShrink_ndvd : ¬ p ∣ Nat.card (Shrink.{u} I) := by
    simpa [Nat.card_congr eShrink.toEquiv] using hI_ndvd
  have hConjLift_shrink :
      IsResidueFieldLift
        (ρT.comp eShrink.toMonoidHom)
        (ρA_conj.comp eShrink.toMonoidHom)
        red_conj := by
    exact Representation.isResidueFieldLift_comp hConjLift eShrink.toMonoidHom
  have hLiteralTransport_shrink :
      IsResidueFieldLift
        (ρT.comp eShrink.toMonoidHom)
        (ρA_fixed.comp eShrink.toMonoidHom)
        red_transport := by
    exact Representation.isResidueFieldLift_comp hLiteralTransport eShrink.toMonoidHom
  -- Chapter `15` uniqueness now compares this explicit lift with the literal transported lift.
  obtain ⟨uShrink, hu⟩ :=
    residueFieldLift_unique_up_to_equivariant_iso
      (A := A) (p := p) (G := Shrink.{u} I) (V := T_s.toSubmodule)
      hShrink_ndvd
      (ρT.comp eShrink.toMonoidHom)
      (ρA_conj.comp eShrink.toMonoidHom)
      red_conj
      hConjLift_shrink
      (ρA_fixed.comp eShrink.toMonoidHom)
      red_transport
      hLiteralTransport_shrink
  let u : Representation.Equiv ρA_conj ρA_fixed :=
    Representation.Equiv.mk uShrink.toLinearEquiv fun g ↦ by
      -- The shrink comparison is equivariant for every `g' : Shrink I`, hence also for the
      -- original subgroup element `g` after rewriting along `eShrink`.
      simpa [ρA_conj, ρA_fixed] using uShrink.isIntertwining' (eShrink.symm g)
  -- Re-express the uniqueness conclusion in the original theorem statement.
  refine ⟨u, ?_⟩
  change red_transport.comp uShrink.toLinearMap = red_conj
  exact hu

/-- Helper for Theorem 17-17.6-1: choose the source-faithful lifted conjugation automorphism on
the fixed carrier `P_S`; later stages use this concrete carrier automorphism to define Serre's
finite projective cover. -/
noncomputable def fixed_constituent_transport_aut_of_lift
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
    Representation.Equiv
      (ρA_I.comp (MulAut.conjNormal s⁻¹).toMonoidHom) ρA_I :=
  Classical.choose <|
    exists_fixed_constituent_transport_aut_of_lift
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s

/-- Helper for Theorem 17-17.6-1: Serre's transport fiber `U_s` on the fixed lifted constituent
carrier is the type of `A[I]`-equivariant identifications between the conjugated fixed lift and
the fixed lift itself. Naming this owner restores the source proof's literal `U_s` language before
the later scalar-coset and determinant analysis. -/
abbrev fixed_constituent_transport_fiber
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (s : G) : Type (max u v x) :=
  Representation.Equiv
    (ρA_I.comp (MulAut.conjNormal s⁻¹).toMonoidHom) ρA_I

/-- Helper for Theorem 17-17.6-1: the fixed transport fiber `U_s` is nonempty. This is exactly
Serre's source step asserting that every conjugate of the fixed constituent lift is identified
with the original lift on the same carrier. -/
theorem fixed_constituent_transport_fiber_nonempty
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
    Nonempty
      (fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s) := by
  -- Reuse the chosen transport automorphism as Serre's witness that the fiber `U_s` is inhabited.
  exact
    ⟨fixed_constituent_transport_aut_of_lift
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s⟩

/-- Helper for Theorem 17-17.6-1: the chosen lifted conjugation automorphism reduces to the
comparison between the transported constituent `sS̄` and the fixed constituent `S̄`. -/
theorem fixed_constituent_transport_aut_of_lift_reduction
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
    (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S).comp
        (fixed_constituent_transport_aut_of_lift
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s).toLinearMap =
      ((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s).toLinearMap.restrictScalars A).comp
        red_S := by
  -- Unpack the chosen uniqueness witness once; this is the reduction identity used in the
  -- later determinant-normalized cover construction.
  exact
    Classical.choose_spec <|
      exists_fixed_constituent_transport_aut_of_lift
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s

/-- Helper for Theorem 17-17.6-1: the chosen transport family on the fixed lift already satisfies
Serre's projective cocycle relation up to a literal self-equivalence of `ρA_I`. This isolates the
remaining finite-cover frontier to classifying these self-equivalences and controlling their
determinants. -/
noncomputable def fixed_constituent_transport_aut_discrepancy
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
    (s t : G) :
    Representation.Equiv ρA_I ρA_I := by
  let u_s :=
    fixed_constituent_transport_aut_of_lift
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s
  let u_t :=
    fixed_constituent_transport_aut_of_lift
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift t
  let u_st :=
    fixed_constituent_transport_aut_of_lift
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (s * t)
  let u_t_over_s :
      Representation.Equiv
        (ρA_I.comp (MulAut.conjNormal (s * t)⁻¹).toMonoidHom)
        (ρA_I.comp (MulAut.conjNormal s⁻¹).toMonoidHom) := by
    -- The same carrier automorphism `u_t` still intertwines after conjugating both source actions
    -- by `s`; this is the literal projective-cocycle step before Serre's scalar reduction.
    refine Representation.Equiv.mk u_t.toLinearEquiv ?_
    intro a
    ext x
    -- Normalize the double conjugation first: `t⁻¹ (s⁻¹ a s) t = (s * t)⁻¹ a (s * t)`.
    simpa [MulAut.conjNormal_apply, mul_assoc] using
      LinearMap.congr_fun (u_t.isIntertwining' ((MulAut.conjNormal s⁻¹) a)) x
  let composed :
      Representation.Equiv
        (ρA_I.comp (MulAut.conjNormal (s * t)⁻¹).toMonoidHom) ρA_I :=
    u_t_over_s.trans u_s
  -- Compare the two literal lifts of the `(s * t)`-transport: the composed one and the chosen one.
  exact composed.symm.trans u_st

end

end Representation
