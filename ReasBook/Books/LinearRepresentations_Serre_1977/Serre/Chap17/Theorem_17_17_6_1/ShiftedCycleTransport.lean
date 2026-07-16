import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_6_1.KernelReductionComparison

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

/-- Helper for Theorem 17-17.6-1: once the reduced-side section has been normalized so that the
chosen comparison at `1` is canonical, Serre's literal `n`-step section cycle reduces to the
canonical ambient transport over `s ^ n`. The normalization hypothesis is necessary already at
`n = 0`, where the empty cycle forces the endpoint comparison at `1` to be the canonical one. -/
theorem fixed_constituent_section_cycle_fiber_succ_toLinearMap
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
    (s : G) (n : ℕ) :
    let cycle_n :=
      fixed_constituent_section_cycle_fiber
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
    let sec :=
      fixed_constituent_transport_total_space_section
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    (fixed_constituent_section_cycle_fiber
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s (n + 1)).toLinearMap =
      cycle_n.toLinearMap.comp (sec s).2.toLinearMap := by
  ext z
  simp [fixed_constituent_section_cycle_fiber, fixed_constituent_transport_fiber_comp]
  rfl

/-- Helper for Theorem 17-17.6-1: once the reduced-side section has been normalized so that the
chosen comparison at `1` is canonical, Serre's literal `n`-step section cycle reduces to the
canonical ambient transport over `s ^ n`. The normalization hypothesis is necessary already at
`n = 0`, where the empty cycle forces the endpoint comparison at `1` to be the canonical one. -/
theorem fixed_constituent_section_cycle_source_lift
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
    (s : G) (n : ℕ) :
    let cycle_n :=
      fixed_constituent_section_cycle_fiber
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
    IsResidueFieldLift
      (transportedSubrepresentation ρ Sbar (s ^ n)).toRepresentation
      (ρA_I.comp (MulAut.conjNormal (s ^ n)⁻¹).toMonoidHom)
      ((((hTransport (s ^ n)).some.toLinearMap.restrictScalars A).comp red_S).comp
        cycle_n.toLinearMap) := by
  let cycle_n :=
    fixed_constituent_section_cycle_fiber
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
  -- The cycle already is the required source equivalence from the conjugated lift to the fixed
  -- lift, so the shifted reduction map is obtained by the general source-transport lemma.
  simpa [cycle_n] using
    residueFieldLift_of_equiv_source_local
      (A := A)
      (ρ := (transportedSubrepresentation ρ Sbar (s ^ n)).toRepresentation)
      (ρA := ρA_I)
      (ρA' := ρA_I.comp (MulAut.conjNormal (s ^ n)⁻¹).toMonoidHom)
      (red := (((hTransport (s ^ n)).some.toLinearMap.restrictScalars A).comp red_S))
      (hLift := hTransportLift (s ^ n))
      cycle_n

/-- Helper for Theorem 17-17.6-1: after transporting the fixed constituent around the `n`-cycle,
the same reduced transport family reindexes along right multiplication by `s ^ n`, and the cycle
source equivalence transports the fixed lift to that shifted family. -/
theorem shifted_cycle_transport_family
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
    (s t : G) (n : ℕ) :
    let cycle_n :=
      fixed_constituent_section_cycle_fiber
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
    let Tn := transportedSubrepresentation ρ Sbar (s ^ n)
    ∃ e : Tn.toRepresentation.Equiv (transportedSubrepresentation ρ Tn t).toRepresentation,
      IsResidueFieldLift
        (transportedSubrepresentation ρ Tn t).toRepresentation
        (ρA_I.comp (MulAut.conjNormal (s ^ n)⁻¹).toMonoidHom)
        (((e.toLinearMap.restrictScalars A).comp
            ((((hTransport (s ^ n)).some.toLinearMap.restrictScalars A).comp red_S).comp
              cycle_n.toLinearMap))) := by
  let cycle_n :=
    fixed_constituent_section_cycle_fiber
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
  let Tn := transportedSubrepresentation ρ Sbar (s ^ n)
  have hmul :
      transportedSubrepresentation ρ Tn t =
        transportedSubrepresentation ρ Sbar (t * s ^ n) := by
    simpa [Tn] using
      transportedSubrepresentation_mul
        (I := I) (ρ := ρ) (Sbar := Sbar) t (s ^ n)
  let eBase :
      Tn.toRepresentation.Equiv
        (transportedSubrepresentation ρ Sbar (t * s ^ n)).toRepresentation :=
    (hTransport (s ^ n)).some.symm.trans (hTransport (t * s ^ n)).some
  let eCast :
      (transportedSubrepresentation ρ Sbar (t * s ^ n)).toRepresentation.Equiv
        (transportedSubrepresentation ρ Tn t).toRepresentation := by
    refine
      Representation.Equiv.mk
        (LinearEquiv.ofEq _ _ (congrArg Subrepresentation.toSubmodule hmul.symm)) ?_
    intro a
    ext x
    rfl
  let e := eBase.trans eCast
  have hsource :
      IsResidueFieldLift
        (transportedSubrepresentation ρ Sbar (t * s ^ n)).toRepresentation
        (ρA_I.comp (MulAut.conjNormal (s ^ n)⁻¹).toMonoidHom)
        ((((hTransport (t * s ^ n)).some.toLinearMap.restrictScalars A).comp red_S).comp
          cycle_n.toLinearMap) := by
    simpa [cycle_n, LinearMap.comp_assoc] using
      residueFieldLift_of_equiv_source_local
        (A := A)
        (ρ := (transportedSubrepresentation ρ Sbar (t * s ^ n)).toRepresentation)
        (ρA := ρA_I)
        (ρA' := ρA_I.comp (MulAut.conjNormal (s ^ n)⁻¹).toMonoidHom)
        (red := (((hTransport (t * s ^ n)).some.toLinearMap.restrictScalars A).comp red_S))
        (hLift := hTransportLift (t * s ^ n))
        cycle_n
  refine ⟨e, ?_⟩
  have htarget :=
    residueFieldLift_of_equiv_target_local
      (A := A) (G := I)
      (hLift := hsource)
      eCast
  have hred :
      (e.toLinearMap.restrictScalars A).comp
          ((((hTransport (s ^ n)).some.toLinearMap.restrictScalars A).comp red_S).comp
            cycle_n.toLinearMap) =
        (eCast.toLinearMap.restrictScalars A).comp
          ((((hTransport (t * s ^ n)).some.toLinearMap.restrictScalars A).comp red_S).comp
            cycle_n.toLinearMap) := by
    have hcancel :
        ((hTransport (s ^ n)).some.symm.toLinearMap.restrictScalars A).comp
            ((hTransport (s ^ n)).some.toLinearMap.restrictScalars A) =
          LinearMap.id := by
      ext x
      simpa using Representation.Equiv.symm_apply_apply (hTransport (s ^ n)).some x
    have hinner :
        ((hTransport (s ^ n)).some.symm.toLinearMap.restrictScalars A).comp
            (((hTransport (s ^ n)).some.toLinearMap.restrictScalars A).comp
              (red_S.comp cycle_n.toLinearMap)) =
          red_S.comp cycle_n.toLinearMap := by
      rw [← LinearMap.comp_assoc
        (red_S.comp cycle_n.toLinearMap)
        ((hTransport (s ^ n)).some.toLinearMap.restrictScalars A)
        ((hTransport (s ^ n)).some.symm.toLinearMap.restrictScalars A), hcancel]
      simp
    simpa [e, eBase, LinearMap.comp_assoc] using
      congrArg
        (fun L ↦
          (eCast.toLinearMap.restrictScalars A).comp
            (((hTransport (t * s ^ n)).some.toLinearMap.restrictScalars A).comp L))
        hinner
  rw [hred]
  exact htarget

/-- Helper for Theorem 17-17.6-1: the chosen section element `(sec s).2` can be re-read over the
shifted cycle source as a map from the `(s ^ (n + 1))`-twisted lift to the `(s ^ n)`-twisted
lift. This isolates the source-twist reindexing that remains before the endpoint comparison. -/
noncomputable def fixed_constituent_section_step_over_shifted_cycle_source
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
    (s : G) (n : ℕ) :
    Representation.Equiv
      (ρA_I.comp (MulAut.conjNormal (s ^ (n + 1))⁻¹).toMonoidHom)
      (ρA_I.comp (MulAut.conjNormal (s ^ n)⁻¹).toMonoidHom) := by
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  refine Representation.Equiv.mk (sec s).2.toLinearEquiv ?_
  intro a
  ext x
  -- Route correction: the same linear operator `(sec s).2` is reused, but now the source action
  -- is first reindexed by `(s ^ n)`. The only content is the conjugation identity
  -- `s⁻¹ * (s ^ n)⁻¹ * a * (s ^ n) * s = (s ^ (n + 1))⁻¹ * a * (s ^ (n + 1))`.
  simpa [sec, pow_succ, MulAut.conjNormal_apply, mul_assoc] using
    LinearMap.congr_fun ((sec s).2.isIntertwining' ((MulAut.conjNormal (s ^ n)⁻¹) a)) x

/-- Helper for Theorem 17-17.6-1: on the common carrier `P_S`, the shifted source-step map is
exactly the consecutive-cycle comparison from the `(n + 1)`-cycle back to the `n`-cycle. This is
the source-faithful object Serre controls, so later proofs can avoid introducing a fresh shifted
transport witness. -/
theorem fixed_constituent_section_step_over_shifted_cycle_source_toLinearMap
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
    (s : G) (n : ℕ) :
    let cycle_n :=
      fixed_constituent_section_cycle_fiber
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
    let cycle_succ :=
      fixed_constituent_section_cycle_fiber
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s (n + 1)
    (fixed_constituent_section_step_over_shifted_cycle_source
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n).toLinearMap =
      (cycle_succ.trans cycle_n.symm).toLinearMap := by
  let cycle_n :=
    fixed_constituent_section_cycle_fiber
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
  let cycle_succ :=
    fixed_constituent_section_cycle_fiber
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s (n + 1)
  have hcycle :
      cycle_n.toLinearMap.comp
          (fixed_constituent_section_step_over_shifted_cycle_source
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n).toLinearMap =
        cycle_succ.toLinearMap := by
    -- Expanding the recursive cycle definition exposes the common left factor `cycle_n`.
    simpa [cycle_n, cycle_succ, fixed_constituent_section_step_over_shifted_cycle_source,
      LinearMap.comp_assoc] using
      (fixed_constituent_section_cycle_fiber_succ_toLinearMap
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n).symm
  -- Cancel the equivalence `cycle_n` on the left to recover the literal step operator itself.
  ext x
  apply cycle_n.toLinearEquiv.injective
  calc
    cycle_n.toLinearMap
        ((fixed_constituent_section_step_over_shifted_cycle_source
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n).toLinearMap x) =
      cycle_succ.toLinearMap x := by
        simpa [LinearMap.comp_apply] using LinearMap.congr_fun hcycle x
    _ =
      cycle_n.toLinearMap (((cycle_succ.trans cycle_n.symm).toLinearMap) x) := by
        change cycle_succ x = cycle_n (cycle_n.symm (cycle_succ x))
        exact (cycle_n.toLinearEquiv.apply_symm_apply (cycle_succ x)).symm

/-- Helper for Theorem 17-17.6-1: every cycle comparison cancels with its inverse on the common
lift carrier `P_S`. This pointwise cancellation is the stable fragment of the cycle transport
normalization that survives before resolving the remaining shifted-family choice bridge. -/
theorem fixedConstituentSectionCycleFiber_apply_symm_apply
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
    (s : G) (n : ℕ) (x : P_S) :
    let cycle_n :=
      fixed_constituent_section_cycle_fiber
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
    cycle_n (cycle_n.symm x) = x := by
  let cycle_n :=
    fixed_constituent_section_cycle_fiber
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
  -- The cycle fiber is a representation equivalence, so it cancels with its inverse pointwise.
  simpa using cycle_n.toLinearEquiv.apply_symm_apply x

/-- Helper for Theorem 17-17.6-1: irreducibility is preserved when the fixed constituent is
transported by an element of `G`. This packages the standard conjugation/transport argument at the
exact API level needed for the shifted cycle-source normalization. -/
theorem transportedSubrepresentation_isIrreducible
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (g : G) :
    (transportedSubrepresentation ρ Sbar g).toRepresentation.IsIrreducible := by
  letI : Sbar.toRepresentation.IsIrreducible := hSbar_irred
  letI :
      Representation.IsIrreducible
        (Sbar.toRepresentation.comp (MulAut.conjNormal g⁻¹).toMonoidHom) := by
    -- Conjugating the source action does not change irreducibility.
    exact
      (conjugatedSubrepresentationOrderIso_local_c17
        (σ := Sbar.toRepresentation) g).isSimpleOrder_iff.mpr inferInstance
  -- The transported constituent is the canonical concrete model of that conjugated action.
  exact
    isIrreducible_of_equiv_local_c17
      (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar g)

/-- Helper for Theorem 17-17.6-1: two residue-field reductions of the same lifted source
representation identify their reduced target representations, and the resulting equivalence sends
the first reduction map to the second one. -/
theorem residueFieldLift_targetEquiv_of_commonSource
    {H : Type*} [Group H] [Finite H]
    {W₁ : Type*} [AddCommGroup W₁] [Module k W₁]
    [Module A W₁] [IsScalarTower A k W₁]
    {W₂ : Type*} [AddCommGroup W₂] [Module k W₂]
    [Module A W₂] [IsScalarTower A k W₂]
    {P : Type*} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    (σ : Representation k H W₁)
    (τ : Representation k H W₂)
    (ρA : Representation A H P)
    (red₁ : P →ₗ[A] W₁)
    (red₂ : P →ₗ[A] W₂)
    (hred₁ :
      letI : Module (MonoidAlgebra A H) P := Module.compHom P ρA.asAlgebraHom.toRingHom
      letI : IsScalarTower A (MonoidAlgebra A H) P :=
        IsScalarTower.of_algebraMap_smul fun a x ↦ by
          change ρA.asAlgebraHom (algebraMap A (MonoidAlgebra A H) a) x = a • x
          simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA.asAlgebraHom.commutes a) x
      letI : Module (MonoidAlgebra k H) W₁ := Module.compHom W₁ σ.asAlgebraHom.toRingHom
      letI : IsScalarTower k (MonoidAlgebra k H) W₁ :=
        IsScalarTower.of_algebraMap_smul fun a x ↦ by
          change σ.asAlgebraHom (algebraMap k (MonoidAlgebra k H) a) x = a • x
          simpa [Algebra.smul_def] using LinearMap.congr_fun (σ.asAlgebraHom.commutes a) x
      red₁.IsResidueFieldReduction H)
    (hred₂ :
      letI : Module (MonoidAlgebra A H) P := Module.compHom P ρA.asAlgebraHom.toRingHom
      letI : IsScalarTower A (MonoidAlgebra A H) P :=
        IsScalarTower.of_algebraMap_smul fun a x ↦ by
          change ρA.asAlgebraHom (algebraMap A (MonoidAlgebra A H) a) x = a • x
          simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA.asAlgebraHom.commutes a) x
      letI : Module (MonoidAlgebra k H) W₂ := Module.compHom W₂ τ.asAlgebraHom.toRingHom
      letI : IsScalarTower k (MonoidAlgebra k H) W₂ :=
        IsScalarTower.of_algebraMap_smul fun a x ↦ by
          change τ.asAlgebraHom (algebraMap k (MonoidAlgebra k H) a) x = a • x
          simpa [Algebra.smul_def] using LinearMap.congr_fun (τ.asAlgebraHom.commutes a) x
      red₂.IsResidueFieldReduction H) :
    ∃ e : σ.Equiv τ,
      (e.toLinearMap.restrictScalars A).comp red₁ = red₂ := by
  letI : Module (MonoidAlgebra A H) P := Module.compHom P ρA.asAlgebraHom.toRingHom
  letI : IsScalarTower A (MonoidAlgebra A H) P :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρA.asAlgebraHom (algebraMap A (MonoidAlgebra A H) a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA.asAlgebraHom.commutes a) x
  letI : Module A k := Algebra.toModule
  letI : IsScalarTower A k k := inferInstance
  letI : Module (MonoidAlgebra k H) W₁ := Module.compHom W₁ σ.asAlgebraHom.toRingHom
  letI : IsScalarTower k (MonoidAlgebra k H) W₁ :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change σ.asAlgebraHom (algebraMap k (MonoidAlgebra k H) a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (σ.asAlgebraHom.commutes a) x
  letI : Module (MonoidAlgebra k H) W₂ := Module.compHom W₂ τ.asAlgebraHom.toRingHom
  letI : IsScalarTower k (MonoidAlgebra k H) W₂ :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change τ.asAlgebraHom (algebraMap k (MonoidAlgebra k H) a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (τ.asAlgebraHom.commutes a) x
  change red₁.IsResidueFieldReduction H at hred₁
  change red₂.IsResidueFieldReduction H at hred₂
  let e : W₁ ≃ₗ[k] W₂ := hred₁.1.equiv.symm.trans hred₂.1.equiv
  have happly (x : P) : e (red₁ x) = red₂ x := by
    have h₁ : hred₁.1.equiv (1 ⊗ₜ[A] x) = red₁ x := by
      simpa using hred₁.1.equiv_tmul (1 : k) x
    have h₂ : hred₂.1.equiv (1 ⊗ₜ[A] x) = red₂ x := by
      simpa using hred₂.1.equiv_tmul (1 : k) x
    calc
      e (red₁ x) = e (hred₁.1.equiv (1 ⊗ₜ[A] x)) := by rw [h₁.symm]
      _ = hred₂.1.equiv (1 ⊗ₜ[A] x) := by simp [e]
      _ = red₂ x := h₂
  have hsurj : Function.Surjective red₁ := by
    intro y
    obtain ⟨t, rfl⟩ := hred₁.1.equiv.surjective y
    have hres : Function.Surjective (algebraMap A k) := by
      simpa [IsLocalRing.ResidueField.algebraMap_eq] using IsLocalRing.residue_surjective
    obtain ⟨x, hx⟩ := TensorProduct.mk_surjective (R := A) (S := k) (M := P) hres t
    refine ⟨x, ?_⟩
    have htmul : hred₁.1.equiv (1 ⊗ₜ[A] x) = red₁ x := by
      simpa using hred₁.1.equiv_tmul (1 : k) x
    exact htmul.symm.trans (congrArg hred₁.1.equiv hx)
  refine ⟨Representation.Equiv.mk e ?_, ?_⟩
  · intro g
    ext y
    obtain ⟨x, rfl⟩ := hsurj y
    have hσ :
        σ g (red₁ x) = MonoidAlgebra.of k H g • red₁ x := by
      change σ g (red₁ x) =
        (σ.asAlgebraHom (MonoidAlgebra.single g (1 : k))) (red₁ x)
      simp [Representation.asAlgebraHom_single, MonoidAlgebra.of_apply]
    have hτ :
        τ g (red₂ x) = MonoidAlgebra.of k H g • red₂ x := by
      change τ g (red₂ x) =
        (τ.asAlgebraHom (MonoidAlgebra.single g (1 : k))) (red₂ x)
      simp [Representation.asAlgebraHom_single, MonoidAlgebra.of_apply]
    calc
      e (σ g (red₁ x)) =
          e (MonoidAlgebra.of k H g • red₁ x) := by rw [hσ]
      _ = e (red₁ (MonoidAlgebra.of A H g • x)) := by
            rw [LinearMap.IsResidueFieldReduction.map_monoidAlgebra_of hred₁ g x]
      _ = red₂ (MonoidAlgebra.of A H g • x) := happly _
      _ = MonoidAlgebra.of k H g • red₂ x := by
            rw [LinearMap.IsResidueFieldReduction.map_monoidAlgebra_of hred₂ g x]
      _ = τ g (red₂ x) := hτ.symm
      _ = τ g (e (red₁ x)) := by rw [happly x]
  · ext x
    simpa [e] using happly x

/-- Helper for Theorem 17-17.6-1: any element of the transport fiber `U_s` determines a reduced
comparison from the fixed constituent `S̄` to the transported constituent `sS̄`; the difference
from the chosen section point in the same fiber is a scalar automorphism coming from the kernel
ratio in `U₁`. -/
theorem exists_fixed_constituent_transport_fiber_reduction_equiv
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
    ∃ e : Sbar.toRepresentation.Equiv
        (transportedSubrepresentation ρ Sbar s).toRepresentation,
      (((e.toLinearMap.restrictScalars A).comp red_S).comp u.toLinearMap =
        ((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s).toLinearMap.restrictScalars A).comp
          red_S) := by
  let ρA_conj : Representation A I P_S :=
    ρA_I.comp (MulAut.conjNormal s⁻¹).toMonoidHom
  let red_u : P_S →ₗ[A] Sbar.toSubmodule := red_S.comp u.toLinearMap
  let red_can : P_S →ₗ[A] (transportedSubrepresentation ρ Sbar s).toSubmodule :=
    ((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s).toLinearMap.restrictScalars A).comp
      red_S
  have hred_u_lift :
      IsResidueFieldLift Sbar.toRepresentation ρA_conj red_u := by
    simpa [ρA_conj, red_u] using
      residueFieldLift_of_equiv_source_local
        (A := A)
        (ρ := Sbar.toRepresentation)
        (ρA := ρA_I)
        (ρA' := ρA_conj)
        (red := red_S)
        (hLift := hLiftSbar)
        u
  have hred_can_lift :
      IsResidueFieldLift
        (transportedSubrepresentation ρ Sbar s).toRepresentation
        ρA_conj
        red_can := by
    simpa [ρA_conj, red_can] using
      transported_fixed_constituent_lift_of_conjugation
        (A := A) (G := G) (V := V) I ρ Sbar ρA_I red_S hLiftSbar s
  obtain ⟨e, he⟩ :=
    residueFieldLift_targetEquiv_of_commonSource
      (A := A)
      (H := I)
      (σ := Sbar.toRepresentation)
      (τ := (transportedSubrepresentation ρ Sbar s).toRepresentation)
      (ρA := ρA_conj)
      (red₁ := red_u)
      (red₂ := red_can)
      (by simpa [IsResidueFieldLift, ρA_conj, red_u] using hred_u_lift)
      (by simpa [IsResidueFieldLift, ρA_conj, red_can] using hred_can_lift)
  refine ⟨e, ?_⟩
  simpa [red_u, red_can, LinearMap.comp_assoc] using he

/-- Helper for Theorem 17-17.6-1: choose the reduced comparison attached to an arbitrary element
of the transport fiber `U_s`. This is the reusable reduction-side interface needed for the later
`G₂`-action on the multiplicity space. -/
noncomputable def fixed_constituent_transport_fiber_reduction_equiv
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
    Sbar.toRepresentation.Equiv
      (transportedSubrepresentation ρ Sbar s).toRepresentation :=
  Classical.choose <|
    exists_fixed_constituent_transport_fiber_reduction_equiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s u

/-- Helper for Theorem 17-17.6-1: the chosen reduced comparison for an arbitrary fiber element
intertwines its action on the lift carrier with the canonical transported constituent map in the
ambient representation. -/
theorem fixed_constituent_transport_fiber_reduction_equiv_spec
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
    ((LinearMap.restrictScalars A
        ((fixed_constituent_transport_fiber_reduction_equiv
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s u).toLinearMap)).comp
        red_S).comp u.toLinearMap =
      (LinearMap.restrictScalars A
        ((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s).toLinearMap)).comp red_S := by
  exact
    Classical.choose_spec <|
      exists_fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s u

/-- Helper for Theorem 17-17.6-1: the chosen reduced comparison attached to a fixed transport
fiber element is uniquely determined by its reduction identity after composing with `red_S`.
This packages the exact source-side uniqueness needed before enforcing group-law coherence. -/
theorem fixed_constituent_transport_fiber_reduction_equiv_unique
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
    {s : G}
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s)
    {e e' :
      Sbar.toRepresentation.Equiv
        (transportedSubrepresentation ρ Sbar s).toRepresentation}
    (he :
      (((e.toLinearMap.restrictScalars A).comp red_S).comp u.toLinearMap =
        ((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s).toLinearMap.restrictScalars A).comp
          red_S))
    (he' :
      (((e'.toLinearMap.restrictScalars A).comp red_S).comp u.toLinearMap =
        ((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s).toLinearMap.restrictScalars A).comp
          red_S)) :
    e = e' := by
  letI : Module (MonoidAlgebra A I) P_S := representationCarrierGroupAlgebraModule ρA_I
  letI : IsScalarTower A (MonoidAlgebra A I) P_S :=
    representationCarrierGroupAlgebraIsScalarTower ρA_I
  letI : Module (MonoidAlgebra k I) Sbar.toSubmodule :=
    representationCarrierGroupAlgebraModule Sbar.toRepresentation
  letI : IsScalarTower k (MonoidAlgebra k I) Sbar.toSubmodule :=
    representationCarrierGroupAlgebraIsScalarTower Sbar.toRepresentation
  have hred : red_S.IsResidueFieldReduction I := by
    simpa using hLiftSbar
  have hsurj_red : Function.Surjective red_S :=
    fixed_constituent_reduction_surjective (A := A) (H := I) hred
  have hsurj : Function.Surjective (red_S.comp u.toLinearMap) := by
    intro y
    obtain ⟨x, hx⟩ := hsurj_red y
    refine ⟨u.symm x, ?_⟩
    have hcancel : u.toLinearMap (u.symm.toLinearMap x) = x :=
      u.toLinearEquiv.apply_symm_apply x
    change red_S (u.toLinearMap (u.symm.toLinearMap x)) = y
    rw [hcancel]
    exact hx
  have hcomp :
      ((e.toLinearMap.restrictScalars A).comp red_S).comp u.toLinearMap =
        ((e'.toLinearMap.restrictScalars A).comp red_S).comp u.toLinearMap :=
    he.trans he'.symm
  ext y
  obtain ⟨x, hx⟩ := hsurj y
  have hpoint := LinearMap.congr_fun hcomp x
  have hpoint' :
      e.toLinearMap ((red_S.comp u.toLinearMap) x) =
        e'.toLinearMap ((red_S.comp u.toLinearMap) x) := by
    simpa [LinearMap.comp_apply] using hpoint
  rw [hx] at hpoint'
  simpa using hpoint'

/-- Helper for Theorem 17-17.6-1: once the reduced-side section has been normalized so that the
chosen comparison at `1` is canonical, Serre's literal `n`-step section cycle reduces to the
canonical ambient transport over `s ^ n`. The normalization hypothesis is necessary already at
`n = 0`, where the empty cycle forces the endpoint comparison at `1` to be the canonical one. -/
theorem shiftedCycleSourceReductionUnique
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
    (s : G) (n : ℕ) :
    let Tn := transportedSubrepresentation ρ Sbar (s ^ n)
    let cycle_n :=
      fixed_constituent_section_cycle_fiber
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
    let red_n :=
      ((((hTransport (s ^ n)).some.toLinearMap.restrictScalars A).comp red_S).comp
        cycle_n.toLinearMap)
    ∀ (u :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I
          (ρA_I.comp (MulAut.conjNormal (s ^ n)⁻¹).toMonoidHom) s)
      {e e' :
        Tn.toRepresentation.Equiv (transportedSubrepresentation ρ Tn s).toRepresentation},
      ((((e.toLinearMap.restrictScalars A).comp red_n).comp u.toLinearMap) =
          ((transportedSubrepresentation_rep_equiv_local_c17 ρ Tn s).toLinearMap.restrictScalars A).comp
            red_n) →
        ((((e'.toLinearMap.restrictScalars A).comp red_n).comp u.toLinearMap) =
          ((transportedSubrepresentation_rep_equiv_local_c17 ρ Tn s).toLinearMap.restrictScalars A).comp
            red_n) →
          e = e' := by
  dsimp only
  let Tn := transportedSubrepresentation ρ Sbar (s ^ n)
  let cycle_n :=
    fixed_constituent_section_cycle_fiber
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
  let red_n :=
    ((((hTransport (s ^ n)).some.toLinearMap.restrictScalars A).comp red_S).comp
      cycle_n.toLinearMap)
  intro u e e' he he'
  letI : Module (MonoidAlgebra A I) P_S := representationCarrierGroupAlgebraModule ρA_I
  letI : IsScalarTower A (MonoidAlgebra A I) P_S :=
    representationCarrierGroupAlgebraIsScalarTower ρA_I
  letI : Module (MonoidAlgebra k I) Sbar.toSubmodule :=
    representationCarrierGroupAlgebraModule Sbar.toRepresentation
  letI : IsScalarTower k (MonoidAlgebra k I) Sbar.toSubmodule :=
    representationCarrierGroupAlgebraIsScalarTower Sbar.toRepresentation
  have hred : red_S.IsResidueFieldReduction I := by
    simpa using hLiftSbar
  have hsurj_red : Function.Surjective red_S :=
    fixed_constituent_reduction_surjective (A := A) (H := I) hred
  have hsurj_red_n : Function.Surjective red_n := by
    intro y
    obtain ⟨x, hx⟩ := hsurj_red ((hTransport (s ^ n)).some.symm y)
    refine ⟨cycle_n.symm x, ?_⟩
    have hcycle : cycle_n.toLinearMap (cycle_n.symm.toLinearMap x) = x :=
      cycle_n.toLinearEquiv.apply_symm_apply x
    have htransport :
        (hTransport (s ^ n)).some.toLinearMap
            ((hTransport (s ^ n)).some.symm.toLinearMap y) =
          y :=
      (hTransport (s ^ n)).some.toLinearEquiv.apply_symm_apply y
    calc
      red_n (cycle_n.symm x) =
        (hTransport (s ^ n)).some.toLinearMap
          (red_S (cycle_n.toLinearMap (cycle_n.symm.toLinearMap x))) := rfl
      _ = (hTransport (s ^ n)).some.toLinearMap (red_S x) := by
        rw [hcycle]
      _ =
        (hTransport (s ^ n)).some.toLinearMap
          ((hTransport (s ^ n)).some.symm.toLinearMap y) := by
        simpa using
          congrArg
            (fun y0 : Sbar.toSubmodule =>
              (hTransport (s ^ n)).some.toLinearMap y0)
            hx
      _ = y := htransport
  have hsurj : Function.Surjective (red_n.comp u.toLinearMap) := by
    intro y
    obtain ⟨x, hx⟩ := hsurj_red_n y
    refine ⟨u.symm x, ?_⟩
    have hcancel : u.toLinearMap (u.symm.toLinearMap x) = x :=
      u.toLinearEquiv.apply_symm_apply x
    change red_n (u.toLinearMap (u.symm.toLinearMap x)) = y
    rw [hcancel]
    exact hx
  have hcomp :
      ((e.toLinearMap.restrictScalars A).comp red_n).comp u.toLinearMap =
        ((e'.toLinearMap.restrictScalars A).comp red_n).comp u.toLinearMap :=
    he.trans he'.symm
  ext y
  obtain ⟨x, hx⟩ := hsurj y
  have hpoint := LinearMap.congr_fun hcomp x
  have hpoint' :
      e.toLinearMap ((red_n.comp u.toLinearMap) x) =
        e'.toLinearMap ((red_n.comp u.toLinearMap) x) := by
    simpa [LinearMap.comp_apply] using hpoint
  rw [hx] at hpoint'
  simpa using hpoint'

/-- Helper for Theorem 17-17.6-1: the canonical comparison for transport by `s ^ (n + 1)`
is the one-step canonical comparison after the canonical comparison for transport by `s ^ n`. -/
private theorem transportedSubrepresentation_rep_equiv_local_pow_succ_toLinearMap
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G) (n : ℕ) :
    (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (s ^ (n + 1))).toLinearMap =
      (transportedSubrepresentation_rep_equiv_local_pow_succ
        (I := I) (ρ := ρ) (Sbar := Sbar) s n).toLinearMap.comp
        (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (s ^ n)).toLinearMap := by
  ext x
  have hsucc :=
    LinearMap.congr_fun
      (transportedSubrepresentation_rep_equiv_local_subtype
        (I := I) (ρ := ρ) (Sbar := Sbar) (s ^ (n + 1))) x
  have hstep :=
    LinearMap.congr_fun
      (transportedSubrepresentation_rep_equiv_local_subtype_pow_succ
        (I := I) (ρ := ρ) (Sbar := Sbar) s n) x
  exact hsucc.trans hstep.symm

/-- Helper for Theorem 17-17.6-1: Serre's literal cycle step reduces through the reduced
equivalences attached to the actual fiber elements in the transport cover. -/
theorem fixed_constituent_section_cycle_succ_reduction_in_ambient
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
    (s : G) (n : ℕ) :
    let Tn := transportedSubrepresentation ρ Sbar (s ^ n)
    let cycle_n :=
      fixed_constituent_section_cycle_fiber
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
    let cycle_succ :=
      fixed_constituent_section_cycle_fiber
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s (n + 1)
    let e_n :=
      fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (s ^ n) cycle_n
    let e_succ :=
      fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (s ^ (n + 1)) cycle_succ
    (((transportedSubrepresentation ρ Sbar (s ^ (n + 1))).toSubmodule.subtype.restrictScalars A).comp
        (((e_succ.toLinearMap.restrictScalars A).comp red_S).comp cycle_succ.toLinearMap)) =
      ((((ρ s).comp Tn.toSubmodule.subtype).restrictScalars A).comp
        (((e_n.toLinearMap.restrictScalars A).comp red_S).comp cycle_n.toLinearMap)) := by
  dsimp only
  let Tn := transportedSubrepresentation ρ Sbar (s ^ n)
  let cycle_n :=
    fixed_constituent_section_cycle_fiber
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
  let cycle_succ :=
    fixed_constituent_section_cycle_fiber
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s (n + 1)
  let e_n :=
    fixed_constituent_transport_fiber_reduction_equiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (s ^ n) cycle_n
  let e_succ :=
    fixed_constituent_transport_fiber_reduction_equiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (s ^ (n + 1)) cycle_succ
  have hsucc :=
    fixed_constituent_transport_fiber_reduction_equiv_spec
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (s ^ (n + 1)) cycle_succ
  have hn :=
    fixed_constituent_transport_fiber_reduction_equiv_spec
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (s ^ n) cycle_n
  ext z
  have hsucc_z := LinearMap.congr_fun hsucc z
  have hn_z := LinearMap.congr_fun hn z
  have hlocal_z :=
    LinearMap.congr_fun
      (transportedSubrepresentation_rep_equiv_local_pow_succ_toLinearMap
        (I := I) (ρ := ρ) (Sbar := Sbar) s n) (red_S z)
  have hsubtype_z :=
    LinearMap.congr_fun
      (transportedSubrepresentation_rep_equiv_local_pow_succ_subtype
        (I := I) (ρ := ρ) (Sbar := Sbar) s n)
      (((e_n.toLinearMap.restrictScalars A).comp red_S).comp cycle_n.toLinearMap z)
  calc
    ((transportedSubrepresentation ρ Sbar (s ^ (n + 1))).toSubmodule.subtype)
        (e_succ.toLinearMap (red_S (cycle_succ.toLinearMap z))) =
      ((transportedSubrepresentation ρ Sbar (s ^ (n + 1))).toSubmodule.subtype)
        ((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (s ^ (n + 1))).toLinearMap
          (red_S z)) := by
        simpa [LinearMap.comp_apply] using congrArg
          (fun y => (transportedSubrepresentation ρ Sbar (s ^ (n + 1))).toSubmodule.subtype y)
          hsucc_z
    _ =
      ((transportedSubrepresentation ρ Sbar (s ^ (n + 1))).toSubmodule.subtype)
        ((transportedSubrepresentation_rep_equiv_local_pow_succ
          (I := I) (ρ := ρ) (Sbar := Sbar) s n).toLinearMap
          (((e_n.toLinearMap.restrictScalars A).comp red_S).comp cycle_n.toLinearMap z)) := by
        have harg :
            ((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (s ^ n)).toLinearMap
              (red_S z)) =
              (((e_n.toLinearMap.restrictScalars A).comp red_S).comp
                cycle_n.toLinearMap z) := by
          simpa [LinearMap.comp_apply] using hn_z.symm
        have htarget :
            (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (s ^ (n + 1))).toLinearMap
                (red_S z) =
              (transportedSubrepresentation_rep_equiv_local_pow_succ
                (I := I) (ρ := ρ) (Sbar := Sbar) s n).toLinearMap
                (((e_n.toLinearMap.restrictScalars A).comp red_S).comp
                  cycle_n.toLinearMap z) := by
          calc
            (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (s ^ (n + 1))).toLinearMap
                (red_S z) =
              (transportedSubrepresentation_rep_equiv_local_pow_succ
                (I := I) (ρ := ρ) (Sbar := Sbar) s n).toLinearMap
                ((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (s ^ n)).toLinearMap
                  (red_S z)) := by
                simpa [LinearMap.comp_apply] using hlocal_z
            _ =
              (transportedSubrepresentation_rep_equiv_local_pow_succ
                (I := I) (ρ := ρ) (Sbar := Sbar) s n).toLinearMap
                (((e_n.toLinearMap.restrictScalars A).comp red_S).comp
                  cycle_n.toLinearMap z) := by
                rw [harg]
        exact congrArg
          (fun y => (transportedSubrepresentation ρ Sbar (s ^ (n + 1))).toSubmodule.subtype y)
          htarget
    _ =
      ((ρ s).comp (transportedSubrepresentation ρ Sbar (s ^ n)).toSubmodule.subtype)
        (((e_n.toLinearMap.restrictScalars A).comp red_S).comp cycle_n.toLinearMap z) := by
        simpa [LinearMap.comp_apply] using hsubtype_z

/-- Helper for Theorem 17-17.6-1: the one-step section after an `n`-cycle reduces to the
canonical one-step transport when both endpoints use the reduced equivalences attached to their
actual fiber elements. -/
theorem fixed_constituent_section_step_reduction_after_cycle_precompose
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
    (s : G) (n : ℕ) :
    let Tn := transportedSubrepresentation ρ Sbar (s ^ n)
    let cycle_n :=
      fixed_constituent_section_cycle_fiber
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
    let cycle_succ :=
      fixed_constituent_section_cycle_fiber
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s (n + 1)
    let sec :=
      fixed_constituent_transport_total_space_section
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let e_n :=
      fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (s ^ n) cycle_n
    let e_succ :=
      fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (s ^ (n + 1)) cycle_succ
    (((e_succ.toLinearMap.restrictScalars A).comp red_S).comp
        (cycle_n.toLinearMap.comp (sec s).2.toLinearMap)) =
        (((transportedSubrepresentation_rep_equiv_local_pow_succ
                (I := I) (ρ := ρ) (Sbar := Sbar) s n).toLinearMap.restrictScalars
            A).comp
          (((e_n.toLinearMap.restrictScalars A).comp red_S).comp cycle_n.toLinearMap)) := by
  dsimp only
  let Tn := transportedSubrepresentation ρ Sbar (s ^ n)
  let cycle_n :=
    fixed_constituent_section_cycle_fiber
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
  let cycle_succ :=
    fixed_constituent_section_cycle_fiber
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s (n + 1)
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let e_n :=
    fixed_constituent_transport_fiber_reduction_equiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (s ^ n) cycle_n
  let e_succ :=
    fixed_constituent_transport_fiber_reduction_equiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (s ^ (n + 1)) cycle_succ
  have hcycle :=
    fixed_constituent_section_cycle_fiber_succ_toLinearMap
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
  have hsucc :=
    fixed_constituent_transport_fiber_reduction_equiv_spec
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (s ^ (n + 1)) cycle_succ
  have hn :=
    fixed_constituent_transport_fiber_reduction_equiv_spec
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (s ^ n) cycle_n
  ext z
  have hcycle_z : cycle_n.toLinearMap ((sec s).2.toLinearMap z) = cycle_succ.toLinearMap z := by
    simpa [cycle_n, cycle_succ, sec, LinearMap.comp_apply] using
      (LinearMap.congr_fun hcycle z).symm
  have hsucc_z := LinearMap.congr_fun hsucc z
  have hn_z := LinearMap.congr_fun hn z
  have hlocal_z :=
    LinearMap.congr_fun
      (transportedSubrepresentation_rep_equiv_local_pow_succ_toLinearMap
        (I := I) (ρ := ρ) (Sbar := Sbar) s n) (red_S z)
  simpa [LinearMap.comp_apply] using
    (calc
      e_succ.toLinearMap (red_S (cycle_n.toLinearMap ((sec s).2.toLinearMap z))) =
        e_succ.toLinearMap (red_S (cycle_succ.toLinearMap z)) := by
          rw [hcycle_z]
      _ =
        (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (s ^ (n + 1))).toLinearMap
          (red_S z) := by
          simpa [LinearMap.comp_apply] using hsucc_z
      _ =
        (transportedSubrepresentation_rep_equiv_local_pow_succ
          (I := I) (ρ := ρ) (Sbar := Sbar) s n).toLinearMap
          (((e_n.toLinearMap.restrictScalars A).comp red_S).comp cycle_n.toLinearMap z) := by
          have harg :
              (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (s ^ n)).toLinearMap
                  (red_S z) =
                (((e_n.toLinearMap.restrictScalars A).comp red_S).comp
                  cycle_n.toLinearMap z) := by
            simpa [LinearMap.comp_apply] using hn_z.symm
          calc
            (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (s ^ (n + 1))).toLinearMap
                (red_S z) =
              (transportedSubrepresentation_rep_equiv_local_pow_succ
                (I := I) (ρ := ρ) (Sbar := Sbar) s n).toLinearMap
                ((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (s ^ n)).toLinearMap
                  (red_S z)) := by
                simpa [LinearMap.comp_apply] using hlocal_z
            _ =
              (transportedSubrepresentation_rep_equiv_local_pow_succ
                (I := I) (ρ := ρ) (Sbar := Sbar) s n).toLinearMap
                (((e_n.toLinearMap.restrictScalars A).comp red_S).comp
                  cycle_n.toLinearMap z) := by
                rw [harg])

/-- Helper for Theorem 17-17.6-1: the literal `n`-step section cycle reduces to the ambient
transport by `s ^ n` after applying the reduced equivalence attached to that cycle element. -/
theorem fixed_constituent_section_cycle_reduction_in_ambient
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
    (hTransportOne :
      (hTransport (1 : G)).some =
        transportedSubrepresentation_rep_equiv_local_one (I := I) (ρ := ρ) Sbar)
    (s : G) :
    ∀ n : ℕ,
      let cycle_n :=
        fixed_constituent_section_cycle_fiber
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
      let e_n :=
        fixed_constituent_transport_fiber_reduction_equiv
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
          (s ^ n) cycle_n
      (((transportedSubrepresentation ρ Sbar (s ^ n)).toSubmodule.subtype.restrictScalars A).comp
          (((e_n.toLinearMap.restrictScalars A).comp red_S).comp cycle_n.toLinearMap)) =
        ((((ρ (s ^ n)).comp Sbar.toSubmodule.subtype).restrictScalars A).comp red_S) := by
  intro n
  dsimp only
  let cycle_n :=
    fixed_constituent_section_cycle_fiber
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
  let e_n :=
    fixed_constituent_transport_fiber_reduction_equiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (s ^ n) cycle_n
  have hn :=
    fixed_constituent_transport_fiber_reduction_equiv_spec
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (s ^ n) cycle_n
  ext z
  have hn_z := LinearMap.congr_fun hn z
  have hsubtype :=
    LinearMap.congr_fun
      (transportedSubrepresentation_rep_equiv_local_subtype
        (I := I) (ρ := ρ) (Sbar := Sbar) (s ^ n)) (red_S z)
  calc
    ((transportedSubrepresentation ρ Sbar (s ^ n)).toSubmodule.subtype)
        (e_n.toLinearMap (red_S (cycle_n.toLinearMap z))) =
      ((transportedSubrepresentation ρ Sbar (s ^ n)).toSubmodule.subtype)
        ((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (s ^ n)).toLinearMap
          (red_S z)) := by
        simpa [LinearMap.comp_apply] using congrArg
          (fun y => (transportedSubrepresentation ρ Sbar (s ^ n)).toSubmodule.subtype y)
          hn_z
    _ = ((ρ (s ^ n)).comp Sbar.toSubmodule.subtype) (red_S z) := by
        simpa [LinearMap.comp_apply] using hsubtype

/-- Helper for Theorem 17-17.6-1: casting a fixed-constituent transport fiber along an equality
of group indices leaves the underlying linear map unchanged. -/
theorem fixed_constituent_transport_fiber_cast_toLinearMap_apply
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    {s t : G} (h : s = t)
    (u : fixed_constituent_transport_fiber (A := A) (G := G) I ρA_I s)
    (x : P_S) :
    ((cast
        (congrArg
          (fun g : G =>
            fixed_constituent_transport_fiber
              (A := A) (G := G) I ρA_I g) h) u :
      fixed_constituent_transport_fiber (A := A) (G := G) I ρA_I t).toLinearMap x) =
      u.toLinearMap x := by
  cases h
  rfl

/-- Helper for Theorem 17-17.6-1: the `|G|`-cycle in the kernel fiber reduces to the identity
ambient action after applying the reduced equivalence attached to that kernel element. -/
theorem fixed_constituent_section_card_cycle_kernel_reduction_comp_eq
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
    (hTransportOne :
      (hTransport (1 : G)).some =
        transportedSubrepresentation_rep_equiv_local_one (I := I) (ρ := ρ) Sbar)
    (s : G) :
    let cycle :=
      fixed_constituent_section_card_cycle_kernel
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s
    let e :=
      fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (1 : G) cycle
    (((transportedSubrepresentation ρ Sbar (1 : G)).toSubmodule.subtype.restrictScalars A).comp
        (((e.toLinearMap.restrictScalars A).comp red_S).comp cycle.toLinearMap)) =
      (Sbar.toSubmodule.subtype.restrictScalars A).comp red_S := by
  dsimp only
  let cycle :=
    fixed_constituent_section_card_cycle_kernel
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s
  let e :=
    fixed_constituent_transport_fiber_reduction_equiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (1 : G) cycle
  have hspec :=
    fixed_constituent_transport_fiber_reduction_equiv_spec
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (1 : G) cycle
  ext z
  have hspec_z := LinearMap.congr_fun hspec z
  have hsubtype :=
    LinearMap.congr_fun
      (transportedSubrepresentation_rep_equiv_local_subtype
        (I := I) (ρ := ρ) (Sbar := Sbar) (1 : G)) (red_S z)
  calc
    (transportedSubrepresentation ρ Sbar (1 : G)).toSubmodule.subtype
        (e.toLinearMap (red_S (cycle.toLinearMap z))) =
      (transportedSubrepresentation ρ Sbar (1 : G)).toSubmodule.subtype
        ((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (1 : G)).toLinearMap
          (red_S z)) := by
        simpa [LinearMap.comp_apply] using congrArg
          (fun y => (transportedSubrepresentation ρ Sbar (1 : G)).toSubmodule.subtype y)
          hspec_z
    _ = Sbar.toSubmodule.subtype (red_S z) := by
        simpa [LinearMap.comp_apply] using hsubtype

/-- Helper for Theorem 17-17.6-1: the reduced comparison attached to the `|G|`-cycle identifies
its action on the fixed lift with the canonical identity transport at `1`. -/
theorem fixed_constituent_section_card_cycle_kernel_reduction_eq_id
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
    (hTransportOne :
      (hTransport (1 : G)).some =
        transportedSubrepresentation_rep_equiv_local_one (I := I) (ρ := ρ) Sbar)
    (s : G) :
    let cycle :=
      fixed_constituent_section_card_cycle_kernel
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s
    let e :=
      fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (1 : G) cycle
    (((e.toLinearMap.restrictScalars A).comp red_S).comp cycle.toLinearMap) =
      ((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (1 : G)).toLinearMap.restrictScalars A).comp
        red_S := by
  dsimp only
  let cycle :=
    fixed_constituent_section_card_cycle_kernel
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s
  exact
    fixed_constituent_transport_fiber_reduction_equiv_spec
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (1 : G) cycle

end

end Representation
