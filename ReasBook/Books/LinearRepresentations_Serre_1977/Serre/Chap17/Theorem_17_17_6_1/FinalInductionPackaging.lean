import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_6_1.QuotientStepReduction
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_6_1.QuotientHeightRecursion
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_6_1.HallKernelCliffordSplit

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

/-- Helper for Theorem 17-17.6-1: precomposing an irreducible representation with a group
equivalence preserves irreducibility. -/
theorem isIrreducible_comp_mulEquiv
    {F : Type*} [Field F] {H K : Type*} [Group H] [Group K]
    {W : Type*} [AddCommGroup W] [Module F W]
    (e : H ≃* K) (σ : Representation F K W) [σ.IsIrreducible] :
    Representation.IsIrreducible (σ.comp e.toMonoidHom) := by
  classical
  letI : Nontrivial (Subrepresentation (σ.comp e.toMonoidHom)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro hbot
    have h' : (⊥ : Subrepresentation σ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using congrArg Subrepresentation.toSubmodule hbot
    exact IsSimpleOrder.bot_ne_top h'
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro Wsub hWsub
  let W' : Subrepresentation σ :=
    { toSubmodule := Wsub.toSubmodule
      apply_mem_toSubmodule := by
        intro g y hy
        simpa using Wsub.apply_mem_toSubmodule (e.symm g) hy }
  have hW'_ne_bot : W' ≠ ⊥ := by
    intro hW'
    apply hWsub
    apply Subrepresentation.toSubmodule_injective
    simpa [W'] using congrArg Subrepresentation.toSubmodule hW'
  have hW'_top : W' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W').resolve_left hW'_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [W'] using congrArg Subrepresentation.toSubmodule hW'_top

/-- Helper for Theorem 17-17.6-1: a residue-field lift of the pullback along a group equivalence
transports back to a lift over the original group. -/
theorem residueFieldLift_of_mulEquiv_group
    {H K : Type*} [Group H] [Group K]
    {W : Type*} [AddCommGroup W] [Module k W]
    {P : Type*} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    (e : H ≃* K)
    {σ : Representation k K W}
    {ρA : Representation A H P}
    {red : P →ₗ[A] W}
    (hLift : IsResidueFieldLift (σ.comp e.toMonoidHom) ρA red) :
    IsResidueFieldLift σ (ρA.comp e.symm.toMonoidHom) red := by
  have hcomp := Representation.isResidueFieldLift_comp hLift e.symm.toMonoidHom
  convert hcomp
  ext g w
  simp

/-- Helper for Theorem 17-17.6-1: lower-height recursion over the original finite-group universe
also applies to any finite group after shrinking it to that universe and transporting the lift
back. -/
theorem exists_residueFieldLift_of_shrink_lower_height
    (hrecLower :
      ∀ {G' : Type v} [Group G'] [Finite G']
        {V' : Type x} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
        (hG' : IsPSolvableOfHeight p h G')
        (ρ' : Representation k G' V') [ρ'.IsIrreducible],
          ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
            (_ : Module.Free A P) (_ : Module.Finite A P)
            (ρA : Representation A G' P)
            (red : P →ₗ[A] V'),
              IsResidueFieldLift ρ' ρA red)
    {H : Type w} [Group H] [Finite H]
    {W : Type x} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (hH : IsPSolvableOfHeight p h H)
    (τ : Representation k H W) [τ.IsIrreducible] :
    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A H P)
      (red : P →ₗ[A] W),
        IsResidueFieldLift τ ρA red := by
  letI : Small.{v} H := small_map (Finite.equivFin H)
  let Hs : Type v := Shrink.{v} H
  letI : Group Hs := inferInstance
  letI : Finite Hs := Finite.of_equiv H (equivShrink H)
  let e : Hs ≃* H := Shrink.mulEquiv
  let τs : Representation k Hs W := τ.comp e.toMonoidHom
  have hτs : τs.IsIrreducible := by
    exact isIrreducible_comp_mulEquiv e τ
  letI : τs.IsIrreducible := hτs
  have hHs : IsPSolvableOfHeight p h Hs := by
    exact IsPSolvableOfHeight.of_equiv e.symm hH
  rcases hrecLower hHs τs with ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA, red, hLift⟩
  letI : AddCommGroup P := hPadd
  letI : Module A P := hPmod
  letI : Module.Free A P := hPfree
  letI : Module.Finite A P := hPfinite
  exact
    ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA.comp e.symm.toMonoidHom, red,
      residueFieldLift_of_mulEquiv_group e hLift⟩

/-- Helper for Theorem 17-17.6-1: if Serre's chosen quotient step `M̄ = M / N` is a `p`-group,
the remaining work is the source-faithful Schur-Zassenhaus split `M = N × P` inside the literal
pullback subgroup `M ≤ H`. -/
theorem
    exists_residueFieldLift_of_central_cyclic_coprime_kernel_pgroup_preimage_branch
    (hp : Nat.Prime p)
    {H : Type v} [Group H] [Finite H]
    {W : Type x} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (N : Subgroup H) [N.Normal]
    (hNcentral : N ≤ Subgroup.center H)
    (hNcyclic : IsCyclic N)
    (hNcop : Nat.Coprime p (Nat.card N))
    (hrecLower :
      ∀ {G' : Type v} [Group G'] [Finite G']
        {V' : Type x} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
        (hG' : IsPSolvableOfHeight p (Nat.succ h) G')
        (ρ' : Representation k G' V') [ρ'.IsIrreducible],
          ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
            (_ : Module.Free A P) (_ : Module.Finite A P)
            (ρA : Representation A G' P)
            (red : P →ₗ[A] V'),
              IsResidueFieldLift ρ' ρA red)
    (τ : Representation k H W) [τ.IsIrreducible]
    (Mbar : Subgroup (H ⧸ N)) [Mbar.Normal]
    (hMp : IsPGroup p Mbar)
    (hMquot :
      IsPSolvableOfHeight p h
        (H ⧸ Subgroup.comap (QuotientGroup.mk' N) Mbar)) :
    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A H P)
      (red : P →ₗ[A] W),
        IsResidueFieldLift τ ρA red := by
  let M : Subgroup H := Subgroup.comap (QuotientGroup.mk' N) Mbar
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP_le_M, hPp, hP_disjoint, hP_sup⟩ :
      ∃ P : Subgroup H,
        P ≤ M ∧
        IsPGroup p P ∧
        Disjoint N P ∧
        N ⊔ P = M := by
    -- First isolate Serre's literal subgroup decomposition `M = N × P`; the remaining blocker is
    -- only the quotient descent through this concrete complement.
    simpa [M] using
      pgroup_preimage_complement_data_of_quotient_normal_step
        (p := p) hp (N := N) hNcop Mbar hMp
  letI : P.Normal := by
    -- Route correction: install normality on the literal complement `P` before forming
    -- `H ⧸ P`; this is the exact subgroup-transport step that was previously left implicit.
    exact
      normal_of_pgroup_preimage_complement
        (p := p) hp (N := N) hNcentral hNcop Mbar P hP_le_M hPp hP_disjoint hP_sup
  have hτ_trivial : Representation.IsTrivial (τ.comp P.subtype) := by
    -- A normal `p`-subgroup acts trivially on an irreducible module in characteristic `p`.
    exact
      isTrivial_restrict_normal_pSubgroup_of_isIrreducible
        (p := p) (A := A) (G := H) (V := W) τ P hPp
  letI : Representation.IsTrivial (τ.comp P.subtype) := hτ_trivial
  let τP : Representation k (H ⧸ P) W := τ.ofQuotient P
  letI : τP.IsIrreducible := by
    exact isIrreducible_of_ofQuotient_of_isTrivial_c17 τ P
  let hPkg :=
    central_cyclic_image_quotient_data_of_pgroup_preimage_split
      (p := p) (h := h) (N := N) hNcentral hNcyclic hNcop Mbar P hP_le_M hP_disjoint hP_sup
      hMquot
  have hHPsolv := hPkg.hQuotientHeight
  have hLiftQuot :
      ∃ (P' : Type (max u v x)) (_ : AddCommGroup P') (_ : Module A P')
        (_ : Module.Free A P') (_ : Module.Finite A P')
        (ρA : Representation A (H ⧸ P) P')
        (red : P' →ₗ[A] W),
          IsResidueFieldLift τP ρA red := by
    -- The recursive content is now exactly Serre's lower-height step on `H ⧸ P`.
    exact hrecLower hHPsolv τP
  -- Inflate the recursive quotient lift back to `τ` in the already prepared witness universe.
  exact
    exists_residueFieldLift_of_ofQuotient_of_isTrivial_witness
      (A := A) (ρ := τ) (I := P) hLiftQuot

/-- Helper for Theorem 17-17.6-1: once Serre's quotient module `τ` over `H / N̄` is in hand, the
remaining source-faithful step is a lower-height induction across the central cyclic coprime
kernel `N̄`. -/
theorem
    exists_residueFieldLift_of_isIrreducible_of_central_cyclic_coprime_kernel_via_lower_height
    (hp : Nat.Prime p)
    {H : Type v} [Group H] [Finite H]
    {W : Type x} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (N : Subgroup H) [N.Normal]
    (hNcentral : N ≤ Subgroup.center H)
    (hNcyclic : IsCyclic N)
    (hNcop : Nat.Coprime p (Nat.card N))
    (hquot : IsPSolvableOfHeight p h (H ⧸ N))
    (hrecLower :
      ∀ {G' : Type v} [Group G'] [Finite G']
        {V' : Type x} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
        (hG' : IsPSolvableOfHeight p h G')
        (ρ' : Representation k G' V') [ρ'.IsIrreducible],
          ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
            (_ : Module.Free A P) (_ : Module.Finite A P)
            (ρA : Representation A G' P)
            (red : P →ₗ[A] V'),
              IsResidueFieldLift ρ' ρA red)
    (τ : Representation k H W) [τ.IsIrreducible] :
    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A H P)
      (red : P →ₗ[A] W),
        IsResidueFieldLift τ ρA red := by
  cases h with
  | zero =>
      letI : Subsingleton (H ⧸ N) := hquot
      have hN_top : N = ⊤ := by
        -- When `H ⧸ N` is trivial, every element of `H` maps to `1`, so the kernel is all of `H`.
        ext x
        constructor
        · intro hx
          simp
        · intro _
          have hxq : (QuotientGroup.mk x : H ⧸ N) = 1 := Subsingleton.elim _ _
          exact (QuotientGroup.eq_one_iff (N := N) (x := x)).mp hxq
      have hHcop : ¬ p ∣ Nat.card H := by
        -- In Serre's base case `H = N`, so the whole group has order prime to `p`.
        rcases CharP.char_is_prime_or_zero k p with hp | hp0
        · simpa [hN_top] using (hp.coprime_iff_not_dvd.mp hNcop)
        · subst hp0
          simpa using (Nat.card_pos (α := H)).ne'
      -- With `H = N`, the Chapter `17.3` prime-to-`p` lift theorem applies directly.
      rcases
          exists_residueFieldLift_of_non_dvd_card_witness
            (A := A) (p := p) (G' := H) (V' := W) hHcop τ with
        ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA, red, hLift⟩
      exact ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA, red, hLift⟩
  | succ h =>
      -- Route correction: the remaining source-faithful work is only Serre's successor-height
      -- split inside `H / N`. One must choose the normal step `M / N`, handle the `p`-group case
      -- by killing the normal `p`-subgroup action, and handle the prime-to-`p` case by lowering
      -- the ambient quotient height before feeding the result to `hrecLower`.
      obtain ⟨Mbar, hMbar_normal, hMbar_step, hMbar_quot⟩ :=
        exists_quotient_normal_step_of_psolvableHeight_succ
          (p := p) (h := h) (N := N) hquot
      let _ := Mbar
      let _ := hMbar_normal
      let M : Subgroup H := Subgroup.comap (QuotientGroup.mk' N) Mbar
      letI : M.Normal := by infer_instance
      have hMquot : IsPSolvableOfHeight p h (H ⧸ M) := by
        -- First move the quotient-height witness from `((H ⧸ N) ⧸ M̄)` to the literal pullback
        -- subgroup `M ≤ H`; the remaining work is now the genuine Serre branch split on `M / N`.
        change IsPSolvableOfHeight p h (H ⧸ Subgroup.comap (QuotientGroup.mk' N) Mbar)
        simpa [M] using
          IsPSolvableOfHeight.of_equiv
            (quotient_preimage_equiv_of_quotient_normal_step (N := N) Mbar)
            hMbar_quot
      have hMcop_preimage :
          Nat.Coprime p (Nat.card Mbar) →
            Nat.Coprime p (Nat.card M) := by
        -- In the prime-to-`p` branch, Serre's literal subgroup `M` inherits coprime order from
        -- the exact factorization `|M| = |M / N| |N|`.
        intro hMbar_cop
        exact
          coprime_card_preimage_of_quotient_normal_step
            (p := p) (N := N) hNcop Mbar hMbar_cop
      let _ := hMquot
      let _ := hMcop_preimage
      rcases hMbar_step with hMbar_cop | hMp
      · -- In the coprime branch, the literal subgroup `M` already has prime-to-`p` order, so the
        -- same-height recursion hypothesis applies directly to the whole ambient group `H`.
        exact
          exists_residueFieldLift_of_central_cyclic_coprime_kernel_coprime_preimage_branch
            (p := p) (A := A) (h := h) (N := N) hNcop hrecLower τ Mbar hMbar_cop hMquot
      · -- In the `p`-group branch, the only remaining blocker is Serre's explicit
        -- Schur-Zassenhaus complement construction on the literal pullback subgroup `M`.
        exact
          exists_residueFieldLift_of_central_cyclic_coprime_kernel_pgroup_preimage_branch
            (p := p) (A := A) (h := h) hp (N := N)
            hNcentral hNcyclic hNcop hrecLower τ Mbar hMp hMquot

theorem exists_residueFieldLift_of_restriction_isotypic_via_projective_extension
    [IsAlgClosed k]
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (hquot : IsPSolvableOfHeight p h (G ⧸ I))
    (hrecLower :
      ∀ {G' : Type v} [Group G'] [Finite G']
        {V' : Type x} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
        (hG' : IsPSolvableOfHeight p h G')
        (ρ' : Representation k G' V') [ρ'.IsIrreducible],
          ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
            (_ : Module.Free A P) (_ : Module.Finite A P)
            (ρA : Representation A G' P)
            (red : P →ₗ[A] V'),
              IsResidueFieldLift ρ' ρA red)
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (hIsotypic :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      IsIsotypic (MonoidAlgebra k I) V) :
    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
        (ρA : Representation A G P)
        (red : P →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  -- Route correction: this branch must follow Serre's `S̄ ⊗ F` route through the finite central
  -- extension `G₂`; replacing it by an ad hoc recursion would lose the source proof's main
  -- controlling object and the lower-height quotient `H = G₂ / I`.
  -- The verified prefix in this file already handles the two outer recursive branches:
  -- `p`-kernel descent through quotients and the non-isotypic Hall-kernel branch through proper
  -- stabilizers. The only missing frontier is the intrinsic projective-extension package for the
  -- genuinely isotypic Hall-kernel case.
  let ρI : Representation k I V := ρ.comp I.subtype
  letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
  rcases
      exists_irreducible_constituent_with_isotypic_component_top_of_isotypic_restriction
        (p := p) (A := A) (G := G) (V := V) hp I hIcop ρ hIsotypic with
    ⟨Sbar, hSbar_irred, hSbar_top⟩
  letI : Sbar.toRepresentation.IsIrreducible := hSbar_irred
  let F := fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar
  have hCoord :
      ∃ n : ℕ, Nonempty (V ≃ₗ[MonoidAlgebra k I] Fin n → Sbar.asSubmodule) := by
    -- Rigidify Serre's chosen constituent onto a coordinate model before building `G₂`.
    exact
      exists_linearEquiv_pi_of_isotypic_component_top
        (p := p) (A := A) (G := G) (V := V) hp I hIcop ρ Sbar hSbar_irred
        (by simpa using hSbar_top)
  have hLiftSbar :
      ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
        (_ : Module.Free A P) (_ : Module.Finite A P)
        (ρA : Representation A I P)
        (red : P →ₗ[A] Sbar.toSubmodule),
          IsResidueFieldLift Sbar.toRepresentation ρA red := by
    -- Serre's source route lifts the fixed constituent before defining the finite cover `G₂`.
    exact
      exists_residueFieldLift_of_fixed_constituent
        (p := p) (A := A) (G := G) (V := V) hp I hIcop ρ Sbar
  rcases hCoord with ⟨d, eCoord⟩
  rcases hLiftSbar with
    ⟨P_S, hP_S_add, hP_S_mod, hP_S_free, hP_S_finite, ρA_I, red_S, hLiftSbar⟩
  letI : AddCommGroup P_S := hP_S_add
  letI : Module A P_S := hP_S_mod
  letI : Module.Free A P_S := hP_S_free
  letI : Module.Finite A P_S := hP_S_finite
  have hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation) := by
    -- This is the source-faithful `U_s ≠ ∅` step on the fixed literal constituent `S̄`.
    exact
      transported_constituent_equiv_of_isotypic_component_top
        (p := p) (A := A) (G := G) (V := V) hp I hIcop ρ Sbar hSbar_irred
        (by simpa using hSbar_top)
  have hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S) := by
    -- Transport the fixed `A[I]`-lift of `S̄` across the source-faithful equivalence
    -- `S̄ ≃ sS̄`; only the reduction map changes by postcomposition.
    intro s
    exact
      residueFieldLift_of_equiv_target_local
        (A := A) (G := I) (ρA := ρA_I) (red := red_S) hLiftSbar (hTransport s).some
  let pkg :
      ConstituentProjectiveExtensionQuotientData
        (p := p) (A := A) (G := G) (V := V) I ρ Sbar P_S ρA_I red_S :=
    exists_constituent_projective_extension_quotient_data
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport hTransportLift
  letI : Group pkg.G2 := pkg.instGroupG2
  letI : Finite pkg.G2 := pkg.instFiniteG2
  letI : pkg.I2.Normal := pkg.instNormalI2
  letI : pkg.Nbar.Normal := pkg.instNormalNbar
  have hquotPkg : IsPSolvableOfHeight p h ((pkg.G2 ⧸ pkg.I2) ⧸ pkg.Nbar) := by
    -- The quotient in Serre's finite cover is designed to recover the original lower-height
    -- quotient `G / I`.
    exact IsPSolvableOfHeight.of_equiv pkg.quotientEquiv.symm hquot
  letI : pkg.tau.IsIrreducible := pkg.tau_irred
  have hTauLift :
      ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
        (_ : Module.Free A P) (_ : Module.Finite A P)
        (ρA : Representation A (pkg.G2 ⧸ pkg.I2) P)
        (red : P →ₗ[A] F),
          IsResidueFieldLift pkg.tau ρA red := by
    have hrecLowerLarge :
        ∀ {G' : Type (max u v x)} [Group G'] [Finite G']
          {V' : Type x} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
          (hG' : IsPSolvableOfHeight p h G')
          (ρ' : Representation k G' V') [ρ'.IsIrreducible],
            ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
              (_ : Module.Free A P) (_ : Module.Finite A P)
              (ρA : Representation A G' P)
              (red : P →ₗ[A] V'),
                IsResidueFieldLift ρ' ρA red := by
      intro G' _ _ V' _ _ _ hG' ρ' _
      exact exists_residueFieldLift_of_shrink_lower_height hrecLower hG' ρ'
    -- The quotient-side module is now isolated; the remaining recursive content is purely the
    -- lower-height induction across the central cyclic prime-to-`p` kernel.
    exact
      exists_residueFieldLift_of_isIrreducible_of_central_cyclic_coprime_kernel_via_lower_height
        (p := p) (A := A) (h := h) hp (N := pkg.Nbar)
        pkg.hNbar_central pkg.hNbar_cyclic pkg.hNbar_coprime hquotPkg hrecLowerLarge pkg.tau
  rcases hTauLift with ⟨P_tau, hP_tau_add, hP_tau_mod, hP_tau_free, hP_tau_finite, ρA_tau,
      red_tau, hLift_tau⟩
  -- The only remaining source-faithful work is now owned by the fixed-constituent package:
  -- tensor the lifted constituent with this quotient-side lift and descend the prime-to-`p`
  -- kernel upstairs. The main theorem only consumes that packaged assembly.
  exact
    pkg.descendLift hP_tau_add hP_tau_mod hP_tau_free hP_tau_finite ρA_tau red_tau hLift_tau

/-- Helper for Theorem 17-17.6-1: the coprime-kernel branch packages Serre's isotypic
decomposition and projective-extension argument for a normal Hall subgroup. -/
theorem exists_residueFieldLift_of_isIrreducible_of_normal_coprime_kernel
    [IsAlgClosed k]
    (hp : Nat.Prime p)
    (I : Subgroup G) (hI : I.Normal)
    (hIcop : Nat.Coprime p (Nat.card I))
    (hquot : IsPSolvableOfHeight p h (G ⧸ I))
    (hrecSame :
      ∀ {H : Subgroup G} {W : Type x} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
        (hH : H < ⊤)
        (hHG : IsPSolvableOfHeight p (Nat.succ h) H)
        (σ : Representation k H W) [σ.IsIrreducible],
          ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
            (_ : Module.Free A P) (_ : Module.Finite A P)
            (ρA : Representation A H P)
            (red : P →ₗ[A] W),
              IsResidueFieldLift σ ρA red)
    (hrecLower :
      ∀ {G' : Type v} [Group G'] [Finite G']
        {V' : Type x} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
        (hG' : IsPSolvableOfHeight p h G')
        (ρ' : Representation k G' V') [ρ'.IsIrreducible],
          ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
            (_ : Module.Free A P) (_ : Module.Finite A P)
            (ρA : Representation A G' P)
            (red : P →ₗ[A] V'),
              IsResidueFieldLift ρ' ρA red)
    (ρ : Representation k G V) [ρ.IsIrreducible] :
    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A G P)
      (red : P →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  letI : I.Normal := hI
  -- Route correction: the trivial-quotient case is already covered by the Chapter `15` Hall lift.
  -- The only remaining frontier is the genuine proper Hall-kernel case, which needs the
  -- Clifford/stabilizer split and Serre's projective-extension descent.
  by_cases hItop : I = ⊤
  · -- If `I = G`, then `|G|` is itself prime to `p`, so the Chapter `15` lifting theorem applies
    -- directly without any quotient recursion.
    have hGcop : ¬ p ∣ Nat.card G := by
      simpa [hItop] using (hp.coprime_iff_not_dvd.mp hIcop)
    rcases exists_residueFieldLift_of_non_dvd_card_witness (A := A) (p := p) hGcop ρ with
      ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA, red, hLift⟩
    exact ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA, red, hLift⟩
  have hsemisimple :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      IsSemisimpleModule (MonoidAlgebra k I) V :=
    isSemisimpleModule_restrict_of_coprime_card hp I hIcop ρ
  let ρI : Representation k I V := ρ.comp I.subtype
  letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
  by_cases hsub : Subsingleton (isotypicComponents (MonoidAlgebra k I) V)
  · -- If the restricted module has a single isotypic component, we are exactly in Serre's
    -- projective-extension branch.
    have hIsotypic : IsIsotypic (MonoidAlgebra k I) V := by
      exact
        isIsotypic_of_subsingleton_isotypicComponents
          (R := MonoidAlgebra k I) (M := V) hsub
    exact
      exists_residueFieldLift_of_restriction_isotypic_via_projective_extension
        (p := p) (A := A) (h := h) (G := G) (V := V)
        hp I hIcop hquot hrecLower ρ hIsotypic
  · have hsplit :
        (∃ H : Subgroup G,
          I ≤ H ∧ H < ⊤ ∧
            ∃ W : Subrepresentation (ρ.comp H.subtype),
              W.toRepresentation.IsIrreducible ∧ ρ.IsInducedFromSubrepresentation H W) ∨
          (let ρI : Representation k I V := ρ.comp I.subtype
           letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
           IsIsotypic (MonoidAlgebra k I) V) :=
      exists_proper_overgroup_irreducible_induced_or_restriction_isotypic_of_semisimple_restriction
        I ρ hsemisimple
    rcases hsplit with hproper | hIsotypic
    · -- In the non-isotypic branch, recurse on the proper stabilizer overgroup and then induce
      -- the lifted representation back to `G`.
      exact
        exists_residueFieldLift_of_proper_overgroup_induced_hall
          (p := p) (A := A) (h := h) (G := G) (V := V)
          hp I hIcop hquot hrecSame ρ hproper
    · -- In the isotypic branch, Serre's projective-extension construction is the remaining step.
      exact
        exists_residueFieldLift_of_restriction_isotypic_via_projective_extension
          (p := p) (A := A) (h := h) (G := G) (V := V)
          hp I hIcop hquot hrecLower ρ hIsotypic

-- Proof sketch: recurse outermost on the ambient cardinal bound and only then on the height, so
-- the proper-stabilizer Hall branch gets access to same-height recursion on smaller groups while
-- the quotient branch keeps the lower-height recursion.
/-- Helper for Theorem 17-17.6-1: explicit height induction together with a cardinal bound, so the
same-height recursive call is available on proper subgroups. -/
theorem exists_residueFieldLift_of_isIrreducible_of_isPSolvableOfHeight_aux
    [IsAlgClosed k]
    (hp : Nat.Prime p) :
    ∀ {h' n : ℕ} {G' : Type v} [Group G'] [Finite G']
      {V' : Type x} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
      (hG' : IsPSolvableOfHeight p h' G') (hcard : Nat.card G' ≤ n)
      (ρ : Representation k G' V') [ρ.IsIrreducible],
        ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A G' P)
      (red : P →ₗ[A] V'),
            IsResidueFieldLift ρ ρA red := by
  intro h'
  induction h' with
  | zero =>
      intro n G' _ _ V' _ _ _ hG' hcard ρ _
      letI : Fact p.Prime := ⟨hp⟩
      letI : Subsingleton G' := hG'
      letI : Unique G' := { default := 1, uniq := fun g ↦ Subsingleton.elim g 1 }
      -- At height `0` the group is trivial, so the prime-to-`p` lifting theorem applies
      -- directly to the whole group.
      have hcardG' : Nat.card G' = 1 := by
        exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
      have hGcop : ¬ p ∣ Nat.card G' := by
        simpa [hcardG'] using hp.not_dvd_one
      rcases exists_residueFieldLift_of_non_dvd_card_witness (A := A) (p := p) hGcop ρ with
        ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA, red, hLift⟩
      exact ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA, red, hLift⟩
  | succ h ihh =>
      intro n
      induction n with
      | zero =>
          intro G' _ _ V' _ _ _ hG' hcard ρ _
          have hfalse : False := (Nat.not_lt_of_ge hcard) Nat.card_pos
          exact False.elim hfalse
      | succ n ihn =>
          intro G' _ _ V' _ _ _ hG' hcard ρ _
          letI : Fact p.Prime := ⟨hp⟩
          rcases (IsPSolvableOfHeight.succ_iff.mp hG') with ⟨I, hI, hstep, hquot⟩
          rcases hstep with hIcop | hIp
          · letI : I.Normal := hI
            -- Route correction: the proper-subgroup branch still descends on cardinality, but
            -- the lower-height branch now comes directly from the outer height induction with no
            -- ambient cardinal bound.
            have hrecSame :
                ∀ {H : Subgroup G'} {W : Type x} [AddCommGroup W] [Module k W]
                  [FiniteDimensional k W]
                  (hH : H < ⊤)
                  (hHG : IsPSolvableOfHeight p (Nat.succ h) H)
                  (σ : Representation k H W) [σ.IsIrreducible],
                    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
                      (_ : Module.Free A P) (_ : Module.Finite A P)
                      (ρA : Representation A H P)
                      (red : P →ₗ[A] W),
                        IsResidueFieldLift σ ρA red := by
              intro H W _ _ _ hH hHG σ _
              have hcardH : Nat.card H ≤ n := by
                exact
                  Nat.lt_succ_iff.mp <|
                    lt_of_lt_of_le (subgroup_natCard_lt_of_ne_top_c1731 H hH.ne) hcard
              rcases ihn hHG hcardH σ with
                ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA, red, hLift⟩
              exact ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA, red, hLift⟩
            have hrecLower :
                ∀ {G'' : Type v} [Group G''] [Finite G'']
                  {W : Type x} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
                  (hG'' : IsPSolvableOfHeight p h G'')
                  (σ : Representation k G'' W) [σ.IsIrreducible],
                    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
                      (_ : Module.Free A P) (_ : Module.Finite A P)
                      (ρA : Representation A G'' P)
                      (red : P →ₗ[A] W),
                        IsResidueFieldLift σ ρA red := by
              intro G'' _ _ W _ _ _ hG'' σ _
              exact
                @ihh (Nat.card G'') G'' _ _ W _ _ _ hG''
                  (le_rfl : Nat.card G'' ≤ Nat.card G'') σ inferInstance
            exact
              exists_residueFieldLift_of_isIrreducible_of_normal_coprime_kernel
                hp I hI hIcop hquot hrecSame hrecLower ρ
          · letI : I.Normal := hI
            letI : Representation.IsTrivial (ρ.comp I.subtype) :=
              isTrivial_restrict_normal_pSubgroup_of_isIrreducible ρ I hIp
            let τ : Representation k (G' ⧸ I) V' := ρ.ofQuotient I
            letI : τ.IsIrreducible := isIrreducible_of_ofQuotient_of_isTrivial_c17 ρ I
            -- Descend through the trivial `p`-kernel, recurse on the strictly lower height
            -- quotient with its own cardinal bound, then inflate back to `G'`.
            exact
              exists_residueFieldLift_of_ofQuotient_of_isTrivial_witness
                (A := A) (ρ := ρ) (I := I)
                (@ihh (Nat.card (G' ⧸ I)) (G' ⧸ I) _ _ V' _ _ _
                  hquot (le_rfl : Nat.card (G' ⧸ I) ≤ Nat.card (G' ⧸ I)) τ inferInstance)

/-- The height-indexed inductive form of Theorem `17-17.6-1`, phrased on the primitive recursive
`p`-solvable data. -/
theorem exists_residueFieldLift_of_isIrreducible_of_isPSolvableOfHeight
    [IsAlgClosed k]
    (hp : Nat.Prime p) (hG : IsPSolvableOfHeight p h G) (ρ : Representation k G V)
    [ρ.IsIrreducible] :
    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A G P)
      (red : P →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  -- Specialize the explicit `(height, card)` recursion at the actual ambient group order.
  exact
    exists_residueFieldLift_of_isIrreducible_of_isPSolvableOfHeight_aux
      (A := A) (p := p) (h' := h) (G' := G) (V' := V)
      hp hG (le_rfl : Nat.card G ≤ Nat.card G) ρ

end

end Representation
