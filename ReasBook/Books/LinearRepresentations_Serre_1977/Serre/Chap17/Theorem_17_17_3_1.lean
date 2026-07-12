import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CharacterFieldTransportLift
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.SameUniverseInductionPackaging
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.InducedCoinvariantsScalarExtension

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Representation

open scoped Representation

section

variable {A : Type u} [CommRing A] [HenselianLocalRing A]
variable {G : Type v} [Group G] [Finite G]
variable {p : ℕ}

variable [CharP (IsLocalRing.ResidueField A) p]
variable {V : Type w} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]
variable [FiniteDimensional (IsLocalRing.ResidueField A) V]
variable {C P : Subgroup G}

local notation "k" => IsLocalRing.ResidueField A
noncomputable local instance theorem1731MainResidueFieldModule
    {W : Type*} [AddCommGroup W] [Module k W] : Module A W :=
  Module.compHom W (algebraMap A k)
local instance theorem1731MainResidueFieldIsScalarTower
    {W : Type*} [AddCommGroup W] [Module k W] : IsScalarTower A k W :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.3-1: if the restriction to `C` is isotypic, Serre's multiplicity
space argument produces the desired residue-field lift. -/
lemma exists_residueFieldLift_of_restriction_isotypic
    (hp : Nat.Prime p) (hC : C.Normal) (hCP : C.IsComplement' P) (hCyclic : IsCyclic C)
    (hCoprime : Nat.Coprime p (Nat.card C)) (hP : IsPGroup p P)
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (hIso :
      let ρC : Representation k C V := ρ.comp C.subtype
      letI : Module (MonoidAlgebra k C) V := ρC.instModuleMonoidAlgebraAsModule
      IsIsotypic (MonoidAlgebra k C) V) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module A W)
      (_ : Module.Free A W) (_ : Module.Finite A W)
      (ρA : Representation A G W)
      (red : W →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Nontrivial V := nontrivial_of_isIrreducible_local_c17 (ρ := ρ)
  let ρP : Representation k P V := ρ.comp P.subtype
  have hCndvd : ¬ p ∣ Nat.card C := hp.coprime_iff_not_dvd.mp hCoprime
  have hPinv : ρP.invariants ≠ ⊥ := by
    -- Serre's first checkpoint in the isotypic branch is the existence of a nonzero `P`-fixed
    -- vector in characteristic `p`.
    exact invariants_ne_bot_of_isPGroup_charP (ρ := ρP) hP
  obtain ⟨ν, hνinv, hν0⟩ := ρP.invariants.ne_bot_iff.mp hPinv
  have hνfixed : ∀ s : P, ρP s ν = ν := by
    -- Unpack membership in the invariant subspace as the fixed-vector relation.
    exact (ρP.mem_invariants ν).mp hνinv
  have hOrbitSpan :
      Submodule.span k (Set.range fun c : C ↦ ρ c ν) = ⊤ := by
    -- Serre's orbit-span checkpoint is now closed: the `C`-orbit of the nonzero `P`-fixed vector
    -- spans a nonzero `G`-stable subrepresentation, hence all of `V` by irreducibility.
    exact
      c_orbit_span_eq_top_of_fixed_vector
        (ρ := ρ) hC hCP ν hν0 hνfixed
  have hLiftC :
      ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module A W)
        (_ : Module.Free A W) (_ : Module.Finite A W)
        (ρA_C : Representation A C W)
        (red_C : W →ₗ[A] V),
          IsResidueFieldLift (ρ.comp C.subtype) ρA_C red_C := by
    -- Chapter `15` already lifts the restricted `C`-representation because `|C|` is prime to `p`.
    exact
      exists_residueFieldLift_of_non_dvd_card
        (A := A) (H := C) (V := V) (p := p) hCndvd (ρ.comp C.subtype)
  -- Route correction: the fixed-vector and orbit-span part of Serre's argument is now completed
  -- here. The only remaining blocker is the character-field transport from the chosen `C`-lift to
  -- an ambient `G`-lift.
  exact
    exists_residueFieldLift_of_character_field_transport
      (A := A) (G := G) (V := V) (C := C) (P := P) ρ hC hCP hCndvd hCyclic hIso ν hν0
      hνfixed hOrbitSpan hLiftC

/-- Helper for Theorem 17-17.3-1: a lifted `H`-subrepresentation can be induced and repackaged on
the same-universe standard induced model without changing the resulting residue-field reduction. -/
theorem induced_standard_model_residueFieldLift_exists_via_same_universe
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    ∃ (W' : Type u) (_ : AddCommGroup W') (_ : Module A W')
      (_ : Module.Free A W') (_ : Module.Finite A W')
      (ρA_ind : Representation A G W')
      (red_ind : W' →ₗ[A] Representation.IndV H.subtype W.toRepresentation),
        IsResidueFieldLift (Representation.ind H.subtype W.toRepresentation) ρA_ind red_ind := by
  let ρA_HU := uliftRepresentation_witness_local (A := A) ρA_H
  let red_HU :=
    red_H.comp
      (ULift.moduleEquiv : ULift.{max (max u v) w} W0 ≃ₗ[A] W0).toLinearMap
  let hLiftHU :=
    residueFieldLift_ulift_witness_local
      (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
  let fHU :=
    induced_subrepresentation_lift_unit_intertwining_local
      (A := A) (G := G) (ρ := ρ) W ρA_HU red_HU hLiftHU
  let red_u :
      Representation.IndV H.subtype ρA_HU →ₗ[A] Representation.IndV H.subtype W.toRepresentation :=
    (((Rep.indResHomEquiv
        H.subtype (Rep.of ρA_HU)
        (Rep.of ((Representation.ind H.subtype W.toRepresentation).restrictScalars A))).symm
      (Rep.ofHom fHU)).hom)
  have hred_u :
      ∀ g : G, ∀ xU : ULift.{max (max u v) w} W0,
        red_u (Representation.IndV.mk H.subtype ρA_HU g xU) =
          Representation.IndV.mk H.subtype W.toRepresentation g (red_HU xU) := by
    intro g xU
    simpa [ρA_HU, red_HU, hLiftHU, fHU, red_u] using
      induced_subrepresentation_lift_ulift_source_apply_mk_local
        (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH g xU
  have hBase_u : IsBaseChange k red_u := by
    exact
      induced_subrepresentation_lift_ulift_source_isBaseChange_local
        (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH red_u hred_u
  have hInter_u :
      (Representation.ind H.subtype ρA_HU).IsIntertwiningMap
        ((Representation.ind H.subtype W.toRepresentation).restrictScalars A)
        red_u := by
    simpa [ρA_HU, red_HU, hLiftHU, fHU, red_u] using
      induced_subrepresentation_lift_ulift_source_isIntertwining_local
        (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
  let eU : ρA_HU.Equiv ρA_H :=
    Representation.Equiv.mk ULift.moduleEquiv fun h ↦ by
      ext y
      rfl
  let eInd_native :
      (Representation.ind H.subtype ρA_HU).Equiv
        (Representation.ind H.subtype ρA_H) :=
    ind_equiv_of_source_equiv_over_local (R := A) H.subtype eU
  let red_native :
      Representation.IndV H.subtype ρA_H →ₗ[A] Representation.IndV H.subtype W.toRepresentation :=
    red_u.comp eInd_native.symm.toLinearMap
  have hred_native :
      RawIsResidueFieldReduction_local
        (A := A)
        (Representation.ind H.subtype W.toRepresentation)
        (Representation.ind H.subtype ρA_H)
        red_native := by
    simpa [red_native] using
      residueFieldReduction_of_equiv_source_local
        (A := A)
        (ρ := Representation.ind H.subtype W.toRepresentation)
        hBase_u hInter_u eInd_native.symm
  have hBase_native : IsBaseChange k red_native := by
    simpa [RawIsResidueFieldReduction_local] using hred_native.1
  have hInter_native :
      (Representation.ind H.subtype ρA_H).IsIntertwiningMap
        ((Representation.ind H.subtype W.toRepresentation).restrictScalars A)
        red_native := by
    refine Representation.IsIntertwiningMap.mk ?_
    intro g x
    have heq :
        eInd_native.symm ((Representation.ind H.subtype ρA_H) g x) =
          (Representation.ind H.subtype ρA_HU) g (eInd_native.symm x) := by
      simpa using LinearMap.congr_fun (eInd_native.symm.isIntertwining' g) x
    calc
      red_native ((Representation.ind H.subtype ρA_H) g x) =
          red_u ((Representation.ind H.subtype ρA_HU) g (eInd_native.symm x)) := by
            simpa [red_native, LinearMap.comp_apply] using congrArg red_u heq
      _ =
          ((Representation.ind H.subtype W.toRepresentation).restrictScalars A) g
            (red_u (eInd_native.symm x)) := by
              simpa [Representation.restrictScalars_apply] using
                hInter_u.isIntertwining g (eInd_native.symm x)
      _ =
          ((Representation.ind H.subtype W.toRepresentation).restrictScalars A) g
            (red_native x) := by
              simp [red_native, LinearMap.comp_apply]
  obtain ⟨W', hW'add, hW'mod, hW'free, hW'finite, ρA_ind, hEquiv⟩ :=
    exists_same_universe_finite_free_induced_model_local
      (A := A) (G := G) (H := H) ρA_H
  letI : AddCommGroup W' := hW'add
  letI : Module A W' := hW'mod
  letI : Module.Free A W' := hW'free
  letI : Module.Finite A W' := hW'finite
  rcases hEquiv with ⟨ePack⟩
  let red_ind : W' →ₗ[A] Representation.IndV H.subtype W.toRepresentation :=
    red_native.comp ePack.toLinearMap
  have hred_ind :
      RawIsResidueFieldReduction_local
        (A := A)
        (Representation.ind H.subtype W.toRepresentation)
        ρA_ind
        red_ind := by
    simpa [red_ind] using
      residueFieldReduction_of_equiv_source_local
        (A := A)
        (ρ := Representation.ind H.subtype W.toRepresentation)
        (ρA' := ρA_ind)
        (ρA := Representation.ind H.subtype ρA_H)
        (red := red_native)
        hBase_native hInter_native ePack
  refine ⟨W', hW'add, hW'mod, hW'free, hW'finite, ρA_ind, red_ind, ?_⟩
  simpa [IsResidueFieldLift, RawIsResidueFieldReduction_local] using hred_ind

/-- Helper for Theorem 17-17.3-1: once the recursive lift exists on the inducing
subrepresentation, the final proper-overgroup step is the explicit Chapter `7` transport from the
standard induced model back to the ambient representation. -/
lemma exists_residueFieldLift_of_isInducedFromSubrepresentation_via_same_universe
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H)
    (hInd : ρ.IsInducedFromSubrepresentation H W) :
    ∃ (W' : Type u) (_ : AddCommGroup W') (_ : Module A W')
      (_ : Module.Free A W') (_ : Module.Finite A W')
      (ρA : Representation A G W')
      (red : W' →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  obtain ⟨W', hW'add, hW'mod, hW'free, hW'finite, ρA_ind, red_ind, hLiftInd⟩ :=
    induced_standard_model_residueFieldLift_exists_via_same_universe
      (A := A) (G := G) (V := V) ρ W ρA_H red_H hLiftH
  letI : AddCommGroup W' := hW'add
  letI : Module A W' := hW'mod
  letI : Module.Free A W' := hW'free
  letI : Module.Finite A W' := hW'finite
  let ρU : Representation k G (ULift.{max (max u v) w, w} V) :=
    { toFun := fun g =>
        { toFun := fun x ↦ ⟨ρ g x.down⟩
          map_add' := by
            intro x y
            ext
            simp
          map_smul' := by
            intro a x
            ext
            simp }
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro g h
        ext x
        simp [map_mul] }
  let eU : ρ.Equiv ρU :=
    Representation.Equiv.mk
      (ULift.moduleEquiv.symm : V ≃ₗ[k] ULift.{max (max u v) w, w} V) fun g ↦ by
        ext x
        rfl
  let WU : Subrepresentation (ρU.comp H.subtype) :=
    transported_subrepresentation_of_equiv_local_c17
      (comp_subtype_equiv_local_c17 eU H) W
  have hIndU :
      ρU.IsInducedFromSubrepresentation H WU := by
    simpa [WU] using
      (isInducedFromSubrepresentation_of_equiv_local_c17
        (ρ₁ := ρ) (ρ₂ := ρU) eU H W hInd)
  let eW : W.toRepresentation.Equiv WU.toRepresentation := by
    simpa [WU, transported_subrepresentation_of_equiv_local_c17, subrepresentationOrderIso_local_c17] using
      (subrepresentation_equiv_of_equiv_image_local_c17
        (comp_subtype_equiv_local_c17 eU H) W)
  let eIndU :
      (Representation.ind H.subtype WU.toRepresentation).Equiv ρU :=
    inducedFromSubrepresentation_explicit_equiv
      (ρ := ρU) (W := WU) hIndU
  let eSource :
      (Representation.ind H.subtype W.toRepresentation).Equiv
        (Representation.ind H.subtype WU.toRepresentation) :=
    ind_equiv_of_source_equiv_local_c17 H.subtype eW
  let eInd :
      (Representation.ind H.subtype W.toRepresentation).Equiv ρ :=
    (eSource.trans eIndU).trans eU.symm
  refine
    ⟨W', hW'add, hW'mod, hW'free, hW'finite, ρA_ind,
      (eInd.toLinearMap.restrictScalars A).comp red_ind, ?_⟩
  exact
    residueFieldLift_of_equiv_target
      (A := A) (G := G) (V := V) hLiftInd eInd

/-- Helper for Theorem 17-17.3-1: in the non-isotypic branch, recurse on the proper overgroup
containing `C` and then induce the lifted module back to the ambient representation. -/
lemma exists_residueFieldLift_of_proper_overgroup_induced_via_same_universe
    (hC : C.Normal) (hCP : C.IsComplement' P) (hCyclic : IsCyclic C)
    (hCoprime : Nat.Coprime p (Nat.card C)) (hP : IsPGroup p P)
    (hrecSame :
      ∀ {H : Subgroup G} {W0 : Type w} [AddCommGroup W0] [Module k W0]
        [FiniteDimensional k W0]
        {C0 P0 : Subgroup H}
        (_hH : H < ⊤)
        (_hC0 : C0.Normal) (_hC0P0 : C0.IsComplement' P0) (_hC0cyc : IsCyclic C0)
        (_hC0cop : Nat.Coprime p (Nat.card C0)) (_hP0 : IsPGroup p P0)
        (σ : Representation k H W0) [σ.IsIrreducible],
          ∃ (W' : Type u) (_ : AddCommGroup W') (_ : Module A W')
            (_ : Module.Free A W') (_ : Module.Finite A W')
            (ρA_H : Representation A H W')
            (red_H : W' →ₗ[A] W0),
              IsResidueFieldLift σ ρA_H red_H)
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (hproper :
      ∃ H : Subgroup G,
        C ≤ H ∧ H < ⊤ ∧
          ∃ W : Subrepresentation (ρ.comp H.subtype),
            W.toRepresentation.IsIrreducible ∧ ρ.IsInducedFromSubrepresentation H W) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module A W)
      (_ : Module.Free A W) (_ : Module.Finite A W)
      (ρA : Representation A G W)
      (red : W →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  rcases hproper with ⟨H, hCH, hHlt, W, hWirred, hInd⟩
  let C0 : Subgroup H := C.subgroupOf H
  let P0 : Subgroup H := (H ⊓ P).subgroupOf H
  have hHdecomp :
      C0.Normal ∧ C0.IsComplement' P0 ∧ IsCyclic C0 ∧ Nat.Coprime p (Nat.card C0) ∧ IsPGroup p P0 :=
    subgroup_cyclicNormalByPGroupDecomposition_of_le
      (p := p) (C := C) (P := P) hCH hC hCP hCyclic hCoprime hP
  rcases hHdecomp with ⟨hC0, hC0P0, hC0cyc, hC0cop, hP0⟩
  letI : W.toRepresentation.IsIrreducible := hWirred
  have hLiftH :
      ∃ (W0 : Type u) (_ : AddCommGroup W0) (_ : Module A W0)
        (_ : Module.Free A W0) (_ : Module.Finite A W0)
        (ρA_H : Representation A H W0)
        (red_H : W0 →ₗ[A] W.toSubmodule),
          IsResidueFieldLift W.toRepresentation ρA_H red_H := by
    exact hrecSame hHlt hC0 hC0P0 hC0cyc hC0cop hP0 W.toRepresentation
  rcases hLiftH with ⟨W0, hW0add, hW0mod, hW0free, hW0finite, ρA_H, red_H, hLiftH⟩
  letI : AddCommGroup W0 := hW0add
  letI : Module A W0 := hW0mod
  letI : Module.Free A W0 := hW0free
  letI : Module.Finite A W0 := hW0finite
  exact
    exists_residueFieldLift_of_isInducedFromSubrepresentation_via_same_universe
      (A := A) (G := G) (V := V) ρ W ρA_H red_H hLiftH hInd

/-- Helper for Theorem 17-17.3-1: explicit cardinal induction isolates the proper-overgroup
recursion from the genuinely new induced-transport and isotypic-model blockers. -/
theorem exists_residueFieldLift_of_isIrreducible_of_cyclicNormalByPGroupDecomposition_of_prime_aux
    (hp : Nat.Prime p) :
    ∀ {n : ℕ} {G' : Type v} [Group G'] [Finite G']
      {V' : Type w} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
      {C' P' : Subgroup G'}
      (_hcard : Nat.card G' ≤ n)
      (_hC' : C'.Normal) (_hC'P' : C'.IsComplement' P') (_hCyclic' : IsCyclic C')
      (_hCoprime' : Nat.Coprime p (Nat.card C')) (_hP' : IsPGroup p P')
      (ρ' : Representation k G' V') [ρ'.IsIrreducible],
        ∃ (W' : Type u) (_ : AddCommGroup W') (_ : Module A W')
          (_ : Module.Free A W') (_ : Module.Finite A W')
          (ρA' : Representation A G' W')
          (red' : W' →ₗ[A] V'),
            IsResidueFieldLift ρ' ρA' red' := by
  intro n
  induction n with
  | zero =>
      intro G' _ _ V' _ _ _ C' P' hcard hC' hC'P' hCyclic' hCoprime' hP' ρ' _
      have hfalse : False := (Nat.not_lt_of_ge hcard) Nat.card_pos
      exact False.elim hfalse
  | succ n ihn =>
      intro G' _ _ V' _ _ _ C' P' hcard hC' hC'P' hCyclic' hCoprime' hP' ρ' _
      have hsemi :
          let ρC' : Representation k C' V' := ρ'.comp C'.subtype
          letI : Module (MonoidAlgebra k C') V' := ρC'.instModuleMonoidAlgebraAsModule
          IsSemisimpleModule (MonoidAlgebra k C') V' :=
        isSemisimpleModule_asModule_of_coprime_card
          (A := A) (G := G') (p := p) (V := V') (H := C') hp hCoprime' (ρ'.comp C'.subtype)
      have hrecSame :
          ∀ {H : Subgroup G'} {W0 : Type w} [AddCommGroup W0] [Module k W0]
            [FiniteDimensional k W0]
            {C0 P0 : Subgroup H}
            (hH : H < ⊤)
            (hC0 : C0.Normal) (hC0P0 : C0.IsComplement' P0) (hC0cyc : IsCyclic C0)
            (hC0cop : Nat.Coprime p (Nat.card C0)) (hP0 : IsPGroup p P0)
            (σ : Representation k H W0) [σ.IsIrreducible],
              ∃ (W' : Type u) (_ : AddCommGroup W') (_ : Module A W')
                (_ : Module.Free A W') (_ : Module.Finite A W')
                (ρA' : Representation A H W')
                (red' : W' →ₗ[A] W0),
                  IsResidueFieldLift σ ρA' red' := by
        intro H W0 _ _ _ C0 P0 hH hC0 hC0P0 hC0cyc hC0cop hP0 σ _
        exact
          exists_residueFieldLift_of_isIrreducible_of_cyclicNormalByPGroupDecomposition_of_prime_of_proper_subgroup
            (A := A) (G := G') (p := p) (n := n)
            (hrec := by
              intro G'' _ _ V'' _ _ _ C'' P'' hC'' hC''P'' hCyclic'' hCoprime'' hP'' hcard'' ρ'' _
              exact ihn hcard'' hC'' hC''P'' hCyclic'' hCoprime'' hP'' ρ'')
            H hH hC0 hC0P0 hC0cyc hC0cop hP0 σ hcard
      have hsplit :
          (∃ H : Subgroup G',
            C' ≤ H ∧ H < ⊤ ∧
              ∃ W : Subrepresentation (ρ'.comp H.subtype),
                W.toRepresentation.IsIrreducible ∧ ρ'.IsInducedFromSubrepresentation H W) ∨
            (let ρC' : Representation k C' V' := ρ'.comp C'.subtype
             letI : Module (MonoidAlgebra k C') V' := ρC'.instModuleMonoidAlgebraAsModule
             IsIsotypic (MonoidAlgebra k C') V') :=
        exists_proper_overgroup_irreducible_induced_or_restriction_isotypic_of_semisimple_restrict
          (A := A) (G := G') (C := C') hC' ρ' hsemi
      rcases hsplit with hproper | hIso
      · -- In the non-isotypic branch, recurse on the proper overgroup and induce back to `G'`.
        exact
          exists_residueFieldLift_of_proper_overgroup_induced_via_same_universe
            (A := A) (G := G') (p := p) (V := V') (C := C') (P := P')
            hC' hC'P' hCyclic' hCoprime' hP' hrecSame ρ' hproper
      · -- In the isotypic branch, the remaining work is exactly the character-field transport.
        exact
          exists_residueFieldLift_of_restriction_isotypic
            (A := A) (G := G') (p := p) (V := V') (C := C') (P := P')
            hp hC' hC'P' hCyclic' hCoprime' hP' ρ' hIso

/-- Helper for Theorem 17-17.3-1: after ruling out the degenerate `p = 0` case, the cyclic
normal-by-`p` hypotheses reduce the lifting problem to the prime-characteristic Clifford/stabilizer
argument on a `p`-solvable group. -/
lemma exists_residueFieldLift_of_isIrreducible_of_cyclicNormalByPGroupDecomposition_of_prime
    (hp : Nat.Prime p) (hC : C.Normal) (hCP : C.IsComplement' P) (hCyclic : IsCyclic C)
    (hCoprime : Nat.Coprime p (Nat.card C)) (hP : IsPGroup p P)
    (ρ : Representation k G V) [ρ.IsIrreducible] :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module A W)
      (_ : Module.Free A W) (_ : Module.Finite A W)
      (ρA : Representation A G W)
      (red : W →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  -- Specialize the explicit cardinal recursion at the actual order of `G`.
  exact
    exists_residueFieldLift_of_isIrreducible_of_cyclicNormalByPGroupDecomposition_of_prime_aux
      (A := A) (G' := G) (p := p) (V' := V) (n := Nat.card G)
      hp (le_rfl : Nat.card G ≤ Nat.card G) hC hCP hCyclic hCoprime hP ρ

/-- Theorem 17-17.3-1: let `k = IsLocalRing.ResidueField A` have characteristic `p`, with `A`
henselian local. If `G` is the semidirect product of a `p`-group complement `P` by a cyclic
normal subgroup `C` of order prime to `p`, then every finite-dimensional irreducible
representation of `G` over `k` admits a free finitely generated lift over `A`. Equivalently,
every simple finite-dimensional `k[G]`-module lifts to a free finitely generated `A[G]`-module. -/
theorem exists_residueFieldLift_of_isIrreducible_of_cyclicNormalByPGroupDecomposition
    (hC : C.Normal) (hCP : C.IsComplement' P) (hCyclic : IsCyclic C)
    (hCoprime : Nat.Coprime p (Nat.card C)) (hP : IsPGroup p P)
    (ρ : Representation k G V) [ρ.IsIrreducible] :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module A W)
      (_ : Module.Free A W) (_ : Module.Finite A W)
      (ρA : Representation A G W)
      (red : W →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  rcases CharP.char_is_prime_or_zero k p with hp | hp0
  · exact
      exists_residueFieldLift_of_isIrreducible_of_cyclicNormalByPGroupDecomposition_of_prime
        (A := A) (G := G) (p := p) (V := V)
        hp hC hCP hCyclic hCoprime hP ρ
  · exact
      exists_residueFieldLift_of_isIrreducible_of_cyclicNormalByPGroupDecomposition_of_charZero
        (A := A) (G := G) (p := p) (V := V) hp0 ρ

end

end Representation
