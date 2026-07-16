import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_6_1.FixedConstituentRootLifting

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

/-- Helper for Theorem 17-17.6-1: Serre's determinant subgroup is finite because it is the
range of the determinant character of the finite Hall-kernel action. -/
instance fixed_constituent_determinant_subgroup_finite
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    Finite (fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I) := by
  let f := fixed_constituent_action_det_hom (A := A) (G := G) (I := I) ρA_I
  rw [fixed_constituent_determinant_subgroup_eq_range
    (A := A) (G := G) (I := I) (ρA_I := ρA_I)]
  exact
    Finite.of_surjective
      (fun x : I => (⟨f x, ⟨x, rfl⟩⟩ : f.range))
      (by
        rintro ⟨_, x, rfl⟩
        exact ⟨x, rfl⟩)

/-- Helper for Theorem 17-17.6-1: reindexing a transport fiber along an equality of group
indices leaves the determinant unchanged. -/
@[simp] theorem fixed_constituent_transport_fiber_det_reindex_eq
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    {s t : G} (hst : s = t)
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s) :
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_fiber_reindex
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) hst u) =
      fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) u := by
  cases hst
  rfl

/-- Helper for Theorem 17-17.6-1: each chosen section determinant class already lies in the
explicit candidate subgroup that precedes the final cyclicity/prime-to-`p` normalization. -/
theorem fixed_constituent_section_determinant_class_mem_candidate
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
    fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s ∈
      fixed_constituent_projective_extension_candidate_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift := by
  -- The section classes are built in as generators of the candidate subgroup.
  exact Subgroup.subset_closure (Or.inl ⟨s, rfl⟩)

/-- Helper for Theorem 17-17.6-1: the residue-field image of every element of Serre's determinant
subgroup `C` already lies in the same explicit candidate subgroup. This isolates the remaining
work to proving that the generated subgroup has the expected finite cyclic prime-to-`p` shape. -/
theorem fixed_constituent_determinant_subgroup_residue_class_mem_candidate
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
    (c : fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I) :
    fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I c ∈
      fixed_constituent_projective_extension_candidate_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift := by
  -- The determinant subgroup image is the second generator family of the candidate subgroup.
  exact Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)

/-- Helper for Theorem 17-17.6-1: each chosen section determinant class is torsion in the
residue-field quotient, because its `|G|`-th power is already trivial modulo `d`-th powers. -/
theorem fixed_constituent_section_determinant_class_isOfFinOrder
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
    (s : G) :
    IsOfFinOrder
      (fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s) := by
  -- Repackage the already proved quotient-power identity as finite order of the section class.
  refine isOfFinOrder_iff_pow_eq_one.mpr ?_
  refine ⟨Nat.card G, Nat.card_pos, ?_⟩
  simpa using
    section_determinant_class_pow_card_eq_one_mod_dth_powers
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
      (fixed_constituent_transport_kernel_eq_unit_smul_id_of_endomorphism_scalar
        (A := A) (G := G) (I := I) ρA_I
        (fun f ↦
          fixed_constituent_lift_equivariant_endomorphism_scalar
            (A := A) (G := G) (V := V) hp I hIcop (ρ := ρ) (Sbar := Sbar)
            hSbar_irred
            ρA_I red_S hLiftSbar f))
      s

/-- Helper for Theorem 17-17.6-1: every residue-field image of the determinant subgroup `C`
remains torsion after passing to the quotient modulo `d`-th powers. -/
theorem fixed_constituent_determinant_subgroup_residue_class_isOfFinOrder
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (c : fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I) :
    IsOfFinOrder
      (fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I c) := by
  -- The quotient class inherits the finite order of its source element in the finite subgroup `C`.
  refine isOfFinOrder_iff_pow_eq_one.mpr ?_
  refine ⟨Nat.card (fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I),
    Nat.card_pos, ?_⟩
  let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
  let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
  have hc_sub : c ^ Nat.card C = 1 := by
    simpa [C] using (pow_card_eq_one' (x := c))
  have hc_pow : (c : Aˣ) ^ Nat.card C = 1 := by
    exact
      congrArg
        (fun y : fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I =>
          (y : Aˣ))
        hc_sub
  have hres_pow :
      (Units.map (IsLocalRing.residue A).toMonoidHom (c : Aˣ)) ^ Nat.card C = 1 := by
    simpa using congrArg (Units.map (IsLocalRing.residue A).toMonoidHom) hc_pow
  have hclass_one :
      QuotientGroup.mk' Qd
        ((Units.map (IsLocalRing.residue A).toMonoidHom (c : Aˣ)) ^ Nat.card C) =
        1 := by
    rw [hres_pow]
    simp
  simpa [fixed_constituent_determinant_subgroup_residue_class, C, Qd, map_pow] using hclass_one

/-- Helper for Theorem 17-17.6-1: every explicit generator coming from Serre's determinant
subgroup `C` is already represented by an actual `(card C)`-th root of unity in the residue
field, not merely by an abstract torsion quotient class. -/
theorem determinant_subgroup_residue_class_mem_card_rootsOfUnity_image
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (c : fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I) :
    let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
    let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
    fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I c ∈
      (rootsOfUnity (Nat.card C) k).map (QuotientGroup.mk' Qd) := by
  let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
  let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
  let ζ : kˣ := Units.map (IsLocalRing.residue A).toMonoidHom c
  have hc_sub : c ^ Nat.card C = 1 := by
    simpa [C] using (pow_card_eq_one' (x := c))
  have hc_pow : (c : Aˣ) ^ Nat.card C = 1 := by
    exact
      congrArg
        (fun y : fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I =>
          (y : Aˣ))
        hc_sub
  have hpow : ζ ^ Nat.card C = 1 := by
    -- The determinant subgroup is finite, so each of its residue images is killed by `|C|`.
    simpa [ζ] using congrArg (Units.map (IsLocalRing.residue A).toMonoidHom) hc_pow
  have hpow_val : (ζ : k) ^ Nat.card C = 1 := by
    simpa using congrArg (fun y : kˣ => (y : k)) hpow
  letI : NeZero (Nat.card C) := NeZero.of_gt Nat.card_pos
  let ξ : rootsOfUnity (Nat.card C) k := rootsOfUnity.mkOfPowEq (ζ : k) hpow_val
  refine ⟨(ξ : kˣ), ?_, ?_⟩
  · exact ξ.property
  -- Route correction: package the source element of `C` itself as the required roots-of-unity
  -- representative before mapping into the quotient modulo `d`-th powers.
  change QuotientGroup.mk' Qd (((ξ : rootsOfUnity (Nat.card C) k) : kˣ)) =
      QuotientGroup.mk' Qd (Units.map (IsLocalRing.residue A).toMonoidHom c)
  congr 1
  apply Units.ext
  simpa [ξ, ζ]

/-- Helper for Theorem 17-17.6-1: the same determinant-subgroup generator family already lands in
the common `lcm`-bounded roots-of-unity subgroup that will later host Serre's full candidate
subgroup `N̄`. -/
theorem determinant_subgroup_residue_class_mem_lcm_rootsOfUnity_image
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (c : fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I) :
    let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
    let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
    fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I c ∈
      (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map (QuotientGroup.mk' Qd) := by
  let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
  let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
  have hbase :
      fixed_constituent_determinant_subgroup_residue_class
          (A := A) (G := G) (I := I) ρA_I c ∈
        (rootsOfUnity (Nat.card C) k).map (QuotientGroup.mk' Qd) := by
    simpa [C, Qd] using
      determinant_subgroup_residue_class_mem_card_rootsOfUnity_image
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) c
  have hle :
      (rootsOfUnity (Nat.card C) k).map (QuotientGroup.mk' Qd) ≤
        (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map (QuotientGroup.mk' Qd) := by
    -- Passing from `|C|` to the common `lcm` bound is a plain divisibility enlargement.
    exact
      Subgroup.map_mono
        (rootsOfUnity_le_of_dvd (Nat.dvd_lcm_right (Nat.card G) (Nat.card C)))
  exact hle hbase

/-- Helper for Theorem 17-17.6-1: transporting the fixed constituent first by `t` and then by `s`
is the same subrepresentation as transporting it once by `s * t`. This is the ambient carrier
identity underlying Serre's repeated section cycle. -/
theorem transportedSubrepresentation_mul
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s t : G) :
    transportedSubrepresentation ρ (transportedSubrepresentation ρ Sbar t) s =
      transportedSubrepresentation ρ Sbar (s * t) := by
  apply Subrepresentation.toSubmodule_injective
  ext v
  constructor
  · intro hv
    -- Unpack the two successive ambient images and collapse them with `ρ.map_mul`.
    rcases Submodule.mem_map.mp hv with ⟨w, hw, rfl⟩
    rcases Submodule.mem_map.mp hw with ⟨u, hu, rfl⟩
    refine Submodule.mem_map.mpr ⟨u, hu, ?_⟩
    simpa using LinearMap.congr_fun (ρ.map_mul s t) u
  · intro hv
    -- Factor the single `ρ (s * t)` image through the intermediate transported subrepresentation.
    rcases Submodule.mem_map.mp hv with ⟨u, hu, rfl⟩
    refine Submodule.mem_map.mpr ⟨ρ t u, ?_, ?_⟩
    · exact Submodule.mem_map.mpr ⟨u, hu, rfl⟩
    · simpa using LinearMap.congr_fun (ρ.map_mul s t) u

/-- Helper for Theorem 17-17.6-1: in the cycle step, transporting the already moved constituent by
one more copy of `s` is the same as transport by `s ^ (n + 1)`. This isolates the exact carrier
rewrite needed before comparing the canonical reduced transport maps. -/
theorem transportedSubrepresentation_pow_succ
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G) (n : ℕ) :
    transportedSubrepresentation ρ (transportedSubrepresentation ρ Sbar (s ^ n)) s =
      transportedSubrepresentation ρ Sbar (s ^ (n + 1)) := by
  -- Rewrite the double transport with the literal `pow_succ` factorization.
  simpa [pow_succ'] using
    transportedSubrepresentation_mul (I := I) (ρ := ρ) (Sbar := Sbar) s (s ^ n)

/-- Helper for Theorem 17-17.6-1: the canonical transport comparison is literally the restriction
of the ambient operator `ρ g` to the fixed constituent carrier. Recording this linear-map formula
avoids reopening the `equivMapOfInjective` term in the remaining cycle proof. -/
theorem transportedSubrepresentation_rep_equiv_local_subtype
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (g : G) :
    (transportedSubrepresentation ρ Sbar g).toSubmodule.subtype.comp
        (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar g).toLinearMap =
      (ρ g).comp Sbar.toSubmodule.subtype := by
  -- Both sides are the same ambient vector `ρ g x` on the underlying carrier of `S̄`.
  ext x
  rfl

/-- Helper for Theorem 17-17.6-1: at `g = 1`, the canonical transport equivalence already has
source `S̄` itself after simplifying the trivial conjugation. This isolates the normalization
target used in the section-cycle base case. -/
noncomputable def transportedSubrepresentation_rep_equiv_local_one
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype)) :
    Sbar.toRepresentation.Equiv (transportedSubrepresentation ρ Sbar (1 : G)).toRepresentation := by
  -- The conjugated source action at `1` is definitionally the original `I`-action.
  simpa using transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (1 : G)

/-- Helper for Theorem 17-17.6-1: the single-step transport from `s ^ n` to `s ^ (n + 1)` is the
canonical transport equivalence from the conjugated source action on the `s ^ n`-transported
constituent. This packages the `pow_succ` carrier alignment needed in the section-cycle
induction. -/
noncomputable def transportedSubrepresentation_rep_equiv_local_pow_succ
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G) (n : ℕ) :
    Representation.Equiv
      ((transportedSubrepresentation ρ Sbar (s ^ n)).toRepresentation.comp
        (MulAut.conjNormal s⁻¹).toMonoidHom)
      (transportedSubrepresentation ρ Sbar (s ^ (n + 1))).toRepresentation :=
  (transportedSubrepresentation_pow_succ (I := I) (ρ := ρ) (Sbar := Sbar) s n) ▸
    transportedSubrepresentation_rep_equiv_local_c17 ρ
      (transportedSubrepresentation ρ Sbar (s ^ n)) s

omit [Finite G] [FiniteDimensional k V] in
/-- Helper for Theorem 17-17.6-1: casting the target subrepresentation of an equivalence
does not change the induced ambient subtype map. -/
theorem subrepresentation_subtype_comp_castTargetEquiv_toLinearMap
    (I : Subgroup G)
    (ρ : Representation k G V)
    {U : Type w} [AddCommGroup U] [Module k U]
    {σ : Representation k I U}
    {S T : Subrepresentation (ρ.comp I.subtype)}
    (h : S = T)
    (e : σ.Equiv S.toRepresentation) :
    T.toSubmodule.subtype.comp (h ▸ e).toLinearMap =
      S.toSubmodule.subtype.comp e.toLinearMap := by
  cases h
  rfl

/-- Helper for Theorem 17-17.6-1: after the same `pow_succ` simplification, the subtype map of
the transported constituent still agrees with the ambient action of `ρ s`. This is the ambient
linear-map formula used in the cycle-succ reduction lemmas. -/
theorem transportedSubrepresentation_rep_equiv_local_pow_succ_subtype
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G) (n : ℕ) :
    (transportedSubrepresentation ρ Sbar (s ^ (n + 1))).toSubmodule.subtype.comp
        (transportedSubrepresentation_rep_equiv_local_pow_succ
          (I := I) (ρ := ρ) (Sbar := Sbar) s n).toLinearMap =
      (ρ s).comp (transportedSubrepresentation ρ Sbar (s ^ n)).toSubmodule.subtype := by
  -- The `pow_succ` wrapper is just the canonical one-step transport, viewed through the carrier
  -- equality `transport (s^n)` then `s` equals transport by `s^(n+1)`.
  let Tn := transportedSubrepresentation ρ Sbar (s ^ n)
  let hpow := transportedSubrepresentation_pow_succ (I := I) (ρ := ρ) (Sbar := Sbar) s n
  calc
    (transportedSubrepresentation ρ Sbar (s ^ (n + 1))).toSubmodule.subtype.comp
        (transportedSubrepresentation_rep_equiv_local_pow_succ
          (I := I) (ρ := ρ) (Sbar := Sbar) s n).toLinearMap =
      (transportedSubrepresentation ρ Tn s).toSubmodule.subtype.comp
        (transportedSubrepresentation_rep_equiv_local_c17 ρ Tn s).toLinearMap := by
        simpa [transportedSubrepresentation_rep_equiv_local_pow_succ, Tn, hpow] using
          subrepresentation_subtype_comp_castTargetEquiv_toLinearMap
            (I := I) (ρ := ρ) hpow (transportedSubrepresentation_rep_equiv_local_c17 ρ Tn s)
    _ = (ρ s).comp (transportedSubrepresentation ρ Sbar (s ^ n)).toSubmodule.subtype := by
        simpa [Tn] using
          transportedSubrepresentation_rep_equiv_local_subtype
            (I := I) (ρ := ρ) (Sbar := Tn) s

/-- Helper for Theorem 17-17.6-1: the canonical reduced-side transports compose in the ambient
representation exactly as the corresponding group elements do. This isolates the `pow_succ`
rewrite needed in the normalized section-cycle induction before the remaining endpoint comparison
against the chosen section family. -/
theorem transportedSubrepresentation_rep_equiv_local_subtype_pow_succ
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G) (n : ℕ) :
    (((transportedSubrepresentation ρ Sbar (s ^ (n + 1))).toSubmodule.subtype).comp
        (transportedSubrepresentation_rep_equiv_local_pow_succ
          (I := I) (ρ := ρ) (Sbar := Sbar) s n).toLinearMap).comp
        (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (s ^ n)).toLinearMap =
      ((ρ (s ^ (n + 1))).comp Sbar.toSubmodule.subtype) := by
  -- Compose the one-step subtype formula with the previous `s^n` transport formula, then collapse
  -- the two ambient representation operators using `ρ.map_mul` and `pow_succ'`.
  calc
    (((transportedSubrepresentation ρ Sbar (s ^ (n + 1))).toSubmodule.subtype).comp
        (transportedSubrepresentation_rep_equiv_local_pow_succ
          (I := I) (ρ := ρ) (Sbar := Sbar) s n).toLinearMap).comp
        (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (s ^ n)).toLinearMap =
      ((ρ s).comp (transportedSubrepresentation ρ Sbar (s ^ n)).toSubmodule.subtype).comp
        (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (s ^ n)).toLinearMap := by
        rw [transportedSubrepresentation_rep_equiv_local_pow_succ_subtype]
    _ = (ρ s).comp
        ((transportedSubrepresentation ρ Sbar (s ^ n)).toSubmodule.subtype.comp
          (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (s ^ n)).toLinearMap) := by
        ext x
        rfl
    _ = (ρ s).comp ((ρ (s ^ n)).comp Sbar.toSubmodule.subtype) := by
        rw [transportedSubrepresentation_rep_equiv_local_subtype]
    _ = ((ρ (s ^ (n + 1))).comp Sbar.toSubmodule.subtype) := by
        ext x
        simpa [pow_succ'] using LinearMap.congr_fun (ρ.map_mul s (s ^ n)) x

/-- Helper for Theorem 17-17.6-1: the literal `n`-fold section cycle in Serre's transport cover
`G₁` is obtained by repeatedly composing the chosen section value at `s` inside the transport
fiber over `s ^ n`. This is the source-faithful controlling object behind the remaining section
normalization step. -/
noncomputable def fixed_constituent_section_cycle_fiber
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
    (n : ℕ) →
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I (s ^ n)
  | 0 =>
      fixed_constituent_transport_fiber_reindex
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) (pow_zero s).symm
        (fixed_constituent_transport_fiber_one
          (A := A) (G := G) (I := I) (ρA_I := ρA_I))
  | n + 1 =>
      -- Build the next cycle step by composing the current `s ^ n`-fiber point with the chosen
      -- section element in the `s`-fiber, then reindex from `s ^ n * s` to `s ^ (n + 1)`.
      fixed_constituent_transport_fiber_reindex
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) (pow_succ s n).symm
        (fixed_constituent_transport_fiber_comp
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (fixed_constituent_section_cycle_fiber
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n)
            ((fixed_constituent_transport_total_space_section
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s).2))

/-- Helper for Theorem 17-17.6-1: the determinant of the literal section cycle is the expected
power of the determinant of the chosen section element. This records the multiplicative part of
Serre's cycle argument before the reduced-action comparison is imposed. -/
theorem fixed_constituent_section_cycle_fiber_det
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
    ∀ n : ℕ,
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_section_cycle_fiber
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n) =
        (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          ((fixed_constituent_transport_total_space_section
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s).2)) ^ n := by
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  intro n
  induction n with
  | zero =>
      -- The empty cycle is the identity element of `U₁`, whose determinant is `1`.
      simp only [fixed_constituent_section_cycle_fiber]
      rw [fixed_constituent_transport_fiber_det_reindex_eq]
      simp [fixed_constituent_transport_fiber_det, fixed_constituent_transport_fiber_one,
        Representation.Equiv.mk]
      change LinearEquiv.det (LinearEquiv.refl A P_S) = 1
      simp
  | succ n ihn =>
      -- One more cycle step composes with the chosen section value, so determinants multiply.
      calc
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (fixed_constituent_section_cycle_fiber
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s (n + 1)) =
          fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2 *
            fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)
              (fixed_constituent_section_cycle_fiber
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n) := by
              simpa [fixed_constituent_section_cycle_fiber, sec, pow_succ] using
                fixed_constituent_transport_fiber_det_comp
                  (A := A) (G := G) (I := I) (ρA_I := ρA_I)
                  (fixed_constituent_section_cycle_fiber
                    (p := p) (A := A) (G := G) (V := V)
                    hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n)
                  ((sec s).2)
        _ =
          fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2 *
            (fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2) ^ n := by
                rw [ihn]
        _ =
          (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2) ^ (n + 1) := by
              rw [pow_succ]
              ac_rfl

/-- Helper for Theorem 17-17.6-1: specializing the literal section cycle at `n = |G|` produces an
actual point of the kernel fiber `U₁`. This is the concrete cycle element whose reduced action
must still be shown to be the identity in the remaining section-normalization blocker. -/
noncomputable def fixed_constituent_section_card_cycle_kernel
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
    fixed_constituent_transport_fiber
      (A := A) (G := G) I ρA_I (1 : G) := by
  -- Rewrite `s ^ |G| = 1` so the literal cycle lives in the kernel fiber `U₁`.
  simpa [pow_card_eq_one'] using
    fixed_constituent_section_cycle_fiber
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s (Nat.card G)

/-- Helper for Theorem 17-17.6-1: the literal `|G|`-cycle of the chosen section is already a
kernel scalar upstairs. The remaining source-faithful gap is only to prove that its reduction is
the identity, forcing the scalar residue to be `1`. -/
theorem fixed_constituent_section_card_cycle_kernel_scalar
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
    (hkernel :
      ∀ u :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (1 : G),
        ∃ a : Aˣ, u.toLinearEquiv = a • LinearEquiv.refl A P_S)
    (s : G) :
    ∃ a : Aˣ,
      (fixed_constituent_section_card_cycle_kernel
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s).toLinearEquiv =
        a • LinearEquiv.refl A P_S := by
  -- Apply the kernel classification to the actual cycle element of `U₁`.
  exact
    hkernel
      (fixed_constituent_section_card_cycle_kernel
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s)

end

end Representation
