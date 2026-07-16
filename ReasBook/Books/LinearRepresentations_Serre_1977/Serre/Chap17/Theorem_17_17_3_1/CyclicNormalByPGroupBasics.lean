import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_1_3
import LinearRepresentations_Serre_1977.Serre.Chap07.Remark_7_7_1_4
import LinearRepresentations_Serre_1977.Serre.Chap08.Corollary_8_8_3_8
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_5_3.Index
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_5_3
import LinearRepresentations_Serre_1977.GroupTheory.PSolvable

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace Representation

section

variable {A : Type u} [CommRing A] [HenselianLocalRing A]
variable {G : Type v} [Group G] [Finite G]
variable {p : ℕ}

variable [CharP (IsLocalRing.ResidueField A) p]
variable {V : Type w} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]
variable [FiniteDimensional (IsLocalRing.ResidueField A) V]
variable {C P : Subgroup G}

local notation "k" => IsLocalRing.ResidueField A
noncomputable local instance basicsResidueFieldModule : Module A V :=
  Module.compHom V (algebraMap A k)
local instance basicsResidueFieldIsScalarTower : IsScalarTower A k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.3-1: the quotient by the cyclic normal factor is a `p`-group as soon
as the complement factor is a `p`-group. -/
lemma quotient_isPGroup_of_isComplement'
    (hC : C.Normal) (hCP : C.IsComplement' P) (hP : IsPGroup p P) :
    IsPGroup p (G ⧸ C) := by
  letI : C.Normal := hC
  -- Identify `G ⧸ C` with the complementary `p`-group `P`.
  let e : G ⧸ C ≃* P := hCP.symm.QuotientMulEquiv
  exact hP.of_equiv e.symm

/-- Helper for Theorem 17-17.3-1: a cyclic normal Hall subgroup together with a `p`-group
complement makes `G` `p`-solvable of height `2`. -/
lemma isPSolvableOfHeight_two_of_cyclicNormalByPGroupDecomposition
    (hC : C.Normal) (hCP : C.IsComplement' P)
    (hCoprime : Nat.Coprime p (Nat.card C)) (hP : IsPGroup p P) :
    IsPSolvableOfHeight p 2 G := by
  letI : C.Normal := hC
  have hquotP : IsPGroup p (G ⧸ C) := quotient_isPGroup_of_isComplement' hC hCP hP
  refine ⟨C, hC, Or.inl hCoprime, ?_⟩
  refine ⟨⊤, inferInstance, Or.inr ?_, ?_⟩
  · -- Transport the ambient `p`-group structure to the top subgroup of the quotient.
    exact
      hquotP.of_equiv
        (Subgroup.topEquiv : (⊤ : Subgroup (G ⧸ C)) ≃* (G ⧸ C)).symm
  · -- The quotient by the top subgroup is trivial, so the height drops to `0`.
    simpa [IsPSolvableOfHeight] using
      (inferInstance : Subsingleton ((G ⧸ C) ⧸ (⊤ : Subgroup (G ⧸ C))))

/-- Helper for Theorem 17-17.3-1: the group-theoretic hypotheses already imply that `G` is
`p`-solvable. -/
lemma isPSolvable_of_cyclicNormalByPGroupDecomposition
    (hC : C.Normal) (hCP : C.IsComplement' P)
    (hCoprime : Nat.Coprime p (Nat.card C)) (hP : IsPGroup p P) :
    IsPSolvable p G := by
  -- Package the explicit height-two witness obtained from the cyclic-normal-by-`p` decomposition.
  exact ⟨2, isPSolvableOfHeight_two_of_cyclicNormalByPGroupDecomposition hC hCP hCoprime hP⟩

/-- Helper for Theorem 17-17.3-1: a proper subgroup of a finite group has strictly smaller
cardinality. -/
lemma subgroup_natCard_lt_of_ne_top_c1731 (H : Subgroup G) (hH : H ≠ ⊤) :
    Nat.card H < Nat.card G := by
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype H := Fintype.ofFinite H
  -- A proper subgroup misses at least one ambient element, so its carrier subtype is strictly
  -- smaller than the full ambient type.
  have hex : ∃ x : G, x ∉ H := by
    by_cases hforall : ∀ x : G, x ∈ H
    · exact False.elim (hH (by
        ext x
        simp [hforall x]))
    · exact not_forall.mp hforall
  rcases hex with ⟨x, hx⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simpa using (Fintype.card_subtype_lt (p := fun y : G ↦ y ∈ H) hx)

/-- Helper for Theorem 17-17.3-1: the Chapter `15` prime-to-`p` lifting theorem remains available
after resizing a finite group into the coefficient-ring universe. -/
lemma exists_residueFieldLift_of_non_dvd_card
    {H : Type v} [Group H] [Finite H]
    (hHcop : ¬ p ∣ Nat.card H) (ρH : Representation k H V) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module A W)
      (_ : Module.Free A W) (_ : Module.Finite A W)
      (ρA_H : Representation A H W)
      (red_H : W →ₗ[A] V),
        IsResidueFieldLift ρH ρA_H red_H := by
  have hSmallH : Small.{u} H := by
    obtain ⟨n, ⟨efin⟩⟩ := Finite.exists_equiv_fin H
    exact Small.mk' (efin.trans Equiv.ulift.symm)
  letI : Small.{u} H := hSmallH
  let eShrink : Shrink.{u} H ≃* H := Shrink.mulEquiv
  have hShrink_ndvd : ¬ p ∣ Nat.card (Shrink.{u} H) := by
    simpa [Nat.card_congr eShrink.toEquiv] using hHcop
  obtain ⟨W, hWadd, hWmod, hWfree, hWfinite, ρA_shrink, red_H, hLift_shrink⟩ :=
    Representation.exists_residueFieldLift
      (A := A) (p := p) (G := Shrink.{u} H) (V := V) hShrink_ndvd
      (ρH.comp eShrink.toMonoidHom)
  let ρA_H : Representation A H W := ρA_shrink.comp eShrink.symm.toMonoidHom
  refine ⟨W, hWadd, hWmod, hWfree, hWfinite, ρA_H, red_H, ?_⟩
  have hLift :
      IsResidueFieldLift
        ((ρH.comp eShrink.toMonoidHom).comp eShrink.symm.toMonoidHom)
        (ρA_shrink.comp eShrink.symm.toMonoidHom)
        red_H := by
    exact Representation.isResidueFieldLift_comp hLift_shrink eShrink.symm.toMonoidHom
  have hρH :
      (ρH.comp eShrink.toMonoidHom).comp eShrink.symm.toMonoidHom = ρH := by
    ext h x
    simp
  rw [← hρH]
  simpa [ρA_H] using hLift

/-- Helper for Theorem 17-17.3-1: when the residue characteristic parameter vanishes, the Chapter
`15` prime-to-`p` lifting theorem applies directly because divisibility by `0` never occurs for the
positive cardinality of a finite group. -/
lemma exists_residueFieldLift_of_isIrreducible_of_cyclicNormalByPGroupDecomposition_of_charZero
    (hp0 : p = 0) (ρ : Representation k G V) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module A W)
      (_ : Module.Free A W) (_ : Module.Finite A W)
      (ρA : Representation A G W)
      (red : W →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  have hGcop : ¬ p ∣ Nat.card G := by
    subst hp0
    simpa using (Nat.ne_of_gt (Nat.card_pos (α := G)))
  exact exists_residueFieldLift_of_non_dvd_card (A := A) (p := p) hGcop ρ

/-- Helper for Theorem 17-17.3-1: over the residue field of characteristic `p`, every
representation of a finite group whose cardinality is coprime to `p` is semisimple as a
`MonoidAlgebra`-module. -/
lemma isSemisimpleModule_asModule_of_coprime_card
    {H : Subgroup G} (hp : Nat.Prime p) (hHcop : Nat.Coprime p (Nat.card H))
    (ρH : Representation k H V) :
    letI : Module (MonoidAlgebra k H) V := ρH.instModuleMonoidAlgebraAsModule
    IsSemisimpleModule (MonoidAlgebra k H) V := by
  letI : Module (MonoidAlgebra k H) V := ρH.instModuleMonoidAlgebraAsModule
  -- Maschke applies because the group order stays nonzero in the residue field.
  letI : NeZero (Nat.card H : k) := by
    exact NeZero.of_not_dvd k (hp.coprime_iff_not_dvd.mp hHcop)
  infer_instance

/-- Helper for Theorem 17-17.3-1: a nonzero semisimple owner submodule of a restricted
representation contains an irreducible subrepresentation. -/
lemma exists_irreducible_subrepresentation_le
    {H : Subgroup G} [Finite H] [NeZero (Nat.card H : k)]
    (ρH : Representation k H V)
    (hsem :
      letI : Module (MonoidAlgebra k H) V := ρH.instModuleMonoidAlgebraAsModule
      IsSemisimpleModule (MonoidAlgebra k H) V)
    (U : Subrepresentation ρH)
    (hU : U.asSubmodule ≠ ⊥) :
    ∃ W : Subrepresentation ρH,
      W.toSubmodule ≤ U.toSubmodule ∧
        W.toSubmodule ≠ ⊥ ∧
          W.toRepresentation.IsIrreducible := by
  letI : Module (MonoidAlgebra k H) V := ρH.instModuleMonoidAlgebraAsModule
  letI : IsSemisimpleModule (MonoidAlgebra k H) V := hsem
  -- Pick a simple owner submodule inside `U.asSubmodule` and repackage it as a subrepresentation.
  obtain ⟨N, hNle, hNsimple⟩ :=
    (IsSemisimpleModule.eq_bot_or_exists_simple_le
      (R := MonoidAlgebra k H) (M := V) U.asSubmodule).resolve_left hU
  let W : Subrepresentation ρH := Subrepresentation.ofSubmodule' N
  refine ⟨W, ?_, ?_, ?_⟩
  · -- Forgetting from the owner submodule back to the underlying `k`-subspace preserves inclusion.
    simpa [W] using hNle
  · -- A simple owner submodule cannot be zero, so its underlying `k`-subspace is nonzero.
    intro hW
    have hN_ne_bot : N ≠ ⊥ := by
      letI : IsSimpleModule (MonoidAlgebra k H) N := hNsimple
      exact Submodule.nontrivial_iff_ne_bot.mp
        (IsSimpleModule.nontrivial (MonoidAlgebra k H) N)
    apply hN_ne_bot
    ext v
    have hW' : (Subrepresentation.ofSubmodule' N).toSubmodule = (⊥ : Submodule k V) := by
      simpa [W] using hW
    simpa using congrArg (fun S : Submodule k V ↦ v ∈ S) hW'
  · -- The Chapter `1` bridge upgrades owner simplicity to irreducibility of the subrepresentation.
    exact isIrreducible_toRepresentation_of_isSimpleModule_asSubmodule ρH N hNsimple

/-- Helper for Theorem 17-17.3-1: the supremum of the left-coset translates of a restricted
subrepresentation is stable under the ambient action. -/
lemma leftQuotientSubmodule_iSup_stable
    (ρ : Representation k G V)
    {H : Subgroup G}
    (U : Subrepresentation (ρ.comp H.subtype))
    (s : G) :
    (⨆ q : G ⧸ H, ρ.leftQuotientSubmodule H U q).map (ρ s) ≤
      ⨆ q : G ⧸ H, ρ.leftQuotientSubmodule H U q := by
  -- Send each quotient summand to the translated summand indexed by `s • q`.
  calc
    (⨆ q : G ⧸ H, ρ.leftQuotientSubmodule H U q).map (ρ s) =
        ⨆ q : G ⧸ H, (ρ.leftQuotientSubmodule H U q).map (ρ s) := by
          rw [Submodule.map_iSup]
    _ ≤ ⨆ q : G ⧸ H, ρ.leftQuotientSubmodule H U q := by
          refine iSup_le fun q ↦ ?_
          have hq :
              (ρ.leftQuotientSubmodule H U q).map (ρ s) ≤
                ρ.leftQuotientSubmodule H U (s • q) := by
            refine Quotient.inductionOn' q ?_
            intro g
            change Submodule.map (ρ s) (Submodule.map (ρ g) U.toSubmodule) ≤
              ρ.leftQuotientSubmodule H U (((s * g : G) : G ⧸ H))
            rw [ρ.leftQuotientSubmodule_mk H U (s * g)]
            intro x hx
            rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
            rcases Submodule.mem_map.mp hy with ⟨u, hu, rfl⟩
            exact Submodule.mem_map.mpr ⟨u, hu, by
              simpa [Module.End.mul_apply] using
                (LinearMap.congr_fun (ρ.map_mul s g) u).symm⟩
          exact hq.trans (le_iSup (fun q : G ⧸ H ↦ ρ.leftQuotientSubmodule H U q) (s • q))

/-- Helper for Theorem 17-17.3-1: if an irreducible ambient representation is induced from a
restricted subrepresentation `W`, then it is already induced from any nonzero subrepresentation
contained in `W`. -/
lemma isInducedFromSubrepresentation_of_nonzero_le
    (ρ : Representation k G V) [ρ.IsIrreducible]
    {H : Subgroup G}
    {U W : Subrepresentation (ρ.comp H.subtype)}
    (hUW : U.toSubmodule ≤ W.toSubmodule)
    (hUne : U.toSubmodule ≠ ⊥)
    (hInd : ρ.IsInducedFromSubrepresentation H W) :
    ρ.IsInducedFromSubrepresentation H U := by
  classical
  let _ : DecidableEq (G ⧸ H) := Classical.decEq _
  let ℳW : G ⧸ H → Submodule k V := ρ.leftQuotientSubmodule H W
  let ℳU : G ⧸ H → Submodule k V := ρ.leftQuotientSubmodule H U
  have hInternalW : DirectSum.IsInternal ℳW := by
    -- Unpack the Chapter `3` owner for `W` into its quotient-indexed internal direct sum.
    simpa [ℳW, Representation.IsInducedFromSubrepresentation] using hInd
  have hfamily_le : ℳU ≤ ℳW := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro g
    simpa [ℳU, ℳW, ρ.leftQuotientSubmodule_mk H U g, ρ.leftQuotientSubmodule_mk H W g] using
      (Submodule.map_mono hUW)
  have hIndepU : iSupIndep ℳU := by
    -- Independence descends because each `U`-translate lies inside the matching `W`-translate.
    exact hInternalW.submodule_iSupIndep.mono hfamily_le
  let S : Submodule k V := ⨆ q : G ⧸ H, ℳU q
  let Sρ : Subrepresentation ρ :=
    { toSubmodule := S
      apply_mem_toSubmodule := by
        intro s x hx
        have hxmap : ρ s x ∈ S.map (ρ s) := by
          exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
        exact leftQuotientSubmodule_iSup_stable ρ U s hxmap }
  have hS_ne_bot : S ≠ ⊥ := by
    intro hSbot
    apply hUne
    have hU_le_S : U.toSubmodule ≤ S := by
      intro x hx
      have hxq : x ∈ ρ.leftQuotientSubmodule H U ((1 : G) : G ⧸ H) := by
        rw [ρ.leftQuotientSubmodule_mk H U (1 : G)]
        exact Submodule.mem_map.mpr ⟨x, hx, by
          simpa using (LinearMap.congr_fun ρ.map_one x).symm⟩
      exact (show ρ.leftQuotientSubmodule H U ((1 : G) : G ⧸ H) ≤ S by
        simpa [S, ℳU] using
          (le_iSup (fun q : G ⧸ H ↦ ρ.leftQuotientSubmodule H U q) ((1 : G) : G ⧸ H))) hxq
    exact le_bot_iff.mp (hSbot ▸ hU_le_S)
  have hSρ_ne_bot : Sρ ≠ ⊥ := by
    intro hbot
    apply hS_ne_bot
    simpa [Sρ] using congrArg Subrepresentation.toSubmodule hbot
  have hSρ_top : Sρ = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top Sρ).resolve_left hSρ_ne_bot
  have hspanU : iSup ℳU = ⊤ := by
    -- Irreducibility forces the nonzero stable span of the `U`-translates to be all of `V`.
    simpa [S, Sρ] using congrArg Subrepresentation.toSubmodule hSρ_top
  -- Repackage the descended independence and spanning statements into the induced owner.
  unfold Representation.IsInducedFromSubrepresentation
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hIndepU hspanU

/-- Helper for Theorem 17-17.3-1: the underlying `k`-subspace obtained by transporting a
restricted `H`-subrepresentation through the operator `ρ g`. -/
noncomputable def transportedSubrepresentationCarrier
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    (g : G) :
    Submodule k V :=
  W.toSubmodule.map (ρ g)

/-- Helper for Theorem 17-17.3-1: normality of `H` makes the `ρ g`-image of an `H`-stable
subspace stable under the restricted `H`-action again. -/
lemma transportedSubrepresentationCarrier_apply_mem
    (ρ : Representation k G V)
    {H : Subgroup G} [H.Normal]
    (W : Subrepresentation (ρ.comp H.subtype))
    (g : G) (a : H)
    {v : V} (hv : v ∈ transportedSubrepresentationCarrier ρ W g) :
    ρ a v ∈ transportedSubrepresentationCarrier ρ W g := by
  -- Write `v` as `ρ g w` with `w ∈ W`, then move the `H`-action across `ρ g` by conjugation.
  rcases Submodule.mem_map.mp hv with ⟨w, hw, rfl⟩
  let a' : H := ⟨g⁻¹ * a * g, Subgroup.Normal.conj_mem' (H := H) inferInstance a a.property g⟩
  refine Submodule.mem_map.mpr ?_
  refine ⟨ρ a' w, W.apply_mem_toSubmodule a' hw, ?_⟩
  calc
    ρ g (ρ a' w) = ρ (g * (a' : H)) w := by
      exact (LinearMap.congr_fun (ρ.map_mul g (a' : H)) w).symm
    _ = ρ ((a : G) * g) w := by
      simp [a', mul_assoc]
    _ = ρ a (ρ g w) := by
      exact LinearMap.congr_fun (ρ.map_mul (a : G) g) w

/-- Helper for Theorem 17-17.3-1: transporting an `H`-stable subrepresentation through `ρ g`
produces another `H`-stable subrepresentation. -/
noncomputable def transportedSubrepresentation
    (ρ : Representation k G V)
    {H : Subgroup G} [H.Normal]
    (W : Subrepresentation (ρ.comp H.subtype))
    (g : G) :
    Subrepresentation (ρ.comp H.subtype) :=
  { toSubmodule := transportedSubrepresentationCarrier ρ W g
    apply_mem_toSubmodule := transportedSubrepresentationCarrier_apply_mem ρ W g }

/-- Helper for Theorem 17-17.3-1: the transported subrepresentation has the expected carrier. -/
@[simp] lemma transportedSubrepresentation_toSubmodule
    (ρ : Representation k G V)
    {H : Subgroup G} [H.Normal]
    (W : Subrepresentation (ρ.comp H.subtype))
    (g : G) :
    (transportedSubrepresentation ρ W g).toSubmodule =
      transportedSubrepresentationCarrier ρ W g :=
  rfl

/-- Helper for Theorem 17-17.3-1: every `ρ g` is injective, so transporting a nonzero restricted
subrepresentation keeps it nonzero. -/
lemma transportedSubrepresentation_ne_bot
    (ρ : Representation k G V)
    {H : Subgroup G} [H.Normal]
    (W : Subrepresentation (ρ.comp H.subtype))
    (g : G)
    (hW : W.toSubmodule ≠ ⊥) :
    (transportedSubrepresentation ρ W g).toSubmodule ≠ ⊥ := by
  -- Apply `ρ g⁻¹` to an equality `map (ρ g) = ⊥` to recover `W = ⊥`.
  intro hbot
  apply hW
  refine le_antisymm ?_ bot_le
  intro w hw
  have hmem : ρ g w ∈ (transportedSubrepresentation ρ W g).toSubmodule := by
    rw [transportedSubrepresentation_toSubmodule]
    exact Submodule.mem_map.mpr ⟨w, hw, rfl⟩
  have hzero_mem : ρ g w ∈ (⊥ : Submodule k V) := by
    rw [hbot] at hmem
    simpa using hmem
  have hzero : ρ g w = 0 := by
    simpa using hzero_mem
  have happly := congrArg (ρ g⁻¹) hzero
  simpa using happly

/-- Helper for Theorem 17-17.3-1: if a restricted subrepresentation is nonzero as an owner
submodule over `k[H]`, then its transported copy is still nonzero as an owner submodule. -/
lemma transportedSubrepresentation_asSubmodule_ne_bot
    (ρ : Representation k G V)
    {H : Subgroup G} [H.Normal]
    (W : Subrepresentation (ρ.comp H.subtype))
    (g : G)
    (hW : W.asSubmodule ≠ ⊥) :
    (transportedSubrepresentation ρ W g).asSubmodule ≠ ⊥ := by
  let ρH : Representation k H V := ρ.comp H.subtype
  have hW_toSubmodule : W.toSubmodule ≠ ⊥ := by
    intro hbot
    apply hW
    ext v
    change ((v : V) ∈ W.toSubmodule) ↔ v ∈ (⊥ : Submodule (MonoidAlgebra k H) ρH.asModule)
    rw [hbot]
    constructor <;> intro hv <;> simpa using hv
  have htransport_toSubmodule :
      (transportedSubrepresentation ρ W g).toSubmodule ≠ ⊥ :=
    transportedSubrepresentation_ne_bot ρ W g hW_toSubmodule
  intro hbot
  have hbot_toSubmodule : (transportedSubrepresentation ρ W g).toSubmodule = ⊥ := by
    ext v
    change v ∈ (transportedSubrepresentation ρ W g).asSubmodule ↔
        v ∈ (⊥ : Submodule (MonoidAlgebra k H) ρH.asModule)
    rw [hbot]
  exact htransport_toSubmodule hbot_toSubmodule

/-- Helper for Theorem 17-17.3-1: if the semisimple restricted module has at most one isotypic
component, then the whole restriction is isotypic. -/
lemma isIsotypic_of_subsingleton_componentFamily
    (R : Type*) (M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    [IsSemisimpleModule R M]
    (hsub : Subsingleton (isotypicComponents R M)) :
    IsIsotypic R M := by
  classical
  by_cases hne : Nonempty (isotypicComponents R M)
  · rcases hne with ⟨⟨c, hc⟩⟩
    -- A singleton family of isotypic components has supremum equal to its unique member.
    have hsSup_le : sSup (isotypicComponents R M) ≤ c := by
      exact sSup_le fun m hm ↦ by
        have hm_eq : m = c := by
          exact congrArg Subtype.val (hsub.elim ⟨m, hm⟩ ⟨c, hc⟩)
        exact hm_eq ▸ le_rfl
    have htop_le : (⊤ : Submodule R M) ≤ c := by
      simpa [sSup_isotypicComponents R M] using hsSup_le
    have hc_top : c = ⊤ := top_unique htop_le
    -- Once the unique component is all of `M`, its isotypy is the target statement.
    subst hc_top
    have htop_isotypic : IsIsotypic R ↥(⊤ : Submodule R M) := by
      simpa using (IsIsotypic.isotypicComponents hc)
    exact
      (LinearEquiv.isIsotypic_iff
        (e := (Submodule.topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M))).mp htop_isotypic
  · have hEmpty : isotypicComponents R M = ∅ := by
      ext m
      constructor
      · intro hm
        exact hne ⟨⟨m, hm⟩⟩
      · intro hm
        simp at hm
    have htop_eq_bot : (⊤ : Submodule R M) = ⊥ := by
      calc
        (⊤ : Submodule R M) = sSup (isotypicComponents R M) := (sSup_isotypicComponents R M).symm
        _ = sSup (∅ : Set (Submodule R M)) := by simp [hEmpty]
        _ = ⊥ := by simp
    letI : Subsingleton M := by
      refine ⟨fun x y ↦ ?_⟩
      have hx_top : x ∈ (⊤ : Submodule R M) := by simp
      have hy_top : y ∈ (⊤ : Submodule R M) := by simp
      have hx_bot : x ∈ (⊥ : Submodule R M) := by simpa [htop_eq_bot] using hx_top
      have hy_bot : y ∈ (⊥ : Submodule R M) := by simpa [htop_eq_bot] using hy_top
      have hx_zero : x = 0 := by simpa [Submodule.mem_bot] using hx_bot
      have hy_zero : y = 0 := by simpa [Submodule.mem_bot] using hy_bot
      simp [hx_zero, hy_zero]
    -- The zero module is automatically isotypic.
    exact IsIsotypic.of_subsingleton R M

/-- Helper for Theorem 17-17.3-1: converting a set-indexed family of owner submodules into the
corresponding subtype-indexed family of bundled subrepresentations preserves independence and
spanning after forgetting from `k[C]` to `k`. -/
lemma iSupIndep_and_iSup_top_of_subtype_ofSubmodule'_family_c17
    {H : Subgroup G}
    (ρH : Representation k H V)
    (s : Set (Submodule (MonoidAlgebra k H) ρH.asModule))
    (hs_indep : sSupIndep s) (hs_top : sSup s = ⊤) :
    iSupIndep (fun i : s ↦ (Subrepresentation.ofSubmodule' i.1).toSubmodule) ∧
      (⨆ i : s, (Subrepresentation.ofSubmodule' i.1).toSubmodule) = ⊤ := by
  -- Convert the set-indexed owner decomposition to the subtype-indexed owner family first.
  have hs_indep' :
      iSupIndep (fun i : s ↦ (i : Submodule (MonoidAlgebra k H) ρH.asModule)) :=
    (sSupIndep_iff s).mp hs_indep
  -- Restrict scalars from `k[H]` to `k`; this keeps both independence and the top supremum.
  have hσ_indep :
      iSupIndep
        (fun i : s ↦ Submodule.restrictScalars k (i : Submodule (MonoidAlgebra k H) ρH.asModule)) := by
    rw [iSupIndep] at hs_indep'
    rw [iSupIndep]
    intro i
    rw [disjoint_iff_inf_le]
    have hi :
        ((i : Submodule (MonoidAlgebra k H) ρH.asModule) ⊓
            ⨆ (j : s) (_ : j ≠ i), (j : Submodule (MonoidAlgebra k H) ρH.asModule)) ≤ ⊥ := by
      simpa [disjoint_iff_inf_le] using hs_indep' i
    simpa [Submodule.restrictScalars_inf, Submodule.restrictScalars_iSup] using
      (Submodule.restrictScalars_mono (S := k) (hst := hi))
  have hs_top' : (⨆ i : s, (i : Submodule (MonoidAlgebra k H) ρH.asModule)) = ⊤ := by
    simpa [sSup_eq_iSup'] using hs_top
  have hσ_top :
      (⨆ i : s, Submodule.restrictScalars k (i : Submodule (MonoidAlgebra k H) ρH.asModule)) = ⊤ := by
    simpa [Submodule.restrictScalars_iSup] using
      congrArg (Submodule.restrictScalars k) hs_top'
  -- `Subrepresentation.ofSubmodule'` is definitionally the restricted-scalar carrier.
  simpa using ⟨hσ_indep, hσ_top⟩

/-- Helper for Theorem 17-17.3-1: every element of `C` stabilizes each `C`-stable restricted
subrepresentation. -/
lemma stabilizer_contains_C_of_restricted_subrepresentation
    (ρ : Representation k G V)
    (W : Subrepresentation (ρ.comp C.subtype)) :
    C ≤ ρ.submoduleStabilizer W.toSubmodule := by
  intro x hx
  rw [mem_submoduleStabilizer_iff_map_eq]
  -- The restricted `C`-action already preserves the chosen `C`-stable summand.
  refine le_antisymm ?_ ?_
  · intro v hv
    rcases Submodule.mem_map.mp hv with ⟨w, hw, rfl⟩
    exact W.apply_mem_toSubmodule ⟨x, hx⟩ hw
  · intro v hv
    refine Submodule.mem_map.mpr ⟨ρ x⁻¹ v, ?_, ?_⟩
    · exact W.apply_mem_toSubmodule ⟨x⁻¹, C.inv_mem hx⟩ hv
    · simpa [Module.End.mul_apply] using
        (LinearMap.congr_fun (ρ.map_mul x x⁻¹) v).symm

/-- Helper for Theorem 17-17.3-1: a simple owner submodule gives an irreducible bundled
subrepresentation even when no Maschke-style `NeZero` hypothesis is available. -/
lemma isIrreducible_toRepresentation_of_isSimpleModule_asSubmodule_without_neZero
    {H : Type*} [Group H]
    {W : Type*} [AddCommGroup W] [Module k W]
    (ρ : Representation k H W) (N : Submodule (MonoidAlgebra k H) ρ.asModule)
    (hN : IsSimpleModule (MonoidAlgebra k H) N) :
    (Subrepresentation.ofSubmodule' N).toRepresentation.IsIrreducible := by
  let ρN : Representation k H N := (Subrepresentation.ofSubmodule' N).toRepresentation
  letI : Module (MonoidAlgebra k H) ρN.asModule := ρN.instModuleMonoidAlgebraAsModule
  let hsmul :
      ∀ (r : MonoidAlgebra k H) (x : N),
        (((Subrepresentation.ofSubmodule' N).toRepresentation).asAlgebraHom r) x = r • x := by
    intro r x
    apply Subtype.ext
    induction r using MonoidAlgebra.induction_linear with
    | zero =>
        rfl
    | add a b ha hb =>
        have hmap :
            (((Subrepresentation.ofSubmodule' N).toRepresentation).asAlgebraHom (a + b)) x =
              ((((Subrepresentation.ofSubmodule' N).toRepresentation).asAlgebraHom a) +
                (((Subrepresentation.ofSubmodule' N).toRepresentation).asAlgebraHom b)) x := by
          exact
            congrArg (fun f : Module.End k ↥(Subrepresentation.ofSubmodule' N).toSubmodule ↦ f x)
              (((Subrepresentation.ofSubmodule' N).toRepresentation).asAlgebraHom.map_add a b)
        have haddN :
            (((Subrepresentation.ofSubmodule' N).toRepresentation).asAlgebraHom (a + b)) x =
              ((a + b) • x : N) := by
          rw [hmap]
          apply Subtype.ext
          simpa [Submodule.coe_add, add_smul] using
            congrArg₂ (fun u v : W ↦ u + v) ha hb
        exact congrArg Subtype.val haddN
    | single g a =>
        have hsingleN :
            (((Subrepresentation.ofSubmodule' N).toRepresentation).asAlgebraHom (MonoidAlgebra.single g a)) x =
              (MonoidAlgebra.single g a • x : N) := by
          apply Subtype.ext
          have hsingle :
              ↑(((Subrepresentation.ofSubmodule' N).toRepresentation g) x) =
                (ρ g) (ρ.asModuleEquiv ↑x) := by
            rfl
          simpa [Representation.asAlgebraHom_single, Representation.single_smul] using
            congrArg (fun y : W ↦ a • y) hsingle
        exact congrArg Subtype.val hsingleN
  let e : ρN.asModule ≃ₗ[MonoidAlgebra k H] N := by
    refine
      { toFun := fun x => ρN.asModuleEquiv x
        invFun := fun x => ρN.asModuleEquiv.symm x
        left_inv := by
          intro x
          simp
        right_inv := by
          intro x
          simp
        map_add' := by
          intro x y
          rfl
        map_smul' := by
          intro r x
          calc
            ρN.asModuleEquiv (r • x) = (ρN.asAlgebraHom r) (ρN.asModuleEquiv x) := by
              exact Representation.asModuleEquiv_map_smul (ρ := ρN) r x
            _ = r • ρN.asModuleEquiv x := by
              exact hsmul r (ρN.asModuleEquiv x) }
  exact
    (Representation.irreducible_iff_isSimpleModule_asModule ρN).mpr
      (@IsSimpleModule.congr (MonoidAlgebra k H) inferInstance ρN.asModule
        ρN.instAddCommGroupAsModule ρN.instModuleMonoidAlgebraAsModule
        N N.addCommGroup N.module e hN)

/-- Helper for Theorem 17-17.3-1: every nonzero `H`-stable subrepresentation contains an
irreducible `H`-subrepresentation, by choosing a minimal nonzero owner submodule. -/
lemma exists_irreducible_subrepresentation_le_of_nonzero
    {H : Subgroup G} [Finite H]
    (ρH : Representation k H V)
    (U : Subrepresentation ρH)
    (hU : U.asSubmodule ≠ ⊥) :
    ∃ W : Subrepresentation ρH,
      W.toSubmodule ≤ U.toSubmodule ∧
        W.toSubmodule ≠ ⊥ ∧
          W.toRepresentation.IsIrreducible := by
  letI : Module (MonoidAlgebra k H) V := ρH.instModuleMonoidAlgebraAsModule
  letI : IsScalarTower k (MonoidAlgebra k H) V := by
    simpa [Representation.asModule] using
      (inferInstance : IsScalarTower k (MonoidAlgebra k H) ρH.asModule)
  have hArtV_k : IsArtinian k V := by infer_instance
  letI : IsArtinian (MonoidAlgebra k H) V := isArtinian_of_tower k (M := V) hArtV_k
  let s : Set (Submodule (MonoidAlgebra k H) V) := {N | N ≤ U.asSubmodule ∧ N ≠ ⊥}
  have hs_nonempty : s.Nonempty := ⟨U.asSubmodule, le_rfl, hU⟩
  obtain ⟨N, hN_mem, hN_min⟩ :=
    IsArtinian.set_has_minimal (R := MonoidAlgebra k H) (M := V) s hs_nonempty
  have hN_le : N ≤ U.asSubmodule := hN_mem.1
  have hN_ne : N ≠ ⊥ := hN_mem.2
  have hN_simple : IsSimpleModule (MonoidAlgebra k H) N := by
    rw [isSimpleModule_iff_isAtom, isAtom_iff_le_of_ge]
    constructor
    · exact hN_ne
    · intro J hJ_ne hJ_le
      by_cases hJN : J = N
      · simpa [hJN] using (le_rfl : N ≤ N)
      · have hJ_mem : J ∈ s := ⟨hJ_le.trans hN_le, hJ_ne⟩
        have hJ_not_lt : ¬ J < N := hN_min J hJ_mem
        exact False.elim <| hJ_not_lt (lt_of_le_of_ne hJ_le hJN)
  let W : Subrepresentation ρH := Subrepresentation.ofSubmodule' N
  refine ⟨W, ?_, ?_, ?_⟩
  · -- Forgetting the owner structure preserves inclusion into the ambient `k`-subspace.
    simpa [W] using hN_le
  · -- A nonzero owner submodule cannot become zero after forgetting to `k`.
    intro hW
    apply hN_ne
    ext v
    have hW' : (Subrepresentation.ofSubmodule' N).toSubmodule = (⊥ : Submodule k V) := by
      simpa [W] using hW
    simpa using congrArg (fun S : Submodule k V ↦ v ∈ S) hW'
  · -- Chapter `1` upgrades owner simplicity to irreducibility of the bundled witness.
    exact
      isIrreducible_toRepresentation_of_isSimpleModule_asSubmodule_without_neZero
        ρH N hN_simple

end

end Representation
