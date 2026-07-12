import Mathlib
import LinearRepresentations_Serre_1977.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.GroupTheory.PSolvable
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_1_3
import LinearRepresentations_Serre_1977.Chap07.Remark_7_7_1_4
import LinearRepresentations_Serre_1977.Chap08.Proposition_8_8_3_7
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_5_3
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CyclicNormalByPGroupBasics
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CliffordIsotypicTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ResidueFieldLiftTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ProperOvergroupRecursion
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CyclicOrbitSpan
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.SameUniverseInductionPackaging
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.InducedSubrepresentationLift

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

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
private noncomputable instance quotientHeightRecursionModule : Module A V :=
  Module.compHom V (algebraMap A k)
private instance quotientHeightRecursionScalarTower : IsScalarTower A k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.6-1: `p`-solvable height passes to subgroups. -/
lemma isPSolvableOfHeight_of_subgroup
    (H : Subgroup G) (hG : IsPSolvableOfHeight p h G) :
    IsPSolvableOfHeight p h H := by
  induction h generalizing G H with
  | zero =>
      letI : Subsingleton G := hG
      exact (inferInstance : Subsingleton H)
  | succ h ih =>
      rcases IsPSolvableOfHeight.succ_iff.mp hG with ⟨I, hI, hstep, hquot⟩
      let J : Subgroup H := I.subgroupOf H
      letI : J.Normal := hI.subgroupOf H
      have hJ_eq : (H ⊓ I).subgroupOf H = J := by
        simpa [J] using (Subgroup.inf_subgroupOf_left I H)
      refine ⟨J, inferInstance, ?_, ?_⟩
      · rcases hstep with hIcop | hIp
        · left
          have hdiv : Nat.card ↥(H ⊓ I) ∣ Nat.card ↥I := by
            exact Subgroup.card_dvd_of_le (show H ⊓ I ≤ I from inf_le_right)
          have hcardJ : Nat.card ↥J = Nat.card ↥(H ⊓ I) := by
            calc
              Nat.card ↥J = Nat.card ↥((H ⊓ I).subgroupOf H) := by rw [← hJ_eq]
              _ = Nat.card ↥(H ⊓ I) := by
                exact
                  Nat.card_congr
                    (Subgroup.subgroupOfEquivOfLe (show H ⊓ I ≤ H from inf_le_left)).toEquiv
          exact hIcop.of_dvd_right (hcardJ ▸ hdiv)
        · right
          have hJsub : IsPGroup p ↥((H ⊓ I).subgroupOf I) := by
            exact hIp.to_subgroup ((H ⊓ I).subgroupOf I)
          have hHI : IsPGroup p ↥(H ⊓ I) := by
            exact hJsub.of_equiv
              (Subgroup.subgroupOfEquivOfLe (show H ⊓ I ≤ I from inf_le_right))
          have hJinf : IsPGroup p ↥((H ⊓ I).subgroupOf H) := by
            exact hHI.of_equiv
              (Subgroup.subgroupOfEquivOfLe (show H ⊓ I ≤ H from inf_le_left)).symm
          rw [← hJ_eq]
          exact hJinf
      · let φ : H →* G ⧸ I := (QuotientGroup.mk' I).comp H.subtype
        have hker : φ.ker = J := by
          ext x
          change (QuotientGroup.mk' I ((x : H) : G) = 1) ↔ x ∈ J
          constructor
          · intro hx
            change ((x : H) : G) ∈ I
            exact (QuotientGroup.eq_one_iff ((x : H) : G)).mp hx
          · intro hx
            exact (QuotientGroup.eq_one_iff ((x : H) : G)).mpr hx
        have hrange : φ.range = H.map (QuotientGroup.mk' I) := by
          ext q
          constructor
          · rintro ⟨x, rfl⟩
            exact Subgroup.mem_map.mpr ⟨x, x.property, rfl⟩
          · intro hq
            rcases Subgroup.mem_map.mp hq with ⟨x, hx, rfl⟩
            exact ⟨⟨x, hx⟩, rfl⟩
        have hmap : IsPSolvableOfHeight p h (H.map (QuotientGroup.mk' I)) := by
          exact ih (G := G ⧸ I) (H := H.map (QuotientGroup.mk' I)) hquot
        let e : H ⧸ J ≃* H.map (QuotientGroup.mk' I) :=
          (QuotientGroup.quotientMulEquivOfEq hker.symm).trans <|
            (QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange)
        exact IsPSolvableOfHeight.of_equiv e.symm hmap

/-- Helper for Theorem 17-17.6-1: quotienting by a normal subgroup that acts trivially preserves
irreducibility because the quotient representation has the same invariant subspaces. -/
lemma isIrreducible_of_ofQuotient_of_isTrivial_c17
    {K : Type*} [Field K] {H : Type*} [Group H] {W : Type*}
    [AddCommGroup W] [Module K W]
    (σ : Representation K H W) (S : Subgroup H) [S.Normal]
    [Representation.IsTrivial (σ.comp S.subtype)] [σ.IsIrreducible] :
    Representation.IsIrreducible (σ.ofQuotient S) := by
  classical
  letI : Nontrivial (Subrepresentation (σ.ofQuotient S)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation σ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using congrArg Subrepresentation.toSubmodule h
    exact IsSimpleOrder.bot_ne_top h'
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro W' hW'
  let W'' : Subrepresentation σ :=
    { toSubmodule := W'.toSubmodule
      apply_mem_toSubmodule := by
        intro g x hx
        simpa using W'.apply_mem_toSubmodule (g : H ⧸ S) hx }
  have hW''_ne_bot : W'' ≠ ⊥ := by
    intro hW''
    apply hW'
    apply Subrepresentation.toSubmodule_injective
    simpa [W''] using congrArg Subrepresentation.toSubmodule hW''
  have hW''_top : W'' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W'').resolve_left hW''_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [W''] using congrArg Subrepresentation.toSubmodule hW''_top

/-- Helper for Theorem 17-17.6-1: a normal `p`-subgroup acts trivially on every irreducible
representation in characteristic `p`. -/
lemma isTrivial_restrict_normal_pSubgroup_of_isIrreducible
    [Fact p.Prime]
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (I : Subgroup G) [I.Normal] (hI : IsPGroup p I) :
    Representation.IsTrivial (ρ.comp I.subtype) := by
  classical
  let ρI : Representation k I V := ρ.comp I.subtype
  letI : Nontrivial V := by
    by_contra hV
    have hV' : (⊥ : Subrepresentation ρ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      ext x
      constructor
      · intro hx
        trivial
      · intro _
        haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
        simpa using (show x = 0 from Subsingleton.elim x 0)
    exact IsSimpleOrder.bot_ne_top hV'
  let U : Subrepresentation ρ :=
    { toSubmodule := ρI.invariants
      apply_mem_toSubmodule := by
        intro g x hx
        rw [ρI.mem_invariants] at hx ⊢
        intro i
        have hconj : g⁻¹ * (i : G) * g ∈ I :=
          Subgroup.Normal.conj_mem' inferInstance (i : G) i.2 g
        have hfixed : ρ (g⁻¹ * (i : G) * g) x = x := hx ⟨g⁻¹ * (i : G) * g, hconj⟩
        calc
          ρ (i : G) (ρ g x) = ρ ((i : G) * g) x := by
            simp [map_mul]
          _ = ρ (g * (g⁻¹ * (i : G) * g)) x := by
            simp [mul_assoc]
          _ = ρ g (ρ (g⁻¹ * (i : G) * g) x) := by
            simp [map_mul]
          _ = ρ g x := by rw [hfixed] }
  have hU_ne_bot : U ≠ ⊥ := by
    intro hU
    exact
      ((invariants_ne_bot_of_isPGroup_charP ρI hI) <|
        by simpa [U] using congrArg Subrepresentation.toSubmodule hU)
  have hU_top : U = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U).resolve_left hU_ne_bot
  refine ⟨fun i ↦ ?_⟩
  ext x
  have hxU : x ∈ U.toSubmodule := by
    rw [hU_top]
    exact Submodule.mem_top
  have hxI : x ∈ ρI.invariants := by
    simpa [U] using hxU
  exact (ρI.mem_invariants x).1 hxI i

/-- Helper for Theorem 17-17.6-1: after descending along a normal subgroup acting trivially,
inflating back through the quotient map recovers the original representation. -/
lemma quotient_inflation_eq_original_of_isTrivial
    (ρ : Representation k G V) (I : Subgroup G) [I.Normal]
    [Representation.IsTrivial (ρ.comp I.subtype)] :
    ρ = (ρ.ofQuotient I).comp (QuotientGroup.mk' I) := by
  ext g x
  simp [Representation.ofQuotient_coe_apply]

/-- Helper for Theorem 17-17.6-1: once the quotient representation has a residue-field lift,
inflating that lift along the quotient map lifts the original representation whenever the kernel
acts trivially. -/
lemma exists_residueFieldLift_of_ofQuotient_of_isTrivial
    (ρ : Representation k G V) (I : Subgroup G) [I.Normal]
    [Representation.IsTrivial (ρ.comp I.subtype)]
    (hquotLift :
      ∃ (P : Type x) (_ : AddCommGroup P) (_ : Module A P)
        (_ : Module.Free A P) (_ : Module.Finite A P)
        (ρA : Representation A (G ⧸ I) P)
        (red : P →ₗ[A] V),
          IsResidueFieldLift (ρ.ofQuotient I) ρA red) :
    ∃ (P : Type x) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A G P)
      (red : P →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  rcases hquotLift with ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA, red, hLift⟩
  letI : AddCommGroup P := hPadd
  letI : Module A P := hPmod
  letI : Module.Free A P := hPfree
  letI : Module.Finite A P := hPfinite
  refine ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA.comp (QuotientGroup.mk' I), red, ?_⟩
  have hLift' :
      IsResidueFieldLift
        ((ρ.ofQuotient I).comp (QuotientGroup.mk' I))
        (ρA.comp (QuotientGroup.mk' I))
        red :=
    Representation.isResidueFieldLift_comp hLift (QuotientGroup.mk' I)
  rw [quotient_inflation_eq_original_of_isTrivial (ρ := ρ) (I := I)]
  exact hLift'

/-- Helper for Theorem 17-17.6-1: once the explicit cardinal recursion is available at height
`h + 1`, a proper subgroup inherits a smaller cardinal bound and can be handled by the same-height
recursive hypothesis. -/
lemma exists_residueFieldLift_of_isIrreducible_of_isPSolvableOfHeight_of_proper_subgroup
    {n : ℕ}
    (hrec :
      ∀ {G' : Type v} [Group G'] [Finite G']
        {V' : Type x} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
        (hG' : IsPSolvableOfHeight p (Nat.succ h) G') (hcard' : Nat.card G' ≤ n)
        (ρ' : Representation k G' V') [ρ'.IsIrreducible],
          ∃ (P : Type x) (_ : AddCommGroup P) (_ : Module A P)
            (_ : Module.Free A P) (_ : Module.Finite A P)
            (ρA : Representation A G' P)
            (red : P →ₗ[A] V'),
              IsResidueFieldLift ρ' ρA red)
    (H : Subgroup G) (hH : H < ⊤)
    {W : Type x} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (hHG : IsPSolvableOfHeight p (Nat.succ h) H)
    (σ : Representation k H W) [σ.IsIrreducible]
    (hcardG : Nat.card G ≤ n.succ) :
    ∃ (P : Type x) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A H P)
      (red : P →ₗ[A] W),
        IsResidueFieldLift σ ρA red := by
  have hcardH : Nat.card H ≤ n := by
    exact
      Nat.lt_succ_iff.mp <|
        lt_of_lt_of_le (subgroup_natCard_lt_of_ne_top_c1731 H hH.ne) hcardG
  exact @hrec H _ _ W _ _ _ hHG hcardH σ inferInstance

/-- Helper for Theorem 17-17.6-1: a proper overgroup of the Hall kernel remains proper after
passing to the quotient image, inherits the quotient-height hypothesis, and has smaller order than
the ambient group. -/
lemma proper_overgroup_quotient_data
    (I H : Subgroup G) [I.Normal] (hIH : I ≤ H) (hH : H < ⊤)
    (hquot : IsPSolvableOfHeight p h (G ⧸ I)) :
    H.map (QuotientGroup.mk' I) < ⊤ ∧
      IsPSolvableOfHeight p h (H.map (QuotientGroup.mk' I)) ∧
      Nat.card H < Nat.card G := by
  refine ⟨?_, ?_, ?_⟩
  · refine lt_top_iff_ne_top.mpr ?_
    intro htop
    have hcomap :
        Subgroup.comap (QuotientGroup.mk' I) (H.map (QuotientGroup.mk' I)) = H := by
      simpa [QuotientGroup.comap_map_mk', sup_eq_right.mpr hIH]
    have htop' : H = ⊤ := by
      calc
        H = Subgroup.comap (QuotientGroup.mk' I) (H.map (QuotientGroup.mk' I)) := hcomap.symm
        _ = Subgroup.comap (QuotientGroup.mk' I) ⊤ := by simpa [htop]
        _ = ⊤ := by
          ext g
          simp
    exact hH.ne htop'
  · exact isPSolvableOfHeight_of_subgroup (H := H.map (QuotientGroup.mk' I)) hquot
  · exact subgroup_natCard_lt_of_ne_top_c1731 H hH.ne

/-- Helper for Theorem 17-17.6-1: if `I ≤ H` has order prime to `p` and the quotient image of
`H` in `G ⧸ I` has height `h`, then `H` itself has height `h + 1`. -/
lemma isPSolvableOfHeight_succ_of_normal_coprime_subgroup_and_quotient_map
    (I H : Subgroup G) [I.Normal] (hIH : I ≤ H)
    (hIcop : Nat.Coprime p (Nat.card I))
    (hquot : IsPSolvableOfHeight p h (H.map (QuotientGroup.mk' I))) :
    IsPSolvableOfHeight p (Nat.succ h) H := by
  let J : Subgroup H := I.subgroupOf H
  letI : J.Normal := by infer_instance
  have hcardJ : Nat.card J = Nat.card I := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIH).toEquiv
  let φ : H →* G ⧸ I := (QuotientGroup.mk' I).comp H.subtype
  have hker : φ.ker = J := by
    ext x
    change (QuotientGroup.mk' I ((x : H) : G) = 1) ↔ x ∈ J
    constructor
    · intro hx
      change ((x : H) : G) ∈ I
      exact (QuotientGroup.eq_one_iff ((x : H) : G)).mp hx
    · intro hx
      exact (QuotientGroup.eq_one_iff ((x : H) : G)).mpr hx
  have hrange : φ.range = H.map (QuotientGroup.mk' I) := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact Subgroup.mem_map.mpr ⟨x, x.property, rfl⟩
    · intro hq
      rcases Subgroup.mem_map.mp hq with ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  let e : H ⧸ J ≃* H.map (QuotientGroup.mk' I) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans <|
      (QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange)
  have hquotJ : IsPSolvableOfHeight p h (H ⧸ J) := by
    exact IsPSolvableOfHeight.of_equiv e.symm hquot
  exact
    IsPSolvableOfHeight.succ_iff.mpr
      ⟨J, inferInstance, Or.inl (by
        rw [hcardJ]
        exact hIcop), hquotJ⟩

end

end Representation
