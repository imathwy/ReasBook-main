import Mathlib
import LinearRepresentations_Serre_1977.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.GroupTheory.PSolvable
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_1_3
import LinearRepresentations_Serre_1977.Chap07.Remark_7_7_1_4
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_5_3
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CyclicNormalByPGroupBasics
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CliffordIsotypicTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ResidueFieldLiftTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ProperOvergroupRecursion
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CyclicOrbitSpan
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.SameUniverseInductionPackaging
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.InducedSubrepresentationLift
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_6_1.HallKernelOwnerTransport

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
private noncomputable instance hallKernelCliffordSplitModule : Module A V :=
  Module.compHom V (algebraMap A k)
private instance hallKernelCliffordSplitScalarTower : IsScalarTower A k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.6-1: when a normal subgroup has order prime to the residue
characteristic, the restricted module is semisimple over its monoid algebra. -/
lemma isSemisimpleModule_restrict_of_coprime_card
    (hp : Nat.Prime p) (I : Subgroup G) (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V) :
    let ρI : Representation k I V := ρ.comp I.subtype
    letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
    IsSemisimpleModule (MonoidAlgebra k I) V := by
  let ρI : Representation k I V := ρ.comp I.subtype
  letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
  letI : NeZero (Nat.card I : k) := by
    exact NeZero.of_not_dvd k (hp.coprime_iff_not_dvd.mp hIcop)
  infer_instance

/-- Helper for Theorem 17-17.6-1: each element of the normal Hall kernel stabilizes any chosen
restricted isotypic component. -/
lemma stabilizer_contains_subgroup_of_isotypic_component
    (ρ : Representation k G V) (I : Subgroup G) [I.Normal] :
    let ρI : Representation k I V := ρ.comp I.subtype
    letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
    ∀ c : isotypicComponents (MonoidAlgebra k I) V,
      I ≤ ρ.submoduleStabilizer ((Subrepresentation.ofSubmodule' c.1).toSubmodule) := by
  intro ρI
  letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
  intro c a ha
  let aI : I := ⟨a, ha⟩
  let W : Subrepresentation ρI := Subrepresentation.ofSubmodule' c.1
  rw [mem_submoduleStabilizer_iff_map_eq]
  apply le_antisymm
  · intro x hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
    simpa [W] using W.apply_mem_toSubmodule aI hy
  · intro x hx
    refine Submodule.mem_map.mpr ⟨ρ aI⁻¹ x, ?_, ?_⟩
    · simpa [W] using W.apply_mem_toSubmodule aI⁻¹ hx
    · calc
        ρ a (ρ aI⁻¹ x) = ρ ((a : G) * (aI⁻¹ : I)) x := by
          exact (LinearMap.congr_fun (ρ.map_mul (a : G) (aI⁻¹ : I)) x).symm
        _ = x := by
          simp [aI]

/-- Helper for Theorem 17-17.6-1: semisimplicity of the Hall-kernel restriction gives Serre's
Clifford split between induction from a proper overgroup and isotypy of the restriction. -/
theorem exists_proper_overgroup_irreducible_induced_or_restriction_isotypic_of_semisimple_restriction
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (hsemisimple :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      IsSemisimpleModule (MonoidAlgebra k I) V) :
    (∃ H : Subgroup G,
      I ≤ H ∧ H < ⊤ ∧
        ∃ W : Subrepresentation (ρ.comp H.subtype),
          W.toRepresentation.IsIrreducible ∧ ρ.IsInducedFromSubrepresentation H W) ∨
      (let ρI : Representation k I V := ρ.comp I.subtype
       letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
       IsIsotypic (MonoidAlgebra k I) V) := by
  classical
  let ρI : Representation k I V := ρ.comp I.subtype
  letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
  letI : IsSemisimpleModule (MonoidAlgebra k I) V := hsemisimple
  letI : Finite I := by infer_instance
  by_cases hsub : Subsingleton (isotypicComponents (MonoidAlgebra k I) V)
  · right
    simpa [ρI] using
      isIsotypic_of_subsingleton_isotypicComponents
        (R := MonoidAlgebra k I) (M := V) hsub
  · let J := isotypicComponents (MonoidAlgebra k I) V
    let W : J → Submodule k V := fun c ↦ (Subrepresentation.ofSubmodule' c.1).toSubmodule
    letI : MulAction G J :=
      { smul := fun g c ↦
          ⟨(transportedSubrepresentation ρ (Subrepresentation.ofSubmodule' c.1) g).asSubmodule,
            transported_isotypic_component_mem_of_semisimple_restriction ρ hsemisimple c g⟩
        one_smul := by
          intro c
          apply Subtype.ext
          ext v
          constructor
          · intro hv
            rcases Submodule.mem_map.mp hv with ⟨w, hw, rfl⟩
            simpa using hw
          · intro hv
            refine Submodule.mem_map.mpr ⟨v, hv, ?_⟩
            simpa using (LinearMap.congr_fun ρ.map_one v).symm
        mul_smul := by
          intro g h c
          apply Subtype.ext
          ext v
          constructor
          · intro hv
            rcases Submodule.mem_map.mp hv with ⟨w, hw, hwv⟩
            refine Submodule.mem_map.mpr ⟨ρ h w, ?_, ?_⟩
            · exact Submodule.mem_map.mpr ⟨w, hw, rfl⟩
            · simpa [LinearMap.comp_apply] using hwv
          · intro hv
            rcases Submodule.mem_map.mp hv with ⟨w, hw, hwv⟩
            rcases Submodule.mem_map.mp hw with ⟨u, hu, rfl⟩
            refine Submodule.mem_map.mpr ⟨u, hu, ?_⟩
            simpa [LinearMap.comp_apply] using hwv }
    have hperm : ρ.PermutesSubmoduleFamily W := by
      intro g c
      rfl
    have hcomponents :
        iSupIndep W ∧ (⨆ c : J, W c) = ⊤ := by
      exact
        iSupIndep_and_iSup_top_of_subtype_ofSubmodule'_family_c17 (ρH := ρI)
          (s := isotypicComponents (MonoidAlgebra k I) V)
          (hs_indep := sSupIndep_isotypicComponents (MonoidAlgebra k I) V)
          (hs_top := sSup_isotypicComponents (MonoidAlgebra k I) V)
    have hindep : iSupIndep W := hcomponents.1
    have hspan : (⨆ c : J, W c) = ⊤ := hcomponents.2
    have hne : ∀ c : J, W c ≠ ⊥ := fun c ↦ by
      intro hbot
      apply (bot_lt_isotypicComponents c.2).ne'
      ext x
      change x ∈ c.1 ↔ x ∈ (⊥ : Submodule (MonoidAlgebra k I) V)
      simpa [W] using congrArg (fun S : Submodule k V ↦ x ∈ S) hbot
    letI : MulAction.IsPretransitive G J :=
      Representation.IsIrreducible.isPretransitive_of_permuted_internalSummands
        ρ W hindep hperm hne
    letI : Nontrivial J := not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨c₀, c₁, hc_ne⟩ := exists_pair_ne J
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G c₀ c₁
    let H : Subgroup G := ρ.submoduleStabilizer (W c₀)
    have hI_le_H : I ≤ H := by
      simpa [H, W] using
        stabilizer_contains_subgroup_of_isotypic_component
          (ρ := ρ) (I := I) c₀
    have hH_ne_top : H ≠ ⊤ := by
      intro htop
      have hg_mem : g ∈ H := by simpa [H, htop]
      have hW_eq : W c₁ = W c₀ := by
        calc
          W c₁ = W (g • c₀) := by simpa [hg]
          _ = (W c₀).map (ρ g) := (hperm g c₀).symm
          _ = W c₀ := (mem_submoduleStabilizer_iff_map_eq ρ (W c₀)).mp hg_mem
      have hc_eq : c₀.1 = c₁.1 := by
        ext x
        change x ∈ c₀.1 ↔ x ∈ c₁.1
        simpa [W] using congrArg (fun S : Submodule k V ↦ x ∈ S) hW_eq.symm
      exact hc_ne (Subtype.ext hc_eq)
    have hH_lt : H < ⊤ := lt_top_iff_ne_top.mpr hH_ne_top
    have hIndW :
        ρ.IsInducedFromSubrepresentation H (ρ.stabilizedSubrepresentation (W c₀)) := by
      simpa [H, W] using
        Representation.IsIrreducible.isInducedFromStabilizer_of_permuted_internalSummands
          ρ W c₀ hindep hspan hperm hne
    let ρH : Representation k H V := ρ.comp H.subtype
    have hW₀_ne :
        (ρ.stabilizedSubrepresentation (W c₀)).asSubmodule ≠ ⊥ := by
      intro hbot
      have hbot_to :
          (ρ.stabilizedSubrepresentation (W c₀)).toSubmodule = ⊥ := by
        ext v
        change v ∈ (ρ.stabilizedSubrepresentation (W c₀)).asSubmodule ↔
            v ∈ (⊥ : Submodule (MonoidAlgebra k H) ρH.asModule)
        rw [hbot]
      exact hne c₀ <| by simpa [H, W] using hbot_to
    obtain ⟨U, hU_le, hU_ne, hU_irred⟩ :=
      exists_irreducible_subrepresentation_le_of_nonzero
        ρH (ρ.stabilizedSubrepresentation (W c₀)) hW₀_ne
    have hIndU : ρ.IsInducedFromSubrepresentation H U :=
      isInducedFromSubrepresentation_of_nonzero_le ρ hU_le hU_ne hIndW
    left
    exact ⟨H, hI_le_H, hH_lt, U, hU_irred, hIndU⟩

end

end Representation
