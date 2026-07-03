import Mathlib
import Serre.Chap09.Proposition_9_9_4_2
import Serre.Chap09.Theorem_9_9_2_1
import Serre.Chap11.Theorem_11_11_1_2
import Serre.Chap11.Theorem_11_11_2_2

-- Stable cyclic restriction helpers extracted from Exercise 11-11.2-7.

noncomputable section

universe u v

namespace Representation

open scoped BigOperators Representation SubgroupInduction

section FrobeniusTheorem

variable {G : Type} [Group G] [Finite G]

/-- A subgroup of a finite group is finite. -/
local instance cyclicPowerInvariantFintypeSubgroup (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

/-- Conjugacy classes in a finite group form a finite type. -/
local instance cyclicPowerInvariantFintypeConjClasses
    (H : Type*) [Group H] [Finite H] : Fintype (ConjClasses H) :=
  Fintype.ofFinite (ConjClasses H)

/-- Equality of subgroups is decidable by classical choice in this file-local proof environment. -/
local instance cyclicPowerInvariantDecidableEqSubgroup
    (H : Type*) [Group H] : DecidableEq (Subgroup H) :=
  Classical.decEq _

/-- Helper for Exercise 11-11.2-7: on a cyclic subgroup, the indicator of a fixed generator
stratum belongs to the rational scalar extension of the character ring. -/
lemma generator_stratum_indicator_mem_characterRingScalarExtension
    {H : Subgroup G} (hcyc : IsCyclic H) (J : Subgroup H) :
    (fun x : H ↦ if Subgroup.zpowers x = J then (1 : ℂ) else 0) ∈
      characterRingScalarExtension ℚ H := by
  classical
  let _ : CommGroup H := IsCyclic.commGroup
  let _ : Fintype J := Fintype.ofFinite J
  let _ : IsCyclic H := hcyc
  let _ : IsCyclic J := by infer_instance
  have hcardJ_ne : (Nat.card J : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have htheta : (θ[J] : J → ℂ) ∈ R(J) := by
    simpa using (Representation.cyclicGroupTheta_mem_characterRing (A := J))
  have hind : Ind[J]((θ[J] : J → ℂ)) ∈ R(H) := by
    exact
      _root_.Subgroup.inducedClassFunction_mem_characterRingOverField (K := ℂ) J
        ⟨(θ[J] : J → ℂ), htheta⟩
  have hscalar : Ind[J]((θ[J] : J → ℂ)) ∈ characterRingScalarExtension ℚ H := by
    exact mem_characterRingScalarExtension_of_mem_characterRing (A := ℚ) _ hind
  have hpoint :
      (fun x : H ↦ if Subgroup.zpowers x = J then (1 : ℂ) else 0) =
        (((Nat.card H : ℚ)⁻¹) : ℚ) • Ind[J]((θ[J] : J → ℂ)) := by
    funext x
    by_cases hxJ : x ∈ J
    · by_cases hgen : Subgroup.zpowers x = J
      · have hind_x : Ind[J]((θ[J] : J → ℂ)) x = Nat.card H := by
          rw [Subgroup.inducedClassFunction]
          simp [hxJ, Representation.cyclicGroupTheta, subgroup_zpowers_eq_top_iff, hgen,
            mul_assoc, hcardJ_ne]
          field_simp [hcardJ_ne]
        simp [hgen, hind_x, Pi.smul_apply, Algebra.smul_def]
      · have hind_x : Ind[J]((θ[J] : J → ℂ)) x = 0 := by
          rw [Subgroup.inducedClassFunction]
          simp [hxJ, Representation.cyclicGroupTheta, subgroup_zpowers_eq_top_iff, hgen,
            mul_assoc]
        simp [hgen, hind_x, Pi.smul_apply, Algebra.smul_def]
    · have hind_x : Ind[J]((θ[J] : J → ℂ)) x = 0 := by
        rw [Subgroup.inducedClassFunction]
        simp [hxJ, mul_comm, mul_left_comm, mul_assoc]
      have hgen : Subgroup.zpowers x ≠ J := by
        intro hEq
        exact hxJ (hEq ▸ Subgroup.mem_zpowers x)
      simp [hgen, hind_x, Pi.smul_apply, Algebra.smul_def]
  simpa [hpoint] using
    (characterRingScalarExtension ℚ H).smul_mem (((Nat.card H : ℚ)⁻¹) : ℚ) hscalar

/-- Helper for Exercise 11-11.2-7: on a finite subgroup, the ambient power-invariance hypothesis
forces a rational class function to be constant on each cyclic-generator stratum. -/
lemma power_invariant_eq_of_same_zpowers
    {H : Subgroup G} (φ : classFunctionSubmodule ℚ H)
    (hpow :
      ∀ x : H, ∀ m : ℕ, Nat.Coprime m (Nat.card G) → φ (x ^ m) = φ x)
    {x y : H} (hxy : Subgroup.zpowers x = Subgroup.zpowers y) :
    φ x = φ y := by
  classical
  have hy_mem : y ∈ Subgroup.zpowers x := by
    simp [hxy]
  rw [mem_zpowers_iff_mem_range_orderOf] at hy_mem
  simp only [Finset.mem_image, Finset.mem_range] at hy_mem
  rcases hy_mem with ⟨k, hklt, hyk⟩
  have hx_mem_y : x ∈ Subgroup.zpowers y := by
    simpa [hxy] using (show x ∈ Subgroup.zpowers x by exact Subgroup.mem_zpowers x)
  have hx_mem : x ∈ Subgroup.zpowers (x ^ k) := by
    simpa [hyk] using hx_mem_y
  have hk_coprime_ord : Nat.Coprime k (orderOf x) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    exact mem_zpowers_pow_iff.mp hx_mem
  obtain ⟨m, hmgt, hmprime, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (Nat.card G) (q := orderOf x) (a := k)
      (Nat.ne_of_gt (orderOf_pos x)) hk_coprime_ord
  have hm_coprime : Nat.Coprime m (Nat.card G) := by
    rw [hmprime.coprime_iff_not_dvd]
    intro hdiv
    have hle : m ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos hdiv
    exact Nat.not_lt_of_ge hle hmgt
  have hym : y = x ^ m := by
    have hmk : m % orderOf x = k % orderOf x := by
      simpa [Nat.ModEq] using hmod
    calc
      y = x ^ k := by simpa using hyk.symm
      _ = x ^ m := by
        rw [← pow_mod_orderOf x k, ← pow_mod_orderOf x m, hmk]
  calc
    φ x = φ (x ^ m) := by symm; exact hpow x m hm_coprime
    _ = φ y := by simpa [hym]

/-- Helper for Exercise 11-11.2-7: the cyclic case of the rational power-invariance criterion,
stated with the ambient prime-to-`|G|` invariance that is inherited directly by subgroup
restrictions. -/
lemma cyclic_power_invariant_mem_characterRingScalarExtension
    {H : Subgroup G} (hcyc : IsCyclic H) (φ : classFunctionSubmodule ℚ H)
    (hpow :
      ∀ x : H, ∀ m : ℕ, Nat.Coprime m (Nat.card G) → φ (x ^ m) = φ x) :
    (fun x ↦ algebraMap ℚ ℂ (φ x)) ∈ characterRingScalarExtension ℚ H := by
  classical
  let _ : Fintype (Subgroup H) := Fintype.ofFinite (Subgroup H)
  let _ : IsCyclic H := hcyc
  have hrepr_exists : ∀ J : Subgroup H, ∃ x : H, Subgroup.zpowers x = J := by
    intro J
    let _ : IsCyclic J := by infer_instance
    obtain ⟨x, hx⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top J).1 inferInstance
    exact ⟨x, hx⟩
  let repr : Subgroup H → H := fun J ↦ Classical.choose (hrepr_exists J)
  let a : Subgroup H → ℚ := fun J ↦ φ (repr J)
  have hrepr : ∀ J : Subgroup H, Subgroup.zpowers (repr J) = J := by
    intro J
    exact Classical.choose_spec (hrepr_exists J)
  have hsum :
      (∑ J : Subgroup H,
          a J • (fun x : H ↦ if Subgroup.zpowers x = J then (1 : ℂ) else 0) : H → ℂ) =
        fun x : H ↦ algebraMap ℚ ℂ (φ x) := by
    funext x
    have hcoeff :
        algebraMap ℚ ℂ (a (Subgroup.zpowers x)) = algebraMap ℚ ℂ (φ x) := by
      have hsame : φ (repr (Subgroup.zpowers x)) = φ x :=
        power_invariant_eq_of_same_zpowers (G := G) (φ := φ) hpow
          (x := repr (Subgroup.zpowers x)) (y := x) <| by
            simpa [hrepr]
      simpa [a] using congrArg (algebraMap ℚ ℂ) hsame
    calc
      (∑ J : Subgroup H,
          a J • (fun y : H ↦ if Subgroup.zpowers y = J then (1 : ℂ) else 0) : H → ℂ) x
          = ∑ J : Subgroup H,
              algebraMap ℚ ℂ (a J) *
                (if Subgroup.zpowers x = J then (1 : ℂ) else 0) := by
              simp [Pi.smul_apply, Algebra.smul_def]
      _ = algebraMap ℚ ℂ (a (Subgroup.zpowers x)) := by
            rw [Finset.sum_eq_single (Subgroup.zpowers x)]
            · simp
            · intro J _ hJ
              have hxJ : Subgroup.zpowers x ≠ J := by
                intro hEq
                exact hJ hEq.symm
              simp [hxJ]
            · simp
      _ = algebraMap ℚ ℂ (φ x) := hcoeff
  rw [← hsum]
  refine Submodule.sum_mem (characterRingScalarExtension ℚ H) ?_
  intro J hJ
  exact (characterRingScalarExtension ℚ H).smul_mem _ <|
    generator_stratum_indicator_mem_characterRingScalarExtension (G := G) hcyc J

/-- Helper for Exercise 11-11.2-7: restricting a rational-valued bundled class function to a
subgroup preserves the class-function condition. -/
lemma rat_classFunctionRestriction_mem
    (H : Subgroup G) (f : classFunctionSubmodule ℚ G) :
    (fun h : H ↦ f h) ∈ classFunctionSubmodule ℚ H := by
  let hf : _root_.IsClassFunction (f : G → ℚ) := (mem_classFunctionSubmodule_iff ℚ _).1 f.2
  refine (mem_classFunctionSubmodule_iff ℚ _).2 ?_
  refine ⟨fun {x y} hxy ↦ ?_⟩
  have hxyH : IsConj x y := (ConjClasses.mk_eq_mk_iff_isConj).1 hxy
  have hxyG : IsConj (x : G) (y : G) := by
    rw [isConj_iff] at hxyH ⊢
    rcases hxyH with ⟨c, hc⟩
    exact ⟨(c : G), by simpa using congrArg Subtype.val hc⟩
  exact hf.eq_of_isConj hxyG

/-- Helper for Exercise 11-11.2-7: subgroup restriction of a rational-valued bundled class
function. -/
def rat_classFunctionRestriction
    (H : Subgroup G) (f : classFunctionSubmodule ℚ G) :
    classFunctionSubmodule ℚ H :=
  ⟨fun h ↦ f h, rat_classFunctionRestriction_mem (G := G) H f⟩

end FrobeniusTheorem

end Representation
