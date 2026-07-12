import Mathlib
import LinearRepresentations_Serre_1977.Chap12.Lemma_12_12_7_4
import LinearRepresentations_Serre_1977.Chap12.Lemma_12_12_7_6.OrbitSupportedLift
import LinearRepresentations_Serre_1977.Chap12.Lemma_12_12_7_5.AssociatedElementaryCore

noncomputable section

open Representation
open PrimeSpectrum
open scoped Representation SubgroupInduction

universe u v w

namespace Representation

open IsCyclotomicExtension.Rat

section

variable {G : Type u} [Group G] [Finite G]
variable {A : Type v} [CommRing A] [IsDomain A]
variable {L : Type w} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
variable (K : IntermediateField ℚ L)
variable [Algebra A K] [IsFractionRing A K]
variable {p : ℕ} [Fact p.Prime]

local instance instFintypeAmbientGroupAssociatedSubgroupBridge : Fintype G := Fintype.ofFinite G
local instance instFintypeSubgroupAssociatedSubgroupBridge
    {H : Type*} [Group H] [Finite H] (S : Subgroup H) : Fintype S := Fintype.ofFinite S
attribute [local instance] Classical.propDecidable
local notation "ΓK" => Γ[K](G)

omit [Fact p.Prime] in
/-- Helper for Lemma 12-12.7-6: the source element `x` lies in the associated subgroup
`H = ⟨x⟩ ⋅ P`. -/
lemma associatedGammaPElementary_generator_mem
    (x : G) (P : Sylow p N[ΓK](x)) :
    x ∈ associatedGammaPElementarySubgroup ΓK x P := by
  exact zpowers_le_associatedGammaPElementarySubgroup ΓK p x P <|
    Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩

omit [Fact p.Prime] in
/-- Helper for Lemma 12-12.7-6: the cyclic factor `⟨x⟩` viewed inside the associated subgroup has
cardinality `orderOf x`. -/
lemma associatedGammaPElementary_zpowers_card_eq_orderOf
    (x : G) (P : Sylow p N[ΓK](x)) :
    Nat.card
        ((Subgroup.zpowers x).subgroupOf (associatedGammaPElementarySubgroup ΓK x P)) =
      orderOf x := by
  let H := associatedGammaPElementarySubgroup ΓK x P
  have hz : Subgroup.zpowers x ≤ H := zpowers_le_associatedGammaPElementarySubgroup ΓK p x P
  simpa [H] using
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hz).toEquiv).trans (Nat.card_zpowers x)

/-- Helper for Lemma 12-12.7-6: an element of `N[ΓK](x)` conjugates every element of `⟨x⟩` by the
same `Γ_K`-power that it uses on the generator `x`. -/
lemma gammaNormalizer_conjugates_zpowers_by_power_local
    (x y : G) (hy : y ∈ N[ΓK](x)) :
    ∃ t : ΓK, ∀ c : Subgroup.zpowers x, y * (c : G) * y⁻¹ = (c : G) ^ t := by
  rcases hy with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  intro c
  rcases Subgroup.mem_zpowers_iff.mp c.2 with ⟨n, hn⟩
  rw [hn.symm]
  calc
    y * (x ^ n) * y⁻¹ = (y * x * y⁻¹) ^ n := by
      simpa using (conj_zpow (a := y) (b := x) (i := n)).symm
    _ = (x ^ t) ^ n := by rw [ht]
    _ = x ^ (n * galoisPowerExponentUnit (t : (ZMod (Monoid.exponent G))ˣ)) := by
      rw [pow_subgroup_eq_pow_nat]
      rw [← zpow_natCast]
      simpa using
        (zpow_mul' x n (galoisPowerExponentUnit (t : (ZMod (Monoid.exponent G))ˣ) : ℤ)).symm
    _ = (x ^ n) ^ galoisPowerExponentUnit (t : (ZMod (Monoid.exponent G))ˣ) := by
      rw [← zpow_natCast]
      simpa using
        (zpow_mul x n (galoisPowerExponentUnit (t : (ZMod (Monoid.exponent G))ˣ) : ℤ))
    _ = (x ^ n) ^ t := by
      exact (pow_subgroup_eq_pow_nat (G := G) (s := x ^ n) t).symm

omit [Fact p.Prime] in
/-- Helper for Lemma 12-12.7-6: inside `H = associatedGammaPElementarySubgroup ΓK x P`, the
cyclic factor `⟨x⟩` is normal because the `P`-factor acts on it by `Γ_K`-power automorphisms. -/
lemma associatedGammaPElementary_zpowers_normal
    (x : G) (P : Sylow p N[ΓK](x)) :
    let H := associatedGammaPElementarySubgroup ΓK x P
    ((Subgroup.zpowers x).subgroupOf H).Normal := by
  dsimp
  let Pimg : Subgroup G := Subgroup.map N[ΓK](x).subtype (P : Subgroup N[ΓK](x))
  have hPimg_normalizes : Pimg ≤ Subgroup.normalizer (Subgroup.zpowers x) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    rcases Subgroup.mem_map.mp hy with ⟨z, hzP, rfl⟩
    rcases gammaNormalizer_conjugates_zpowers_by_power_local (K := K) x z.1 z.2 with ⟨t, ht⟩
    intro c
    constructor
    · intro hc
      have hpow : N[ΓK](x).subtype z * c * (N[ΓK](x).subtype z)⁻¹ = c ^ t := by
        simpa using ht ⟨c, hc⟩
      rw [hpow, pow_subgroup_eq_pow_nat]
      exact Subgroup.pow_mem (Subgroup.zpowers x) hc _
    · intro hc
      have hz_inv : z.1⁻¹ ∈ N[ΓK](x) := (N[ΓK](x)).inv_mem z.2
      rcases gammaNormalizer_conjugates_zpowers_by_power_local (K := K) x z.1⁻¹ hz_inv with
          ⟨t, htInv⟩
      have hconjInv :
          (N[ΓK](x).subtype z)⁻¹ * (N[ΓK](x).subtype z * c * (N[ΓK](x).subtype z)⁻¹) *
              ((N[ΓK](x).subtype z)⁻¹)⁻¹ =
            (N[ΓK](x).subtype z * c * (N[ΓK](x).subtype z)⁻¹) ^ t := by
        simpa using htInv ⟨N[ΓK](x).subtype z * c * (N[ΓK](x).subtype z)⁻¹, hc⟩
      have hpow : c = (N[ΓK](x).subtype z * c * (N[ΓK](x).subtype z)⁻¹) ^ t := by
        calc
          c =
              (N[ΓK](x).subtype z)⁻¹ * (N[ΓK](x).subtype z * c * (N[ΓK](x).subtype z)⁻¹) *
                ((N[ΓK](x).subtype z)⁻¹)⁻¹ := by
              group
          _ = (N[ΓK](x).subtype z * c * (N[ΓK](x).subtype z)⁻¹) ^ t := hconjInv
      rw [hpow, pow_subgroup_eq_pow_nat]
      exact Subgroup.pow_mem (Subgroup.zpowers x) hc _
  have hH_normalizes :
      associatedGammaPElementarySubgroup ΓK x P ≤ Subgroup.normalizer (Subgroup.zpowers x) := by
    simpa [associatedGammaPElementarySubgroup, Pimg] using
      sup_le Subgroup.le_normalizer hPimg_normalizes
  simpa [associatedGammaPElementarySubgroup] using
    (Subgroup.normal_subgroupOf_of_le_normalizer hH_normalizes)

/-- Helper for Lemma 12-12.7-6: every `p`-regular element of
`associatedGammaPElementarySubgroup ΓK x P` already lies in the cyclic factor `⟨x⟩`. -/
lemma pregular_eq_inclusion_zpowers_of_mem_associatedGammaPElementarySubgroup
    (x : G) (hx : IsPRegular p x) (P : Sylow p N[ΓK](x)) :
    let H := associatedGammaPElementarySubgroup ΓK x P
    let hC : Subgroup.zpowers x ≤ H := zpowers_le_associatedGammaPElementarySubgroup ΓK p x P
    ∀ h : H, IsPRegular p h.1 → ∃ c : Subgroup.zpowers x, Subgroup.inclusion hC c = h := by
  classical
  dsimp
  let H := associatedGammaPElementarySubgroup ΓK x P
  let C₀ : Subgroup H := (Subgroup.zpowers x).subgroupOf H
  let Pimg : Subgroup G := Subgroup.map N[ΓK](x).subtype (P : Subgroup N[ΓK](x))
  let P₀ : Subgroup H := Pimg.subgroupOf H
  let hC : Subgroup.zpowers x ≤ H := zpowers_le_associatedGammaPElementarySubgroup ΓK p x P
  have hdecomp :
      Subgroup.IsGammaPElementaryDecomposition ΓK p C₀ P₀ :=
    associatedGammaPElementarySubgroup_decomposition ΓK p x hx P
  haveI : C₀.Normal := by
    simpa [H, C₀] using associatedGammaPElementary_zpowers_normal (K := K) (p := p) x P
  have hquotP : IsPGroup p (H ⧸ C₀) := by
    let e : H ⧸ C₀ ≃* P₀ := hdecomp.isComplement.symm.QuotientMulEquiv
    exact hdecomp.isPGroup.of_equiv e.symm
  intro h hh
  have hhH : IsPRegular p h := by
    simpa [IsPRegular, Subgroup.orderOf_mk] using hh
  have hq_order : orderOf (QuotientGroup.mk' C₀ h : H ⧸ C₀) = 1 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hquotP) (QuotientGroup.mk' C₀ h)
    have hq_dvd : p ^ n ∣ orderOf h := by
      exact hn ▸ orderOf_map_dvd (QuotientGroup.mk' C₀) h
    exact hn.trans (Nat.Coprime.eq_one_of_dvd (hhH.pow_left n) hq_dvd)
  have hq_one : (QuotientGroup.mk' C₀ h : H ⧸ C₀) = 1 := orderOf_eq_one_iff.mp hq_order
  have hhker : h ∈ (QuotientGroup.mk' C₀).ker := by
    change QuotientGroup.mk' C₀ h = 1
    exact hq_one
  have hhC₀_subgroupOf : h ∈ C₀ := by
    simpa [QuotientGroup.ker_mk'] using hhker
  have hhC₀ : h.1 ∈ Subgroup.zpowers x := by
    simpa [C₀] using hhC₀_subgroupOf
  refine ⟨⟨h.1, hhC₀⟩, ?_⟩
  exact Subtype.ext rfl

end

end Representation
