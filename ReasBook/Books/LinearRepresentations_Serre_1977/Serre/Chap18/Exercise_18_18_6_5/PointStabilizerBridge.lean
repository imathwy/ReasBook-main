import Mathlib
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_4
-- `a4_quotient_by_kleinFour_card` is owned (public) by Exercise 12.2.3; the copy in 12.2.4 is
-- privatized (dedup), so import the owner to consume it here.
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_3

noncomputable section

open scoped BigOperators
open Representation

local notation "A5" => alternatingGroup (Fin 5)
local notation "A4" => alternatingGroup (Fin 4)
local notation "V4" => alternatingGroup.kleinFour (Fin 4)

local instance : Fintype A4 := Fintype.ofFinite A4

local instance : (V4).Normal :=
  alternatingGroup.normal_kleinFour (show Nat.card (Fin 4) = 4 by simp)

namespace OrdinaryIrreducible

/-- Helper for Exercise 18-18.6-5: the four-point complement of `0` in `Fin 5`. -/
private def pointComplementZero : Finset (Fin 5) :=
  Finset.univ.erase 0

/-- Helper for Exercise 18-18.6-5: membership in the complement of `0` is the expected inequality.
-/
private theorem mem_pointComplementZero_iff (x : Fin 5) :
    x ∈ pointComplementZero ↔ x ≠ 0 := by
  simp [pointComplementZero]

/-- Helper for Exercise 18-18.6-5: identify `Fin 4` with the four-point complement of `0` in
`Fin 5`. -/
private def pointComplementZeroEquiv : Fin 4 ≃ pointComplementZero := by
  simpa [pointComplementZero] using (finSuccAboveEquiv (0 : Fin 5))

/-- Helper for Exercise 18-18.6-5: extend an even permutation of the four-point complement by the
identity on `0`. -/
private def point_stabilizer_zero_to_a5 : A4 →* A5 := by
  exact
    (alternatingGroup.ofSubtype pointComplementZero).comp
      (Equiv.altCongrHom pointComplementZeroEquiv).toMonoidHom

/-- Helper for Exercise 18-18.6-5: the extension from the four-point complement fixes `0`, so it
lands in the point stabilizer. -/
private theorem point_stabilizer_zero_to_a5_mem_stabilizer (σ : A4) :
    point_stabilizer_zero_to_a5 σ ∈ MulAction.stabilizer A5 (0 : Fin 5) := by
  -- Elements coming from `ofSubtype` have support away from `0`, hence they fix `0`.
  rw [MulAction.mem_stabilizer_iff]
  change ((point_stabilizer_zero_to_a5 σ : A5) : Equiv.Perm (Fin 5)) 0 = 0
  have hsupp :
      (((point_stabilizer_zero_to_a5 σ : A5) : Equiv.Perm (Fin 5)).support) ⊆
        pointComplementZero := by
    have hmem : point_stabilizer_zero_to_a5 σ ∈
        (alternatingGroup.ofSubtype pointComplementZero).range := by
      exact ⟨(Equiv.altCongrHom pointComplementZeroEquiv) σ, by
        simp [point_stabilizer_zero_to_a5]⟩
    exact
      (alternatingGroup.mem_range_ofSubtype_iff pointComplementZero
        (point_stabilizer_zero_to_a5 σ)).1 hmem
  have hnot :
      0 ∉ (((point_stabilizer_zero_to_a5 σ : A5) : Equiv.Perm (Fin 5)).support) := by
    intro h0
    exact (mem_pointComplementZero_iff 0).1 (hsupp h0) rfl
  simpa [Equiv.Perm.mem_support] using hnot

/-- Helper for Exercise 18-18.6-5: the point stabilizer of `0` is obtained by extending even
permutations of the complementary four points. -/
private def point_stabilizer_zero_to_stabilizer :
    A4 →* MulAction.stabilizer A5 (0 : Fin 5) where
  toFun σ := ⟨point_stabilizer_zero_to_a5 σ, point_stabilizer_zero_to_a5_mem_stabilizer σ⟩
  map_one' := by
    ext
    simp [point_stabilizer_zero_to_a5]
  map_mul' σ τ := by
    ext
    simp [point_stabilizer_zero_to_a5]

/-- Helper for Exercise 18-18.6-5: the point stabilizer of `0` in `A₅` is canonically
isomorphic to `A₄`. -/
noncomputable def point_stabilizer_zero_mulEquiv_a4 :
    MulAction.stabilizer A5 (0 : Fin 5) ≃* A4 := by
  let φ : A4 →* MulAction.stabilizer A5 (0 : Fin 5) := point_stabilizer_zero_to_stabilizer
  have hbij : Function.Bijective φ := by
    constructor
    · intro σ τ hστ
      -- Injectivity reduces to injectivity of `alternatingGroup.ofSubtype`.
      have hofSubtype_injective :
          Function.Injective (alternatingGroup.ofSubtype pointComplementZero) := by
        intro a b hab
        apply Subtype.ext
        exact Equiv.Perm.ofSubtype_injective <|
          congrArg (fun k : A5 => ((k : A5) : Equiv.Perm (Fin 5))) hab
      apply (Equiv.altCongrHom pointComplementZeroEquiv).injective
      apply hofSubtype_injective
      simpa [φ, point_stabilizer_zero_to_stabilizer, point_stabilizer_zero_to_a5] using
        congrArg Subtype.val hστ
    · intro g
      -- Any stabilizer element has support away from `0`, so it comes from `ofSubtype`.
      have hfix : ((g : MulAction.stabilizer A5 (0 : Fin 5)) : A5) • (0 : Fin 5) = 0 := by
        exact MulAction.mem_stabilizer_iff.mp g.property
      have hsupp :
          ((((g : MulAction.stabilizer A5 (0 : Fin 5)) : A5) : Equiv.Perm (Fin 5)).support) ⊆
            pointComplementZero := by
        intro x hx
        have hx0 : x ≠ 0 := by
          intro hx_eq
          have hmove :
              (((g : MulAction.stabilizer A5 (0 : Fin 5)) : A5) : Equiv.Perm (Fin 5)) x ≠ x := by
            simpa [Equiv.Perm.mem_support] using hx
          exact hmove (by simpa [hx_eq] using hfix)
        exact (mem_pointComplementZero_iff x).2 hx0
      have hmem_range :
          ((g : MulAction.stabilizer A5 (0 : Fin 5)) : A5) ∈
            (alternatingGroup.ofSubtype pointComplementZero).range :=
        (alternatingGroup.mem_range_ofSubtype_iff pointComplementZero
          ((g : MulAction.stabilizer A5 (0 : Fin 5)) : A5)).2 hsupp
      rcases hmem_range with ⟨σ0, hσ0⟩
      refine ⟨(Equiv.altCongrHom pointComplementZeroEquiv).symm σ0, ?_⟩
      apply Subtype.ext
      simpa [φ, point_stabilizer_zero_to_stabilizer, point_stabilizer_zero_to_a5] using hσ0
  exact (MulEquiv.ofBijective φ hbij).symm

/-- Helper for Exercise 18-18.6-5: the subgroup character on `A₄` coming from the nontrivial
character of `A₄/V₄`. -/
private def a4_specialized_group_character : A4 →* ℂˣ :=
  a4_specialized_cyclotomic_linearCharacter.comp (QuotientGroup.mk' V4)

/-- Helper for Exercise 18-18.6-5: the pulled-back quotient character on `A₄` is nontrivial. -/
private theorem a4_specialized_group_character_ne_one :
    a4_specialized_group_character ≠ 1 := by
  -- Surjectivity of the quotient map lets us descend equality on `A₄` back to the quotient.
  intro h
  have hquot : a4_specialized_cyclotomic_linearCharacter = 1 := by
    apply MonoidHom.ext
    intro q
    rcases QuotientGroup.mk'_surjective V4 q with ⟨g, hg⟩
    have hval : a4_specialized_group_character g = (1 : A4 →* ℂˣ) g :=
      congrArg (fun χ : A4 →* ℂˣ => χ g) h
    simpa [a4_specialized_group_character] using hg ▸ hval
  exact a4_specialized_cyclotomic_linearCharacter_ne_one hquot

/-- Helper for Exercise 18-18.6-5: an order-`3` element of `A₄` stays nontrivial in the quotient
`A₄/V₄`. -/
private theorem quotient_mk_ne_one_of_order_three
    (g : A4) (hg : orderOf g = 3) :
    QuotientGroup.mk' V4 g ≠ (1 : A4 ⧸ V4) := by
  -- If the quotient class were trivial then `g ∈ V₄`, but every element of `V₄` squares to `1`.
  intro hq
  have hg_mem : g ∈ V4 := by
    change QuotientGroup.mk g = 1 at hq
    simpa using (QuotientGroup.eq_one_iff g).mp hq
  let kg : V4 := ⟨g, hg_mem⟩
  letI : IsKleinFour V4 :=
    alternatingGroup.kleinFour_isKleinFour (α := Fin 4) (by simp)
  have hsq : g ^ 2 = 1 := by
    change ((kg : V4) : A4) ^ 2 = 1
    have hmul : kg * kg = 1 := IsKleinFour.mul_self kg
    simpa [pow_two] using congrArg (fun x : V4 => ((x : V4) : A4)) hmul
  have hgdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rw [hg] at hgdvd
  norm_num at hgdvd

/-- Helper for Exercise 18-18.6-5: on the cyclic quotient of order `3`, the chosen specialized
character is nontrivial on every element of order `3`. -/
private theorem specialized_quotient_character_ne_one_of_order_three
    (q : A4 ⧸ V4) (hq : orderOf q = 3) :
    a4_specialized_cyclotomic_linearCharacter q ≠ 1 := by
  -- A nontrivial character of a group of prime order cannot vanish on a generator.
  intro hqval
  have hq_ne : q ≠ 1 := by
    exact fun h => by simpa [h] using hq
  letI : Fact (Nat.card (A4 ⧸ V4)).Prime := by
    refine ⟨?_⟩
    rw [a4_quotient_by_kleinFour_card]
    exact Nat.prime_three
  have htop : Subgroup.zpowers q = ⊤ :=
    zpowers_eq_top_of_prime_card a4_quotient_by_kleinFour_card hq_ne
  have htriv : a4_specialized_cyclotomic_linearCharacter = 1 := by
    apply MonoidHom.ext
    intro r
    have hrmem : r ∈ Subgroup.zpowers q := by
      simpa [htop]
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hrmem
    calc
      a4_specialized_cyclotomic_linearCharacter (q ^ n) =
          a4_specialized_cyclotomic_linearCharacter q ^ n := by
            simp
      _ = 1 := by
            simp [hqval]
  exact a4_specialized_cyclotomic_linearCharacter_ne_one htriv

/-- Helper for Exercise 18-18.6-5: order-`2` elements of `A₄` lie in `V₄`, so the quotient
character takes the value `1` on them. -/
private theorem a4_specialized_group_character_order_two_eq_one
    (g : A4) (hg : orderOf g = 2) :
    a4_specialized_group_character g = 1 := by
  -- The quotient class has both square `1` and cube `1`, hence it is trivial.
  let q : A4 ⧸ V4 := QuotientGroup.mk' V4 g
  have hq2 : q ^ 2 = 1 := by
    change QuotientGroup.mk' V4 (g ^ 2) = 1
    simpa [hg] using congrArg (QuotientGroup.mk' V4) (pow_orderOf_eq_one g)
  have hq3 : q ^ 3 = 1 := a4_quotient_cube_eq_one q
  have hqdvd2 : orderOf q ∣ 2 := orderOf_dvd_of_pow_eq_one hq2
  have hqdvd3 : orderOf q ∣ 3 := orderOf_dvd_of_pow_eq_one hq3
  have hqord : orderOf q = 1 := by
    have hqdvd1 : orderOf q ∣ Nat.gcd 2 3 := Nat.dvd_gcd hqdvd2 hqdvd3
    have hqdvd1' : orderOf q ∣ 1 := by simpa using hqdvd1
    exact Nat.eq_one_of_dvd_one hqdvd1'
  have hqone : q = 1 := orderOf_eq_one_iff.mp hqord
  change a4_specialized_cyclotomic_linearCharacter q = 1
  simpa [q] using congrArg a4_specialized_cyclotomic_linearCharacter hqone

/-- Helper for Exercise 18-18.6-5: for an order-`3` element of `A₄`, the specialized quotient
character takes the two inverse cube-root values whose sum is `-1`. -/
private theorem a4_specialized_group_character_order_three_sum
    (g : A4) (hg : orderOf g = 3) :
    ((a4_specialized_group_character g : ℂ) +
        (a4_specialized_group_character (g ^ 2) : ℂ) = -1) := by
  -- Route correction: work in the quotient `A₄/V₄ ≃ C₃` first, prove the root-of-unity identity
  -- there, and only then pull the result back to `A₄`.
  let q : A4 ⧸ V4 := QuotientGroup.mk' V4 g
  have hqpow : q ^ 3 = 1 := a4_quotient_cube_eq_one q
  have hqdvd : orderOf q ∣ 3 := orderOf_dvd_of_pow_eq_one hqpow
  have hq_ne : q ≠ 1 := quotient_mk_ne_one_of_order_three g hg
  have hqord : orderOf q = 3 := by
    have hq_ne_one : orderOf q ≠ 1 := by
      intro h1
      exact hq_ne (orderOf_eq_one_iff.mp h1)
    rcases Nat.dvd_prime Nat.prime_three |>.mp hqdvd with h1 | h3
    · exact (hq_ne_one h1).elim
    · exact h3
  let z : ℂ := a4_specialized_cyclotomic_linearCharacter q
  have hzpow : z ^ 3 = 1 := by
    change ((a4_specialized_cyclotomic_linearCharacter q : ℂˣ) : ℂ) ^ 3 = 1
    simpa [map_pow] using
      congrArg (fun u : ℂˣ => (u : ℂ))
        (congrArg a4_specialized_cyclotomic_linearCharacter hqpow)
  have hzne : z ≠ 1 := by
    intro hz1
    exact (specialized_quotient_character_ne_one_of_order_three q hqord) (Units.ext hz1)
  have hzpoly : z ^ 2 + z + 1 = 0 := by
    have hzfact : (z - 1) * (z ^ 2 + z + 1) = 0 := by
      calc
        (z - 1) * (z ^ 2 + z + 1) = z ^ 3 - 1 := by
          ring
        _ = 0 := by
          simp [hzpow]
    have hzminus : z - 1 ≠ 0 := sub_ne_zero.mpr hzne
    exact (mul_eq_zero.mp hzfact).resolve_left hzminus
  have hzsum : z + z ^ 2 = -1 := by
    calc
      z + z ^ 2 = (z ^ 2 + z + 1) - 1 := by
        ring
      _ = -1 := by
        simp [hzpoly]
  simpa [z, q, a4_specialized_group_character, map_pow] using hzsum

/-- Helper for Exercise 18-18.6-5: pull the nontrivial `A₄/V₄` character back along the point
stabilizer isomorphism `Stab_{A₅}(0) ≃ A₄`. -/
noncomputable def point_stabilizer_zero_linear_character :
    MulAction.stabilizer A5 (0 : Fin 5) →* ℂˣ :=
  a4_specialized_group_character.comp point_stabilizer_zero_mulEquiv_a4.toMonoidHom

/-- Helper for Exercise 18-18.6-5: the pulled-back point-stabilizer character is nontrivial. -/
theorem point_stabilizer_zero_linear_character_ne_one :
    point_stabilizer_zero_linear_character ≠ 1 := by
  -- Surjectivity of the stabilizer-to-`A₄` equivalence descends equality back to `A₄`.
  intro h
  apply a4_specialized_group_character_ne_one
  ext g
  rcases point_stabilizer_zero_mulEquiv_a4.surjective g with ⟨h0, rfl⟩
  simpa [point_stabilizer_zero_linear_character] using
    congrArg (fun χ : MulAction.stabilizer A5 (0 : Fin 5) →* ℂˣ => χ h0) h

/-- Helper for Exercise 18-18.6-5: order-`2` elements in the point stabilizer map to the trivial
quotient class. -/
theorem point_stabilizer_zero_linear_character_order_two_eq_one
    (h : MulAction.stabilizer A5 (0 : Fin 5)) (hh : orderOf h = 2) :
    point_stabilizer_zero_linear_character h = 1 := by
  -- Transport the order statement across `Stab_{A₅}(0) ≃ A₄` and reuse the quotient lemma.
  have hh' : orderOf (point_stabilizer_zero_mulEquiv_a4 h) = 2 := by
    simpa [hh] using point_stabilizer_zero_mulEquiv_a4.orderOf_eq h
  simpa [point_stabilizer_zero_linear_character] using
    a4_specialized_group_character_order_two_eq_one
      (point_stabilizer_zero_mulEquiv_a4 h) hh'

/-- Helper for Exercise 18-18.6-5: order-`3` elements in the point stabilizer contribute the two
inverse cube-root values whose sum is `-1`. -/
theorem point_stabilizer_zero_linear_character_order_three_sum
    (h : MulAction.stabilizer A5 (0 : Fin 5)) (hh : orderOf h = 3) :
    ((point_stabilizer_zero_linear_character h : ℂ) +
        (point_stabilizer_zero_linear_character (h ^ 2) : ℂ) = -1) := by
  -- Transport to `A₄`, use the quotient-root computation there, and map powers back.
  have hh' : orderOf (point_stabilizer_zero_mulEquiv_a4 h) = 3 := by
    simpa [hh] using point_stabilizer_zero_mulEquiv_a4.orderOf_eq h
  simpa [point_stabilizer_zero_linear_character, map_pow] using
    a4_specialized_group_character_order_three_sum
      (point_stabilizer_zero_mulEquiv_a4 h) hh'

end OrdinaryIrreducible
