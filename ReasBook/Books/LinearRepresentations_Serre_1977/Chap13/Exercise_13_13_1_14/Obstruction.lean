import Mathlib
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_2_1
import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_1

noncomputable section

universe u v

open scoped Representation
open scoped Quaternion

namespace Representation

section CharacterAPI

variable {G : Type u} [Group G] [Finite G]

/- The subgroup permutation characters are written `ℓ_H^G` on the source-facing theorem surface. -/
scoped[Representation] notation "ℓ_{" H "}^" G:max =>
  (Subgroup.characterRingOverFieldInduction H ℚ 1 : R[ℚ](G))

/-- Helper for Exercise 13-13.1-14: the `ℤ`-span of the subgroup permutation characters
`ℓ_H^G = Ind_H^G(1_H)`. -/
def subgroupPermutationCharacterSpanOverQ (G : Type u) [Group G] [Finite G] :
    Submodule ℤ (R[ℚ](G)) :=
  Submodule.span ℤ
    (Set.range fun H : Subgroup G ↦ (ℓ_{H}^G : R[ℚ](G)))

end CharacterAPI

section

local notation "Q8" => QuaternionGroup 2
local notation "C3" => Multiplicative (ZMod 3)
local notation "G0" => Q8 × C3

local instance : Fintype Q8 := inferInstance
local instance : Fintype C3 := inferInstance
local instance : DecidableEq Q8 := inferInstance
local instance : DecidableEq C3 := inferInstance
local instance : Finite G0 := inferInstance
local instance : Fintype G0 := inferInstance
local instance : DecidableEq G0 := inferInstance
local instance : Finite (ULift.{u} G0) := inferInstance
local instance (H : Subgroup G0) : Fintype H := Fintype.ofFinite H
local instance (H : Subgroup (ULift.{u} G0)) : Fintype H := Fintype.ofFinite H
local instance (H : Subgroup G0) : DecidablePred fun x : G0 ↦ x ∈ H := Classical.decPred _
local instance : DecidableEq (Subgroup G0) := Classical.decEq _

/-- Helper for Exercise 13-13.1-14: the central involution in `Q8 × C3`. -/
def quaternion_cyclic_central_order_two : G0 :=
  (QuaternionGroup.a (2 : ZMod 4), 1)

/-- Helper for Exercise 13-13.1-14: a chosen generator of the cyclic factor `C3`. -/
def quaternion_cyclic_central_order_three : G0 :=
  (1, Multiplicative.ofAdd (1 : ZMod 3))

/-- Helper for Exercise 13-13.1-14: the central element of order `6` obtained by multiplying the
distinguished order-`2` and order-`3` elements. -/
def quaternion_cyclic_central_order_six : G0 :=
  quaternion_cyclic_central_order_two * quaternion_cyclic_central_order_three

/-- Helper for Exercise 13-13.1-14: the `Q8` involution `a 2 = -1` is central. -/
theorem quaternion_cyclic_central_order_two_mem_center :
    quaternion_cyclic_central_order_two ∈ Subgroup.center G0 := by
  -- The `Q8` element `a 2` commutes with every quaternion-group element, and the `C3` coordinate
  -- is just `1`.
  have hzq : (QuaternionGroup.a (2 : ZMod 4) : Q8) ∈ Subgroup.center Q8 := by
    rw [Subgroup.mem_center_iff]
    intro q
    cases q with
    | a i =>
        simp [QuaternionGroup.a_mul_a, add_comm]
    | xa i =>
        rw [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa]
        fin_cases i <;> decide
  rw [Subgroup.mem_center_iff]
  intro g
  have hq := (Subgroup.mem_center_iff.mp hzq) g.1
  ext <;> simp [quaternion_cyclic_central_order_two, hq]

/-- Helper for Exercise 13-13.1-14: the chosen generator of `C3` is central in the direct
product. -/
theorem quaternion_cyclic_central_order_three_mem_center :
    quaternion_cyclic_central_order_three ∈ Subgroup.center G0 := by
  -- The first factor is `1`, and the second factor lies in the abelian group `C3`.
  rw [Subgroup.mem_center_iff]
  intro g
  ext <;> simp [quaternion_cyclic_central_order_three, mul_comm]

/-- Helper for Exercise 13-13.1-14: the product of the two distinguished central elements is
still central. -/
theorem quaternion_cyclic_central_order_six_mem_center :
    quaternion_cyclic_central_order_six ∈ Subgroup.center G0 := by
  -- The center is a subgroup, so it is closed under multiplication.
  simpa [quaternion_cyclic_central_order_six] using
    Subgroup.mul_mem (Subgroup.center G0)
      quaternion_cyclic_central_order_two_mem_center
      quaternion_cyclic_central_order_three_mem_center

/-- Helper for Exercise 13-13.1-14: every nonidentity element of `Q8` is either the central
involution or squares to it. -/
theorem quaternionGroupTwo_sq_eq_a_two_or_eq_a_two
    (q : Q8) (hq : q ≠ 1) :
    q = QuaternionGroup.a (2 : ZMod 4) ∨ q ^ 2 = QuaternionGroup.a (2 : ZMod 4) := by
  -- Split over the eight normal forms in `Q8`.
  cases q with
  | a i =>
      fin_cases i
      · exfalso
        exact hq QuaternionGroup.a_zero
      · right
        decide
      · left
        decide
      · right
        decide
  | xa i =>
      right
      fin_cases i <;> decide

/-- Helper for Exercise 13-13.1-14: if an element of `Q8 × C3` has nontrivial `Q8`-projection,
then a power of it is the distinguished central involution. -/
theorem pow_eq_central_order_two_of_fst_ne_one
    (g : G0) (hg : g.1 ≠ 1) :
    g ^ 3 = quaternion_cyclic_central_order_two ∨
      g ^ 6 = quaternion_cyclic_central_order_two := by
  -- This is a finite computation on the explicit product group `Q8 × C3`.
  let h :
      ∀ g : G0, g.1 ≠ 1 →
        g ^ 3 = quaternion_cyclic_central_order_two ∨
          g ^ 6 = quaternion_cyclic_central_order_two := by
    native_decide
  exact h g hg

/-- Helper for Exercise 13-13.1-14: if an element of `Q8 × C3` has trivial `Q8`-projection but
nontrivial `C3`-projection, then one of its first two powers is the chosen generator of `C3`. -/
theorem pow_eq_central_order_three_of_fst_eq_one_snd_ne_one
    (g : G0) (hgfst : g.1 = 1) (hgsnd : g.2 ≠ 1) :
    g = quaternion_cyclic_central_order_three ∨
      g ^ 2 = quaternion_cyclic_central_order_three := by
  -- Once the first coordinate is `1`, the claim is another finite check on `C3`.
  let h :
      ∀ g : G0, g.1 = 1 → g.2 ≠ 1 →
        g = quaternion_cyclic_central_order_three ∨
          g ^ 2 = quaternion_cyclic_central_order_three := by
    native_decide
  exact h g hgfst hgsnd

/-- Helper for Exercise 13-13.1-14: a subgroup omitting the distinguished central order-`2` and
order-`3` elements must be trivial. -/
theorem subgroup_eq_bot_of_not_mem_central_order_two_and_three
    (H : Subgroup G0)
    (hz : quaternion_cyclic_central_order_two ∉ H)
    (hc : quaternion_cyclic_central_order_three ∉ H) :
    H = ⊥ := by
  -- Any nontrivial subgroup element forces one of the two distinguished central elements to lie in
  -- the subgroup, contradicting the hypotheses.
  ext g
  constructor
  · intro hg
    by_cases h1 : g = 1
    · simp [h1]
    · by_cases hgfst : g.1 = 1
      · have hgsnd : g.2 ≠ 1 := by
          intro hsnd
          apply h1
          ext <;> simp [hgfst, hsnd]
        rcases pow_eq_central_order_three_of_fst_eq_one_snd_ne_one g hgfst hgsnd with hg3 | hg3
        · exact False.elim (hc (hg3 ▸ hg))
        · exact False.elim (hc (hg3 ▸ H.pow_mem hg 2))
      · rcases pow_eq_central_order_two_of_fst_ne_one g hgfst with hg2 | hg2
        · exact False.elim (hz (hg2 ▸ H.pow_mem hg 3))
        · exact False.elim (hz (hg2 ▸ H.pow_mem hg 6))
  · intro hg
    have hg' : g = 1 := by
      simpa [Subgroup.mem_bot] using hg
    exact hg' ▸ H.one_mem

/-- Helper for Exercise 13-13.1-14: the four-point central-value test used to isolate the trivial
subgroup coefficient. -/
def trivial_subgroup_test (f : G0 → ℚ) : ℚ :=
  (f 1 - f quaternion_cyclic_central_order_three - f quaternion_cyclic_central_order_two +
      f quaternion_cyclic_central_order_six) /
    24

/-- Helper for Exercise 13-13.1-14: the subgroup test is additive on rational characters. -/
theorem trivial_subgroup_test_map_add
    (χ ψ : R[ℚ](G0)) :
    trivial_subgroup_test (((χ + ψ : R[ℚ](G0)) : G0 → ℚ)) =
      trivial_subgroup_test (χ : G0 → ℚ) + trivial_subgroup_test (ψ : G0 → ℚ) := by
  -- Expand the four evaluation terms and collect the rational coefficients.
  simp [trivial_subgroup_test]
  ring

/-- Helper for Exercise 13-13.1-14: the subgroup test commutes with integer scalar
multiplication. -/
theorem trivial_subgroup_test_map_zsmul
    (n : ℤ) (χ : R[ℚ](G0)) :
    trivial_subgroup_test (((n • χ : R[ℚ](G0)) : G0 → ℚ)) =
      n • trivial_subgroup_test (χ : G0 → ℚ) := by
  -- The test is a fixed rational linear combination of four evaluations.
  simp [trivial_subgroup_test]
  ring

/-- Helper for Exercise 13-13.1-14: the subgroup test upgraded to a `ℤ`-linear functional on the
rational character ring. -/
def trivial_subgroup_test_linear : R[ℚ](G0) →ₗ[ℤ] ℚ :=
  { toFun := fun χ ↦ trivial_subgroup_test (χ : G0 → ℚ)
    map_add' := trivial_subgroup_test_map_add
    map_smul' := trivial_subgroup_test_map_zsmul }

/-- Helper for Exercise 13-13.1-14: on a central element, the subgroup permutation character
`ℓ_H^G` is either the index of `H` or `0`, according as the element lies in `H`. -/
theorem subgroupPermutationCharacter_value_of_mem_center
    (H : Subgroup G0) (g : G0) (hg : g ∈ Subgroup.center G0) :
    (((ℓ_{H}^G0 : R[ℚ](G0)) : G0 → ℚ) g) = if g ∈ H then H.index else 0 := by
  classical
  have hψ : _root_.IsClassFunction (1 : H → ℚ) := by
    -- The trivial subgroup character is constant.
    refine ⟨?_⟩
    intro a b hab
    simp
  obtain ⟨S, hS, h1S⟩ := H.exists_isComplement_left (1 : G0)
  let R : Finset G0 := (Set.toFinite S).toFinset
  have hR : Subgroup.IsComplement (R : Set G0) (H : Set G0) := by
    simpa [R] using hS
  have hcardR : R.card = H.index := by
    simpa [R] using hR.card_left
  haveI : NeZero (Nat.card H : ℚ) :=
    ⟨Nat.cast_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨⟨1, H.one_mem⟩, inferInstance⟩)⟩
  rw [Subgroup.characterRingOverFieldInduction_apply]
  change Subgroup.inducedClassFunction H (1 : H → ℚ) g = _
  rw [Subgroup.induced_class_function_eq_sum_over_left_transversal
    (H := H) (ψ := (1 : H → ℚ)) hψ (R := R) (hR := hR) (x := g)]
  have hconj (r : G0) : r⁻¹ * g * r = g := by
    -- Centrality collapses every conjugate `r⁻¹ g r` back to `g`.
    have hcomm := (Subgroup.mem_center_iff.mp hg) r
    have hleft := congrArg (fun x : G0 ↦ r⁻¹ * x) hcomm
    simpa [mul_assoc] using hleft.symm
  have hterm (r : G0) :
      (if hr : r⁻¹ * g * r ∈ H then (1 : H → ℚ) ⟨r⁻¹ * g * r, hr⟩ else 0) =
        if g ∈ H then 1 else 0 := by
    -- Each summand is the same constant because every conjugate equals `g`.
    by_cases hgH : g ∈ H
    · have hr : r⁻¹ * g * r ∈ H := by
        simpa [hconj r] using hgH
      simp [hr, hgH]
    · have hr : ¬ r⁻¹ * g * r ∈ H := by
        simpa [hconj r] using hgH
      simp [hr, hgH]
  rw [show
      (∑ r ∈ R, if hr : r⁻¹ * g * r ∈ H then (1 : H → ℚ) ⟨r⁻¹ * g * r, hr⟩ else 0) =
        ∑ r ∈ R, (if g ∈ H then 1 else 0) by
      refine Finset.sum_congr rfl ?_
      intro r hr
      exact hterm r]
  by_cases hgH : g ∈ H
  · simp [hgH, hcardR]
  · simp [hgH]

/-- Helper for Exercise 13-13.1-14: the subgroup test takes only the values `0` and `1` on
subgroup permutation characters. -/
theorem trivial_subgroup_test_on_subgroupPermutationCharacter
    (H : Subgroup G0) :
    trivial_subgroup_test (((ℓ_{H}^G0 : R[ℚ](G0)) : G0 → ℚ)) =
      if H = ⊥ then 1 else 0 := by
  classical
  -- Evaluate the subgroup permutation character on the four distinguished central elements.
  have hone :
      (((ℓ_{H}^G0 : R[ℚ](G0)) : G0 → ℚ) 1) = H.index := by
    simpa using
      subgroupPermutationCharacter_value_of_mem_center (H := H) (g := 1) (by simp)
  have hz :
      (((ℓ_{H}^G0 : R[ℚ](G0)) : G0 → ℚ) quaternion_cyclic_central_order_two) =
        if quaternion_cyclic_central_order_two ∈ H then H.index else 0 := by
    exact
      subgroupPermutationCharacter_value_of_mem_center
        (H := H) (g := quaternion_cyclic_central_order_two)
        quaternion_cyclic_central_order_two_mem_center
  have hc :
      (((ℓ_{H}^G0 : R[ℚ](G0)) : G0 → ℚ) quaternion_cyclic_central_order_three) =
        if quaternion_cyclic_central_order_three ∈ H then H.index else 0 := by
    exact
      subgroupPermutationCharacter_value_of_mem_center
        (H := H) (g := quaternion_cyclic_central_order_three)
        quaternion_cyclic_central_order_three_mem_center
  have hzc :
      (((ℓ_{H}^G0 : R[ℚ](G0)) : G0 → ℚ) quaternion_cyclic_central_order_six) =
        if quaternion_cyclic_central_order_six ∈ H then H.index else 0 := by
    exact
      subgroupPermutationCharacter_value_of_mem_center
        (H := H) (g := quaternion_cyclic_central_order_six)
        quaternion_cyclic_central_order_six_mem_center
  rw [trivial_subgroup_test, hone, hz, hc, hzc]
  by_cases hH : H = ⊥
  · -- For the trivial subgroup, only the identity contributes, and the resulting index is `24`.
    subst hH
    have hz2ne : quaternion_cyclic_central_order_two ≠ 1 := by
      decide
    have hz3ne : quaternion_cyclic_central_order_three ≠ 1 := by
      decide
    have hz6ne : quaternion_cyclic_central_order_six ≠ 1 := by
      decide
    have hcard : Fintype.card G0 = 24 := by
      native_decide
    norm_num [Subgroup.index_bot, hcard, hz2ne, hz3ne, hz6ne]
  · -- For a nontrivial subgroup, the two central detectors force cancellation in the four-term
    -- test.
    by_cases hzH : quaternion_cyclic_central_order_two ∈ H
    · by_cases hcH : quaternion_cyclic_central_order_three ∈ H
      · have hzcH : quaternion_cyclic_central_order_six ∈ H := by
          simpa [quaternion_cyclic_central_order_six] using H.mul_mem hzH hcH
        simp [hH, hzH, hcH, hzcH]
      · have hzcH : quaternion_cyclic_central_order_six ∉ H := by
          intro hzcH
          have : quaternion_cyclic_central_order_three ∈ H := by
            have hz2inv : quaternion_cyclic_central_order_two⁻¹ ∈ H := H.inv_mem hzH
            simpa [quaternion_cyclic_central_order_six, mul_assoc] using H.mul_mem hz2inv hzcH
          exact hcH this
        simp [hH, hzH, hcH, hzcH]
    · have hcH : quaternion_cyclic_central_order_three ∈ H := by
        by_contra hcH
        exact hH (subgroup_eq_bot_of_not_mem_central_order_two_and_three H hzH hcH)
      have hzcH : quaternion_cyclic_central_order_six ∉ H := by
        intro hzcH
        have : quaternion_cyclic_central_order_two ∈ H := by
          simpa [quaternion_cyclic_central_order_six, mul_assoc] using
            H.mul_mem hzcH (H.inv_mem hcH)
        exact hzH this
      simp [hH, hzH, hcH, hzcH]

/-- Helper for Exercise 13-13.1-14: LinearRepresentations_Serre_1977's four central values force the subgroup test to take
the obstruction value `1 / 2`. -/
theorem trivial_subgroup_test_eq_half_of_central_values
    {χ : R[ℚ](G0)}
    (hone : ((χ : G0 → ℚ) 1) = 4)
    (hz : ((χ : G0 → ℚ) quaternion_cyclic_central_order_two) = -4)
    (hc : ((χ : G0 → ℚ) quaternion_cyclic_central_order_three) = -2)
    (hzc : ((χ : G0 → ℚ) quaternion_cyclic_central_order_six) = 2) :
    trivial_subgroup_test_linear χ = (1 / 2 : ℚ) := by
  -- The source-side four-point test is a fixed affine combination of these four character values.
  rw [show trivial_subgroup_test_linear χ = trivial_subgroup_test (χ : G0 → ℚ) by rfl]
  rw [trivial_subgroup_test, hone, hz, hc, hzc]
  norm_num

/-- Helper for Exercise 13-13.1-14: any rational character on `Q8 × C3` with LinearRepresentations_Serre_1977's four
distinguished central values already lies outside the subgroup-permutation lattice. -/
theorem quaternion_cyclic_obstruction_of_central_values
    {χ : R[ℚ](G0)}
    (hone : ((χ : G0 → ℚ) 1) = 4)
    (hz : ((χ : G0 → ℚ) quaternion_cyclic_central_order_two) = -4)
    (hc : ((χ : G0 → ℚ) quaternion_cyclic_central_order_three) = -2)
    (hzc : ((χ : G0 → ℚ) quaternion_cyclic_central_order_six) = 2) :
    χ ∉ subgroupPermutationCharacterSpanOverQ G0 := by
  -- Apply the `ℤ`-linear test to the subgroup-permutation span and compare it with the explicit
  -- four central values of `χ`.
  intro hχ
  change χ ∈
      Submodule.span ℤ (Set.range fun H : Subgroup G0 ↦ (ℓ_{H}^G0 : R[ℚ](G0))) at hχ
  have hinteger :
      ∃ n : ℤ, trivial_subgroup_test_linear χ = n := by
    -- The test takes the values `0` and `1` on the subgroup-permutation generators, hence lands
    -- in the integers on their entire `ℤ`-span.
    let p :
        (x : R[ℚ](G0)) →
          x ∈ Submodule.span ℤ (Set.range fun H : Subgroup G0 ↦ (ℓ_{H}^G0 : R[ℚ](G0))) →
            Prop :=
      fun x _ ↦ ∃ n : ℤ, trivial_subgroup_test_linear x = n
    exact
      Submodule.span_induction
        (p := p)
        (mem := by
          intro x hx
          rcases hx with ⟨H, rfl⟩
          refine ⟨if H = ⊥ then 1 else 0, ?_⟩
          change
            trivial_subgroup_test (((ℓ_{H}^G0 : R[ℚ](G0)) : G0 → ℚ)) =
              ((if H = ⊥ then 1 else 0 : ℤ) : ℚ)
          simpa using trivial_subgroup_test_on_subgroupPermutationCharacter H)
        (zero := by
          refine ⟨0, ?_⟩
          change trivial_subgroup_test (0 : G0 → ℚ) = (0 : ℚ)
          simp [trivial_subgroup_test])
        (add := by
          intro x y hx hy hx_int hy_int
          rcases hx_int with ⟨m, hm⟩
          rcases hy_int with ⟨n, hn⟩
          refine ⟨m + n, ?_⟩
          calc
            trivial_subgroup_test_linear (x + y)
                = trivial_subgroup_test_linear x + trivial_subgroup_test_linear y := by
                    simp
            _ = (m : ℚ) + (n : ℚ) := by
                  simp [hm, hn]
            _ = ((m + n : ℤ) : ℚ) := by
                  simp)
        (smul := by
          intro a x hx hx_int
          rcases hx_int with ⟨n, hn⟩
          refine ⟨a * n, ?_⟩
          calc
            trivial_subgroup_test_linear (a • x) = a • trivial_subgroup_test_linear x := by
              change
                trivial_subgroup_test (((a • x : R[ℚ](G0)) : G0 → ℚ)) =
                  a • trivial_subgroup_test (x : G0 → ℚ)
              simpa [trivial_subgroup_test_linear] using trivial_subgroup_test_map_zsmul a x
            _ = (a : ℚ) * (n : ℚ) := by
              simp [hn]
            _ = ((a * n : ℤ) : ℚ) := by
              simp)
        hχ
  -- The explicit central values compute the test on `χ`.
  have hhalf : trivial_subgroup_test_linear χ = (1 / 2 : ℚ) :=
    trivial_subgroup_test_eq_half_of_central_values hone hz hc hzc
  rcases hinteger with ⟨n, hn⟩
  have : (1 / 2 : ℚ) = n := by
    rw [← hhalf, hn]
  have h0 : (0 : ℚ) < n := by
    linarith
  have h1 : (n : ℚ) < 1 := by
    linarith
  have h0' : (0 : ℤ) < n := by
    exact_mod_cast h0
  have h1' : n < 1 := by
    exact_mod_cast h1
  linarith

end

end Representation
