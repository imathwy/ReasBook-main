import Mathlib
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_6.Bases
import LinearRepresentations_Serre_1977.Chap18.Corollary_18_18_2_5
import LinearRepresentations_Serre_1977.Chap18.Remark_18_18_6_1

noncomputable section

open CategoryTheory
open Representation
open AlternatingGroupFive

namespace Representation

local notation "A5" => alternatingGroup (Fin 5)
local notation "𝔽₄" => FiniteField.Extension (ZMod 2) 2 2

/-- Helper for Exercise 18-18.6-3: the explicit order-`5` generator used to distinguish the two
`5`-cycle classes of `A₅`. -/
private theorem a5_generator_five_mem_alternatingGroup :
    finRotate 5 ∈ alternatingGroup (Fin 5) := by
  -- The cycle `(0 1 2 3 4)` is even, so it lies in `A₅`.
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

/-- Helper for Exercise 18-18.6-3: the explicit order-`2` generator used to build a concrete
order-`3` element of `A₅`. -/
private theorem a5_generator_two_mem_alternatingGroup :
    Equiv.swap 1 2 * Equiv.swap 3 4 ∈ alternatingGroup (Fin 5) := by
  -- The product of two disjoint transpositions is even.
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

/-- Helper for Exercise 18-18.6-3: the chosen order-`5` element of `A₅`. -/
private def a5_generator_five : A5 :=
  ⟨finRotate 5, a5_generator_five_mem_alternatingGroup⟩

/-- Helper for Exercise 18-18.6-3: the chosen involution of `A₅`. -/
private def a5_generator_two : A5 :=
  ⟨Equiv.swap 1 2 * Equiv.swap 3 4, a5_generator_two_mem_alternatingGroup⟩

/-- Helper for Exercise 18-18.6-3: the chosen order-`3` element of `A₅`. -/
private def a5_generator_three : A5 :=
  a5_generator_five * a5_generator_two

/-- Helper for Exercise 18-18.6-3: the explicit generators satisfy the usual `2,3,5` triangle
relations. -/
private theorem a5_generator_triangle_relations :
    a5_generator_five ^ 5 = 1 ∧
      a5_generator_two ^ 2 = 1 ∧
      (a5_generator_five * a5_generator_two) ^ 3 = 1 := by
  -- These are finite checks on the chosen permutations.
  decide

/-- Helper for Exercise 18-18.6-3: the chosen `5`-cycle has order `5`. -/
private theorem a5_generator_five_order :
    orderOf a5_generator_five = 5 := by
  -- The `5`-cycle is nontrivial and its fifth power is the identity.
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  refine orderOf_eq_prime ?_ ?_
  · simpa using a5_generator_triangle_relations.1
  · decide

/-- Helper for Exercise 18-18.6-3: the chosen `3`-cycle has order `3`. -/
private theorem a5_generator_three_order :
    orderOf a5_generator_three = 3 := by
  -- The product of the order-`5` and order-`2` generators gives a concrete `3`-cycle.
  refine orderOf_eq_prime ?_ ?_
  · simpa [a5_generator_three] using a5_generator_triangle_relations.2.2
  · decide

/-- Helper for Exercise 18-18.6-3: the chosen order-`3` element is `2`-regular. -/
private theorem a5_generator_three_isPRegular_modTwo :
    IsPRegular 2 a5_generator_three := by
  -- Its order is prime to `2`.
  have hcop : Nat.Coprime 2 3 := by decide
  simpa [IsPRegular, a5_generator_three_order] using hcop

/-- Helper for Exercise 18-18.6-3: the chosen order-`5` element is `2`-regular. -/
private theorem a5_generator_five_isPRegular_modTwo :
    IsPRegular 2 a5_generator_five := by
  -- Its order is also prime to `2`.
  have hcop : Nat.Coprime 2 5 := by decide
  simpa [IsPRegular, a5_generator_five_order] using hcop

/-- Helper for Exercise 18-18.6-3: the square of the chosen order-`5` element has order `5`. -/
private theorem a5_generator_five_sq_order :
    orderOf (a5_generator_five ^ 2) = 5 := by
  have hcop : Nat.Coprime (orderOf a5_generator_five) 2 := by
    rw [a5_generator_five_order]
    decide
  simpa [a5_generator_five_order] using hcop.orderOf_pow (y := a5_generator_five) (m := 2)

/-- Helper for Exercise 18-18.6-3: the square of the chosen order-`5` element remains
`2`-regular. -/
private theorem a5_generator_five_sq_isPRegular_modTwo :
    IsPRegular 2 (a5_generator_five ^ 2) := by
  -- Squaring by an exponent prime to `5` preserves the order.
  have hcop : Nat.Coprime 2 5 := by decide
  simpa [IsPRegular, a5_generator_five_sq_order] using hcop

/-- Helper for Exercise 18-18.6-3: package the identity as a `2`-regular representative. -/
private def a5_one_pRegular_modTwo : { x : A5 // IsPRegular 2 x } :=
  ⟨1, isPRegular_one 2⟩

/-- Helper for Exercise 18-18.6-3: package the chosen order-`3` element as a `2`-regular
representative. -/
private def a5_generator_three_pRegular_modTwo : { x : A5 // IsPRegular 2 x } :=
  ⟨a5_generator_three, a5_generator_three_isPRegular_modTwo⟩

/-- Helper for Exercise 18-18.6-3: package the chosen `5`-cycle as a `2`-regular representative. -/
private def a5_generator_five_pRegular_modTwo : { x : A5 // IsPRegular 2 x } :=
  ⟨a5_generator_five, a5_generator_five_isPRegular_modTwo⟩

/-- Helper for Exercise 18-18.6-3: package the square `5`-cycle as a `2`-regular
representative. -/
private def a5_generator_five_sq_pRegular_modTwo : { x : A5 // IsPRegular 2 x } :=
  ⟨a5_generator_five ^ 2, a5_generator_five_sq_isPRegular_modTwo⟩

/-- Helper for Exercise 18-18.6-3: every element of `A₅` has one of the power patterns forced by
cycle types on five letters. -/
private theorem alternating_group_fin5_pow_eq_one_in_small_degree
    (g : A5) :
    g = 1 ∨
      (g ^ 2 = 1 ∧ g ≠ 1) ∨
        (g ^ 3 = 1 ∧ g ^ 2 ≠ 1) ∨
          (g ^ 5 = 1 ∧ g ^ 3 ≠ 1 ∧ g ^ 2 ≠ 1) := by
  -- This is a finite check on the concrete permutation group `A₅`.
  revert g
  native_decide

/-- Helper for Exercise 18-18.6-3: all order-`3` elements of `A₅` are conjugate. -/
private theorem alternating_group_fin5_isConj_of_cube_eq_one_sq_ne_one
    {g h : A5} (hg₃ : g ^ 3 = 1) (hg₂ : g ^ 2 ≠ 1)
    (hh₃ : h ^ 3 = 1) (hh₂ : h ^ 2 ≠ 1) :
    IsConj g h := by
  -- There is a single conjugacy class of `3`-cycles in `A₅`.
  revert hh₂ hh₃ hg₂ hg₃ h g
  native_decide

/-- Helper for Exercise 18-18.6-3: every `2`-regular element of `A₅` has order `1`, `3`, or
`5`. -/
private theorem alternating_group_fin5_pRegular_order_eq_one_or_three_or_five
    (g : A5) (hg : IsPRegular 2 g) :
    orderOf g = 1 ∨ orderOf g = 3 ∨ orderOf g = 5 := by
  rcases alternating_group_fin5_pow_eq_one_in_small_degree g with h1 | h2 | h3 | h5
  · -- The identity is the unique order-`1` case.
    exact Or.inl (orderOf_eq_one_iff.mpr h1)
  · -- Order `2` is excluded by `2`-regularity.
    have horder : orderOf g = 2 := orderOf_eq_prime h2.1 h2.2
    have hregular_order : Nat.Coprime 2 (orderOf g) := by
      simpa [IsPRegular] using hg
    have hcop : Nat.Coprime 2 2 := by
      rw [horder] at hregular_order
      exact hregular_order
    have : ¬ Nat.Coprime 2 2 := by decide
    exact False.elim (this hcop)
  · -- The remaining nontrivial `2`-regular small-order case is order `3`.
    have hg_ne : g ≠ 1 := by
      intro hg1
      exact h3.2 <| by simp [hg1]
    exact Or.inr (Or.inl (orderOf_eq_prime h3.1 hg_ne))
  · -- The last possible `2`-regular case is order `5`.
    have hg_ne : g ≠ 1 := by
      intro hg1
      exact h5.2.2 <| by simp [hg1]
    letI : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact Or.inr (Or.inr (orderOf_eq_prime h5.1 hg_ne))

/-- Helper for Exercise 18-18.6-3: an `A₅` element with the order-`5` power pattern and outside
the chosen `5`-cycle class lies in the square `5`-cycle class. -/
private theorem alternating_group_fin5_isConj_sq_of_fifth_eq_one_not_phi
    {g : A5} (hg₅ : g ^ 5 = 1) (hg₃ : g ^ 3 ≠ 1) (hg₂ : g ^ 2 ≠ 1)
    (hnot : ¬ IsConj g a5_generator_five) :
    IsConj g (a5_generator_five ^ 2) := by
  -- Finite search distinguishes the two split `5`-cycle classes.
  revert hnot hg₂ hg₃ hg₅ g
  native_decide

/-- Helper for Exercise 18-18.6-3: the two split `5`-cycle classes of `A₅` are distinct. -/
private theorem a5_generator_five_not_isConj_sq :
    ¬ IsConj a5_generator_five (a5_generator_five ^ 2) := by
  -- The two source labels `φ` and `ψ` correspond to different split `5`-cycle classes.
  native_decide

/-- Helper for Exercise 18-18.6-3: an order-`5` element not conjugate to
`a5_generator_five` must lie in the square split class. -/
private theorem alternating_group_fin5_isConj_of_order_five_not_phi
    {g : A5} (hg : orderOf g = 5) (hnot : ¬ IsConj g a5_generator_five) :
    IsConj g (a5_generator_five ^ 2) := by
  -- Convert the order statement to the finite power-pattern classifier.
  have hg₅ : g ^ 5 = 1 := by
    simpa [hg] using pow_orderOf_eq_one g
  have hg₃ : g ^ 3 ≠ 1 := by
    intro hpow
    have hdiv : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hpow
    have : ¬ 5 ∣ 3 := by decide
    exact this <| hg ▸ hdiv
  have hg₂ : g ^ 2 ≠ 1 := by
    intro hpow
    have hdiv : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hpow
    have : ¬ 5 ∣ 2 := by decide
    exact this <| hg ▸ hdiv
  exact alternating_group_fin5_isConj_sq_of_fifth_eq_one_not_phi hg₅ hg₃ hg₂ hnot

/-- Helper for Exercise 18-18.6-3: conjugacy in `A₅` can be unpacked as an even permutation
conjugator. -/
private theorem alternating_group_fin5_isConj_iff_subtype_exists {g h : A5} :
    IsConj g h ↔
      ∃ x : Equiv.Perm (Fin 5), ∃ hx : Equiv.Perm.sign x = 1,
        (⟨x, hx⟩ : A5) * g * (⟨x, hx⟩ : A5)⁻¹ = h := by
  rw [isConj_iff]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x.1, x.2, hx⟩
  · rintro ⟨x, hx, hconj⟩
    exact ⟨⟨x, hx⟩, hconj⟩

/-- Helper for Exercise 18-18.6-3: choose a representative of a `2`-regular conjugacy class of
`A₅`. -/
private noncomputable def alternating_group_fin5_pRegular_representative_modTwo
    (c : PRegularConjClass A5 2) : { x : A5 // IsPRegular 2 x } :=
  let g : A5 := Classical.choose (ConjClasses.mk_surjective (c : ConjClasses A5))
  let hg : ConjClasses.mk g = (c : ConjClasses A5) :=
    Classical.choose_spec (ConjClasses.mk_surjective (c : ConjClasses A5))
  ⟨g, c.2 g (ConjClasses.mem_carrier_iff_mk_eq.mpr hg)⟩

/-- Helper for Exercise 18-18.6-3: the chosen representative lies in the prescribed `2`-regular
conjugacy class. -/
private theorem alternating_group_fin5_pRegular_representative_modTwo_spec
    (c : PRegularConjClass A5 2) :
    ConjClasses.mk (alternating_group_fin5_pRegular_representative_modTwo c).1 =
      (c : ConjClasses A5) := by
  -- This is immediate from the chosen witness of surjectivity of `ConjClasses.mk`.
  simpa [alternating_group_fin5_pRegular_representative_modTwo] using
    Classical.choose_spec (ConjClasses.mk_surjective (c : ConjClasses A5))

/-- Helper for Exercise 18-18.6-3: a chosen representative of `PRegularConjClass.ofSubtype` has
the same order as the original `A₅` element. -/
private theorem alternating_group_fin5_orderOf_representative_ofSubtype_modTwo
    (s : { x : A5 // IsPRegular 2 x }) :
    orderOf
        (alternating_group_fin5_pRegular_representative_modTwo
          (_root_.PRegularConjClass.ofSubtype (G := A5) 2 s)).1 =
      orderOf s.1 := by
  have hconj :
      IsConj
        (alternating_group_fin5_pRegular_representative_modTwo
          (_root_.PRegularConjClass.ofSubtype (G := A5) 2 s)).1
        s.1 := by
    apply (ConjClasses.mk_eq_mk_iff_isConj).1
    simpa [_root_.PRegularConjClass.coe_ofSubtype] using
      alternating_group_fin5_pRegular_representative_modTwo_spec
        (_root_.PRegularConjClass.ofSubtype (G := A5) 2 s)
  rcases hconj with ⟨c, hc⟩
  -- Conjugate elements have the same order.
  simpa using hc.orderOf_eq

/-- Helper for Exercise 18-18.6-3: code the four `2`-regular conjugacy classes of `A₅` by the
Brauer labels from Serre's table. -/
private noncomputable def alternating_group_fin5_pRegular_code_modTwo
    (c : PRegularConjClass A5 2) : BrauerProjectiveModTwo :=
  let g := (alternating_group_fin5_pRegular_representative_modTwo c).1
  if h1 : orderOf g = 1 then .trivial
  else if h3 : orderOf g = 3 then .degreeFour
  else if IsConj g a5_generator_five then .degreeTwo_from_chi3_phi_psi
  else .degreeTwo_from_chi3_psi_phi

/-- Helper for Exercise 18-18.6-3: choose concrete representatives of the four `2`-regular
classes of `A₅` indexed by the Brauer labels. -/
private def alternating_group_fin5_pRegular_class_of_code_modTwo :
    BrauerProjectiveModTwo → PRegularConjClass A5 2
  | .trivial =>
      _root_.PRegularConjClass.ofSubtype (G := A5) 2 a5_one_pRegular_modTwo
  | .degreeTwo_from_chi3_phi_psi =>
      _root_.PRegularConjClass.ofSubtype (G := A5) 2 a5_generator_five_pRegular_modTwo
  | .degreeTwo_from_chi3_psi_phi =>
      _root_.PRegularConjClass.ofSubtype (G := A5) 2 a5_generator_five_sq_pRegular_modTwo
  | .degreeFour =>
      _root_.PRegularConjClass.ofSubtype (G := A5) 2 a5_generator_three_pRegular_modTwo

/-- Helper for Exercise 18-18.6-3: the concrete class representatives recover their own Brauer
codes. -/
private theorem alternating_group_fin5_pRegular_code_modTwo_right_inv
    (φ : BrauerProjectiveModTwo) :
    alternating_group_fin5_pRegular_code_modTwo
      (alternating_group_fin5_pRegular_class_of_code_modTwo φ) = φ := by
  cases φ with
  | trivial =>
      have horder :
          orderOf
              (alternating_group_fin5_pRegular_representative_modTwo
                (alternating_group_fin5_pRegular_class_of_code_modTwo
                  BrauerProjectiveModTwo.trivial)).1 = 1 := by
        simpa [alternating_group_fin5_pRegular_class_of_code_modTwo, a5_one_pRegular_modTwo] using
          alternating_group_fin5_orderOf_representative_ofSubtype_modTwo a5_one_pRegular_modTwo
      -- The identity class lands in the trivial Brauer label.
      simp [alternating_group_fin5_pRegular_code_modTwo, horder]
  | degreeTwo_from_chi3_phi_psi =>
      have horder :
          orderOf
              (alternating_group_fin5_pRegular_representative_modTwo
                (alternating_group_fin5_pRegular_class_of_code_modTwo
                  BrauerProjectiveModTwo.degreeTwo_from_chi3_phi_psi)).1 = 5 := by
        simpa [alternating_group_fin5_pRegular_class_of_code_modTwo,
          a5_generator_five_pRegular_modTwo, a5_generator_five_order] using
          alternating_group_fin5_orderOf_representative_ofSubtype_modTwo
            a5_generator_five_pRegular_modTwo
      have hconj :
          IsConj
            (alternating_group_fin5_pRegular_representative_modTwo
              (alternating_group_fin5_pRegular_class_of_code_modTwo
                BrauerProjectiveModTwo.degreeTwo_from_chi3_phi_psi)).1
            a5_generator_five := by
        apply (ConjClasses.mk_eq_mk_iff_isConj).1
        simpa [alternating_group_fin5_pRegular_class_of_code_modTwo,
          _root_.PRegularConjClass.coe_ofSubtype] using
          alternating_group_fin5_pRegular_representative_modTwo_spec
            (alternating_group_fin5_pRegular_class_of_code_modTwo
              BrauerProjectiveModTwo.degreeTwo_from_chi3_phi_psi)
      have hnot1 :
          ¬ orderOf
              (alternating_group_fin5_pRegular_representative_modTwo
                (alternating_group_fin5_pRegular_class_of_code_modTwo
                  BrauerProjectiveModTwo.degreeTwo_from_chi3_phi_psi)).1 = 1 := by
        simpa [horder] using (show ¬ (5 = 1) by decide)
      have hnot3 :
          ¬ orderOf
              (alternating_group_fin5_pRegular_representative_modTwo
                (alternating_group_fin5_pRegular_class_of_code_modTwo
                  BrauerProjectiveModTwo.degreeTwo_from_chi3_phi_psi)).1 = 3 := by
        simpa [horder] using (show ¬ (5 = 3) by decide)
      -- The chosen `φ`-oriented `5`-cycle class is detected by the final conjugacy test.
      simp [alternating_group_fin5_pRegular_code_modTwo, hnot1, hnot3]
      exact alternating_group_fin5_isConj_iff_subtype_exists.mp hconj
  | degreeTwo_from_chi3_psi_phi =>
      have horder :
          orderOf
              (alternating_group_fin5_pRegular_representative_modTwo
                (alternating_group_fin5_pRegular_class_of_code_modTwo
                  BrauerProjectiveModTwo.degreeTwo_from_chi3_psi_phi)).1 = 5 := by
        simpa [alternating_group_fin5_pRegular_class_of_code_modTwo,
          a5_generator_five_sq_pRegular_modTwo, a5_generator_five_sq_order] using
          alternating_group_fin5_orderOf_representative_ofSubtype_modTwo
            a5_generator_five_sq_pRegular_modTwo
      have hconj_inv :
          IsConj
            (alternating_group_fin5_pRegular_representative_modTwo
              (alternating_group_fin5_pRegular_class_of_code_modTwo
                BrauerProjectiveModTwo.degreeTwo_from_chi3_psi_phi)).1
            (a5_generator_five ^ 2) := by
        apply (ConjClasses.mk_eq_mk_iff_isConj).1
        simpa [alternating_group_fin5_pRegular_class_of_code_modTwo,
          a5_generator_five_sq_pRegular_modTwo, _root_.PRegularConjClass.coe_ofSubtype] using
          alternating_group_fin5_pRegular_representative_modTwo_spec
            (alternating_group_fin5_pRegular_class_of_code_modTwo
              BrauerProjectiveModTwo.degreeTwo_from_chi3_psi_phi)
      have hnot_conj :
          ¬ IsConj
            (alternating_group_fin5_pRegular_representative_modTwo
              (alternating_group_fin5_pRegular_class_of_code_modTwo
                BrauerProjectiveModTwo.degreeTwo_from_chi3_psi_phi)).1
            a5_generator_five := by
        intro hconj
        exact a5_generator_five_not_isConj_sq
          (hconj.symm.trans hconj_inv)
      have hnot1 :
          ¬ orderOf
              (alternating_group_fin5_pRegular_representative_modTwo
                (alternating_group_fin5_pRegular_class_of_code_modTwo
                  BrauerProjectiveModTwo.degreeTwo_from_chi3_psi_phi)).1 = 1 := by
        simpa [horder] using (show ¬ (5 = 1) by decide)
      have hnot3 :
          ¬ orderOf
              (alternating_group_fin5_pRegular_representative_modTwo
                (alternating_group_fin5_pRegular_class_of_code_modTwo
                  BrauerProjectiveModTwo.degreeTwo_from_chi3_psi_phi)).1 = 3 := by
        simpa [horder] using (show ¬ (5 = 3) by decide)
      -- The square `5`-cycle class is forced when the `φ`-test fails.
      simp [alternating_group_fin5_pRegular_code_modTwo, hnot1, hnot3]
      intro x hx hconj
      exact hnot_conj (alternating_group_fin5_isConj_iff_subtype_exists.mpr ⟨x, hx, hconj⟩)
  | degreeFour =>
      have horder :
          orderOf
              (alternating_group_fin5_pRegular_representative_modTwo
                (alternating_group_fin5_pRegular_class_of_code_modTwo
                  BrauerProjectiveModTwo.degreeFour)).1 = 3 := by
        simpa [alternating_group_fin5_pRegular_class_of_code_modTwo,
          a5_generator_three_pRegular_modTwo, a5_generator_three_order] using
          alternating_group_fin5_orderOf_representative_ofSubtype_modTwo
            a5_generator_three_pRegular_modTwo
      have hnot1 :
          ¬ orderOf
              (alternating_group_fin5_pRegular_representative_modTwo
                (alternating_group_fin5_pRegular_class_of_code_modTwo
                  BrauerProjectiveModTwo.degreeFour)).1 = 1 := by
        simpa [horder] using (show ¬ (3 = 1) by decide)
      -- The unique `3`-cycle class is coded by the degree-`4` Brauer label.
      simp [alternating_group_fin5_pRegular_code_modTwo, hnot1, horder]

/-- Helper for Exercise 18-18.6-3: the Brauer code classifies every `2`-regular conjugacy class
of `A₅`. -/
private theorem alternating_group_fin5_pRegular_code_modTwo_left_inv
    (c : PRegularConjClass A5 2) :
    alternating_group_fin5_pRegular_class_of_code_modTwo
      (alternating_group_fin5_pRegular_code_modTwo c) = c := by
  let repC := (alternating_group_fin5_pRegular_representative_modTwo c).1
  have hrep_regular : IsPRegular 2 repC :=
    (alternating_group_fin5_pRegular_representative_modTwo c).2
  rcases alternating_group_fin5_pRegular_order_eq_one_or_three_or_five repC hrep_regular with
    h1 | h3 | h5
  · have hcode :
        alternating_group_fin5_pRegular_code_modTwo c = BrauerProjectiveModTwo.trivial := by
      simp [alternating_group_fin5_pRegular_code_modTwo, repC, h1]
    have hrep : repC = 1 := orderOf_eq_one_iff.mp h1
    -- The identity is the only `2`-regular class of order `1`.
    apply Subtype.ext
    calc
      (alternating_group_fin5_pRegular_class_of_code_modTwo
          (alternating_group_fin5_pRegular_code_modTwo c) : ConjClasses A5)
          = ConjClasses.mk (1 : A5) := by
              simp [hcode, alternating_group_fin5_pRegular_class_of_code_modTwo,
                a5_one_pRegular_modTwo, _root_.PRegularConjClass.coe_ofSubtype]
      _ = ConjClasses.mk repC := by simpa [hrep]
      _ = c.1 := alternating_group_fin5_pRegular_representative_modTwo_spec c
  · have hnot1 : ¬ orderOf repC = 1 := by
      simpa [h3] using (show ¬ (3 = 1) by decide)
    have hcode :
        alternating_group_fin5_pRegular_code_modTwo c = BrauerProjectiveModTwo.degreeFour := by
      simp [alternating_group_fin5_pRegular_code_modTwo, repC, hnot1, h3]
    have hrep3 : repC ^ 3 = 1 := by
      simpa [h3] using pow_orderOf_eq_one repC
    have hrep2ne : repC ^ 2 ≠ 1 := by
      intro hsq
      have hdiv : orderOf repC ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
      have : ¬ 3 ∣ 2 := by decide
      exact this <| h3 ▸ hdiv
    have hgen3 : a5_generator_three ^ 3 = 1 := by
      simpa [a5_generator_three_order] using pow_orderOf_eq_one a5_generator_three
    have hgen2ne : a5_generator_three ^ 2 ≠ 1 := by
      intro hsq
      have hdiv : orderOf a5_generator_three ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
      have : ¬ 3 ∣ 2 := by decide
      exact this <| a5_generator_three_order ▸ hdiv
    have hconj : IsConj repC a5_generator_three := by
      exact alternating_group_fin5_isConj_of_cube_eq_one_sq_ne_one
        hrep3 hrep2ne hgen3 hgen2ne
    -- The unique `3`-cycle class is the one coded by `degreeFour`.
    apply Subtype.ext
    calc
      (alternating_group_fin5_pRegular_class_of_code_modTwo
          (alternating_group_fin5_pRegular_code_modTwo c) : ConjClasses A5)
          = ConjClasses.mk a5_generator_three := by
              simp [hcode, alternating_group_fin5_pRegular_class_of_code_modTwo,
                a5_generator_three_pRegular_modTwo, _root_.PRegularConjClass.coe_ofSubtype]
      _ = ConjClasses.mk repC := by
            exact (ConjClasses.mk_eq_mk_iff_isConj).2 hconj.symm
      _ = c.1 := alternating_group_fin5_pRegular_representative_modTwo_spec c
  · have hnot1 : ¬ orderOf repC = 1 := by
      simpa [h5] using (show ¬ (5 = 1) by decide)
    have hnot3 : ¬ orderOf repC = 3 := by
      simpa [h5] using (show ¬ (5 = 3) by decide)
    by_cases hphi : IsConj repC a5_generator_five
    · have hcode :
          alternating_group_fin5_pRegular_code_modTwo c =
            BrauerProjectiveModTwo.degreeTwo_from_chi3_phi_psi := by
        simp [alternating_group_fin5_pRegular_code_modTwo, repC, hnot1, hnot3]
        exact alternating_group_fin5_isConj_iff_subtype_exists.mp hphi
      -- The `φ`-oriented `5`-cycle class is represented by `a5_generator_five`.
      apply Subtype.ext
      calc
        (alternating_group_fin5_pRegular_class_of_code_modTwo
            (alternating_group_fin5_pRegular_code_modTwo c) : ConjClasses A5)
            = ConjClasses.mk a5_generator_five := by
                simp [hcode, alternating_group_fin5_pRegular_class_of_code_modTwo,
                  a5_generator_five_pRegular_modTwo, _root_.PRegularConjClass.coe_ofSubtype]
        _ = ConjClasses.mk repC := by
              exact (ConjClasses.mk_eq_mk_iff_isConj).2 hphi.symm
        _ = c.1 := alternating_group_fin5_pRegular_representative_modTwo_spec c
    · have hpsi : IsConj repC (a5_generator_five ^ 2) :=
        alternating_group_fin5_isConj_of_order_five_not_phi h5 hphi
      have hcode :
          alternating_group_fin5_pRegular_code_modTwo c =
            BrauerProjectiveModTwo.degreeTwo_from_chi3_psi_phi := by
        simp [alternating_group_fin5_pRegular_code_modTwo, repC, hnot1, hnot3]
        intro x hx hconj
        exact hphi (alternating_group_fin5_isConj_iff_subtype_exists.mpr ⟨x, hx, hconj⟩)
      -- The second split `5`-cycle class is represented by the square `5`-cycle.
      apply Subtype.ext
      calc
        (alternating_group_fin5_pRegular_class_of_code_modTwo
            (alternating_group_fin5_pRegular_code_modTwo c) : ConjClasses A5)
            = ConjClasses.mk (a5_generator_five ^ 2) := by
                simp [hcode, alternating_group_fin5_pRegular_class_of_code_modTwo,
                  a5_generator_five_sq_pRegular_modTwo,
                  _root_.PRegularConjClass.coe_ofSubtype]
        _ = ConjClasses.mk repC := by
              exact (ConjClasses.mk_eq_mk_iff_isConj).2 hpsi.symm
        _ = c.1 := alternating_group_fin5_pRegular_representative_modTwo_spec c

/-- Helper for Exercise 18-18.6-3: the `2`-regular conjugacy classes of `A₅` can be indexed by
Serre's four Brauer labels. -/
noncomputable def alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels :
    PRegularConjClass A5 2 ≃ BrauerProjectiveModTwo :=
  { toFun := alternating_group_fin5_pRegular_code_modTwo
    invFun := alternating_group_fin5_pRegular_class_of_code_modTwo
    left_inv := alternating_group_fin5_pRegular_code_modTwo_left_inv
    right_inv := alternating_group_fin5_pRegular_code_modTwo_right_inv }

/-- Helper for Exercise 18-18.6-3: on the explicit four `2`-regular classes of `A₅`, the source
function `χ₃,φ,ψ - χ₁` is exactly the degree-`2` Brauer slot attached to
`degreeTwo_from_chi3_phi_psi`. -/
theorem a5_source_degree_two_character_function_phi_modTwo :
    (fun c : PRegularConjClass A5 2 ↦
      (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi3_phi_psi : 𝔽₄) -
        (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi1 : 𝔽₄)) =
      fun c ↦
        match alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c with
        | .trivial => 0
        | .degreeTwo_from_chi3_phi_psi => 1
        | .degreeTwo_from_chi3_psi_phi => 0
        | .degreeFour => 0 := by
  -- Evaluate after reindexing by the explicit Brauer-label equivalence and reduce to the four
  -- decomposition-table entries.
  ext c
  cases hφ : alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c <;>
    simp [hφ, alternating_group_five_decomposition_matrix_mod_two]

/-- Helper for Exercise 18-18.6-3: on the explicit four `2`-regular classes of `A₅`, the source
function `χ₃,ψ,φ - χ₁` is exactly the degree-`2` Brauer slot attached to
`degreeTwo_from_chi3_psi_phi`. -/
theorem a5_source_degree_two_character_function_psi_modTwo :
    (fun c : PRegularConjClass A5 2 ↦
      (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi3_psi_phi : 𝔽₄) -
        (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi1 : 𝔽₄)) =
      fun c ↦
        match alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c with
        | .trivial => 0
        | .degreeTwo_from_chi3_phi_psi => 0
        | .degreeTwo_from_chi3_psi_phi => 1
        | .degreeFour => 0 := by
  -- The companion source row isolates the other degree-`2` Brauer slot after subtracting the
  -- trivial constituent.
  ext c
  cases hφ : alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c <;>
    simp [hφ, alternating_group_five_decomposition_matrix_mod_two]

end Representation
