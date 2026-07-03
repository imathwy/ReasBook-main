import Mathlib
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_1
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1.RegularConjClassCore

noncomputable section

open Representation
open scoped MatrixGroups

local notation "A5" => alternatingGroup (Fin 5)

/-- Helper for Exercise 18-18.6-4: the explicit order-`5` generator used in the finite `A₅`
lookup witness. -/
def a5_generator_five : A5 :=
  ⟨finRotate 5, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

/-- Helper for Exercise 18-18.6-4: the explicit order-`2` generator used in the finite `A₅`
lookup witness. -/
def a5_generator_two : A5 :=
  ⟨Equiv.swap 1 2 * Equiv.swap 3 4, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

/-- Helper for Exercise 18-18.6-4: the explicit order-`5` lift in `SL(2, 𝔽₅)` whose class
generates the `PSL₂(𝔽₅)` side of the lookup witness. -/
def sl_generator_five : SL(2, ZMod 5) :=
  ⟨!![(1 : ZMod 5), 1; 0, 1], by
    simp [Matrix.det_fin_two]⟩

/-- Helper for Exercise 18-18.6-4: the explicit order-`2` lift in `SL(2, 𝔽₅)` whose class
generates the `PSL₂(𝔽₅)` side of the lookup witness. -/
def sl_generator_two : SL(2, ZMod 5) :=
  ⟨!![(0 : ZMod 5), -1; 1, 0], by
    simp [Matrix.det_fin_two]⟩

/-- Helper for Exercise 18-18.6-4: the distinguished projective order-`5` generator. -/
def psl_generator_five : PSL(2, ZMod 5) :=
  QuotientGroup.mk sl_generator_five

/-- Helper for Exercise 18-18.6-4: the distinguished projective order-`2` generator. -/
def psl_generator_two : PSL(2, ZMod 5) :=
  QuotientGroup.mk sl_generator_two

/-- Helper for Exercise 18-18.6-4: the chosen `A₅` generators satisfy LinearRepresentations_Serre_1977's `2,3,5` triangle
relations. -/
theorem a5_generator_triangle_relations :
    a5_generator_five ^ 5 = 1 ∧
      a5_generator_two ^ 2 = 1 ∧
      (a5_generator_five * a5_generator_two) ^ 3 = 1 := by
  decide

/-- Helper for Exercise 18-18.6-4: the chosen `PSL₂(𝔽₅)` generators satisfy the same `2,3,5`
triangle relations. -/
theorem psl_generator_triangle_relations :
    psl_generator_five ^ 5 = 1 ∧
      psl_generator_two ^ 2 = 1 ∧
      (psl_generator_five * psl_generator_two) ^ 3 = 1 := by
  native_decide

/-- Helper for Exercise 18-18.6-4: the LinearRepresentations_Serre_1977 generator product gives an explicit order-`3`
element of `A₅`. -/
def a5_generator_three : A5 :=
  a5_generator_five * a5_generator_two

/-- Helper for Exercise 18-18.6-4: the identity of `A₅` is `5`-regular. -/
theorem alternating_group_fin5_one_isPRegular :
    IsPRegular 5 (1 : A5) := by
  simp [IsPRegular]

/-- Helper for Exercise 18-18.6-4: the explicit involution generator has order `2`. -/
theorem alternating_group_fin5_generator_two_order :
    orderOf a5_generator_two = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · simpa using a5_generator_triangle_relations.2.1
  · decide

/-- Helper for Exercise 18-18.6-4: the explicit `3`-cycle generator has order `3`. -/
theorem alternating_group_fin5_generator_three_order :
    orderOf a5_generator_three = 3 := by
  refine orderOf_eq_prime ?_ ?_
  · simpa using a5_generator_triangle_relations.2.2
  · decide

/-- Helper for Exercise 18-18.6-4: the explicit order-`2` generator is `5`-regular. -/
theorem alternating_group_fin5_generator_two_isPRegular :
    IsPRegular 5 a5_generator_two := by
  have hcop : Nat.Coprime 5 2 := by decide
  simpa [IsPRegular, alternating_group_fin5_generator_two_order] using hcop

/-- Helper for Exercise 18-18.6-4: the explicit order-`3` generator is `5`-regular. -/
theorem alternating_group_fin5_generator_three_isPRegular :
    IsPRegular 5 a5_generator_three := by
  have hcop : Nat.Coprime 5 3 := by decide
  simpa [IsPRegular, alternating_group_fin5_generator_three_order] using hcop

/-- Helper for Exercise 18-18.6-4: every element of `A₅` has one of the power patterns forced by
cycle types on five letters. -/
theorem alternating_group_fin5_pow_eq_one_in_small_degree
    (g : A5) :
    g = 1 ∨
      (g ^ 2 = 1 ∧ g ≠ 1) ∨
        (g ^ 3 = 1 ∧ g ^ 2 ≠ 1) ∨
          (g ^ 5 = 1 ∧ g ^ 3 ≠ 1 ∧ g ^ 2 ≠ 1) := by
  revert g
  native_decide

/-- Helper for Exercise 18-18.6-4: all nontrivial involutions in `A₅` are conjugate. -/
theorem alternating_group_fin5_isConj_of_square_eq_one_ne_one
    {g h : A5} (hg₂ : g ^ 2 = 1) (hg₁ : g ≠ 1)
    (hh₂ : h ^ 2 = 1) (hh₁ : h ≠ 1) :
    IsConj g h := by
  revert hh₁ hh₂ hg₁ hg₂ h g
  native_decide

/-- Helper for Exercise 18-18.6-4: all order-`3` elements of `A₅` are conjugate. -/
theorem alternating_group_fin5_isConj_of_cube_eq_one_sq_ne_one
    {g h : A5} (hg₃ : g ^ 3 = 1) (hg₂ : g ^ 2 ≠ 1)
    (hh₃ : h ^ 3 = 1) (hh₂ : h ^ 2 ≠ 1) :
    IsConj g h := by
  revert hh₂ hh₃ hg₂ hg₃ h g
  native_decide

/-- Helper for Exercise 18-18.6-4: every `5`-regular element of `A₅` has order `1`, `2`, or
`3`. -/
theorem alternating_group_fin5_pRegular_order_eq_one_or_two_or_three
    (g : A5) (hg : IsPRegular 5 g) :
    orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 3 := by
  rcases alternating_group_fin5_pow_eq_one_in_small_degree g with h1 | h2 | h3 | h5
  · exact Or.inl (orderOf_eq_one_iff.mpr h1)
  · right
    left
    exact orderOf_eq_prime h2.1 h2.2
  · right
    right
    have hg_ne : g ≠ 1 := by
      intro hg1
      exact h3.2 <| by simp [hg1]
    exact orderOf_eq_prime h3.1 hg_ne
  · have hg_ne : g ≠ 1 := by
      intro hg1
      exact h5.2.2 <| by simp [hg1]
    letI : Fact (Nat.Prime 5) := ⟨by decide⟩
    have horder : orderOf g = 5 := orderOf_eq_prime h5.1 hg_ne
    have hregular_order : Nat.Coprime 5 (orderOf g) := by
      simpa [IsPRegular] using hg
    have hcop : Nat.Coprime 5 5 := by
      rw [horder] at hregular_order
      exact hregular_order
    have : ¬ Nat.Coprime 5 5 := by decide
    exact False.elim (this hcop)

/-- Helper for Exercise 18-18.6-4: within the `5`-regular locus of `A₅`, the order determines
the conjugacy class. -/
theorem alternating_group_fin5_isConj_of_pRegular_same_order
    {g h : A5} (hg : IsPRegular 5 g) (_hh : IsPRegular 5 h)
    (hord : orderOf g = orderOf h) :
    IsConj g h := by
  rcases alternating_group_fin5_pRegular_order_eq_one_or_two_or_three g hg with
    hg1 | hg2 | hg3
  · have hh1 : orderOf h = 1 := hord.symm.trans hg1
    have hg' : g = 1 := orderOf_eq_one_iff.mp hg1
    have hh' : h = 1 := orderOf_eq_one_iff.mp hh1
    exact isConj_iff.2 ⟨1, by simp [hg', hh']⟩
  · have hh2 : orderOf h = 2 := hord.symm.trans hg2
    apply alternating_group_fin5_isConj_of_square_eq_one_ne_one
    · simpa [hg2] using pow_orderOf_eq_one g
    · intro hg1
      simp [hg1] at hg2
    · simpa [hh2] using pow_orderOf_eq_one h
    · intro hh1
      simp [hh1] at hh2
  · have hh3 : orderOf h = 3 := hord.symm.trans hg3
    apply alternating_group_fin5_isConj_of_cube_eq_one_sq_ne_one
    · simpa [hg3] using pow_orderOf_eq_one g
    · intro hg2
      have hdiv : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg2
      have : ¬ 3 ∣ 2 := by decide
      exact this <| hg3 ▸ hdiv
    · simpa [hh3] using pow_orderOf_eq_one h
    · intro hh2
      have hdiv : orderOf h ∣ 2 := orderOf_dvd_of_pow_eq_one hh2
      have : ¬ 3 ∣ 2 := by decide
      exact this <| hh3 ▸ hdiv

/-- Helper for Exercise 18-18.6-4: choose a representative of a `5`-regular conjugacy class of
`A₅`. -/
noncomputable def alternating_group_fin5_pRegular_representative
    (c : _root_.PRegularConjClass A5 5) : { x : A5 // IsPRegular 5 x } :=
  let g : A5 := Classical.choose (ConjClasses.mk_surjective (c : ConjClasses A5))
  let hg : ConjClasses.mk g = (c : ConjClasses A5) :=
    Classical.choose_spec (ConjClasses.mk_surjective (c : ConjClasses A5))
  ⟨g, c.2 g (ConjClasses.mem_carrier_iff_mk_eq.mpr hg)⟩

/-- Helper for Exercise 18-18.6-4: the chosen representative lies in the prescribed conjugacy
class. -/
theorem alternating_group_fin5_pRegular_representative_spec
    (c : _root_.PRegularConjClass A5 5) :
    ConjClasses.mk (alternating_group_fin5_pRegular_representative c).1 = (c : ConjClasses A5) := by
  simpa [alternating_group_fin5_pRegular_representative] using
    Classical.choose_spec (ConjClasses.mk_surjective (c : ConjClasses A5))

/-- Helper for Exercise 18-18.6-4: a chosen representative of `PRegularConjClass.ofSubtype`
has the same order as the original `A₅` element. -/
theorem alternating_group_fin5_orderOf_representative_ofSubtype
    (s : { x : A5 // IsPRegular 5 x }) :
    orderOf
        (alternating_group_fin5_pRegular_representative
          (_root_.PRegularConjClass.ofSubtype (G := A5) 5 s)).1 =
      orderOf s.1 := by
  have hconj :
      IsConj
        (alternating_group_fin5_pRegular_representative
          (_root_.PRegularConjClass.ofSubtype (G := A5) 5 s)).1
        s.1 := by
    apply (ConjClasses.mk_eq_mk_iff_isConj).1
    simpa [_root_.PRegularConjClass.coe_ofSubtype] using
      alternating_group_fin5_pRegular_representative_spec
        (_root_.PRegularConjClass.ofSubtype (G := A5) 5 s)
  rcases hconj with ⟨c, hc⟩
  simpa using hc.orderOf_eq

/-- Helper for Exercise 18-18.6-4: code the three `5`-regular conjugacy classes of `A₅` by the
orders `1`, `2`, and `3`. -/
noncomputable def alternating_group_fin5_pRegular_code
    (c : _root_.PRegularConjClass A5 5) : Fin 3 :=
  let g := (alternating_group_fin5_pRegular_representative c).1
  if _h1 : orderOf g = 1 then 0
  else if _h2 : orderOf g = 2 then 1
  else 2

/-- Helper for Exercise 18-18.6-4: the code attached to a `5`-regular class records the order of
its chosen representative. -/
theorem alternating_group_fin5_pRegular_code_spec
    (c : _root_.PRegularConjClass A5 5) :
    orderOf (alternating_group_fin5_pRegular_representative c).1 =
      match alternating_group_fin5_pRegular_code c with
      | 0 => 1
      | 1 => 2
      | 2 => 3 := by
  let g := (alternating_group_fin5_pRegular_representative c).1
  have hg : IsPRegular 5 g := (alternating_group_fin5_pRegular_representative c).2
  by_cases h1 : orderOf g = 1
  · simp [alternating_group_fin5_pRegular_code, g, h1]
  · by_cases h2 : orderOf g = 2
    · simp [alternating_group_fin5_pRegular_code, g, h2]
    · have h3 : orderOf g = 3 := by
        rcases alternating_group_fin5_pRegular_order_eq_one_or_two_or_three g hg with
          hg1 | hg2 | hg3
        · exact False.elim (h1 hg1)
        · exact False.elim (h2 hg2)
        · exact hg3
      simp [alternating_group_fin5_pRegular_code, g, h3]

/-- Helper for Exercise 18-18.6-4: pick concrete `A₅` representatives for the three
`5`-regular conjugacy classes. -/
def alternating_group_fin5_pRegular_class_of_code :
    Fin 3 → _root_.PRegularConjClass A5 5
  | 0 =>
      _root_.PRegularConjClass.ofSubtype (G := A5) 5
        ⟨1, alternating_group_fin5_one_isPRegular⟩
  | 1 =>
      _root_.PRegularConjClass.ofSubtype (G := A5) 5
        ⟨a5_generator_two, alternating_group_fin5_generator_two_isPRegular⟩
  | 2 =>
      _root_.PRegularConjClass.ofSubtype (G := A5) 5
        ⟨a5_generator_three, alternating_group_fin5_generator_three_isPRegular⟩

/-- Helper for Exercise 18-18.6-4: the chosen representative of
`alternating_group_fin5_pRegular_class_of_code i` has the expected order. -/
theorem alternating_group_fin5_pRegular_class_of_code_spec
    (i : Fin 3) :
    orderOf
        (alternating_group_fin5_pRegular_representative
          (alternating_group_fin5_pRegular_class_of_code i)).1 =
      match i with
      | 0 => 1
      | 1 => 2
      | 2 => 3 := by
  fin_cases i
  · simpa [alternating_group_fin5_pRegular_class_of_code] using
      alternating_group_fin5_orderOf_representative_ofSubtype
        ⟨1, alternating_group_fin5_one_isPRegular⟩
  · simpa [alternating_group_fin5_pRegular_class_of_code,
      alternating_group_fin5_generator_two_order] using
      alternating_group_fin5_orderOf_representative_ofSubtype
        ⟨a5_generator_two, alternating_group_fin5_generator_two_isPRegular⟩
  · simpa [alternating_group_fin5_pRegular_class_of_code,
      alternating_group_fin5_generator_three_order] using
      alternating_group_fin5_orderOf_representative_ofSubtype
        ⟨a5_generator_three, alternating_group_fin5_generator_three_isPRegular⟩

/-- Helper for Exercise 18-18.6-4: the concrete order-code representatives recover their own
code. -/
theorem alternating_group_fin5_pRegular_code_right_inv
    (i : Fin 3) :
    alternating_group_fin5_pRegular_code
      (alternating_group_fin5_pRegular_class_of_code i) = i := by
  fin_cases i
  · have hrep :
        (alternating_group_fin5_pRegular_representative
          (alternating_group_fin5_pRegular_class_of_code 0)).1 = 1 := by
        exact orderOf_eq_one_iff.mp (alternating_group_fin5_pRegular_class_of_code_spec 0)
    simp [alternating_group_fin5_pRegular_code, hrep]
  · have hrep_ne : (alternating_group_fin5_pRegular_representative
        (alternating_group_fin5_pRegular_class_of_code 1)).1 ≠ 1 := by
        intro h
        have horder : orderOf
            (alternating_group_fin5_pRegular_representative
              (alternating_group_fin5_pRegular_class_of_code 1)).1 = 1 := by
          exact orderOf_eq_one_iff.mpr h
        simp [alternating_group_fin5_pRegular_class_of_code_spec 1] at horder
    have horder : orderOf
        (alternating_group_fin5_pRegular_representative
          (alternating_group_fin5_pRegular_class_of_code 1)).1 = 2 :=
      alternating_group_fin5_pRegular_class_of_code_spec 1
    simp [alternating_group_fin5_pRegular_code, horder]
  · have hrep_ne : (alternating_group_fin5_pRegular_representative
        (alternating_group_fin5_pRegular_class_of_code 2)).1 ≠ 1 := by
        intro h
        have horder : orderOf
            (alternating_group_fin5_pRegular_representative
              (alternating_group_fin5_pRegular_class_of_code 2)).1 = 1 := by
          exact orderOf_eq_one_iff.mpr h
        simp [alternating_group_fin5_pRegular_class_of_code_spec 2] at horder
    have horder_ne : orderOf
        (alternating_group_fin5_pRegular_representative
          (alternating_group_fin5_pRegular_class_of_code 2)).1 ≠ 2 := by
        intro h
        simp [alternating_group_fin5_pRegular_class_of_code_spec 2] at h
    simp [alternating_group_fin5_pRegular_code, hrep_ne, horder_ne]

/-- Helper for Exercise 18-18.6-4: the order code classifies every `5`-regular conjugacy class
of `A₅`. -/
theorem alternating_group_fin5_pRegular_code_left_inv
    (c : _root_.PRegularConjClass A5 5) :
    alternating_group_fin5_pRegular_class_of_code
      (alternating_group_fin5_pRegular_code c) = c := by
  let repC := (alternating_group_fin5_pRegular_representative c).1
  let repI :=
    (alternating_group_fin5_pRegular_representative
      (alternating_group_fin5_pRegular_class_of_code
        (alternating_group_fin5_pRegular_code c))).1
  have hconj : IsConj repC repI := by
    apply alternating_group_fin5_isConj_of_pRegular_same_order
    · exact (alternating_group_fin5_pRegular_representative c).2
    · exact
        (alternating_group_fin5_pRegular_representative
          (alternating_group_fin5_pRegular_class_of_code
            (alternating_group_fin5_pRegular_code c))).2
    · exact
        (alternating_group_fin5_pRegular_code_spec c).trans
          (alternating_group_fin5_pRegular_class_of_code_spec
            (alternating_group_fin5_pRegular_code c)).symm
  apply Subtype.ext
  calc
    (alternating_group_fin5_pRegular_class_of_code
        (alternating_group_fin5_pRegular_code c) : ConjClasses A5)
        = ConjClasses.mk repI := by
            symm
            exact alternating_group_fin5_pRegular_representative_spec _
    _ = ConjClasses.mk repC := by
          exact (ConjClasses.mk_eq_mk_iff_isConj).2 hconj.symm
    _ = c.1 := alternating_group_fin5_pRegular_representative_spec c

/-- Helper for Exercise 18-18.6-4: `A₅` has exactly three `5`-regular conjugacy classes. -/
theorem alternatingGroup_fin5_pRegularConjClass_modFive_card_eq_three :
    Nat.card (_root_.PRegularConjClass A5 5) = 3 := by
  let e : _root_.PRegularConjClass A5 5 ≃ Fin 3 :=
    { toFun := alternating_group_fin5_pRegular_code
      invFun := alternating_group_fin5_pRegular_class_of_code
      left_inv := alternating_group_fin5_pRegular_code_left_inv
      right_inv := alternating_group_fin5_pRegular_code_right_inv }
  simpa using Nat.card_congr e
