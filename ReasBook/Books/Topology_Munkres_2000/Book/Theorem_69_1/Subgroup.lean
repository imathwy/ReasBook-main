module

public import Mathlib.LinearAlgebra.FreeModule.Basic

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Finset.Max
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.SetTheory.Cardinal.Order

public section

universe u

namespace Finsupp

/-- Helper for Theorem 69.1: a triangular family of finitely supported vectors with
nonzero diagonal entries is linearly independent. -/
lemma linearIndependent_of_support_le {R : Type*} [CommRing R] [IsDomain R]
    {ι : Type*} [LinearOrder ι] {J : Set ι} (v : J → ι →₀ R)
    (support_le : ∀ j, ↑(v j).support ⊆ Set.Iic j.1)
    (diagonal_ne : ∀ j, v j j ≠ 0) : LinearIndependent R v := by
  rw [linearIndependent_iff]
  intro l combination_eq_zero
  -- A nonzero relation has a greatest active index because its coefficients are finitely supported.
  by_contra l_ne_zero
  have support_nonempty : l.support.Nonempty := Finsupp.support_nonempty_iff.mpr l_ne_zero
  let k := l.support.max' support_nonempty
  have k_mem : k ∈ l.support := Finset.max'_mem l.support support_nonempty
  have relation_at_k := congrArg (fun x : ι →₀ R ↦ x k) combination_eq_zero
  have lower_coordinates_vanish :
      ∀ (j : J), l j ≠ 0 → j ≠ k → l j * v j k = 0 := by
    intro j coefficient_ne_zero j_ne_k
    have j_le_k : j ≤ k := Finset.le_max' l.support j
      (Finsupp.mem_support_iff.mpr coefficient_ne_zero)
    have j_lt_k : j < k := lt_of_le_of_ne j_le_k j_ne_k
    have coordinate_eq_zero : v j k = 0 := by
      by_contra coordinate_ne_zero
      have k_le_j : (k : ι) ≤ j :=
        support_le j (Finsupp.mem_support_iff.mpr coordinate_ne_zero)
      exact (not_le_of_gt j_lt_k) k_le_j
    rw [coordinate_eq_zero, mul_zero]
  -- Evaluating at the greatest index leaves only its diagonal summand.
  have single_term :
      l.sum (fun j a ↦ a * v j k) = l k * v k k := by
    exact Finsupp.sum_eq_single k lower_coordinates_vanish (fun _ ↦ zero_mul _)
  have diagonal_product_eq_zero : l k * v k k = 0 := by
    rw [← single_term]
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum_apply, Finsupp.smul_apply,
      Finsupp.zero_apply, smul_eq_mul] using relation_at_k
  exact (Finsupp.mem_support_iff.mp k_mem)
    ((mul_eq_zero.mp diagonal_product_eq_zero).resolve_right (diagonal_ne k))

end Finsupp

namespace Module.Free

section FinsuppSubmodule

variable {ι : Type*} [LinearOrder ι]

/-- Helper for Theorem 69.1: the ideal of possible `i`-th coefficients of vectors in `N`
whose support is bounded above by `i`. -/
private noncomputable def leadingCoeffIdeal (N : Submodule ℤ (ι →₀ ℤ)) (i : ι) :
    Submodule ℤ ℤ :=
  (N ⊓ Finsupp.supported ℤ ℤ (Set.Iic i)).map (Finsupp.lapply i)

/-- Helper for Theorem 69.1: membership in `leadingCoeffIdeal N i` is witnessed by a vector
of `N` supported at or below `i`. -/
private lemma mem_leadingCoeffIdeal_iff (N : Submodule ℤ (ι →₀ ℤ)) (i : ι) (z : ℤ) :
    z ∈ leadingCoeffIdeal N i ↔
      ∃ x : N, (x : ι →₀ ℤ) ∈ Finsupp.supported ℤ ℤ (Set.Iic i) ∧ (x : ι →₀ ℤ) i = z := by
  -- Unpack the range of coordinate evaluation on the bounded-support intersection.
  constructor
  · intro hz
    obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.mp hz
    exact ⟨⟨y, hy.1⟩, hy.2, hyz⟩
  · rintro ⟨x, support_x, coefficient_x⟩
    exact Submodule.mem_map.mpr ⟨x, ⟨x.property, support_x⟩, coefficient_x⟩

/-- Helper for Theorem 69.1: indices at which the bounded coefficient ideal of `N` is
nonzero. -/
private abbrev LeadingIndex (N : Submodule ℤ (ι →₀ ℤ)) :=
  {i : ι // leadingCoeffIdeal N i ≠ ⊥}

/-- Helper for Theorem 69.1: the chosen vector whose leading coefficient generates the
bounded coefficient ideal at `j`. -/
private noncomputable def pivotVector (N : Submodule ℤ (ι →₀ ℤ)) (j : LeadingIndex N) : N :=
  Classical.choose
    ((mem_leadingCoeffIdeal_iff N j.1
      (Submodule.IsPrincipal.generator (leadingCoeffIdeal N j.1))).mp
      (Submodule.IsPrincipal.generator_mem (leadingCoeffIdeal N j.1)))

/-- Helper for Theorem 69.1: a pivot vector has no support strictly above its index. -/
private lemma pivotVector_mem_supported (N : Submodule ℤ (ι →₀ ℤ)) (j : LeadingIndex N) :
    (pivotVector N j : ι →₀ ℤ) ∈ Finsupp.supported ℤ ℤ (Set.Iic j.1) := by
  -- This is the bounded-support projection of the chosen coefficient-ideal witness.
  exact (Classical.choose_spec
    ((mem_leadingCoeffIdeal_iff N j.1
      (Submodule.IsPrincipal.generator (leadingCoeffIdeal N j.1))).mp
      (Submodule.IsPrincipal.generator_mem (leadingCoeffIdeal N j.1)))).1

/-- Helper for Theorem 69.1: the leading coefficient of a pivot is the generator of its
coefficient ideal. -/
private lemma pivotVector_apply (N : Submodule ℤ (ι →₀ ℤ)) (j : LeadingIndex N) :
    (pivotVector N j : ι →₀ ℤ) j.1 =
      Submodule.IsPrincipal.generator (leadingCoeffIdeal N j.1) := by
  -- This is the coefficient projection of the same chosen witness.
  exact (Classical.choose_spec
    ((mem_leadingCoeffIdeal_iff N j.1
      (Submodule.IsPrincipal.generator (leadingCoeffIdeal N j.1))).mp
      (Submodule.IsPrincipal.generator_mem (leadingCoeffIdeal N j.1)))).2

/-- Helper for Theorem 69.1: every pivot has a nonzero leading coefficient. -/
private lemma pivotVector_apply_ne_zero (N : Submodule ℤ (ι →₀ ℤ)) (j : LeadingIndex N) :
    (pivotVector N j : ι →₀ ℤ) j.1 ≠ 0 := by
  -- A zero generator would make the defining coefficient ideal trivial.
  rw [pivotVector_apply]
  intro generator_eq_zero
  exact j.property
    ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero (leadingCoeffIdeal N j.1)).mpr
      generator_eq_zero)

/-- Helper for Theorem 69.1: every vector of `N` supported at or below `i` lies in the
span of the chosen pivot vectors. -/
private lemma mem_span_pivotVector_of_mem_supported [WellFoundedLT ι]
    (N : Submodule ℤ (ι →₀ ℤ)) (i : ι) (x : N)
    (support_x : (x : ι →₀ ℤ) ∈ Finsupp.supported ℤ ℤ (Set.Iic i)) :
    x ∈ Submodule.span ℤ (Set.range (pivotVector N)) := by
  induction i using WellFoundedLT.induction generalizing x with
  | ind i induction_hypothesis =>
      let pivotSpan := Submodule.span ℤ (Set.range (pivotVector N))
      -- A vector supported strictly below `i` is handled at the greatest index in its support.
      have mem_span_of_support_lt (y : N)
          (support_y : (y : ι →₀ ℤ) ∈ Finsupp.supported ℤ ℤ (Set.Iio i)) :
          y ∈ pivotSpan := by
        by_cases y_eq_zero : (y : ι →₀ ℤ) = 0
        · have y_subtype_eq_zero : y = 0 := Subtype.ext y_eq_zero
          rw [y_subtype_eq_zero]
          exact pivotSpan.zero_mem
        · have support_nonempty : (y : ι →₀ ℤ).support.Nonempty :=
            Finsupp.support_nonempty_iff.mpr y_eq_zero
          let k := (y : ι →₀ ℤ).support.max' support_nonempty
          have k_mem : k ∈ (y : ι →₀ ℤ).support :=
            Finset.max'_mem (y : ι →₀ ℤ).support support_nonempty
          have k_lt_i : k < i :=
            (Finsupp.mem_supported ℤ (y : ι →₀ ℤ)).mp support_y k_mem
          apply induction_hypothesis k k_lt_i y
          rw [Finsupp.mem_supported]
          intro q q_mem
          exact Finset.le_max' (y : ι →₀ ℤ).support q q_mem
      have coefficient_mem : (x : ι →₀ ℤ) i ∈ leadingCoeffIdeal N i :=
        (mem_leadingCoeffIdeal_iff N i ((x : ι →₀ ℤ) i)).mpr ⟨x, support_x, rfl⟩
      by_cases coefficient_ideal_eq_bot : leadingCoeffIdeal N i = ⊥
      · have coefficient_eq_zero : (x : ι →₀ ℤ) i = 0 := by
          rw [coefficient_ideal_eq_bot] at coefficient_mem
          exact coefficient_mem
        have support_lt :
            (x : ι →₀ ℤ) ∈ Finsupp.supported ℤ ℤ (Set.Iio i) := by
          rw [Finsupp.mem_supported]
          intro k k_mem
          have k_le_i := (Finsupp.mem_supported ℤ (x : ι →₀ ℤ)).mp support_x k_mem
          have k_ne_i : k ≠ i := by
            intro k_eq_i
            subst k
            exact (Finsupp.mem_support_iff.mp k_mem) coefficient_eq_zero
          exact lt_of_le_of_ne k_le_i k_ne_i
        exact mem_span_of_support_lt x support_lt
      · let j : LeadingIndex N := ⟨i, coefficient_ideal_eq_bot⟩
        obtain ⟨c, coefficient_eq⟩ :=
          (Submodule.IsPrincipal.mem_iff_eq_smul_generator (leadingCoeffIdeal N i)).mp
            coefficient_mem
        let y : N := x - c • pivotVector N j
        have pivot_coefficient :
            (pivotVector N j : ι →₀ ℤ) i =
              Submodule.IsPrincipal.generator (leadingCoeffIdeal N i) := by
          simpa only [j] using pivotVector_apply N j
        have y_apply : (y : ι →₀ ℤ) i = 0 := by
          simp only [y, Submodule.coe_sub, Submodule.coe_smul, Finsupp.sub_apply,
            Finsupp.smul_apply]
          rw [coefficient_eq, pivot_coefficient, sub_self]
        have y_support_le :
            (y : ι →₀ ℤ) ∈ Finsupp.supported ℤ ℤ (Set.Iic i) := by
          rw [Finsupp.mem_supported]
          intro k k_mem
          have support_sub := Finsupp.support_sub k_mem
          rcases Finset.mem_union.mp support_sub with x_mem | smul_pivot_mem
          · exact (Finsupp.mem_supported ℤ (x : ι →₀ ℤ)).mp support_x x_mem
          · have pivot_mem := Finsupp.support_smul smul_pivot_mem
            exact (Finsupp.mem_supported ℤ (pivotVector N j : ι →₀ ℤ)).mp
              (pivotVector_mem_supported N j) pivot_mem
        have y_support_lt :
            (y : ι →₀ ℤ) ∈ Finsupp.supported ℤ ℤ (Set.Iio i) := by
          rw [Finsupp.mem_supported]
          intro k k_mem
          have k_le_i := (Finsupp.mem_supported ℤ (y : ι →₀ ℤ)).mp y_support_le k_mem
          have k_ne_i : k ≠ i := by
            intro k_eq_i
            subst k
            exact (Finsupp.mem_support_iff.mp k_mem) y_apply
          exact lt_of_le_of_ne k_le_i k_ne_i
        have y_mem : y ∈ pivotSpan := mem_span_of_support_lt y y_support_lt
        have pivot_mem : pivotVector N j ∈ pivotSpan :=
          Submodule.subset_span (Set.mem_range_self j)
        have reconstructed_mem := pivotSpan.add_mem y_mem (pivotSpan.smul_mem c pivot_mem)
        simpa only [y, sub_add_cancel] using reconstructed_mem

/-- Helper for Theorem 69.1: the chosen pivot vectors span the entire submodule `N`. -/
private lemma span_pivotVector_eq_top [WellFoundedLT ι] (N : Submodule ℤ (ι →₀ ℤ)) :
    Submodule.span ℤ (Set.range (pivotVector N)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  -- Every nonzero finitely supported vector is bounded by the maximum of its support.
  by_cases x_eq_zero : (x : ι →₀ ℤ) = 0
  · have x_subtype_eq_zero : x = 0 := Subtype.ext x_eq_zero
    rw [x_subtype_eq_zero]
    exact Submodule.zero_mem _
  · have support_nonempty : (x : ι →₀ ℤ).support.Nonempty :=
      Finsupp.support_nonempty_iff.mpr x_eq_zero
    let i := (x : ι →₀ ℤ).support.max' support_nonempty
    apply mem_span_pivotVector_of_mem_supported N i x
    rw [Finsupp.mem_supported]
    intro k k_mem
    exact Finset.le_max' (x : ι →₀ ℤ).support k k_mem

/-- Helper for Theorem 69.1: every submodule of an integer Finsupp module is free. -/
private theorem freeIntFinsupp {κ : Type*} (N : Submodule ℤ (κ →₀ ℤ)) : Module.Free ℤ N := by
  classical
  obtain ⟨wellOrder, wellFounded⟩ := exists_wellFoundedLT κ
  letI := wellOrder
  letI := wellFounded
  -- Triangularity gives independence, while well-founded elimination gives spanning.
  have pivot_independent : LinearIndependent ℤ (pivotVector N) := by
    apply LinearIndependent.of_comp N.subtype
    apply Finsupp.linearIndependent_of_support_le
    · intro j
      exact (Finsupp.mem_supported ℤ (pivotVector N j : κ →₀ ℤ)).mp
        (pivotVector_mem_supported N j)
    · exact pivotVector_apply_ne_zero N
  have pivot_spans : ⊤ ≤ Submodule.span ℤ (Set.range (pivotVector N)) := by
    rw [span_pivotVector_eq_top N]
  exact Module.Free.of_basis (Module.Basis.mk pivot_independent pivot_spans)

end FinsuppSubmodule

/-- Helper for Theorem 69.1: additive subgroups of free abelian groups are free abelian
groups. -/
lemma ofAddSubgroup {G : Type u} [AddCommGroup G] [Module.Free ℤ G]
    (H : AddSubgroup G) : Module.Free ℤ H := by
  -- Represent the ambient free group as a Finsupp module and transport the subgroup to its image.
  let b := Module.Free.chooseBasis ℤ G
  let N := H.toIntSubmodule.map b.repr.toLinearMap
  have free_image : Module.Free ℤ N := freeIntFinsupp N
  let subgroupEquivImage : H ≃ₗ[ℤ] N :=
    Submodule.equivMapOfInjective b.repr.toLinearMap b.repr.injective H.toIntSubmodule
  -- Freeness returns along the representation equivalence.
  exact Module.Free.of_equiv' free_image subgroupEquivImage.symm

end Module.Free
