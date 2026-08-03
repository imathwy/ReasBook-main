import Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_example_3_19
import Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_1

open scoped BigOperators Matrix

-- This file reuses the Chapter 3 owner `is_valid_inequality` and adds the lifting-specific
-- binary-knapsack constructions from Section 7.2.2.

noncomputable section

namespace SequenceIndependentLifting

section OwnerAPI

universe u

variable {ι : Type u}

/-- The coefficient vector of the base inequality supported on `C`. -/
def base_coefficients
    [DecidableEq ι]
    (C : Finset ι)
    (α : ι → ℝ) : ι → ℝ :=
  C.piecewise α 0

/-- On the distinguished set `C`, `base_coefficients C α` agrees with `α`. -/
@[simp] theorem base_coefficients_apply_of_mem
    [DecidableEq ι]
    {C : Finset ι}
    {α : ι → ℝ}
    {j : ι}
    (hj : j ∈ C) :
    base_coefficients C α j = α j :=
  Finset.piecewise_eq_of_mem _ _ _ hj

/-- Outside `C`, `base_coefficients C α` vanishes. -/
@[simp] theorem base_coefficients_apply_of_not_mem
    [DecidableEq ι]
    {C : Finset ι}
    {α : ι → ℝ}
    {j : ι}
    (hj : j ∉ C) :
    base_coefficients C α j = 0 :=
  Finset.piecewise_eq_of_notMem _ _ _ hj

/-- The coefficient vector obtained by lifting the base inequality with a scalar function `φ`
evaluated at the weights `a j` outside `C`. -/
def lifted_coefficients
    [DecidableEq ι]
    (C : Finset ι)
    (α : ι → ℝ)
    (a : ι → ℝ)
    (φ : ℝ → ℝ) : ι → ℝ :=
  C.piecewise α (φ ∘ a)

/-- On `C`, `lifted_coefficients C α a φ` agrees with the original coefficients `α`. -/
@[simp] theorem lifted_coefficients_apply_of_mem
    [DecidableEq ι]
    {C : Finset ι}
    {α a : ι → ℝ}
    {φ : ℝ → ℝ}
    {j : ι}
    (hj : j ∈ C) :
    lifted_coefficients C α a φ j = α j :=
  Finset.piecewise_eq_of_mem _ _ _ hj

/-- Outside `C`, `lifted_coefficients C α a φ` is given by `φ (a j)`. -/
@[simp] theorem lifted_coefficients_apply_of_not_mem
    [DecidableEq ι]
    {C : Finset ι}
    {α a : ι → ℝ}
    {φ : ℝ → ℝ}
    {j : ι}
    (hj : j ∉ C) :
    lifted_coefficients C α a φ j = φ (a j) :=
  Finset.piecewise_eq_of_notMem _ _ _ hj

/-- A coefficient vector is a lifting of the base inequality on `C` when it is valid for `S`
and agrees with `α` on `C`. -/
def is_lifting_of_base_inequality
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (α : ι → ℝ)
    (β : ℝ)
    (c : ι → ℝ) : Prop :=
  is_valid_inequality S c β ∧ ∀ ⦃j : ι⦄, j ∈ C → c j = α j

/-- `is_lifting_of_base_inequality` unfolds to validity for `S` together with agreement
with the base coefficients on `C`. -/
theorem is_lifting_of_base_inequality_iff
    [Fintype ι]
    {S : Set (ι → ℝ)}
    {C : Finset ι}
    {α : ι → ℝ}
    {β : ℝ}
    {c : ι → ℝ} :
    is_lifting_of_base_inequality S C α β c ↔
      is_valid_inequality S c β ∧ ∀ ⦃j : ι⦄, j ∈ C → c j = α j :=
  Iff.rfl

/-- A lifting of the base inequality is, in particular, a valid inequality for `S`. -/
theorem is_lifting_of_base_inequality.is_valid_inequality
    [Fintype ι]
    {S : Set (ι → ℝ)}
    {C : Finset ι}
    {α : ι → ℝ}
    {β : ℝ}
    {c : ι → ℝ}
    (hc : is_lifting_of_base_inequality S C α β c) :
    is_valid_inequality S c β :=
  hc.1

/-- A lifting of the base inequality agrees with the base coefficients on `C`. -/
theorem is_lifting_of_base_inequality.eq_base_of_mem
    [Fintype ι]
    {S : Set (ι → ℝ)}
    {C : Finset ι}
    {α : ι → ℝ}
    {β : ℝ}
    {c : ι → ℝ}
    (hc : is_lifting_of_base_inequality S C α β c)
    {j : ι}
    (hj : j ∈ C) :
    c j = α j :=
  hc.2 hj

/-- A coefficient vector is the unique maximal lifting of the base inequality when it is a
lifting and every other lifting lies pointwise below it. -/
def is_unique_maximal_lifting_of_base_inequality
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (α : ι → ℝ)
    (β : ℝ)
    (c : ι → ℝ) : Prop :=
  is_lifting_of_base_inequality S C α β c ∧
    ∀ c' : ι → ℝ,
      is_lifting_of_base_inequality S C α β c' →
        c' ≤ c

/-- `is_unique_maximal_lifting_of_base_inequality` unfolds to validity, agreement on `C`, and
pointwise domination over every other lifting. -/
theorem is_unique_maximal_lifting_of_base_inequality_iff
    [Fintype ι]
    {S : Set (ι → ℝ)}
    {C : Finset ι}
    {α : ι → ℝ}
    {β : ℝ}
    {c : ι → ℝ} :
    is_unique_maximal_lifting_of_base_inequality S C α β c ↔
      is_lifting_of_base_inequality S C α β c ∧
        ∀ c' : ι → ℝ,
          is_lifting_of_base_inequality S C α β c' →
            c' ≤ c :=
  Iff.rfl

/-- A unique maximal lifting is, in particular, a lifting of the base inequality. -/
theorem is_unique_maximal_lifting_of_base_inequality.is_lifting
    [Fintype ι]
    {S : Set (ι → ℝ)}
    {C : Finset ι}
    {α : ι → ℝ}
    {β : ℝ}
    {c : ι → ℝ}
    (hc : is_unique_maximal_lifting_of_base_inequality S C α β c) :
    is_lifting_of_base_inequality S C α β c :=
  hc.1

/-- A unique maximal lifting dominates every other lifting pointwise. -/
theorem is_unique_maximal_lifting_of_base_inequality.maximal
    [Fintype ι]
    {S : Set (ι → ℝ)}
    {C : Finset ι}
    {α : ι → ℝ}
    {β : ℝ}
    {c : ι → ℝ}
    (hc : is_unique_maximal_lifting_of_base_inequality S C α β c)
    (c' : ι → ℝ)
    (hc' : is_lifting_of_base_inequality S C α β c') :
    c' ≤ c :=
  hc.2 c' hc'

end OwnerAPI

section Theorem77

variable {n : ℕ}

/-- A function on `[0,b]` is superadditive when `g (u + v)` dominates `g u + g v` whenever
`u`, `v`, and `u + v` all lie in the interval `[0,b]`. -/
def is_superadditive_on_Icc
    (g : ℝ → ℝ)
    (b : ℝ) : Prop :=
  ∀ ⦃u v : ℝ⦄,
    u ∈ Set.Icc (0 : ℝ) b →
    v ∈ Set.Icc (0 : ℝ) b →
    u + v ∈ Set.Icc (0 : ℝ) b →
    g u + g v ≤ g (u + v)

/-- The sequence-independent lifting profile associated with the base inequality on `C` and the
binary knapsack data `(a, b)`. -/
def lifting_profile
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ) : ℝ → ℝ :=
  fun z ↦
    β -
      sSup
        {r : ℝ |
          ∃ x : Fin n → ℝ,
            x ∈ zero_one_knapsack_set a (b - z) ∧
            (∀ j, j ∉ C → x j = 0) ∧
            r = base_coefficients C α ⬝ᵥ x}

/-- Helper for Theorem 7.7: if all contributions outside `C` vanish termwise, then the
dot product reduces to the sum over `C`. -/
lemma dotProduct_eq_sum_of_zero_off_cover
    (C : Finset (Fin n))
    (c x : Fin n → ℝ)
    (hzero : ∀ j, j ∉ C → c j * x j = 0) :
    c ⬝ᵥ x = ∑ j ∈ C, c j * x j := by
  classical
  -- Split the full finite sum into the cover part and its complement.
  calc
    c ⬝ᵥ x
        = ∑ j ∈ Finset.univ with j ∈ C, c j * x j +
            ∑ j ∈ Finset.univ with j ∉ C, c j * x j := by
            simpa [dotProduct] using
              (Finset.sum_filter_add_sum_filter_not
                Finset.univ
                (fun j : Fin n ↦ j ∈ C)
                (fun j ↦ c j * x j)).symm
    _ = ∑ j ∈ Finset.univ with j ∈ C, c j * x j := by
          have hcompl : ∑ j ∈ Finset.univ with j ∉ C, c j * x j = 0 := by
            apply Finset.sum_eq_zero
            intro j hj
            exact hzero j (by simpa using hj)
          rw [hcompl, add_zero]
    _ = ∑ j ∈ C, c j * x j := by
          simp

/-- Helper for Theorem 7.7: the base coefficient vector contributes only on the distinguished
cover `C`. -/
lemma baseCoefficients_dotProduct
    (C : Finset (Fin n))
    (α x : Fin n → ℝ) :
    (base_coefficients C α) ⬝ᵥ x = ∑ j ∈ C, α j * x j := by
  -- First remove the zero contributions outside `C`.
  calc
    (base_coefficients C α) ⬝ᵥ x
        = ∑ j ∈ C, base_coefficients C α j * x j := by
            apply dotProduct_eq_sum_of_zero_off_cover
            intro j hj
            simp [base_coefficients_apply_of_not_mem hj]
    _ = ∑ j ∈ C, α j * x j := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [base_coefficients_apply_of_mem hj]

/-- Helper for Theorem 7.7: the lifted coefficient vector splits into the base contribution on
`C` and the lifted contribution on the complement of `C`. -/
lemma liftedCoefficients_dotProduct
    (C : Finset (Fin n))
    (α a x : Fin n → ℝ)
    (g : ℝ → ℝ) :
    (lifted_coefficients C α a g) ⬝ᵥ x =
      (base_coefficients C α) ⬝ᵥ x +
        ∑ j ∈ (Finset.univ \ C), g (a j) * x j := by
  classical
  let offCover : Fin n → ℝ := fun j ↦ if j ∈ C then 0 else g (a j)
  have hsplit :
      lifted_coefficients C α a g = base_coefficients C α + offCover := by
    funext j
    by_cases hj : j ∈ C
    · simp [offCover, hj]
    · simp [offCover, hj]
  have hoffCover :
      offCover ⬝ᵥ x = ∑ j ∈ (Finset.univ \ C), g (a j) * x j := by
    calc
      offCover ⬝ᵥ x = ∑ j ∈ (Finset.univ \ C), offCover j * x j := by
        apply dotProduct_eq_sum_of_zero_off_cover
        intro j hj
        have hjC : j ∈ C := by
          by_contra hnot
          exact hj (by simp [hnot])
        simp [offCover, hjC]
      _ = ∑ j ∈ (Finset.univ \ C), g (a j) * x j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            have hjC : j ∉ C := by
              simpa using hj
            simp [offCover, hjC]
  -- Express the lifted coefficients as base plus off-cover terms, then use bilinearity.
  calc
    (lifted_coefficients C α a g) ⬝ᵥ x
        = (base_coefficients C α + offCover) ⬝ᵥ x := by
            rw [hsplit]
    _ = (base_coefficients C α) ⬝ᵥ x + offCover ⬝ᵥ x := by
          rw [add_dotProduct]
    _ = (base_coefficients C α) ⬝ᵥ x + ∑ j ∈ (Finset.univ \ C), g (a j) * x j := by
          rw [hoffCover]

/-- Helper for Theorem 7.7: every valid lifting coefficient on an off-cover index is bounded
above by the sequence-independent lifting profile evaluated at that weight. -/
lemma liftingCoeff_le_liftingProfile_of_lifting
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    {c : Fin n → ℝ}
    (ha : ∀ ⦃j : Fin n⦄, j ∉ C → a j ∈ Set.Icc (0 : ℝ) b)
    (hc : is_lifting_of_base_inequality (zero_one_knapsack_set a b) C α β c)
    {j : Fin n}
    (hj : j ∉ C) :
    c j ≤ lifting_profile a b C α β (a j) := by
  let residualValues : Set ℝ :=
    {r : ℝ |
      ∃ x : Fin n → ℝ,
        x ∈ zero_one_knapsack_set a (b - a j) ∧
          (∀ i, i ∉ C → x i = 0) ∧
          r = base_coefficients C α ⬝ᵥ x}
  have hnonempty : residualValues.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨0, ?_, ?_, ?_⟩
    · rw [mem_zero_one_knapsack_set_iff]
      constructor
      · intro i
        left
        simp
      · have haj : a j ≤ b := (ha hj).2
        simpa using sub_nonneg.mpr haj
    · intro i hi
      simp
    · simp
  have hsSup_le : sSup residualValues ≤ β - c j := by
    refine csSup_le hnonempty ?_
    intro r hr
    rcases hr with ⟨x, hx, hxzero, rfl⟩
    rw [mem_zero_one_knapsack_set_iff] at hx
    rcases hx with ⟨hxbin, hxweight⟩
    have hxj_zero : x j = 0 := hxzero j hj
    let ej : Fin n → ℝ := Pi.single j (1 : ℝ)
    let y : Fin n → ℝ := x + ej
    have hy_mem : y ∈ zero_one_knapsack_set a b := by
      rw [mem_zero_one_knapsack_set_iff]
      constructor
      · intro i
        by_cases hij : i = j
        · subst hij
          right
          simp [y, ej, hxj_zero]
        · rcases hxbin i with hxi | hxi
          · left
            simp [y, ej, hij, hxi]
          · right
            simp [y, ej, hij, hxi]
      · have hy_weight :
            ∑ i, a i * y i = ∑ i, a i * x i + a j := by
          calc
            ∑ i, a i * y i = a ⬝ᵥ y := by
              rfl
            _ = a ⬝ᵥ x + a ⬝ᵥ ej := by
                  simp [y]
            _ = a ⬝ᵥ x + a j := by
                  have hej : a ⬝ᵥ ej = a j := by
                    simp [ej]
                  rw [hej]
            _ = ∑ i, a i * x i + a j := by
                  rfl
        linarith
    have hdot_x : c ⬝ᵥ x = base_coefficients C α ⬝ᵥ x := by
      -- Outside `C`, the residual witnesses are zero, so the lifting agrees with the base sum.
      calc
        c ⬝ᵥ x = ∑ i ∈ C, c i * x i := by
          apply dotProduct_eq_sum_of_zero_off_cover
          intro i hi
          simp [hxzero i hi]
        _ = ∑ i ∈ C, α i * x i := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [hc.eq_base_of_mem hi]
        _ = base_coefficients C α ⬝ᵥ x := by
              symm
              exact baseCoefficients_dotProduct C α x
    have hy_dot :
        c ⬝ᵥ y = base_coefficients C α ⬝ᵥ x + c j := by
      -- Adding the unit vector at `j` isolates the new lifting coefficient.
      calc
        c ⬝ᵥ y = c ⬝ᵥ x + c ⬝ᵥ ej := by
          simp [y]
        _ = c ⬝ᵥ x + c j := by
          have hej : c ⬝ᵥ ej = c j := by
            simp [ej]
          rw [hej]
        _ = base_coefficients C α ⬝ᵥ x + c j := by
          rw [hdot_x]
    have hy_valid : c ⬝ᵥ y ≤ β := hc.is_valid_inequality hy_mem
    linarith [hy_valid, hy_dot]
  -- Rewriting the profile at `a j` converts the supremum bound into the desired coefficient bound.
  have hcj : c j + sSup residualValues ≤ β := by
    linarith
  have hprofile :
      lifting_profile a b C α β (a j) = β - sSup residualValues := by
    simp [lifting_profile, residualValues]
  rw [hprofile]
  linarith

/-- Theorem 7.7. Every superadditive function `g` on `[0,b]` that is pointwise bounded above by
the lifting profile yields a valid lifted inequality when the off-cover coefficients are
evaluated at weights in `[0,b]`. -/
theorem superadditive_lift_valid
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    (g : ℝ → ℝ)
    (hbase :
      is_valid_inequality (zero_one_knapsack_set a b) (base_coefficients C α) β)
    (ha : ∀ ⦃j : Fin n⦄, j ∉ C → a j ∈ Set.Icc (0 : ℝ) b)
    (hg_super : is_superadditive_on_Icc g b)
    (hg_le :
      ∀ ⦃z : ℝ⦄, z ∈ Set.Icc (0 : ℝ) b → g z ≤ lifting_profile a b C α β z) :
    is_valid_inequality
      (zero_one_knapsack_set a b)
      (lifted_coefficients C α a g)
      β := sorry

/-- In particular, if the lifting profile itself is superadditive on `[0,b]`, then the lifted
inequality obtained from that profile is the unique maximal lifting of the base inequality on the
binary knapsack set, provided the off-cover weights lie in `[0,b]`. -/
theorem lifting_profile_is_unique_maximal_lifting
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    (hbase :
      is_valid_inequality (zero_one_knapsack_set a b) (base_coefficients C α) β)
    (ha : ∀ ⦃j : Fin n⦄, j ∉ C → a j ∈ Set.Icc (0 : ℝ) b)
    (hf_super : is_superadditive_on_Icc (lifting_profile a b C α β) b) :
    is_unique_maximal_lifting_of_base_inequality
      (zero_one_knapsack_set a b)
      C
      α
      β
      (lifted_coefficients C α a (lifting_profile a b C α β)) := sorry

end Theorem77

end SequenceIndependentLifting
