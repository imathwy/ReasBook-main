import Mathlib
import BauschkeLean.Chap01.Text_1_0_8
import BauschkeLean.Chap09.Proposition_9_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace SetValuedOperator

noncomputable section

/- Source/core/bridge triage:
- `source-facing`: Proposition 20.23 is the maximal-monotonicity theorem for the componentwise
  product operator on the Hilbert product `H × K`, written in ordinary pair coordinates.
- `core/canonical`: the owner abstractions are the chapter's product operator `A × B` from
  `Definition_20_1` and maximal monotonicity `Maximal IsMonotone`.
- `bridge/view`: Chapter 9 only supplies the local `ℓ²` Hilbert-space structure on the raw pair
  type `H × K`; it is not a second public owner. -/

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

/-- Helper for Proposition 20.23: the componentwise product operator on raw pairs. -/
private def prodOperator (A : SetValuedOperator H H) (B : SetValuedOperator K K) :
    SetValuedOperator (H × K) (H × K) :=
  fun p ↦ A p.1 ×ˢ B p.2

local infixr:35 " × " => prodOperator

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] in
/-- Helper for Proposition 20.23: membership in the componentwise product
operator is coordinatewise. -/
@[simp] private theorem mem_prod_iff_local
    (A : SetValuedOperator H H) (B : SetValuedOperator K K)
    (p : H × K) (w : H × K) :
    w ∈ (A × B) p ↔ w.1 ∈ A p.1 ∧ w.2 ∈ B p.2 :=
  Iff.rfl

/-- Helper for Proposition 20.23: textbook monotonicity for a set-valued operator. -/
private abbrev operatorIsMonotone (A : SetValuedOperator H H) : Prop :=
  ∀ ⦃x u y v : H⦄, u ∈ A x → v ∈ A y → 0 ≤ ⟪x - y, u - v⟫_ℝ

local notation "IsMonotone" => operatorIsMonotone

/-- Helper for Proposition 20.23: unfolding the local monotonicity notion gives
the textbook inequality. -/
private theorem isMonotone_iff_local (A : SetValuedOperator H H) :
    IsMonotone A ↔
      ∀ ⦃x u y v : H⦄, u ∈ A x → v ∈ A y → 0 ≤ ⟪x - y, u - v⟫_ℝ :=
  Iff.rfl

/-- Helper for Proposition 20.23: maximal monotonicity is equivalent to the
Minty membership test. -/
private theorem maximal_mem_iff_local
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (x u : H) :
    u ∈ A x ↔ ∀ ⦃y v : H⦄, v ∈ A y → 0 ≤ ⟪x - y, u - v⟫_ℝ := by
  constructor
  · intro hxu y v hv
    exact (isMonotone_iff_local A).1 hA.1 hxu hv
  · intro hxu
    classical
    let B : SetValuedOperator H H :=
      fun y ↦ if h : y = x then Set.insert u (A x) else A y
    have hAB : A ≤ B := by
      intro y v hv
      by_cases hy : y = x
      · subst y
        simpa [B] using (Or.inr hv : v = u ∨ v ∈ A x)
      · simp [B, hy, hv]
    have hBmono : IsMonotone B := by
      rw [isMonotone_iff_local]
      intro y v z w hv hw
      by_cases hy : y = x
      · subst y
        by_cases hz : z = x
        · subst z
          simp
        · have hv' : v = u ∨ v ∈ A x := by
            simpa [B] using hv
          have hw' : w ∈ A z := by
            simpa [B, hz] using hw
          rcases hv' with rfl | hvA
          · simpa using hxu hw'
          · exact (isMonotone_iff_local A).1 hA.1 hvA hw'
      · by_cases hz : z = x
        · subst z
          have hv' : v ∈ A y := by
            simpa [B, hy] using hv
          have hw' : w = u ∨ w ∈ A x := by
            simpa [B] using hw
          rcases hw' with rfl | hwA
          · have hxy : 0 ≤ ⟪x - y, w - v⟫_ℝ := hxu hv'
            have hswap : ⟪x - y, w - v⟫_ℝ = ⟪y - x, v - w⟫_ℝ := by
              have hxy' : x - y = -(y - x) := by
                abel_nf
              have hwv' : w - v = -(v - w) := by
                abel_nf
              calc
                ⟪x - y, w - v⟫_ℝ = ⟪-(y - x), -(v - w)⟫_ℝ := by
                  rw [hxy', hwv']
                _ = ⟪y - x, v - w⟫_ℝ := by
                  rw [inner_neg_left, inner_neg_right]
                  simp
            rw [← hswap]
            exact hxy
          · exact (isMonotone_iff_local A).1 hA.1 hv' hwA
        · have hv' : v ∈ A y := by
            simpa [B, hy] using hv
          have hw' : w ∈ A z := by
            simpa [B, hz] using hw
          exact (isMonotone_iff_local A).1 hA.1 hv' hw'
    have huB : u ∈ B x := by
      dsimp [B]
      split_ifs with hx
      · exact Or.inl rfl
      · contradiction
    exact (hA.2 hBmono hAB x) huB

/-- Helper for Proposition 20.23: the Minty membership test characterizes maximal monotonicity. -/
private theorem maximal_iff_mem_iff_local (A : SetValuedOperator H H) :
    Maximal IsMonotone A ↔
      ∀ x u : H, u ∈ A x ↔ ∀ ⦃y v : H⦄, v ∈ A y → 0 ≤ ⟪x - y, u - v⟫_ℝ := by
  constructor
  · intro hA x u
    exact maximal_mem_iff_local hA x u
  · intro hA
    have hmem : ∀ x u : H,
        u ∈ A x ↔ ∀ ⦃y v : H⦄, v ∈ A y → 0 ≤ ⟪x - y, u - v⟫_ℝ := @hA
    constructor
    · rw [isMonotone_iff_local]
      intro x u y v hxu hyv
      exact (hmem x u).1 hxu hyv
    · intro B hB hAB x u huB
      exact (hmem x u).2 fun {y v} hvA ↦
        (isMonotone_iff_local B).1 hB huB (hAB y hvA)

-- Proof sketch: use `Maximal.mem_iff` for `A` and `B`. Membership in the product operator is
-- componentwise by `mem_prod_iff`, and the Chapter 9 `ℓ²` inner product on `H × K` splits into
-- the sum of the two coordinate pairings. The product Minty criterion therefore separates into the
-- two component Minty criteria, yielding maximal monotonicity of `A × B`.
/-- Helper for Proposition 20.23: the Chapter 9 `ℓ²` inner product on `H × K` splits
coordinatewise after taking differences. -/
private theorem prod_inner_sub_eq_sum
    (p q r s : H × K) :
    ⟪p - q, r - s⟫_ℝ =
      ⟪p.1 - q.1, r.1 - s.1⟫_ℝ + ⟪p.2 - q.2, r.2 - s.2⟫_ℝ := by
  -- The local raw-product Hilbert structure defines the inner product coordinatewise.
  rfl

/-- Helper for Proposition 20.23: componentwise membership in `A` and `B` implies the product
Minty inequality against every graph point of `A × B`. -/
private theorem prod_minty_of_mem
    {A : SetValuedOperator H H} {B : SetValuedOperator K K}
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    {x u : H} {y v : K} (hu : u ∈ A x) (hv : v ∈ B y) :
    ∀ ⦃p : H × K⦄ ⦃w : H × K⦄, w ∈ (A × B) p →
      0 ≤ ⟪(x, y) - p, (u, v) - w⟫_ℝ := by
  intro p w hw
  rcases p with ⟨a, b⟩
  rcases w with ⟨ua, vb⟩
  -- Split product-graph membership into its two coordinate graph memberships.
  rcases (mem_prod_iff_local A B (a, b) (ua, vb)).1 hw with ⟨hua, hvb⟩
  -- Apply the two coordinate Minty criteria and add the resulting nonnegative terms.
  have hAu : 0 ≤ ⟪x - a, u - ua⟫_ℝ := (maximal_mem_iff_local hA x u).1 hu hua
  have hBv : 0 ≤ ⟪y - b, v - vb⟫_ℝ := (maximal_mem_iff_local hB y v).1 hv hvb
  rw [prod_inner_sub_eq_sum]
  exact add_nonneg hAu hBv

/-- Helper for Proposition 20.23: if a pair is monotonically related to every graph point of
`A × B`, then it belongs to the product value `(A × B) (x, y)`. -/
private theorem mem_prod_of_prod_minty
    {A : SetValuedOperator H H} {B : SetValuedOperator K K}
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    {x u : H} {y v : K}
    (hminty : ∀ ⦃p : H × K⦄ ⦃w : H × K⦄, w ∈ (A × B) p →
      0 ≤ ⟪(x, y) - p, (u, v) - w⟫_ℝ) :
    (u, v) ∈ (A × B) (x, y) := by
  classical
  -- Route correction: prove the converse by the source-faithful four-case split on
  -- component membership, extracting violating witnesses from `Maximal.mem_iff` when needed.
  by_cases hu : u ∈ A x
  · by_cases hv : v ∈ B y
    · -- In the good-good case, product membership is exactly componentwise membership.
      simpa using (show u ∈ A x ∧ v ∈ B y from ⟨hu, hv⟩)
    · -- If only the second coordinate fails, contradict the product Minty inequality by pairing
      -- the violating `B`-witness with the actual graph point `(x, u)` in the first coordinate.
      have hnotB : ¬ ∀ b vb, vb ∈ B b → 0 ≤ ⟪y - b, v - vb⟫_ℝ := by
        intro hall
        apply hv
        exact (maximal_mem_iff_local hB y v).2 fun {b vb} hvb ↦ hall b vb hvb
      push Not at hnotB
      rcases hnotB with ⟨b, vb, hvb, hbadB⟩
      have hprod : 0 ≤ ⟪(x, y) - (x, b), (u, v) - (u, vb)⟫_ℝ := by
        apply hminty
        simpa using (show u ∈ A x ∧ vb ∈ B b from ⟨hu, hvb⟩)
      rw [prod_inner_sub_eq_sum] at hprod
      exfalso
      exact (not_lt_of_ge (by simpa using hprod)) hbadB
  · by_cases hv : v ∈ B y
    · -- If only the first coordinate fails, use the symmetric contradiction.
      have hnotA : ¬ ∀ a ua, ua ∈ A a → 0 ≤ ⟪x - a, u - ua⟫_ℝ := by
        intro hall
        apply hu
        exact (maximal_mem_iff_local hA x u).2 fun {a ua} hua ↦ hall a ua hua
      push Not at hnotA
      rcases hnotA with ⟨a, ua, hua, hbadA⟩
      have hprod : 0 ≤ ⟪(x, y) - (a, y), (u, v) - (ua, v)⟫_ℝ := by
        apply hminty
        simpa using (show ua ∈ A a ∧ v ∈ B y from ⟨hua, hv⟩)
      rw [prod_inner_sub_eq_sum] at hprod
      exfalso
      exact (not_lt_of_ge (by simpa using hprod)) hbadA
    · -- If both coordinates fail, combine the two violating witnesses and contradict the
      -- assumed nonnegativity of the product Minty inequality.
      have hnotA : ¬ ∀ a ua, ua ∈ A a → 0 ≤ ⟪x - a, u - ua⟫_ℝ := by
        intro hall
        apply hu
        exact (maximal_mem_iff_local hA x u).2 fun {a ua} hua ↦ hall a ua hua
      have hnotB : ¬ ∀ b vb, vb ∈ B b → 0 ≤ ⟪y - b, v - vb⟫_ℝ := by
        intro hall
        apply hv
        exact (maximal_mem_iff_local hB y v).2 fun {b vb} hvb ↦ hall b vb hvb
      push Not at hnotA
      push Not at hnotB
      rcases hnotA with ⟨a, ua, hua, hbadA⟩
      rcases hnotB with ⟨b, vb, hvb, hbadB⟩
      have hprod : 0 ≤ ⟪(x, y) - (a, b), (u, v) - (ua, vb)⟫_ℝ := by
        apply hminty
        simpa using (show ua ∈ A a ∧ vb ∈ B b from ⟨hua, hvb⟩)
      rw [prod_inner_sub_eq_sum] at hprod
      have hsumlt : ⟪x - a, u - ua⟫_ℝ + ⟪y - b, v - vb⟫_ℝ < 0 := by
        linarith
      exfalso
      exact (not_lt_of_ge hprod) hsumlt

/-- Proposition 20.23: if `A` and `B` are maximally monotone, then the componentwise product
operator `(x, y) ↦ A x × B y` is maximally monotone on the Chapter 9 `ℓ²` Hilbert product
structure on the raw pair type `H × K`. -/
theorem Maximal.prod
    {A : SetValuedOperator H H} {B : SetValuedOperator K K}
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B) :
    Maximal IsMonotone (A × B) := by
  -- Reduce maximality on the product space to the Minty membership characterization.
  rw [maximal_iff_mem_iff_local]
  intro p w
  rcases p with ⟨x, y⟩
  rcases w with ⟨u, v⟩
  constructor
  · intro huw
    -- Componentwise membership yields the product Minty inequality by adding the two
    -- coordinate Minty inequalities.
    rcases (mem_prod_iff_local A B (x, y) (u, v)).1 huw with ⟨hu, hv⟩
    exact prod_minty_of_mem hA hB hu hv
  · intro hminty
    -- Conversely, any violation of a coordinate membership produces a product witness that
    -- contradicts the assumed Minty inequality.
    exact mem_prod_of_prod_minty hA hB hminty

end

end SetValuedOperator
