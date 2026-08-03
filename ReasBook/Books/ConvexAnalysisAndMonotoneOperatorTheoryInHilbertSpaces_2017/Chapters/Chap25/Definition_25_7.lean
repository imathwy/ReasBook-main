import BauschkeLean.Chap01.Text_1_0_10
import BauschkeLean.Chap20.Definition_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Semantic recall: `lean_leansearch` did not surface a matching existing owner for local maximal
-- monotonicity, so this file follows the Chapter 20/22 precedent of source-faithful `Prop`
-- classes on `SetValuedOperator` with explicit side-condition fields and theorem-style companions.

/-- Definition 25.7 (1): a monotone set-valued operator is locally maximally monotone with
respect to an open convex set `U` meeting `range A` when every `(x, u)` with `u ∈ U` and
`u ∉ A x` admits `(y, v) ∈ gra A` with `v ∈ U` and `⟪x - y, u - v⟫_ℝ < 0`. -/
class IsLocallyMaximallyMonotoneOn (A : SetValuedOperator H H) (U : Set H) : Prop where
  /-- Local maximal monotonicity with respect to `U` is only defined for monotone operators. -/
  monotone : A.IsMonotone
  /-- The localization set is open. -/
  isOpen : IsOpen U
  /-- The localization set is convex. -/
  convex : Convex ℝ U
  /-- The localization set meets the range of `A`. -/
  inter_range_nonempty : (U ∩ A.range).Nonempty
  /-- Every point of `H × U` outside the graph is strictly separated from some graph point in
  `H × U` by the monotonicity pairing. -/
  exists_inner_lt_zero :
    ∀ ⦃x u : H⦄, u ∈ U → u ∉ A x →
      ∃ y v, v ∈ U ∧ v ∈ A y ∧ ⟪x - y, u - v⟫_ℝ < 0

/-- A locally maximally monotone operator on `U` is monotone. -/
theorem IsLocallyMaximallyMonotoneOn.isMonotone
    {A : SetValuedOperator H H} {U : Set H} (hAU : A.IsLocallyMaximallyMonotoneOn U) :
    A.IsMonotone :=
  hAU.monotone

/-- A locally maximally monotone operator on `U` satisfies the defining strict-separation
criterion for every `u ∈ U` lying outside the value `A x`. -/
theorem IsLocallyMaximallyMonotoneOn.exists_mem_and_inner_lt_zero
    {A : SetValuedOperator H H} {U : Set H} (hAU : A.IsLocallyMaximallyMonotoneOn U)
    {x u : H} (hu : u ∈ U) (hxu : u ∉ A x) :
    ∃ y v, v ∈ U ∧ v ∈ A y ∧ ⟪x - y, u - v⟫_ℝ < 0 :=
  hAU.exists_inner_lt_zero hu hxu

/-- A locally maximally monotone operator on `U` also satisfies the defining strict-separation
criterion in graph form. -/
theorem IsLocallyMaximallyMonotoneOn.exists_mem_graph_and_inner_lt_zero_of_not_mem_graph
    {A : SetValuedOperator H H} {U : Set H} (hAU : A.IsLocallyMaximallyMonotoneOn U)
    {x u : H} (hu : u ∈ U) (hxu : (x, u) ∉ gra A) :
    ∃ y v, v ∈ U ∧ (y, v) ∈ gra A ∧ ⟪x - y, u - v⟫_ℝ < 0 := by
  rcases hAU.exists_mem_and_inner_lt_zero hu (by simpa using hxu) with ⟨y, v, hvU, hvA, hlt⟩
  exact ⟨y, v, hvU, by simpa using hvA, hlt⟩

/-- Unfolding `IsLocallyMaximallyMonotoneOn` exposes the full source-facing bundle: monotonicity
of `A`, openness and convexity of `U`, nonempty intersection with `range A`, and the local
strict-separation criterion in graph form. -/
theorem isLocallyMaximallyMonotoneOn_iff
    {A : SetValuedOperator H H} {U : Set H} :
    A.IsLocallyMaximallyMonotoneOn U ↔
      A.IsMonotone ∧ IsOpen U ∧ Convex ℝ U ∧ (U ∩ A.range).Nonempty ∧
        ∀ ⦃x u : H⦄, u ∈ U → (x, u) ∉ gra A →
          ∃ y v, v ∈ U ∧ (y, v) ∈ gra A ∧ ⟪x - y, u - v⟫_ℝ < 0 := by
  constructor
  · intro hAU
    refine ⟨hAU.monotone, hAU.isOpen, hAU.convex, hAU.inter_range_nonempty, ?_⟩
    intro x u hu hxu
    exact hAU.exists_mem_graph_and_inner_lt_zero_of_not_mem_graph hu hxu
  · rintro ⟨hA_mono, hU_open, hU_convex, hU_range, hsep⟩
    refine ⟨hA_mono, hU_open, hU_convex, hU_range, ?_⟩
    intro x u hu hxu
    rcases hsep hu (by simpa using hxu) with ⟨y, v, hvU, hvA, hlt⟩
    exact ⟨y, v, hvU, by simpa using hvA, hlt⟩

/-- Definition 25.7 (2): a monotone set-valued operator is locally maximally monotone when it is
locally maximally monotone with respect to every open convex set meeting its range. -/
class IsLocallyMaximallyMonotone (A : SetValuedOperator H H) : Prop where
  /-- Local maximal monotonicity includes ordinary monotonicity. -/
  monotone : A.IsMonotone
  /-- Every open convex set meeting the range carries the local maximal monotonicity property. -/
  on :
    ∀ ⦃U : Set H⦄, IsOpen U → Convex ℝ U → (U ∩ A.range).Nonempty →
      A.IsLocallyMaximallyMonotoneOn U

/-- A locally maximally monotone operator is monotone. -/
theorem IsLocallyMaximallyMonotone.isMonotone
    {A : SetValuedOperator H H} (hA : A.IsLocallyMaximallyMonotone) :
    A.IsMonotone :=
  hA.monotone

/-- A locally maximally monotone operator is locally maximally monotone on every open convex set
meeting its range. -/
theorem IsLocallyMaximallyMonotone.on_set
    {A : SetValuedOperator H H} (hA : A.IsLocallyMaximallyMonotone)
    {U : Set H} (hU_open : IsOpen U) (hU_convex : Convex ℝ U)
    (hU_range : (U ∩ A.range).Nonempty) :
    A.IsLocallyMaximallyMonotoneOn U :=
  hA.on hU_open hU_convex hU_range

/-- Unfolding `IsLocallyMaximallyMonotone` exposes monotonicity together with the universal local
maximal-monotonicity condition on open convex sets meeting `range A`. -/
theorem isLocallyMaximallyMonotone_iff
    {A : SetValuedOperator H H} :
    A.IsLocallyMaximallyMonotone ↔
      A.IsMonotone ∧
        ∀ ⦃U : Set H⦄, IsOpen U → Convex ℝ U → (U ∩ A.range).Nonempty →
          A.IsLocallyMaximallyMonotoneOn U := by
  constructor
  · intro hA
    exact ⟨hA.monotone, hA.on⟩
  · rintro ⟨hA_mono, hA_on⟩
    exact ⟨hA_mono, hA_on⟩

end SetValuedOperator
