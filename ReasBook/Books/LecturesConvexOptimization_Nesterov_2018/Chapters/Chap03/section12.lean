import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_12 (from Chap03) -/
universe u

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Definition 3.12 is source-facing in the chapter's hyperplane-separation domain.

Primary domain:
- affine hyperplanes and set separation in a real inner-product space. Specializing
  `E = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ` presentation.

Relevant sampled declarations:
- `AffineHyperplane`
- `AffineHyperplane.SeparatesPointFrom`
- `AffineHyperplane.StrictlySeparatesPointFrom`
- `areStronglySeparable_of_disjoint_closed_convex_of_bounded_one_side`

Best owner abstraction:
- `AffineHyperplane`

Source/core/bridge triage:
- source-facing: the notions that a fixed hyperplane separates, strictly separates, or strongly
  separates two sets, together with the existential set-level predicates
  `AreSeparable`, `AreStrictlySeparable`, and `AreStronglySeparable`;
- core/canonical: `AffineHyperplane`, whose primitive data are a nonzero normal vector and an
  offset;
- bridge/view: the direct coordinate characterizations
  `areSeparable_iff`, `areStrictlySeparable_iff`, `areStronglySeparable_iff`.

Primitive data:
- the nonzero normal vector and offset packaged by `AffineHyperplane`.

Derived API:
- the owner-level separation predicates on `AffineHyperplane`;
- the existential set-level separation predicates;
- the direct coordinate companion equivalences.

This file now defines the later two-set separation layer directly on top of the upstream owner
`AffineHyperplane`, so the earlier point/support file `Definition_3_1_4_1` no longer carries
extra later-chapter public API. The repeated hyperplane/support/point-separation clauses from the
textbook entry are already owned by `Definition_3_1_4_1`; this file adds only the genuinely new
two-set separation layer.
-/

local notation "HPlane" => AffineHyperplane E

namespace AffineHyperplane

/-- `H` separates `Q₁` and `Q₂` when they lie in opposite closed half-spaces of `H`. -/
def SeparatesSets (H : HPlane) (Q₁ Q₂ : Set E) : Prop :=
  Q₁ ⊆ H.closedLowerHalfspace ∧
    Q₂ ⊆ H.closedUpperHalfspace

/-- `H` strictly separates `Q₁` and `Q₂` when it separates them and at least one of the two
defining inequalities is strict. -/
def StrictlySeparatesSets (H : HPlane) (Q₁ Q₂ : Set E) : Prop :=
  H.SeparatesSets Q₁ Q₂ ∧
    (Q₁ ⊆ H.openLowerHalfspace ∨ Q₂ ⊆ H.openUpperHalfspace)

/-- `H` strongly separates `Q₁` and `Q₂` when they lie in opposite open half-spaces of `H`. -/
def StronglySeparatesSets (H : HPlane) (Q₁ Q₂ : Set E) : Prop :=
  Q₁ ⊆ H.openLowerHalfspace ∧
    Q₂ ⊆ H.openUpperHalfspace

end AffineHyperplane

/-- Definition 3.12 (1): two sets are separable when some nonzero normal vector and offset define
a hyperplane whose opposite closed half-spaces contain the two sets. -/
def AreSeparable (Q₁ Q₂ : Set E) : Prop :=
  ∃ H : HPlane, H.SeparatesSets Q₁ Q₂

/-- Definition 3.12 (2): two sets are strictly separable when some hyperplane separates them and
at least one of the two half-space inequalities is strict. -/
def AreStrictlySeparable (Q₁ Q₂ : Set E) : Prop :=
  ∃ H : HPlane, H.StrictlySeparatesSets Q₁ Q₂

/-- Definition 3.12 (3): two sets are strongly separable when some hyperplane places them in
opposite open half-spaces; this is the owner-level form of the source inequality
`sup_{x ∈ Q₁} ⟪g, x⟫ < γ < inf_{y ∈ Q₂} ⟪g, y⟫`. -/
def AreStronglySeparable (Q₁ Q₂ : Set E) : Prop :=
  ∃ H : HPlane, H.StronglySeparatesSets Q₁ Q₂

/-- The empty set and any singleton are strongly separable in a nontrivial real inner-product
space. This is the owner-level empty-case companion used by the later point-versus-set corollary.
-/
-- Proof sketch: choose any nonzero normal vector and place the offset one unit below
-- `⟪g, x⟫`, so the lower-side condition is vacuous on `∅` and the singleton lies strictly in the
-- upper open half-space.
theorem areStronglySeparable_empty_singleton [Nontrivial E] (x : E) :
    AreStronglySeparable (∅ : Set E) ({x} : Set E) := by
  obtain ⟨g, hg⟩ := exists_ne (0 : E)
  refine ⟨⟨g, hg, inner ℝ g x - 1⟩, ?_⟩
  constructor
  · intro y hy
    simp at hy
  · intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    change inner ℝ g x - 1 < inner ℝ g x
    linarith

/-- `AreSeparable` is equivalent to the existence of coordinate data `g ≠ 0`, `γ` defining a
separating hyperplane. -/
-- Proof sketch: unpack an `AffineHyperplane` witness into its normal vector and offset, and
-- conversely package any nonzero `g` and offset `γ` into the corresponding affine hyperplane.
theorem areSeparable_iff {Q₁ Q₂ : Set E} :
    AreSeparable Q₁ Q₂ ↔
      ∃ g : E, ∃ _ : g ≠ 0, ∃ γ : ℝ,
        (∀ x ∈ Q₁, inner ℝ g x ≤ γ) ∧
          ∀ y ∈ Q₂, γ ≤ inner ℝ g y := by
  constructor
  · rintro ⟨H, hH⟩
    refine ⟨H.normal, H.normal_ne_zero, H.offset, ?_⟩
    constructor
    · intro x hx
      exact hH.1 hx
    · intro y hy
      exact hH.2 hy
  · rintro ⟨g, hg, γ, hQ₁, hQ₂⟩
    refine ⟨⟨g, hg, γ⟩, ?_⟩
    constructor
    · intro x hx
      exact hQ₁ x hx
    · intro y hy
      exact hQ₂ y hy

/-- `AreStrictlySeparable` is equivalent to the existence of coordinate data `g ≠ 0`, `γ`
realizing a strict separation. -/
-- Proof sketch: as in `areSeparable_iff`, pass back and forth between an `AffineHyperplane`
-- witness and its normal-offset coordinates; the strictness disjunction is preserved verbatim.
theorem areStrictlySeparable_iff {Q₁ Q₂ : Set E} :
    AreStrictlySeparable Q₁ Q₂ ↔
      ∃ g : E, ∃ _ : g ≠ 0, ∃ γ : ℝ,
        ((∀ x ∈ Q₁, inner ℝ g x ≤ γ) ∧
          ∀ y ∈ Q₂, γ ≤ inner ℝ g y) ∧
            ((∀ x ∈ Q₁, inner ℝ g x < γ) ∨
              ∀ y ∈ Q₂, γ < inner ℝ g y) := by
  constructor
  · rintro ⟨H, hH⟩
    refine ⟨H.normal, H.normal_ne_zero, H.offset, ?_⟩
    refine ⟨?_, ?_⟩
    · constructor
      · intro x hx
        exact hH.1.1 hx
      · intro y hy
        exact hH.1.2 hy
    · rcases hH.2 with hQ₁ | hQ₂
      · left
        intro x hx
        exact hQ₁ hx
      · right
        intro y hy
        exact hQ₂ hy
  · rintro ⟨g, hg, γ, hsep, hstrict⟩
    refine ⟨⟨g, hg, γ⟩, ?_⟩
    refine ⟨?_, ?_⟩
    · constructor
      · intro x hx
        exact hsep.1 x hx
      · intro y hy
        exact hsep.2 y hy
    · rcases hstrict with hQ₁ | hQ₂
      · left
        intro x hx
        exact hQ₁ x hx
      · right
        intro y hy
        exact hQ₂ y hy

/-- `AreStronglySeparable` is equivalent to the existence of coordinate data `g ≠ 0`, `γ`
realizing a strong separation. -/
-- Proof sketch: unpack or repackage the `AffineHyperplane` witness exactly as in
-- `areSeparable_iff`, using the open-halfspace form of strong separation.
theorem areStronglySeparable_iff {Q₁ Q₂ : Set E} :
    AreStronglySeparable Q₁ Q₂ ↔
      ∃ g : E, ∃ _ : g ≠ 0, ∃ γ : ℝ,
        (∀ x ∈ Q₁, inner ℝ g x < γ) ∧
          ∀ y ∈ Q₂, γ < inner ℝ g y := by
  constructor
  · rintro ⟨H, hH⟩
    refine ⟨H.normal, H.normal_ne_zero, H.offset, ?_⟩
    constructor
    · intro x hx
      exact hH.1 hx
    · intro y hy
      exact hH.2 hy
  · rintro ⟨g, hg, γ, hQ₁, hQ₂⟩
    refine ⟨⟨g, hg, γ⟩, ?_⟩
    constructor
    · intro x hx
      exact hQ₁ x hx
    · intro y hy
      exact hQ₂ y hy

namespace AreStronglySeparable

/-- Strong separation of `Q` from the singleton `{x}` yields a point-versus-set coordinate
witness: the same normal vector and offset define a separating hyperplane for `Q` and `x`, and
`x` lies strictly above it. This is the canonical singleton-right bridge from the owner predicate
to the coordinate point-separation API. -/
theorem exists_separatesPointFromWith {Q : Set E} {x : E}
    (h : AreStronglySeparable Q ({x} : Set E)) :
    ∃ g : E, ∃ γ : ℝ, SeparatesPointFromWith Q x g γ ∧ γ < inner ℝ g x := by
  rcases areStronglySeparable_iff.mp h with ⟨g, hg, γ, hQ, hx⟩
  refine ⟨g, γ, ?_, ?_⟩
  · refine ⟨hg, ?_⟩
    constructor
    · intro y hy
      exact (hQ y hy).le
    · exact (hx x (by simp : x ∈ ({x} : Set E))).le
  · simpa using hx x (by simp : x ∈ ({x} : Set E))

end AreStronglySeparable

/-! ### Lemma_3_12 (from Chap03) -/
/- Lemma 3.12 lies in the chapter's weighted-sum / subdifferential calculus for closed convex
`WithTop ℝ`-valued functions on the intrinsic ambient spaces already used by the chapter owners.

Relevant sampled declarations in this domain:
- `withTopEffectiveDomain_nonneg_weighted_add_eq_inter_of_pos` from `Lemma_3_1_12`
- `ClosedConvexFunction.nonneg_weighted_add` from `Lemma_3_1_12`
- `interior_effectiveDomain_nonneg_weighted_add_eq_of_pos` from `Lemma_3_1_12`
- `subdifferential_nonneg_weighted_add_eq_of_pos` from `Lemma_3_1_12`
- `withTopEffectiveDomain` from `Definition_3_3`
- `ClosedConvexFunction` from `Definition_3_1_1_5`
- `subdifferential` from `Definition_3_1_5`

Best owner abstraction:
- the canonical pointwise weighted sum
  `((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂)`
- the ambient effective-domain, closed-convex, and subdifferential notions remain owned by the
  earlier chapter files sampled above
- this file is therefore a bridge/view recalling the weighted-sum theorems stated directly on that
  canonical owner

Primitive data:
- none in this recall file; the imported owner surface already carries the only primitive
  mathematical inputs, namely the scalars `α₁`, `α₂` and the summands `f₁`, `f₂`

Derived API:
- `withTopEffectiveDomain_nonneg_weighted_add_eq_inter_of_pos`
- `ClosedConvexFunction.nonneg_weighted_add`
- `interior_effectiveDomain_nonneg_weighted_add_eq_of_pos`
- `subdifferential_nonneg_weighted_add_eq_of_pos`

Source/core/bridge triage:
- source-facing: the three weighted-sum consequences in Lemma 3.12, now stated on the canonical
  pointwise weighted sum
- core/canonical: `withTopEffectiveDomain`, `ClosedConvexFunction`, `subdifferential`
- bridge/view: the positive-weight effective-domain identity and this recall-only file

This bridge now recalls the weighted-sum conclusions directly on the canonical pointwise weighted
sum. The incorrect auxiliary wrapper has been removed, so the exported surface no longer shrinks
domains at zero weights. -/

recall withTopEffectiveDomain_nonneg_weighted_add_eq_inter_of_pos

recall ClosedConvexFunction.nonneg_weighted_add

recall interior_effectiveDomain_nonneg_weighted_add_eq_of_pos

recall subdifferential_nonneg_weighted_add_eq_of_pos

/-! ### Proposition_3_12 (from Chap03) -/
open scoped WithTopConvexAnalysis

/- Proposition 3.12 lies in the chapter's one-dimensional positive-part / subdifferential domain.

Relevant owner-style declarations sampled before refinement:
- `posPart`
- `posPart_def`
- `subdifferential`
- `mem_subdifferential_iff`

Best owner abstraction:
- the chapter owner `subdifferential`, specialized to the lifted positive-part map
  `fun x : ℝ ↦ ((x⁺ : ℝ) : WithTop ℝ)`

Primitive data:
- the canonical positive-part owner `x ↦ x⁺`
- the owner-level subgradient predicate from `mem_subdifferential_iff`

Derived API:
- the interval description of the source-facing subdifferential at `0`

Source/core/bridge triage:
- source-facing: the subdifferential of `x ↦ (x)_+` at `0`
- core/canonical: `subdifferential`
- bridge/view: `mem_subdifferential_iff`, `posPart_def`

This file therefore removes the duplicate raw set-builder formulation and states the textbook claim
directly on the chapter owner `∂ f(x)`, while keeping the same mathematical meaning. -/

/-- Helper for Proposition 3.12: on the real line, the inner product is ordinary multiplication. -/
lemma real_inner_eq_mul (g x : ℝ) : inner ℝ g x = g * x := by
  -- The one-dimensional Euclidean pairing is just scalar multiplication.
  simpa using (RCLike.inner_apply' g x)

/-- Helper for Proposition 3.12: the global support inequality for `x ↦ x⁺` forces the slope to
lie in `[0, 1]`. -/
lemma subgradient_bounds_of_posPart_support {g : ℝ}
    (hg : ∀ x : ℝ, x⁺ ≥ g * x) : 0 ≤ g ∧ g ≤ 1 := by
  constructor
  · -- Test the support inequality at `x = -1` to obtain the lower bound `0 ≤ g`.
    have hminus := hg (-1)
    have hminus' : 0 ≥ g * (-1 : ℝ) := by
      simpa [posPart_eq_ite] using hminus
    linarith
  · -- Test the support inequality at `x = 1` to obtain the upper bound `g ≤ 1`.
    have hplus := hg 1
    have hplus' : 1 ≥ g * (1 : ℝ) := by
      simpa [posPart_eq_ite] using hplus
    linarith

/-- Helper for Proposition 3.12: every slope `g ∈ [0, 1]` supports the positive-part function from
below at the origin. -/
lemma posPart_support_of_mem_Icc {g : ℝ} (hg : g ∈ Set.Icc (0 : ℝ) 1) :
    ∀ x : ℝ, x⁺ ≥ g * x := by
  intro x
  by_cases hx : 0 ≤ x
  · -- On the nonnegative ray, `x⁺ = x`, so it is enough to compare `g * x` with `x`.
    have hmul : g * x ≤ x := by
      have hmul' : g * x ≤ 1 * x := mul_le_mul_of_nonneg_right hg.2 hx
      simpa using hmul'
    simpa [posPart_eq_ite, hx] using hmul
  · -- On the nonpositive ray, `x⁺ = 0`, and `g * x ≤ 0` follows from `g ≥ 0`.
    have hx' : x ≤ 0 := le_of_not_ge hx
    have hmul : g * x ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos hg.1 hx'
    simpa [posPart_eq_ite, hx] using hmul

/-- Proposition 3.12: for `f(x) = (x)_+`, the subdifferential at `0` is exactly the interval
`[0, 1]`. -/
-- Proof sketch: rewrite membership in the owner subdifferential `∂ f(0)` via
-- `mem_subdifferential_coe_real_iff`, which produces the textbook support inequality
-- `x⁺ ≥ g * x`. Testing at `x = -1` and `x = 1` gives `0 ≤ g ≤ 1`. Conversely, if
-- `g ∈ [0, 1]`, then `g * x ≤ x⁺` follows from the cases `x ≥ 0` and `x ≤ 0`.
theorem real_posPart_subdifferential_at_zero_eq_Icc :
    ∂ (fun x : ℝ ↦ (x⁺ : ℝ))(0) = Set.Icc (0 : ℝ) 1 := by
  ext g
  rw [Set.mem_Icc, mem_subdifferential_coe_real_iff]
  -- Rewrite the owner-level subgradient condition into the scalar support inequality from the
  -- source proof.
  constructor
  · intro hg
    -- The forward inclusion is exactly the endpoint test from the source proof.
    exact subgradient_bounds_of_posPart_support (fun x ↦ by
      have hx := hg x
      simpa [real_inner_eq_mul, sub_eq_add_neg] using hx)
  · intro hg x
    -- The reverse inclusion is the two-case sign split proving `x⁺ ≥ g * x`.
    have hx := posPart_support_of_mem_Icc hg x
    simpa [real_inner_eq_mul, sub_eq_add_neg] using hx

/-! ### Theorem_3_12 (from Chap03) -/
/- Theorem 3.12 is a recall-only item in the chapter's convex-analysis/minimax-linearization
domain.

Sampled owner-style declarations:
- `ClosedConvexOn`
- `maxTypeObjective`
- `constrainedSublevelSet`
- `exists_stdSimplex_minimax_linearization_of_bounded_familyMaximumSublevelSets`

Best owner abstraction:
- source-facing: the bounded-level-set minimax-linearization statement of Theorem 3.12
- core/canonical: `maxTypeObjective fs`, the bounded feasible sublevel owner
  `constrainedSublevelSet Q (fun x ↦ ((maxTypeObjective fs x : ℝ) : WithTop ℝ)) α`, and the
  simplex coefficient owner `StdSimplex ℝ ι`
- bridge/view: the weighted-sum expression `∑ i, coeffs.weights i * fs i x`, derived from the
  canonical simplex data

Primitive data:
- a nonempty finite family `fs : ι → E → ℝ`
- closed convexity of each component on `Q`
- boundedness of the constrained sublevel sets of `maxTypeObjective fs`

Derived API:
- the simplex coefficient vector `coeffs : StdSimplex ℝ ι`
- the equality of constrained `EReal` infima between `maxTypeObjective fs` and the simplex-weighted
  objective

The previous version introduced a second public theorem name with exactly the same interface as the
upstream source-facing theorem
`exists_stdSimplex_minimax_linearization_of_bounded_familyMaximumSublevelSets`. Since that theorem
already has the correct statement and owner-level data, this file now recalls it directly instead
of keeping a duplicate wrapper. In particular, the old file-level `[FiniteDimensional ℝ E]`
assumption was redundant and is removed here because the canonical theorem does not use it.
-/

recall exists_stdSimplex_minimax_linearization_of_bounded_familyMaximumSublevelSets
