import Mathlib.Analysis.Convex.Jensen
import Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2
import Integer.Chapters.Chap08.section_8_5.ch8_sec8_5_exercise_8_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

-- Domain sampling for this file:
-- * source-facing layer: the split product-space formulation and its equality-dual value;
-- * core/canonical owners: `mixed_integer_equality_lagrangian_base_set` from Exercise 8.2 and
--   the Section 8.1 Lagrangian-duality pattern;
-- * bridge/view constraint: the Section 8.1 owners are stated for a single `Fin n` variable with
--   inequality multipliers, so the split product/equality-dual layer remains local here.
--
-- The duplicated wheel to remove is therefore only the exercise-number shell around the local
-- split owner, while the upstream mixed-integer block owner continues to be reused directly.

noncomputable section

section Exercise88

variable {m₁ m₂ n p : ℕ}

abbrev split_mixed_integer_base_set
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  Set.prod
    (mixed_integer_equality_lagrangian_base_set hp A₁ b₁)
    (mixed_integer_equality_lagrangian_base_set hp A₂ b₂)

/-- Membership in `split_mixed_integer_base_set hp A₁ b₁ A₂ b₂` means that the first component
lies in the first mixed-integer base set and the second component lies in the second one. -/
theorem mem_split_mixed_integer_base_set_iff
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    {x y : Fin n → ℝ} :
    (x, y) ∈ split_mixed_integer_base_set hp A₁ b₁ A₂ b₂ ↔
      x ∈ mixed_integer_equality_lagrangian_base_set hp A₁ b₁ ∧
        y ∈ mixed_integer_equality_lagrangian_base_set hp A₂ b₂ :=
  Iff.rfl

/-- The Lagrangian relaxation value obtained from the split formulation of Exercise 8.8 by
dualizing the coupling equations `x - y = 0` with unrestricted multiplier vector `λ`. -/
def split_mixed_integer_lagrangian_relaxation_value
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ)
    (lam : Fin n → ℝ) : EReal :=
  sSup
    ((fun xy : (Fin n → ℝ) × (Fin n → ℝ) ↦
        ((c ⬝ᵥ xy.1 + lam ⬝ᵥ (xy.2 - xy.1) : ℝ) : EReal)) ''
      split_mixed_integer_base_set hp A₁ b₁ A₂ b₂)

/-- `split_mixed_integer_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c λ` unfolds to the supremum
of the split Lagrangian objective over `split_mixed_integer_base_set hp A₁ b₁ A₂ b₂`. -/
theorem split_mixed_integer_lagrangian_relaxation_value_eq_sSup
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ)
    (lam : Fin n → ℝ) :
    split_mixed_integer_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c lam =
      sSup
        ((fun xy : (Fin n → ℝ) × (Fin n → ℝ) ↦
            ((c ⬝ᵥ xy.1 + lam ⬝ᵥ (xy.2 - xy.1) : ℝ) : EReal)) ''
          split_mixed_integer_base_set hp A₁ b₁ A₂ b₂) :=
  rfl

/-- The Lagrangian dual value `z̄` from Exercise 8.8, obtained by minimizing the split
Lagrangian-relaxation value over all multiplier vectors `λ ∈ ℝ^n`. -/
def split_mixed_integer_lagrangian_dual_value
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ) : EReal :=
  sInf
    (Set.range fun lam : Fin n → ℝ ↦
      split_mixed_integer_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c lam)

/-- `split_mixed_integer_lagrangian_dual_value hp A₁ b₁ A₂ b₂ c` unfolds to the infimum of the
split Lagrangian-relaxation values over all multiplier vectors `λ ∈ ℝ^n`. -/
theorem split_mixed_integer_lagrangian_dual_value_eq_sInf
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ) :
    split_mixed_integer_lagrangian_dual_value hp A₁ b₁ A₂ b₂ c =
      sInf
        (Set.range fun lam : Fin n → ℝ ↦
          split_mixed_integer_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c lam) :=
  rfl

/-- The feasible region `conv(Q₁) ∩ conv(Q₂)` that appears in the convex-hull description of the
split Lagrangian dual from Exercise 8.8. -/
abbrev split_mixed_integer_convex_hull_intersection
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ) : Set (Fin n → ℝ) :=
  convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₁ b₁) ∩
    convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₂ b₂)

/-- Membership in `split_mixed_integer_convex_hull_intersection hp A₁ b₁ A₂ b₂` means belonging
to both convex hulls `conv(Q₁)` and `conv(Q₂)`. -/
theorem mem_split_mixed_integer_convex_hull_intersection_iff
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    {x : Fin n → ℝ} :
    x ∈ split_mixed_integer_convex_hull_intersection hp A₁ b₁ A₂ b₂ ↔
      x ∈ convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₁ b₁) ∧
      x ∈ convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₂ b₂) :=
  Iff.rfl

/-- The canonical Chapter 8 value of maximizing `c x` over `conv(Q₁) ∩ conv(Q₂)`, recorded on the
`EReal` value layer so the statement remains meaningful without separate attainment or boundedness
hypotheses. -/
noncomputable abbrev split_mixed_integer_convex_hull_intersection_value
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ) : EReal :=
  integer_program_value (0 : Matrix (Fin 0) (Fin n) ℝ) (0 : Fin 0 → ℝ) c
    (split_mixed_integer_convex_hull_intersection hp A₁ b₁ A₂ b₂)

/-- `split_mixed_integer_convex_hull_intersection_value hp A₁ b₁ A₂ b₂ c` unfolds to the
supremum of the objective over `conv(Q₁) ∩ conv(Q₂)`. -/
theorem split_mixed_integer_convex_hull_intersection_value_eq_sSup
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ) :
    split_mixed_integer_convex_hull_intersection_value hp A₁ b₁ A₂ b₂ c =
      sSup
        ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
          split_mixed_integer_convex_hull_intersection hp A₁ b₁ A₂ b₂) := by
  simp [split_mixed_integer_convex_hull_intersection_value, integer_program_value,
    lagrangian_integer_feasible_set]

/-- Helper for Exercise 8.8: `splitStrictDisplacementHypograph C₁ C₂ c` is the strict hypograph in
the displacement-value space generated by pairs `x ∈ C₁`, `y ∈ C₂` and levels
`t < c ⬝ᵥ x`. -/
private def splitStrictDisplacementHypograph
    (C₁ C₂ : Set (Fin n → ℝ))
    (c : Fin n → ℝ) : Set ((Fin n → ℝ) × ℝ) :=
  {p : (Fin n → ℝ) × ℝ |
    ∃ x ∈ C₁, ∃ y ∈ C₂, p.1 = y - x ∧ p.2 < c ⬝ᵥ x}

/-- Helper for Exercise 8.8: the strict displacement hypograph is convex as soon as both source
sets are convex. -/
private lemma splitStrictDisplacementHypographConvex
    (C₁ C₂ : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    (hC₁ : Convex ℝ C₁)
    (hC₂ : Convex ℝ C₂) :
    Convex ℝ (splitStrictDisplacementHypograph C₁ C₂ c) := by
  intro a ha b hb t s ht hs hts
  rcases ha with ⟨x₁, hx₁, y₁, hy₁, hdisp₁, hobj₁⟩
  rcases hb with ⟨x₂, hx₂, y₂, hy₂, hdisp₂, hobj₂⟩
  refine ⟨t • x₁ + s • x₂, hC₁ hx₁ hx₂ ht hs hts,
    t • y₁ + s • y₂, hC₂ hy₁ hy₂ ht hs hts, ?_, ?_⟩
  · -- The displacement coordinate respects convex combinations componentwise.
    calc
      (t • a + s • b).1 = t • a.1 + s • b.1 := by rfl
      _ = t • (y₁ - x₁) + s • (y₂ - x₂) := by rw [hdisp₁, hdisp₂]
      _ = t • y₁ + s • y₂ - (t • x₁ + s • x₂) := by
        ext i
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  · -- The height coordinate keeps the strict inequality because the objective is affine.
    have hlin :
        c ⬝ᵥ (t • x₁ + s • x₂) =
          t * (c ⬝ᵥ x₁) + s * (c ⬝ᵥ x₂) := by
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul]
      simp [smul_eq_mul]
    have hlt :
        t * a.2 + s * b.2 <
          t * (c ⬝ᵥ x₁) + s * (c ⬝ᵥ x₂) := by
      by_cases ht0 : t = 0
      · have hs_pos : 0 < s := by linarith
        have h₂ : s * b.2 < s * (c ⬝ᵥ x₂) := by
          nlinarith
        simpa [ht0] using h₂
      · by_cases hs0 : s = 0
        · have ht_pos : 0 < t := by linarith
          have h₁ : t * a.2 < t * (c ⬝ᵥ x₁) := by
            nlinarith
          simpa [hs0] using h₁
        · have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
          have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
          have h₁ : t * a.2 < t * (c ⬝ᵥ x₁) := by
            nlinarith
          have h₂ : s * b.2 < s * (c ⬝ᵥ x₂) := by
            nlinarith
          linarith
    simpa [hlin]

/-- Helper for Exercise 8.8: the strict displacement hypograph is downward closed in its scalar
coordinate. -/
private lemma splitStrictDisplacementHypograph_downward
    (C₁ C₂ : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    {u : Fin n → ℝ}
    {t s : ℝ}
    (ht : (u, t) ∈ splitStrictDisplacementHypograph C₁ C₂ c)
    (hs : s ≤ t) :
    (u, s) ∈ splitStrictDisplacementHypograph C₁ C₂ c := by
  rcases ht with ⟨x, hx, y, hy, hdisp, hobj⟩
  refine ⟨x, hx, y, hy, hdisp, ?_⟩
  exact lt_of_le_of_lt hs hobj

/-- Helper for Exercise 8.8: every diagonal witness `x ∈ C₁ ∩ C₂` contributes the whole strict
vertical ray below `c ⬝ᵥ x` at displacement `0`. -/
private lemma zero_mem_splitStrictDisplacementHypograph_of_mem_inter
    (C₁ C₂ : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    {x : Fin n → ℝ}
    (hx : x ∈ C₁ ∩ C₂)
    {t : ℝ}
    (ht : t < c ⬝ᵥ x) :
    ((0 : Fin n → ℝ), t) ∈ splitStrictDisplacementHypograph C₁ C₂ c := by
  refine ⟨x, hx.1, x, hx.2, ?_, ht⟩
  ext i
  simp

/-- Helper for Exercise 8.8: the strict displacement hypograph can be read fiberwise by fixing the
first-set witness `x` and asking that its translate `x + u` belongs to `C₂`. -/
private lemma splitStrictDisplacementHypograph_mem_iff_exists_add
    (C₁ C₂ : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    {u : Fin n → ℝ}
    {t : ℝ} :
    (u, t) ∈ splitStrictDisplacementHypograph C₁ C₂ c ↔
      ∃ x ∈ C₁, x + u ∈ C₂ ∧ t < c ⬝ᵥ x := by
  constructor
  · rintro ⟨x, hx, y, hy, hdisp, hobj⟩
    refine ⟨x, hx, ?_, hobj⟩
    -- Rewrite the displacement witness into the translated-membership view `x + u ∈ C₂`.
    have hy_eq : x + u = y := by
      ext i
      have hi : u i = y i - x i := by
        simpa using congrArg (fun v : Fin n → ℝ ↦ v i) hdisp
      calc
        (x + u) i = x i + u i := by simp
        _ = x i + (y i - x i) := by rw [hi]
        _ = y i := by ring
    exact hy_eq ▸ hy
  · rintro ⟨x, hx, hxu, hobj⟩
    refine ⟨x, hx, x + u, hxu, ?_, hobj⟩
    -- Repackage the translated witness back into the source `(x, y)` formulation.
    ext i
    simp

/-- Helper for Exercise 8.8: the zero-displacement slice of the strict hypograph is exactly the
strict hypograph of the objective over `C₁ ∩ C₂`. -/
private lemma splitStrictDisplacementHypograph_zeroSlice_iff
    (C₁ C₂ : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    {t : ℝ} :
    ((0 : Fin n → ℝ), t) ∈ splitStrictDisplacementHypograph C₁ C₂ c ↔
      ∃ x ∈ C₁ ∩ C₂, t < c ⬝ᵥ x := by
  constructor
  · rintro ⟨x, hx, y, hy, hdisp, hobj⟩
    -- On the zero slice, the displacement witness forces the two primal points to coincide.
    have hxy : y = x := by
      ext i
      have hi : (0 : ℝ) = y i - x i := by
        simpa using congrArg (fun v : Fin n → ℝ ↦ v i) hdisp
      have hi' : y i - x i = 0 := by
        simpa using hi.symm
      exact sub_eq_zero.mp hi'
    subst y
    exact ⟨x, ⟨hx, hy⟩, hobj⟩
  · rintro ⟨x, hx, hobj⟩
    -- Repackage the common witness back into the source hypograph owner.
    exact zero_mem_splitStrictDisplacementHypograph_of_mem_inter C₁ C₂ c hx hobj

/-- Helper for Exercise 8.8: the displacement-value function at shift `u` is the supremum of
`c ⬝ᵥ x` over witnesses `x ∈ C₁` whose translate `x + u` lies in `C₂`. -/
private def splitDisplacementValue
    (C₁ C₂ : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    (u : Fin n → ℝ) : EReal :=
  sSup
    ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
      {x : Fin n → ℝ | x ∈ C₁ ∧ x + u ∈ C₂})

/-- Helper for Exercise 8.8: at zero displacement, the displacement value is exactly the supremum
of `c ⬝ᵥ x` over `C₁ ∩ C₂`. -/
private lemma splitDisplacementValue_zero_eq_intersectionSup
    (C₁ C₂ : Set (Fin n → ℝ))
    (c : Fin n → ℝ) :
    splitDisplacementValue C₁ C₂ c 0 =
      sSup ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) '' (C₁ ∩ C₂)) := by
  -- At `u = 0`, the translation side condition collapses to ordinary intersection membership.
  simp [splitDisplacementValue]

/-- Helper for Exercise 8.8: the closed hypograph owner of the displacement-value function. -/
private def splitDisplacementClosedHypograph
    (C₁ C₂ : Set (Fin n → ℝ))
    (c : Fin n → ℝ) : Set ((Fin n → ℝ) × ℝ) :=
  {p : (Fin n → ℝ) × ℝ | ((p.2 : ℝ) : EReal) ≤ splitDisplacementValue C₁ C₂ c p.1}

/-- Helper for Exercise 8.8: every strict-hypograph witness also belongs to the closed displacement
hypograph. -/
private lemma splitStrictDisplacementHypograph_subset_closedHypograph
    (C₁ C₂ : Set (Fin n → ℝ))
    (c : Fin n → ℝ) :
    splitStrictDisplacementHypograph C₁ C₂ c ⊆
      splitDisplacementClosedHypograph C₁ C₂ c := by
  rintro ⟨u, t⟩ ht
  rcases (splitStrictDisplacementHypograph_mem_iff_exists_add C₁ C₂ c).1 ht with
    ⟨x, hx, hxu, hobj⟩
  change ((t : ℝ) : EReal) ≤
    sSup
      ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
        {x : Fin n → ℝ | x ∈ C₁ ∧ x + u ∈ C₂})
  -- A strict witness contributes one objective value below the displacement supremum.
  have ht_lt_obj : ((t : ℝ) : EReal) < ((c ⬝ᵥ x : ℝ) : EReal) := by
    exact_mod_cast hobj
  exact le_of_lt (lt_of_lt_of_le ht_lt_obj (le_sSup ⟨x, ⟨hx, hxu⟩, rfl⟩))

/-- Helper for Exercise 8.8: a strict threshold at `u = 0` excludes the corresponding point from
the closed displacement hypograph. -/
private lemma zero_not_mem_splitDisplacementClosedHypograph_of_threshold
    (C₁ C₂ : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    {r : ℝ}
    (hr : splitDisplacementValue C₁ C₂ c 0 < (r : EReal)) :
    ((0 : Fin n → ℝ), r) ∉ splitDisplacementClosedHypograph C₁ C₂ c := by
  intro hmem
  -- Membership in the closed hypograph would reverse the strict threshold inequality.
  exact (not_le_of_gt hr) hmem

/-- Helper for Exercise 8.8: a threshold strictly above the intersection-value supremum excludes
the corresponding point on the zero-displacement line from the closure of the zero-line slice. -/
private lemma splitStrictDisplacementHypograph_zeroLine_outside_of_threshold
    (C₁ C₂ : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    {r : ℝ}
    (hr :
      sSup ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) '' (C₁ ∩ C₂)) < (r : EReal)) :
    ((0 : Fin n → ℝ), r) ∉
      closure (splitStrictDisplacementHypograph C₁ C₂ c ∩ {p : (Fin n → ℝ) × ℝ | p.1 = 0}) := by
  intro hclosure
  obtain ⟨q, hsup_lt_q, hq_lt_rE⟩ := EReal.lt_iff_exists_real_btwn.mp hr
  have hq_lt_r : q < r := by
    exact_mod_cast hq_lt_rE
  have hpoint_mem :
      (((0 : Fin n → ℝ), r) : (Fin n → ℝ) × ℝ) ∈
        (Set.univ : Set (Fin n → ℝ)) ×ˢ Set.Ioi q := by
    simp [hq_lt_r]
  rcases mem_closure_iff.mp hclosure
      ((Set.univ : Set (Fin n → ℝ)) ×ˢ Set.Ioi q)
      (isOpen_univ.prod isOpen_Ioi) hpoint_mem with
    ⟨p, hp_open, hp_mem⟩
  rcases hp_mem with ⟨hpH, hpZero⟩
  rcases p with ⟨u, s⟩
  change u = 0 at hpZero
  subst u
  rcases hp_open with ⟨_, hs_gt_q⟩
  rcases (splitStrictDisplacementHypograph_zeroSlice_iff C₁ C₂ c).mp hpH with
    ⟨x, hx, hs_lt_obj⟩
  have hs_lt_sup :
      ((s : ℝ) : EReal) <
        sSup ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) '' (C₁ ∩ C₂)) := by
    -- The zero-slice witness contributes one objective value to the intersection supremum.
    have hs_lt_objE : ((s : ℝ) : EReal) < ((c ⬝ᵥ x : ℝ) : EReal) := by
      exact_mod_cast hs_lt_obj
    exact lt_of_lt_of_le hs_lt_objE (le_sSup ⟨x, hx, rfl⟩)
  have hsup_lt_s :
      sSup ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) '' (C₁ ∩ C₂)) <
        ((s : ℝ) : EReal) := by
    exact lt_of_lt_of_le hsup_lt_q (le_of_lt (by exact_mod_cast hs_gt_q))
  exact (lt_irrefl (((s : ℝ) : EReal))) (hs_lt_sup.trans hsup_lt_s)

/-- Helper for Exercise 8.8: every point of
`conv(Q₁) ×ˢ conv(Q₂)` has split penalized objective value bounded above by the original split
relaxation value. -/
private lemma splitPenalizedObjective_le_relaxation_of_mem_convexifiedProduct
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ)
    (lam : Fin n → ℝ)
    {xy : (Fin n → ℝ) × (Fin n → ℝ)}
    (hxy :
      xy ∈ convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₁ b₁) ×ˢ
        convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₂ b₂)) :
    ((c ⬝ᵥ xy.1 + lam ⬝ᵥ (xy.2 - xy.1) : ℝ) : EReal) ≤
      split_mixed_integer_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c lam := by
  rcases hxy with ⟨hxHull, hyHull⟩
  let xObjective : (Fin n → ℝ) →ₗ[ℝ] ℝ := dotProductBilin ℝ ℝ (c - lam)
  let yObjective : (Fin n → ℝ) →ₗ[ℝ] ℝ := dotProductBilin ℝ ℝ lam
  have hxObjectiveConvex :
      ConvexOn ℝ Set.univ (fun x : Fin n → ℝ ↦ xObjective x + lam ⬝ᵥ xy.2) := by
    -- The split objective is affine in the first block when the second block is fixed.
    simpa [xObjective] using
      (LinearMap.convexOn xObjective (s := Set.univ) convex_univ).add_const (lam ⬝ᵥ xy.2)
  have hyObjectiveConvex :
      ConvexOn ℝ Set.univ (fun y : Fin n → ℝ ↦ yObjective y + (c - lam) ⬝ᵥ xy.1) := by
    -- The same affine-linearity holds in the second block once the first block is fixed.
    simpa [yObjective] using
      (LinearMap.convexOn yObjective (s := Set.univ) convex_univ).add_const
        ((c - lam) ⬝ᵥ xy.1)
  have hxObjective_eval (x : Fin n → ℝ) :
      xObjective x + lam ⬝ᵥ xy.2 = c ⬝ᵥ x + lam ⬝ᵥ (xy.2 - x) := by
    calc
      xObjective x + lam ⬝ᵥ xy.2 = (c - lam) ⬝ᵥ x + lam ⬝ᵥ xy.2 := by
        rfl
      _ = (c ⬝ᵥ x - lam ⬝ᵥ x) + lam ⬝ᵥ xy.2 := by
        rw [sub_dotProduct]
      _ = c ⬝ᵥ x + (lam ⬝ᵥ xy.2 - lam ⬝ᵥ x) := by
        ring
      _ = c ⬝ᵥ x + lam ⬝ᵥ (xy.2 - x) := by
        rw [dotProduct_sub]
  obtain ⟨x₀, hx₀, hfirst⟩ :=
    ConvexOn.exists_ge_of_mem_convexHull hxObjectiveConvex
      (show mixed_integer_equality_lagrangian_base_set hp A₁ b₁ ⊆ Set.univ by
        intro x hx
        trivial)
      hxHull
  have hyObjective_eval (y : Fin n → ℝ) :
      yObjective y + (c - lam) ⬝ᵥ x₀ = c ⬝ᵥ x₀ + lam ⬝ᵥ (y - x₀) := by
    calc
      yObjective y + (c - lam) ⬝ᵥ x₀ = lam ⬝ᵥ y + (c - lam) ⬝ᵥ x₀ := by
        rfl
      _ = lam ⬝ᵥ y + (c ⬝ᵥ x₀ - lam ⬝ᵥ x₀) := by
        rw [sub_dotProduct]
      _ = c ⬝ᵥ x₀ + (lam ⬝ᵥ y - lam ⬝ᵥ x₀) := by
        ring
      _ = c ⬝ᵥ x₀ + lam ⬝ᵥ (y - x₀) := by
        rw [dotProduct_sub]
  have hyObjectiveConvexAtX₀ :
      ConvexOn ℝ Set.univ (fun y : Fin n → ℝ ↦ yObjective y + (c - lam) ⬝ᵥ x₀) := by
    -- Recenter the affine second-block objective at the chosen first-block witness.
    simpa [yObjective] using
      (LinearMap.convexOn yObjective (s := Set.univ) convex_univ).add_const
        ((c - lam) ⬝ᵥ x₀)
  obtain ⟨y₀, hy₀, hsecond⟩ :=
    ConvexOn.exists_ge_of_mem_convexHull hyObjectiveConvexAtX₀
      (show mixed_integer_equality_lagrangian_base_set hp A₂ b₂ ⊆ Set.univ by
        intro y hy
        trivial)
      hyHull
  have hstepFirst :
      c ⬝ᵥ xy.1 + lam ⬝ᵥ (xy.2 - xy.1) ≤
        c ⬝ᵥ x₀ + lam ⬝ᵥ (xy.2 - x₀) := by
    calc
      c ⬝ᵥ xy.1 + lam ⬝ᵥ (xy.2 - xy.1) = xObjective xy.1 + lam ⬝ᵥ xy.2 := by
        rw [hxObjective_eval]
      _ ≤ xObjective x₀ + lam ⬝ᵥ xy.2 := hfirst
      _ = c ⬝ᵥ x₀ + lam ⬝ᵥ (xy.2 - x₀) := hxObjective_eval x₀
  have hstepSecond :
      c ⬝ᵥ x₀ + lam ⬝ᵥ (xy.2 - x₀) ≤
        c ⬝ᵥ x₀ + lam ⬝ᵥ (y₀ - x₀) := by
    calc
      c ⬝ᵥ x₀ + lam ⬝ᵥ (xy.2 - x₀) = yObjective xy.2 + (c - lam) ⬝ᵥ x₀ := by
        rw [hyObjective_eval]
      _ ≤ yObjective y₀ + (c - lam) ⬝ᵥ x₀ := hsecond
      _ = c ⬝ᵥ x₀ + lam ⬝ᵥ (y₀ - x₀) := hyObjective_eval y₀
  have hwitness :
      ((c ⬝ᵥ x₀ + lam ⬝ᵥ (y₀ - x₀) : ℝ) : EReal) ≤
        split_mixed_integer_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c lam := by
    -- Reinsert the maximizing witnesses from both factor base sets into the split supremum.
    rw [split_mixed_integer_lagrangian_relaxation_value_eq_sSup]
    exact le_sSup ⟨(x₀, y₀), ⟨hx₀, hy₀⟩, rfl⟩
  exact
    (show ((c ⬝ᵥ xy.1 + lam ⬝ᵥ (xy.2 - xy.1) : ℝ) : EReal) ≤
        ((c ⬝ᵥ x₀ + lam ⬝ᵥ (y₀ - x₀) : ℝ) : EReal) by
      exact_mod_cast hstepFirst.trans hstepSecond).trans hwitness

/-- Helper for Exercise 8.8: the split relaxation can be computed over
`conv(Q₁) ×ˢ conv(Q₂)` because the split objective is affine in each block. -/
private lemma splitRelaxationValue_eq_convexifiedProduct
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ)
    (lam : Fin n → ℝ) :
    split_mixed_integer_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c lam =
      sSup
        ((fun xy : (Fin n → ℝ) × (Fin n → ℝ) ↦
            ((c ⬝ᵥ xy.1 + lam ⬝ᵥ (xy.2 - xy.1) : ℝ) : EReal)) ''
          ((convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₁ b₁)) ×ˢ
            (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₂ b₂)))) := by
  rw [split_mixed_integer_lagrangian_relaxation_value_eq_sSup]
  refine le_antisymm ?_ ?_
  · -- The original split base set sits inside the product of the two convex hulls.
    refine sSup_le ?_
    rintro _ ⟨xy, hxy, rfl⟩
    apply le_sSup
    refine ⟨xy, ?_, rfl⟩
    rcases hxy with ⟨hx, hy⟩
    exact ⟨subset_convexHull ℝ _ hx, subset_convexHull ℝ _ hy⟩
  · -- Every point of the convexified product is dominated by a point of the original split base
    -- set, so the supremum does not change after convexification.
    refine sSup_le ?_
    rintro _ ⟨xy, hxy, rfl⟩
    rw [← split_mixed_integer_lagrangian_relaxation_value_eq_sSup]
    exact
      splitPenalizedObjective_le_relaxation_of_mem_convexifiedProduct hp A₁ b₁ A₂ b₂ c lam hxy

/-- Helper for Exercise 8.8: diagonal points from `conv(Q₁) ∩ conv(Q₂)` give feasible witnesses
for every split relaxation, so the convex-hull intersection value is bounded above by the split
dual value. -/
private lemma splitConvexHullIntersectionValue_le_splitDualValue
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ) :
    split_mixed_integer_convex_hull_intersection_value hp A₁ b₁ A₂ b₂ c ≤
      split_mixed_integer_lagrangian_dual_value hp A₁ b₁ A₂ b₂ c := by
  rw [split_mixed_integer_convex_hull_intersection_value_eq_sSup,
    split_mixed_integer_lagrangian_dual_value_eq_sInf]
  refine le_sInf ?_
  rintro _ ⟨lam, rfl⟩
  change
    sSup ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
      split_mixed_integer_convex_hull_intersection hp A₁ b₁ A₂ b₂) ≤
      split_mixed_integer_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c lam
  rw [splitRelaxationValue_eq_convexifiedProduct]
  refine sSup_le ?_
  rintro _ ⟨x, hx, rfl⟩
  rcases (mem_split_mixed_integer_convex_hull_intersection_iff hp A₁ b₁ A₂ b₂).1 hx with
    ⟨hx₁, hx₂⟩
  have hwitness :
      ((c ⬝ᵥ x : ℝ) : EReal) ≤
        sSup
          ((fun xy : (Fin n → ℝ) × (Fin n → ℝ) ↦
              ((c ⬝ᵥ xy.1 + lam ⬝ᵥ (xy.2 - xy.1) : ℝ) : EReal)) ''
            ((convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₁ b₁)) ×ˢ
              (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₂ b₂)))) := by
    -- The coupling penalty vanishes on the diagonal pair `(x, x)`.
    have :
        ((c ⬝ᵥ x + lam ⬝ᵥ (x - x) : ℝ) : EReal) ≤
          sSup
            ((fun xy : (Fin n → ℝ) × (Fin n → ℝ) ↦
                ((c ⬝ᵥ xy.1 + lam ⬝ᵥ (xy.2 - xy.1) : ℝ) : EReal)) ''
              ((convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₁ b₁)) ×ˢ
                (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₂ b₂)))) := by
      exact le_sSup ⟨(x, x), ⟨hx₁, hx₂⟩, rfl⟩
    simpa using this
  exact hwitness

/-- Helper for Exercise 8.8: a strict upper threshold on the intersection value yields one
multiplier vector whose convexified split relaxation lies below that threshold. -/
private lemma strictDisplacementHypographSeparator
    (H : Set ((Fin n → ℝ) × ℝ))
    (hH_convex : Convex ℝ H)
    (hH_downward :
      ∀ {u : Fin n → ℝ} {t s : ℝ}, (u, t) ∈ H → s ≤ t → (u, s) ∈ H)
    (hvertical : ∃ s₀ : ℝ, ((0 : Fin n → ℝ), s₀) ∈ H)
    {r : ℝ}
    (hr : ((0 : Fin n → ℝ), r) ∉ closure H) :
    ∃ lam : Fin n → ℝ,
      ∀ p ∈ H, ((p.2 + lam ⬝ᵥ p.1 : ℝ) : EReal) ≤ (r : EReal) := by
  obtain ⟨f, u, hsep, hstrict⟩ :=
    geometric_hahn_banach_closed_point
      (s := closure H)
      (x := ((0 : Fin n → ℝ), r))
      hH_convex.closure
      isClosed_closure
      hr
  let ℓ : (Fin n → ℝ) →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) ℝ)
  let a : ℝ := f (0, 1)
  have hprod (y : Fin n → ℝ) (t : ℝ) : f (y, t) = ℓ y + a * t := by
    have hsmul : ((0 : Fin n → ℝ), t) = t • ((0 : Fin n → ℝ), (1 : ℝ)) := by
      ext i <;> simp
    -- Split the product-space functional into its horizontal and vertical parts.
    calc
      f (y, t) = f ((y, 0) + (0, t)) := by simp
      _ = f (y, 0) + f (0, t) := by rw [map_add]
      _ = ℓ y + f (0, t) := by simp [ℓ]
      _ = ℓ y + a * t := by
        rw [hsmul, map_smul]
        simp [a, mul_comm]
  rcases hvertical with ⟨s₀, hs₀⟩
  have ha_nonneg : 0 ≤ a := by
    by_contra ha_neg
    have ha_lt : a < 0 := lt_of_not_ge ha_neg
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (u - a * s₀) / (-a) < N := exists_nat_gt ((u - a * s₀) / (-a))
    let t : ℝ := s₀ - (N : ℝ)
    have ht_le : t ≤ s₀ := by
      dsimp [t]
      linarith
    have ht_mem : ((0 : Fin n → ℝ), t) ∈ H :=
      hH_downward hs₀ ht_le
    have ht_sep : f ((0 : Fin n → ℝ), t) < u :=
      hsep _ (subset_closure ht_mem)
    have hu_lt : u < a * t := by
      dsimp [t]
      have hden_pos : 0 < -a := by linarith
      have hmul : u - a * s₀ < (N : ℝ) * (-a) := by
        have hmul' : ((u - a * s₀) / (-a)) * (-a) < (N : ℝ) * (-a) :=
          mul_lt_mul_of_pos_right hN hden_pos
        have hcancel : ((u - a * s₀) / (-a)) * (-a) = u - a * s₀ := by
          exact div_mul_cancel₀ _ hden_pos.ne'
        rw [hcancel] at hmul'
        exact hmul'
      nlinarith [hmul]
    have hft : f ((0 : Fin n → ℝ), t) = a * t := by
      rw [hprod]
      simp [a]
    linarith
  have ha_ne : a ≠ 0 := by
    intro ha_zero
    have hs_sep : f ((0 : Fin n → ℝ), s₀) < u :=
      hsep _ (subset_closure hs₀)
    have hr_sep : u < f ((0 : Fin n → ℝ), r) := hstrict
    have hs_val : f ((0 : Fin n → ℝ), s₀) = 0 := by
      rw [hprod]
      simp [a, ha_zero]
    have hr_val : f ((0 : Fin n → ℝ), r) = 0 := by
      rw [hprod]
      simp [a, ha_zero]
    linarith
  have ha_pos : 0 < a := by
    refine lt_of_le_of_ne ha_nonneg ?_
    exact Ne.symm ha_ne
  obtain ⟨lam₀, hlam₀⟩ := strongDual_eq_dotProduct_fin ℓ
  let lam : Fin n → ℝ := fun i ↦ lam₀ i / a
  have hlam (x : Fin n → ℝ) : a * (lam ⬝ᵥ x) = ℓ x := by
    -- Normalize the horizontal coefficients by the positive vertical coefficient.
    calc
      a * (lam ⬝ᵥ x) = ∑ i, a * (lam i * x i) := by
        rw [dotProduct, Finset.mul_sum]
      _ = ∑ i, lam₀ i * x i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        dsimp [lam]
        field_simp [ha_ne]
      _ = ℓ x := by
        simpa [dotProduct] using (hlam₀ x).symm
  refine ⟨lam, ?_⟩
  intro p hp
  have hp_sep : f p < u := hsep _ (subset_closure hp)
  have hp_lt : ℓ p.1 + a * p.2 < a * r := by
    calc
      ℓ p.1 + a * p.2 = f p := by simp [hprod]
      _ < u := hp_sep
      _ < f ((0 : Fin n → ℝ), r) := hstrict
      _ = a * r := by
        rw [hprod]
        simp [a]
  have hp_scaled : a * (p.2 + lam ⬝ᵥ p.1) < a * r := by
    calc
      a * (p.2 + lam ⬝ᵥ p.1) = a * p.2 + ℓ p.1 := by
        rw [mul_add, hlam]
      _ = ℓ p.1 + a * p.2 := by ring
      _ < a * r := hp_lt
  have hp_real : p.2 + lam ⬝ᵥ p.1 < r := by
    nlinarith
  exact le_of_lt (by exact_mod_cast hp_real)

/-- Helper for Exercise 8.8: a strict upper threshold on the intersection value yields one
multiplier vector whose convexified split relaxation lies below that threshold. -/
private lemma splitStrictDisplacementHypograph_separator_of_threshold
    (C₁ C₂ : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    (hC₁ : Convex ℝ C₁)
    (hC₂ : Convex ℝ C₂)
    (hfeas : Set.Nonempty (C₁ ∩ C₂))
    (hAclosed : IsClosed (splitDisplacementClosedHypograph C₁ C₂ c))
    {r : ℝ}
    (hr : splitDisplacementValue C₁ C₂ c 0 < (r : EReal)) :
    ∃ lam : Fin n → ℝ,
      ∀ p ∈ splitStrictDisplacementHypograph C₁ C₂ c,
        ((p.2 + lam ⬝ᵥ p.1 : ℝ) : EReal) ≤ (r : EReal) := by
  -- Route correction: isolate the missing step as a threshold-separation statement for the
  -- displacement value itself, instead of forcing the wrapper lemma to upgrade a zero-line
  -- closure exclusion to an ambient closure exclusion.
  let H : Set ((Fin n → ℝ) × ℝ) := splitStrictDisplacementHypograph C₁ C₂ c
  have hH_convex : Convex ℝ H := by
    -- Keep the geometric owner explicit so the remaining blocker is only the threshold separator.
    simpa [H] using splitStrictDisplacementHypographConvex C₁ C₂ c hC₁ hC₂
  have hH_downward :
      ∀ {u : Fin n → ℝ} {t s : ℝ},
        (u, t) ∈ H → s ≤ t → (u, s) ∈ H := by
    intro u t s ht hs
    simpa [H] using splitStrictDisplacementHypograph_downward C₁ C₂ c ht hs
  rcases hfeas with ⟨x₀, hx₀⟩
  have hvertical : ∃ s₀ : ℝ, ((0 : Fin n → ℝ), s₀) ∈ H := by
    refine ⟨c ⬝ᵥ x₀ - 1, ?_⟩
    -- One feasible diagonal point provides the vertical reference ray through displacement `0`.
    have hlt : c ⬝ᵥ x₀ - 1 < c ⬝ᵥ x₀ := by
      linarith
    simpa [H] using
      zero_mem_splitStrictDisplacementHypograph_of_mem_inter C₁ C₂ c hx₀ hlt
  have hH_subset_A :
      H ⊆ splitDisplacementClosedHypograph C₁ C₂ c := by
    -- The strict hypograph embeds into the closed hypograph pointwise.
    simpa [H] using splitStrictDisplacementHypograph_subset_closedHypograph C₁ C₂ c
  have houtside_closure :
      ((0 : Fin n → ℝ), r) ∉ closure H := by
    -- Route correction: use the closed displacement hypograph as the actual closed owner and
    -- push `closure H` into it, instead of comparing zero slices of `closure H`.
    have hclosure_subset :
        closure H ⊆ splitDisplacementClosedHypograph C₁ C₂ c :=
      closure_minimal hH_subset_A hAclosed
    intro hmem
    exact
      zero_not_mem_splitDisplacementClosedHypograph_of_threshold C₁ C₂ c hr
        (hclosure_subset hmem)
  exact strictDisplacementHypographSeparator H hH_convex hH_downward hvertical houtside_closure

/-- Helper for Exercise 8.8: a strict upper threshold on the intersection value yields one
multiplier vector whose convexified split relaxation lies below that threshold. -/
private lemma splitThresholdRelaxationBound
    (C₁ C₂ : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    (hC₁ : Convex ℝ C₁)
    (hC₂ : Convex ℝ C₂)
    (hfeas : Set.Nonempty (C₁ ∩ C₂))
    (hAclosed : IsClosed (splitDisplacementClosedHypograph C₁ C₂ c))
    {r : ℝ}
    (hr :
      sSup ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) '' (C₁ ∩ C₂)) < (r : EReal)) :
    ∃ lam : Fin n → ℝ,
      sSup
          ((fun xy : (Fin n → ℝ) × (Fin n → ℝ) ↦
              ((c ⬝ᵥ xy.1 + lam ⬝ᵥ (xy.2 - xy.1) : ℝ) : EReal)) '' (C₁ ×ˢ C₂)) ≤
        (r : EReal) := by
  have hvalue_lt_r : splitDisplacementValue C₁ C₂ c 0 < (r : EReal) := by
    -- Normalize the source threshold to the displacement-value view at `u = 0`.
    simpa [splitDisplacementValue_zero_eq_intersectionSup C₁ C₂ c] using hr
  rcases
      splitStrictDisplacementHypograph_separator_of_threshold
        C₁ C₂ c hC₁ hC₂ hfeas hAclosed hvalue_lt_r with
    ⟨lam, hlam⟩
  refine ⟨lam, ?_⟩
  refine sSup_le ?_
  rintro _ ⟨xy, hxy, rfl⟩
  by_contra hgt
  have hreal_gt :
      (r : EReal) < ((c ⬝ᵥ xy.1 + lam ⬝ᵥ (xy.2 - xy.1) : ℝ) : EReal) :=
    lt_of_not_ge hgt
  have hobj_gt : r < c ⬝ᵥ xy.1 + lam ⬝ᵥ (xy.2 - xy.1) := by
    exact_mod_cast hreal_gt
  let δ : ℝ := (c ⬝ᵥ xy.1 + lam ⬝ᵥ (xy.2 - xy.1) - r) / 2
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    linarith
  let t : ℝ := c ⬝ᵥ xy.1 - δ
  have ht_mem : ((xy.2 - xy.1), t) ∈ splitStrictDisplacementHypograph C₁ C₂ c := by
    -- Keep the witness explicit here to avoid extra transport while the separator lemma is open.
    refine ⟨xy.1, hxy.1, xy.2, hxy.2, rfl, ?_⟩
    · dsimp [t]
      linarith
  have hbound := hlam ((xy.2 - xy.1), t) ht_mem
  have hgt' : r < t + lam ⬝ᵥ (xy.2 - xy.1) := by
    have ht_eq :
        t + lam ⬝ᵥ (xy.2 - xy.1) =
          (r + (c ⬝ᵥ xy.1 + lam ⬝ᵥ (xy.2 - xy.1))) / 2 := by
      dsimp [t, δ]
      ring
    nlinarith [hobj_gt, ht_eq]
  exact (not_le_of_gt (by exact_mod_cast hgt')) hbound

private lemma splitDualValue_le_splitConvexHullIntersectionValue_of_nonempty
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ)
    (hfeas :
      Set.Nonempty (split_mixed_integer_convex_hull_intersection hp A₁ b₁ A₂ b₂)) :
    split_mixed_integer_lagrangian_dual_value hp A₁ b₁ A₂ b₂ c ≤
      split_mixed_integer_convex_hull_intersection_value hp A₁ b₁ A₂ b₂ c := by
  let C₁ := convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₁ b₁)
  let C₂ := convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₂ b₂)
  have hC₁ : Convex ℝ C₁ := by
    -- The first split block is already convex after passing to its convex hull.
    simpa [C₁] using convex_convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₁ b₁)
  have hC₂ : Convex ℝ C₂ := by
    -- The same convexification step handles the second split block.
    simpa [C₂] using convex_convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₂ b₂)
  have hfeasHull : Set.Nonempty (C₁ ∩ C₂) := by
    -- Rewrite the source nonemptiness into the local convex-hull abbreviations.
    simpa [C₁, C₂, split_mixed_integer_convex_hull_intersection] using hfeas
  have hClosedHypograph :
      IsClosed (splitDisplacementClosedHypograph C₁ C₂ c) := by
    -- TODO: prove this concrete closedness witness from the polyhedral descriptions of
    -- `conv(Q₁)` and `conv(Q₂)`. The generic separator is now correct; only this theorem-local
    -- regularity bridge for the actual convex-hull owners remains.
    sorry
  by_contra hdual
  have hlt :
      split_mixed_integer_convex_hull_intersection_value hp A₁ b₁ A₂ b₂ c <
        split_mixed_integer_lagrangian_dual_value hp A₁ b₁ A₂ b₂ c :=
    lt_of_not_ge hdual
  rcases EReal.lt_iff_exists_real_btwn.mp hlt with ⟨r, hvalue_lt_r, hr_lt_dual⟩
  have hthreshold :
      sSup ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) '' (C₁ ∩ C₂)) < (r : EReal) := by
    -- Rewrite the source value owner into the explicit supremum used by the threshold lemma.
    rw [split_mixed_integer_convex_hull_intersection_value_eq_sSup] at hvalue_lt_r
    simpa [C₁, C₂, split_mixed_integer_convex_hull_intersection] using hvalue_lt_r
  rcases splitThresholdRelaxationBound C₁ C₂ c hC₁ hC₂ hfeasHull hClosedHypograph hthreshold with
    ⟨lam, hlam⟩
  have hrelax_le_r :
      split_mixed_integer_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c lam ≤ (r : EReal) := by
    -- Convert the abstract threshold certificate back to the split relaxation owner.
    rw [splitRelaxationValue_eq_convexifiedProduct]
    simpa [C₁, C₂] using hlam
  have hdual_le_r :
      split_mixed_integer_lagrangian_dual_value hp A₁ b₁ A₂ b₂ c ≤ (r : EReal) := by
    -- The dual value is the infimum over all multiplier relaxations, so one certificate suffices.
    rw [split_mixed_integer_lagrangian_dual_value_eq_sInf]
    have hlam_mem :
        split_mixed_integer_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c lam ∈
          Set.range
            (fun lam' : Fin n → ℝ ↦
              split_mixed_integer_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c lam') :=
      ⟨lam, rfl⟩
    exact (sInf_le hlam_mem).trans hrelax_le_r
  exact (not_le_of_gt hr_lt_dual) hdual_le_r

/-- Exercise 8.8. Let
`Qᵢ := {x ∈ ℤ_+^p × ℝ_+^(n-p) : Aᵢ x ≤ bⁱ}` for `i = 1, 2`. If
`conv(Q₁) ∩ conv(Q₂)` is nonempty, then the optimal value `z̄` of the Lagrangian dual obtained by
dualizing `x - y = 0` in the split formulation equals the canonical Chapter 8 value of maximizing
`c x` over `conv(Q₁) ∩ conv(Q₂)`. -/
theorem split_mixed_integer_lagrangian_dual_value_is_max_on_convex_hull_intersection
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ)
    (hfeas :
      Set.Nonempty (split_mixed_integer_convex_hull_intersection hp A₁ b₁ A₂ b₂)) :
    split_mixed_integer_lagrangian_dual_value hp A₁ b₁ A₂ b₂ c =
      split_mixed_integer_convex_hull_intersection_value hp A₁ b₁ A₂ b₂ c := by
  -- First compare the two values through the convexified split product, then isolate the
  -- remaining strong-duality certificate as the only nontrivial direction.
  refine le_antisymm ?_ ?_
  · exact
      splitDualValue_le_splitConvexHullIntersectionValue_of_nonempty hp A₁ b₁ A₂ b₂ c hfeas
  · exact splitConvexHullIntersectionValue_le_splitDualValue hp A₁ b₁ A₂ b₂ c

end Exercise88
