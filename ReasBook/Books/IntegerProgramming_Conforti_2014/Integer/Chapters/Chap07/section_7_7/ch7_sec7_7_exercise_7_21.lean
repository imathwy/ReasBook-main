import Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_3
import Integer.Chapters.Chap04.section_4_8_1.ch4_sec4_8_1_theorem_4_34

-- Domain sampling for this exercise:
-- * primary domain: mixing inequalities for the mixing hull `P^mix`
-- * core/canonical owner: Chapter 3's `facet_defining_inequality`
-- * source-facing owner reused from Chapter 4: Theorem 4.34's mixing inequalities together with
--   their coefficient/rhs bridge to linear inequalities
-- * source/core/bridge triage: Exercise 7.21 is a facet statement about those already-owned
--   inequalities, so this file keeps only the facet layer

section Exercise721

variable {n : ℕ}

/-- Helper for Exercise 7.21: the coefficient form of mixing inequality `(4.29)` is valid on
`mixingHull b` because Theorem 4.34 identifies `P^mix` with the region cut out by the source
mixing inequalities. -/
lemma mixingInequalityTypeOneCoeff_valid_on_mixingHull
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s) :
    is_valid_inequality
      (mixingHull b)
      (mixingInequalityTypeOneCoeff b s)
      (mixingInequalityTypeOneRhs b s) := by
  intro x hx
  -- Rewrite hull membership through Theorem 4.34, then read off the source `(4.29)` inequality.
  have hxRegion : x ∈ mixingInequalitiesRegion b := by
    simpa [mixingHull_eq_mixing_inequalities_region b] using hx
  exact (mixingInequalityTypeOneCoeff_iff b s hs x).2 ((hxRegion.2.2 s hs).1)

/-- Helper for Exercise 7.21: the coefficient form of mixing inequality `(4.30)` is valid on
`mixingHull b` by the same Theorem 4.34 region description. -/
lemma mixingInequalityTypeTwoCoeff_valid_on_mixingHull
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s) :
    is_valid_inequality
      (mixingHull b)
      (mixingInequalityTypeTwoCoeff b s)
      (mixingInequalityTypeTwoRhs b s) := by
  intro x hx
  -- Rewrite hull membership through Theorem 4.34, then read off the source `(4.30)` inequality.
  have hxRegion : x ∈ mixingInequalitiesRegion b := by
    simpa [mixingHull_eq_mixing_inequalities_region b] using hx
  exact (mixingInequalityTypeTwoCoeff_iff b s hs x).2 ((hxRegion.2.2 s hs).2)

/-- Helper for Exercise 7.21: every mixing fractional part is nonnegative. -/
lemma mixingFractionalPart_nonneg
    (b : Fin n → ℚ) (i : Fin n) :
    0 ≤ mixingFractionalPart b i := by
  -- The Chapter 4 fractional parts are real `Int.fract` values.
  simpa [mixingFractionalPart_eq_fract] using Int.fract_nonneg ((b i : ℚ) : ℝ)

/-- Helper for Exercise 7.21: every member of an admissible sequence has positive fractional part. -/
lemma mixingFractionalPart_pos_of_mem_isMixingIndexSequence
    (b : Fin n → ℚ) :
    ∀ {s : List (Fin n)}, IsMixingIndexSequence b s →
      ∀ {i : Fin n}, i ∈ s → 0 < mixingFractionalPart b i
  | [], hs, i, hi => False.elim hs
  | i0 :: is, hs, i, hi => by
      -- Positivity holds at the head by definition and propagates along the fractional-part chain.
      rcases hs with ⟨hi0_pos, -, hfracChain⟩
      rcases List.mem_cons.mp hi with rfl | hi
      · exact hi0_pos
      · exact lt_trans hi0_pos (hfracChain.rel_cons hi)

/-- Helper for Exercise 7.21: a positive mixing fractional part forces `⌈bᵢ⌉ = ⌊bᵢ⌋ + 1`. -/
lemma ceil_eq_floor_add_one_of_mixingFractionalPart_pos
    (b : Fin n → ℚ) {i : Fin n}
    (hi_pos : 0 < mixingFractionalPart b i) :
    (⌈b i⌉ : ℝ) = (⌊b i⌋ : ℝ) + 1 := by
  -- A positive fractional part means `bᵢ` is not integral, so the ceiling is the next integer.
  have hnot_int : b i ∉ Set.range (fun z : ℤ ↦ (z : ℚ)) := by
    intro hmem
    rcases hmem with ⟨z, hz⟩
    have hz' : ((b i : ℚ) : ℝ) = (z : ℝ) := by
      simpa using congrArg (fun q : ℚ ↦ (q : ℝ)) hz.symm
    have hfract_zero : mixingFractionalPart b i = 0 := by
      rw [mixingFractionalPart_eq_fract, hz']
      simp
    exact (ne_of_gt hi_pos) hfract_zero
  exact_mod_cast (Int.ceil_eq_floor_add_one_iff_notMem (b i)).2 hnot_int

/-- Helper for Exercise 7.21: the canonical slice witness at head level `c` uses the least
integral successor coordinates allowed by the covering inequalities. -/
noncomputable def mixingSliceWitness
    (b : Fin n → ℚ) (c : ℝ) : Fin (n + 1) → ℝ :=
  Fin.cases c (fun i : Fin n ↦ (⌈(b i : ℝ) - c⌉ : ℝ))

/-- Helper for Exercise 7.21: every slice witness with `0 ≤ c < 1` already lies in the mixed set
generating `mixingHull b`. -/
lemma mixingSliceWitness_mem_mixingSet
    (b : Fin n → ℚ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    mixingSliceWitness b c ∈ mixingSet b := by
  -- The slice witness is mixed-integer by construction and satisfies each covering inequality by
  -- the defining ceiling bound.
  rw [mem_mixingSet_iff]
  refine ⟨hc_nonneg, ?_, ?_⟩
  · rw [mem_integerVectors_iff_forall]
    intro i
    refine ⟨⌈(b i : ℝ) - c⌉, ?_⟩
    simp [mixingSliceWitness]
  · intro i
    have hceil : (b i : ℝ) - c ≤ (⌈(b i : ℝ) - c⌉ : ℝ) := by
      exact_mod_cast Int.le_ceil ((b i : ℝ) - c)
    have hcover : (b i : ℝ) ≤ c + (⌈(b i : ℝ) - c⌉ : ℝ) := by
      linarith
    simpa [mixingSliceWitness, add_comm] using hcover

/-- Helper for Exercise 7.21: every slice witness gives a hull point because it is itself a
generator of `conv(mixingSet b)`. -/
lemma mixingSliceWitness_mem_mixingHull
    (b : Fin n → ℚ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    mixingSliceWitness b c ∈ mixingHull b := by
  -- Promote the explicit mixed-set witness into the convex hull.
  simpa [mixingHull] using
    (subset_convexHull ℝ (mixingSet b) (mixingSliceWitness_mem_mixingSet b hc_nonneg hc_lt_one))

/-- Helper for Exercise 7.21: every slice witness belongs to the Chapter 4 region description of
`mixingHull b`, so all public mixing inequalities already apply to it. -/
lemma mixingSliceWitness_mem_mixingInequalitiesRegion
    (b : Fin n → ℚ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    mixingSliceWitness b c ∈ mixingInequalitiesRegion b := by
  -- Transport the explicit hull point through Theorem 4.34's region description.
  simpa [mixingHull_eq_mixing_inequalities_region b] using
    mixingSliceWitness_mem_mixingHull b hc_nonneg hc_lt_one

/-- Helper for Exercise 7.21: at a slice witness, each shifted successor coordinate is either the
floor branch `0` or the ceiling branch `1` depending on the breakpoint test `fᵢ ≤ c`. -/
lemma mixingSliceWitness_shiftProfile
    (b : Fin n → ℚ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) (i : Fin n) :
    mixingSliceWitness b c i.succ - (⌊b i⌋ : ℝ) =
      if mixingFractionalPart b i ≤ c then 0 else 1 := by
  -- Normalize the slice coordinate with the public floor/ceiling breakpoint lemma.
  have hcoord :
      mixingSliceWitness b c i.succ =
        if mixingFractionalPart b i ≤ c then (⌊b i⌋ : ℝ) else (⌈b i⌉ : ℝ) := by
    simp [mixingSliceWitness, ceil_sub_eq_floor_or_ceil_by_fract hc_nonneg hc_lt_one i]
  rw [hcoord]
  by_cases hfi : mixingFractionalPart b i ≤ c
  · rw [if_pos hfi]
    simpa [mixingFractionalPart_eq_fract] using hfi
  · rw [if_neg hfi]
    have hfi_ne_zero : mixingFractionalPart b i ≠ 0 := by
      intro hzero
      apply hfi
      rw [hzero]
      exact hc_nonneg
    have hfi_pos : 0 < mixingFractionalPart b i := by
      exact lt_of_le_of_ne (mixingFractionalPart_nonneg b i) hfi_ne_zero.symm
    rw [ceil_eq_floor_add_one_of_mixingFractionalPart_pos b hfi_pos]
    simpa [mixingFractionalPart_eq_fract] using (lt_of_not_ge hfi)

/-- Helper for Exercise 7.21: the slice profile collapses to the floor branch when the breakpoint
is already reached. -/
lemma mixingSliceWitness_shiftProfile_of_le
    (b : Fin n → ℚ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) {i : Fin n}
    (hfi : mixingFractionalPart b i ≤ c) :
    mixingSliceWitness b c i.succ - (⌊b i⌋ : ℝ) = 0 := by
  -- Route correction: record the `≤` branch as a standalone rewrite lemma instead of repeatedly
  -- rewriting inside the `if` returned by `mixingSliceWitness_shiftProfile`.
  rw [mixingSliceWitness_shiftProfile b hc_nonneg hc_lt_one i, if_pos hfi]

/-- Helper for Exercise 7.21: the slice profile collapses to the ceiling branch when the
breakpoint is still ahead. -/
lemma mixingSliceWitness_shiftProfile_of_lt
    (b : Fin n → ℚ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) {i : Fin n}
    (hfi : c < mixingFractionalPart b i) :
    mixingSliceWitness b c i.succ - (⌊b i⌋ : ℝ) = 1 := by
  -- Route correction: record the strict branch once so later telescoping proofs can rewrite
  -- directly to `1` instead of reopening the `if` expression.
  rw [mixingSliceWitness_shiftProfile b hc_nonneg hc_lt_one i, if_neg (not_le.mpr hfi)]

/-- Helper for Exercise 7.21: adding the head ray `r⁰` to a mixed-set point preserves the
mixed-integer constraints. -/
lemma mixingSet_add_headRay_mem
    (b : Fin n → ℚ) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingSet b) :
    x + exercise_3_29_ray (0 : Fin (n + 1)) ∈ mixingSet b := by
  rw [mem_mixingSet_iff] at hx ⊢
  rcases hx with ⟨hx0_nonneg, htail, hcover⟩
  refine ⟨?_, ?_, ?_⟩
  · -- The head coordinate increases by one.
    have hhead : (x + exercise_3_29_ray (0 : Fin (n + 1))) 0 = x 0 + 1 := by
      simp [exercise_3_29_ray_apply]
    rw [hhead]
    linarith
  · -- Each tail coordinate decreases by one and remains integral.
    rw [mem_integerVectors_iff_forall] at htail ⊢
    intro t
    rcases htail t with ⟨m, hm⟩
    refine ⟨m - 1, ?_⟩
    simp [exercise_3_29_ray_apply, hm, sub_eq_add_neg]
  · -- The covering sums stay unchanged under the head ray.
    intro t
    have ht := hcover t
    have hmixed :
        (x + exercise_3_29_ray (0 : Fin (n + 1))) 0 +
            (x + exercise_3_29_ray (0 : Fin (n + 1))) t.succ =
          x 0 + x t.succ := by
      simp [exercise_3_29_ray_apply, sub_eq_add_neg]
      ring
    rw [hmixed]
    exact ht

/-- Helper for Exercise 7.21: the head-ray translation extends from generators to all of
`mixingHull b` by convexity. -/
lemma mixingHull_add_headRay_mem
    (b : Fin n → ℚ) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingHull b) :
    x + exercise_3_29_ray (0 : Fin (n + 1)) ∈ mixingHull b := by
  -- Transport the generator-level head-ray move through the convex hull.
  let r : Fin (n + 1) → ℝ := exercise_3_29_ray (0 : Fin (n + 1))
  let translated : Set (Fin (n + 1) → ℝ) := {y | y + r ∈ mixingHull b}
  have hsubset : mixingSet b ⊆ translated := by
    intro y hy
    change y + r ∈ mixingHull b
    exact subset_convexHull ℝ (mixingSet b) (mixingSet_add_headRay_mem b hy)
  have hconv : Convex ℝ translated := by
    intro y hy z hz a c ha hc hac
    change a • y + c • z + r ∈ mixingHull b
    have hcomb :
        a • (y + r) + c • (z + r) ∈ mixingHull b :=
      (convex_convexHull ℝ (mixingSet b)) hy hz ha hc hac
    have hrewrite :
        a • (y + r) + c • (z + r) = a • y + c • z + r := by
      ext j
      calc
        a * (y j + r j) + c * (z j + r j)
            = a * y j + c * z j + (a + c) * r j := by
                ring
        _ = a * y j + c * z j + r j := by
              rw [hac, one_mul]
        _ = (a • y + c • z + r) j := by
              simp [Pi.add_apply, Pi.smul_apply]
    rw [← hrewrite]
    exact hcomb
  have hxHull : x ∈ convexHull ℝ (mixingSet b) := by
    simpa [mixingHull] using hx
  exact convexHull_min hsubset hconv hxHull

/-- Helper for Exercise 7.21: every successor Exercise 3.29 ray also preserves `mixingHull b`
because Proposition 4.33 already preserves the generators. -/
lemma mixingHull_add_successorRay_mem
    (b : Fin n → ℚ) {x : Fin (n + 1) → ℝ} (i : Fin n)
    (hx : x ∈ mixingHull b) :
    x + exercise_3_29_ray i.succ ∈ mixingHull b := by
  -- Push the generator-level successor translation through the convex hull exactly as for `r⁰`.
  let r : Fin (n + 1) → ℝ := exercise_3_29_ray i.succ
  let translated : Set (Fin (n + 1) → ℝ) := {y | y + r ∈ mixingHull b}
  have hsubset : mixingSet b ⊆ translated := by
    intro y hy
    change y + r ∈ mixingHull b
    exact subset_convexHull ℝ (mixingSet b) (mixingSet_add_successor_ray_mem hy i)
  have hconv : Convex ℝ translated := by
    intro y hy z hz a c ha hc hac
    change a • y + c • z + r ∈ mixingHull b
    have hcomb :
        a • (y + r) + c • (z + r) ∈ mixingHull b :=
      (convex_convexHull ℝ (mixingSet b)) hy hz ha hc hac
    have hrewrite :
        a • (y + r) + c • (z + r) = a • y + c • z + r := by
      ext j
      calc
        a * (y j + r j) + c * (z j + r j)
            = a * y j + c * z j + (a + c) * r j := by
                ring
        _ = a * y j + c * z j + r j := by
              rw [hac, one_mul]
        _ = (a • y + c • z + r) j := by
              simp [Pi.add_apply, Pi.smul_apply]
    rw [← hrewrite]
    exact hcomb
  have hxHull : x ∈ convexHull ℝ (mixingSet b) := by
    simpa [mixingHull] using hx
  exact convexHull_min hsubset hconv hxHull

/-- Helper for Exercise 7.21: two points on the same equality face have zero dot product against
the exposing vector after subtraction. -/
lemma faceSet_dot_sub_eq_zero_of_two_mem
    {P : Set (Fin (n + 1) → ℝ)} {d x y : Fin (n + 1) → ℝ} {ε : ℝ}
    (hx : x ∈ face_set P d ε) (hy : y ∈ face_set P d ε) :
    d ⬝ᵥ (x - y) = 0 := by
  -- Unpack the two face equalities and subtract them once instead of repeating this algebra.
  have hx_eq : d ⬝ᵥ x = ε := (mem_face_set_iff.mp hx).2
  have hy_eq : d ⬝ᵥ y = ε := (mem_face_set_iff.mp hy).2
  rw [dotProduct_sub, hx_eq, hy_eq]
  simp

/-- Helper for Exercise 7.21: multiplying a defining inequality by a nonzero scalar does not
change its equality face. -/
lemma faceSet_eq_of_nonzero_smul
    {P : Set (Fin (n + 1) → ℝ)} {c : Fin (n + 1) → ℝ} {δ lam : ℝ}
    (hlam : lam ≠ 0) :
    face_set P (lam • c) (lam * δ) = face_set P c δ := by
  ext x
  rw [mem_face_set_iff, mem_face_set_iff]
  constructor
  · rintro ⟨hxP, hxEq⟩
    refine ⟨hxP, ?_⟩
    have hscaled : lam * (c ⬝ᵥ x) = lam * δ := by
      calc
        lam * (c ⬝ᵥ x) = (lam • c) ⬝ᵥ x := by
          simpa [smul_eq_mul] using (smul_dotProduct lam c x).symm
        _ = lam * δ := hxEq
    exact mul_left_cancel₀ hlam hscaled
  · rintro ⟨hxP, hxEq⟩
    refine ⟨hxP, ?_⟩
    calc
      (lam • c) ⬝ᵥ x = lam * (c ⬝ᵥ x) := by
        simpa [smul_eq_mul] using (smul_dotProduct lam c x)
      _ = lam * δ := by rw [hxEq]

/-- Helper for Exercise 7.21: the zero-level slice witness is tight for the source mixing
inequality `(4.29)`. -/
lemma mixingInequalityTypeOne_on_sliceWitness_zero
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s) :
    mixingInequalityTypeOne b s (mixingSliceWitness b 0) := by
  -- The zero-level slice witness already lies in the Chapter 4 region description of `mixingHull`.
  have hwitness :
      mixingSliceWitness b 0 ∈ mixingInequalitiesRegion b :=
    mixingSliceWitness_mem_mixingInequalitiesRegion b (show 0 ≤ (0 : ℝ) by simp)
      (show (0 : ℝ) < 1 by norm_num)
  exact (hwitness.2.2 s hs).1

/-- Helper for Exercise 7.21: the slice witness at the first selected fractional part is tight for
the source mixing inequality `(4.30)`. -/
lemma mixingInequalityTypeTwo_on_firstSliceWitness
    (b : Fin n → ℚ) (first : Fin n) (tail : List (Fin n))
    (hs : IsMixingIndexSequence b (first :: tail)) :
    mixingInequalityTypeTwo b (first :: tail)
      (mixingSliceWitness b (mixingFractionalPart b first)) := by
  -- The first-breakpoint slice witness is another hull generator, so the source inequality holds
  -- directly from the region description.
  have hfrac_nonneg : 0 ≤ mixingFractionalPart b first :=
    mixingFractionalPart_nonneg b first
  have hfrac_lt_one : mixingFractionalPart b first < 1 := by
    rw [mixingFractionalPart_eq_fract]
    exact Int.fract_lt_one (((b first : ℚ) : ℝ))
  have hwitness :
      mixingSliceWitness b (mixingFractionalPart b first) ∈ mixingInequalitiesRegion b :=
    mixingSliceWitness_mem_mixingInequalitiesRegion b hfrac_nonneg hfrac_lt_one
  exact (hwitness.2.2 (first :: tail) hs).2

/-- Helper for Exercise 7.21: the recursive floor contribution in Chapter 4's shifted normal form
for the mixing inequalities. -/
private noncomputable def chap4MixingInequalityFloorSumAux
    (b : Fin n → ℚ) : ℝ → List (Fin n) → ℝ
  | _, [] => 0
  | prev, i :: is =>
      let fi := mixingFractionalPart b i
      (fi - prev) * (⌊b i⌋ : ℝ) + chap4MixingInequalityFloorSumAux b fi is

/-- Helper for Exercise 7.21: the accumulated floor contribution in Chapter 4's shifted normal
form for the mixing inequalities. -/
private noncomputable def chap4MixingInequalityFloorSum
    (b : Fin n → ℚ) (s : List (Fin n)) : ℝ :=
  chap4MixingInequalityFloorSumAux b 0 s

/-- Helper for Exercise 7.21: the recursive raw selected-coordinate sum before the floor-shift
constants move to the right-hand side. -/
private noncomputable def chap4MixingInequalityTypeOneRawSumAux
    (b : Fin n → ℚ) (x : Fin (n + 1) → ℝ) : ℝ → List (Fin n) → ℝ
  | _, [] => 0
  | prev, i :: is =>
      let fi := mixingFractionalPart b i
      (fi - prev) * x i.succ + chap4MixingInequalityTypeOneRawSumAux b x fi is

/-- Helper for Exercise 7.21: the recursive shifted-coordinate sum for the left-hand side of
mixing inequality `(4.29)`. -/
private noncomputable def chap4MixingInequalityTypeOneSumAux
    (b : Fin n → ℚ) (x : Fin (n + 1) → ℝ) : ℝ → List (Fin n) → ℝ
  | _, [] => 0
  | prev, i :: is =>
      let fi := mixingFractionalPart b i
      (fi - prev) * (x i.succ - (⌊b i⌋ : ℝ)) + chap4MixingInequalityTypeOneSumAux b x fi is

/-- Helper for Exercise 7.21: the local shifted-coordinate sum for mixing inequality `(4.29)`. -/
private noncomputable def chap4MixingInequalityTypeOneSum
    (b : Fin n → ℚ) (s : List (Fin n)) (x : Fin (n + 1) → ℝ) : ℝ :=
  chap4MixingInequalityTypeOneSumAux b x 0 s

/-- Helper for Exercise 7.21: the recursive coefficient contribution in Chapter 4's linear form
for mixing inequality `(4.29)`. -/
private noncomputable def chap4MixingInequalityTypeOneCoeffAux
    (b : Fin n → ℚ) : ℝ → List (Fin n) → Fin (n + 1) → ℝ
  | _, [] => fun _ ↦ 0
  | prev, i :: is =>
      fun j ↦
        (if j = i.succ then -(mixingFractionalPart b i - prev) else 0) +
          chap4MixingInequalityTypeOneCoeffAux b (mixingFractionalPart b i) is j

/-- Helper for Exercise 7.21: the local recursive coefficient vector for `(4.29)` evaluates to
the negative of the raw selected-coordinate sum. -/
private lemma chap4MixingInequalityTypeOneCoeffAux_dotProduct
    (b : Fin n → ℚ) (x : Fin (n + 1) → ℝ) :
    ∀ prev : ℝ, ∀ s : List (Fin n),
      chap4MixingInequalityTypeOneCoeffAux b prev s ⬝ᵥ x =
        -chap4MixingInequalityTypeOneRawSumAux b x prev s
  | prev, [] => by
      -- TODO: recover the exact Chapter 4 recursion proof once the local coefficient bridge is
      -- restated in the same normal form as the source private helper.
      sorry
  | prev, i :: is => by
      -- TODO: split the singleton coordinate and tail dot products using the source-shape helper
      -- `single_coordinate_dotProduct` after the coefficient bridge is stabilized.
      sorry

/-- Helper for Exercise 7.21: a single-coordinate vector evaluates to the expected scalar
multiple of that coordinate. -/
private lemma single_coordinate_dotProduct
    {m : ℕ} (j : Fin m) (c : ℝ) (x : Fin m → ℝ) :
    (fun k : Fin m ↦ if k = j then c else 0) ⬝ᵥ x = c * x j := by
  -- Collapse the finite dot product to its unique nonzero coordinate.
  rw [dotProduct, Fintype.sum_eq_single j]
  · simp
  · intro k hk
    simp [hk]

/-- Helper for Exercise 7.21: a successor Exercise 3.29 ray pairs with a coefficient vector by
reading off the matching successor coordinate. -/
lemma dotProduct_exercise_3_29_ray_succ
    (c : Fin (n + 1) → ℝ) (i : Fin n) :
    c ⬝ᵥ exercise_3_29_ray i.succ = c i.succ := by
  have hray :
      exercise_3_29_ray i.succ =
        (fun j : Fin (n + 1) ↦ if j = i.succ then 1 else 0) := by
    ext j
    have hsucc_ne_zero : (i.succ : Fin (n + 1)) ≠ 0 := by
      simp
    simp [exercise_3_29_ray_apply, hsucc_ne_zero]
  rw [hray, dotProduct_comm, single_coordinate_dotProduct]
  simp

/-- Helper for Exercise 7.21: the head Exercise 3.29 ray pairs with a coefficient vector by
subtracting the successor coordinates from the head coordinate. -/
lemma dotProduct_exercise_3_29_ray_zero
    (c : Fin (n + 1) → ℝ) :
    c ⬝ᵥ exercise_3_29_ray (0 : Fin (n + 1)) = c 0 - ∑ i : Fin n, c i.succ := by
  rw [dotProduct, Fin.sum_univ_succ]
  simp [exercise_3_29_ray_apply]
  ring

/-- Helper for Exercise 7.21: the recursive coefficient vector for `(4.29)` vanishes at every
successor coordinate whose index does not belong to the selected list. -/
lemma chap4MixingInequalityTypeOneCoeffAux_eq_zero_of_not_mem
    (b : Fin n → ℚ) :
    ∀ {prev : ℝ} {s : List (Fin n)} {i : Fin n},
      i ∉ s →
      chap4MixingInequalityTypeOneCoeffAux b prev s i.succ = 0
  | _, [], _, _ => by
      simp [chap4MixingInequalityTypeOneCoeffAux]
  | prev, j :: js, i, hi => by
      have hij : i ≠ j := by
        intro hEq
        exact hi (by simp [hEq])
      have hsucc_ne : i.succ ≠ j.succ := fun hEq ↦ hij (by simpa using hEq)
      have htail : i ∉ js := by
        intro hmem
        exact hi (by simp [hmem])
      simp [chap4MixingInequalityTypeOneCoeffAux, hsucc_ne]
      exact chap4MixingInequalityTypeOneCoeffAux_eq_zero_of_not_mem b htail

/-- Helper for Exercise 7.21: Chapter 4 already identifies the raw left-hand side with the
shifted sum plus the accumulated floor contribution. -/
private lemma chap4MixingInequalityTypeOneRawSum_eq_shifted_add_floor
    (b : Fin n → ℚ) (x : Fin (n + 1) → ℝ) (s : List (Fin n)) :
    chap4MixingInequalityTypeOneRawSumAux b x 0 s =
      chap4MixingInequalityTypeOneSum b s x + chap4MixingInequalityFloorSum b s := by
  -- Split each selected coordinate into its shifted part plus the floor contribution.
  have haux :
      ∀ prev : ℝ, ∀ t : List (Fin n),
        chap4MixingInequalityTypeOneRawSumAux b x prev t =
          chap4MixingInequalityTypeOneSumAux b x prev t + chap4MixingInequalityFloorSumAux b prev t := by
    intro prev t
    induction t generalizing prev with
    | nil =>
        simp [chap4MixingInequalityTypeOneRawSumAux, chap4MixingInequalityTypeOneSumAux,
          chap4MixingInequalityFloorSumAux]
    | cons i is ih =>
        rw [chap4MixingInequalityTypeOneRawSumAux, chap4MixingInequalityTypeOneSumAux,
          chap4MixingInequalityFloorSumAux, ih]
        ring
  simpa [chap4MixingInequalityTypeOneSum, chap4MixingInequalityFloorSum] using haux 0 s

/-- Helper for Exercise 7.21: Chapter 4's exact dot-product formula for the coefficient vector of
`(4.29)`. -/
private lemma chap4MixingInequalityTypeOneCoeff_dotProduct
    (b : Fin n → ℚ) (s : List (Fin n)) (x : Fin (n + 1) → ℝ) :
    mixingInequalityTypeOneCoeff b s ⬝ᵥ x =
      -(x 0 + chap4MixingInequalityTypeOneRawSumAux b x 0 s) := by
  -- TODO: replace the failed definitional `change` step with an explicit equality between the
  -- imported public coefficient vector and the local Chapter 4 clone.
  sorry

/-- Helper for Exercise 7.21: Chapter 4's exact dot-product formula for the coefficient vector of
`(4.30)` once the first and last selected indices are fixed. -/
private lemma chap4MixingInequalityTypeTwoCoeff_dotProduct_of_reverse
    (b : Fin n → ℚ) (first last : Fin n) (tail revTail : List (Fin n))
    (hrev : (first :: tail).reverse = last :: revTail) (x : Fin (n + 1) → ℝ) :
    mixingInequalityTypeTwoCoeff b (first :: tail) ⬝ᵥ x =
      -(x 0 + chap4MixingInequalityTypeOneRawSumAux b x 0 (first :: tail) +
        (1 - mixingFractionalPart b last) * x first.succ) := by
  -- TODO: once the type-one coefficient bridge is repaired, add the extra first-coordinate term
  -- exactly as in the Chapter 4 source proof.
  sorry

/-- Helper for Exercise 7.21: on successor coordinates, the public coefficient vector for
`(4.29)` agrees with the local recursive coefficient copy. -/
private lemma mixingInequalityTypeOneCoeff_apply_succ
    (b : Fin n → ℚ) (s : List (Fin n)) (i : Fin n) :
    mixingInequalityTypeOneCoeff b s i.succ =
      chap4MixingInequalityTypeOneCoeffAux b 0 s i.succ := by
  -- TODO: prove this by evaluating both sides against the successor ray after the type-one
  -- dot-product bridge is repaired.
  sorry

/-- Helper for Exercise 7.21: target-face membership for `(4.29)` is exactly hull membership plus
equality in the source scalar form of the mixing inequality. -/
lemma mem_mixingInequalityTypeOne_face_iff
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s)
    (x : Fin (n + 1) → ℝ) :
    x ∈ face_set
        (mixingHull b)
        (mixingInequalityTypeOneCoeff b s)
        (mixingInequalityTypeOneRhs b s) ↔
      x ∈ mixingHull b ∧
        match s.reverse with
        | [] => False
        | last :: _ =>
            mixingFractionalPart b last = x 0 + chap4MixingInequalityTypeOneSum b s x := by
  -- TODO: replace this raw `match s.reverse` interface by an `_of_reverse` adapter so later
  -- face-transport lemmas can rewrite against an explicit last index.
  sorry

/-- Helper for Exercise 7.21: target-face membership for `(4.30)` is exactly hull membership plus
equality in the source scalar form of the mixing inequality. -/
lemma mem_mixingInequalityTypeTwo_face_iff
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s)
    (x : Fin (n + 1) → ℝ) :
    x ∈ face_set
        (mixingHull b)
        (mixingInequalityTypeTwoCoeff b s)
        (mixingInequalityTypeTwoRhs b s) ↔
      x ∈ mixingHull b ∧
        match s, s.reverse with
        | first :: _, last :: _ =>
            mixingFractionalPart b last =
              x 0 + chap4MixingInequalityTypeOneSum b s x +
                (1 - mixingFractionalPart b last) * (x first.succ - (⌊b first⌋ : ℝ))
        | _, _ => False := by
  -- TODO: restate this as a fixed-shape reverse lemma so the first/last indices are parameters
  -- rather than hidden in a nested `match`.
  sorry

/-- Helper for Exercise 7.21: along a strictly increasing fractional-part chain, every tail
member has fractional part at least that of the head. -/
lemma mixingFractionalPart_le_of_mem_chain
    (b : Fin n → ℚ) {i : Fin n} {is : List (Fin n)}
    (hchain : (i :: is).IsChain (fun j k ↦ mixingFractionalPart b j < mixingFractionalPart b k))
    {j : Fin n} (hj : j ∈ is) :
    mixingFractionalPart b i ≤ mixingFractionalPart b j := by
  exact le_of_lt (hchain.rel_cons hj)

/-- Helper for Exercise 7.21: if every selected fractional part lies strictly above `c`, then the
slice witness at `c` makes the shifted type-one sum telescope to the last fractional part minus the
incoming base level. -/
lemma mixingInequalityTypeOneSumAux_eq_last_sub_prev_of_all_gt
    (b : Fin n → ℚ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    ∀ {prev : ℝ} {s : List (Fin n)},
      (∀ j ∈ s, c < mixingFractionalPart b j) →
      s.IsChain (fun j k ↦ mixingFractionalPart b j < mixingFractionalPart b k) →
      chap4MixingInequalityTypeOneSumAux b (mixingSliceWitness b c) prev s =
        match s.reverse with
        | [] => 0
        | last :: _ => mixingFractionalPart b last - prev
  | prev, [], hgt, hchain => by
      -- TODO: replay the Chapter 4 telescoping argument using the branch lemmas
      -- `mixingSliceWitness_shiftProfile_of_le` and `_of_lt`.
      sorry
  | prev, [i], hgt, hchain => by
      -- TODO: normalize the singleton branch directly to `1` via
      -- `mixingSliceWitness_shiftProfile_of_lt`.
      sorry
  | prev, i :: j :: is, hgt, hchain => by
      -- TODO: recurse on the tail after replacing all `if` rewrites by the new branch lemmas.
      sorry

/-- Helper for Exercise 7.21: at the slice level determined by a selected fractional part, the
shifted type-one sum telescopes to the last fractional part minus that selected level. -/
lemma mixingInequalityTypeOneSumAux_eq_last_sub_target_of_mem
    (b : Fin n → ℚ) {i : Fin n} {s : List (Fin n)}
    (hchain : s.IsChain (fun j k ↦ mixingFractionalPart b j < mixingFractionalPart b k))
    (hi : i ∈ s) :
    ∀ {prev : ℝ}, prev ≤ mixingFractionalPart b i →
      chap4MixingInequalityTypeOneSumAux b
          (mixingSliceWitness b (mixingFractionalPart b i)) prev s =
        match s.reverse with
        | [] => 0
        | last :: _ => mixingFractionalPart b last - mixingFractionalPart b i
  | prev, hprev_le => by
      -- TODO: separate the head-selected and tail-selected cases using the new fixed branch
      -- normalization lemmas instead of rewriting raw `if` expressions.
      sorry

/-- Helper for Exercise 7.21: the slice witness at any selected fractional part lies on the face
of mixing inequality `(4.29)`. -/
lemma mixingSliceWitness_mem_mixingInequalityTypeOne_face_of_mem
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s)
    {i : Fin n} (hi : i ∈ s) :
    mixingSliceWitness b (mixingFractionalPart b i) ∈
      face_set (mixingHull b) (mixingInequalityTypeOneCoeff b s) (mixingInequalityTypeOneRhs b s) := by
  -- TODO: consume the future `_of_reverse` face adapter after the fixed-shape reverse interface
  -- replaces the current raw `match s.reverse` statement.
  sorry

/-- Helper for Exercise 7.21: the zero-level slice witness lies on the face of mixing inequality
`(4.29)`. -/
lemma mixingSliceWitness_zero_mem_mixingInequalityTypeOne_face
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s) :
    mixingSliceWitness b 0 ∈
      face_set (mixingHull b) (mixingInequalityTypeOneCoeff b s) (mixingInequalityTypeOneRhs b s) := by
  -- TODO: specialize the previous witness-on-face lemma to the zero slice once the telescoping
  -- sum lemma is restated through the branch-normalized interface.
  sorry

/-- Helper for Exercise 7.21: the slice witness at any selected fractional part lies on the face
of mixing inequality `(4.30)`. -/
lemma mixingSliceWitness_mem_mixingInequalityTypeTwo_face_of_mem
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s)
    {i : Fin n} (hi : i ∈ s) :
    mixingSliceWitness b (mixingFractionalPart b i) ∈
      face_set (mixingHull b) (mixingInequalityTypeTwoCoeff b s) (mixingInequalityTypeTwoRhs b s) := by
  -- TODO: reprove the type-two witness statement against the fixed-shape reverse adapter and the
  -- branch lemma `mixingSliceWitness_shiftProfile_of_le`.
  sorry

/-- Helper for Exercise 7.21: a successor ray outside the selected sequence leaves the shifted
type-one sum unchanged. -/
lemma mixingInequalityTypeOneSum_add_nonselected_successorRay
    (b : Fin n → ℚ) (s : List (Fin n)) (x : Fin (n + 1) → ℝ) {i : Fin n}
    (hi : i ∉ s) :
    chap4MixingInequalityTypeOneSum b s (x + exercise_3_29_ray i.succ) =
      chap4MixingInequalityTypeOneSum b s x := by
  -- TODO: reopen this recursion once the face-interface blocker is cleared; the arithmetic here is
  -- local but downstream lemmas currently depend on the fixed-shape reverse refactor.
  sorry

/-- Helper for Exercise 7.21: a successor ray outside the selected sequence stays inside the face
of mixing inequality `(4.29)`. -/
lemma mixingInequalityTypeOneFace_add_nonselected_successorRay_mem
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s)
    {x : Fin (n + 1) → ℝ} {i : Fin n}
    (hx : x ∈ face_set (mixingHull b) (mixingInequalityTypeOneCoeff b s) (mixingInequalityTypeOneRhs b s))
    (hi : i ∉ s) :
    x + exercise_3_29_ray i.succ ∈
      face_set (mixingHull b) (mixingInequalityTypeOneCoeff b s) (mixingInequalityTypeOneRhs b s) := by
  -- TODO: consume the future `_of_reverse` type-one face adapter here.
  sorry

/-- Helper for Exercise 7.21: a successor ray outside the selected sequence stays inside the face
of mixing inequality `(4.30)`. -/
lemma mixingInequalityTypeTwoFace_add_nonselected_successorRay_mem
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s)
    {x : Fin (n + 1) → ℝ} {i : Fin n}
    (hx : x ∈ face_set (mixingHull b) (mixingInequalityTypeTwoCoeff b s) (mixingInequalityTypeTwoRhs b s))
    (hi : i ∉ s) :
    x + exercise_3_29_ray i.succ ∈
      face_set (mixingHull b) (mixingInequalityTypeTwoCoeff b s) (mixingInequalityTypeTwoRhs b s) := by
  -- TODO: consume the future `_of_reverse` type-two face adapter here.
  sorry

/-- Helper for Exercise 7.21: translating by the head ray changes the shifted type-one sum by the
incoming base level minus the last selected fractional part. -/
lemma mixingInequalityTypeOneSumAux_add_headRay
    (b : Fin n → ℚ) (x : Fin (n + 1) → ℝ) :
    ∀ prev : ℝ, ∀ s : List (Fin n),
      chap4MixingInequalityTypeOneSumAux b (x + exercise_3_29_ray (0 : Fin (n + 1))) prev s =
        chap4MixingInequalityTypeOneSumAux b x prev s +
          match s.reverse with
          | [] => 0
          | last :: _ => prev - mixingFractionalPart b last
  | prev, [] => by
      -- TODO: keep this as the base case once the recursive head-ray transport is rebuilt.
      sorry
  | prev, i :: is => by
      -- TODO: isolate the head-ray coordinate rewrite in a small helper and then recurse.
      sorry

/-- Helper for Exercise 7.21: translating by the head ray subtracts the last selected fractional
part from the shifted type-one sum. -/
lemma mixingInequalityTypeOneSum_add_headRay
    (b : Fin n → ℚ) (s : List (Fin n)) (x : Fin (n + 1) → ℝ) :
    chap4MixingInequalityTypeOneSum b s (x + exercise_3_29_ray (0 : Fin (n + 1))) =
      chap4MixingInequalityTypeOneSum b s x +
        match s.reverse with
        | [] => 0
        | last :: _ => -mixingFractionalPart b last := by
  -- TODO: specialize the repaired auxiliary head-ray recursion at `prev = 0`.
  sorry

/-- Helper for Exercise 7.21: translating by the head ray stays inside the face of mixing
inequality `(4.30)`. -/
lemma mixingInequalityTypeTwoFace_add_headRay_mem
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s)
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ face_set (mixingHull b) (mixingInequalityTypeTwoCoeff b s) (mixingInequalityTypeTwoRhs b s)) :
    x + exercise_3_29_ray (0 : Fin (n + 1)) ∈
      face_set (mixingHull b) (mixingInequalityTypeTwoCoeff b s) (mixingInequalityTypeTwoRhs b s) := by
  -- TODO: rebuild this translation lemma after introducing the fixed-shape type-two face adapter.
  sorry

/-- Helper for Exercise 7.21: any proper face containing the equality set of mixing inequality
`(4.29)` already equals that face. -/
lemma mixingInequalityTypeOne_face_eq_of_subset_proper_face
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s)
    {G : Set (Fin (n + 1) → ℝ)}
    (hG : is_proper_face (mixingHull b) G)
    (hsubset :
      face_set
          (mixingHull b)
          (mixingInequalityTypeOneCoeff b s)
          (mixingInequalityTypeOneRhs b s) ⊆
        G) :
    G =
      face_set
        (mixingHull b)
        (mixingInequalityTypeOneCoeff b s)
        (mixingInequalityTypeOneRhs b s) := by
  -- TODO: the remaining blocker is the proportionality argument over the repaired type-one face
  -- interface; keep the file compiling while that structural refactor is replanned.
  sorry


/-- Exercise 7.21 (1). For every admissible index sequence
`1 ≤ i₁ < ⋯ < i_m ≤ n` with `0 < f_{i₁} < ⋯ < f_{i_m}`, the mixing inequality `(4.29)`
defines a facet of `P^mix`. -/
theorem exercise_7_21_mixing_inequality_4_29_facet_defining
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s) :
    facet_defining_inequality
      (mixingHull b)
      (mixingInequalityTypeOneCoeff b s)
      (mixingInequalityTypeOneRhs b s) := by
  -- TODO: reassemble the type-one facet proof once the maximality lemma is rebuilt against the
  -- fixed-shape reverse interface.
  sorry

/-- Helper for Exercise 7.21: the zero-level slice witness satisfies the type-two inequality
strictly, so it does not lie on the equality face of `(4.30)`. -/
lemma mixingSliceWitness_zero_not_mem_mixingInequalityTypeTwo_face
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s) :
    mixingSliceWitness b 0 ∉
      face_set (mixingHull b) (mixingInequalityTypeTwoCoeff b s) (mixingInequalityTypeTwoRhs b s) := by
  -- TODO: show the zero slice is strict for type two after the fixed-shape reverse adapter lands.
  sorry

/-- Helper for Exercise 7.21: any proper face containing the equality set of mixing inequality
`(4.30)` already equals that face. -/
lemma mixingInequalityTypeTwo_face_eq_of_subset_proper_face
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s)
    {G : Set (Fin (n + 1) → ℝ)}
    (hG : is_proper_face (mixingHull b) G)
    (hsubset :
      face_set
          (mixingHull b)
          (mixingInequalityTypeTwoCoeff b s)
          (mixingInequalityTypeTwoRhs b s) ⊆
        G) :
    G =
      face_set
        (mixingHull b)
        (mixingInequalityTypeTwoCoeff b s)
        (mixingInequalityTypeTwoRhs b s) := by
  -- TODO: the remaining blocker is the type-two proportionality endgame after the reverse
  -- interface refactor; keep the file compiling while that route is replanned.
  sorry

/-- Exercise 7.21 (2). For every admissible index sequence
`1 ≤ i₁ < ⋯ < i_m ≤ n` with `0 < f_{i₁} < ⋯ < f_{i_m}`, the mixing inequality `(4.30)`
defines a facet of `P^mix`. -/
theorem exercise_7_21_mixing_inequality_4_30_facet_defining
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s) :
    facet_defining_inequality
      (mixingHull b)
      (mixingInequalityTypeTwoCoeff b s)
      (mixingInequalityTypeTwoRhs b s) := by
  -- TODO: reassemble the type-two facet proof once the maximality lemma is rebuilt against the
  -- fixed-shape reverse interface.
  sorry

end Exercise721
