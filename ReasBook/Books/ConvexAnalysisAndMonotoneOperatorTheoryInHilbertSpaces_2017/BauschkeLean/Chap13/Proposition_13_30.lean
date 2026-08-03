import Mathlib
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Remark_9_37
import BauschkeLean.Chap13.Proposition_13_15

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators ERealFunction InnerProductSpace

universe u v

namespace ERealFunction

noncomputable section

variable {I : Type v}
variable {H : I → Type u}
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]

/-- Helper for Proposition 13 30: an `]-∞,+∞]`-valued function with nonempty effective domain has
Fenchel conjugate nowhere equal to `-∞`. -/
private theorem conjugate_ne_bot_of_effectiveDomain_nonempty
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    {f : K → Set.Ioi (⊥ : EReal)} (hdom : (effectiveDomain f).Nonempty) (u : K) :
    f.asEReal∗ u ≠ ⊥ := by
  have hproper : IsProper f.asEReal := by
    constructor
    · intro x
      exact ne_of_gt (f x).2
    · simpa [effectiveDomain, dom] using hdom
  -- Package the nonempty effective-domain hypothesis into the properness input for
  -- Proposition 13.15.
  exact conjugate_ne_bot_of_isProper hproper u

/-- Helper for Proposition 13 30: package the conjugate of an `]-∞,+∞]`-valued function with
nonempty effective domain back into `]-∞,+∞]`. -/
private noncomputable abbrev properConjugateIoi
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (f : K → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain f).Nonempty) :
    K → Set.Ioi (⊥ : EReal) :=
  fun u ↦
    ⟨f.asEReal∗ u,
      bot_lt_iff_ne_bot.mpr (conjugate_ne_bot_of_effectiveDomain_nonempty hdom u)⟩

/-- Helper for Proposition 13 30: coercing `properConjugateIoi` back to `EReal` recovers the raw
Fenchel conjugate. -/
@[simp] private theorem properConjugateIoi_apply
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (f : K → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain f).Nonempty) (u : K) :
    (properConjugateIoi f hdom u : EReal) = f.asEReal∗ u :=
  rfl

/-- Helper for Proposition 13 30: the `Γ₀`-packaged Fenchel conjugate is the nonempty-domain
specialization of `properConjugateIoi`. -/
private noncomputable abbrev gammaZeroConjugate
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (f : K → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(K)) :
    K → Set.Ioi (⊥ : EReal) :=
  properConjugateIoi f hf.2.nonempty

/-- Helper for Proposition 13 30: coercing the local `Γ₀`-packaged conjugate back to `EReal`
recovers the raw Fenchel conjugate. -/
@[simp] private theorem gammaZeroConjugate_apply
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (f : K → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(K)) (u : K) :
    (gammaZeroConjugate f hf u : EReal) = f.asEReal∗ u :=
  rfl

section HilbertSum

variable [Finite I]

omit [Finite I] in
/-- Helper for Proposition 13 30: a finite sum of real-cast values in `EReal` is the cast of the
corresponding real sum. -/
private theorem finset_sum_coe_real (s : Finset I) (r : I → ℝ) :
    s.sum (fun i ↦ (r i : EReal)) = ((s.sum r : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty sum is preserved by the real-to-`EReal` coercion.
      simp
  | @insert i s hi ih =>
      -- Peel off the distinguished term and combine it with the induction hypothesis.
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ih, EReal.coe_add]

/-- Helper for Proposition 13 30: the defect contributed by one coordinate in the conjugate body.
-/
private def coordinateDefect
    (f : ∀ i, H i → EReal) (u : lp H 2) (i : I) (z : H i) : EReal :=
  (((⟪z, u i⟫_ℝ : ℝ) : EReal) - f i z)

/-- Helper for Proposition 13 30: the partial finite-coordinate conjugate defect over a finite set
of active coordinates. -/
private def partialCoordinateDefect
    (f : ∀ i, H i → EReal) (u : lp H 2) (s : Finset I) (x : lp H 2) : EReal :=
  s.sum (fun j ↦ coordinateDefect f u j (x j))

/-- Helper for Proposition 13 30: the supremum of all pairwise sums in `EReal` is the sum of the
two individual suprema. -/
private theorem sSup_image2_add_eq (A B : Set EReal) :
    sSup (Set.image2 (· + ·) A B) = sSup A + sSup B :=
  by
  apply le_antisymm
  · -- Bound every pairwise sum above by the sum of the two individual suprema.
    refine sSup_le ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact add_le_add (le_sSup ha) (le_sSup hb)
  · -- Approximate each supremum from below and combine the two approximants.
    refine EReal.add_le_of_forall_lt ?_
    intro a ha b hb
    rcases lt_sSup_iff.mp ha with ⟨a', ha', haa'⟩
    rcases lt_sSup_iff.mp hb with ⟨b', hb', hbb'⟩
    have hab' : a + b < a' + b' := EReal.add_lt_add haa' hbb'
    exact hab'.le.trans <| le_sSup <| Set.mem_image2.mpr ⟨a', ha', b', hb', rfl⟩

omit [Finite I] in
/-- Helper for Proposition 13 30: a finite sum of `EReal` values that are never `-∞` is itself
never `-∞`. -/
private theorem finset_sum_ne_bot_of_forall_ne_bot
    {ι : Type*} (s : Finset ι) (g : ι → EReal)
    (hbot : ∀ i ∈ s, g i ≠ ⊥) :
    s.sum g ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty sum is never `-∞`.
      simp
  | @insert i s hi ih =>
      -- Split off one summand and use the induction hypothesis on the tail.
      rw [Finset.sum_insert hi]
      refine EReal.add_ne_bot_iff.2 ?_
      constructor
      · exact hbot i (by simp)
      · exact ih (fun j hj ↦ hbot j (by simp [hj]))

omit [Finite I] in
/-- Helper for Proposition 13 30: summing coordinatewise negatives in `EReal` is the negation of
the finite sum as soon as no summand is `-∞`. -/
private theorem finset_sum_neg_ereal
    {ι : Type*} (s : Finset ι) (g : ι → EReal)
    (hbot : ∀ i ∈ s, g i ≠ ⊥) :
    s.sum (fun i ↦ -g i) = -s.sum g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty sum is fixed by negation.
      simp
  | @insert i s hi ih =>
      -- Peel off one term and move the negation across the remaining finite sum.
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        ih (fun j hj ↦ hbot j (by simp [hj]))]
      have hi_ne_bot : g i ≠ ⊥ := hbot i (by simp)
      have hs_ne_bot : s.sum g ≠ ⊥ :=
        finset_sum_ne_bot_of_forall_ne_bot (s := s) (g := g)
          (fun j hj ↦ hbot j (by simp [hj]))
      simpa using (EReal.neg_add (.inl hi_ne_bot) (.inr hs_ne_bot)).symm

omit [Finite I] in
/-- Helper for Proposition 13 30: the finite partial coordinate defect is the global
sum-of-inners minus the sum of coordinate function values over the same active set. -/
private theorem partial_coordinate_defect_eq_sum_sub
    (f : ∀ i, H i → EReal) (u : lp H 2) (s : Finset I) (x : lp H 2)
    (hbot : ∀ j ∈ s, f j (x j) ≠ ⊥) :
    partialCoordinateDefect f u s x =
      (((s.sum fun j ↦ ⟪x j, u j⟫_ℝ : ℝ) : EReal) - s.sum (fun j ↦ f j (x j))) := by
  -- Normalize each coordinate defect to `a + (-b)` and then regroup the finite sums.
  simp_rw [partialCoordinateDefect, coordinateDefect, sub_eq_add_neg]
  rw [Finset.sum_add_distrib, finset_sum_coe_real]
  congr 1
  simpa using finset_sum_neg_ereal (s := s) (g := fun j ↦ f j (x j)) hbot

/-- Helper for Proposition 13 30: activating one more coordinate splits the partial-defect range
as pairwise sums of the new coordinate defect and the old partial defect. -/
private theorem partial_coordinate_defect_range_insert_eq_image2
    (f : ∀ i, H i → EReal) (u : lp H 2) (s : Finset I) (i : I) (hi : i ∉ s) :
    Set.range (partialCoordinateDefect f u (Finset.cons i s hi)) =
      Set.image2 (· + ·) (Set.range (coordinateDefect f u i))
        (Set.range (partialCoordinateDefect f u s)) := by
  classical
  ext r
  constructor
  · intro hr
    rcases hr with ⟨x, rfl⟩
    -- Split the inserted finite sum into the distinguished coordinate and the old tail.
    refine Set.mem_image2.mpr ?_
    refine ⟨coordinateDefect f u i (x i), ⟨x i, rfl⟩, partialCoordinateDefect f u s x, ⟨x, rfl⟩, ?_⟩
    -- The finite sum over the inserted set is exactly the distinguished term plus the old tail.
    simpa [partialCoordinateDefect] using
      (Finset.sum_cons (s := s) (a := i) (h := hi)
        (f := fun j ↦ coordinateDefect f u j (x j))).symm
  · intro hr
    rcases Set.mem_image2.mp hr with ⟨a, ha, b, hb, hab⟩
    rcases ha with ⟨z, rfl⟩
    rcases hb with ⟨x, rfl⟩
    refine ⟨coordinateSlice x i z, ?_⟩
    -- Rebuild the full point by inserting the chosen coordinate into the base family `x`.
    have htail :
        partialCoordinateDefect f u s (coordinateSlice x i z) =
          partialCoordinateDefect f u s x := by
      -- Away from `i`, the slice agrees with the base point coordinatewise.
      unfold partialCoordinateDefect
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hji : j ≠ i := ne_of_mem_of_not_mem hj hi
      simp [coordinateDefect, coordinateSlice_apply_of_ne, hji]
    -- Route correction: first separate the inserted coordinate, then rewrite the frozen tail by
    -- the slice invariance lemma.
    rw [show
        partialCoordinateDefect f u (Finset.cons i s hi) (coordinateSlice x i z) =
          coordinateDefect f u i ((coordinateSlice x i z) i) +
            partialCoordinateDefect f u s (coordinateSlice x i z) by
        simpa [partialCoordinateDefect] using
          (Finset.sum_cons (s := s) (a := i) (h := hi)
            (f := fun j ↦ coordinateDefect f u j ((coordinateSlice x i z) j)))]
    simp only [coordinateSlice_apply_self]
    rw [htail]
    simpa [coordinateDefect] using hab

/-- Helper for Proposition 13 30: the supremum of the partial coordinate defects over a finite
active set is the sum of the corresponding coordinate conjugates. -/
private theorem sSup_partial_coordinate_defect_eq_sum_conjugate
    (f : ∀ i, H i → EReal) (u : lp H 2) :
    ∀ s : Finset I,
      sSup (Set.range (partialCoordinateDefect f u s)) = s.sum (fun j ↦ (f j)∗ (u j)) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      -- The empty partial defect is constantly zero.
      have hconst : partialCoordinateDefect f u ∅ = fun _ : lp H 2 ↦ (0 : EReal) := by
        funext x
        simp [partialCoordinateDefect]
      have hzero : Set.range (partialCoordinateDefect f u ∅) = ({0} : Set EReal) := by
        rw [hconst, Set.range_const]
      rw [hzero]
      simp
  | @insert i s hi ih =>
      -- Separate the new coordinate and use the induction hypothesis on the remaining coordinates.
      have hsplit :
          Set.range (partialCoordinateDefect f u (insert i s)) =
            Set.image2 (· + ·) (Set.range (coordinateDefect f u i))
              (Set.range (partialCoordinateDefect f u s)) := by
        simpa [Finset.cons_eq_insert] using
          partial_coordinate_defect_range_insert_eq_image2 (f := f) (u := u) (s := s) (i := i) hi
      rw [hsplit, sSup_image2_add_eq, ih, Finset.sum_insert hi]
      have hcoord :
          sSup (Set.range (coordinateDefect f u i)) = (f i)∗ (u i) := by
        -- The one-coordinate defect supremum is exactly the coordinate Fenchel conjugate.
        rw [conjugate_apply, ← sSup_range]
        rfl
      rw [hcoord]

/-- Helper for Proposition 13 30: after expanding the finite Hilbert sum and the `lp` inner
product, the conjugate body is the finite sum of the coordinate defects. -/
private theorem hilbertSum_conjugate_body_eq_univ_coordinate_defect
    [Fintype I] (f : ∀ i, H i → EReal) (hf_ne_bot : ∀ i x, f i x ≠ ⊥) (u x : lp H 2) :
    (((⟪x, u⟫_ℝ : ℝ) : EReal) - (⨁ i, f i) x) =
      partialCoordinateDefect f u (Finset.univ : Finset I) x :=
  by
  have huniv :
      (@Finset.univ I inferInstance) = (@Finset.univ I (Fintype.ofFinite I)) := by
    ext i
    simp
  have hsum :
      (let _ : Fintype I := Fintype.ofFinite I
       ∑ i, f i (x i)) = ∑ i, f i (x i) := by
    simpa using congrArg (fun s : Finset I ↦ s.sum (fun i ↦ f i (x i))) huniv.symm
  have hinner_sum : ∑ i, ⟪x i, u i⟫_ℝ = ⟪x, u⟫_ℝ := by
    calc
      ∑ i, ⟪x i, u i⟫_ℝ
          = ∑ i, ⟪(lpPiLpₗᵢ H ℝ x) i, (lpPiLpₗᵢ H ℝ u) i⟫_ℝ := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [coe_lpPiLpₗᵢ]
      _ = ⟪lpPiLpₗᵢ H ℝ x, lpPiLpₗᵢ H ℝ u⟫_ℝ := by
            symm
            rw [PiLp.inner_apply]
      _ = ⟪x, u⟫_ℝ := by
            exact (lpPiLpₗᵢ H ℝ).inner_map_map x u
  have hinner_cast :
      (((⟪x, u⟫_ℝ : ℝ) : EReal)) = ∑ i, ((⟪x i, u i⟫_ℝ : ℝ) : EReal) := by
    calc
      (((⟪x, u⟫_ℝ : ℝ) : EReal)) = (((∑ i, ⟪x i, u i⟫_ℝ : ℝ) : ℝ) : EReal) := by
        rw [← hinner_sum]
      _ = ∑ i, ((⟪x i, u i⟫_ℝ : ℝ) : EReal) := by
        exact (finset_sum_coe_real (s := Finset.univ) (r := fun i ↦ ⟪x i, u i⟫_ℝ)).symm
  -- Route correction: first convert the owner Hilbert sum to the concrete finite sum, then match
  -- the resulting expression with the partial-defect normal form over `Finset.univ`.
  calc
    (((⟪x, u⟫_ℝ : ℝ) : EReal) - (⨁ i, f i) x)
        = (((∑ i, ⟪x i, u i⟫_ℝ) : EReal) - ∑ i, f i (x i)) := by
            rw [hilbertSumFunction_apply_of_finite (f := f) (x := x), hsum, hinner_cast]
    _ = partialCoordinateDefect f u (Finset.univ : Finset I) x := by
          rw [finset_sum_coe_real]
          symm
          exact partial_coordinate_defect_eq_sum_sub
            (f := f) (u := u) (s := Finset.univ) (x := x)
            (hbot := fun j _ ↦ hf_ne_bot j (x j))

-- Proof sketch: unfold the finite Hilbert direct sum through the Chapter 8 owner `⨁ i, f i`, then
-- separate the defining supremum of the Fenchel conjugate into the independent coordinate suprema
-- that define the coordinate conjugates.
/-- Core owner form of Proposition 13.30: the Fenchel conjugate of a finite Hilbert direct sum is
the finite Hilbert direct sum of the coordinate Fenchel conjugates. -/
theorem conjugate_hilbertSumFunction_eq_hilbertSumFunction_conjugate
    (f : ∀ i, H i → EReal) (hf_ne_bot : ∀ i x, f i x ≠ ⊥) :
    (⨁ i, f i)∗ = ⨁ i, (f i)∗ := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  ext u
  -- Rewrite the conjugate as the supremum of the global finite-coordinate defect.
  rw [conjugate_apply, ← sSup_range]
  have hbody :
      (fun x : lp H 2 ↦ (((⟪x, u⟫_ℝ : ℝ) : EReal) - (⨁ i, f i) x)) =
        partialCoordinateDefect f u (Finset.univ : Finset I) := by
    -- Route correction: normalize the global body first, then apply the finite-set `sSup` lemma.
    funext x
    simpa using
      hilbertSum_conjugate_body_eq_univ_coordinate_defect
        (f := f) (hf_ne_bot := hf_ne_bot) (u := u) (x := x)
  rw [hbody, sSup_partial_coordinate_defect_eq_sum_conjugate (f := f) (u := u)]
  -- Convert the finite sum of coordinate conjugates back to the owner Hilbert-sum notation.
  symm
  exact hilbertSumFunction_apply_of_finite (f := fun i ↦ (f i)∗) (x := u)

end HilbertSum

section DirectSum

variable [Fintype I]

-- Proof sketch: rewrite the `Γ₀`-valued direct sum as the Chapter 8 owner `⨁ i, ...`, apply the
-- owner-level conjugate identity above, then specialize the resulting finite Hilbert sum back to
-- an ordinary coordinate sum.
/-- Proposition 13 30: after coercing a finite direct sum of `]-∞,+∞]`-valued functions to
`EReal`, its Fenchel conjugate is the finite sum of the coordinate Fenchel conjugates. -/
theorem conjugate_directSumFunction_eq_sum_conjugate
    (f : ∀ i, H i → Set.Ioi (⊥ : EReal)) :
    (directSumFunction f).asEReal∗ =
      fun u : lp H 2 ↦ ∑ i, (f i).asEReal∗ (u i) := by
  calc
    (directSumFunction f).asEReal∗ = (⨁ i, (f i).asEReal)∗ := by
      congr 1
      ext x
      simpa using directSumFunction_coe_eq_hilbertSumFunction f x
    _ = ⨁ i, ((f i).asEReal)∗ :=
      conjugate_hilbertSumFunction_eq_hilbertSumFunction_conjugate
        (fun i ↦ (f i).asEReal) (fun i x ↦ ne_of_gt ((f i x).2))
    _ = fun u : lp H 2 ↦ ∑ i, (f i).asEReal∗ (u i) := by
      ext u
      have huniv :
          (@Finset.univ I inferInstance) = (@Finset.univ I (Fintype.ofFinite I)) := by
        ext i
        simp
      simp [hilbertSumFunction, show Finite I by infer_instance]
      simpa using
        congrArg (fun s : Finset I ↦ s.sum (fun i ↦ (f i).asEReal∗ (u i))) huniv.symm

section GammaZero

variable [∀ i, CompleteSpace (H i)]

-- Proof sketch: package the source-facing conjugate identity back into `]-∞,+∞]`-valued
-- functions using `gammaZeroConjugate_apply` and the `Γ₀` membership facts supplied by `hf`.
omit [∀ i, CompleteSpace (H i)] in
/-- Companion bridge: the `Γ₀`-packaged Fenchel conjugate of the finite direct sum agrees with the
finite direct sum of the packaged coordinate conjugates. -/
theorem gammaZeroConjugate_directSumFunction_eq_directSumFunction_gammaZeroConjugate
    (f : ∀ i, H i → Set.Ioi (⊥ : EReal)) (hf : ∀ i, f i ∈ Γ₀(H i)) :
    gammaZeroConjugate (directSumFunction f)
        (directSumFunction_mem_gammaZero_of_forall_mem_gammaZero f hf) =
      directSumFunction (fun i ↦ gammaZeroConjugate (f i) (hf i)) := by
  ext u
  simpa [directSumFunction_apply, gammaZeroConjugate_apply] using
    congrFun (conjugate_directSumFunction_eq_sum_conjugate f) u

end GammaZero

end DirectSum

end

end ERealFunction
