import Mathlib.Data.EReal.Inv
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap12.Definition_12_34

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H]

section ModuleCore

variable [Module ℝ H]

/-- The midpoint map on `H × H` sending `(y, z)` to `(y + z) / 2`. -/
def proximalAverageMidpointMap : H × H → H :=
  fun p ↦ (1 / 2 : ℝ) • (p.1 + p.2)

/-- Evaluating the midpoint map at `(y, z)` returns the midpoint `(y + z) / 2`. -/
@[simp] theorem proximalAverageMidpointMap_apply (p : H × H) :
    proximalAverageMidpointMap p = (1 / 2 : ℝ) • (p.1 + p.2) :=
  rfl

omit [Module ℝ H] in
/-- The fiber kernel defining the proximal average:
`F(y, z) = (1 / 2) f(y) + (1 / 2) g(z) + (1 / 8) ‖y - z‖²`. -/
theorem proximalAverageKernel_value_mem_Ioi
    (f g : H → Set.Ioi (⊥ : EReal)) (p : H × H) :
    (((1 / 2 : ℝ) : EReal) * (f p.1 : EReal) +
        ((1 / 2 : ℝ) : EReal) * (g p.2 : EReal) +
        ((((1 / 8 : ℝ) * ‖p.1 - p.2‖ ^ 2 : ℝ) : EReal))) ∈
      Set.Ioi (⊥ : EReal) := by
  -- Each summand is strictly above `⊥`, so their sum is also strictly above `⊥`.
  rw [Set.mem_Ioi, bot_lt_iff_ne_bot]
  have hhalf_ne_bot : (((1 / 2 : ℝ) : EReal)) ≠ ⊥ := EReal.coe_ne_bot _
  have hhalf_ne_top : (((1 / 2 : ℝ) : EReal)) ≠ ⊤ := EReal.coe_ne_top _
  have hhalf_nonneg : (0 : EReal) ≤ (((1 / 2 : ℝ) : EReal)) := by
    exact EReal.coe_nonneg.mpr (by norm_num)
  have hf_ne_bot : (f p.1 : EReal) ≠ ⊥ := by
    exact (bot_lt_iff_ne_bot.mp (f p.1).2)
  have hg_ne_bot : (g p.2 : EReal) ≠ ⊥ := by
    exact (bot_lt_iff_ne_bot.mp (g p.2).2)
  have hleft_ne_bot : (((1 / 2 : ℝ) : EReal) * (f p.1 : EReal)) ≠ ⊥ := by
    exact (EReal.mul_ne_bot _ _).2
      ⟨Or.inl hhalf_ne_bot, Or.inr hf_ne_bot, Or.inl hhalf_ne_top, Or.inl hhalf_nonneg⟩
  have hmid_ne_bot : (((1 / 2 : ℝ) : EReal) * (g p.2 : EReal)) ≠ ⊥ := by
    exact (EReal.mul_ne_bot _ _).2
      ⟨Or.inl hhalf_ne_bot, Or.inr hg_ne_bot, Or.inl hhalf_ne_top, Or.inl hhalf_nonneg⟩
  have hquad_ne_bot :
      ((((1 / 8 : ℝ) * ‖p.1 - p.2‖ ^ 2 : ℝ) : EReal)) ≠ ⊥ := EReal.coe_ne_bot _
  have hsum_ne_bot :
      (((1 / 2 : ℝ) : EReal) * (f p.1 : EReal) +
          ((1 / 2 : ℝ) : EReal) * (g p.2 : EReal)) ≠ ⊥ := by
    exact (EReal.add_ne_bot_iff.2 ⟨hleft_ne_bot, hmid_ne_bot⟩)
  exact (EReal.add_ne_bot_iff.2 ⟨hsum_ne_bot, hquad_ne_bot⟩)

/-- The textbook proximal-average kernel on `H × H`. -/
def proximalAverageKernel (f g : H → Set.Ioi (⊥ : EReal)) :
    H × H → Set.Ioi (⊥ : EReal) :=
  fun p ↦
    ⟨(((1 / 2 : ℝ) : EReal) * (f p.1 : EReal) +
        ((1 / 2 : ℝ) : EReal) * (g p.2 : EReal) +
        ((((1 / 8 : ℝ) * ‖p.1 - p.2‖ ^ 2 : ℝ) : EReal))),
      proximalAverageKernel_value_mem_Ioi f g p⟩

omit [Module ℝ H] in
/-- Coercing the proximal-average kernel to `EReal` recovers the textbook formula for `F`. -/
@[simp] theorem proximalAverageKernel_apply
    (f g : H → Set.Ioi (⊥ : EReal)) (p : H × H) :
    (proximalAverageKernel f g p : EReal) =
      ((1 / 2 : ℝ) : EReal) * (f p.1 : EReal) +
        ((1 / 2 : ℝ) : EReal) * (g p.2 : EReal) +
        ((((1 / 8 : ℝ) * ‖p.1 - p.2‖ ^ 2 : ℝ) : EReal)) :=
  rfl

/-- The raw proximal-average owner obtained as the infimal postcomposition of the textbook kernel
along the midpoint map. -/
def proximalAverage (f g : H → Set.Ioi (⊥ : EReal)) : H → EReal :=
  proximalAverageMidpointMap ▷ proximalAverageKernel f g

notation "pav(" f ", " g ")" => proximalAverage f g

-- Semantic recall: `lean_leansearch` surfaced midpoint lemmas such as `midpoint_eq_smul_add`; this
-- file keeps the project's direct midpoint-map owner because later API is phrased via fibers.

/-- A pair `(y, z)` lies in the midpoint fiber above `x` exactly when
`z` is the affine companion `(2 : ℝ) • x - y`. -/
theorem proximalAverageMidpointMap_eq_iff (x y z : H) :
    proximalAverageMidpointMap (y, z) = x ↔ z = (2 : ℝ) • x - y := by
  constructor
  · intro hmid
    -- Scale the midpoint identity by `2` to recover the affine constraint `y + z = 2 • x`.
    have hsum : y + z = (2 : ℝ) • x := by
      have htwo := congrArg (fun t : H ↦ (2 : ℝ) • t) hmid
      simpa [proximalAverageMidpointMap_apply, smul_smul] using htwo
    exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using hsum)
  · intro hz
    -- Substitute the affine companion back into the midpoint map and simplify the scalar action.
    have hsum : y + z = (2 : ℝ) • x := by
      calc
        y + z = y + ((2 : ℝ) • x - y) := by rw [hz]
        _ = (2 : ℝ) • x := by
          simp [sub_eq_add_neg, add_comm]
    calc
      proximalAverageMidpointMap (y, z) = (1 / 2 : ℝ) • (y + z) := by
        rw [proximalAverageMidpointMap_apply]
      _ = (1 / 2 : ℝ) • ((2 : ℝ) • x) := by rw [hsum]
      _ = x := by simp [smul_smul]

/-- Evaluating the infimal postcomposition over the midpoint fiber can
be parameterized by the single variable `y`, with companion point `(2 : ℝ) • x - y`. -/
theorem proximalAverage_apply_eq_iInf_parameterized
    (f g : H → Set.Ioi (⊥ : EReal)) (x : H) :
    pav(f, g) x = ⨅ y : H, (proximalAverageKernel f g (y, (2 : ℝ) • x - y) : EReal) := by
  -- Rewrite the midpoint fiber as the affine range `y ↦ (y, 2 • x - y)`.
  calc
    pav(f, g) x =
        sInf ((fun p ↦ (proximalAverageKernel f g p : EReal)) ''
          (proximalAverageMidpointMap ⁻¹' ({x} : Set H))) := by
            change (proximalAverageMidpointMap ▷ proximalAverageKernel f g) x =
              sInf ((fun p ↦ (proximalAverageKernel f g p : EReal)) ''
                (proximalAverageMidpointMap ⁻¹' ({x} : Set H)))
            exact infimalPostcomposition_apply proximalAverageMidpointMap
              (proximalAverageKernel f g) x
    _ = ⨅ y : H, (proximalAverageKernel f g (y, (2 : ℝ) • x - y) : EReal) := by
      have hfiber :
          proximalAverageMidpointMap ⁻¹' ({x} : Set H) =
            Set.range (fun y : H ↦ (y, (2 : ℝ) • x - y)) := by
        ext p
        rcases p with ⟨y, z⟩
        constructor
        · intro hp
          rw [Set.mem_preimage, Set.mem_singleton_iff] at hp
          have hz : z = (2 : ℝ) • x - y := (proximalAverageMidpointMap_eq_iff x y z).1 hp
          refine ⟨y, ?_⟩
          simp [hz]
        · rintro ⟨w, hw⟩
          rw [Set.mem_preimage, Set.mem_singleton_iff]
          have hy : w = y := by
            simpa using congrArg Prod.fst hw
          have hz : (2 : ℝ) • x - w = z := by
            simpa using congrArg Prod.snd hw
          subst w
          exact (proximalAverageMidpointMap_eq_iff x y z).2 (by simpa [eq_comm] using hz)
      have himage :
          ((fun p ↦ (proximalAverageKernel f g p : EReal)) ''
              Set.range (fun y : H ↦ (y, (2 : ℝ) • x - y))) =
            Set.range
              (fun y : H ↦
                (proximalAverageKernel f g (y, (2 : ℝ) • x - y) : EReal)) := by
        ext a
        constructor
        · rintro ⟨p, hp, rfl⟩
          rcases hp with ⟨y, rfl⟩
          exact ⟨y, rfl⟩
        · rintro ⟨y, rfl⟩
          exact ⟨(y, (2 : ℝ) • x - y), ⟨y, rfl⟩, rfl⟩
      rw [hfiber, himage, sInf_range]

end ModuleCore

/-- After substituting the midpoint-fiber parameterization, the
proximal-average kernel factors as the positive scalar `1 / 2` times the textbook single-variable
integrand. -/
-- Route note: the intended proof uses a norm-scaling identity, so later proof work will need a
-- Hilbert/normed-space bridge rather than the ambient `Module` assumptions alone.
theorem proximalAverageKernel_midpoint_substitution
    [NormedSpace ℝ H]
    (f g : H → Set.Ioi (⊥ : EReal)) (x y : H) :
    (proximalAverageKernel f g (y, (2 : ℝ) • x - y) : EReal) =
      ((1 / 2 : ℝ) : EReal) *
        ((f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) +
          ((‖x - y‖ ^ 2 : ℝ) : EReal)) := by
  -- Route correction: this normalization needs `norm_smul`, so the helper now works in a
  -- genuine normed `ℝ`-space rather than a bare `Module`.
  rw [proximalAverageKernel_apply]
  have hhalf_nonneg : (0 : EReal) ≤ (((1 / 2 : ℝ) : EReal)) := by
    exact EReal.coe_nonneg.mpr (by norm_num)
  have hhalf_ne_top : (((1 / 2 : ℝ) : EReal)) ≠ ⊤ := EReal.coe_ne_top _
  have hdiff :
      y - ((2 : ℝ) • x - y) = (2 : ℝ) • (y - x) := by
    calc
      y - ((2 : ℝ) • x - y) = y + y - (2 : ℝ) • x := by
        simp [sub_eq_add_neg, add_assoc, add_comm]
      _ = (2 : ℝ) • y - (2 : ℝ) • x := by simp [two_smul, sub_eq_add_neg]
      _ = (2 : ℝ) • (y - x) := by rw [smul_sub]
  have hnormsq : ‖y - ((2 : ℝ) • x - y)‖ ^ 2 = (4 : ℝ) * ‖x - y‖ ^ 2 := by
    have hnorm : ‖(2 : ℝ) • (y - x)‖ = (2 : ℝ) * ‖y - x‖ := by
      simpa using norm_smul_of_nonneg (t := (2 : ℝ)) (x := y - x) (by norm_num)
    calc
      ‖y - ((2 : ℝ) • x - y)‖ ^ 2 = ‖(2 : ℝ) • (y - x)‖ ^ 2 := by rw [hdiff]
      _ = ((2 : ℝ) * ‖y - x‖) ^ 2 := by rw [hnorm]
      _ = (4 : ℝ) * ‖x - y‖ ^ 2 := by
        rw [norm_sub_rev]
        ring
  have hquadratic :
      ((((1 / 8 : ℝ) * ‖y - ((2 : ℝ) • x - y)‖ ^ 2 : ℝ) : EReal)) =
        ((1 / 2 : ℝ) : EReal) * ((‖x - y‖ ^ 2 : ℝ) : EReal) := by
    rw [hnormsq, ← EReal.coe_mul]
    congr 1
    ring
  -- Expand the common factor `1 / 2` across the three textbook summands.
  calc
    ((1 / 2 : ℝ) : EReal) * (f y : EReal) +
        ((1 / 2 : ℝ) : EReal) * (g ((2 : ℝ) • x - y) : EReal) +
        ((((1 / 8 : ℝ) * ‖y - ((2 : ℝ) • x - y)‖ ^ 2 : ℝ) : EReal)) =
      ((1 / 2 : ℝ) : EReal) * ((f y : EReal) + (g ((2 : ℝ) • x - y) : EReal)) +
        (((1 / 2 : ℝ) : EReal) * ((‖x - y‖ ^ 2 : ℝ) : EReal)) := by
          rw [← EReal.left_distrib_of_nonneg_of_ne_top hhalf_nonneg hhalf_ne_top, hquadratic]
    _ = ((1 / 2 : ℝ) : EReal) *
        ((f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) +
          ((‖x - y‖ ^ 2 : ℝ) : EReal)) := by
          rw [← EReal.left_distrib_of_nonneg_of_ne_top hhalf_nonneg hhalf_ne_top]

/-- Multiplication by a positive finite real scalar commutes with
indexed infima in `EReal`. -/
theorem ereal_mul_iInf_of_pos {ι : Sort v} (a : ℝ) (ha : 0 < a) (φ : ι → EReal) :
    ((a : EReal) * ⨅ i, φ i) = ⨅ i, ((a : EReal) * φ i) := by
  let aE : EReal := a
  have haE_pos : 0 < aE := EReal.coe_pos.2 ha
  have haE_nonneg : 0 ≤ aE := le_of_lt haE_pos
  have haE_ne_top : aE ≠ ⊤ := EReal.coe_ne_top a
  apply le_antisymm
  · -- The infimum is below each term, and positive multiplication preserves that order.
    refine le_iInf fun i ↦ ?_
    exact mul_le_mul_of_nonneg_left (iInf_le φ i) haE_nonneg
  · -- Divide by the positive scalar to reduce to the universal property of `iInf`.
    rw [← EReal.div_le_iff_le_mul haE_pos haE_ne_top]
    refine le_iInf fun i ↦ ?_
    rw [EReal.div_le_iff_le_mul haE_pos haE_ne_top]
    exact iInf_le (fun i ↦ aE * φ i) i

section ModuleTextbook

variable [Module ℝ H]

/-- Definition 14.6: if `f, g ∈ Γ₀(H)`, then `pav(f, g) x` is the constrained infimum of
`proximalAverageKernel f g` over the pairs `(y, z)` with `y + z = (2 : ℝ) • x`, i.e. the
owner-level form of `(14.10)`. -/
theorem proximalAverage_textbookFormula
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) (x : H) :
    pav(f, g) x =
      sInf ((fun p : H × H ↦ (proximalAverageKernel f g p : EReal)) ''
        {p : H × H | p.1 + p.2 = (2 : ℝ) • x}) := by
  -- The owner definition already takes the infimum over the midpoint fiber; rewrite that fiber by
  -- the equivalent affine constraint `y + z = 2 • x`.
  let _ : f ∈ Γ₀(H) := hf
  let _ : g ∈ Γ₀(H) := hg
  have hfiber :
      proximalAverageMidpointMap ⁻¹' ({x} : Set H) =
        {p : H × H | p.1 + p.2 = (2 : ℝ) • x} := by
    ext p
    rcases p with ⟨y, z⟩
    constructor
    · intro hp
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hp
      have htwo := congrArg (fun t : H ↦ (2 : ℝ) • t) hp
      simpa [proximalAverageMidpointMap_apply, smul_smul] using htwo
    · intro hp
      rw [Set.mem_preimage, Set.mem_singleton_iff]
      calc
        proximalAverageMidpointMap (y, z) = (1 / 2 : ℝ) • (y + z) := by
          rw [proximalAverageMidpointMap_apply]
        _ = (1 / 2 : ℝ) • ((2 : ℝ) • x) := by rw [hp]
        _ = x := by simp [smul_smul]
  calc
    pav(f, g) x =
        sInf ((fun p ↦ (proximalAverageKernel f g p : EReal)) ''
          (proximalAverageMidpointMap ⁻¹' ({x} : Set H))) := by
            change (proximalAverageMidpointMap ▷ proximalAverageKernel f g) x =
              sInf ((fun p ↦ (proximalAverageKernel f g p : EReal)) ''
                (proximalAverageMidpointMap ⁻¹' ({x} : Set H)))
            exact infimalPostcomposition_apply proximalAverageMidpointMap
              (proximalAverageKernel f g) x
    _ = sInf ((fun p : H × H ↦ (proximalAverageKernel f g p : EReal)) ''
          {p : H × H | p.1 + p.2 = (2 : ℝ) • x}) := by
      rw [hfiber]

end ModuleTextbook

section HilbertFormula

-- Semantic recall: `lean_leansearch` confirms mathlib's `HilbertSpace ℝ H` packages
-- `[InnerProductSpace ℝ H] [CompleteSpace H]`, matching the textbook Hilbert-space ambient.
variable [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Evaluating `pav(f, g)` at `x` gives the single-variable infimum formula used throughout
Chapter 14. -/
-- Route note: this companion keeps the established `proximalAverage_apply` name used downstream,
-- while the label-associated theorem above carries the source-faithful `Γ₀(H)` surface.
@[simp] theorem proximalAverage_apply (f g : H → Set.Ioi (⊥ : EReal)) (x : H) :
    pav(f, g) x =
      ((1 / 2 : ℝ) : EReal) *
        (⨅ y : H,
          (f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) +
            ((‖x - y‖ ^ 2 : ℝ) : EReal)) := by
  -- Parameterize the midpoint fiber by `y`, then normalize the kernel term pointwise.
  rw [proximalAverage_apply_eq_iInf_parameterized]
  have hpointwise :
      (fun y : H ↦ (proximalAverageKernel f g (y, (2 : ℝ) • x - y) : EReal)) =
        fun y : H ↦
          ((1 / 2 : ℝ) : EReal) *
            ((f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) +
              ((‖x - y‖ ^ 2 : ℝ) : EReal)) := by
    funext y
    exact proximalAverageKernel_midpoint_substitution f g x y
  rw [hpointwise]
  symm
  exact ereal_mul_iInf_of_pos (a := 1 / 2) (by norm_num) _

end HilbertFormula

end ERealFunction
