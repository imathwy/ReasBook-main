import Mathlib
import Mathlib.Data.List.TFAE
import BauschkeLean.Chap01.Text_1_0_57
import BauschkeLean.Chap01.Lemma_1_24
import BauschkeLean.Chap08.Corollary_8_5
import BauschkeLean.Chap07.Definition_7_8
import BauschkeLean.Chap07.Exercise_7_1
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_3
import BauschkeLean.Chap10.Definition_10_1
import BauschkeLean.Chap13.Example_13_3
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap13.Proposition_13_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

noncomputable section

section SupportFunctionCharacterization

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 14.11 characterizes positively homogeneous members of `Γ₀(H)` as
  support functions, with the source-defined set `C` from formula `(14.19)`.
- `core/canonical`: the owner object behind `(14.19)` is the affine-defect supremum
  `u ↦ ⨆ x, ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x`; the source-defined set is exactly its zero lower
  level set.
- `bridge/view`: this file keeps the source-facing set `linearMinorantSet f` and bridges it to the
  canonical lower-level-set API, without replacing the textbook clause `(i) → (ii)` by a second
  owner-level support-function theorem. -/

/-- The source-defined set `C` from `(14.19)`, consisting of the vectors whose linear functional
is dominated pointwise by `f`. -/
def linearMinorantSet (f : H → Set.Ioi (⊥ : EReal)) : Set H :=
  {u | ∀ x, (⟪x, u⟫_ℝ : EReal) ≤ f x}

/-- A vector belongs to `linearMinorantSet f` exactly when its linear functional is pointwise
dominated by `f`. -/
@[simp] theorem mem_linearMinorantSet_iff
    {f : H → Set.Ioi (⊥ : EReal)} {u : H} :
    u ∈ linearMinorantSet f ↔ ∀ x, (⟪x, u⟫_ℝ : EReal) ≤ f x := by
  -- Unfold the source-defined set from `(14.19)`.
  rfl

/-- The source-defined set `linearMinorantSet f` is the zero lower level set of the affine-defect
supremum `u ↦ sup_x (⟪x, u⟫ - f x)`. -/
theorem linearMinorantSet_eq_lowerLevelSet_affineDefectSup_zero
    (f : H → Set.Ioi (⊥ : EReal)) :
    linearMinorantSet f =
      lowerLevelSet (fun u ↦ ⨆ x : H, ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) 0 := by
  ext u
  -- Rewrite the source-defined inequalities as a zero-sublevel condition on the affine-defect
  -- supremum.
  rw [mem_linearMinorantSet_iff, mem_lowerLevelSet_iff]
  constructor
  · intro hu
    refine iSup_le ?_
    intro x
    exact
      (EReal.sub_le_iff_le_add
        (a := ((⟪x, u⟫_ℝ : ℝ) : EReal)) (b := (f x : EReal)) (c := (0 : EReal))
        (Or.inr EReal.zero_ne_top) (Or.inr EReal.zero_ne_bot)).2 <| by
          simpa using hu x
  · intro hu x
    have hx :
        ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x ≤ 0 := by
      exact le_trans (le_iSup (fun y : H ↦ ((⟪y, u⟫_ℝ : ℝ) : EReal) - f y) x) hu
    have hx' :
        ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ 0 + (f x : EReal) :=
      (EReal.sub_le_iff_le_add
        (a := ((⟪x, u⟫_ℝ : ℝ) : EReal)) (b := (f x : EReal)) (c := (0 : EReal))
        (Or.inr EReal.zero_ne_top) (Or.inr EReal.zero_ne_bot)).1 hx
    simpa [zero_add] using hx'

/-- Helper for Proposition 14 11: a positively homogeneous member of `Γ₀(H)` has value `0` at
the origin. -/
lemma value_zero_eq_zero_of_positivelyHomogeneous_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)}
    (hph : PositivelyHomogeneous f.asEReal) (hf : f ∈ Γ₀(H)) :
    (f 0 : EReal) = 0 := by
  rcases hf.2.nonempty with ⟨y, hy⟩
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
  -- Route correction: the source ray-limit argument is implemented directly through lower
  -- semicontinuity at `0`, because the available Proposition 9.14 API already assumes the
  -- endpoint value at `0` is finite.
  let ray : ℝ → EReal := fun t ↦ (f (t • y) : EReal)
  have hray_lsc : LowerSemicontinuous ray := by
    -- Compose the lower semicontinuous owner `f.asEReal` with the continuous ray `t ↦ t • y`.
    simpa [ray, Function.comp] using hf.1.comp (continuous_id.smul continuous_const)
  have hzero_le_liminf :
      (f 0 : EReal) ≤ Filter.liminf ray (𝓝[>] (0 : ℝ)) := by
    -- Lower semicontinuity gives the usual liminf lower bound, and the right-neighborhood filter
    -- only weakens that conclusion.
    calc
      (f 0 : EReal) = ray 0 := by simp [ray]
      _ ≤ Filter.liminf ray (𝓝 (0 : ℝ)) := (hray_lsc.lowerSemicontinuousAt 0).le_liminf
      _ ≤ Filter.liminf ray (𝓝[>] (0 : ℝ)) :=
        Filter.liminf_le_liminf_of_le (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hscaled_tendsto_real :
      Filter.Tendsto (fun t : ℝ ↦ t * (f y : EReal).toReal)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    -- Along the ray, the positive homogeneity formula reduces the values to an ordinary real
    -- multiple of `t`, which tends to `0`.
    simpa using
      (((continuous_id.mul continuous_const).continuousAt : ContinuousAt
          (fun t : ℝ ↦ t * (f y : EReal).toReal) 0).tendsto.mono_left nhdsWithin_le_nhds)
  have hscaled_tendsto :
      Filter.Tendsto (fun t : ℝ ↦ ((t * (f y : EReal).toReal : ℝ) : EReal))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : EReal)) := by
    exact (continuous_coe_real_ereal.tendsto 0).comp hscaled_tendsto_real
  have hray_eq :
      ray =ᶠ[𝓝[>] (0 : ℝ)]
        fun t : ℝ ↦ ((t * (f y : EReal).toReal : ℝ) : EReal) := by
    have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := by
      simpa using (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))
    filter_upwards [hpos] with t ht
    -- Positive homogeneity identifies the ray values with the expected real scaling.
    calc
      ray t = (f (t • y) : EReal) := by rfl
      _ = t • (f y : EReal) := by simpa [ray] using hph ht y
      _ = ((t : EReal) * (f y : EReal)) := by rw [EReal.real_smul_def]
      _ = ((t : EReal) * (((f y : EReal).toReal : ℝ) : EReal)) := by
            rw [EReal.coe_toReal hy_top hy_bot]
      _ = ((t * (f y : EReal).toReal : ℝ) : EReal) := by
            rw [← EReal.coe_mul]
  have hray_tendsto : Filter.Tendsto ray (𝓝[>] (0 : ℝ)) (𝓝 (0 : EReal)) := by
    exact hscaled_tendsto.congr' hray_eq.symm
  have hzero_le : (f 0 : EReal) ≤ 0 := by
    simpa [ray] using hzero_le_liminf.trans_eq hray_tendsto.liminf_eq
  have hzero_top : (f 0 : EReal) ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt hzero_le (EReal.coe_lt_top 0))
  have hzero_bot : (f 0 : EReal) ≠ ⊥ := ne_of_gt (f 0).2
  have hdouble : (f 0 : EReal) = (2 : ℝ) • (f 0 : EReal) := by
    simpa using hph (by norm_num : 0 < (2 : ℝ)) (0 : H)
  have hdouble_real : (f 0 : EReal).toReal = 2 * (f 0 : EReal).toReal := by
    -- Once `f 0` is known to be finite, the positive-homogeneity identity becomes an ordinary real
    -- equation.
    simpa [EReal.real_smul_def, EReal.toReal_mul, EReal.toReal_coe, hzero_top, hzero_bot] using
      congrArg EReal.toReal hdouble
  have hzero_real_nonpos : (f 0 : EReal).toReal ≤ 0 := by
    rw [← EReal.coe_toReal hzero_top hzero_bot] at hzero_le
    exact_mod_cast hzero_le
  have hzero_real : (f 0 : EReal).toReal = 0 := by
    linarith
  rw [← EReal.coe_toReal hzero_top hzero_bot, hzero_real]
  rfl

/-- Helper for Proposition 14 11: once `f 0 = 0`, the conjugate of a positively homogeneous
`Γ₀(H)` owner is the indicator of its linear-minorant set. -/
lemma conjugate_eq_indicator_linearMinorantSet_of_value_zero_of_positivelyHomogeneous
    {f : H → Set.Ioi (⊥ : EReal)}
    (h0 : (f 0 : EReal) = 0) (hph : PositivelyHomogeneous f.asEReal) :
    f.asEReal∗ = (ι[linearMinorantSet f]).asEReal := by
  ext u
  by_cases hu : u ∈ linearMinorantSet f
  · -- On the minorant set, every affine defect is nonpositive, and `x = 0` realizes the value
    -- `0`.
    have hupper : f.asEReal∗ u ≤ 0 := by
      rw [conjugate_apply]
      refine iSup_le ?_
      intro x
      exact
        (EReal.sub_le_iff_le_add
          (a := ((⟪x, u⟫_ℝ : ℝ) : EReal)) (b := (f x : EReal)) (c := (0 : EReal))
          (Or.inr EReal.zero_ne_top) (Or.inr EReal.zero_ne_bot)).2 <| by
            simpa using (mem_linearMinorantSet_iff.mp hu) x
    have hlower : 0 ≤ f.asEReal∗ u := by
      rw [conjugate_apply]
      simpa [h0] using
        (le_iSup (fun x : H ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) (0 : H))
    have hvalue : f.asEReal∗ u = 0 := le_antisymm hupper hlower
    simpa [indicator_apply, hu] using hvalue
  · -- Off the minorant set, a positive affine defect can be scaled along a ray to force the
    -- conjugate value to `⊤`.
    have hnot_mem : u ∉ linearMinorantSet f := hu
    rw [mem_linearMinorantSet_iff] at hu
    simp only [not_forall] at hu
    rcases hu with ⟨z, hz⟩
    have hz_sub :
        ¬ (((⟪z, u⟫_ℝ : ℝ) : EReal) - f z ≤ 0) := by
      intro hz0
      apply hz
      have hz_le :
          ((⟪z, u⟫_ℝ : ℝ) : EReal) ≤ 0 + (f z : EReal) :=
        (EReal.sub_le_iff_le_add
          (a := ((⟪z, u⟫_ℝ : ℝ) : EReal)) (b := (f z : EReal)) (c := (0 : EReal))
          (Or.inr EReal.zero_ne_top) (Or.inr EReal.zero_ne_bot)).1 hz0
      simpa [zero_add] using hz_le
    have hz_pos : 0 < (((⟪z, u⟫_ℝ : ℝ) : EReal) - f z) := by
      exact lt_of_not_ge hz_sub
    have hz_top : (f z : EReal) ≠ ⊤ := by
      intro htop
      have : (((⟪z, u⟫_ℝ : ℝ) : EReal) - f z) ≤ 0 := by simp [htop]
      exact (not_lt_of_ge this) hz_pos
    have hz_bot : (f z : EReal) ≠ ⊥ := ne_of_gt (f z).2
    have hz_real : 0 < ⟪z, u⟫_ℝ - (f z : EReal).toReal := by
      rw [← EReal.coe_toReal hz_top hz_bot] at hz_pos
      exact_mod_cast hz_pos
    have htop : f.asEReal∗ u = ⊤ := by
      rw [conjugate_apply, EReal.eq_top_iff_forall_lt]
      intro y
      let t : ℝ := |y| / (⟪z, u⟫_ℝ - (f z : EReal).toReal) + 1
      have ht : 0 < t := by
        dsimp [t]
        positivity
      have hmul :
          t * (⟪z, u⟫_ℝ - (f z : EReal).toReal) =
            |y| + (⟪z, u⟫_ℝ - (f z : EReal).toReal) := by
        dsimp [t]
        field_simp [hz_real.ne']
      have hy_lt :
          y < t * (⟪z, u⟫_ℝ - (f z : EReal).toReal) := by
        have hy_abs : y ≤ |y| := le_abs_self y
        rw [hmul]
        linarith
      have hscaled_defect :
          (((⟪t • z, u⟫_ℝ : ℝ) : EReal) - f (t • z)) =
            ((t * (⟪z, u⟫_ℝ - (f z : EReal).toReal) : ℝ) : EReal) := by
        -- Positive homogeneity turns the defect at `t • z` into the scalar multiple of the
        -- original defect.
        have hmul_fz :
            ((t : EReal) * (f z : EReal)) =
              ((t * (f z : EReal).toReal : ℝ) : EReal) := by
          rw [(EReal.coe_toReal hz_top hz_bot).symm]
          simpa using (EReal.coe_mul t ((f z : EReal).toReal)).symm
        calc
          (((⟪t • z, u⟫_ℝ : ℝ) : EReal) - f (t • z)) =
              (((t * ⟪z, u⟫_ℝ : ℝ) : EReal) - ((t : EReal) * (f z : EReal))) := by
                rw [show (f (t • z) : EReal) = (t : EReal) * (f z : EReal) by
                      simpa using hph ht z]
                rw [real_inner_smul_left]
          _ = (((t * ⟪z, u⟫_ℝ : ℝ) : EReal) -
                ((t * (f z : EReal).toReal : ℝ) : EReal)) := by
                rw [hmul_fz]
          _ = ((t * (⟪z, u⟫_ℝ - (f z : EReal).toReal) : ℝ) : EReal) := by
                norm_num [mul_sub]
      calc
        (y : EReal) < ((t * (⟪z, u⟫_ℝ - (f z : EReal).toReal) : ℝ) : EReal) := by
          exact_mod_cast hy_lt
        _ = (((⟪t • z, u⟫_ℝ : ℝ) : EReal) - f (t • z)) := by
          symm
          exact hscaled_defect
        _ ≤ ⨆ x : H, ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x := by
          exact le_iSup (fun x : H ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) (t • z)
    simpa [indicator_apply, hnot_mem] using htop

/-- Helper for Proposition 14 11: the remaining source-faithful gap is the noncomplete
Fenchel--Moreau step turning the indicator-conjugate description into the support-function
representation. -/
theorem asEReal_eq_supportFunction_linearMinorantSet_of_positivelyHomogeneous_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)}
    (hph : PositivelyHomogeneous f.asEReal) (hf : f ∈ Γ₀(H)) :
    f.asEReal = σ[linearMinorantSet f] := by
  -- First identify the conjugate as the indicator of the source-defined minorant set.
  have h0 : (f 0 : EReal) = 0 :=
    value_zero_eq_zero_of_positivelyHomogeneous_mem_gammaZero hph hf
  have hconj :
      f.asEReal∗ = (ι[linearMinorantSet f]).asEReal :=
    conjugate_eq_indicator_linearMinorantSet_of_value_zero_of_positivelyHomogeneous h0 hph
  -- Then Fenchel--Moreau turns the biconjugate back into the support function.
  calc
    f.asEReal = f.asEReal∗∗ := by
      symm
      exact biconjugate_eq_of_mem_gammaZero hf
    _ = ((ι[linearMinorantSet f]).asEReal)∗ := by
      rw [hconj]
    _ = σ[linearMinorantSet f] := by
      rw [conjugate_indicator_eq_supportFunction]

/-- Helper for Proposition 14 11: the linear-minorant set is closed because it is the zero lower
level set of the lower semicontinuous conjugate. -/
theorem isClosed_linearMinorantSet
    (f : H → Set.Ioi (⊥ : EReal)) :
    IsClosed (linearMinorantSet f) := by
  have hlsc : LowerSemicontinuous f.asEReal∗ := by
    exact (mem_gamma_iff (f.asEReal∗)).mp (conjugate_mem_gamma f.asEReal) |>.2
  have hclosed : IsClosed (lowerLevelSet f.asEReal∗ 0) := by
    exact (lowerSemicontinuous_iff_isClosed_lowerLevelSet f.asEReal∗).1 hlsc 0
  -- Rewrite the source-defined set as the zero lower level set of the conjugate.
  simpa [linearMinorantSet_eq_lowerLevelSet_affineDefectSup_zero, conjugate_apply] using hclosed

/-- Helper for Proposition 14 11: the linear-minorant set is convex because it is a lower level
set of the convex conjugate. -/
theorem convex_linearMinorantSet
    (f : H → Set.Ioi (⊥ : EReal)) :
    Convex ℝ (linearMinorantSet f) := by
  have hconv : IsConvex f.asEReal∗ := by
    exact (mem_gamma_iff (f.asEReal∗)).mp (conjugate_mem_gamma f.asEReal) |>.1
  have hconv_epi : Convex ℝ (epigraph f.asEReal∗) := by
    exact (convex_epigraph_iff_jensen_on_dom f.asEReal∗).2 <| by
      intro x y hx hy a ha0 ha1
      exact hconv ha0.le ha1.le
  have hlevel : Convex ℝ (lowerLevelSet f.asEReal∗ 0) := by
    exact convex_lowerLevelSet_of_convex_epigraph f.asEReal∗ hconv_epi 0
  -- Rewrite the source-defined set as the zero lower level set of the conjugate.
  simpa [linearMinorantSet_eq_lowerLevelSet_affineDefectSup_zero, conjugate_apply] using hlevel

/-- Helper for Proposition 14 11: the support function is the supremum over the subtype indexing
set. -/
private lemma supportFunction_eq_iSup_subtype_local
    (C : Set H) :
    σ[C] = fun u : H ↦ ⨆ x : C, ((⟪(x : H), u⟫_ℝ : ℝ) : EReal) := by
  funext u
  -- Replace the image over `C` by the range of the same functional on the subtype.
  rw [supportFunction_eq_sSup_image]
  have himage :
      (fun x : H ↦ (⟪x, u⟫_ℝ : EReal)) '' C =
        Set.range (fun x : C ↦ ((⟪(x : H), u⟫_ℝ : ℝ) : EReal)) := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
  rw [himage, sSup_range]

/-- Helper for Proposition 14 11: every continuous inner functional belongs to `Γ(H)`. -/
private lemma inner_functional_mem_gamma_local
    (x : H) :
    (fun u : H ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal)) ∈ gamma H := by
  rw [mem_gamma_iff]
  refine ⟨?_, ?_⟩
  · intro u v a ha0 ha1
    -- Jensen convexity is equality because the inner functional is linear.
    have hinner :
        ⟪x, a • u + (1 - a) • v⟫_ℝ =
          a * ⟪x, u⟫_ℝ + (1 - a) * ⟪x, v⟫_ℝ := by
      simp [inner_add_right, inner_smul_right]
    change (((⟪x, a • u + (1 - a) • v⟫_ℝ : ℝ) : EReal)) ≤
      (a : EReal) * ((⟪x, u⟫_ℝ : ℝ) : EReal) +
        (((1 - a : ℝ) : EReal) * ((⟪x, v⟫_ℝ : ℝ) : EReal))
    rw [hinner, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  · -- Continuity of the real inner functional lifts to lower semicontinuity in `EReal`.
    simpa using
      (continuous_coe_real_ereal.comp (continuous_const.inner continuous_id)).lowerSemicontinuous

/-- Helper for Proposition 14 11: the support function belongs to `Γ(H)`. -/
private lemma supportFunction_mem_gamma_local
    (C : Set H) :
    σ[C] ∈ gamma H := by
  rw [supportFunction_eq_iSup_subtype_local]
  -- The support function is the supremum of the inner functionals indexed by `C`.
  exact iSup_mem_gamma
    (fun x : C ↦ fun u : H ↦ ((⟪(x : H), u⟫_ℝ : ℝ) : EReal))
    (fun x ↦ inner_functional_mem_gamma_local (x : H))

/-- Helper for Proposition 14 11: support functions are positively homogeneous. -/
private lemma supportFunction_positivelyHomogeneous_local
    (C : Set H) :
    PositivelyHomogeneous (σ[C]) := by
  intro a ha u
  -- Evaluate the Chapter 7 support-function scaling identity at `u`.
  simpa [Function.comp, EReal.real_smul_def] using
    congrFun (supportFunction_comp_pos_smul_eq_mul_supportFunction (C := C) ha) u

/-- Helper for Proposition 14 11: the packaged support function of a nonempty set belongs to
`Γ₀(H)`. -/
private lemma supportFunction_mem_gammaZero_of_nonempty_local
    {C : Set H} (hC_nonempty : C.Nonempty) :
    properIoi (σ[C]) (isProper_supportFunction_of_nonempty C hC_nonempty) ∈ Γ₀(H) := by
  -- Upgrade the raw `Γ(H)` support-function owner through the canonical proper packaging.
  exact properIoi_mem_gammaZero_of_mem_gamma
    (isProper_supportFunction_of_nonempty C hC_nonempty)
    (supportFunction_mem_gamma_local C)

/-- Helper for Proposition 14 11: the indicator of a nonempty closed convex set belongs to
`Γ₀(H)`. -/
private theorem indicator_mem_gammaZero_of_nonempty_isClosed_convex_local
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    ι[C] ∈ Γ₀(H) := by
  have hindicator_lsc :
      LowerSemicontinuous (fun y ↦ ((ι[C]) y : EReal)) := by
    -- Closedness gives lower semicontinuity of the indicator.
    simpa using (lowerSemicontinuous_indicator_compl_top_iff_isClosed C).2 hC_closed
  have hdom : effectiveDomain (ι[C]) = C := by
    ext y
    by_cases hy : y ∈ C <;> simp [ERealFunction.effectiveDomain, ERealFunction.indicator, hy]
  refine ⟨hindicator_lsc, ?_⟩
  refine ⟨by simpa [hdom] using hC_nonempty, fun _ hy ↦ hy, ?_⟩
  intro y hy z hz a ha0 ha1
  have hyC : y ∈ C := by
    simpa [hdom] using hy
  have hzC : z ∈ C := by
    simpa [hdom] using hz
  -- Convexity of the feasible set is exactly the Jensen step for the indicator.
  have hayzC : a • y + (1 - a) • z ∈ C :=
    hC_convex hyC hzC ha0.le (sub_nonneg.mpr ha1.le) (by ring)
  simp [ERealFunction.indicator, hyC, hzC, hayzC]

/-- Helper for Proposition 14 11: once the support-function identity is available, the
linear-minorant set automatically supplies the full textbook clause `(ii)`. -/
theorem supportFunction_linearMinorantSet_data_of_positivelyHomogeneous_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)}
    (hph : PositivelyHomogeneous f.asEReal) (hf : f ∈ Γ₀(H)) :
    f.asEReal = σ[linearMinorantSet f] ∧
      (linearMinorantSet f).Nonempty ∧
      IsClosed (linearMinorantSet f) ∧
      Convex ℝ (linearMinorantSet f) := by
  -- The support-function identity is the owner theorem; the remaining data come from the
  -- indicator description of the conjugate.
  have h0 : (f 0 : EReal) = 0 :=
    value_zero_eq_zero_of_positivelyHomogeneous_mem_gammaZero hph hf
  have hconj :
      f.asEReal∗ = (ι[linearMinorantSet f]).asEReal :=
    conjugate_eq_indicator_linearMinorantSet_of_value_zero_of_positivelyHomogeneous h0 hph
  have hsupport :
      f.asEReal = σ[linearMinorantSet f] :=
    asEReal_eq_supportFunction_linearMinorantSet_of_positivelyHomogeneous_mem_gammaZero hph hf
  have hdom_eq :
      effectiveDomain (f∗[hf]) = linearMinorantSet f := by
    ext u
    rw [mem_effectiveDomain_iff, gammaZeroConjugate_apply, hconj]
    by_cases hu : u ∈ linearMinorantSet f <;> simp [indicator_apply, hu]
  have hnonempty : (linearMinorantSet f).Nonempty := by
    simpa [hdom_eq] using (gammaZeroConjugate_mem_gammaZero hf).2.nonempty
  exact ⟨hsupport, hnonempty, isClosed_linearMinorantSet f, convex_linearMinorantSet f⟩

-- Proof sketch: `(i) → (ii)` identifies the conjugate of `f.asEReal` with the indicator of
-- `linearMinorantSet f`, then applies Fenchel--Moreau and the Chapter 12 closed-convex indicator
-- criterion. `(ii) → (iii)` is the existential reformulation taking `D = linearMinorantSet f`.
-- `(iii) → (i)` uses the standard support-function facts: support functions are positively
-- homogeneous, and the indicator of a nonempty closed convex set belongs to `Γ₀(H)`, so its
-- conjugate support function does as well.
/-- Proposition 14.11: let
`C = {u | ∀ x, ⟪x, u⟫ ≤ f x}`, written here as `linearMinorantSet f`. Then the following
are equivalent: (i) `f` is positively homogeneous and `f ∈ Γ₀(H)`; (ii)
`f = σ[C]` and `C` is nonempty, closed, and convex; (iii) `f` is the support function of a
nonempty closed convex subset of `H`. Equivalently, the source-defined set `C` is the zero lower
level set of the affine-defect supremum `u ↦ sup_x (⟪x, u⟫ - f x)`. -/
theorem supportFunction_tfae_positivelyHomogeneous_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) :
    List.TFAE
      [ PositivelyHomogeneous f.asEReal ∧ f ∈ Γ₀(H),
        f.asEReal = σ[linearMinorantSet f] ∧
          (linearMinorantSet f).Nonempty ∧
          IsClosed (linearMinorantSet f) ∧
          Convex ℝ (linearMinorantSet f),
        ∃ D : Set H, f.asEReal = σ[D] ∧ D.Nonempty ∧ IsClosed D ∧ Convex ℝ D ] := by
  tfae_have 1 → 2 := by
    rintro ⟨hph, hf⟩
    exact supportFunction_linearMinorantSet_data_of_positivelyHomogeneous_mem_gammaZero hph hf
  tfae_have 2 → 3 := by
    rintro ⟨hsupport, hnonempty, hclosed, hconvex⟩
    exact ⟨linearMinorantSet f, hsupport, hnonempty, hclosed, hconvex⟩
  tfae_have 3 → 1 := by
    rintro ⟨D, hsupport, hD_nonempty, _hD_closed, _hD_convex⟩
    have hph : PositivelyHomogeneous f.asEReal := by
      simpa [hsupport] using supportFunction_positivelyHomogeneous_local D
    have hpack :
        f = properIoi (σ[D]) (isProper_supportFunction_of_nonempty D hD_nonempty) := by
      funext x
      apply Subtype.ext
      exact congrFun hsupport x
    have hf : f ∈ Γ₀(H) := by
      simpa [hpack] using supportFunction_mem_gammaZero_of_nonempty_local (C := D) hD_nonempty
    exact ⟨hph, hf⟩
  tfae_finish

/-- Source-facing clause `(i) → (ii)`: if `f ∈ Γ₀(H)` is positively homogeneous, then `f`
is the support function of the source-defined set `linearMinorantSet f`, equivalently of the zero
lower level set of the affine-defect supremum `u ↦ sup_x (⟪x, u⟫ - f x)`, and that set is
nonempty, closed, and convex. -/
theorem eq_supportFunction_linearMinorantSet_of_positivelyHomogeneous_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)}
    (hph : PositivelyHomogeneous f.asEReal) (hf : f ∈ Γ₀(H)) :
    f.asEReal = σ[linearMinorantSet f] ∧
      (linearMinorantSet f).Nonempty ∧
      IsClosed (linearMinorantSet f) ∧
      Convex ℝ (linearMinorantSet f) := by
  -- This is exactly the clause `(i) → (ii)` already extracted above.
  exact supportFunction_linearMinorantSet_data_of_positivelyHomogeneous_mem_gammaZero hph hf

end SupportFunctionCharacterization

end

end ERealFunction
