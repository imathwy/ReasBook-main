import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Div
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open scoped Rockafellar
open scoped Pointwise
open Function

variable {E : Type*}
variable {𝕜 : Type*}
variable {α : Type*}

local notation "𝕜≥0" => Set.Ici (0 : 𝕜)
attribute [local instance] Classical.propDecidable

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.4.3 computes the right scalar multiple from Text 5.4.2 in the
  positive-scalar case and at zero.
- `core/canonical`: the owner abstraction is the scaled-epigraph vertical-infimum operation
  `rightScalarMul` already introduced in `Text_5_4_2`, together with the chapter indicator owner
  `indicator`, used on the source-facing theorem surface through the notation
  `δ(· | ({0} : Set E))`.
- `bridge/view`: for a positive scalar, the scaled-epigraph vertical infimum simplifies to the
  explicit rescaling formula `x ↦ a * f (a⁻¹ • x)`; at zero, the scaled epigraph collapses to the
  origin indicator `δ(· | ({0} : Set E))` unless `f` is identically `⊤`, in which case it stays
  identically `⊤`.
- Primitive data vs derived API: `rightScalarMul` is primitive; the positive-scalar formula and
  the zero-scalar identification with the canonical origin indicator are derived API, and the
  pointwise evaluation theorem is recorded directly through that same indicator notation.
- Redundant-source-assumption elimination: the source assumes `f` is convex, but these
  identification formulas depend only on the scaled-epigraph construction itself, not on
  convexity.

Domain-style sampling used here:
- `rightScalarMul`;
- `rightScalarMul_eq_sInf`;
- `epi`;
- `Function.verticalInfimum` from `Theorem_5_3`;
- `indicator` and the notation `δ(· | C)` from `Defintion_4_8_1`.
- Ambient minimization: the file is expressed over a general ordered scalar `𝕜`; no theorem
  surface is pinned to `ℝ`.
-/

section

variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [MulAction 𝕜 E]

/-- Text 5.4.3 (1): for a positive scalar `a`, the right scalar multiple is given pointwise by
`x ↦ a * f (a⁻¹ • x)`. -/
theorem rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos
    (f : E → WithBotTop 𝕜) {a : 𝕜} (ha : 0 < a) (x : E) :
    ((⟨a, ha.le⟩ : 𝕜≥0) •ʳ f) x = a * f (a⁻¹ • x) := by
  have hscaled :
      ((a : 𝕜) • epi f : Set (E × 𝕜)) =
        epi (fun y ↦ (a : WithBotTop 𝕜) * f (a⁻¹ • y)) := by
    ext p
    rcases p with ⟨y, μ⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ ha.ne']
    rw [mem_epi_iff, mem_epi_iff]
    change f (a⁻¹ • y) ≤ a⁻¹ * μ ↔ (a : WithBotTop 𝕜) * f (a⁻¹ • y) ≤ μ
    set z := f (a⁻¹ • y)
    cases z using WithBotTop.rec with
    | bot =>
        rw [WithBotTop.coe_mul_bot_of_pos ha]
        simp
    | top =>
        have hlhs : ¬ ⊤ ≤ (WithBotTop.coe a)⁻¹ * WithBotTop.coe μ := by
          intro h
          have : (WithBotTop.coe a)⁻¹ * WithBotTop.coe μ = (⊤ : WithBotTop 𝕜) :=
            top_le_iff.mp h
          have hEq : (WithBotTop.coe a)⁻¹ * WithBotTop.coe μ =
              (((a⁻¹ * μ : 𝕜)) : WithBotTop 𝕜) := by
            conv_lhs => rw [← WithBotTop.coe_inv a, ← WithBotTop.coe_mul]
          rw [hEq] at this
          exact (WithBotTop.coe_ne_top (a⁻¹ * μ)) this
        constructor
        · intro h
          exact (hlhs h).elim
        · intro h
          rw [WithBotTop.coe_mul_top_of_pos ha] at h
          simp at h
    | coe r =>
        constructor
        · intro h
          rw [← WithBotTop.coe_mul] at h
          have hmulinv : r ≤ a⁻¹ * μ := WithBotTop.coe_le_coe.mp h
          have hdiv : r ≤ μ / a := by
            simpa [div_eq_mul_inv, mul_comm] using hmulinv
          exact WithBotTop.coe_le_coe.mpr <|
            by simpa [mul_comm] using (le_div_iff₀' ha).mp hdiv
        · intro h
          rw [← WithBotTop.coe_mul] at h
          have hmul : a * r ≤ μ := WithBotTop.coe_le_coe.mp h
          have hdiv : r ≤ μ / a := (le_div_iff₀' ha).mpr <|
            by simpa [mul_comm] using hmul
          have hmulinv : r ≤ a⁻¹ * μ := by
            simpa [div_eq_mul_inv, mul_comm] using hdiv
          exact (WithBotTop.coe_le_coe.mpr hmulinv :
            (r : WithBotTop 𝕜) ≤ ((a⁻¹ * μ : 𝕜) : WithBotTop 𝕜))
  calc
    ((⟨a, ha.le⟩ : 𝕜≥0) •ʳ f) x = Function.verticalInfimum (((a : 𝕜) • epi f) : Set (E × 𝕜)) x :=
      rfl
    _ = Function.verticalInfimum (epi (fun y ↦ (a : WithBotTop 𝕜) * f (a⁻¹ • y))) x := by
      rw [hscaled]
    _ = a * f (a⁻¹ • x) := by
      simp

end

section

variable [Monoid 𝕜] [Preorder 𝕜] [Zero 𝕜] [ZeroLEOneClass 𝕜]
variable [ConditionallyCompleteLattice α] [NoBotOrder α]
variable [MulAction 𝕜 E] [MulAction 𝕜 α]

/-- The unit right scalar multiple recovers the original function. -/
@[simp] theorem rightScalarMul_one (f : E → WithBotTop α) :
    ((⟨1, zero_le_one⟩ : 𝕜≥0) •ʳ f) = f := by
  have hs : (1 : 𝕜) • (epi[Set.univ] f : Set (E × α)) = epi[Set.univ] f := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rw [mem_epi_iff] at hq ⊢
      simpa using hq
    · intro hp
      refine ⟨p, hp, ?_⟩
      ext <;> simp
  change Function.verticalInfimum ((1 : 𝕜) • (epi[Set.univ] f : Set (E × α))) = f
  rw [hs]
  exact Function.verticalInfimum_epi f

end

section

variable [Preorder 𝕜] [Zero 𝕜]
variable [ConditionallyCompleteLattice α]
variable [Zero E] [Zero α]
variable [SMulWithZero 𝕜 E] [SMulWithZero 𝕜 α]

/-- Canonical epigraph-owner form of Text 5.4.3 (2): if `epi f` is nonempty, then `0 •ʳ f`
is the canonical indicator of the origin. -/
theorem rightScalarMul_zero_eq_indicator_zero_of_epi_nonempty
    (f : E → WithBotTop α) (hepi : (epi f).Nonempty) :
    ((⟨0, le_rfl⟩ : 𝕜≥0) •ʳ f) = (δ(· | ({0} : Set E))) := by
  have hzeroepi : ((0 : 𝕜) • epi f : Set (E × α)) = 0 := Set.zero_smul_set hepi
  ext x
  by_cases hx : x = 0
  · subst hx
    rw [Function.rightScalarMul_eq_sInf]
    simp [Function.verticalHeights, Function.verticalSection, hzeroepi]
  · rw [Function.rightScalarMul_eq_sInf]
    simp [Function.verticalHeights, Function.verticalSection, hzeroepi, hx]

/-- Text 5.4.3 (2): if `f` is not identically `⊤`, then `0 •ʳ f` is the
canonical indicator of the origin. -/
theorem rightScalarMul_zero_eq_indicator_zero_of_ne_top
    (f : E → WithBotTop α) (hf : f ≠ ⊤) :
    ((⟨0, le_rfl⟩ : 𝕜≥0) •ʳ f) = (δ(· | ({0} : Set E))) := by
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ ⊤ := by
    by_contra h
    apply hf
    funext y
    exact by simpa using not_exists.mp h y
  have hepi : (epi f).Nonempty := by
    by_cases hbot : f y = ⊥
    · refine ⟨(y, 0), ?_⟩
      simp [hbot]
    · lift f y to α using ⟨hy, hbot⟩ with a ha
      refine ⟨(y, a), ?_⟩
      simp [ha]
  exact rightScalarMul_zero_eq_indicator_zero_of_epi_nonempty f hepi

/-- Pointwise canonical epigraph-owner form of Text 5.4.3 (2). -/
theorem rightScalarMul_zero_apply_eq_origin_indicator_of_epi_nonempty
    (f : E → WithBotTop α) (hepi : (epi f).Nonempty) (x : E) :
    (((⟨0, le_rfl⟩ : 𝕜≥0) •ʳ f) x) = δ(x | ({0} : Set E)) := by
  simpa using congrFun (rightScalarMul_zero_eq_indicator_zero_of_epi_nonempty f hepi) x

/-- Pointwise form of Text 5.4.3 (2): if `f` is not identically `⊤`, then the zero right scalar
multiple is the canonical origin indicator. -/
theorem rightScalarMul_zero_apply_eq_origin_indicator_of_ne_top
    (f : E → WithBotTop α) (hf : f ≠ ⊤) (x : E) :
    (((⟨0, le_rfl⟩ : 𝕜≥0) •ʳ f) x) = δ(x | ({0} : Set E)) := by
  simpa using congrFun (rightScalarMul_zero_eq_indicator_zero_of_ne_top f hf) x

end

section

variable [Preorder 𝕜] [Zero 𝕜]
variable [ConditionallyCompleteLattice α]
variable [SMul 𝕜 E] [SMul 𝕜 α]

/-- Canonical epigraph-owner form of Text 5.4.3 (3): if `epi f = ∅`, then `0 •ʳ f = f`. -/
theorem rightScalarMul_zero_eq_self_of_epi_eq_empty
    (f : E → WithBotTop α) (hepi : (epi f : Set (E × α)) = ∅) :
    ((⟨0, le_rfl⟩ : 𝕜≥0) •ʳ f) = f := by
  ext x
  rw [Function.rightScalarMul_eq_sInf, hepi, Set.smul_set_empty]
  have htop : f x = ⊤ := by
    by_contra hxtop
    by_cases hbot : f x = ⊥
    · let a0 : α := sInf (Set.univ : Set α)
      have hmem : (x, a0) ∈ (epi f : Set (E × α)) := by
        simp [hbot]
      simp [hepi] at hmem
    · lift f x to α using ⟨hxtop, hbot⟩ with a ha
      have hmem : (x, a) ∈ (epi f : Set (E × α)) := by
        simp [ha]
      simp [hepi] at hmem
  rw [htop]
  simp [Function.verticalHeights, Function.verticalSection]

/-- Text 5.4.3 (3): if `f` is identically `⊤`, then `0 •ʳ f = f`. -/
theorem rightScalarMul_zero_eq_self_of_eq_top
    (f : E → WithBotTop α) (hf : f = ⊤) :
    ((⟨0, le_rfl⟩ : 𝕜≥0) •ʳ f) = f := by
  have hepi : (epi f : Set (E × α)) = ∅ := by
    rw [hf]
    ext p
    rcases p with ⟨x, a⟩
    simp
  simpa using rightScalarMul_zero_eq_self_of_epi_eq_empty f hepi

end

end
