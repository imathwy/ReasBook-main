import Mathlib
import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap02.Definition_2_29
import BauschkeLean.Chap02.Text_2_0_14
import BauschkeLean.Chap02.Fact_2_35
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section SubdifferentialBasicProperties

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Proposition 16 4: outside the effective domain of an `]-∞,+∞]`-valued function,
the value is necessarily `⊤`. -/
private theorem value_eq_top_of_not_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∉ effectiveDomain f) :
    (f x : EReal) = ⊤ := by
  -- A finite value would put `x` back into the effective domain.
  by_contra htop
  exact hx (mem_effectiveDomain_iff.mpr (lt_of_le_of_ne le_top htop))

-- Proof sketch: choose a point `y` in the effective domain. If `u ∈ subdifferential f x`, then
-- the defining inequality with that `y` forces `(f x : EReal) < ⊤`.
/-- Proposition 16 4 (1): if `f` has a nonempty effective domain, then every point at which the
subdifferential is nonempty lies in the effective domain. For `]-∞,+∞]`-valued functions, this is
the remaining properness content after excluding `-∞` by the codomain. -/
theorem subdifferential_domain_subset_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain f).Nonempty) :
    SetValuedOperator.dom (∂ f) ⊆ effectiveDomain f := by
  intro x hx
  rcases hdom with ⟨y, hy⟩
  rw [SetValuedOperator.mem_dom_iff] at hx
  rcases hx with ⟨u, hu⟩
  by_contra hx_not_mem
  have hx_top : (f x : EReal) = ⊤ := value_eq_top_of_not_mem_effectiveDomain hx_not_mem
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  -- Evaluating the subgradient inequality at a finite-domain point forces `f x` to be finite.
  have hxy : (⊤ : EReal) ≤ (f y : EReal) := by
    have hxy₀ : (⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal) := hu y
    rw [hx_top] at hxy₀
    simpa using hxy₀
  exact hy_top (le_antisymm le_top hxy)

/-- Pointwise form of Proposition 16 4 (1): subdifferentiability forces effective-domain
membership. -/
theorem SubdifferentiableAt.mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hdom : (effectiveDomain f).Nonempty) {x : H}
    (hx : SubdifferentiableAt f x) :
    x ∈ effectiveDomain f := by
  -- Clause (1) applies directly to the subdifferential domain point `x`.
  exact subdifferential_domain_subset_effectiveDomain f hdom hx

/-- Helper for Proposition 16 4: at finite points, the affine `EReal` subgradient inequality is
equivalent to the corresponding real half-space inequality. -/
private theorem ereal_affine_ineq_iff_inner_le_toReal_sub
    {f : H → Set.Ioi (⊥ : EReal)} {x y u : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) :
    (((⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal)) ↔
      (⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal)) := by
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hsub :
      (((f y : EReal).toReal - (f x : EReal).toReal : ℝ) : EReal) =
        (f y : EReal) - (f x : EReal) := by
    -- Replace the two finite `EReal` values by their real representatives once and for all.
    calc
      (((f y : EReal).toReal - (f x : EReal).toReal : ℝ) : EReal) =
          (((f y : EReal).toReal : EReal) - (((f x : EReal).toReal : EReal))) := by
            rw [EReal.coe_sub]
      _ = (f y : EReal) - (f x : EReal) := by
        rw [EReal.coe_toReal hy_top hy_bot, EReal.coe_toReal hx_top hx_bot]
  constructor
  · intro hineq
    -- Move the finite value `f x` to the right-hand side inside `EReal`.
    have hsubineq : (⟪y - x, u⟫_ℝ : EReal) ≤ (f y : EReal) - (f x : EReal) := by
      exact (EReal.le_sub_iff_add_le (.inl hx_bot) (.inl hx_top)).2 hineq
    have hcast :
        (⟪y - x, u⟫_ℝ : EReal) ≤
          (((f y : EReal).toReal - (f x : EReal).toReal : ℝ) : EReal) := by
      simpa [hsub] using hsubineq
    exact_mod_cast hcast
  · intro hineq
    -- Cast the real half-space inequality back to `EReal` and undo the subtraction step.
    have hcast :
        (⟪y - x, u⟫_ℝ : EReal) ≤
          (((f y : EReal).toReal - (f x : EReal).toReal : ℝ) : EReal) := by
      exact_mod_cast hineq
    have hsubineq : (⟪y - x, u⟫_ℝ : EReal) ≤ (f y : EReal) - (f x : EReal) := by
      simpa [hsub] using hcast
    exact (EReal.le_sub_iff_add_le (.inl hx_bot) (.inl hx_top)).1 hsubineq

/-- Helper for Proposition 16 4: at a finite point `x`, subgradient membership is equivalent to
the family of affine half-space inequalities indexed by the effective domain. -/
private theorem mem_subdifferential_iff_forall_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {x u : H} (hx : x ∈ effectiveDomain f) :
    u ∈ (∂ f) x ↔
      ∀ y ∈ effectiveDomain f,
        ⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal := by
  -- Route correction: isolate the finite-value `EReal`/`toReal` transport in one adapter lemma,
  -- then use it uniformly in both directions of the subgradient rewrite.
  constructor
  · intro hu y hy
    -- On the effective domain, the global subgradient inequality is exactly the affine half-space
    -- inequality after converting finite `EReal` values to real numbers.
    exact
      (ereal_affine_ineq_iff_inner_le_toReal_sub hx hy).1
        ((mem_subdifferential_iff _ _ _).1 hu y)
  · intro hu
    rw [mem_subdifferential_iff]
    intro y
    by_cases hy : y ∈ effectiveDomain f
    · -- The finite branch is the adapter lemma in the reverse direction.
      exact (ereal_affine_ineq_iff_inner_le_toReal_sub hx hy).2 (hu y hy)
    · -- Outside the effective domain, the target value is `⊤`, so the inequality is automatic.
      have hy_top : (f y : EReal) = ⊤ := value_eq_top_of_not_mem_effectiveDomain hy
      change ((⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal))
      rw [hy_top]
      exact le_top

-- Proof sketch: rewrite `u ∈ subdifferential f x` using the defining affine-minorant inequality,
-- then move the finite value `(f x : EReal)` to the right-hand side for each `y ∈ effectiveDomain
-- f`.
/-- Proposition 16 4 (2): at a point of the effective domain, the subdifferential is the
intersection of the affine half-spaces cut out by the subgradient inequalities over the effective
domain. -/
theorem subdifferential_eq_iInter_affine_halfspaces
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) (hx : x ∈ effectiveDomain f) :
    (∂ f) x =
      ⋂ y ∈ effectiveDomain f,
        {u : H | ⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal} := by
  ext u
  -- Clause (2) is just the set-level version of the pointwise membership rewrite.
  rw [Set.mem_iInter₂]
  exact mem_subdifferential_iff_forall_mem_effectiveDomain hx

/-- Helper for Proposition 16 4: outside the effective domain, the subdifferential is either empty
or all of `H`, depending on whether the effective domain itself is nonempty. -/
private theorem subdifferential_eq_empty_or_univ_of_not_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∉ effectiveDomain f) :
    (∂ f) x = ∅ ∨ (∂ f) x = Set.univ := by
  by_cases hdom : (effectiveDomain f).Nonempty
  · left
    ext u
    constructor
    · intro hu
      -- If the effective domain is nonempty, clause (1) forbids any subgradient outside it.
      have hx_dom : x ∈ SetValuedOperator.dom (∂ f) := by
        rw [SetValuedOperator.mem_dom_iff]
        exact ⟨u, hu⟩
      exact False.elim (hx (subdifferential_domain_subset_effectiveDomain f hdom hx_dom))
    · intro hu
      exact hu.elim
  · right
    ext u
    constructor
    · intro _
      simp
    · intro _
      rw [mem_subdifferential_iff]
      intro y
      have hy_not_mem : y ∉ effectiveDomain f := by
        intro hy
        exact hdom ⟨y, hy⟩
      have hy_top : (f y : EReal) = ⊤ := value_eq_top_of_not_mem_effectiveDomain hy_not_mem
      -- When the effective domain is empty, every value is `⊤`, so every affine inequality holds.
      change ((⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal))
      rw [hy_top]
      exact le_top

/-- Helper for Proposition 16 4: each affine subgradient half-space is closed. -/
private theorem isClosed_subgradient_halfspace
    {x y : H} {c : ℝ} :
    IsClosed ({u : H | ⟪y - x, u⟫_ℝ ≤ c} : Set H) := by
  -- The half-space is the preimage of `Iic c` under the continuous functional
  -- `u ↦ ⟪y - x, u⟫`.
  simpa using isClosed_le (continuous_const.inner continuous_id) continuous_const

/-- Helper for Proposition 16 4: each affine subgradient half-space is convex. -/
private theorem convex_subgradient_halfspace
    {x y : H} {c : ℝ} :
    Convex ℝ ({u : H | ⟪y - x, u⟫_ℝ ≤ c} : Set H) := by
  rw [convex_iff_forall_pos]
  intro u hu v hv a b ha hb hab
  have hcombo :
      ⟪y - x, a • u + b • v⟫_ℝ = a * ⟪y - x, u⟫_ℝ + b * ⟪y - x, v⟫_ℝ := by
    rw [inner_add_right, inner_smul_right, inner_smul_right]
  have hle : a * ⟪y - x, u⟫_ℝ + b * ⟪y - x, v⟫_ℝ ≤ c := by
    have ha0 : 0 ≤ a := le_of_lt ha
    have hb0 : 0 ≤ b := le_of_lt hb
    have hscaled :
        a * ⟪y - x, u⟫_ℝ + b * ⟪y - x, v⟫_ℝ ≤ a * c + b * c := by
      exact add_le_add (mul_le_mul_of_nonneg_left hu ha0) (mul_le_mul_of_nonneg_left hv hb0)
    have hsum : a * c + b * c = c := by
      calc
        a * c + b * c = (a + b) * c := by ring
        _ = c := by rw [hab, one_mul]
    exact hscaled.trans_eq hsum
  -- Expanding the inner product of the convex combination puts the goal into the linear form
  -- handled by the scalar inequality above.
  simpa [hcombo, smul_eq_mul] using hle

-- Proof sketch: if `x ∈ effectiveDomain f`, use the half-space description from clause (2). Each
-- defining set is closed, and arbitrary intersections of closed sets are closed. If
-- `x ∉ effectiveDomain f`, then `(∂ f) x` is either `∅` or `Set.univ`, hence closed.
/-- Proposition 16 4 (3): the subdifferential is closed at every point. -/
theorem isClosed_subdifferential
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) :
    IsClosed ((∂ f) x) := by
  by_cases hx : x ∈ effectiveDomain f
  · -- On the effective domain, clause (2) writes the fiber as an intersection of closed
    -- half-spaces.
    rw [subdifferential_eq_iInter_affine_halfspaces f x hx]
    exact isClosed_iInter fun y ↦ isClosed_iInter fun _ ↦ isClosed_subgradient_halfspace
  · -- Outside the effective domain, the fiber is either `∅` or `univ`.
    rcases subdifferential_eq_empty_or_univ_of_not_mem_effectiveDomain hx with hempty | huniv
    · rw [hempty]
      exact isClosed_empty
    · rw [huniv]
      exact isClosed_univ

-- Proof sketch: if `x ∈ effectiveDomain f`, use the half-space description from clause (2). Each
-- defining set is convex, and arbitrary intersections of convex sets are convex. If
-- `x ∉ effectiveDomain f`, then `(∂ f) x` is either `∅` or `Set.univ`, hence convex.
/-- Proposition 16 4 (4): the subdifferential is convex at every point. -/
theorem convex_subdifferential
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) :
    Convex ℝ ((∂ f) x) := by
  by_cases hx : x ∈ effectiveDomain f
  · -- On the effective domain, clause (2) writes the fiber as an intersection of convex
    -- half-spaces.
    rw [subdifferential_eq_iInter_affine_halfspaces f x hx]
    exact convex_iInter₂ fun y _ ↦ convex_subgradient_halfspace
  · -- Outside the effective domain, the fiber is either `∅` or `univ`.
    rcases subdifferential_eq_empty_or_univ_of_not_mem_effectiveDomain hx with hempty | huniv
    · rw [hempty]
      exact convex_empty
    · rw [huniv]
      exact convex_univ

-- Proof sketch: pick `u ∈ subdifferential f x`; the subgradient inequality gives
-- `f x ≤ f y - ⟪y - x, u⟫`, and continuity of the affine term transfers this to the liminf
-- characterization of lower semicontinuity at `x`.
/-- Proposition 16 4 (5): if the subdifferential of `f` at `x` is nonempty, then `f` is
lower semicontinuous at `x`. -/
theorem SubdifferentiableAt.lowerSemicontinuousAt
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hxsub : SubdifferentiableAt f x) :
    LowerSemicontinuousAt f.asEReal x := by
  by_cases hdom : (effectiveDomain f).Nonempty
  · rcases hxsub with ⟨u, hu⟩
    have hx : x ∈ effectiveDomain f := SubdifferentiableAt.mem_effectiveDomain hdom ⟨u, hu⟩
    have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    let g : H → EReal := fun y ↦
      ((⟪y - x, u⟫_ℝ + (f x : EReal).toReal : ℝ) : EReal)
    have hg_le : g ≤ f.asEReal := by
      intro y
      -- The affine minorant is exactly the defining subgradient lower bound after freezing the
      -- finite value `f x`.
      have hg_eq : g y = ((⟪y - x, u⟫_ℝ : EReal) + (f x : EReal)) := by
        calc
          g y = (((⟪y - x, u⟫_ℝ + (f x : EReal).toReal : ℝ) : EReal)) := rfl
          _ = ((⟪y - x, u⟫_ℝ : EReal) + (((f x : EReal).toReal : ℝ) : EReal)) := by
            rw [EReal.coe_add]
          _ = ((⟪y - x, u⟫_ℝ : EReal) + (f x : EReal)) := by
            rw [EReal.coe_toReal hx_top hx_bot]
      rw [hg_eq]
      simpa [Function.asEReal_apply] using hu y
    have hgx : g x = f.asEReal x := by
      -- At the touching point `x`, the affine minorant agrees with `f`.
      calc
        g x = (((0 : ℝ) + (f x : EReal).toReal : ℝ) : EReal) := by
          simp [g]
        _ = (((f x : EReal).toReal : ℝ) : EReal) := by simp
        _ = f.asEReal x := by
          simpa [Function.asEReal_apply] using EReal.coe_toReal hx_top hx_bot
    have hg_cont : ContinuousAt g x := by
      have hreal_cont :
          ContinuousAt (fun y : H ↦ ⟪y - x, u⟫_ℝ + (f x : EReal).toReal) x := by
        exact (((continuous_id.sub continuous_const).inner continuous_const).continuousAt).add
          continuousAt_const
      exact continuous_coe_real_ereal.continuousAt.comp hreal_cont
    rw [lowerSemicontinuousAt_iff_le_liminf]
    calc
      f.asEReal x = g x := hgx.symm
      _ ≤ Filter.liminf g (nhds x) := hg_cont.lowerSemicontinuousAt.le_liminf
      _ ≤ Filter.liminf f.asEReal (nhds x) := by
        exact Filter.liminf_le_liminf
          (show ∀ᶠ y in nhds x, g y ≤ f.asEReal y from Filter.Eventually.of_forall hg_le)
  · have hconst : f.asEReal = fun _ : H ↦ (⊤ : EReal) := by
      funext y
      have hy : y ∉ effectiveDomain f := by
        intro hy
        exact hdom ⟨y, hy⟩
      exact value_eq_top_of_not_mem_effectiveDomain hy
    -- If the effective domain is empty, `f` is the constant `⊤` function, hence trivially lsc.
    simpa [hconst] using
      (continuousAt_const : ContinuousAt (fun _ : H ↦ (⊤ : EReal)) x).lowerSemicontinuousAt

-- Proof sketch: first obtain ordinary lower semicontinuity at `x` from clause (5). Then view the
-- same subgradient inequality on `WeakSpace ℝ H`; the affine functional remains weakly continuous,
-- so the same liminf argument yields weak lower semicontinuity.
/-- Proposition 16 4 (6): if the subdifferential of `f` at `x` is nonempty, then `f` is
weakly lower semicontinuous at `x`. -/
theorem SubdifferentiableAt.weaklyLowerSemicontinuousAt
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hxsub : SubdifferentiableAt f x) :
    WeaklyLowerSemicontinuousAt f.asEReal x := by
  change LowerSemicontinuousAt (f.asEReal ∘ (toWeakSpace ℝ H).symm) (toWeakSpace ℝ H x)
  by_cases hdom : (effectiveDomain f).Nonempty
  · rcases hxsub with ⟨u, hu⟩
    have hx : x ∈ effectiveDomain f := SubdifferentiableAt.mem_effectiveDomain hdom ⟨u, hu⟩
    have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    let g : WeakSpace ℝ H → EReal := fun z ↦
      ((⟪(toWeakSpace ℝ H).symm z, u⟫_ℝ - ⟪x, u⟫_ℝ + (f x : EReal).toReal : ℝ) : EReal)
    have hg_le : g ≤ f.asEReal ∘ (toWeakSpace ℝ H).symm := by
      intro z
      -- Rewriting `⟪y - x, u⟫` as `⟪y, u⟫ - ⟪x, u⟫` turns the weak affine minorant back into the
      -- defining subgradient inequality at the point `y = (toWeakSpace ℝ H).symm z`.
      have hg_eq :
          g z = ((⟪(toWeakSpace ℝ H).symm z - x, u⟫_ℝ : EReal) + (f x : EReal)) := by
        calc
          g z =
              (((⟪(toWeakSpace ℝ H).symm z, u⟫_ℝ - ⟪x, u⟫_ℝ + (f x : EReal).toReal : ℝ) :
                EReal)) := rfl
          _ =
              (((⟪(toWeakSpace ℝ H).symm z - x, u⟫_ℝ + (f x : EReal).toReal : ℝ) :
                EReal)) := by
                rw [inner_sub_left]
          _ =
              ((⟪(toWeakSpace ℝ H).symm z - x, u⟫_ℝ : EReal) +
                (((f x : EReal).toReal : ℝ) : EReal)) := by
                rw [EReal.coe_add]
          _ =
              ((⟪(toWeakSpace ℝ H).symm z - x, u⟫_ℝ : EReal) + (f x : EReal)) := by
                rw [EReal.coe_toReal hx_top hx_bot]
      rw [hg_eq]
      simpa [Function.comp, Function.asEReal_apply] using hu ((toWeakSpace ℝ H).symm z)
    have hgx : g (toWeakSpace ℝ H x) = (f x : EReal) := by
      -- The weak affine minorant also touches `f` at `x`.
      calc
        g (toWeakSpace ℝ H x) =
            (((0 : ℝ) + (f x : EReal).toReal : ℝ) : EReal) := by
              simp [g]
        _ = (((f x : EReal).toReal : ℝ) : EReal) := by simp
        _ = (f x : EReal) := EReal.coe_toReal hx_top hx_bot
    have hg_cont : ContinuousAt g (toWeakSpace ℝ H x) := by
      have hinner_cont :
          Continuous fun z : WeakSpace ℝ H ↦ inner ℝ ((toWeakSpace ℝ H).symm z) u := by
        have hcont_id : Continuous (fun z : WeakSpace ℝ H ↦ z) := continuous_id
        have hweak_eval :
            Continuous fun z : WeakSpace ℝ H ↦
              StrongDual.toWeakDual (innerSL ℝ u) ((toWeakSpace ℝ H).symm z) :=
          (continuous_iff_forall_weakDual_apply (f := fun z : WeakSpace ℝ H ↦ z)).1 hcont_id
            (StrongDual.toWeakDual (innerSL ℝ u))
        simpa [StrongDual.toWeakDual_apply, innerSL_apply_apply, real_inner_comm]
          using hweak_eval
      have hreal_cont :
          ContinuousAt
            (fun z : WeakSpace ℝ H ↦
              ⟪(toWeakSpace ℝ H).symm z, u⟫_ℝ - ⟪x, u⟫_ℝ + (f x : EReal).toReal)
            (toWeakSpace ℝ H x) := by
        exact (hinner_cont.continuousAt.sub continuousAt_const).add continuousAt_const
      exact continuous_coe_real_ereal.continuousAt.comp hreal_cont
    rw [lowerSemicontinuousAt_iff_le_liminf]
    calc
      (f.asEReal ∘ (toWeakSpace ℝ H).symm) (toWeakSpace ℝ H x) = g (toWeakSpace ℝ H x) := by
        simpa [Function.comp] using hgx.symm
      _ ≤ Filter.liminf g (nhds (toWeakSpace ℝ H x)) := hg_cont.lowerSemicontinuousAt.le_liminf
      _ ≤ Filter.liminf (f.asEReal ∘ (toWeakSpace ℝ H).symm) (nhds (toWeakSpace ℝ H x)) := by
        exact Filter.liminf_le_liminf
          (show ∀ᶠ z in nhds (toWeakSpace ℝ H x),
              g z ≤ (f.asEReal ∘ (toWeakSpace ℝ H).symm) z from
            Filter.Eventually.of_forall hg_le)
  · have hconst : f.asEReal ∘ (toWeakSpace ℝ H).symm = fun _ : WeakSpace ℝ H ↦ (⊤ : EReal) := by
      funext z
      have hz : (toWeakSpace ℝ H).symm z ∉ effectiveDomain f := by
        intro hz_mem
        exact hdom ⟨(toWeakSpace ℝ H).symm z, hz_mem⟩
      simpa [Function.comp] using value_eq_top_of_not_mem_effectiveDomain hz
    -- If the effective domain is empty, the weak owner is again the constant `⊤` function.
    simpa [hconst] using
      (continuousAt_const : ContinuousAt (fun _ : WeakSpace ℝ H ↦ (⊤ : EReal))
        (toWeakSpace ℝ H x)).lowerSemicontinuousAt

end SubdifferentialBasicProperties

end ERealFunction
