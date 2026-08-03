import BauschkeLean.Chap01.Text_1_0_31
import BauschkeLean.Chap09.Definition_9_2
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap13.Proposition_13_44
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap16.Proposition_16_5
import BauschkeLean.Chap16.Theorem_16_3
import BauschkeLean.Chap16.Proposition_16_10
import BauschkeLean.Chap19.Proposition_19_12
import BauschkeLean.Chap19.Theorem_19_1
import BauschkeLean.Chap19.Definition_19_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

section ParametricDuality

variable {H : Type u} {K : Type v}
variable (F : H × K → Set.Ioi (⊥ : EReal))

local notation "ϑ" => (Prod.snd ▷ F)

/- Source/core/bridge triage:
- `source-facing`: Proposition 19.14 relates dual minimizers of the perturbation problem to the
  subdifferential behavior of the value function at `0`.
- `core/canonical`: the owner declarations are the value function `ϑ = Prod.snd ▷ F`, together
  with `Argmin`, `∂`, `SubdifferentiableAt`, `LowerSemicontinuousAt`, and Fenchel biconjugation.
- `bridge/view`: `perturbationDualObjective F` is the Chapter 19 dual slice, identified with `ϑ∗`
  by Proposition 19.12.
-/

section Basic

variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Helper for Proposition 19.14: every dual minimizer yields a subgradient of the biconjugate of
the value function at the origin. -/
lemma mem_subdifferential_biconjugate_valueFunction_zero_of_mem_argmin_perturbationDualObjective
    {u : K} (hu : u ∈ Argmin (perturbationDualObjective F)) :
    u ∈ (∂ (ϑ∗∗)) 0 := by
  -- Rewrite `u` as an actual dual minimizer value, so Proposition 19.12 can identify the contact
  -- value `ϑ**(0)` with `-ϑ*(u)`.
  rw [mem_subdifferential_iff]
  intro y
  have hu_val : perturbationDualObjective F u = sInf (Set.range (perturbationDualObjective F)) :=
    mem_argmin_iff_eq_sInf.mp hu
  have hzero : ϑ∗∗ 0 = -(ϑ∗ u) := by
    calc
      ϑ∗∗ 0 = -sInf (Set.range (perturbationDualObjective F)) :=
        (neg_sInf_perturbationDualObjective_eq_biconjugate_valueFunction_zero F).symm
      _ = -(perturbationDualObjective F u) := by rw [hu_val]
      _ = -(ϑ∗ u) := by rw [← conjugate_valueFunction_eq_dualObjective (F := F)]
  have hy : (((⟪y, u⟫_ℝ : ℝ) : EReal) - ϑ∗ u) ≤ ϑ∗∗ y := by
    -- Evaluate the defining supremum for `ϑ**(y)` at the chosen minimizer `u`.
    rw [conjugate_apply]
    have : (((⟪u, y⟫_ℝ : ℝ) : EReal) - ϑ∗ u) ≤
        ⨆ v : K, (((⟪v, y⟫_ℝ : ℝ) : EReal) - ϑ∗ v) := by
      exact le_iSup (fun v : K ↦ (((⟪v, y⟫_ℝ : ℝ) : EReal) - ϑ∗ v)) u
    simpa [real_inner_comm] using this
  -- The minimizer value at `0` is exactly the affine intercept in the subgradient inequality.
  calc
    ((⟪y - 0, u⟫_ℝ : ℝ) : EReal) + ϑ∗∗ 0 =
        (((⟪y, u⟫_ℝ : ℝ) : EReal) + -(ϑ∗ u)) := by
      rw [hzero]
      simp
    _ = (((⟪y, u⟫_ℝ : ℝ) : EReal) - ϑ∗ u) := by
      rw [sub_eq_add_neg]
    _ ≤ ϑ∗∗ y := hy

/-- Helper for Proposition 19.14: a subgradient of the biconjugate at the origin bounds the
conjugate value by the negative contact value at `0`. -/
lemma conjugate_valueFunction_le_neg_biconjugate_zero_of_mem_subdifferential_biconjugate_zero
    {u : K} (hu : u ∈ (∂ (ϑ∗∗)) 0) :
    ϑ∗ u ≤ -(ϑ∗∗ 0) := by
  have hu0 : ∀ y : K, (((⟪y - (0 : K), u⟫_ℝ : ℝ) : EReal) + ϑ∗∗ 0) ≤ ϑ∗∗ y := hu
  by_cases hzero_bot : ϑ∗∗ 0 = ⊥
  · -- If the contact value is `-∞`, then the desired upper bound is the trivial `≤ ⊤` branch.
    rw [hzero_bot]
    exact le_top
  by_cases hzero_top : ϑ∗∗ 0 = ⊤
  · -- If the contact value is `+∞`, the subgradient inequality forces `ϑ∗∗ ≡ +∞`, so its
    -- conjugate, hence `ϑ∗`, is identically `-∞`.
    have hall_top : ∀ y : K, ϑ∗∗ y = ⊤ := by
      intro y
      have hy : (((⟪y, u⟫_ℝ : ℝ) : EReal) + ϑ∗∗ 0) ≤ ϑ∗∗ y := by
        simpa using hu0 y
      have hleft_top : (((⟪y, u⟫_ℝ : ℝ) : EReal) + ϑ∗∗ 0) = ⊤ := by
        rw [hzero_top]
        exact EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)
      rw [hleft_top] at hy
      exact le_antisymm le_top hy
    have htriple_bot : (ϑ∗∗)∗ u = ⊥ := by
      rw [conjugate_apply]
      refine le_antisymm ?_ bot_le
      refine iSup_le fun y ↦ ?_
      rw [hall_top y]
      simp
    have htriple_eq : (ϑ∗∗)∗ u = ϑ∗ u := by
      simpa using congrFun (triple_conjugate_eq_conjugate (f := ϑ)) u
    have hconj_bot : ϑ∗ u = ⊥ := by
      rw [← htriple_eq]
      exact htriple_bot
    rw [hzero_top]
    exact hconj_bot.le
  have htriple_main : (ϑ∗∗)∗ u ≤ -(ϑ∗∗ 0) := by
    rw [conjugate_apply]
    refine iSup_le fun y ↦ ?_
    by_cases hy_top : ϑ∗∗ y = ⊤
    · -- At a `+∞` branch, the affine defect is `-∞`, so the bound is automatic.
      rw [hy_top, EReal.sub_top]
      exact bot_le
    have hyineq : (((⟪y, u⟫_ℝ : ℝ) : EReal) + ϑ∗∗ 0) ≤ ϑ∗∗ y := by
      simpa using hu0 y
    have hy_bot : ϑ∗∗ y ≠ ⊥ := by
      intro hy_bot
      rw [hy_bot] at hyineq
      have hleft_ne_bot : (((⟪y, u⟫_ℝ : ℝ) : EReal) + ϑ∗∗ 0) ≠ ⊥ := by
        exact EReal.add_ne_bot_iff.2 ⟨EReal.coe_ne_bot _, hzero_bot⟩
      exact hleft_ne_bot (le_bot_iff.mp hyineq)
    have hdefect_le :
        ((⟪y, u⟫_ℝ : EReal)) ≤ ϑ∗∗ y - ϑ∗∗ 0 := by
      exact (EReal.le_sub_iff_add_le (.inl hzero_bot) (.inl hzero_top)).2 <| by
        simpa using hyineq
    exact
      (EReal.sub_le_iff_le_add (.inl hy_bot) (.inl hy_top)).2 <| by
        simpa [sub_eq_add_neg, add_comm] using hdefect_le
  have htriple_eq : (ϑ∗∗)∗ u = ϑ∗ u := by
    simpa using congrFun (triple_conjugate_eq_conjugate (f := ϑ)) u
  rw [← htriple_eq]
  exact htriple_main

/-- Helper for Proposition 19.14: a subgradient of the biconjugate at the origin is exactly a dual
minimizer. -/
lemma mem_argmin_perturbationDualObjective_of_mem_subdifferential_biconjugate_valueFunction_zero
    {u : K} (hu : u ∈ (∂ (ϑ∗∗)) 0) :
    u ∈ Argmin (perturbationDualObjective F) := by
  -- The source route is the zero-slope comparison: first bound `ϑ*(u)` by `-(ϑ**(0))`, then
  -- rewrite that contact value as the infimum of `ϑ*`.
  have hle :
      ϑ∗ u ≤ -(ϑ∗∗ 0) :=
    conjugate_valueFunction_le_neg_biconjugate_zero_of_mem_subdifferential_biconjugate_zero
      (F := F) hu
  have hzero :
      -(ϑ∗∗ 0) = sInf (Set.range (ϑ∗)) := by
    have hzero' : ϑ∗∗ 0 = -(sInf (Set.range (ϑ∗))) := by
      simpa [sInf_range] using (conjugate_zero_eq_neg_iInf_local (φ := ϑ∗))
    have := congrArg Neg.neg hzero'
    simpa using this
  have hsInf_le : sInf (Set.range (ϑ∗)) ≤ ϑ∗ u := by
    exact sInf_le ⟨u, rfl⟩
  have hu_eq : ϑ∗ u = sInf (Set.range (ϑ∗)) := by
    refine le_antisymm ?_ hsInf_le
    calc
      ϑ∗ u ≤ -(ϑ∗∗ 0) := hle
      _ = sInf (Set.range (ϑ∗)) := hzero
  -- Rewrite the conjugate back to the Chapter 19 dual objective and close by `mem_argmin`.
  rw [mem_argmin_iff_eq_sInf]
  calc
    perturbationDualObjective F u = ϑ∗ u := by
      rw [← conjugate_valueFunction_eq_dualObjective (F := F)]
    _ = sInf (Set.range (ϑ∗)) := hu_eq
    _ = sInf (Set.range (perturbationDualObjective F)) := by
      rw [← conjugate_valueFunction_eq_dualObjective (F := F)]

-- Proof sketch: Proposition 19.12 identifies `perturbationDualObjective F` with the Fenchel
-- conjugate `(Prod.snd ▷ F)∗`. The forward inclusion is the direct conjugate-definition route
-- above; the reverse inclusion still needs the missing lightweight transport from
-- `u ∈ ∂((Prod.snd ▷ F)∗∗)(0)` back to dual minimality of `(Prod.snd ▷ F)∗`.
/-- Proposition 19.14 (1): the dual solution set `U = Argmin (perturbationDualObjective F)`
equals the subdifferential of the biconjugate of the value function at the origin. -/
theorem argmin_perturbationDualObjective_eq_subdifferential_biconjugate_valueFunction_zero
    (_hproper : IsProper (ϑ∗)) :
    Argmin (perturbationDualObjective F) = (∂ (ϑ∗∗)) 0 := by
  -- Route correction: the stable source-faithful forward inclusion comes directly from the
  -- conjugate definition plus Proposition 19.12, while the reverse inclusion now uses the raw
  -- zero-slope comparison `ϑ*(u) ≤ -(ϑ**(0))`.
  ext u
  constructor
  · intro hu
    exact
      mem_subdifferential_biconjugate_valueFunction_zero_of_mem_argmin_perturbationDualObjective
        (F := F) hu
  · intro hu
    exact
      mem_argmin_perturbationDualObjective_of_mem_subdifferential_biconjugate_valueFunction_zero
        (F := F) hu

/-- Helper for Proposition 19.14: if `g ≤ f` pointwise and the two functions agree at the base
point `x`, then every subgradient of `g` at `x` is also a subgradient of `f` there. -/
lemma mem_subdifferential_of_le_of_eq_at_point
    {f g : K → EReal} {x u : K} (hgf : g ≤ f) (hEq : g x = f x)
    (hu : u ∈ (∂ g) x) :
    u ∈ (∂ f) x := by
  -- Expand both subdifferentials and transport the affine minorant through the pointwise order
  -- using the equality at the active point.
  rw [mem_subdifferential_iff] at hu ⊢
  intro y
  calc
    ((⟪y - x, u⟫_ℝ : ℝ) : EReal) + f x = ((⟪y - x, u⟫_ℝ : ℝ) : EReal) + g x := by
      rw [hEq]
    _ ≤ g y := hu y
    _ ≤ f y := hgf y

/-- Helper for Proposition 19.14: if `u ∈ ∂ f(0)` and `f*` is proper, then the value `f(0)` is
finite. -/
lemma zero_mem_effectiveDom_of_mem_subdifferential_of_conjugate_isProper
    {f : K → EReal} {u : K} (hproper : IsProper (f∗)) (hu : u ∈ (∂ f) 0) :
    (0 : K) ∈ effectiveDom f := by
  have hzero_ne_bot : f 0 ≠ ⊥ := by
    -- If `f(0) = -∞`, then the `0`-term already forces `f*` to be `+∞` everywhere.
    intro hbot
    rcases hproper.2 with ⟨v, hv_dom⟩
    have htop : f∗ v = ⊤ := by
      rw [conjugate_apply]
      refine le_antisymm le_top ?_
      have hzero_term : (⊤ : EReal) ≤ (((⟪(0 : K), v⟫_ℝ : ℝ) : EReal) - f 0) := by
        simp [hbot]
      exact
        le_trans hzero_term
          (le_iSup (fun y : K ↦ (((⟪y, v⟫_ℝ : ℝ) : EReal) - f y)) (0 : K))
    exact (mem_dom_iff_ne_top _ _).mp hv_dom htop
  have hzero_ne_top : f 0 ≠ ⊤ := by
    -- If `f(0) = +∞`, the subgradient inequality forces `f ≡ +∞`, so `f* ≡ -∞`.
    intro htop
    have hall_top : ∀ y : K, f y = ⊤ := by
      intro y
      have huy := (mem_subdifferential_iff (f := f) (x := (0 : K)) (u := u)).1 hu y
      rw [htop] at huy
      have hy_top : (⊤ : EReal) ≤ f y := by
        have hterm : (((⟪y, u⟫_ℝ : ℝ) : EReal) + (⊤ : EReal)) = (⊤ : EReal) := by
          exact EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)
        calc
          (⊤ : EReal) = (((⟪y, u⟫_ℝ : ℝ) : EReal) + (⊤ : EReal)) := hterm.symm
          _ ≤ f y := huy
      exact le_antisymm le_top hy_top
    have hbot : f∗ u = ⊥ := by
      rw [conjugate_apply]
      refine le_antisymm ?_ bot_le
      refine iSup_le fun y ↦ ?_
      rw [hall_top y]
      simp
    exact hproper.1 u hbot
  -- The two exclusions are exactly the effective-domain criterion for raw `EReal` functions.
  exact (mem_effectiveDom_iff f 0).2 ⟨hzero_ne_top, hzero_ne_bot⟩

/-- Helper for Proposition 19.14: a subgradient at the origin, together with finiteness there,
gives lower semicontinuity at the origin. -/
lemma lowerSemicontinuousAt_zero_of_mem_subdifferential
    {f : K → EReal} {u : K} (hu : u ∈ (∂ f) 0) (hzero : (0 : K) ∈ effectiveDom f) :
    LowerSemicontinuousAt f 0 := by
  have hzero_top : f 0 ≠ ⊤ := (mem_effectiveDom_iff f 0).mp hzero |>.1
  have hzero_bot : f 0 ≠ ⊥ := (mem_effectiveDom_iff f 0).mp hzero |>.2
  let g : K → EReal := fun y ↦ (((⟪y, u⟫_ℝ + (f 0).toReal : ℝ) : EReal))
  have hg_le : g ≤ f := by
    intro y
    -- Freeze the finite value `f(0)` and rewrite the affine minorant in the subgradient
    -- inequality as an `EReal` inequality.
    have huy := (mem_subdifferential_iff (f := f) (x := (0 : K)) (u := u)).1 hu y
    have hg_eq : g y = ((⟪y, u⟫_ℝ : EReal) + f 0) := by
      calc
        g y = (((⟪y, u⟫_ℝ + (f 0).toReal : ℝ) : EReal)) := rfl
        _ = ((⟪y, u⟫_ℝ : EReal) + (((f 0).toReal : ℝ) : EReal)) := by
              rw [EReal.coe_add]
        _ = ((⟪y, u⟫_ℝ : EReal) + f 0) := by
              rw [EReal.coe_toReal hzero_top hzero_bot]
    simpa [hg_eq] using huy
  have hg_zero : g 0 = f 0 := by
    -- At the base point, the affine minorant agrees with `f`.
    calc
      g 0 = (((⟪(0 : K), u⟫_ℝ + (f 0).toReal : ℝ) : EReal)) := rfl
      _ = ((((f 0).toReal : ℝ) : EReal)) := by simp
      _ = f 0 := EReal.coe_toReal hzero_top hzero_bot
  have hg_cont : ContinuousAt g 0 := by
    have hreal_cont : ContinuousAt (fun y : K ↦ ⟪y, u⟫_ℝ + (f 0).toReal) 0 := by
      have hinner : Continuous (fun y : K ↦ ⟪y, u⟫_ℝ) := continuous_id.inner continuous_const
      exact hinner.continuousAt.add continuousAt_const
    exact continuous_coe_real_ereal.continuousAt.comp hreal_cont
  -- Compare the liminf of `f` with the touching affine minorant.
  rw [lowerSemicontinuousAt_iff_le_liminf]
  calc
    f 0 = g 0 := hg_zero.symm
    _ ≤ Filter.liminf g (nhds (0 : K)) := hg_cont.lowerSemicontinuousAt.le_liminf
    _ ≤ Filter.liminf f (nhds (0 : K)) := by
          exact Filter.liminf_le_liminf (Filter.Eventually.of_forall hg_le)

-- The generic owner theorems `SubdifferentiableAt.lowerSemicontinuousAt`,
-- `SubdifferentiableAt.mem_effectiveDomain`, and the codomain fact `(ϑ 0).2` are used directly
-- below, so we do not keep perturbation-specific wrapper lemmas for those facts.

end Basic

section Complete

variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Helper for Proposition 19.14: a subgradient of the value function at the origin yields a dual
minimizer by combining the zero-slope identity with Proposition 19.13. -/
lemma mem_argmin_perturbationDualObjective_of_mem_subdifferential_valueFunction_zero
    (hconv : IsConvex ϑ) (hproper : IsProper (ϑ∗)) {u : K} (hu : u ∈ (∂ ϑ) 0) :
    u ∈ Argmin (perturbationDualObjective F) := by
  let θ : K → EReal := Prod.snd ▷ F
  have hconvθ : IsConvex θ := by
    simpa [θ] using hconv
  have hproperθ : IsProper (θ∗) := by
    simpa [θ] using hproper
  have huθ : u ∈ (∂ θ) 0 := by
    simpa [θ] using hu
  have hzero : 0 ∈ effectiveDom θ := by
    have hzeroE : 0 ∈ effectiveDom θ :=
      zero_mem_effectiveDom_of_mem_subdifferential_of_conjugate_isProper
        (f := θ) hproperθ huθ
    exact hzeroE
  have hlsc : LowerSemicontinuousAt θ 0 := by
    have hlscE : LowerSemicontinuousAt θ 0 :=
      lowerSemicontinuousAt_zero_of_mem_subdifferential
        (f := θ) huθ hzero
    exact hlscE
  have hzero_top : θ 0 ≠ ⊤ :=
    ((mem_effectiveDom_iff (f := θ) (x := (0 : K))).mp hzero).1
  have hzero_bot : θ 0 ≠ ⊥ :=
    ((mem_effectiveDom_iff (f := θ) (x := (0 : K))).mp hzero).2
  have hu0 := (mem_subdifferential_iff (f := θ) (x := (0 : K)) (u := u)).1 huθ
  have hupper : θ∗ u ≤ -(θ 0) := by
    rw [conjugate_apply]
    refine iSup_le fun y ↦ ?_
    by_cases hy_top : θ y = ⊤
    · rw [hy_top, EReal.sub_top]
      exact bot_le
    have hyineq : (((⟪y, u⟫_ℝ : ℝ) : EReal) + θ 0) ≤ θ y := by
      simpa using hu0 y
    have hy_bot : θ y ≠ ⊥ := by
      intro hy_bot
      rw [hy_bot] at hyineq
      have hleft_ne_bot : (((⟪y, u⟫_ℝ : ℝ) : EReal) + θ 0) ≠ ⊥ := by
        exact EReal.add_ne_bot_iff.2 ⟨EReal.coe_ne_bot _, hzero_bot⟩
      exact hleft_ne_bot (le_bot_iff.mp hyineq)
    have hdefect_le : ((⟪y, u⟫_ℝ : EReal)) ≤ θ y - θ 0 := by
      exact (EReal.le_sub_iff_add_le (.inl hzero_bot) (.inl hzero_top)).2 <| by
        simpa using hyineq
    exact (EReal.sub_le_iff_le_add (.inl hy_bot) (.inl hy_top)).2 <| by
      simpa [sub_eq_add_neg, add_comm] using hdefect_le
  have hlower : -(θ 0) ≤ θ∗ u := by
    rw [conjugate_apply]
    simpa using
      (le_iSup (fun y : K ↦ (((⟪y, u⟫_ℝ : ℝ) : EReal) - θ y)) (0 : K))
  have hu_eq : θ∗ u = sInf (Set.range (θ∗)) := by
    have hu_value : θ∗ u = -(θ 0) := le_antisymm hupper hlower
    have hvalue_zero :
        θ 0 = -sInf (Set.range (perturbationDualObjective F)) := by
      have hbiconj_zero : θ∗∗ 0 = θ 0 :=
        (lscAt_iff_biconjugate_eq_self_of_convex_at_finite_point hconvθ hzero).mp hlsc
      calc
        θ 0 = θ∗∗ 0 := hbiconj_zero.symm
        _ = -sInf (Set.range (perturbationDualObjective F)) := by
          symm
          exact neg_sInf_perturbationDualObjective_eq_biconjugate_valueFunction_zero F
    calc
      θ∗ u = -(θ 0) := hu_value
      _ = sInf (Set.range (perturbationDualObjective F)) := by
        have := congrArg Neg.neg hvalue_zero
        simpa using this
      _ = sInf (Set.range (θ∗)) := by
        simpa [θ] using
          (show
            sInf (Set.range (perturbationDualObjective F)) = sInf (Set.range (ϑ∗)) by
              rw [← conjugate_valueFunction_eq_dualObjective (F := F)])
  rw [mem_argmin_iff_eq_sInf]
  calc
    perturbationDualObjective F u = θ∗ u := by
      simpa [θ] using congrArg (fun f : K → EReal ↦ f u)
        (conjugate_valueFunction_eq_dualObjective (F := F)).symm
    _ = sInf (Set.range (θ∗)) := hu_eq
    _ = sInf (Set.range (perturbationDualObjective F)) := by
      simpa [θ] using
        (show
          sInf (Set.range (ϑ∗)) = sInf (Set.range (perturbationDualObjective F)) by
            rw [conjugate_valueFunction_eq_dualObjective (F := F)])

-- Proof sketch: clause (1) identifies the dual solution set with `∂ϑ**(0)`, and Proposition
-- 16.5 transfers subdifferentiability of `ϑ` at `0` to subdifferentiability of `ϑ**` there.
/-- Subdifferentiability of the value function at the origin yields a dual minimizer. -/
theorem argmin_perturbationDualObjective_nonempty_of_subdifferentiableAt_valueFunction_zero
    (hconv : IsConvex ϑ) (hproper : IsProper (ϑ∗)) (hsub : SubdifferentiableAt ϑ 0) :
    (Argmin (perturbationDualObjective F)).Nonempty := by
  -- Pick a subgradient of `ϑ` at `0` and convert the zero-slope identity into dual attainment.
  rw [subdifferentiableAt_iff_mem_dom, SetValuedOperator.mem_dom_iff] at hsub
  rcases hsub with ⟨u, hu⟩
  exact
    ⟨u,
      mem_argmin_perturbationDualObjective_of_mem_subdifferential_valueFunction_zero
        (F := F) hconv hproper hu⟩

-- Proof sketch: lower semicontinuity and membership of `0` in the effective domain give
-- `ϑ(0) = ϑ**(0)` by Proposition 13.44. Clause (1) identifies the dual solution set with
-- `∂ϑ**(0)`, and `ϑ** ≤ ϑ` upgrades a dual minimizer to subdifferentiability of `ϑ` at `0`.
/-
The next two source-facing clauses share the same owner-level hypotheses on the canonical value
function `ϑ`.
-/
/-- Lower semicontinuity, finiteness, and dual attainment at the origin imply
subdifferentiability of the value function there. -/
theorem
    subdifferentiableAt_valueFunction_zero_of_lscAt_of_finite_of_dualArgmin_nonempty
    (hconv : IsConvex ϑ) (_hproper : IsProper (ϑ∗))
    (hlsc : LowerSemicontinuousAt ϑ 0)
    (hzero : 0 ∈ effectiveDom ϑ)
    (hdual : (Argmin (perturbationDualObjective F)).Nonempty)
    : SubdifferentiableAt ϑ 0 := by
  let θ : K → EReal := Prod.snd ▷ F
  have hconvθ : IsConvex θ := by
    simpa [θ] using hconv
  have hlscθ : LowerSemicontinuousAt θ 0 := by
    simpa [θ] using hlsc
  have hzeroθ : 0 ∈ effectiveDom θ := by
    change 0 ∈ effectiveDom θ
    simpa [θ] using hzero
  rcases hdual with ⟨u, hu⟩
  have hu_biconj : u ∈ (∂ (θ∗∗)) 0 := by
    simpa [θ] using
      (mem_subdifferential_biconjugate_valueFunction_zero_of_mem_argmin_perturbationDualObjective
        (F := F) hu)
  have hEq0 : θ∗∗ 0 = θ 0 := by
    -- Proposition 13.44 identifies the lower-semicontinuous convex value with its biconjugate at
    -- finite points.
    exact (lscAt_iff_biconjugate_eq_self_of_convex_at_finite_point hconvθ hzeroθ).mp hlscθ
  -- Upgrade the `ϑ**`-subgradient along the pointwise inequality `ϑ** ≤ ϑ`.
  change SubdifferentiableAt θ 0
  rw [subdifferentiableAt_iff_mem_dom, SetValuedOperator.mem_dom_iff]
  refine ⟨u, ?_⟩
  exact
    mem_subdifferential_of_le_of_eq_at_point
      (f := θ) (g := θ∗∗) (x := (0 : K)) (u := u)
      (biconjugate_le (f := θ)) hEq0 hu_biconj

-- Proof sketch: Proposition 16.4 makes `SubdifferentiableAt ϑ 0` imply lower semicontinuity at
-- `0` and membership of `0` in `effectiveDom ϑ`; clause (1) together with Proposition 16.5
-- identifies a dual minimizer. The reverse implication is the helper theorem above.
/-- Proposition 19.14 (2): `∂ ϑ 0 ≠ ∅`, written canonically as `SubdifferentiableAt ϑ 0`, if and
only if `ϑ` is lower semicontinuous at `0`, `0 ∈ effectiveDom ϑ`, and the dual solution set
`Argmin (perturbationDualObjective F)` is nonempty. -/
theorem
    subdifferentiableAt_valueFunction_zero_iff_lscAt_and_finite_and_dualArgmin_nonempty
    (hconv : IsConvex ϑ) (hproper : IsProper (ϑ∗)) :
    SubdifferentiableAt ϑ 0 ↔
      LowerSemicontinuousAt ϑ 0 ∧
        0 ∈ effectiveDom ϑ ∧
        (Argmin (perturbationDualObjective F)).Nonempty := by
  constructor
  · intro hsub
    have hsub0 : SubdifferentiableAt ϑ 0 := hsub
    let θ : K → EReal := Prod.snd ▷ F
    rw [subdifferentiableAt_iff_mem_dom, SetValuedOperator.mem_dom_iff] at hsub
    rcases hsub with ⟨u, hu⟩
    have hzero : 0 ∈ effectiveDom ϑ := by
      -- Properness of `ϑ*` upgrades the raw subgradient witness to finiteness at the origin.
      have huθ : u ∈ (∂ θ) 0 := by
        simpa [θ] using hu
      have hproperθ : IsProper (θ∗) := by
        simpa [θ] using hproper
      have hzeroE : 0 ∈ effectiveDom θ :=
        zero_mem_effectiveDom_of_mem_subdifferential_of_conjugate_isProper
          (f := θ) hproperθ huθ
      change 0 ∈ effectiveDom θ
      exact hzeroE
    have hlsc : LowerSemicontinuousAt ϑ 0 := by
      -- Once the origin value is finite, the touching affine minorant forces lower
      -- semicontinuity there.
      have huθ : u ∈ (∂ θ) 0 := by
        simpa [θ] using hu
      have hzeroθ : 0 ∈ effectiveDom θ := by
        simpa [θ] using hzero
      have hlscE : LowerSemicontinuousAt θ 0 :=
        lowerSemicontinuousAt_zero_of_mem_subdifferential
          (f := θ) huθ hzeroθ
      change LowerSemicontinuousAt θ 0
      exact hlscE
    have harg : (Argmin (perturbationDualObjective F)).Nonempty :=
      argmin_perturbationDualObjective_nonempty_of_subdifferentiableAt_valueFunction_zero
        (F := F) hconv hproper hsub0
    exact ⟨hlsc, hzero, harg⟩
  · rintro ⟨hlsc, hzero, hdual⟩
    exact
      subdifferentiableAt_valueFunction_zero_of_lscAt_of_finite_of_dualArgmin_nonempty
        (F := F) hconv hproper hlsc hzero hdual

-- Proof sketch: under the right-hand side of clause (2), Proposition 13.44 gives
-- `(Prod.snd ▷ F) 0 = (Prod.snd ▷ F)∗∗ 0` from the effective-domain hypothesis. Combining this
-- with clause (1) and the inequality `(Prod.snd ▷ F)∗∗ ≤ Prod.snd ▷ F` upgrades the dual-solution
-- set from `∂(ϑ**)(0)` to `∂ϑ(0)`.
/-- Proposition 19.14 (3): under the lower-semicontinuity, finiteness, and dual-attainment
hypotheses from Proposition 19.14 (2), the dual solution set equals `∂ ϑ 0`. -/
theorem
    argmin_perturbationDualObjective_eq_subdifferential_valueFunction_zero
    (hconv : IsConvex ϑ) (hproper : IsProper (ϑ∗))
    (hlsc : LowerSemicontinuousAt ϑ 0)
    (hzero : 0 ∈ effectiveDom ϑ)
    (hdual : (Argmin (perturbationDualObjective F)).Nonempty)
    : Argmin (perturbationDualObjective F) = (∂ ϑ) 0 := by
  let θ : K → EReal := Prod.snd ▷ F
  have hsub : SubdifferentiableAt ϑ 0 :=
    subdifferentiableAt_valueFunction_zero_of_lscAt_of_finite_of_dualArgmin_nonempty
      (F := F) hconv hproper hlsc hzero hdual
  have hEq0 : θ∗∗ 0 = θ 0 := by
    -- Proposition 13.44 identifies the lower-semicontinuous convex value with its biconjugate at
    -- finite points.
    have hconvθ : IsConvex θ := by
      simpa [θ] using hconv
    have hlscθ : LowerSemicontinuousAt θ 0 := by
      simpa [θ] using hlsc
    have hzeroθ : 0 ∈ effectiveDom θ := by
      simpa [θ] using hzero
    exact (lscAt_iff_biconjugate_eq_self_of_convex_at_finite_point hconvθ hzeroθ).mp hlscθ
  ext u
  constructor
  · intro hu
    have hu_biconj :
        u ∈ (∂ (ϑ∗∗)) 0 :=
      mem_subdifferential_biconjugate_valueFunction_zero_of_mem_argmin_perturbationDualObjective
        (F := F) hu
    exact
      by
        simpa [θ] using
          mem_subdifferential_of_le_of_eq_at_point
            (f := θ) (g := θ∗∗) (x := (0 : K)) (u := u)
            (biconjugate_le (f := θ)) hEq0 (by simpa [θ] using hu_biconj)
  · intro hu
    exact
      mem_argmin_perturbationDualObjective_of_mem_subdifferential_valueFunction_zero
        (F := F) hconv hproper hu

section OptimalValue

-- Proof sketch: Proposition 19.13 gives `(Prod.snd ▷ F) 0 = - inf perturbationDualObjective`
-- from lower semicontinuity and the effective-domain hypothesis at the origin. A dual minimizer
-- from `hdual` turns the dual infimum into an attained minimum value, and the primal infimum is
-- exactly `(Prod.snd ▷ F) 0` by Definition 19.11.
/-- Proposition 19.14 (4): under the lower-semicontinuity, finiteness, and dual-attainment
hypotheses from Proposition 19.14 (2), the primal optimal value is a real number `μ`, and the
dual minimum is attained at some `v ∈ Argmin (perturbationDualObjective F)` with value `-μ`. -/
theorem
    exists_real_primalOptimalValue_and_mem_argmin_perturbationDualObjective
    (hconv : IsConvex ϑ)
    (hlsc : LowerSemicontinuousAt ϑ 0)
    (hzero : 0 ∈ effectiveDom ϑ)
    (hdual : (Argmin (perturbationDualObjective F)).Nonempty)
    : ∃ μ : ℝ, ∃ v : K,
        v ∈ Argmin (perturbationDualObjective F) ∧
          sInf (Set.range (perturbationPrimalObjective F)) = (μ : EReal) ∧
          perturbationDualObjective F v = (-μ : EReal) := by
  rcases hdual with ⟨v, hv⟩
  have hEq0 : ϑ∗∗ 0 = ϑ 0 := by
    -- Proposition 13.44 recovers the primal value from the biconjugate at the origin.
    exact (lscAt_iff_biconjugate_eq_self_of_convex_at_finite_point hconv hzero).mp hlsc
  have hneg_dual : -sInf (Set.range (perturbationDualObjective F)) = ϑ 0 := by
    -- Proposition 19.12(2) is the source strong-duality identity for the value function.
    calc
      -sInf (Set.range (perturbationDualObjective F)) = ϑ∗∗ 0 :=
        neg_sInf_perturbationDualObjective_eq_biconjugate_valueFunction_zero F
      _ = ϑ 0 := hEq0
  have hdual_value :
      sInf (Set.range (perturbationDualObjective F)) = -(ϑ 0) := by
    -- Negate the previous identity to place the dual optimum on the usual infimum side.
    have := congrArg Neg.neg hneg_dual
    simpa using this
  have hprimal_value :
      sInf (Set.range (perturbationPrimalObjective F)) = ϑ 0 := by
    -- The primal objective is exactly the zero slice of the value function.
    rw [sInf_range, infimalPostcomposition_snd_apply]
    rfl
  let μ : ℝ := (ϑ 0).toReal
  have hmu : ϑ 0 = (μ : EReal) := by
    -- Finiteness at `0` lets us replace the extended-real value by its real representative.
    symm
    exact EReal.coe_toReal ((mem_effectiveDom_iff (f := ϑ) (x := (0 : K))).mp hzero).1
      ((mem_effectiveDom_iff (f := ϑ) (x := (0 : K))).mp hzero).2
  have hv_value : perturbationDualObjective F v = -(ϑ 0) := by
    calc
      perturbationDualObjective F v = sInf (Set.range (perturbationDualObjective F)) :=
        mem_argmin_iff_eq_sInf.mp hv
      _ = -(ϑ 0) := hdual_value
  refine ⟨μ, v, hv, ?_, ?_⟩
  · exact hprimal_value.trans hmu
  · calc
      perturbationDualObjective F v = -(ϑ 0) := hv_value
      _ = (-μ : EReal) := by rw [hmu]

end OptimalValue

end Complete

end ParametricDuality

end ERealFunction
