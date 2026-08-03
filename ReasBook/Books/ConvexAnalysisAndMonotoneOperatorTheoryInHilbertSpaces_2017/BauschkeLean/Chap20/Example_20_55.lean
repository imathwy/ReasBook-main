import BauschkeLean.Chap01.Text_1_0_8
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_10
import BauschkeLean.Chap20.Definition_20_51

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace SetValuedOperator
open SetValuedOperator

universe u

namespace ERealFunction

section Subdifferential

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))

/- Source/core/bridge triage:
- `source-facing`: Example 20.55 states the two Fitzpatrick consequences for the subdifferential
  of a `Γ₀(H)` function.
- `core/canonical`: the owner abstractions are `F[_]`, the packaged conjugate `f∗[hf]`, the
  separable sum `⊕`, and `effectiveDomain`.
- `bridge/view`: the subdifferential owner is the canonical Chapter 16 operator `∂ f`; there is
  no additional wrapper data here. -/

-- Semantic recall: `lean_leansearch` did not return a useful existing theorem for this
-- subdifferential/Fitzpatrick comparison, so the source-facing statement stays on the project
-- owners `F[_]`, `∂`, `⊕`, and `effectiveDomain`.

-- Proof sketch: fix `(x, u)` and expand `F[(∂ f)] (x, u)` as the supremum over graph points
-- `(y, v)` of `∂ f`. Proposition 16.10 rewrites `v ∈ (∂ f) y` as Fenchel--Young equality
-- `f y + f^*(v) = ⟪y, v⟫`, and Proposition 13.15 gives `⟪y, u⟫ - f y ≤ f^*(u)` together with
-- `⟪x, v⟫ - f^*(v) ≤ f^{**}(x) = f x` by Corollary 13.38. Taking the supremum yields the
-- Fitzpatrick upper bound by `f ⊕ f^*`.
/-- Helper for Example 20.55: an active graph point of `∂ f` rewrites the Fitzpatrick
graph supremand as the sum of the two Fenchel defects from the source proof. -/
private lemma subgradientGraphSupremandEqFenchelDefects
    {x u y v : H} (hsub : v ∈ (∂ f) y) :
    ((⟪y, u⟫_ℝ + ⟪x, v⟫_ℝ - ⟪y, v⟫_ℝ : ℝ) : EReal) =
      (((⟪y, u⟫_ℝ : ℝ) : EReal) - (f y : EReal)) +
        (((⟪x, v⟫_ℝ : ℝ) : EReal) - (f∗[hf] v : EReal)) := by
  -- Proposition 16.10 gives the contact equality `f y + f*(v) = ⟪y, v⟫` at a graph point.
  have hcontact :
      (f y : EReal) + (f∗[hf] v : EReal) =
        ((⟪y, v⟫_ℝ : ℝ) : EReal) := by
    simpa [gammaZeroConjugate_apply] using
      (mem_subdifferential_iff_fenchel_young_eq (f := f) hf.2.nonempty y v).1 hsub
  have hfy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
  have hgv_bot : (f∗[hf] v : EReal) ≠ ⊥ := ne_of_gt (f∗[hf] v).2
  have hfy_top : (f y : EReal) ≠ ⊤ := by
    intro hfy_top
    have hsum_top : (f y : EReal) + (f∗[hf] v : EReal) = ⊤ := by
      rw [hfy_top]
      exact EReal.top_add_of_ne_bot hgv_bot
    exact EReal.coe_ne_top _ (hcontact.symm.trans hsum_top)
  have hgv_top : (f∗[hf] v : EReal) ≠ ⊤ := by
    intro hgv_top
    have hsum_top : (f y : EReal) + (f∗[hf] v : EReal) = ⊤ := by
      rw [hgv_top]
      exact EReal.add_top_of_ne_bot hfy_bot
    exact EReal.coe_ne_top _ (hcontact.symm.trans hsum_top)
  have hcontact_real :
      (f y : EReal).toReal + (f∗[hf] v : EReal).toReal = ⟪y, v⟫_ℝ := by
    have hcontact' := hcontact
    rw [← EReal.coe_toReal hfy_top hfy_bot, ← EReal.coe_toReal hgv_top hgv_bot,
      ← EReal.coe_add] at hcontact'
    exact EReal.coe_eq_coe_iff.mp hcontact'
  -- Convert both finite `EReal` subtractions back to a real identity and finish by arithmetic.
  rw [← EReal.coe_toReal hfy_top hfy_bot, ← EReal.coe_toReal hgv_top hgv_bot,
    ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add]
  exact congrArg (fun t : ℝ ↦ (t : EReal)) <| by
    linarith [hcontact_real]

/-- Helper for Example 20.55: each graph-point supremand of `F[(∂ f)]` is bounded above by the
separable sum `f ⊕ f∗[hf]`. -/
private lemma subgradientGraphSupremand_le_separableSum
    (x u : H) (p : gra (∂ f)) :
    ((⟪p.1.1, u⟫_ℝ + ⟪x, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ : ℝ) : EReal) ≤
      ((f ⊕ f∗[hf]) (x, u) : EReal) := by
  rcases p with ⟨⟨y, v⟩, hsub⟩
  -- Start by recording the subgradient contact equality and the resulting finiteness facts.
  have hcontact :
      (f y : EReal) + (f∗[hf] v : EReal) =
        ((⟪y, v⟫_ℝ : ℝ) : EReal) := by
    simpa [gammaZeroConjugate_apply] using
      (mem_subdifferential_iff_fenchel_young_eq (f := f) hf.2.nonempty y v).1 hsub
  have hfy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
  have hgv_bot : (f∗[hf] v : EReal) ≠ ⊥ := ne_of_gt (f∗[hf] v).2
  have hfy_top : (f y : EReal) ≠ ⊤ := by
    intro hfy_top
    have hsum_top : (f y : EReal) + (f∗[hf] v : EReal) = ⊤ := by
      rw [hfy_top]
      exact EReal.top_add_of_ne_bot hgv_bot
    exact EReal.coe_ne_top _ (hcontact.symm.trans hsum_top)
  have hgv_top : (f∗[hf] v : EReal) ≠ ⊤ := by
    intro hgv_top
    have hsum_top : (f y : EReal) + (f∗[hf] v : EReal) = ⊤ := by
      rw [hgv_top]
      exact EReal.add_top_of_ne_bot hfy_bot
    exact EReal.coe_ne_top _ (hcontact.symm.trans hsum_top)
  -- First bound the primal Fenchel defect by the conjugate value at `u`.
  have hprimal :
      (((⟪y, u⟫_ℝ : ℝ) : EReal) - (f y : EReal)) ≤ (f∗[hf] u : EReal) := by
    exact
      (EReal.sub_le_iff_le_add (.inl hfy_bot) (.inl hfy_top)).2 <| by
        simpa [gammaZeroConjugate_apply, add_comm] using
          (fenchel_young_inequality (isProper_of_mem_gammaZero hf) y u)
  -- Then bound the dual Fenchel defect by the biconjugate value, which is `f x`.
  have hdual :
      ((⟪x, v⟫_ℝ : ℝ) : EReal) ≤ (f∗[hf] v : EReal) + (f x : EReal) := by
    have hdual_raw :
        ((⟪x, v⟫_ℝ : ℝ) : EReal) ≤ (f∗[hf] v : EReal) + f.asEReal∗∗ x := by
      simpa [Function.asEReal, gammaZeroConjugate_apply, real_inner_comm] using
        (fenchel_young_inequality
          (f := (f∗[hf]).asEReal)
          (isProper_of_mem_gammaZero (gammaZeroConjugate_mem_gammaZero hf)) v x)
    rw [show f.asEReal∗∗ x = (f x : EReal) by
      simpa using congrFun (biconjugate_eq_of_mem_gammaZero hf) x] at hdual_raw
    exact hdual_raw
  have hdual_defect :
      (((⟪x, v⟫_ℝ : ℝ) : EReal) - (f∗[hf] v : EReal)) ≤ (f x : EReal) := by
    exact
      (EReal.sub_le_iff_le_add (.inl hgv_bot) (.inl hgv_top)).2 <| by
        simpa [add_comm] using hdual
  -- Combine the two defect bounds after rewriting the graph supremand into defect form.
  calc
    ((⟪y, u⟫_ℝ + ⟪x, v⟫_ℝ - ⟪y, v⟫_ℝ : ℝ) : EReal) =
        (((⟪y, u⟫_ℝ : ℝ) : EReal) - (f y : EReal)) +
          (((⟪x, v⟫_ℝ : ℝ) : EReal) - (f∗[hf] v : EReal)) :=
          subgradientGraphSupremandEqFenchelDefects (f := f) hf hsub
    _ ≤ (f∗[hf] u : EReal) + (f x : EReal) := add_le_add hprimal hdual_defect
    _ = ((f ⊕ f∗[hf]) (x, u) : EReal) := by
          simp [separableSum_apply, add_comm, add_left_comm, add_assoc]

/-- Helper for Example 20.55: the separable-sum value is finite above on the product of the
effective domains of `f` and `f∗[hf]`. -/
private lemma separableSum_value_ltTop_of_memEffectiveDomainProd
    {x u : H} (hx : x ∈ effectiveDomain f) (hu : u ∈ effectiveDomain (f∗[hf])) :
    ((f ⊕ f∗[hf]) (x, u) : EReal) < ⊤ := by
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hfu_top : (f∗[hf] u : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hu)
  -- Finiteness of each summand gives finiteness of their separable sum.
  rw [separableSum_apply]
  exact EReal.add_lt_top hfx_top hfu_top

/-- Example 20.55 (1): if `f ∈ Γ₀(H)`, then the Fitzpatrick function of its
subdifferential is bounded above by the separable sum of `f` and its canonical
packaged Fenchel conjugate `f∗[hf]`. -/
theorem fitzpatrickFunction_subdifferential_le_separableSum_conjugate
    :
    F[(∂ f)] ≤ (f ⊕ f∗[hf]).asEReal := by
  intro xu
  rcases xu with ⟨x, u⟩
  -- Bound each graph-point contribution separately, then close the supremum by `iSup_le`.
  refine iSup_le fun p ↦ ?_
  simpa using subgradientGraphSupremand_le_separableSum (f := f) hf x u p

-- If `(x, u) ∈ dom f × dom f^*`, then `(f ⊕ f^*) (x, u)` is finite, so the upper bound implies
-- `F[(∂ f)] (x, u) < ⊤`, hence `(x, u) ∈ dom (F[(∂ f)])`.
/-- Example 20.55 (2): the product of the effective domains of `f` and its
canonical packaged Fenchel conjugate `f∗[hf]` lies in the domain of the
Fitzpatrick function of `∂ f`. -/
theorem dom_prod_conjugate_subset_dom_fitzpatrickFunction_subdifferential
    :
    effectiveDomain f ×ˢ effectiveDomain (f∗[hf]) ⊆ dom (F[(∂ f)]) := by
  intro xu hxu
  rcases hxu with ⟨hx, hu⟩
  rcases xu with ⟨x, u⟩
  have hbound :
      F[(∂ f)] (x, u) ≤ ((f ⊕ f∗[hf]) (x, u) : EReal) := by
    exact (fitzpatrickFunction_subdifferential_le_separableSum_conjugate (f := f) hf) (x, u)
  have hsum_lt_top :
      ((f ⊕ f∗[hf]) (x, u) : EReal) < ⊤ :=
    separableSum_value_ltTop_of_memEffectiveDomainProd (f := f) hf hx hu
  -- The pointwise upper bound from part (1) transfers the finite-above separable-sum value to
  -- the Fitzpatrick function itself.
  rw [mem_dom_iff]
  exact lt_of_le_of_lt hbound hsum_lt_top

end Subdifferential

end ERealFunction
