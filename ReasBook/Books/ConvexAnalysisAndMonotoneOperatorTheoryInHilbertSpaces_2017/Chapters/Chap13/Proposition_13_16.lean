import Mathlib
import BauschkeLean.Chap08.Proposition_8_4
import BauschkeLean.Chap09.Proposition_9_8
import BauschkeLean.Chap13.Proposition_13_13
import BauschkeLean.Chap13.Proposition_13_15

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Semantic recall note: `lean_leansearch` did not return relevant Fenchel-conjugation lemmas, so
-- this item follows the local Chapter 13 conjugation notation/API already used in the repository.

/-- Helper for Proposition 13 16: every affine defect appearing in the definition of the Fenchel
conjugate is bounded above by the conjugate value. -/
private theorem affine_defect_le_conjugate
    (f : H → EReal) (x u : H) :
    (((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) ≤ f∗ u := by
  -- Evaluate the defining supremum of `f∗ u` at the chosen primal point `x`.
  rw [conjugate_apply]
  exact le_iSup (fun y : H ↦ (((⟪y, u⟫_ℝ : ℝ) : EReal) - f y)) x

/-- Helper for Proposition 13 16: Jensen convexity implies convexity of the real-height epigraph.
-/
private theorem convex_epigraph_of_isConvex
    {g : H → EReal} (hg_conv : IsConvex g) :
    Convex ℝ (epigraph g) := by
  -- Rewrite epigraph convexity through the Jensen criterion already stored in `IsConvex`.
  refine (convex_epigraph_iff_jensen_on_dom g).2 ?_
  intro x y hx hy a ha0 ha1
  exact hg_conv ha0.le ha1.le

/-- Helper for Proposition 13 16: Fenchel conjugation reverses the pointwise order. -/
private theorem conjugate_antitone_local :
    Antitone (conjugate : (H → EReal) → H → EReal) := by
  intro f g hfg u
  -- Compare the defining affine defects term-by-term and then take suprema.
  rw [conjugate_apply, conjugate_apply]
  refine iSup_le fun x ↦ ?_
  calc
    (((⟪x, u⟫_ℝ : ℝ) : EReal) - g x)
        ≤ (((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) := by
          exact EReal.sub_le_sub le_rfl (hfg x)
    _ ≤ ⨆ y : H, (((⟪y, u⟫_ℝ : ℝ) : EReal) - f y) := by
          exact le_iSup (fun y : H ↦ (((⟪y, u⟫_ℝ : ℝ) : EReal) - f y)) x

/-- Proposition 13.16 (1): clause (i). Every extended-real-valued function dominates its
biconjugate. -/
theorem biconjugate_le (f : H → EReal) :
    f∗∗ ≤ f := by
  intro x
  by_cases htop : f x = ⊤
  · -- If `f x = ⊤`, the target inequality is immediate.
    simp [htop]
  by_cases hbot : f x = ⊥
  · -- If `f x = ⊥`, every conjugate value is `⊤`, so the biconjugate is also `⊥` at `x`.
    have hconj_top : ∀ u : H, f∗ u = ⊤ := by
      intro u
      have htop_le : (⊤ : EReal) ≤ f∗ u := by
        simpa [hbot] using affine_defect_le_conjugate (f := f) (x := x) (u := u)
      exact top_le_iff.mp htop_le
    have hxle : f∗∗ x ≤ ⊥ := by
      rw [conjugate_apply]
      refine iSup_le fun u ↦ ?_
      rw [hconj_top u]
      simp
    simpa [hbot] using hxle
  · -- Outside the `⊤`/`⊥` branches, rearrange the affine-defect inequality in `EReal`.
    rw [conjugate_apply]
    refine iSup_le fun u ↦ ?_
    have hdefect :
        (((⟪u, x⟫_ℝ : ℝ) : EReal) - f x) ≤ f∗ u := by
      simpa [real_inner_comm] using affine_defect_le_conjugate (f := f) (x := x) (u := u)
    have hsum :
        (((⟪u, x⟫_ℝ : ℝ) : EReal) ≤ f∗ u + f x) :=
      (EReal.sub_le_iff_le_add (Or.inl hbot) (Or.inl htop)).1 hdefect
    exact
      (EReal.sub_le_iff_le_add (Or.inr htop) (Or.inr hbot)).2
        (by simpa [add_comm] using hsum)

/-- Proposition 13.16 (3): clause (ii), second conclusion. Taking biconjugates preserves the
pointwise order. -/
theorem biconjugate_mono :
    Monotone (fun f : H → EReal ↦ f∗∗) := by
  intro f g hfg
  -- Compose the local antitone conjugation rule twice.
  exact conjugate_antitone_local (conjugate_antitone_local hfg)

/-- Proposition 13.16 (4): clause (iii). The triple Fenchel conjugate of a function equals its
single conjugate. -/
theorem triple_conjugate_eq_conjugate
    (f : H → EReal) :
    f∗∗∗ = f∗ := by
  -- The upper bound is clause (i) for `f∗`, and the lower bound comes from antitonicity.
  apply le_antisymm
  · exact biconjugate_le (f := f∗)
  · exact conjugate_antitone_local (biconjugate_le (f := f))

/-- Proposition 13.16 (5): clause (iv). Applying biconjugation to the Fenchel conjugate fixes the
conjugate. -/
theorem conjugate_biconjugate_eq_self
    (f : H → EReal) :
    (f∗)∗∗ = f∗ := by
  -- This is the triple-conjugate identity rewritten at `f`.
  simpa using triple_conjugate_eq_conjugate (f := f)

/-- Helper for Proposition 13 16: the Fenchel biconjugate is a lower semicontinuous convex
minorant of the original function, hence it lies below the lower semicontinuous convex envelope.
-/
private theorem biconjugate_le_lowerSemicontinuousConvexEnvelope
    (f : H → EReal) :
    f∗∗ ≤ lowerSemicontinuousConvexEnvelope f := by
  have hbiconj_gamma : f∗∗ ∈ gamma H := conjugate_mem_gamma (f := f∗)
  have hbiconj_data : IsConvex (f∗∗) ∧ LowerSemicontinuous (f∗∗) :=
    (mem_gamma_iff (f∗∗)).mp hbiconj_gamma
  -- Proposition 9.8 makes the envelope the maximal lower semicontinuous convex minorant.
  exact
    le_lowerSemicontinuousConvexEnvelope_of_lowerSemicontinuous_of_convex_epigraph
      hbiconj_data.2
      (convex_epigraph_of_isConvex hbiconj_data.1)
      (biconjugate_le f)

/-- Helper: passing to the lower semicontinuous convex envelope does not change the Fenchel
conjugate. This is a non-labeled support theorem reused by later files. -/
theorem conjugate_lowerSemicontinuousConvexEnvelope_eq
    (f : H → EReal) :
    (lowerSemicontinuousConvexEnvelope f)∗ = f∗ := by
  -- Sandwich the two conjugates using the envelope bounds and clause (iii).
  apply le_antisymm
  · calc
      (lowerSemicontinuousConvexEnvelope f)∗ ≤ f∗∗∗ := by
        exact conjugate_antitone_local
          (biconjugate_le_lowerSemicontinuousConvexEnvelope (f := f))
      _ = f∗ := triple_conjugate_eq_conjugate (f := f)
  · exact conjugate_antitone_local (lowerSemicontinuousConvexEnvelope_le f)

end Conjugation

end ERealFunction
