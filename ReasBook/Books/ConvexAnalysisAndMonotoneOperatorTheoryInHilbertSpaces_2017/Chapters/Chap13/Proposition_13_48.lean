import Mathlib
import BauschkeLean.Chap09.Definition_9_7
import BauschkeLean.Chap12.Definition_12_34
import BauschkeLean.Chap13.Proposition_13_24
import BauschkeLean.Chap13.Proposition_13_45

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace

universe u v

namespace ERealFunction

section FenchelMoreau

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
variable (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K)) (L : H →L[ℝ] K)

include hg

/-- Helper for Proposition 13.48: the range-domain hypothesis packages the composite `g ∘ L` as a
member of `Γ₀(H)`. -/
private theorem comp_mem_gammaZero_of_range_inter_effectiveDomain_nonempty_local
    (hdom : (range L ∩ effectiveDomain g).Nonempty) :
    g ∘ L ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff]
  refine ⟨?_, ?_⟩
  · -- Lower semicontinuity is preserved under composition with the continuous linear map `L`.
    simpa [Function.comp] using hg.1.comp L.continuous
  · rcases hdom with ⟨y, hy_range, hy_dom⟩
    rcases hy_range with ⟨x, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · -- A range point in `effectiveDomain g` pulls back to a finite point of `g ∘ L`.
      refine ⟨x, ?_⟩
      simpa [Function.comp, mem_effectiveDomain_iff] using hy_dom
    · exact subset_rfl
    · -- Jensen convexity transports through the linear identities `L (x + y)` and `L (α • x)`.
      intro x hx y hy α hα hα_lt_one
      have hx' : L x ∈ effectiveDomain g := by
        simpa [Function.comp, mem_effectiveDomain_iff] using hx
      have hy' : L y ∈ effectiveDomain g := by
        simpa [Function.comp, mem_effectiveDomain_iff] using hy
      simpa [Function.comp, map_add, map_smul] using hg.2.ineq hx' hy' hα hα_lt_one

/-- Helper for Proposition 13.48: the conjugate of the adjoint infimal postcomposition collapses
back to the primal composite `g.asEReal ∘ L`. -/
private theorem conjugate_adjointInfimalPostcomposition_eq_comp_local :
    ((L.adjoint ▷ g.asEReal∗)∗) = g.asEReal ∘ L := by
  calc
    ((L.adjoint ▷ g.asEReal∗)∗) = g.asEReal∗∗ ∘ (L.adjoint).adjoint := by
      -- Apply Proposition 13.24(4) to the canonical `Γ₀`-valued conjugate owner of `g`.
      simpa [Function.comp, gammaZeroConjugate_apply] using
        (conjugate_infimalPostcomposition_eq_comp_adjoint
          (f := g∗[hg]) (L := L.adjoint))
    _ = g.asEReal ∘ L := by
      -- Corollary 13.38 identifies the biconjugate of `g` with `g`, and `L** = L`.
      ext x
      rw [Function.comp_apply, Function.comp_apply, ContinuousLinearMap.adjoint_adjoint]
      exact congrFun (biconjugate_eq_of_mem_gammaZero hg) (L x)

/-- Helper for Proposition 13.48: the dual infimal-postcomposition object has conjugate with
nonempty domain under the range/effective-domain hypothesis. -/
theorem dom_conjugate_adjointInfimalPostcomposition_nonempty
    (hdom : (range L ∩ effectiveDomain g).Nonempty) :
    (dom ((L.adjoint ▷ g.asEReal∗)∗)).Nonempty := by
  rw [conjugate_adjointInfimalPostcomposition_eq_comp_local (g := g) (hg := hg) (L := L)]
  rcases hdom with ⟨y, hy_range, hy_dom⟩
  rcases hy_range with ⟨x, rfl⟩
  refine ⟨x, ?_⟩
  -- The original range/effective-domain witness is already a finite point of `g.asEReal ∘ L`.
  rw [mem_dom_iff]
  simpa [Function.comp, mem_effectiveDomain_iff] using hy_dom

/-- Helper for Proposition 13.48: the explicit biconjugate identity underlying the proposition. -/
theorem conjugate_comp_eq_biconjugate_adjointInfimalPostcomposition
    (hdom : (range L ∩ effectiveDomain g).Nonempty) :
    (g.asEReal ∘ L)∗ = (L.adjoint ▷ g.asEReal∗)∗∗ := by
  let _ := hdom
  -- Conjugating the core bridge once more produces the desired biconjugate identity.
  simpa using
    congrArg conjugate
      (conjugate_adjointInfimalPostcomposition_eq_comp_local (g := g) (hg := hg) (L := L)).symm

/-- Helper for Proposition 13.48: Proposition 13.45 identifies the composite conjugate with the
lower semicontinuous convex envelope of the adjoint infimal postcomposition. -/
private theorem
    conjugate_comp_eq_lowerSemicontinuousConvexEnvelope_adjointInfimalPostcomposition_local
    (hdom : (range L ∩ effectiveDomain g).Nonempty) :
    (g.asEReal ∘ L)∗ =
      lowerSemicontinuousConvexEnvelope (L.adjoint ▷ g.asEReal∗) := by
  let q : H → EReal := L.adjoint ▷ g.asEReal∗
  have hqdom : (dom q∗).Nonempty := by
    -- The source regularity hypothesis gives the exact domain witness required by Proposition
    -- 13.45 after rewriting the dual object as `q`.
    simpa [q] using
      dom_conjugate_adjointInfimalPostcomposition_nonempty (g := g) (hg := hg) (L := L) hdom
  calc
    (g.asEReal ∘ L)∗ = q∗∗ := by
      -- First replace the composite conjugate by the dual biconjugate from the source proof.
      simpa [q] using
        conjugate_comp_eq_biconjugate_adjointInfimalPostcomposition
          (g := g) (hg := hg) (L := L) hdom
    _ = lowerSemicontinuousConvexEnvelope q := by
      -- Then invoke Proposition 13.45 for the named dual object `q`.
      exact
        biconjugate_eq_lowerSemicontinuousConvexEnvelope_of_dom_conjugate_nonempty
          (f := q) hqdom
    _ = lowerSemicontinuousConvexEnvelope (L.adjoint ▷ g.asEReal∗) := by
      rfl

-- Semantic recall via `lean_leansearch` did not surface a more canonical Proposition 13.48 owner
-- than this local envelope statement, so the source-faithful closure layer remains the main entry.
-- Proof sketch: combine Proposition 13.48 with Proposition 13.45. The range-domain hypothesis
-- gives nonemptiness of the domain of the conjugate of `L.adjoint ▷ g.asEReal∗`, so its Fenchel
-- biconjugate is its lower semicontinuous convex envelope.
/-- Proposition 13.48: if `range L` meets `effectiveDomain g`,
then the Fenchel conjugate of `g ∘ L` is the lower semicontinuous convex envelope of the infimal
postcomposition of the Fenchel conjugate of `g` along `L.adjoint`. -/
theorem conjugate_comp_eq_lowerSemicontinuousConvexEnvelope_adjointInfimalPostcomposition
    (hdom : (range L ∩ effectiveDomain g).Nonempty) :
    (g.asEReal ∘ L)∗ =
      lowerSemicontinuousConvexEnvelope (L.adjoint ▷ g.asEReal∗) := by
  -- The local helper already establishes the exact Proposition 13.48 identity.
  exact
    conjugate_comp_eq_lowerSemicontinuousConvexEnvelope_adjointInfimalPostcomposition_local
      (g := g) (hg := hg) (L := L) hdom

end FenchelMoreau

end ERealFunction
