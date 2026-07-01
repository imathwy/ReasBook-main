import Mathlib
import SmoothManifoldsLee.Chap01.Sec01.Example_1_5

-- Declarations for this item will be appended below by the statement pipeline.

open Projectivization

-- Proof sketch: restrict the projectivization quotient map to the unit sphere `𝕊^n ⊆ ℝ^(n+1)`,
-- use the hint that this restriction is surjective, and then conclude because the sphere is compact
-- and continuous images of compact spaces are compact.
/-- Exercise 1.7: real projective space `ℝPⁿ` is compact. -/
instance realProjectiveSpaceCompactSpace (n : ℕ) :
    CompactSpace (RealProjectiveSpace n) := by
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let sphereToRealProjectiveSpace : Metric.sphere (0 : E) 1 → RealProjectiveSpace n :=
    fun x ↦ mk ℝ (x : E) (Metric.ne_of_mem_sphere x.2 one_ne_zero)
  have hq_cont : Continuous sphereToRealProjectiveSpace := by
    change Continuous
      (fun x : Metric.sphere (0 : E) 1 ↦
        (Quotient.mk'' ⟨(x : E), Metric.ne_of_mem_sphere x.2 one_ne_zero⟩ :
          RealProjectiveSpace n))
    exact continuous_quot_mk.comp <| continuous_subtype_val.subtype_mk _
  have hq_surj : Function.Surjective sphereToRealProjectiveSpace := by
    intro x
    have hx_norm_ne : ‖(x.rep : E)‖ ≠ 0 := norm_ne_zero_iff.mpr x.rep_nonzero
    refine ⟨⟨‖(x.rep : E)‖⁻¹ • x.rep, by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hx_norm_ne]⟩, ?_⟩
    change mk ℝ (‖(x.rep : E)‖⁻¹ • x.rep)
      (smul_ne_zero (inv_ne_zero hx_norm_ne) x.rep_nonzero) = x
    have hmk :
        mk ℝ (‖(x.rep : E)‖⁻¹ • x.rep)
          (smul_ne_zero (inv_ne_zero hx_norm_ne) x.rep_nonzero) =
          mk ℝ x.rep x.rep_nonzero := by
      exact (mk_eq_mk_iff' ℝ _ _ (smul_ne_zero (inv_ne_zero hx_norm_ne) x.rep_nonzero)
        x.rep_nonzero).2 ⟨‖(x.rep : E)‖⁻¹, rfl⟩
    simpa [x.mk_rep] using hmk
  have hrange : Set.range sphereToRealProjectiveSpace = Set.univ := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      rcases hq_surj x with ⟨y, rfl⟩
      exact ⟨y, rfl⟩
  have hcompact : IsCompact (Set.univ : Set (RealProjectiveSpace n)) := by
    simpa [hrange] using isCompact_range hq_cont
  exact isCompact_univ_iff.mp hcompact
