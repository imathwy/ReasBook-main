import Mathlib.Topology.Homotopy.Lifting
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Theorem_3_2_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory FundamentalGroup Path.Homotopic.Quotient
open scoped FundamentalGroup Pointwise

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

namespace IsCoveringMap

variable {p : E → B}

/-- Helper for Theorem 3.2.5: lifting a loop at `b` from a point in the fiber ends again in the
fiber over `b`. -/
theorem liftPath_endpoint_mem_fiber (hp : IsCoveringMap p) {b : B} (e : p ⁻¹' {b})
    (γ : Path b b) :
    p (hp.liftPath γ e.1 (γ.source.trans e.2.symm) 1) = b := by
  simpa using
    (congr_fun (hp.liftPath_lifts γ e.1 (γ.source.trans e.2.symm)) 1).trans γ.target

/-- Loop-level form of Theorem 3.2.5: monodromy along a concrete loop at `b` produces the fiber
point whose image subgroup is the corresponding conjugate. -/
private theorem mapOfEq_range_conjugate_of_monodromy_loop (hp : IsCoveringMap p) {b : B}
    (e : p ⁻¹' {b}) (γ : Path b b) :
    (mapOfEq ⟨p, hp.continuous⟩ (hp.monodromy ⟦γ⟧ e).2).range =
      MulAut.conj (fromPath ⟦γ⟧) • (mapOfEq ⟨p, hp.continuous⟩ e.2).range := by
  let e' := hp.monodromy ⟦γ⟧ e
  let δ : Path e.1 e'.1 :=
    Path.mk (hp.liftPath γ e.1 (γ.source.trans e.2.symm))
      (hp.liftPath_zero γ e.1 (γ.source.trans e.2.symm))
      rfl
  have hconj := mapOfEq_range_conjugate_of_path hp e e' δ
  have hproj : ((δ.map hp.continuous).cast e.2.symm e'.2.symm) = γ := by
    ext t
    simpa [δ, e'] using congr_fun (hp.liftPath_lifts γ e.1 (γ.source.trans e.2.symm)) t
  rwa [hproj] at hconj

/-- Helper for Theorem 3.2.5: monodromy along `g : π₁(B, b)` sends `e` to the canonical fiber
point whose image subgroup is the conjugate of the subgroup attached to `e`. -/
theorem mapOfEq_range_conjugate_of_monodromy (hp : IsCoveringMap p) {b : B}
    (e : p ⁻¹' {b}) (g : FundamentalGroup B b) :
    (mapOfEq ⟨p, hp.continuous⟩ (hp.monodromy g.toPath e).2).range =
      MulAut.conj g • (mapOfEq ⟨p, hp.continuous⟩ e.2).range := by
  induction g using Quotient.inductionOn with
  | h γ =>
      simpa using mapOfEq_range_conjugate_of_monodromy_loop hp e γ

/-- Theorem 3.2.5: every conjugate of the subgroup
`p_*(π₁(E, e)) ≤ π₁(B, b)` is realized as the image subgroup coming from some other point of the
fiber `p ⁻¹' {b}`. -/
-- Proof sketch: represent `g : π₁(B, b)` by a loop at `b`, lift that loop through `p` starting at
-- `e`, and let `e'` be the endpoint of the lifted loop. The lifted path gives the required
-- conjugacy relation between the two image subgroups.
theorem exists_fiberPoint_mapOfEq_range_eq_conjugate (hp : IsCoveringMap p) {b : B}
    (e : p ⁻¹' {b}) (g : FundamentalGroup B b) :
    ∃ e' : p ⁻¹' {b},
      (mapOfEq ⟨p, hp.continuous⟩ e'.2).range =
        MulAut.conj g • (mapOfEq ⟨p, hp.continuous⟩ e.2).range := by
  refine ⟨hp.monodromy g.toPath e, ?_⟩
  simpa using mapOfEq_range_conjugate_of_monodromy hp e g

end IsCoveringMap
