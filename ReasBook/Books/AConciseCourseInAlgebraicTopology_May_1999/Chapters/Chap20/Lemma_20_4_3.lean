import Mathlib.Analysis.InnerProductSpace.PiL2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_3_1

noncomputable section

-- Semantic recall via `lean_leansearch`: no canonical mathlib owner for this Euclidean
-- relative-to-local injectivity statement surfaced, while local Chapter 20 search verified
-- `relativeTopHomologyGroup` and `relativeToLocalTopHomologyMap` as the project owners. The
-- source `H_n(ℝ^n, U)` is therefore formalized by the chapter-local model
-- `relativeTopHomologyGroup ℤ n (EuclideanSpace ℝ (Fin n)) Uᶜ`.

section

variable {n : ℕ}

/-- Lemma 20.4.3: if `U ⊂ ℝ^n` is open and a class
`t ∈ H_n(ℝ^n, U; ℤ) = relativeTopHomologyGroup ℤ n (EuclideanSpace ℝ (Fin n)) Uᶜ`
has zero image in every local group `H_n(ℝ^n, ℝ^n \ {x}; ℤ)` for `x ∉ U`, then `t = 0`. -/
theorem eq_zero_of_forall_relativeToLocalTopHomologyMap_eq_zero_openSubsetEuclideanSpace
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
    (t : relativeTopHomologyGroup ℤ n (EuclideanSpace ℝ (Fin n)) Uᶜ)
    (ht : ∀ x : EuclideanSpace ℝ (Fin n), ∀ hx : x ∉ U,
      (relativeToLocalTopHomologyMap ℤ n (EuclideanSpace ℝ (Fin n)) Uᶜ hx) t = 0) :
    t = 0 := sorry

/-- Set-level companion for
`eq_zero_of_forall_relativeToLocalTopHomologyMap_eq_zero_openSubsetEuclideanSpace`. -/
theorem eq_zero_of_forall_relativeToLocalTopHomologyMap_eq_zero_of_isOpen
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (t : relativeTopHomologyGroup ℤ n (EuclideanSpace ℝ (Fin n)) Uᶜ)
    (ht : ∀ x : EuclideanSpace ℝ (Fin n), ∀ hx : x ∉ U,
      (relativeToLocalTopHomologyMap ℤ n (EuclideanSpace ℝ (Fin n)) Uᶜ hx) t = 0) :
    t = 0 :=
  eq_zero_of_forall_relativeToLocalTopHomologyMap_eq_zero_openSubsetEuclideanSpace ⟨U, hU⟩ t ht

end
