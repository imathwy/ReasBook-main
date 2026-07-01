import Mathlib.RingTheory.Jacobson.Ring

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R]

/-- Lemma 10.35.3: if every prime ideal of `R` is the intersection of the maximal ideals
containing it, then `R` is a Jacobson ring. This is a thin source-faithful bridge to the
canonical owner criterion `isJacobsonRing_iff_sInf_maximal`. -/
theorem isJacobsonRing_of_prime_eq_sInf_maximals
    (h : ∀ P : Ideal R, P.IsPrime → P = sInf { J : Ideal R | P ≤ J ∧ J.IsMaximal }) :
    IsJacobsonRing R := by
  rw [isJacobsonRing_iff_sInf_maximal]
  intro P hP
  refine ⟨{ J : Ideal R | P ≤ J ∧ J.IsMaximal }, ?_, h P hP⟩
  intro J hJ
  exact Or.inl hJ.2

end
