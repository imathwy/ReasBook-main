import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 10.36.4: a finite set of elements of an `R`-algebra `S` is integral over `R`
elementwise if and only if it is contained in an `R`-subalgebra of `S` that is finite over
`R`. -/
theorem forall_isIntegral_iff_exists_subalgebra_finite_containing {s : Set S} (hs : s.Finite) :
    (∀ x ∈ s, IsIntegral R x) ↔
      ∃ S' : Subalgebra R S, Module.Finite R S' ∧ s ⊆ S' := by
  constructor
  · intro hs_integral
    exact ⟨adjoin R s, finite_adjoin_of_finite_of_isIntegral hs hs_integral, subset_adjoin⟩
  · rintro ⟨S', hS', hsS'⟩ x hx
    letI := hS'
    have hInt : Algebra.IsIntegral R S' := inferInstance
    exact S'.isIntegral_iff.mp hInt x (hsS' hx)

end
