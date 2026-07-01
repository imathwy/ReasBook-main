import Mathlib
import Mathlib.RingTheory.Polynomial.Content

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Polynomial

noncomputable section

open scoped Function

variable {K : Type u} [Field K]

attribute [local instance] Classical.decEq

section FiniteFamily

variable {ι : Type v} [Fintype ι]

/- Definition 1.3.7 (1): for a finite family of polynomials indexed by `Fin n`, the canonical gcd
owner is `Finset.gcd` specialized to `Finset.univ`. Over a field, this gcd is normalized, so it is
the monic generator of the ideal spanned by the family. -/
#check (fun {n : ℕ} (P : Fin n → K[X]) ↦ (Finset.univ : Finset (Fin n)).gcd P)

/-- The canonical gcd of a finite polynomial family generates exactly the ideal spanned by that
family. -/
theorem span_singleton_gcd_eq_span_range (P : ι → K[X]) :
    Ideal.span ({(Finset.univ : Finset ι).gcd P} : Set K[X]) = Ideal.span (Set.range P) := by
  let I : Ideal K[X] := Ideal.span (Set.range P)
  have hleft : I ≤ Ideal.span ({(Finset.univ : Finset ι).gcd P} : Set K[X]) := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact Ideal.mem_span_singleton.mpr <|
      show (Finset.univ : Finset ι).gcd P ∣ P i from Finset.gcd_dvd (Finset.mem_univ i)
  have hgen :
      Ideal.span ({Submodule.IsPrincipal.generator I} : Set K[X]) = I :=
    Ideal.span_singleton_generator I
  have hgen_dvd : Submodule.IsPrincipal.generator I ∣ (Finset.univ : Finset ι).gcd P := by
    refine Finset.dvd_gcd ?_
    intro i _
    exact (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp <| Ideal.subset_span ⟨i, rfl⟩
  have hright : Ideal.span ({(Finset.univ : Finset ι).gcd P} : Set K[X]) ≤ I := by
    rw [Ideal.span_singleton_le_iff_mem, ← hgen]
    exact Ideal.mem_span_singleton.mpr hgen_dvd
  exact le_antisymm hright hleft

/-- A polynomial divides the canonical gcd of a finite family exactly when it divides every
member of the family. -/
theorem dvd_univ_gcd_iff (P : ι → K[X]) {Q : K[X]} :
    Q ∣ (Finset.univ : Finset ι).gcd P ↔ ∀ i : ι, Q ∣ P i := by
  simpa using
    (Finset.dvd_gcd_iff :
      Q ∣ (Finset.univ : Finset ι).gcd P ↔
        ∀ i ∈ (Finset.univ : Finset ι), Q ∣ P i)

end FiniteFamily

/- Definition 1.3.7 (2): a finite family of polynomials is mutually coprime exactly when its
canonical gcd is `1`. -/
#check (fun {n : ℕ} (P : Fin n → K[X]) ↦ (Finset.univ : Finset (Fin n)).gcd P = 1)

/- Definition 1.3.7 (3): a finite family of polynomials is pairwise coprime exactly when it
satisfies the canonical pairwise relation `Pairwise (IsCoprime on P)`. -/
#check (fun {n : ℕ} (P : Fin n → K[X]) ↦ Pairwise (IsCoprime on P))

end

end Polynomial
