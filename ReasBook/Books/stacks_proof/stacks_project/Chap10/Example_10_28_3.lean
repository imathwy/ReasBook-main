import Mathlib.RingTheory.Ideal.Oka
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommSemiring R]

namespace Ideal

/-- Example 10.28.3: for a submonoid `S` of a commutative semiring `R`, the predicate on ideals
that an ideal meets `S` is an Oka predicate, rendered canonically as non-disjointness from `S`. -/
-- Proof sketch: for the `top` case, any element of `S`, for instance `1`, lies in `⊤ ∩ S`.
-- For the Oka condition, assume `(I ⊔ Ideal.span {a}) ∩ S` and `(I.colon (Ideal.span {a})) ∩ S`
-- are nonempty. Choose `s` from the first intersection and `s'` from the second. Then `s * s'`
-- still lies in `S` because `S` is multiplicative. Writing `s = i + ra` with `i ∈ I`, the colon
-- condition gives `s' * a ∈ I`, hence `s' * s = s' * i + r * (s' * a) ∈ I`. By commutativity,
-- `s * s' ∈ I ∩ S`, so `I` satisfies the predicate.
@[stacks 05KA]
theorem isOka_not_disjoint_submonoid (S : Submonoid R) :
    IsOka (fun I : Ideal R ↦ ¬ Disjoint (I : Set R) S) where
  top := by
    rw [Set.not_disjoint_iff_nonempty_inter]
    exact ⟨1, by simp⟩
  oka {I} {a} hsup hcolon := by
    rw [Set.not_disjoint_iff_nonempty_inter] at hsup hcolon ⊢
    rcases hsup with ⟨s, hsI, hsS⟩
    rcases hcolon with ⟨t, htI, htS⟩
    rcases mem_span_singleton_sup.mp (by simpa [sup_comm] using hsI) with ⟨r, i, hiI, hsi⟩
    refine ⟨t * s, ?_, S.mul_mem htS hsS⟩
    rw [← hsi, mul_add]
    refine I.add_mem ?_ (I.mul_mem_left t hiI)
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      I.mul_mem_left r (mem_colon_span_singleton.mp htI)

end Ideal

end
