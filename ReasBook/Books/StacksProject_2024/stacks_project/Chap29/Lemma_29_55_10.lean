import StacksProject_2024.stacks_project.Chap29.Definition_29_55_9
import StacksProject_2024.stacks_project.Chap29.Lemma_29_54_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable (A : Type u) [CommRing A]

-- Semantic recall: `lean_leansearch` surfaced the affine spectrum owner `Spec`, while local
-- Chapter 29 precedent fixes the owners as `Scheme.WeaklyNormal`, `SeminormalRing`, and the
-- finite-irreducible-components-to-compact-opens bridge from Lemma 29.54.7. The Stacks tag
-- evidence is consistent: item tag `0H3T` agrees with the source URL ending in `/tag/0H3T`.

/-- Lemma 29.55.10: let `X = Spec(A)` be an affine scheme with finitely many irreducible
components. Then `X` is weakly normal if and only if `A` is seminormal and, for every prime
number `p` and `z, w : A`, if `z` is a nonzerodivisor, `w^p` is divisible by `z^p`, and
`p * w` is divisible by `z`, then `w` is divisible by `z`. -/
@[stacks 0H3T]
theorem weaklyNormal_Spec_iff_seminormalRing_and_primeDivisibility
    [Finite (irreducibleComponents (Spec (CommRingCat.of A)))] :
    Scheme.WeaklyNormal (Spec (CommRingCat.of A)) ↔
      SeminormalRing A ∧
        ∀ p : ℕ, Nat.Prime p →
          ∀ z w : A,
            z ∈ nonZeroDivisors A →
            z ^ p ∣ w ^ p →
            z ∣ (p : A) * w →
            z ∣ w := sorry

end

end AlgebraicGeometry
