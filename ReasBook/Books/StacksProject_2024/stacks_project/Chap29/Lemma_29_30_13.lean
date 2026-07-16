import StacksProject_2024.stacks_project.Chap10.Definition_10_125_1
import StacksProject_2024.stacks_project.Chap10.Definition_10_136_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

namespace Presentation

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable {n c : ℕ}

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the scheme owner `Scheme.Hom.fiber`, but this project already
  packages the affine local fiber dimension as `relativeDimensionAt`, so the source statement is
  recorded directly in that owner.
-/

namespace IsRelativeGlobalCompleteIntersection

/-- Lemma 29.30.13: if `R → A` is given by a relative global complete intersection presentation
`P : Algebra.Presentation R A (Fin n) (Fin c)`, then for every `q : PrimeSpectrum A` the local
dimension of the fiber of `Spec(A) → Spec(R)` at `q` is the presentation dimension `P.dimension`.
For a presentation indexed by `Fin n` generators and `Fin c` relations, this is equivalently the
textbook value `n - c`. -/
@[stacks 02K0]
theorem relativeDimensionAt_eq
    {P : Algebra.Presentation R A (Fin n) (Fin c)}
    (hP : P.IsRelativeGlobalCompleteIntersection)
    (q : PrimeSpectrum A) :
    relativeDimensionAt R A q = P.dimension := sorry

/-- For a presentation `P : Algebra.Presentation R A (Fin n) (Fin c)`, the presentation
dimension in Lemma 29.30.13 specializes to the textbook integer `n - c`. -/
theorem relativeDimensionAt_eq_natSub
    {P : Algebra.Presentation R A (Fin n) (Fin c)}
    (hP : P.IsRelativeGlobalCompleteIntersection)
    (q : PrimeSpectrum A) :
    relativeDimensionAt R A q = (n - c : WithBot ℕ∞) := sorry

end IsRelativeGlobalCompleteIntersection

end

end Presentation

end Algebra
