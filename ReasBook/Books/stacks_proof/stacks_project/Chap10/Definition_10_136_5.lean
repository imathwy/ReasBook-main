import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

namespace Algebra

namespace Presentation

variable {n c : ℕ}

/-- A finite presentation `P : R[x₁, …, xₙ] ⟶ S` exhibits `S` as a relative global complete
intersection over `R` if every nonempty fiber of `S` has Krull dimension equal to the
presentation dimension `n - c`. This is the presentation-level source-facing owner underlying the
intrinsic existential class `Algebra.IsRelativeGlobalCompleteIntersection R S`. -/
def IsRelativeGlobalCompleteIntersection (P : Algebra.Presentation R S (Fin n) (Fin c)) : Prop :=
  ∀ p : PrimeSpectrum R,
    Nonempty (PrimeSpectrum (p.asIdeal.Fiber S)) →
      ringKrullDim (p.asIdeal.Fiber S) = P.dimension

end Presentation

/- Source/core/bridge triage:
* source-facing: `IsRelativeGlobalCompleteIntersection R S`, the textbook relative global complete
  intersection condition;
* core/canonical: a finite algebra presentation `Algebra.Presentation R S (Fin n) (Fin c)` and
  the canonical finiteness owner `Algebra.FinitePresentation R S`;
* bridge/view: the presentation-level owner
  `Algebra.Presentation.IsRelativeGlobalCompleteIntersection` and explicit quotient-model or
  map-based reformulations in later files.

Primitive data are exactly one finite presentation together with the fiber-dimension condition.
Finite presentation of `S` over `R` is therefore derived API and should not remain a parallel
public wrapper around the same witness.
-/
/-- Definition 10.136.5: an `R`-algebra `S` is a relative global complete intersection if it
admits a presentation by `n` generators and `c` relations, and for every prime `p` of `R` whose
fiber is nonempty, the fiber ring `κ(p) ⊗[R] S` has Krull dimension equal to the presentation
dimension. -/
@[stacks 00SP]
class IsRelativeGlobalCompleteIntersection (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] : Prop where
  exists_presentation :
    ∃ (n c : ℕ) (P : Algebra.Presentation R S (Fin n) (Fin c)),
        P.IsRelativeGlobalCompleteIntersection

/-- A presentation-level witness upgrades directly to the intrinsic relative global complete
intersection class. -/
theorem Presentation.toIsRelativeGlobalCompleteIntersection
    {n c : ℕ}
    {P : Algebra.Presentation R S (Fin n) (Fin c)}
    (hP : P.IsRelativeGlobalCompleteIntersection) :
    Algebra.IsRelativeGlobalCompleteIntersection R S where
  exists_presentation := ⟨n, c, P, hP⟩

instance instFinitePresentationOfIsRelativeGlobalCompleteIntersection
    [h : IsRelativeGlobalCompleteIntersection R S] : Algebra.FinitePresentation R S := by
  rcases h.exists_presentation with ⟨n, c, P, _⟩
  simpa using P.finitePresentation_of_isFinite

end Algebra

end
