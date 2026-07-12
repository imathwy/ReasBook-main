import StacksProject_2024.Chap29.Lemma_29_37_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}

/- Semantic recall:
`lean_leansearch` surfaced the canonical `UniversallyClosed`, `IsOpenImmersion`, and `IsIso`
scheme-morphism predicates. Local inspection found the Chapter 29 owner
`RelativelyAmpleProjPresentation`; the canonical pushforward relative-`Proj` comparison of
Lemma 29.37.4 is exposed there as the concrete morphism `presentation.comparison` together with
the canonical graded-pushforward and adjunction-map hypotheses below. The Stacks tag evidence is
consistent: item tag `0C6J` agrees with the source URL ending in `/tag/0C6J`.
-/

/-- Lemma 29.43.17: if `f : X ⟶ S` is universally closed and `L` is an `f`-ample invertible
module, then the canonical morphism
`X ⟶ Proj_S(⨁_{d ≥ 0} f_* L^{⊗ d})` supplied by Lemma 29.37.4 is an isomorphism. In the current
relative-`Proj` interface, that morphism is the comparison map of an explicit canonical
pushforward presentation. -/
@[stacks 0C6J]
theorem canonicalRelativeProjComparison_isIso_of_universallyClosed
    [Scheme.Modules.Invertible L] [RelativelyAmple f L]
    (hf : UniversallyClosed f)
    (presentation : RelativelyAmpleProjPresentation f L)
    (hcanonical_domain : presentation.domain = ⊤)
    (hcanonical_algebra : ∀ d : ℕ,
      presentation.algebra (Int.ofNat d) =
        (Scheme.Modules.pushforward f).obj ((inferInstance : Scheme.Modules.Invertible L) d))
    (hcanonical_psi : ∀ d : ℕ,
      presentation.psi d =
        (Scheme.Modules.pullback f).map (eqToHom (hcanonical_algebra d)) ≫
          (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app
            ((inferInstance : Scheme.Modules.Invertible L) d))
    (hcomparison_open : IsOpenImmersion presentation.comparison) :
    IsIso presentation.comparison := sorry

end

end AlgebraicGeometry
