import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the canonical scheme and ring owners
  `Scheme.Hom.QuasiFiniteAt`, `LocallyQuasiFinite`, and `Algebra.QuasiFiniteAt`.
- Local Chapter 29 precedent uses `Scheme.Hom.fiber`, `Scheme.Hom.asFiber`, and affine-open
  points as `IsAffineOpen.fromSpec p`; the affine condition below uses the induced algebra
  structure from `f.appLE V U e`.
-/

/-- Lemma 29.20.6: for a locally finite type morphism of schemes `f : X ⟶ S` and a point
`x : X`, the following are equivalent: `f` is quasi-finite at `x`; `x` is isolated in the
scheme-theoretic fiber over `f x`; `x` is closed in that fiber and no distinct fiber point
specializes to it; and every affine-open presentation around `x` gives a quasi-finite ring map at
the corresponding prime. -/
@[stacks 01TH]
theorem quasiFiniteAt_tfae_isOpen_singleton_asFiber_and_affineOpen
    [LocallyOfFiniteType f] (x : X) :
    List.TFAE
      [ f.QuasiFiniteAt x
      , IsOpen ({f.asFiber x} : Set (f.fiber (f x)))
      , f.asFiber x ∈ closedPoints (f.fiber (f x)) ∧
          ∀ x' : f.fiber (f x), x' ≠ f.asFiber x → ¬ Specializes x' (f.asFiber x)
      , ∀ ⦃U : X.Opens⦄, ∀ hU : IsAffineOpen U,
          ∀ ⦃V : S.Opens⦄, ∀ hV : IsAffineOpen V, ∀ e : U ≤ f ⁻¹ᵁ V,
            ∀ q : PrimeSpectrum (Γ(X, U)), hU.fromSpec q = x →
              let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
              Algebra.FiniteType Γ(S, V) Γ(X, U) ∧
                Algebra.QuasiFiniteAt Γ(S, V) q.asIdeal
      ] := sorry

end Scheme.Hom
end AlgebraicGeometry
