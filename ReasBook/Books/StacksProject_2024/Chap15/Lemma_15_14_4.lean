import Mathlib
import stacks_project.Chap15.Definition_15_14_1

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u

section

variable {A : Type u} [CommRing A]

/-
Domain-style sampling for Lemma 15.14.4:
- primary domain: commutative algebra of absolute integral closedness, integrality, and
  localization;
- sampled owner-level declarations:
  `IsAbsolutelyIntegrallyClosed`,
  `IsAbsolutelyIntegrallyClosed.exists_root`,
  `IsAbsolutelyIntegrallyClosed.of_exists_root`,
  `IsIntegrallyClosedIn`,
  `isIntegrallyClosedIn_iff`,
  `IsIntegrallyClosedIn.algebraMap_eq_of_integral`;
- best owner abstraction: the theorem is `source-facing`, but its proof should use the chapter
  owner `IsAbsolutelyIntegrallyClosed` through the canonical root-existence bridge, and the
  overring owner `IsIntegrallyClosedIn A (Localization S)` directly rather than the image-subring
  bridge view;
- primitive data: the owner predicate `IsAbsolutelyIntegrallyClosed A` and the integrally closed
  owner hypothesis `IsIntegrallyClosedIn A (Localization S)`;
- derived API: root existence for monic polynomials, obtained from
  `IsAbsolutelyIntegrallyClosed.exists_root`.

Source/core/bridge triage:
- `source-facing`: `isAbsolutelyIntegrallyClosed_of_isIntegrallyClosedIn_localization`;
- `core/canonical`: `IsAbsolutelyIntegrallyClosed`, `IsIntegrallyClosedIn`;
- `bridge/view`: the old image-subring packaging via `(algebraMap A (Localization S)).range`,
  which this refinement removes from the public hypothesis.
-/

-- Proof sketch: for a monic polynomial `f` over `A`, map it to a monic polynomial over
-- `Localization S`. Absolute integral closedness of the localization splits the image polynomial.
-- Every resulting root is integral over `A`, and `isIntegrallyClosedIn_iff` supplies injectivity
-- of the localization map together with descent of integral elements, yielding a root of `f`
-- already in `A`.
/-- Lemma 15.14.4: if `Localization S` is absolutely integrally closed and `A` is integrally
closed in `Localization S`, then `A` is absolutely integrally closed. -/
theorem isAbsolutelyIntegrallyClosed_of_isIntegrallyClosedIn_localization (S : Submonoid A)
    [IsIntegrallyClosedIn A (Localization S)]
    [IsAbsolutelyIntegrallyClosed (Localization S)] : IsAbsolutelyIntegrallyClosed A := by
  let φ : A →+* Localization S := algebraMap A (Localization S)
  have hφ : Function.Injective φ := (isIntegrallyClosedIn_iff.mp ‹IsIntegrallyClosedIn A (Localization S)›).1
  refine IsAbsolutelyIntegrallyClosed.of_exists_root fun f hf hdeg ↦ ?_
  let f' : (Localization S)[X] := f.map φ
  have hf' : f'.Monic := hf.map φ
  have hdeg' : f'.degree ≠ 0 := by
    simpa [f', Polynomial.degree_map_eq_of_injective hφ] using hdeg
  obtain ⟨x, hx⟩ := IsAbsolutelyIntegrallyClosed.exists_root f' hf' hdeg'
  have hxint : IsIntegral A x := ⟨f, hf, by simpa [f', φ] using hx.eq_zero⟩
  obtain ⟨a, ha⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hxint
  refine ⟨a, hφ ?_⟩
  have hxa : Polynomial.eval₂ φ (φ a) f = 0 := by
    simpa [φ, f', Polynomial.eval_map, ← ha] using hx.eq_zero
  calc
    φ (Polynomial.eval a f) = Polynomial.eval₂ φ (φ a) f := by
      symm
      exact Polynomial.eval₂_at_apply φ a
    _ = 0 := hxa
    _ = φ 0 := by simp

end
