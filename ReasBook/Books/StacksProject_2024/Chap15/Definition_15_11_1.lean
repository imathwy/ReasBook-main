import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open scoped Polynomial

variable {A : Type u} [CommRing A]

namespace Ideal

/- Domain-style sampling for henselian pairs:
- primary domain: henselian pairs and Hensel lifting for ideals in commutative rings
- primitive owner object: `HenselianRing A I`
- primitive owner fields: `HenselianRing.jac`, `HenselianRing.is_henselian`
- same-domain declarations inspected: `HenselianRing`, `HenselianRing.jac`,
  `HenselianRing.is_henselian`, `RingPairCat.henselianPairProperty`

Layer triage:
- `source-facing`: the Jacobson-radical clause and the coprime-factorization lifting clause from
  the textbook definition of a henselian pair
- `core/canonical`: the mathlib owner `HenselianRing A I`
- `bridge/view`: the factorization-lifting theorem below, which is derived from the owner field
  `HenselianRing.is_henselian`, together with the Jacobson-radical bridge to the chapter surface
  `I ≤ Ring.jacobson A`

Primitive data is exactly the Jacobson-radical field and the simple-root lifting field of
`HenselianRing A I`. The coprime-factorization statement is derived API: mathlib records the
canonical owner in simple-root form, while this file keeps the textbook factorization clause as a
source-facing bridge theorem instead of introducing a second wrapper notion. Likewise, the
Jacobson clause is exposed below on the chapter-level surface `I ≤ Ring.jacobson A` rather than
the lower-level field type `I ≤ Ideal.jacobson ⊥`.
-/

/- Definition 15.11.1: the canonical mathlib notion of a henselian ideal `I` in a commutative
ring `A` is `HenselianRing A I`. The companion declarations below record the Jacobson-radical and
factorization-lifting consequences appearing in the textbook formulation. -/
recall HenselianRing

/- The Jacobson-radical clause of Definition 15.11.1, on the chapter surface
`I ≤ Ring.jacobson A`, is the owner field `HenselianRing.jac` transported along
`Ideal.jacobson_bot`. -/
theorem le_ring_jacobson_of_henselianRing (I : Ideal A) [HenselianRing A I] :
    I ≤ Ring.jacobson A := by
  simpa [Ideal.jacobson_bot] using
    (show I ≤ Ideal.jacobson (⊥ : Ideal A) from HenselianRing.jac)

/- The primitive lifting clause of Definition 15.11.1 is the owner field
`HenselianRing.is_henselian`. -/
recall HenselianRing.is_henselian (I : Ideal A) [HenselianRing A I]
    (f : A[X]) (hf : f.Monic) (a₀ : A)
    (ha₀ : f.eval a₀ ∈ I)
    (hderiv : IsUnit ((Ideal.Quotient.mk I) (f.derivative.eval a₀))) :
    ∃ a : A, f.IsRoot a ∧ a - a₀ ∈ I

-- Proof sketch: translate the coprime residue factorization into the simple-root formulation used
-- by `HenselianRing`, lift the corresponding simple root, and reconstruct the lifted monic factors
-- with the prescribed reductions from that lifted root.
/-- A henselian ideal lifts monic coprime factorizations modulo the ideal. -/
theorem exists_monic_coprime_factorization_lift (I : Ideal A) [HenselianRing A I]
    (f : A[X]) (hf : f.Monic) (g₀ h₀ : (A ⧸ I)[X]) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcoprime : IsCoprime g₀ h₀)
    (hfactor : f.map (Ideal.Quotient.mk I) = g₀ * h₀) :
    ∃ g h : A[X],
      g.Monic ∧ h.Monic ∧
        f = g * h ∧
          g.map (Ideal.Quotient.mk I) = g₀ ∧
            h.map (Ideal.Quotient.mk I) = h₀ := sorry

end Ideal

end
