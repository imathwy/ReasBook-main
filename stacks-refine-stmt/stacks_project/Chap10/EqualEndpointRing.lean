import Mathlib

-- Declarations shared by the equal-endpoint examples in Chapter 10.

noncomputable section

open Polynomial

universe u

variable (k : Type u) [CommRing k]

/-- The equal-endpoint subring `R = {f ∈ k[x] | f(0) = f(1)}`. -/
noncomputable def equal_endpoint_poly_subring : Subring (Polynomial k) :=
  (Polynomial.eval₂RingHom (RingHom.id k) (0 : k)).eqLocus
    (Polynomial.eval₂RingHom (RingHom.id k) (1 : k))

/-- Membership in the equal-endpoint ring means that evaluation at `0` and `1` agree. -/
theorem mem_equal_endpoint_poly_subring_iff (f : Polynomial k) :
    f ∈ equal_endpoint_poly_subring k ↔
      Polynomial.eval₂RingHom (RingHom.id k) (0 : k) f =
        Polynomial.eval₂RingHom (RingHom.id k) (1 : k) f := by
  simp [equal_endpoint_poly_subring]
