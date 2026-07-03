import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.CategoryTheory.Monoidal.Tor

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe u

section

variable (R : Type u) [CommRing R]
variable (A B : Type u) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

set_option quotPrecheck false in
notation "Tor[" R ", " p "](" M ", " N ")" =>
  (((Tor (ModuleCat R) p).obj (ModuleCat.of R M)).obj (ModuleCat.of R N))

/-- Definition 15.61.1: two `R`-algebras are Tor independent over `R` if all positive Tor groups
`Tor_p^R(A, B)` vanish. -/
def IsTorIndependent : Prop :=
  ∀ p : ℕ, 0 < p → IsZero (Tor[R, p](A, B))

-- Proof sketch: unfold `IsTorIndependent`; the result is exactly the defining vanishing condition
-- specialized to the chosen positive degree `p`.
/-- Tor independence gives the vanishing of each positive Tor group. -/
theorem IsTorIndependent.isZero_tor (h : IsTorIndependent R A B) {p : ℕ} (hp : 0 < p) :
    IsZero (Tor[R, p](A, B)) :=
  h p hp

end
