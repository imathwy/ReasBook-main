import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace ModuleCat

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (M N : ModuleCat R) [Module.Finite R M] [Module.Finite R N]

-- Proof sketch: choose a projective resolution of `N` by finite free modules using
-- `module_exists_finite_free_resolution`; tensor it with `M`, so every term remains a finite
-- module by `Module.Finite.tensorProduct`; then identify `Tor` as the homology of this complex and
-- use that subquotients of finite modules over a Noetherian ring are finite.
/-- Library-facing form of Lemma 10.75.7 (Tag `0AZ4`): over a Noetherian commutative ring, the
`p`-th `Tor` of two finite modules is finite. -/
theorem finite_tor (p : ℕ) :
    Module.Finite R (((Tor (ModuleCat R) p).obj M).obj N) := sorry

/-- Typeclass support for finiteness of `Tor_p^R(M, N)` under the hypotheses of
`ModuleCat.finite_tor`. -/
instance (p : ℕ) :
    Module.Finite R (((Tor (ModuleCat R) p).obj M).obj N) :=
  finite_tor M N p

end

end ModuleCat

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (M N : ModuleCat R) [Module.Finite R M] [Module.Finite R N]

/-- Lemma 10.75.7 (Tag 0AZ4): if `R` is Noetherian and `M`, `N` are finite `R`-modules, then
`Tor_p^R(M, N)` is a finite `R`-module for every `p`. -/
@[stacks 0AZ4]
theorem Lemma_10_75_7 (p : ℕ) :
    Module.Finite R (((Tor (ModuleCat R) p).obj M).obj N) :=
  ModuleCat.finite_tor M N p

end
