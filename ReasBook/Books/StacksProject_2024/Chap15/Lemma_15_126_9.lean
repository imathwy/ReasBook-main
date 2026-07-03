import Mathlib
import StacksProject_2024.Chap15.Lemma_15_126_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

-- Source/core/bridge triage:
-- * source-facing: the lemma asserts stability of a system of parameters whose distinguished
--   first entry is the prescribed element `f`;
-- * core/canonical: the owner abstractions are `IsSystemOfParameters`, `parameterIdeal`, and the
--   canonical ordered family `Fin.cons f y`;
-- * bridge/view: the previous existential packaging by a family `x`, an index `i`, and an
--   equality `x i = f` was only a coordinate-level presentation of the same ordered family, so it
--   should be replaced by the owner-level `Fin.cons` form already used in Lemma `15.126.3`.
-- Proof sketch: apply Lemma `15.126.3` to choose a tail `y` such that `Fin.cons f y` is a system
-- of parameters. Since its parameter ideal is an ideal of definition, Lemma `10.32.5` gives a
-- power of the maximal ideal contained in that parameter ideal. For `h` in that power, write `h`
-- modulo the chosen parameter family so that replacing the head entry `f` by `f + h` does not
-- change the generated ideal. Equality of parameter ideals then gives both the perturbed
-- system-of-parameters statement and the equality of quotient lengths.
/-- Lemma 15.126.9: write `dim R = d + 1`. If `f : maximalIdeal R` avoids every minimal prime of
`R`, then there exist `d` further parameters and an exponent `n` such that the ordered family
`Fin.cons f y` is a system of parameters, and every perturbation of the distinguished head entry by
an element of `(maximalIdeal R)^(n + 1)` again yields a system of parameters with the same
quotient length. -/
theorem exists_systemOfParameters_stable_under_highOrder_perturbation_of_not_mem_minimalPrimes
    {d : ℕ} (hdim : ringKrullDim R = d.succ) (f : maximalIdeal R)
    (hmin : ∀ p ∈ minimalPrimes R, (f : R) ∉ p) :
    ∃ y : Fin d → maximalIdeal R, ∃ n : ℕ,
      IsSystemOfParameters (Fin.cons f y) ∧
        ∀ h : maximalIdeal R, ((h : R) ∈ maximalIdeal R ^ (n + 1)) →
          IsSystemOfParameters (Fin.cons (f + h) y) ∧
            Module.length R (R ⧸ parameterIdeal (Fin.cons f y)) =
              Module.length R (R ⧸ parameterIdeal (Fin.cons (f + h) y)) := sorry

end
