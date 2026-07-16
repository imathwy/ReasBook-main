import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_64_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

namespace Ideal

variable (𝔭 : Ideal R) [𝔭.IsPrime]
variable [(𝔭.map (algebraMap R S)).IsPrime]

local notation "𝔭S" => 𝔭.map (algebraMap R S)

/-
Domain triage: this file stays in commutative algebra of prime ideals, flatness, and localization.
The owner abstraction is the source-facing `Ideal.symbolicPower` from `Definition_10_64_1`; this
lemma is a derived base-change statement for that owner, not a new wrapper notion.

Relevant upstream owner-side declarations inspected before refinement:
* `Ideal.symbolicPower` and `Ideal.symbolicPower_eq_ker_quotient_map_pow`
* `RingHom.Flat.generalizingMap_comap` / `Ideal.exists_ideal_le_liesOver_of_le`
* `IsLocalization.AtPrime.map_eq_maximalIdeal` and `IsLocalization.AtPrime.comap_maximalIdeal`
-/

-- Proof sketch: rewrite both symbolic powers through the owner declaration
-- `Ideal.symbolicPower`; flatness identifies the extension of the kernel
-- `R → R_𝔭 / 𝔭^n R_𝔭` with the kernel of the base-changed map
-- `S → S_𝔭 / 𝔭^n S_𝔭`, and the primeness of `𝔭S` lets one compare this with the defining kernel
-- of the symbolic power of `𝔭S`.
/-- Lemma 10.64.3: for a flat ring map `R → S`, if the extension `𝔭S` of a prime ideal `𝔭 ⊂ R`
is prime in `S`, then extending the `n`th symbolic power of `𝔭` to `S` gives the `n`th symbolic
power of `𝔭S`. -/
theorem map_symbolicPower_eq_symbolicPower_map (n : ℕ)
    : map (algebraMap R S) (𝔭.symbolicPower n) = symbolicPower 𝔭S n := sorry

end Ideal

end
