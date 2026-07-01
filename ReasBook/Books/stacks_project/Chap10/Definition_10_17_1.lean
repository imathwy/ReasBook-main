import Mathlib.Tactic.Recall
import Mathlib.RingTheory.Spectrum.Prime.Topology

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open PrimeSpectrum
open scoped PrimeSpectrum

section

variable {R : Type u} [CommRing R]

/- Domain-style sampling for Definition 10.17.1:
- primary domain: the Zariski topology on the prime spectrum of a commutative ring;
- sampled owner declarations:
  `PrimeSpectrum`,
  `PrimeSpectrum.zeroLocus`,
  `PrimeSpectrum.mem_zeroLocus`,
  `PrimeSpectrum.basicOpen`,
  `PrimeSpectrum.mem_basicOpen`;
- best owner abstraction: the canonical `PrimeSpectrum` space together with its owner subsets
  `zeroLocus` and `basicOpen`;
- primitive data: a commutative ring `R`, a subset `T : Set R`, and an element `f : R`;
- derived API: the textbook notation `V(T)` and `D(f)` and their companion membership lemmas.

Source/core/bridge triage:
- `source-facing`: the Stacks notation `Spec(R)`, `V(T)`, and `D(f)`;
- `core/canonical`: `PrimeSpectrum`, `zeroLocus`, and `basicOpen`;
- `bridge/view`: the scoped notation and the membership lemmas `mem_V` and `mem_D`.

This item introduces no new mathematical owner, so the file should recall the canonical
`PrimeSpectrum` declarations directly and keep the notation layer thin.
-/
/- Definition 10.17.1 (1): for a ring `R`, `Spec(R)` is the canonical type `PrimeSpectrum R` of
prime ideals of `R`. -/
recall PrimeSpectrum

/- Definition 10.17.1 (2): for a subset `T ⊆ R`, the subset `V(T)` of `Spec(R)` is the canonical
zero locus `PrimeSpectrum.zeroLocus T`, consisting of the prime ideals containing `T`. -/
recall zeroLocus

/- Definition 10.17.1 (3): for an element `f ∈ R`, the subset `D(f)` of `Spec(R)` is represented
by the canonical open `PrimeSpectrum.basicOpen f`, whose underlying set consists of the prime
ideals not containing `f`. -/
recall basicOpen

/- Textbook basic-open notation on `Spec(R)`, attached to the owner `PrimeSpectrum.basicOpen`. -/
scoped[PrimeSpectrum] notation "D(" f ")" => basicOpen f

/-
Textbook closed-set notation on `Spec(R)`, attached to the owner `PrimeSpectrum.zeroLocus`.
-/
scoped[PrimeSpectrum] notation "V(" T ")" => zeroLocus T

/-- Membership in the textbook closed set `V(T)` means that the prime ideal contains `T`. -/
theorem mem_V (T : Set R) (p : PrimeSpectrum R) :
    p ∈ V(T) ↔ T ⊆ p.asIdeal := by
  exact mem_zeroLocus p T

/-- Membership in the textbook basic open `D(f)` means that the prime ideal does not contain `f`.
-/
theorem mem_D (f : R) (p : PrimeSpectrum R) :
    p ∈ D(f) ↔ f ∉ p.asIdeal := by
  exact mem_basicOpen f p

end
