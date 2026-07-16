import Mathlib.RingTheory.Spectrum.Prime.Topology
import stacks_proof.stacks_project.Chap05.Definition_5_11_4
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R]

/- Domain-style sampling in the catenary API:
- topological owner: `CatenarySpace X`
- prime-spectrum owner: `PrimeSpectrum R`
- chapter source-facing bridge: `Definition_10_105_1` translates the source prime-chain wording to
  the Chapter 5 topological owner on `Spec R`

Layer triage:
- `source-facing`: the textbook condition that a commutative ring is catenary
- `core/canonical`: `CatenarySpace (PrimeSpectrum R)`
- `bridge/view`: the ring-level vocabulary alias `IsCatenaryRing R`

Primitive data is exactly the catenary-space structure on `Spec R`. The ring-level name is useful
high-reuse vocabulary downstream, but it should remain a thin alias to the canonical topological
owner rather than a one-field wrapper class that duplicates the same datum.
-/

/-- A commutative ring is catenary if its prime spectrum is catenary. This is a thin high-reuse
owner alias for the canonical topological owner on `Spec R`. -/
abbrev IsCatenaryRing (R : Type u) [CommRing R] : Prop :=
  CatenarySpace (PrimeSpectrum R)

/-- Lemma 10.105.2: a ring is catenary if and only if the topological space `Spec R` is
catenary. -/
@[stacks 02IH]
theorem isCatenaryRing_iff_catenarySpace_primeSpectrum :
    IsCatenaryRing R ↔ CatenarySpace (PrimeSpectrum R) :=
  Iff.rfl

end
