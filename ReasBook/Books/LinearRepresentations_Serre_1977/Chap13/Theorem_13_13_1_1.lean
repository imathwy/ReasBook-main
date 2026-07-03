import Mathlib.Tactic.Recall
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

-- Declarations for this item will be appended below by the statement pipeline.

open IsCyclotomicExtension.Rat

/- Source/core/bridge triage:
- `source-facing`: Theorem 13-13.1-1, Gauss's theorem identifying `Gal(ℚ(ζ_m)/ℚ)` with
  `(ℤ / mℤ)ˣ`.
- `core/canonical`: `IsCyclotomicExtension.Rat.galEquivZMod`.
- `bridge/view`: LinearRepresentations_Serre_1977-style `Γ`-notation and subgroup bridges are downstream chapter API; this
  file itself is pure recall of the owner equivalence.

Primitive data and the derived equivalence are already owned upstream in mathlib, so a local alias
here would be a duplicate wheel rather than a source-facing definition. -/

/- Theorem 13-13.1-1: Gauss's theorem for the rational field is the canonical cyclotomic Galois
equivalence `IsCyclotomicExtension.Rat.galEquivZMod`, identifying `Gal(ℚ(ζ_m)/ℚ)` with
`(ZMod m)ˣ`; in LinearRepresentations_Serre_1977's notation, this says that `Γ_ℚ = (ℤ / mℤ)ˣ`. -/
recall galEquivZMod
