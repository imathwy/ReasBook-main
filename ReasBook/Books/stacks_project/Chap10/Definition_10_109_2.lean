import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

namespace ModuleCat

variable {R : Type u} [Ring R]

/- 
Domain-style sampling:
- primary domain: projective dimension in the abelian category `ModuleCat R`.
- inspected owner declarations:
  `CategoryTheory.projectiveDimension`,
  `CategoryTheory.projectiveDimension_ne_top_iff`,
  `CategoryTheory.projectiveDimension_le_iff`,
  `CategoryTheory.HasProjectiveDimensionLE`.
- best owner abstraction: `projectiveDimension`.
- source/core/bridge triage:
  `source-facing`: finite projective dimension for an `R`-module;
  `core/canonical`: `projectiveDimension`;
  `bridge/view`: `projectiveDimension_ne_top_iff` together with `projectiveDimension_le_iff`.
- primitive data vs derived API: there is no extra source-defined data here; the invariant
  `projectiveDimension` is primitive, while the existence of a natural-number bound is derived API.
-/

/- Definition 10.109.2: finite projective dimension for an `R`-module is expressed by the
canonical invariant `CategoryTheory.projectiveDimension`. -/
#check (projectiveDimension : ModuleCat.{v} R → WithBot ℕ∞)

/- Companion recall: `projectiveDimension M ≠ ⊤` is the canonical finite-projective-dimension
criterion, and with `projectiveDimension_le_iff` it is equivalent to the existence of a natural
number bound on `projectiveDimension M`. -/
recall projectiveDimension_ne_top_iff
recall projectiveDimension_le_iff

end ModuleCat
