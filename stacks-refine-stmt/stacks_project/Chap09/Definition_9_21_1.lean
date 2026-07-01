import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Definition 9.21.1:
- primary domain: Galois field extensions in field theory;
- sampled owner declarations:
  `Algebra.IsSeparable`,
  `Normal`,
  `IsGalois`;
- sampled derived/specification API:
  `isGalois_iff`;
- best owner abstraction: the extension-level owner is the canonical mathlib typeclass
  `IsGalois F E`;
- primitive data: none locally, since the source notion is already owned upstream;
- derived API: the source-style characterization by separability and normality is already packaged
  by `isGalois_iff`.

Source/core/bridge triage:
- `source-facing`: the textbook notion that a field extension is Galois;
- `core/canonical`: `IsGalois`;
- `bridge/view`: `isGalois_iff`.

This file should therefore remain a pure recall surface. Any local alias or restated wrapper would
only duplicate the owner declaration already provided by mathlib. -/

/- Definition 9.21.1: for a field extension `E/F`, the canonical mathlib notion of a Galois
extension is `IsGalois F E`. -/
recall IsGalois

/- Companion recall: the textbook characterization of a Galois extension as algebraic,
separable, and normal is canonically packaged by `isGalois_iff`; the algebraicity clause is
already absorbed by the canonical owner predicates `Algebra.IsSeparable` and `Normal`. -/
recall isGalois_iff
