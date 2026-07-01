import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Definition 9.15.1:
- primary domain: normal algebraic field extensions and their splitting criteria;
- sampled owner declarations:
  `Normal`,
  `normal_iff`,
  `Normal.splits`,
  `Normal.of_algEquiv`;
- best owner abstraction: the extension-level owner is the canonical mathlib typeclass
  `Normal F E`;
- primitive data: none locally, since the source notion and its pointwise splitting
  characterization are already owned upstream;
- derived API: `normal_iff` exposes the source-style criterion, while `Normal.splits` and
  `Normal.of_algEquiv` supply standard consequences and transport.

Source/core/bridge triage:
- `source-facing`: the textbook notion that an algebraic field extension is normal;
- `core/canonical`: `Normal`;
- `bridge/view`: the splitting criterion `normal_iff`.

This file should therefore remain a pure recall surface. A local theorem restating `normal_iff`
under an ambient algebraicity hypothesis would only duplicate the canonical owner API. -/

/- Definition 9.15.1: for an algebraic field extension `E/F`, the textbook notion that `E` is
normal over `F` is the canonical mathlib typeclass `Normal F E`, which already packages the
algebraicity of the extension. -/
recall Normal

/- Companion recall for Definition 9.15.1: `normal_iff` is the canonical source-facing
characterization of normality by splitting of minimal polynomials; under an ambient algebraicity
hypothesis, its integrality clause is automatic. -/
recall normal_iff
