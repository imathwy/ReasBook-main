import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 9.15.3:
- primary domain: normality of algebraic intermediate-field extensions under lattice operations;
- sampled owner declarations:
  `Normal`,
  `normal_iff`,
  `IntermediateField.normal_iInf`,
  `IntermediateField.normal_inf`;
- best owner abstraction: the canonical owner is the mathlib typeclass `Normal`, with
  `IntermediateField.normal_iInf` as the intermediate-field lattice theorem owning the source
  construction;
- primitive data: a nonempty family `E : ι → IntermediateField F K` together with the pointwise
  normality instances `Normal F (E i)`;
- derived API: binary intersections are the special case `IntermediateField.normal_inf`, derived
  from the general intersection theorem.

Source/core/bridge triage:
- `source-facing`: the intersection of a nonempty family of normal intermediate extensions is
  normal;
- `core/canonical`: `IntermediateField.normal_iInf`;
- `bridge/view`: `IntermediateField.normal_inf` as the two-factor specialization.

This item adds no new mathematics beyond the canonical owner theorem, so the refined file should
remain a pure recall surface instead of introducing a parallel local lemma. -/

/- Lemma 9.15.3: for a nonempty family `E : ι → IntermediateField F K`, if each `E i / F` is
normal, then the intersection `⨅ i, E i` is normal over `F`. This is exactly the canonical
mathlib instance `IntermediateField.normal_iInf`, tagged `[stacks 09HP]`; the nonemptiness
hypothesis is the faithful formalization of the intended statement, since the empty intersection is
`⊤`. -/
recall IntermediateField.normal_iInf
