import Mathlib.FieldTheory.SeparableClosure

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {F : Type u} {E : Type v}
variable [Field F] [Field E] [Algebra F E] [Normal F E]

/- Domain-style sampling for Lemma 9.15.4:
- primary domain: normal algebraic field extensions and the separable closure inside a normal
  extension;
- sampled owner declarations:
  `Normal`,
  `separableClosure`,
  `separableClosure.normalClosure_eq_self`,
  `separableClosure.isGalois`;
- best owner abstraction: the source-faithful main surface is the canonical typeclass
  `Normal F (separableClosure F E)`;
- primitive data: none locally beyond the ambient normal extension `E / F`;
- derived API: the stronger bundled owner `IsGalois F (separableClosure F E)`, whose normality
  component gives the source statement.

Source/core/bridge triage:
- `source-facing`: normality of the intermediate field `separableClosure F E` over `F`;
- `core/canonical`: the owner typeclass `Normal`;
- `bridge/view`: the stronger instance `separableClosure.isGalois`.

This item should therefore remain a pure owner check surface. Replacing the main entry by a recall
of `separableClosure.isGalois` would strengthen the source statement from normality to Galoisness,
so the faithful refined form keeps the `Normal` conclusion as the main entry and treats the Galois
instance only as upstream support. -/
/- Lemma 9.15.4: if `E / F` is a normal algebraic field extension, then the subextension
`E / separableClosure F E / F` from Lemma 9.14.6 is normal; equivalently, the intermediate field
`separableClosure F E` is normal over `F`. In mathlib this is the normality component of the
canonical instance `separableClosure.isGalois`. -/
#check (inferInstance : Normal F (separableClosure F E))
