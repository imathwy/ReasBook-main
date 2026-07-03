import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

/- Domain-style sampling for Definition 9.15.8:
- primary domain: automorphism groups of field extensions in Galois theory;
- sampled canonical declarations:
  `Gal(E / F)`,
  `(inferInstance : Group Gal(E / F))`,
  `AlgEquiv.restrictNormalHom`,
  `IsGalois.card_aut_eq_finrank`;
- best owner abstraction: `Gal(E / F)`, the canonical type of `F`-algebra automorphisms of `E`.

Layer triage:
- `core/canonical`: `Gal(E / F)`;
- `bridge/view`: restriction morphisms such as `AlgEquiv.restrictNormalHom` and later cardinality
  theorems such as `IsGalois.card_aut_eq_finrank`.

Primitive data are only the field extension `E/F` and its `F`-algebra structure. The group
structure and later restriction/counting API are derived from this owner, so this file should not
introduce a parallel local `Aut(E/F)` alias or wrapper.
-/

/- Definition 9.15.8: for a field extension `E/F`, the automorphism group `Aut(E/F)` is the
canonical mathlib owner `Gal(E / F)`, i.e. the type of `F`-algebra automorphisms of `E`. -/
#check Gal(E / F)

/- Companion check: `Gal(E / F)` carries the canonical group structure induced by composition. -/
#check (inferInstance : Group Gal(E / F))

end
