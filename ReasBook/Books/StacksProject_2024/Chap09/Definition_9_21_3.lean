import StacksProject_2024.Chap09.Definition_9_15_8
import StacksProject_2024.Chap09.Definition_9_21_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

/- Domain-style sampling for Definition 9.21.3:
- primary domain: Galois extensions and their automorphism groups in field theory;
- sampled chapter/project owner declarations:
  `Gal(E / F)`,
  `(inferInstance : Group Gal(E / F))`,
  `IsGalois`,
  `IsGalois.card_aut_eq_finrank`;
- best owner abstraction: the canonical automorphism-group owner `Gal(E / F)` already recalled in
  Definition 9.15.8, with `IsGalois F E` from Definition 9.21.1 as the extension property naming
  the case in which this automorphism group is called the Galois group.

Layer triage:
- `source-facing`: the terminology that for a Galois extension `E/F`, the automorphism group of
  `E` over `F` is called the Galois group;
- `core/canonical`: `Gal(E / F)`;
- `bridge/view`: later owner theorems for Galois extensions, such as
  `IsGalois.card_aut_eq_finrank`.

Primitive data are only the field extension `E/F` and its `F`-algebra structure. The source's
extra `IsGalois` hypothesis does not create a new object; it only specifies the terminology for
the already canonical owner `Gal(E / F)`. So this file should remain a direct recall/check surface
rather than introduce any parallel local alias or wrapper.
-/

/- Definition 9.21.3 (Tag 09DV): when `E/F` is a Galois extension, its Galois group is the
already existing canonical automorphism group `Gal(E / F)`. -/
#check Gal(E / F)

/- Companion check: the Galois group uses the canonical group structure on `Gal(E / F)` induced by
composition. -/
#check (inferInstance : Group Gal(E / F))

end
