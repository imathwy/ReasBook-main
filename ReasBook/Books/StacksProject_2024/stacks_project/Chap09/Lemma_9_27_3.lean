import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open IntermediateField

universe u v

/- Domain-style sampling for Lemma 9.27.3:
- primary domain: algebraic / normal field extensions, relative separable closures, purely
  inseparable intermediate fields, and fixed fields of automorphism groups;
- sampled canonical owners:
  `perfectClosure`,
  `perfectClosure.isPurelyInseparable`,
  `separableClosure.isGalois`,
  `IntermediateField.linearDisjoint_of_isPurelyInseparable_of_isSeparable`;
- best owner abstraction: the canonical intermediate fields `separableClosure F E` and
  `perfectClosure F E`, with `Normal F E` as the ambient normal-case owner and the fixed-field
  presentation demoted to a companion bridge theorem;
- primitive data: none locally beyond the ambient field extension hypotheses, with algebraicity
  already part of `Normal F E` on the normal side;
- derived API: the normal-case bridge to `fixedField (⊤ : Subgroup Gal(E/F))`, the Galois
  structure of `E / perfectClosure F E`, and the final decomposition statement.

Source/core/bridge triage:
- `source-facing`: the normal algebraic decomposition into separable and purely inseparable parts;
- `core/canonical`: `separableClosure`, `perfectClosure`, `IsPurelyInseparable`,
  `IsGalois`, and `LinearDisjoint`;
- `bridge/view`: the theorem identifying `perfectClosure F E` with the fixed field of the full
  automorphism group. -/

section AlgebraicPart

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
  [Algebra.IsAlgebraic F E]

/- For any algebraic extension `E / F`, the ambient extension is purely inseparable over the
canonical intermediate field `separableClosure F E`. This is exactly the owner instance
`separableClosure.isPurelyInseparable`. -/
recall separableClosure.isPurelyInseparable

/- In particular, for the algebraic extensions considered here, the canonical purely inseparable
part over `F` is the owner instance `perfectClosure.isPurelyInseparable`. -/
recall perfectClosure.isPurelyInseparable

end AlgebraicPart

section NormalAlgebraicPart

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
  [Normal F E]

/- In the normal case, the separable closure inside `E` is already Galois over `F`. This is the
canonical owner instance `separableClosure.isGalois`. -/
recall separableClosure.isGalois

-- Proof sketch: the canonical purely inseparable intermediate field `perfectClosure F E` is
-- pointwise fixed by every `F`-automorphism of `E`, while the maximality theorem
-- `le_perfectClosure_iff` identifies any purely inseparable intermediate field with a subfield of
-- `perfectClosure F E`.
/-- In a normal algebraic extension, the fixed field of the full automorphism group is exactly the
canonical purely inseparable part `perfectClosure F E`. -/
theorem perfectClosure_eq_fixedField_top_of_normal_algebraic :
    perfectClosure F E = fixedField (⊤ : Subgroup Gal(E/F)) := sorry

-- Proof sketch: first identify the purely inseparable part with the fixed field of the full
-- automorphism group, then transport the standard fixed-field Galois statement across that
-- equality.
/-- In a normal algebraic extension, the ambient field is Galois over its canonical purely
inseparable part `perfectClosure F E`. -/
theorem isGalois_over_perfectClosure_of_normal_algebraic :
    IsGalois (perfectClosure F E) E := sorry

-- Proof sketch: combine the canonical purely inseparable owner `perfectClosure F E` with the
-- canonical separable owner `separableClosure F E`; linear disjointness comes from the
-- purely-inseparable/separable criterion, and the normal-case Galois theorem over
-- `perfectClosure F E` yields that their compositum is all of `E`. The fixed-field description is
-- then recovered from `perfectClosure_eq_fixedField_top_of_normal_algebraic`.
/-- Lemma 9.27.3: for a normal algebraic extension `E/F`, the canonical separable part
`separableClosure F E` and the canonical purely inseparable part `perfectClosure F E` are
linearly disjoint over `F` and generate all of `E`; equivalently, `E` is the tensor product of
its separable and purely inseparable parts over `F`. -/
theorem normal_algebraic_separable_inseparable_decomposition :
    (separableClosure F E).LinearDisjoint (perfectClosure F E) ∧
      separableClosure F E ⊔ perfectClosure F E = ⊤ := sorry

end NormalAlgebraicPart
