import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_9_2_1 (from Chap09) -/
universe u

variable (K : Type u) [Field K]

/- Domain triage:
- primary domain: basic field theory, specifically the canonical bundled owners for fields and
  subfields;
- sampled owner declarations: `Field`, `Subfield`, `SubfieldClass`, and `Subring.toSubfield`;
- core/canonical owner abstraction: `Field` for the ambient field structure, and the bundled type
  expression `Subfield K` for subfields of a fixed field;
- layer: item (1) is a direct `core/canonical` recall, while item (2) is a `source-facing` use of
  the canonical owner `Subfield K`, so this file should stay recall/check-only rather than
  introduce a parallel wrapper or alias;
- primitive data: a field structure on `K`, and for a subfield its carrier together with the
  inherited subring operations and inverse-closure;
- derived API: coercions to sets and subrings, the induced field structure on a subfield, and
  constructors such as `Subring.toSubfield`.
-/

/- Definition 9.2.1 (1): a field is the canonical mathlib typeclass `Field`, namely a nonzero
commutative ring in which every nonzero element is invertible. -/
recall Field

/- Definition 9.2.1 (2): for a field `K`, a subfield is the canonical structure `Subfield K`.
Mathlib defines this owner more generally for division rings; on a field it is exactly a subring
of `K` closed under multiplicative inverses, equivalently a subring that is itself a field. -/
#check (Subfield K)

/-! ### Definition_9_2_2 (from Chap09) -/
/- Definition 9.2.2: in the chapter's commutative-ring setting, the Stacks notion of an integral
domain is expressed by the canonical mathlib owner `IsDomain`; on a ring this is equivalent to
being nontrivial and having no zero divisors. -/
recall IsDomain

/- Definition 9.2.2 companion: on a ring, the source wording "nonzero and with `0` as the only
zerodivisor" is exactly the canonical theorem `isDomain_iff_noZeroDivisors_and_nontrivial`. -/
recall isDomain_iff_noZeroDivisors_and_nontrivial
