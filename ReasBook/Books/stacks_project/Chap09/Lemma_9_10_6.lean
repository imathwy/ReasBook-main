import Mathlib.FieldTheory.IsAlgClosed.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

/- Domain triage:
- primary domain: algebraic closures of fields and canonical comparison isomorphisms;
- sampled owner declarations: `IsAlgClosure`, `IsAlgClosed.lift`, `IsAlgClosure.isAlgClosed`, and
  `IsAlgClosure.equiv`;
- owner abstraction: `IsAlgClosure.equiv`;
- layer targeted here: `source-facing`, since Lemma 9.10.6 is the textbook field-level statement
  that any two algebraic closures of a field are isomorphic, obtained by specializing the
  canonical owner theorem;
- primitive data: a field `F`, two `F`-algebra fields `L` and `M`, and `IsAlgClosure` instances on
  `L` and `M`;
- derived API: the broader integral-domain theorem remains upstream as the canonical owner, while
  this file records only its field-specialized surface.
-/

variable (F : Type u) (L : Type v) (M : Type w)
variable [Field F] [Field L] [Field M] [Algebra F L] [Algebra F M]
variable [IsAlgClosure F L] [IsAlgClosure F M]

/- Lemma 9.10.6: any two algebraic closures of a field are isomorphic. For algebraic closures
`L/F` and `M/F`, the canonical `F`-algebra isomorphism is `IsAlgClosure.equiv F L M`. -/
#check (IsAlgClosure.equiv F L M : L ≃ₐ[F] M)
