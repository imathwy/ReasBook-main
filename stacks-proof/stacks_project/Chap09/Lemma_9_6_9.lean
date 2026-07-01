import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.TensorProduct.Nontrivial

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

/-
Domain-style sampling for common overfields of field extensions:
- primary domain: tensor-product constructions for field extensions over a base field;
- sampled canonical declarations: `Ideal.exists_maximal`, `Ideal.Quotient.field`,
  `Ideal.Quotient.mkₐ`, `Algebra.TensorProduct.includeLeft`, `Algebra.TensorProduct.includeRight`,
  and the stronger nearby owner theorems
  `Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective` and
  `IntermediateField.LinearDisjoint.exists_field_of_isDomain`;
- best owner abstraction for this weaker source-facing item: the tensor product `E ⊗[k] F`
  together with a maximal-ideal quotient;
- the stronger `LinearDisjoint` owners are not exact replacements here: they additionally require
  `IsDomain (E ⊗[k] F)` and conclude linearly disjoint images, while Lemma 9.6.9 is
  unconditional and only asks for a common overfield;
- primitive data: only the base field `k`, the fields `E`, `F`, their `k`-algebra structures, and
  the two resulting `k`-algebra maps into the quotient field;
- derived API: injectivity of those maps, which is automatic because their source and target are
  fields.

Source/core/bridge triage:
- `source-facing`: existence of a common extension field for `E/k` and `F/k`;
- `core/canonical`: the quotient field `(E ⊗[k] F) ⧸ m` for a maximal ideal `m`;
- `bridge/view`: the maps `E →ₐ[k] M` and `F →ₐ[k] M` obtained by composing the quotient map with
  `includeLeft` and `includeRight`.
-/

section

variable {k : Type u} {E : Type v} {F : Type w} [Field k] [Field E] [Field F]
variable [Algebra k E] [Algebra k F]

-- Proof sketch: the canonical common-overfield construction is the quotient of the tensor product
-- `E ⊗[k] F` by a maximal ideal. Since the quotient by a maximal ideal is a field, composing the
-- quotient map with the two tensor-factor maps gives `k`-algebra maps from `E` and `F` into a
-- common field extension.
/-- Lemma 9.6.9: any two field extensions `E/k` and `F/k` admit a common extension field over `k`,
together with `k`-algebra maps from `E` and `F` into it. The usual embedding formulation is the
same statement, because any ring homomorphism out of a field is injective. -/
theorem exists_common_field_extension :
    ∃ (M : Type (max v w)) (_ : Field M) (_ : Algebra k M) (iE : E →ₐ[k] M) (iF : F →ₐ[k] M),
      Function.Injective iE ∧ Function.Injective iF := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (E ⊗[k] F)
  let M : Type (max v w) := (E ⊗[k] F) ⧸ m
  letI : m.IsMaximal := hm
  letI : Field M := Ideal.Quotient.field m
  refine ⟨M, inferInstance, inferInstance, (Ideal.Quotient.mkₐ k m).comp includeLeft,
    (Ideal.Quotient.mkₐ k m).comp includeRight, RingHom.injective _, RingHom.injective _⟩

end
