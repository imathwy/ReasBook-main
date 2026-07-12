import Mathlib.AlgebraicGeometry.Properties

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace

/- Source/core/bridge triage for Lemma 26.11.1:
- `source-facing`: an irreducible closed subset of a scheme has a unique generic point;
- `core/canonical`: the generic-point owners `IsIrreducible.genericPoint`,
  `IsIrreducible.isGenericPoint_genericPoint`, and `IsGenericPoint.eq`;
- `bridge/view`: the bundled `IrreducibleCloseds X` specialization on schemes. -/

namespace AlgebraicGeometry.Scheme

/-- Lemma 26.11.1: any irreducible closed subset of a scheme `X` has a unique generic point. -/
@[stacks 01IS]
theorem existsUnique_genericPoint_of_irreducibleClosed
    {X : Scheme} (Z : IrreducibleCloseds X) :
    ∃! ξ : X, IsGenericPoint ξ Z := by
  refine ⟨Z.isIrreducible.genericPoint, Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed, ?_⟩
  intro ξ hξ
  exact IsGenericPoint.eq hξ (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed)

end AlgebraicGeometry.Scheme
