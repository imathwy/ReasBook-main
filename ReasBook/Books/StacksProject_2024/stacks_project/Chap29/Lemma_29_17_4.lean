import StacksProject_2024.Chap29.Definition_29_17_1
import StacksProject_2024.Chap26.Definition_26_12_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` confirmed the scheme-side locally Noetherian owner `IsLocallyNoetherian`;
- Chapter 29 already uses the canonical owner `UniversallyCatenary`;
- `irreducibleComponents` is the canonical topological owner for components, so the only missing
  scheme-side datum here is the reduced closed-subscheme realization of a component.
-/

namespace Scheme

noncomputable section

/-- The irreducible closed subset of `X` underlying an irreducible component. -/
def irreducibleComponentIrreducibleClosed (X : Scheme.{u}) (Z : irreducibleComponents X) :
    TopologicalSpace.IrreducibleCloseds X :=
  ⟨(Z : Set X), isClosed_of_mem_irreducibleComponents (Z : Set X) Z.2, Z.2.2⟩

/-- The closed subset of `X` underlying an irreducible component. -/
abbrev irreducibleComponentClosed (X : Scheme.{u}) (Z : irreducibleComponents X) :
    TopologicalSpace.Closeds X :=
  X.irreducibleComponentIrreducibleClosed Z

/-- Membership in the closed subset attached to an irreducible component is membership in the
component itself. -/
@[simp] theorem mem_irreducibleComponentClosed
    (X : Scheme.{u}) (Z : irreducibleComponents X) (x : X) :
    x ∈ X.irreducibleComponentClosed Z ↔ x ∈ Z :=
  Iff.rfl

/-- The reduced induced closed subscheme attached to an irreducible component of `X`. -/
abbrev irreducibleComponentSubscheme (X : Scheme.{u}) (Z : irreducibleComponents X) :
    Scheme.{u} :=
  (X.reducedInducedSchemeStructure (X.irreducibleComponentClosed Z)).subscheme

/-- The canonical immersion from the reduced induced irreducible-component subscheme into `X`. -/
abbrev irreducibleComponentSubschemeι (X : Scheme.{u}) (Z : irreducibleComponents X) :
    X.irreducibleComponentSubscheme Z ⟶ X :=
  (X.reducedInducedSchemeStructure (X.irreducibleComponentClosed Z)).subschemeι

end

end Scheme

/-- Lemma 29.17.4: a locally Noetherian scheme is universally catenary if and only if each of its
irreducible components, viewed with its reduced induced closed-subscheme structure, is universally
catenary. -/
@[stacks 0G42]
theorem universallyCatenary_iff_forall_irreducibleComponent
    (S : Scheme.{u}) [IsLocallyNoetherian S] :
    UniversallyCatenary S ↔
      ∀ Z : irreducibleComponents S, UniversallyCatenary (S.irreducibleComponentSubscheme Z) :=
  sorry

end AlgebraicGeometry
