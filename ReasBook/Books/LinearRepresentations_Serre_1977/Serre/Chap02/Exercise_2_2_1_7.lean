import Mathlib.RepresentationTheory.Character
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Source/core/bridge triage:
- `source-facing`: Exercise 2-2.1-7, namely the Hom representation, its character formula, and its
  identification with the dual-tensor representation;
- `core/canonical`: `Representation.linHom`, `Representation.char_linHom`, and
  `Representation.Equiv.dualTensorHom`;
- `bridge/view`: the underlying linear owner `LinearMap.dualTensorHom` and its equivalence
  `dualTensorHomEquiv`.

Primitive data already lives in mathlib's canonical representation-theoretic owner layer, so this
file should be pure recall of that API rather than a parallel local wrapper. -/

/- Exercise 2-2.1-7: the conjugation action of `G` on `Hom(V, W)` given by
`f ↦ σ s ∘ₗ f ∘ₗ ρ s⁻¹` is the canonical Hom representation `Representation.linHom ρ σ`. -/
recall Representation.linHom

/- The character of the Hom representation is the product of the contragredient character of `ρ`
with the character of `σ`, namely `g ↦ ρ.character g⁻¹ * σ.character g`. -/
recall Representation.char_linHom

/- The Hom representation is canonically isomorphic to the tensor product of the dual
representation of `ρ` with `σ`. -/
recall Representation.Equiv.dualTensorHom
