import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} {K : Type v} {V : Type w}
variable [CommRing R] [Field K] [Algebra R K]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/- Domain-style sampling in the fraction-field lattice API:
- primitive data: finite generation of an `R`-submodule and the spanning condition over `K`
- core/canonical owner: `Submodule.IsLattice K`
- bridge/view: the textbook conjunction `Module.Finite R L ∧ Submodule.span K (L : Set V) = ⊤`

Layer triage:
- `source-facing`: Definition 10.121.3 identifies the notion of a lattice in `V`
- `core/canonical`: mathlib already owns this notion as `Submodule.IsLattice K`
- `bridge/view`: the textbook finite-generation-plus-span formulation is a companion restatement,
  not a second owner

Primitive-vs-derived split:
- the owner stores the primitive fields `fg` and `span_eq_top`
- `Module.Finite R L` is derived from `fg` by the canonical instance
- the source-facing conjunction is therefore derived API only
-/

/- Definition 10.121.3: in the fraction-field setting, the canonical notion of a lattice in `V`
is mathlib's `Submodule.IsLattice K`, i.e. an `R`-submodule that is finitely generated and whose
`K`-span is all of `V`. -/
recall Submodule.IsLattice

namespace Submodule

open Module.Finite

/-- The textbook formulation of a lattice is equivalent to mathlib's `Submodule.IsLattice K`. -/
theorem isLattice_iff_moduleFinite_and_span_eq_top (L : Submodule R V) :
    IsLattice K L ↔ Module.Finite R L ∧ span K (L : Set V) = ⊤ := by
  constructor
  · intro hL
    let _ : IsLattice K L := hL
    exact ⟨inferInstance, hL.span_eq_top⟩
  · rintro ⟨hfinite, hspan⟩
    exact ⟨iff_fg.mp hfinite, hspan⟩

end Submodule

end
