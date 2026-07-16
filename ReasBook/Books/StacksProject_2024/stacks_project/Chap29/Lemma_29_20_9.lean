import StacksProject_2024.stacks_project.Chap29.Definition_29_20_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced mathlib's canonical local scheme-morphism owner
  `AlgebraicGeometry.LocallyQuasiFinite` and the morphism property `QuasiCompact`;
- local Chapter 29 precedent introduces the Stacks-facing global owner
  `Scheme.Hom.QuasiFinite` in `Definition_29_20_1.lean`, with companion theorem
  `Scheme.Hom.quasiFinite_iff`.
-/

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Lemma 29.20.9: let `f : X ⟶ S` be a morphism of schemes. Then `f` is quasi-finite if and
only if `f` is locally quasi-finite and quasi-compact. -/
@[stacks 01TJ]
theorem quasiFinite_iff_locallyQuasiFinite_and_quasiCompact :
    QuasiFinite f ↔ LocallyQuasiFinite f ∧ QuasiCompact f := sorry

end Scheme.Hom
end AlgebraicGeometry
