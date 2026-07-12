import Mathlib.AlgebraicGeometry.RationalMap

-- Declarations for this item will be appended below by the statement pipeline.

open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/- Semantic recall / owner check:
- `source-facing`: the Stacks definition identifies rational maps as equivalence classes of partial
  morphisms and records the over-`S` refinement by existence of an over-`S` representative;
- `core/canonical`: mathlib already owns these notions as `Scheme.PartialMap.toRationalMap`,
  `Scheme.PartialMap.toRationalMap_eq_iff`, `Scheme.RationalMap.exists_rep`, and the over-`S`
  existence API on `Scheme.RationalMap.IsOver`;
- `bridge/view`: only the source-facing existence statements below, phrased in the same partial-map
  language as the definition.

Part (1) is a pure canonical recall item, so it should not survive as a duplicate local theorem.
Part (2) is also a pure canonical recall item, while part (3) remains a thin source-facing
companion exposing the over-`S` representative view.
-/

variable {S X Y : Scheme}

/- Definition 29.49.1 (1): two partial morphisms from dense open subschemes of `X` to `Y` are
equivalent exactly when they define the same rational map. This is the canonical owner theorem
`Scheme.PartialMap.toRationalMap_eq_iff`. -/
#check Scheme.PartialMap.toRationalMap_eq_iff

/- Definition 29.49.1 (2): a rational map from `X` to `Y` is represented by a morphism from some
dense open subscheme of `X` to `Y`. This is the canonical owner theorem
`Scheme.RationalMap.exists_rep`. -/
#check Scheme.RationalMap.exists_rep

namespace RationalMap

/-- Definition 29.49.1 (3): a rational map from `X` to `Y` over `S` is exactly a rational map
admitting a representative partial morphism over `S`. -/
theorem isOver_iff_exists_partialMap_over [X.Over S] [Y.Over S] (φ : X ⤏ Y) :
    φ.IsOver S ↔ ∃ f : X.PartialMap Y, f.IsOver S ∧ f.toRationalMap = φ :=
  ⟨fun h ↦ by
    letI : φ.IsOver S := h
    exact RationalMap.exists_partialMap_over S φ, fun h ↦ by
    rcases h with ⟨f, hfOver, rfl⟩
    exact ⟨f, hfOver, rfl⟩⟩

end RationalMap

end AlgebraicGeometry.Scheme
