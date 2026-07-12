import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

/- Semantic recall: `lean_leansearch` recovered the canonical scheme-side owners
`AlgebraicGeometry.IsSeparated`, `AlgebraicGeometry.QuasiSeparated`,
`AlgebraicGeometry.Scheme.IsSeparated`, and `QuasiSeparatedSpace`. This item is therefore a pure
canonical recall block. -/

/- Definition 26.21.3 (1): a morphism of schemes is separated via the canonical morphism property
`AlgebraicGeometry.IsSeparated`, which is the owner for the condition that the diagonal morphism is
a closed immersion. -/
recall IsSeparated

/- Source-facing specialization: for schemes `X` and `Y`, separatedness of a morphism
`f : X ⟶ Y` is expressed by the proposition `IsSeparated f`. -/
#check (IsSeparated : {X Y : Scheme.{u}} → (X ⟶ Y) → Prop)

/- Definition 26.21.3 (2): a morphism of schemes is quasi-separated via the canonical morphism
property `AlgebraicGeometry.QuasiSeparated`, which is the owner for the condition that the diagonal
morphism is quasi-compact. -/
recall QuasiSeparated

/- Source-facing specialization: for schemes `X` and `Y`, quasi-separatedness of a morphism
`f : X ⟶ Y` is expressed by the proposition `QuasiSeparated f`. -/
#check (QuasiSeparated : {X Y : Scheme.{u}} → (X ⟶ Y) → Prop)

/- Definition 26.21.3 (3): a scheme `Y` is separated via the canonical absolute owner
`AlgebraicGeometry.Scheme.IsSeparated`, i.e. via separatedness of the structural morphism
`Y ⟶ Spec(ℤ)`. -/
recall Scheme.IsSeparated

/- Source-facing specialization: separatedness of a scheme `Y` is expressed by the proposition
`Scheme.IsSeparated Y`. -/
#check (Scheme.IsSeparated : Scheme.{u} → Prop)

/- Definition 26.21.3 (4): a scheme `Y` is quasi-separated via the canonical absolute owner
`QuasiSeparatedSpace Y`, i.e. via quasi-separatedness of the structural morphism
`Y ⟶ Spec(ℤ)`. -/
recall QuasiSeparatedSpace

/- Source-facing specialization: quasi-separatedness of a scheme `Y` is expressed by the
proposition `QuasiSeparatedSpace Y`. -/
#check fun (Y : Scheme.{u}) ↦ QuasiSeparatedSpace Y
