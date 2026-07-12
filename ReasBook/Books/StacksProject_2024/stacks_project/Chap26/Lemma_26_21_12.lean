import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` surfaced the canonical composition instances
`AlgebraicGeometry.IsSeparated.instCompScheme` and `AlgebraicGeometry.quasiSeparated_comp`, and the
base-change owner `AlgebraicGeometry.IsSeparated.isStableUnderBaseChange`; the fibre-product
clauses are expressed as binary product maps in the over category. -/

variable {X Y Z S S' : Scheme.{u}}

/-- Lemma 26.21.12 (1): a composition of separated morphisms of schemes is separated. -/
@[stacks 01KU]
theorem isSeparated_comp (f : X ⟶ Y) (g : Y ⟶ Z) [IsSeparated f] [IsSeparated g] :
    IsSeparated (f ≫ g) := sorry

/-- Lemma 26.21.12 (2): a composition of quasi-separated morphisms of schemes is
quasi-separated. -/
@[stacks 01KU]
theorem quasiSeparated_comp_of_quasiSeparated (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiSeparated f] [QuasiSeparated g] :
    QuasiSeparated (f ≫ g) := sorry

/-- Lemma 26.21.12 (3): the base change of a separated morphism of schemes is separated. -/
@[stacks 01KU]
theorem isSeparated_pullback_snd_of_isSeparated (f : X ⟶ S) (g : S' ⟶ S)
    [IsSeparated f] :
    IsSeparated (pullback.snd f g) := sorry

/-- Lemma 26.21.12 (4): the base change of a quasi-separated morphism of schemes is
quasi-separated. -/
@[stacks 01KU]
theorem quasiSeparated_pullback_snd_of_quasiSeparated (f : X ⟶ S) (g : S' ⟶ S)
    [QuasiSeparated f] :
    QuasiSeparated (pullback.snd f g) := sorry

variable {A B C D : Over S}

/-- Lemma 26.21.12 (5): a fibre product of separated morphisms over a base scheme is separated;
the morphism is the underlying scheme map of the binary product map in `Over S`. -/
@[stacks 01KU]
theorem isSeparated_prod_map_left_of_isSeparated (f : A ⟶ B) (g : C ⟶ D)
    [IsSeparated f.left] [IsSeparated g.left] :
    IsSeparated (Limits.prod.map f g).left := sorry

/-- Lemma 26.21.12 (6): a fibre product of quasi-separated morphisms over a base scheme is
quasi-separated; the morphism is the underlying scheme map of the binary product map in `Over S`. -/
@[stacks 01KU]
theorem quasiSeparated_prod_map_left_of_quasiSeparated (f : A ⟶ B) (g : C ⟶ D)
    [QuasiSeparated f.left] [QuasiSeparated g.left] :
    QuasiSeparated (Limits.prod.map f g).left := sorry

end AlgebraicGeometry
