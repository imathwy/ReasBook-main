import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

/- Semantic recall: `lean_leansearch` found the exact canonical mathlib theorem
`AlgebraicGeometry.QuasiCompact.of_comp`. The Stacks tag evidence is consistent for tag `03GI`;
because this item is a pure canonical recall, no local source-facing declaration is introduced. -/

/- Lemma 26.21.14: let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of schemes. If `g ∘ f`,
equivalently `f ≫ g`, is quasi-compact and `g` is quasi-separated, then `f` is quasi-compact. -/
recall AlgebraicGeometry.QuasiCompact.of_comp

section

variable {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact (f ≫ g)] [QuasiSeparated g]

#check (AlgebraicGeometry.QuasiCompact.of_comp f g : QuasiCompact f)

end
