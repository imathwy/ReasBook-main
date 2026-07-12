import StacksProject_2024.Chap29.Definition_29_25_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced the ring-level flatness transitivity owners
-- `Module.Flat.trans` / `RingHom.Flat.comp`; the source-facing local owners used here are
-- `Scheme.Modules.flatOverAt` and `Scheme.Hom.flatAt`.

open Scheme.Hom

/-- Lemma 29.25.5: let `X ⟶ Y ⟶ Z` be morphisms of schemes, let `ℱ` be an
`\mathcal O_X`-module, and let `x : X` with image `f x` in `Y`. If `ℱ` is flat over `Y` at `x`
and `Y` is flat over `Z` at `f x`, then `ℱ` is flat over `Z` at `x`. -/
theorem flatOverAt_of_flatOverAt_of_flatAt
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Modules)
    (x : X)
    (hℱ : flatOverAt ℱ f x)
    (hY : flatAt g (f.base x)) :
    flatOverAt ℱ (f ≫ g) x := by
  simpa [flatOverAt, flatAt] using (Module.Flat.trans _ _ _ hY hℱ)

end AlgebraicGeometry.Scheme.Modules
