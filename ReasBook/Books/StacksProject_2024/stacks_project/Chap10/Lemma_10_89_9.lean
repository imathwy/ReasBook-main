import Mathlib
import StacksProject_2024.Chap10.Definition_10_82_1
import StacksProject_2024.Chap10.Proposition_10_89_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace Module

section

variable {R : Type u} [CommRing R]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]

/- Domain-style sampling:
* primary domain: Mittag-Leffler modules over a commutative ring, organized around the chapter
  owner `Module.MittagLeffler`.
* inspected owner declarations:
  `Module.MittagLeffler` from `Definition_10_88_7`,
  `LinearMap.UniversallyInjective` from `Definition_10_82_1`,
  `mittagLeffler_iff_tensorProduct_piRight_injective` from `Proposition_10_89_5`, and
  `CategoryTheory.ShortComplex.universallyExact_colimit_of_isFiltered` from `Example_10_82_2`.
* best owner abstraction: the chapter owners `Module.MittagLeffler` and
  `LinearMap.UniversallyInjective`; this lemma should build directly on them rather than introduce
  a local wrapper for directed systems with tensor-injective transition maps.
* layer: `source-facing`; the theorem records the directed-colimit closure statement from the
  source, not a new owner abstraction.
* primitive data: the directed diagram `F` and the universally injective transition-map
  hypothesis `hF`.
* derived API: the induced Mittag-Leffler structure on the colimit module `colimit F`.
-/
-- Proof sketch: by Proposition `10.89.5`, it is enough to show injectivity of the canonical map
-- `M ⊗[R] ∏ Q_α → ∏ (M ⊗[R] Q_α)` for the colimit module `M = colimit F`. Tensor product with a
-- fixed module commutes with filtered colimits, so this reduces to the corresponding injectivity at
-- each stage `F.obj i`, where it holds because `F.obj i` is Mittag-Leffler. The maps into the
-- product of the colimit tensors are injective because the transition maps are universally
-- injective after tensoring with each `Q_α`.
/-- Lemma 10.89.9: the colimit of a directed system of Mittag-Leffler `R`-modules with
universally injective transition maps is a Mittag-Leffler `R`-module. -/
theorem mittagLeffler_colimit_of_directedSystem
    (F : I ⥤ ModuleCat R)
    [∀ i, MittagLeffler R (F.obj i)]
    (hF :
      ∀ ⦃i j : I⦄ (hij : i ≤ j),
        LinearMap.UniversallyInjective ((F.map (homOfLE hij)).hom)) :
    MittagLeffler R ((colimit F : ModuleCat R)) := sorry

end

end Module
