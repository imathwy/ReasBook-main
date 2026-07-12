import StacksProject_2024.Chap29.Lemma_29_5_3
import StacksProject_2024.Chap29.Definition_29_25_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced `AlgebraicGeometry.UniversallyOpen` and the
-- canonical flat/l.f.p. universal-openness instance; local Chapter 29/30 precedent uses
-- `moduleSupport ℱ = Set.univ` for the source phrase `X = Supp(ℱ)`.

/-- Lemma 29.25.11: let `f : X ⟶ Y` be a morphism of schemes and let `ℱ` be a
quasi-coherent `\mathcal O_X`-module. If `f` is locally of finite presentation, `ℱ` is of finite
type, `Supp(ℱ) = X`, and `ℱ` is flat over `Y`, then `f` is universally open. -/
@[stacks 0CVT]
theorem universallyOpen_of_flatOver_of_moduleSupport_eq_univ
    {X Y : Scheme.{u}} (f : X ⟶ Y) (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] [LocallyOfFinitePresentation f]
    (hsupp : moduleSupport ℱ = Set.univ) (hflat : flatOver ℱ f) :
    UniversallyOpen f := sorry

end AlgebraicGeometry.Scheme.Modules
