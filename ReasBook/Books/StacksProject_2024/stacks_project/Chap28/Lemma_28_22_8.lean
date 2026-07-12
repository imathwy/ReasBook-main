import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` identified the canonical scheme-module predicates
-- `SheafOfModules.IsFiniteType`, `SheafOfModules.IsQuasicoherent`, and
-- `SheafOfModules.IsFinitePresentation`. Local Chapter 28 precedent records the colimit as an
-- `IsColimit` cocone in `X.Modules`; the source's surjective transition maps are expressed as
-- categorical epimorphisms of the diagram maps.

/-- Lemma 28.22.8: if `X` is quasi-compact and quasi-separated and `F` is a finite type
quasi-coherent `O_X`-module, then `F` is a filtered colimit of finite-presentation
`O_X`-modules with surjective transition maps. -/
@[stacks 086M]
theorem exists_filteredSystem_finitePresentation_colimit_of_isFiniteType_isQuasicoherent
    {X : Scheme.{u}} [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I),
      ∃ (G : I ⥤ X.Modules) (φ : G ⟶ (Functor.const I).obj F),
        ∃ _ : IsColimit (Cocone.mk F φ),
          (∀ i : I, (G.obj i).IsFinitePresentation) ∧
            ∀ {i i' : I} (f : i ⟶ i'), Epi (G.map f) := sorry

end AlgebraicGeometry.Scheme.Modules
