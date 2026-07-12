import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced `SheafOfModules.IsFinitePresentation` and
-- `SheafOfModules.IsQuasicoherent` as the canonical scheme-module finiteness/coherence owners.
-- Local Chapter 28 precedent uses `X.Modules`, `F.IsQuasicoherent`, `F.IsFinitePresentation`,
-- `CompactSpace X.carrier`, and `QuasiSeparatedSpace X.carrier`; the filtered colimit is recorded
-- as an `IsColimit` cocone in `X.Modules`, whose legs are the maps `F_i ⟶ F`.

/-- Lemma 28.22.6: if `X` is a quasi-compact and quasi-separated scheme and `\mathcal F` is a
quasi-coherent `\mathcal O_X`-module, then `\mathcal F` is a filtered colimit of
`\mathcal O_X`-modules of finite presentation. The indexing category `I`, the diagram
`G : I ⥤ X.Modules`, and the cocone legs `G.obj i ⟶ F` are the data asserted in the source. -/
@[stacks 01PJ]
theorem exists_filteredColimit_finitePresentation_of_isQuasicoherent
    {X : Scheme.{u}} [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    (F : X.Modules) [F.IsQuasicoherent] :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I),
      ∃ (G : I ⥤ X.Modules) (φ : G ⟶ (Functor.const I).obj F),
        ∃ _ : IsColimit (Cocone.mk F φ),
          ∀ i : I, (G.obj i).IsFinitePresentation := sorry

end AlgebraicGeometry.Scheme.Modules
