import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` points to the canonical scheme-module predicates
-- `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFinitePresentation`; nearby Chapter 28
-- files express directed systems as filtered diagrams in `X.Modules` with an `IsColimit` cocone.

/-- Lemma 28.22.7: if `X` is a quasi-compact and quasi-separated scheme and `\mathcal F` is a
quasi-coherent `\mathcal O_X`-module, then `\mathcal F` is the filtered colimit of a system of
`\mathcal O_X`-modules of finite presentation. The filtered index category `I`, the diagram
`G : I ⥤ X.Modules`, and the cocone legs `G.obj i ⟶ F` are the Lean counterparts of the directed
set, the system `(\mathcal F_i, \varphi_{ii'})`, and the maps
`\varphi_i : \mathcal F_i \to \mathcal F` in the source. -/
@[stacks 01PK]
theorem exists_filteredSystem_finitePresentation_colimit_of_isQuasicoherent
    {X : Scheme.{u}} [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    (F : X.Modules) [F.IsQuasicoherent] :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I),
      ∃ (G : I ⥤ X.Modules) (φ : G ⟶ (Functor.const I).obj F),
        ∃ _ : IsColimit (Cocone.mk F φ),
          ∀ i : I, (G.obj i).IsFinitePresentation := sorry

end AlgebraicGeometry.Scheme.Modules
