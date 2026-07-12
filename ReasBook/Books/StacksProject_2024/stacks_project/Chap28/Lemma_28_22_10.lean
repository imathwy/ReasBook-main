import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced the scheme-module predicates
-- `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFinitePresentation`; local Chapter 28
-- precedent records directed systems as filtered diagrams with an `IsColimit` cocone. There is no
-- project-local `X.Algebras` owner in the current search, so `CommMon X.Modules` is the canonical
-- algebra-object category used for `\mathcal O_X`-algebras here.

/-- Lemma 28.22.10: if `X` is quasi-compact and quasi-separated and `\mathcal A` is a
quasi-coherent `\mathcal O_X`-algebra, then `\mathcal A` is a filtered colimit of
quasi-coherent `\mathcal O_X`-algebras of finite presentation. The filtered category `I`, the
diagram `G`, and the cocone legs are the Lean counterparts of the directed set, the system
`(\mathcal A_i, \varphi_{ii'})`, and the morphisms `\varphi_i : \mathcal A_i \to \mathcal A`.
Finite presentation is stated in the algebra category `CommMon X.Modules`, while
quasi-coherence is imposed on the underlying `\mathcal O_X`-module. -/
@[stacks 05JS]
theorem exists_filteredSystem_finitePresentationAlgebra_colimit_of_isQuasicoherent
    {X : Scheme.{u}} [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    [MonoidalCategory X.Modules] [BraidedCategory X.Modules]
    (A : CommMon X.Modules) [A.X.IsQuasicoherent] :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I),
      ∃ (G : I ⥤ CommMon X.Modules) (φ : G ⟶ (Functor.const I).obj A),
        ∃ _ : IsColimit (Cocone.mk A φ),
          ∀ i : I, (G.obj i).X.IsQuasicoherent ∧ IsFinitelyPresentable.{u} (G.obj i) := sorry

end AlgebraicGeometry.Scheme.Modules
