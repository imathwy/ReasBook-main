import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}} [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]

-- Semantic recall: `lean_leansearch` points to the canonical scheme-module restriction
-- functor `Scheme.Modules.restrictFunctor` and the sheaf-module predicates
-- `IsQuasicoherent`, `IsFiniteType`, and `IsFinitePresentation`. Nearby Chapter 28 entries
-- formalize quasi-compact opens as quasi-compact open immersions `j : U ⟶ X`.

/-- Lemma 28.22.9: let `X` be a quasi-compact and quasi-separated scheme, let `\mathcal F`
be a finite type quasi-coherent `\mathcal O_X`-module, and let `j : U ⟶ X` be a
quasi-compact open immersion such that `\mathcal F|_U` is of finite presentation. Then there
exists a morphism `\varphi : \mathcal G \to \mathcal F` with `\mathcal G` of finite
presentation, `\varphi` surjective, and `\varphi|_U` an isomorphism. -/
@[stacks 080V]
theorem exists_finitePresentation_epi_restrictIso
    (j : U ⟶ X) [IsOpenImmersion j] (hj : QuasiCompact j)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    [hFpU : (F.restrict j).IsFinitePresentation] :
    ∃ (G : X.Modules) (_ : G.IsFinitePresentation) (φ : G ⟶ F),
      Epi φ ∧ IsIso ((restrictFunctor j).map φ) := sorry

end AlgebraicGeometry.Scheme.Modules
