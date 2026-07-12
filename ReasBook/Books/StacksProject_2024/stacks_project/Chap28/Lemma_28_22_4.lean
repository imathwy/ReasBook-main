import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}} [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]

-- Semantic recall: `lean_leansearch` and the neighboring Chapter 28 files point to the canonical
-- scheme-module restriction owner `restrictFunctor j`, with extension data expressed by an
-- isomorphism on the restricted source and a commuting restricted morphism.

/-- Lemma 28.22.4: let `X` be a quasi-compact and quasi-separated scheme, let `j : U ⟶ X` be a
quasi-compact open immersion, let `\mathcal F` be a quasi-coherent `\mathcal O_X`-module, let
`\mathcal G` be an `\mathcal O_U`-module of finite presentation, and let
`\varphi : \mathcal G \to \mathcal F|_U` be a morphism. Then there exists an
`\mathcal O_X`-module `\mathcal G'` of finite presentation and a morphism
`\varphi' : \mathcal G' \to \mathcal F` whose restriction to `U` identifies with
`\mathcal G` and `\varphi`. -/
@[stacks 01PI]
theorem exists_finitePresentationMorphismExtension
    (j : U ⟶ X) [IsOpenImmersion j] (hj : QuasiCompact j)
    (F : X.Modules) (hFqc : F.IsQuasicoherent)
    (G : U.Modules) (hGfp : G.IsFinitePresentation)
    (φ : G ⟶ F.restrict j) :
    ∃ (G' : X.Modules) (_ : G'.IsFinitePresentation),
      ∃ φ' : G' ⟶ F, ∃ e : G'.restrict j ≅ G,
        e.hom ≫ φ = (restrictFunctor j).map φ' := sorry

end AlgebraicGeometry.Scheme.Modules
