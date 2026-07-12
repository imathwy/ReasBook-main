import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}} [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]

-- Semantic recall: `lean_leansearch` surfaced `Scheme.Modules.restrict`/`restrictFunctor` as
-- the canonical restriction owners and the sheaf-module predicates
-- `IsQuasicoherent`, `IsFiniteType`, and `IsFinitePresentation`.

/-- Lemma 28.22.5 (1): let `X` be a quasi-compact and quasi-separated scheme, let
`j : U ⟶ X` be a quasi-compact open immersion, and let `\mathcal G` be a quasi-coherent
finite type `\mathcal O_U`-module. Then `\mathcal G` extends to a quasi-coherent finite type
`\mathcal O_X`-module. -/
@[stacks 0G41]
theorem exists_finiteTypeQuasiCoherentExtension
    (j : U ⟶ X) [IsOpenImmersion j] (hj : QuasiCompact j)
    (G : U.Modules) (hGqc : G.IsQuasicoherent) (hGft : G.IsFiniteType) :
    ∃ (G' : X.Modules) (_ : G'.IsQuasicoherent) (_ : G'.IsFiniteType),
      Nonempty (G'.restrict j ≅ G) := sorry

/-- Lemma 28.22.5 (2): let `X` be a quasi-compact and quasi-separated scheme, let
`j : U ⟶ X` be a quasi-compact open immersion, and let `\mathcal G` be an
`\mathcal O_U`-module of finite presentation. Then `\mathcal G` extends to an
`\mathcal O_X`-module of finite presentation. -/
@[stacks 0G41]
theorem exists_finitePresentationExtension
    (j : U ⟶ X) [IsOpenImmersion j] (hj : QuasiCompact j)
    (G : U.Modules) (hGfp : G.IsFinitePresentation) :
    ∃ (G' : X.Modules) (_ : G'.IsFinitePresentation),
      Nonempty (G'.restrict j ≅ G) := sorry

end AlgebraicGeometry.Scheme.Modules
