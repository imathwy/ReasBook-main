import StacksProject_2024.Chap30.Lemma_30_12_7
import StacksProject_2024.Chap30.Definition_30_26_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open Scheme.IdealSheafData
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced `Scheme.IdealSheafData.support`,
-- `Scheme.IdealSheafData.vanishingIdeal`, and `Scheme.Modules.pushforward`. Local Chapter 29
-- precedent represents scheme-theoretic support by the affine-open annihilator condition from
-- Definition 29.5.5, while Chapter 30 represents closed-subset properness over a base by
-- `ClosedSubset.IsProperOver`. The Stacks tag evidence is consistent for `0CYS`.

/-- The support of a finite type quasi-coherent scheme module is closed, as needed to view the
ordinary support as a closed subset in the properness predicate. -/
theorem isClosed_moduleSupport_of_finiteType_quasiCoherent
    {X : Scheme} (ℱ : X.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent] :
    IsClosed (moduleSupport ℱ) := sorry

/-- Lemma 30.26.7: for a locally finite type morphism `f : X ⟶ S` and a finite type
quasi-coherent `\mathcal O_X`-module `ℱ`, the ordinary support of `ℱ` being proper over `S`,
the scheme-theoretic support of `ℱ` being proper over `S`, and the existence of a proper closed
subscheme carrying a finite type quasi-coherent module whose pushforward is `ℱ` are equivalent. -/
@[stacks 0CYS]
theorem moduleSupport_properOver_tfae_schemeTheoreticSupport_and_pushforward
    {X S : Scheme} (f : X ⟶ S) [LocallyOfFiniteType f]
    (ℱ : X.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent] :
    List.TFAE [
      ClosedSubset.IsProperOver f
        (⟨moduleSupport ℱ, isClosed_moduleSupport_of_finiteType_quasiCoherent ℱ⟩ :
          TopologicalSpace.Closeds X),
      ∃ I : X.IdealSheafData,
        ∃ _ : (∀ U : X.affineOpens,
          I.ideal U = Module.annihilator Γ(X, U.1) (Γ(ℱ, U.1))),
          IsProper (I.subschemeι ≫ f),
      ∃ I : X.IdealSheafData,
        ∃ 𝒢 : I.subscheme.Modules,
          ∃ _ : 𝒢.IsFiniteType,
            ∃ _ : 𝒢.IsQuasicoherent,
              ∃ _ : IsProper (I.subschemeι ≫ f),
                Nonempty ((Scheme.Modules.pushforward I.subschemeι).obj 𝒢 ≅ ℱ)
    ] := sorry

end AlgebraicGeometry.Scheme.Modules
