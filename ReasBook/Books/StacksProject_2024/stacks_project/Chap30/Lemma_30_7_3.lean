import Mathlib
import StacksProject_2024.stacks_project.Chap30.Lemma_30_7_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the canonical module pullback/pushforward
-- infrastructure; local Lemma 30.7.2 supplies the canonical base-change square notation
-- `pullback f g`, `pullback.snd f g`, and `baseChangeModule f g ℱ`. As in Lemma 30.7.1,
-- quasi-coherence inputs and complex terms are recorded through the local Čech predicates to
-- avoid eager sheaf-compose synthesis while keeping the source-facing base-change statement.

variable {X S : Scheme.{u}}

/-- A bounded-below complex of quasi-coherent `\mathcal O_S`-modules whose pullbacks represent
the derived pushforward after arbitrary base change. -/
class BaseChangeDerivedPushforwardComplex
    (f : X ⟶ S) (ℱ : X.Modules) (K : CochainComplex S.Modules ℤ) : Prop where
  boundedBelow : CochainComplex.plus S.Modules K
  term_isQuasicoherent : ∀ p : ℤ, CechTermIsQuasicoherent (K.X p)
  pullback_represents :
    ∀ ⦃S' : Scheme.{u}⦄ (g : S' ⟶ S)
      [HasInjectiveResolutions (pullback f g : Scheme.{u}).Modules]
      [Functor.HasRightDerivedFunctor
        ((Scheme.Modules.pushforward (pullback.snd f g)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
        (HomologicalComplex.quasiIso (pullback f g : Scheme.{u}).Modules
          (ComplexShape.up ℤ))],
      IsIsomorphic
        (DerivedCategory.Q.obj
          (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
        ((Functor.totalRightDerived
            ((Scheme.Modules.pushforward (pullback.snd f g)).mapHomologicalComplex
              (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
            DerivedCategory.Q
            (HomologicalComplex.quasiIso (pullback f g : Scheme.{u}).Modules
              (ComplexShape.up ℤ))).obj
          ((DerivedCategory.singleFunctor (pullback f g : Scheme.{u}).Modules 0).obj
            (baseChangeModule f g ℱ)))

/-- Lemma 30.7.3: if `f : X ⟶ S` is quasi-compact and quasi-separated and `S` is
quasi-compact and separated, then every quasi-coherent `\mathcal O_X`-module `\mathcal F`
admits a bounded-below complex `K` of quasi-coherent `\mathcal O_S`-modules such that, after
pullback along every `g : S' ⟶ S`, the complex `g^*K` represents
`R(f')_* \mathcal F'` for the canonical base-change square. -/
@[stacks 01XN]
theorem exists_boundedBelow_qcoh_complex_pullback_represents_baseChange_derivedPushforward
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [CompactSpace S.carrier] [S.IsSeparated]
    (ℱ : X.Modules) [CechInputIsQuasicoherent ℱ] :
    ∃ K : CochainComplex S.Modules ℤ,
      BaseChangeDerivedPushforwardComplex f ℱ K := sorry

end AlgebraicGeometry.Scheme
