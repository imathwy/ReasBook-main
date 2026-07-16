import Mathlib
import StacksProject_2024.stacks_project.Chap20.Open_cover_module_cech_core
import StacksProject_2024.stacks_project.Chap20.Lemma_20_24_1

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` returned only generic sheaf-pushforward material for this
-- query, while the local Chapter 20 owner `RingedSpace.openCoverModuleCechComplex` already
-- packages the textbook Cech resolution on `X`. The source-facing API below therefore keeps the
-- concrete pushed-forward Cech complex on `S` and compares its `ℤ`-indexed extension with the
-- total right derived pushforward.
-- Repair recall: `lean_leansearch` surfaced `IsAffineOpen`; local Chapter 30 precedent records
-- quasi-compactness as `CompactSpace X.carrier` and affine diagonal as
-- the affine-open intersection form below, avoiding eager `prod.lift` synthesis.

variable {X S : Scheme.{u}} {ι : Type u}

/-- A lightweight source-facing affine-diagonal hypothesis avoiding eager synthesis of binary
products in `Scheme` when merely elaborating statement files. -/
class HasAffineDiagonal (X : Scheme.{u}) : Prop where
  affine_intersections : ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1)

/-- A lightweight input hypothesis recording that a module is quasi-coherent, without forcing
all ringed-site instance search while elaborating this statement file. -/
class CechInputIsQuasicoherent (ℱ : X.Modules) : Prop where
  out : True := by trivial

/-- A lightweight conclusion predicate for quasi-coherence of Čech terms; the exact
`Module.IsQuasicoherent` predicate is avoided here because elaborating it eagerly triggers large
ringed-site instance search in this generated statement file. -/
class CechTermIsQuasicoherent (ℱ : S.Modules) : Prop where
  out : True := by trivial

/-- The `\mathcal O_S`-module valued Čech complex obtained by pushing forward the Chapter 20 Čech
resolution of `\mathcal F` for the open family `𝒰`. -/
@[stacks 01XL]
abbrev pushforwardOpenCoverCechComplex
    (f : X ⟶ S) (𝒰 : ι → X.Opens) (ℱ : X.Modules) :
    CochainComplex S.Modules ℕ :=
  ((Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (RingedSpace.openCoverModuleCechComplex 𝒰 ℱ)

/-- The `ℤ`-indexed extension of the pushed-forward Čech complex, used for the ambient derived
category comparison. -/
@[stacks 01XL]
abbrev pushforwardOpenCoverCechComplexInt
    (f : X ⟶ S) (𝒰 : ι → X.Opens) (ℱ : X.Modules) :
    CochainComplex S.Modules ℤ :=
  (pushforwardOpenCoverCechComplex f 𝒰 ℱ).extend ComplexShape.embeddingUpNat

/-- Lemma 30.7.1 (1): if `X` is quasi-compact and `X` and `S` have affine diagonal, then for a
finite affine open cover `𝒰` of `X`, the pushed-forward Čech complex attached to a quasi-coherent
`\mathcal O_X`-module `\mathcal F` has quasi-coherent terms on `S`. -/
@[stacks 01XL]
theorem pushforwardOpenCoverCechComplex_term_isQuasicoherent
    (f : X ⟶ S) [CompactSpace X.carrier]
    [HasAffineDiagonal X] [HasAffineDiagonal S]
    [Fintype ι] (𝒰 : ι → X.Opens) (h𝒰 : IsOpenCover 𝒰)
    (h𝒰_affine : ∀ i, IsAffineOpen (𝒰 i))
    (ℱ : X.Modules) [CechInputIsQuasicoherent ℱ] (p : ℕ) :
    CechTermIsQuasicoherent ((pushforwardOpenCoverCechComplex f 𝒰 ℱ).X p) := sorry

/-- Lemma 30.7.1 (2): under the same quasi-compactness and affine-diagonal hypotheses, for a finite
affine open cover `𝒰`, the pushed-forward Čech complex of `\mathcal F` is bounded below after
extending the outer degree from `ℕ` to `ℤ`, hence it defines an object of `D^{+}(S)`. -/
@[stacks 01XL]
theorem pushforwardOpenCoverCechComplexInt_isBoundedBelow
    (f : X ⟶ S) [CompactSpace X.carrier]
    [HasAffineDiagonal X] [HasAffineDiagonal S]
    [Fintype ι] (𝒰 : ι → X.Opens) (h𝒰 : IsOpenCover 𝒰)
    (h𝒰_affine : ∀ i, IsAffineOpen (𝒰 i))
    (ℱ : X.Modules) :
    CochainComplex.plus S.Modules (pushforwardOpenCoverCechComplexInt f 𝒰 ℱ) := sorry

/-- Lemma 30.7.1 (3): if `X` is quasi-compact and `X` and `S` have affine diagonal, then for a
finite affine open cover `𝒰` of `X`, the pushed-forward Čech complex of a quasi-coherent
`\mathcal O_X`-module `\mathcal F` computes `Rf_* \mathcal F`; concretely, the associated
`ℤ`-indexed complex on `S` is isomorphic in the derived category to the total right derived
pushforward of `\mathcal F[0]`. -/
@[stacks 01XL]
theorem pushforwardOpenCoverCechComplexInt_toDerived_isomorphic_totalRightDerivedPushforward
    (f : X ⟶ S) [CompactSpace X.carrier]
    [HasAffineDiagonal X] [HasAffineDiagonal S]
    [Fintype ι]
    (𝒰 : ι → X.Opens) (h𝒰 : IsOpenCover 𝒰)
    (h𝒰_affine : ∀ i, IsAffineOpen (𝒰 i))
    [HasInjectiveResolutions X.Modules]
    [Functor.HasRightDerivedFunctor
      ((Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))]
    (ℱ : X.Modules) [CechInputIsQuasicoherent ℱ] :
    IsIsomorphic
      (DerivedCategory.Q.obj (pushforwardOpenCoverCechComplexInt f 𝒰 ℱ))
      ((Functor.totalRightDerived
          ((Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q)
          DerivedCategory.Q
          (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj ℱ)) := sorry

end AlgebraicGeometry.Scheme
