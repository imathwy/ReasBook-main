import Mathlib
import StacksProject_2024.stacks_project.Chap30.Lemma_30_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced `Scheme.Modules.pullback`; local Chapter 30
-- precedent fixes the Čech owner as `pushforwardOpenCoverCechComplexInt`, and base-change
-- files use the canonical pullback square `pullback f g` with projections `pullback.fst` and
-- `pullback.snd`.

variable {X S S' : Scheme.{u}} {ι : Type u}

/-- The base-changed indexed open family `U_i' = (g')^{-1}(U_i)` on the canonical pullback
`X ×_S S'`, where `g'` is `pullback.fst f g`. -/
@[stacks 01XM]
abbrev baseChangeOpenCover
    (f : X ⟶ S) (g : S' ⟶ S) (𝒰 : ι → X.Opens) :
    ι → (pullback f g : Scheme.{u}).Opens :=
  fun i ↦ (Opens.map (pullback.fst f g).base).obj (𝒰 i)

/-- The pulled-back module `\mathcal F' = (g')^*\mathcal F` on the canonical base change
`X ×_S S'`. -/
@[stacks 01XM]
abbrev baseChangeModule
    (f : X ⟶ S) (g : S' ⟶ S) (ℱ : X.Modules) :
    (pullback f g : Scheme.{u}).Modules :=
  (Scheme.Modules.pullback (pullback.fst f g)).obj ℱ

/-- Lemma 30.7.2 (1): for the canonical base-change square, the inverse images
`U_i' = (g')^{-1}(U_i)` of an indexed open cover of `X` form an indexed open cover of
`X ×_S S'`. -/
@[stacks 01XM]
theorem baseChangeOpenCover_isOpenCover
    (f : X ⟶ S) (g : S' ⟶ S)
    [Fintype ι] (𝒰 : ι → X.Opens) (h𝒰 : IsOpenCover 𝒰) :
    IsOpenCover (baseChangeOpenCover f g 𝒰) := sorry

/-- Lemma 30.7.2 (2): with the hypotheses of Lemma 30.7.1 on `f : X ⟶ S`,
the pullback along `g : S' ⟶ S` of the pushed-forward Čech complex attached to a finite affine
open cover `𝒰` of `X` is isomorphic in the derived category to
`R(f')_* \mathcal F'`, where `f' = pullback.snd f g` and
`\mathcal F' = (g')^*\mathcal F`. -/
@[stacks 01XM]
theorem pullback_pushforwardOpenCoverCechComplexInt_isomorphic_totalRightDerivedPushforward
    (f : X ⟶ S) (g : S' ⟶ S)
    [CompactSpace X.carrier]
    [HasAffineDiagonal X] [HasAffineDiagonal S]
    [Fintype ι]
    (𝒰 : ι → X.Opens) (h𝒰 : IsOpenCover 𝒰)
    (h𝒰_affine : ∀ i, IsAffineOpen (𝒰 i))
    [HasInjectiveResolutions (pullback f g : Scheme.{u}).Modules]
    [Functor.HasRightDerivedFunctor
      ((Scheme.Modules.pushforward (pullback.snd f g)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso (pullback f g : Scheme.{u}).Modules
        (ComplexShape.up ℤ))]
    (ℱ : X.Modules) [CechInputIsQuasicoherent ℱ] :
    IsIsomorphic
      (DerivedCategory.Q.obj
        (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (pushforwardOpenCoverCechComplexInt f 𝒰 ℱ)))
      ((Functor.totalRightDerived
          ((Scheme.Modules.pushforward (pullback.snd f g)).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
          DerivedCategory.Q
          (HomologicalComplex.quasiIso (pullback f g : Scheme.{u}).Modules
            (ComplexShape.up ℤ))).obj
        ((DerivedCategory.singleFunctor (pullback f g : Scheme.{u}).Modules 0).obj
          (baseChangeModule f g ℱ))) := sorry

/-- Lemma 30.7.2 (3): if `g : S' ⟶ S` is affine, then the inverse images
`U_i' = (g')^{-1}(U_i)` of affine opens in `X` are affine opens in `X ×_S S'`. -/
@[stacks 01XM]
theorem baseChangeOpenCover_isAffineOpen_of_isAffineHom
    (f : X ⟶ S) (g : S' ⟶ S) [IsAffineHom g]
    [Fintype ι] (𝒰 : ι → X.Opens) (h𝒰_affine : ∀ i, IsAffineOpen (𝒰 i)) :
    ∀ i, IsAffineOpen (baseChangeOpenCover f g 𝒰 i) := sorry

/-- Lemma 30.7.2 (4): if `g : S' ⟶ S` is affine, then the termwise pullback of the
pushed-forward Čech complex on `S` is the Čech complex on `S'` formed from the base-changed cover
`U_i' = (g')^{-1}(U_i)` and the pulled-back module `\mathcal F'`. -/
@[stacks 01XM]
theorem pullback_pushforwardOpenCoverCechComplex_eq_baseChange_of_isAffineHom
    (f : X ⟶ S) (g : S' ⟶ S) [IsAffineHom g]
    [Fintype ι] (𝒰 : ι → X.Opens) (h𝒰 : IsOpenCover 𝒰)
    (h𝒰_affine : ∀ i, IsAffineOpen (𝒰 i))
    (ℱ : X.Modules) :
    ((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (pushforwardOpenCoverCechComplex f 𝒰 ℱ) =
      pushforwardOpenCoverCechComplex (pullback.snd f g)
        (baseChangeOpenCover f g 𝒰)
        (baseChangeModule f g ℱ) := sorry

end AlgebraicGeometry.Scheme
