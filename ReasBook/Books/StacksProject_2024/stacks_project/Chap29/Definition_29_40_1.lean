import StacksProject_2024.Chap29.Definition_29_15_1
import StacksProject_2024.Chap29.Definition_29_37_1
import StacksProject_2024.Chap29.ProjectiveSpaceBasic

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the scheme-morphism owners `LocallyOfFiniteType`, `QuasiCompact`,
  and `IsImmersion`, together with the absolute `Proj` API;
- the nearby relative-ampleness owner is `RelativelyAmple`.
- `ProjectiveSpaceBasic.lean` exports the Chapter 29 affine-base projective-space helpers
  `projectiveSpace` and `projectiveSpaceToAffineOpen`.

This file therefore records the source item directly, reusing the existing affine-local
projective-space presentation owner instead of introducing a second projective-space packaging
layer, and keeps the three source properties as `Prop`-valued classes with existential fields
instead of data-bearing `Prop` fields. -/

section

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- An affine-local projective-space presentation of `f` by closed immersions into standard
projective space over affine base opens. -/
def AffineLocalProjectiveSpacePresentation (f : X ⟶ S) : Prop :=
  ∃ n : ℕ, ∀ (U : S.Opens) (hU : IsAffineOpen U),
    ∃ i : (f ⁻¹ᵁ U).toScheme ⟶ projectiveSpace Γ(S, U) n,
      IsClosedImmersion i ∧
        i ≫ projectiveSpaceToAffineOpen U hU n = f ∣_ U

/-- Over any affine open of the base, an affine-local projective-space presentation supplies a
closed immersion of the restricted morphism into some standard projective space over that open. -/
theorem AffineLocalProjectiveSpacePresentation.onAffineOpen
    (h : AffineLocalProjectiveSpacePresentation f) (U : S.Opens) (hU : IsAffineOpen U) :
    ∃ n : ℕ, ∃ i : (f ⁻¹ᵁ U).toScheme ⟶ projectiveSpace Γ(S, U) n,
      IsClosedImmersion i ∧
        i ≫ projectiveSpaceToAffineOpen U hU n = f ∣_ U := by
  rcases h with ⟨n, hn⟩
  rcases hn U hU with ⟨i, hi, hcomp⟩
  exact ⟨n, i, hi, hcomp⟩

/-- Definition 29.40.1 (1): a morphism `f : X ⟶ S` is quasi-projective if and only if it is of
finite type and there exists an `f`-relatively ample invertible `\mathcal{O}_X`-module. -/
class QuasiProjective (f : X ⟶ S) : Prop extends Scheme.Hom.FiniteType f where
  /-- There exists an `f`-relatively ample invertible `\mathcal O_X`-module. -/
  exists_relativelyAmple :
    ∃ L : X.Modules, RelativelyAmple f L

/-- A quasi-projective morphism is locally of finite type. -/
instance instLocallyOfFiniteTypeQuasiProjective [h : QuasiProjective f] :
    LocallyOfFiniteType f :=
  h.toFiniteType.toLocallyOfFiniteType

/-- A quasi-projective morphism is quasi-compact. -/
instance instQuasiCompactQuasiProjective [h : QuasiProjective f] :
    QuasiCompact f :=
  h.toFiniteType.toQuasiCompact

/-- Unfold `QuasiProjective f` into the canonical finite-type owner together with a relatively
ample invertible `\mathcal O_X`-module. -/
theorem quasiProjective_iff :
    QuasiProjective f ↔
      Scheme.Hom.FiniteType f ∧
        ∃ L : X.Modules, RelativelyAmple f L :=
  ⟨fun h ↦ ⟨h.toFiniteType, h.exists_relativelyAmple⟩, fun h ↦ by
    letI : Scheme.Hom.FiniteType f := h.1
    exact { exists_relativelyAmple := h.2 }⟩

/-- Definition 29.40.1 (2): a morphism `f : X ⟶ S` is H-quasi-projective if and only if there
exists a scheme `P` over `S` with an affine-local projective-space presentation and a
quasi-compact immersion of `X` over `S` into `P`. -/
class HQuasiProjective (f : X ⟶ S) : Prop where
  /-- There exists an affine-locally presented projective space over `S` into which `X` immerses
  over `S`. -/
  exists_presentation :
    ∃ (P : Scheme.{u}) (p : P ⟶ S),
      AffineLocalProjectiveSpacePresentation p ∧
        ∃ i : X ⟶ P, QuasiCompact i ∧ IsImmersion i ∧ (i ≫ p = f)

/-- Unfold an H-quasi-projective morphism into a chosen affine-locally presented projective-space
scheme together with a quasi-compact immersion over `S`. -/
theorem HQuasiProjective.presentation
    (h : HQuasiProjective f) :
    ∃ (P : Scheme.{u}) (p : P ⟶ S),
      AffineLocalProjectiveSpacePresentation p ∧
        ∃ i : X ⟶ P, QuasiCompact i ∧ IsImmersion i ∧ (i ≫ p = f) :=
  h.exists_presentation

/-- An H-quasi-projective morphism is locally of finite type. -/
theorem HQuasiProjective.locallyOfFiniteType
    (h : HQuasiProjective f) :
    LocallyOfFiniteType f := sorry

/-- An H-quasi-projective morphism is locally of finite type. -/
instance instLocallyOfFiniteTypeOfHQuasiProjective [h : HQuasiProjective f] :
    LocallyOfFiniteType f :=
  h.locallyOfFiniteType

/-- Unfold `HQuasiProjective f` into a quasi-compact immersion over an affine-locally presented
projective-space scheme. -/
theorem hQuasiProjective_iff :
    HQuasiProjective f ↔
      ∃ (P : Scheme.{u}) (p : P ⟶ S),
        AffineLocalProjectiveSpacePresentation p ∧
          ∃ i : X ⟶ P, QuasiCompact i ∧ IsImmersion i ∧ (i ≫ p = f) :=
  ⟨fun h ↦ h.presentation, fun h ↦ ⟨h⟩⟩

/-- An H-quasi-projective morphism is quasi-projective. -/
theorem HQuasiProjective.toQuasiProjective
    (h : HQuasiProjective f) :
    QuasiProjective f := sorry

/-- An H-quasi-projective morphism is quasi-projective. -/
instance instQuasiProjectiveOfHQuasiProjective [h : HQuasiProjective f] :
    QuasiProjective f :=
  h.toQuasiProjective

/-- Definition 29.40.1 (3): a morphism `f : X ⟶ S` is locally quasi-projective if there exists an
open cover of `S` such that each restricted morphism over a member of the cover is
quasi-projective. -/
class LocallyQuasiProjective (f : X ⟶ S) : Prop where
  /-- There exists an open cover of the base on which the restricted morphisms are
  quasi-projective. -/
  exists_cover :
    ∃ 𝒰 : Scheme.OpenCover.{u} S, ∀ i : 𝒰.I₀, QuasiProjective (f ∣_ ((𝒰.f i).opensRange))

/-- Unfold a locally quasi-projective morphism into a chosen target open cover on which its
restrictions are quasi-projective. -/
theorem LocallyQuasiProjective.openCover
    (h : LocallyQuasiProjective f) :
    ∃ 𝒰 : Scheme.OpenCover.{u} S, ∀ i : 𝒰.I₀, QuasiProjective (f ∣_ ((𝒰.f i).opensRange)) :=
  h.exists_cover

/-- Any quasi-projective morphism is locally quasi-projective. -/
theorem QuasiProjective.toLocallyQuasiProjective
    (h : QuasiProjective f) :
    LocallyQuasiProjective f := sorry

/-- A quasi-projective morphism is locally quasi-projective. -/
instance instLocallyQuasiProjectiveOfQuasiProjective [h : QuasiProjective f] :
    LocallyQuasiProjective f :=
  h.toLocallyQuasiProjective

/-- Unfold `LocallyQuasiProjective f` as the existence of an open cover of the base on which the
restricted morphisms are quasi-projective. -/
theorem locallyQuasiProjective_iff :
    LocallyQuasiProjective f ↔
      ∃ 𝒰 : Scheme.OpenCover.{u} S, ∀ i : 𝒰.I₀, QuasiProjective (f ∣_ ((𝒰.f i).opensRange)) :=
  ⟨fun h ↦ h.openCover, fun h ↦ ⟨h⟩⟩

end

end AlgebraicGeometry
