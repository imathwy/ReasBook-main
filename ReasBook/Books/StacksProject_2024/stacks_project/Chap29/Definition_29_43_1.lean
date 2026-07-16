import StacksProject_2024.stacks_project.Chap29.Definition_29_38_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_31_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall / source/core/bridge check:
- source-facing owners in this file: `Projective`, `HProjective`, `LocallyProjective`;
- core canonical owner reused here: `Scheme.IsProjectiveBundle`;
- canonical Chapter 29 projective-space owner reused here: `ProjectiveSpaceOver`.

This file therefore records Definition 29.43.1 on the canonical projective-bundle and relative
projective-space surfaces. The projective owner keeps the direct projective-bundle presentation
API from the source, while the H-projective owner now speaks directly about a closed immersion into
`ProjectiveSpaceOver S n`, matching the source phrase “closed immersion into `\mathbf P^n_S`”.
The downstream bridge from `HProjective` to Chapter 29's affine-local `HQuasiProjective` owner is
kept in `Lemma_29_43_3.lean`, since it is not part of the projective-bundle owner itself. -/

section

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The free rank-`n + 1` `\mathcal O_S`-module whose projective bundle models `\mathbf P^n_S`. -/
abbrev standardProjectiveBundleModule (S : Scheme.{u}) (n : ℕ) : S.Modules :=
  (SheafOfModules.free.{u} (ULift.{u} (Fin (n + 1))) : S.Modules)

/-- The relative projective space `\mathbf P^n_S`, recorded through the Chapter 29
projective-bundle owner for the standard free module. -/
structure ProjectiveSpaceOver (S : Scheme.{u}) (n : ℕ) where
  /-- The underlying scheme of the relative projective space. -/
  scheme : Scheme.{u}
  /-- The structure morphism to the base. -/
  hom : scheme ⟶ S
  /-- The projective-bundle presentation over the standard free module. -/
  isProjectiveBundle :
    Scheme.IsProjectiveBundle hom (standardProjectiveBundleModule S n)

/-- A projective-bundle presentation of `f : X ⟶ S` through a chosen projective bundle
`π : P ⟶ S`. -/
structure ProjectivePresentation
    {P : Scheme.{u}} (f : X ⟶ S) (π : P ⟶ S) (i : X ⟶ P) : Prop where
  /-- The comparison morphism into the projective bundle is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion i
  /-- The comparison morphism lies over the base morphism `f`. -/
  comp_eq : i ≫ π = f

namespace ProjectivePresentation

variable {P : Scheme.{u}} {π : P ⟶ S} {i : X ⟶ P}

/-- A projective presentation equips its comparison morphism with the canonical closed-immersion
instance. -/
instance instIsClosedImmersion
    (h : ProjectivePresentation f π i) :
    IsClosedImmersion i :=
  h.isClosedImmersion

/-- The comparison morphism in a projective presentation lies over the base morphism. -/
@[reassoc (attr := simp)]
theorem w
    (h : ProjectivePresentation f π i) :
    i ≫ π = f :=
  h.comp_eq

/-- Companion projection of the closed-immersion content of a projective presentation. -/
theorem closedImmersion
    (h : ProjectivePresentation f π i) :
    IsClosedImmersion i :=
  h.isClosedImmersion

end ProjectivePresentation

/-- Definition 29.43.1 (1): a morphism `f : X ⟶ S` is projective if it factors as a closed
immersion into a projective bundle attached to a quasi-coherent finite type
`\mathcal O_S`-module. -/
@[stacks 01W8]
class Projective (f : X ⟶ S) : Prop where
  /-- A projective-bundle presentation over `S` together with a closed immersion over `S`
  presenting `f`. -/
  exists_presentation :
    ∃ (P : Scheme.{u}) (π : P ⟶ S) (ℰ : S.Modules),
      ℰ.IsFiniteType ∧ ℰ.IsQuasicoherent ∧
        ∃ _ : Scheme.IsProjectiveBundle π ℰ, ∃ i : X ⟶ P,
          ProjectivePresentation f π i

/-- Definition 29.43.1 (2): a morphism `f : X ⟶ S` is H-projective if there exists an integer `n`
and a closed immersion of `X` over `S` into projective `n`-space over `S`. -/
@[stacks 01W8]
class HProjective (f : X ⟶ S) : Prop where
  /-- A closed immersion over `S` into a relative projective space `\mathbf P^n_S` presenting
  `f`. -/
  exists_presentation :
    ∃ (n : ℕ) (P : ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
      ProjectivePresentation f P.hom i

/-- Definition 29.43.1 (3): a morphism `f : X ⟶ S` is locally projective if there exists an open
cover of `S` such that each restricted morphism over a member of the cover is projective. -/
@[stacks 01W8]
class LocallyProjective (f : X ⟶ S) : Prop where
  /-- A target open cover on which the restriction of `f` is projective. -/
  exists_cover :
    ∃ 𝒰 : Scheme.OpenCover.{u} S, ∀ i : 𝒰.I₀, Projective (f ∣_ ((𝒰.f i).opensRange))

/-- Unfold a projective morphism into a chosen projective-bundle presentation over `S` together
with the closed immersion presenting it. -/
theorem Projective.presentation
    (h : Projective f) :
    ∃ (P : Scheme.{u}) (π : P ⟶ S) (ℰ : S.Modules),
      ℰ.IsFiniteType ∧ ℰ.IsQuasicoherent ∧
        ∃ _ : Scheme.IsProjectiveBundle π ℰ, ∃ i : X ⟶ P,
          ProjectivePresentation f π i :=
  h.exists_presentation

/-- Unfold `Projective f` as the existence of a finite-type quasi-coherent projective-bundle
presentation over `S` together with a closed immersion presenting `f`. -/
theorem projective_iff :
    Projective f ↔
      ∃ (P : Scheme.{u}) (π : P ⟶ S) (ℰ : S.Modules),
        ℰ.IsFiniteType ∧ ℰ.IsQuasicoherent ∧
          ∃ _ : Scheme.IsProjectiveBundle π ℰ, ∃ i : X ⟶ P,
            ProjectivePresentation f π i :=
  ⟨fun h ↦ h.presentation, fun h ↦ ⟨h⟩⟩

/-- Unfold an H-projective morphism into a chosen free-module projective-bundle presentation
together with a closed immersion presenting it. -/
theorem HProjective.presentation
    (h : HProjective f) :
    ∃ (n : ℕ) (P : ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
      ProjectivePresentation f P.hom i :=
  h.exists_presentation

/-- Unfold `HProjective f` as the existence of a closed immersion over `S` into some relative
projective space `\mathbf P^n_S`. -/
theorem hProjective_iff :
    HProjective f ↔
      ∃ (n : ℕ) (P : ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
        ProjectivePresentation f P.hom i :=
  ⟨fun h ↦ h.presentation, fun h ↦ ⟨h⟩⟩

/-- Unfold an H-projective morphism into the corresponding projective-bundle presentation of the
chosen relative projective space `\mathbf P^n_S`. -/
theorem HProjective.projectiveBundlePresentation
    (h : HProjective f) :
    ∃ (n : ℕ) (P : ProjectiveSpaceOver S n),
      ∃ _ : Scheme.IsProjectiveBundle P.hom (standardProjectiveBundleModule S n),
        ∃ i : X ⟶ P.scheme, ProjectivePresentation f P.hom i := by
  rcases h.presentation with ⟨n, P, i, hi⟩
  exact ⟨n, P, P.isProjectiveBundle, i, hi⟩

/-- Unfold a locally projective morphism into a chosen target open cover on which its restrictions
are projective. -/
theorem LocallyProjective.openCover
    (h : LocallyProjective f) :
    ∃ 𝒰 : Scheme.OpenCover.{u} S, ∀ i : 𝒰.I₀, Projective (f ∣_ ((𝒰.f i).opensRange)) :=
  h.exists_cover

/-- Unfold `LocallyProjective f` as the existence of a target open cover on which the restricted
morphisms are projective. -/
theorem locallyProjective_iff :
    LocallyProjective f ↔
      ∃ 𝒰 : Scheme.OpenCover.{u} S, ∀ i : 𝒰.I₀, Projective (f ∣_ ((𝒰.f i).opensRange)) :=
  ⟨fun h ↦ h.openCover, fun h ↦ ⟨h⟩⟩

/-- Any H-projective morphism is projective. -/
theorem HProjective.toProjective
    (h : HProjective f) :
    Projective f := sorry

/-- An H-projective morphism is projective. -/
instance instProjectiveOfHProjective [h : HProjective f] :
    Projective f :=
  h.toProjective

/-- Any projective morphism is locally projective. -/
theorem Projective.toLocallyProjective
    (h : Projective f) :
    LocallyProjective f := sorry

/-- A projective morphism is locally projective. -/
instance instLocallyProjectiveOfProjective [h : Projective f] :
    LocallyProjective f :=
  h.toLocallyProjective

end

end AlgebraicGeometry
