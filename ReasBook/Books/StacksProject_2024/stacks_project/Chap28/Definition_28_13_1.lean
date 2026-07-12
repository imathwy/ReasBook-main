import StacksProject_2024.Chap10.Definition_10_162_1
import StacksProject_2024.Chap28.Definition_28_4_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local analogue check:
-- the canonical Chapter 28 local owner is `HasRingPropertyLocally`, used directly below for the
-- universally Japanese and Nagata parts. The integral Japanese condition is more specific because
-- the `N-2` owner needs the domain structure on `Γ(X, U)`, which is available on a nonempty
-- affine open of an integral scheme.

/-- On an integral scheme, the section ring on a nonempty affine open is a domain. -/
theorem affineOpenSections_isDomain (X : Scheme.{u}) [IsIntegral X] (U : X.affineOpens)
    (hU : Nonempty U) : IsDomain (Γ(X, U)) :=
  letI : Nonempty (U : X.Opens) := hU
  IsIntegral.component_integral (X := X) (U := (U : X.Opens))

/-- On an integral scheme, a nonempty affine open has Japanese section ring exactly when that
section ring is `N-2` with the domain structure induced by integrality. -/
abbrev affineOpenSectionsIsN2Ring (X : Scheme.{u}) [IsIntegral X] (U : X.affineOpens)
    (hU : Nonempty U) : Prop :=
  letI := affineOpenSections_isDomain X U hU
  IsN2Ring (Γ(X, U))

/-- Definition 28.13.1 (1): if `X` is integral, then `X` is Japanese when every point of `X`
admits an affine open neighborhood whose ring of sections is Japanese, i.e. `N-2`. -/
@[stacks 033S]
abbrev IsJapanese (X : Scheme.{u}) [IsIntegral X] : Prop :=
  ∀ x : X,
    ∃ U : X.affineOpens,
      ∃ hx : x ∈ (U : X.Opens),
        affineOpenSectionsIsN2Ring X U ⟨⟨x, hx⟩⟩

/-- On an integral Japanese scheme, every point lies in an affine open neighborhood with Japanese
coordinate ring. -/
theorem exists_affineOpen_isN2Ring (X : Scheme.{u}) [IsIntegral X] (h : IsJapanese X) (x : X) :
    ∃ U : X.affineOpens,
      ∃ hx : x ∈ (U : X.Opens),
        affineOpenSectionsIsN2Ring X U ⟨⟨x, hx⟩⟩ :=
  h x

/-- Unfold `IsJapanese` into the affine-open neighborhood condition on points. -/
theorem isJapanese_iff (X : Scheme.{u}) [IsIntegral X] :
    IsJapanese X ↔
      ∀ x : X,
        ∃ U : X.affineOpens,
          ∃ hx : x ∈ (U : X.Opens),
            affineOpenSectionsIsN2Ring X U ⟨⟨x, hx⟩⟩ :=
  Iff.rfl

/-- Definition 28.13.1 (2): the affine-local universally Japanese condition on a scheme. The
source's integrality hypothesis is redundant for this owner. -/
@[stacks 033S]
abbrev UniversallyJapanese (X : Scheme.{u}) : Prop :=
  X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ UniversallyJapaneseRing.{u, u} A)

/-- On a universally Japanese scheme, every point lies in an affine open neighborhood with
universally Japanese coordinate ring. -/
theorem exists_affineOpen_universallyJapaneseRing (X : Scheme.{u}) [UniversallyJapanese X]
    (x : X) :
    ∃ U : X.affineOpens,
      x ∈ (U : X.Opens) ∧ UniversallyJapaneseRing.{u, u} (Γ(X, (U : X.Opens))) :=
  HasRingPropertyLocally.exists_affineOpen X
    (fun A : CommRingCat.{u} ↦ UniversallyJapaneseRing.{u, u} A) x

/-- Unfold `UniversallyJapanese` into the affine-open neighborhood condition on points. -/
theorem universallyJapanese_iff (X : Scheme.{u}) :
    UniversallyJapanese X ↔
      ∀ x : X,
        ∃ U : X.affineOpens,
          x ∈ (U : X.Opens) ∧ UniversallyJapaneseRing.{u, u} (Γ(X, (U : X.Opens))) :=
  hasRingPropertyLocally_iff X
    (fun A : CommRingCat.{u} ↦ UniversallyJapaneseRing.{u, u} A)

/-- Definition 28.13.1 (3): the affine-local Nagata condition on a scheme. The source's integrality
hypothesis is redundant for this owner. -/
@[stacks 033S]
abbrev Nagata (X : Scheme.{u}) : Prop :=
  X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ NagataRing A)

/-- On a Nagata scheme, every point lies in an affine open neighborhood with Nagata coordinate
ring. -/
theorem exists_affineOpen_nagataRing (X : Scheme.{u}) [Nagata X] (x : X) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ NagataRing (Γ(X, (U : X.Opens))) :=
  HasRingPropertyLocally.exists_affineOpen X
    (fun A : CommRingCat.{u} ↦ NagataRing A) x

/-- Unfold `Nagata` into the affine-open neighborhood condition on points. -/
theorem nagata_iff (X : Scheme.{u}) :
    Nagata X ↔
      ∀ x : X,
        ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ NagataRing (Γ(X, (U : X.Opens))) :=
  hasRingPropertyLocally_iff X (fun A : CommRingCat.{u} ↦ NagataRing A)

end AlgebraicGeometry.Scheme
