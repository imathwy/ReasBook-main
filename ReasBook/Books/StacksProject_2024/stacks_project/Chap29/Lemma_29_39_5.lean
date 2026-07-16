import Mathlib.Data.List.TFAE
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import StacksProject_2024.stacks_project.Chap28.Definition_28_26_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_15_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_31_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

open Scheme.Modules

/- Semantic recall / owner check:
- `lean_leansearch` recalled the canonical scheme-morphism finite-type layer; local Chapter 29
  supplies the source-facing relative-ampleness owners.
- The checked-in `RelativelyAmple`/`RelativelyVeryAmple` owners currently force
  `Definition_29_37_1.lean`, which is not dependency-closed in item checking, so the theorem below
  spells out the same source conditions directly: relative ampleness means quasi-compactness plus
  ampleness on affine preimages, and relative very ampleness means a projective-bundle immersion
  presentation.
- Local Chapter 29 precedent fixes finite type as `f.FiniteType`, quasi-compactness of the base
  as `[CompactSpace S]`, and tensor powers of an invertible module as `(hL d)`.
- The Stacks tag evidence is consistent: item tag `01VU` and source URL
  `https://stacks.math.columbia.edu/tag/01VU`.
-/

section

variable {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}

/-- The affine-preimage form of relative ampleness used here when the packaged
relative-ampleness owner is unavailable in item checking. -/
structure RelativelyAmpleOnAffinePreimages (f : X ⟶ S) (L : X.Modules)
    [hRestrictMonoidal : ∀ U : S.affineOpens,
      MonoidalCategory (f ⁻¹ᵁ (U : S.Opens)).toScheme.Modules] : Prop where
  /-- The structure morphism is quasi-compact. -/
  quasiCompact : QuasiCompact f
  /-- The restriction to each affine preimage is invertible. -/
  restrict_invertible :
    ∀ U : S.affineOpens,
      @Invertible (f ⁻¹ᵁ (U : S.Opens)).toScheme
        (hRestrictMonoidal U) (L.restrict ((f ⁻¹ᵁ (U : S.Opens)).ι))
  /-- The restriction to each affine preimage is ample. -/
  restrict_isAmple :
    ∀ U : S.affineOpens,
      @IsAmple (f ⁻¹ᵁ (U : S.Opens)).toScheme
        (hRestrictMonoidal U) (L.restrict ((f ⁻¹ᵁ (U : S.Opens)).ι))
        (restrict_invertible U)

/-- A projective-bundle presentation showing that a fixed tensor power of an invertible module
is relatively very ample in the expanded form used here. -/
inductive TensorPowerRelativelyVeryAmple (f : X ⟶ S) (L : X.Modules)
    [MonoidalCategory X.Modules] [hL : Invertible L] (d : ℕ) : Prop where
  /-- Constructor from a quasi-coherent projective-bundle presentation plus an immersion whose
  pullback of the tautological sheaf is the chosen tensor power. -/
  | mk
      (P : Scheme.{u}) (π : P ⟶ S) (ℰ : S.Modules)
      (quasicoherent : ℰ.IsQuasicoherent)
      (projectiveBundle : Scheme.IsProjectiveBundle π ℰ)
      (i : X ⟶ P) (isImmersion : IsImmersion i) (comp_eq : i ≫ π = f)
      (pullbackIso :
        Nonempty (hL d ≅ (pullback i).obj (SheafOfModules.unit P.ringCatSheaf)))

/-- The existence of a positive tensor power that is relatively very ample in the expanded
projective-bundle form used here. -/
inductive SomeTensorPowerRelativelyVeryAmple (f : X ⟶ S) (L : X.Modules)
    [MonoidalCategory X.Modules] [Invertible L] : Prop where
  /-- Constructor from a positive exponent whose tensor power has the expanded
  projective-bundle relative-very-ample presentation. -/
  | mk (d : ℕ) (one_le : 1 ≤ d) (veryAmple : TensorPowerRelativelyVeryAmple f L d)

/-- The eventual positive tensor-power relative very ampleness clause in the expanded
projective-bundle form used here. -/
inductive EventuallyTensorPowerRelativelyVeryAmple (f : X ⟶ S) (L : X.Modules)
    [MonoidalCategory X.Modules] [Invertible L] : Prop where
  /-- Constructor from a positive threshold after which each tensor power has the expanded
  projective-bundle relative-very-ample presentation. -/
  | mk (d₀ : ℕ) (one_le : 1 ≤ d₀)
      (eventually_veryAmple : ∀ d : ℕ, d₀ ≤ d → TensorPowerRelativelyVeryAmple f L d)

/-- Lemma 29.39.5: let `f : X ⟶ S` be a morphism of schemes and let `\mathcal L`
be an invertible `\mathcal O_X`-module. Assume `S` is quasi-compact and `f` is of finite type.
Then the following are equivalent: `\mathcal L` is `f`-ample; for some `d ≥ 1`,
`\mathcal L^{\otimes d}` is `f`-very ample; and for all sufficiently large `d`,
`\mathcal L^{\otimes d}` is `f`-very ample. Since the current relative-ampleness owners are not
dependency-closed for item checking, the three clauses are stated using their defining
affine-preimage and projective-bundle-presentation conditions. -/
@[stacks 01VU]
theorem relativeAmpleness_tfae_tensorPow_relativeVeryAmpleness
    [MonoidalCategory X.Modules] [CompactSpace S] [f.FiniteType]
    [hRestrictMonoidal : ∀ U : S.affineOpens,
      MonoidalCategory (f ⁻¹ᵁ (U : S.Opens)).toScheme.Modules]
    [hL : Invertible L] :
    List.TFAE [
    RelativelyAmpleOnAffinePreimages f L,
    SomeTensorPowerRelativelyVeryAmple f L,
    EventuallyTensorPowerRelativelyVeryAmple f L] := sorry

end

end AlgebraicGeometry
