import StacksProject_2024.Chap29.Definition_29_37_1
import StacksProject_2024.Chap31.Definition_31_31_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall / owner check:
- `Scheme.IsProjectiveBundle`, `Scheme.ProjectiveBundleQuotient`, and
  `Scheme.projectiveBundleLiftEquivQuotient` are already owned by Chapter 31 as the current
  repository-level projective-bundle universal-property API;
- Definition 29.38.1 is source-facing relative very ampleness, so this file should reuse that
  canonical projective-bundle owner rather than restating it locally.

The declarations below therefore keep the source-facing relative-very-ample owner and define its
tautological quotient/sheaf API as a thin bridge on top of `Scheme.IsProjectiveBundle`. -/

section

variable {X S P : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}
variable {ℰ : S.Modules}

/-- The tautological sheaf on a projective bundle presentation.  This statement-level owner keeps
only the module surface needed downstream. -/
abbrev projectiveBundleTautologicalSheaf
    (π : P ⟶ S) (hπ : Scheme.IsProjectiveBundle π ℰ) :
    P.Modules :=
  SheafOfModules.unit P.ringCatSheaf

/-- The tautological sheaf on a projective bundle is invertible for the source-facing owner,
with the required monoidal structure carried explicitly. -/
theorem projectiveBundleTautologicalSheaf_hasInvertibleModuleStructure
    (π : P ⟶ S) (hπ : Scheme.IsProjectiveBundle π ℰ) :
    HasInvertibleModuleStructure (projectiveBundleTautologicalSheaf π hπ) := sorry

/-- An immersion into a chosen projective-bundle presentation over `S` exhibits `L` as the
pullback of the tautological quotient sheaf. -/
structure RelativelyVeryAmplePresentation
    (f : X ⟶ S) (L : X.Modules)
    (π : P ⟶ S) (ℰ : S.Modules) (hπ : Scheme.IsProjectiveBundle π ℰ)
    (i : X ⟶ P) : Prop where
  /-- The comparison map into the projective bundle is an immersion. -/
  isImmersion : IsImmersion i
  /-- The immersion is a morphism over `S`. -/
  comp_eq : i ≫ π = f
  /-- Pulling back the tautological quotient recovers the chosen invertible sheaf `L`. -/
  pullbackIso :
    Nonempty (L ≅ (Scheme.Modules.pullback i).obj (projectiveBundleTautologicalSheaf π hπ))

/-- Definition 29.38.1: an invertible `\mathcal{O}_X`-module `\mathcal L` is relatively very
ample on `X/S` if there exist a quasi-coherent `\mathcal O_S`-module `\mathcal E`, a projective
bundle presentation of `\mathbf P(\mathcal E)` over `S`, and an immersion of `X` into that
projective bundle over `S` such that `\mathcal L` is isomorphic to the pullback of the
tautological quotient sheaf `\mathcal O(1)`. -/
class RelativelyVeryAmple (f : X ⟶ S) (L : X.Modules) : Prop where
  /-- The module is invertible on `X`, with the necessary monoidal structure recorded
  explicitly. -/
  invertible : HasInvertibleModuleStructure L
  exists_presentation :
    ∃ (P : Scheme.{u}) (π : P ⟶ S) (ℰ : S.Modules),
      ℰ.IsQuasicoherent ∧
        ∃ (hπ : Scheme.IsProjectiveBundle π ℰ) (i : X ⟶ P),
          RelativelyVeryAmplePresentation f L π ℰ hπ i

/-- A relatively very ample module is invertible on the source. -/
theorem RelativelyVeryAmple.hasInvertibleModuleStructure
    (h : RelativelyVeryAmple f L) :
    HasInvertibleModuleStructure L :=
  h.invertible

/-- Unfold a relatively very ample invertible module into a quasi-coherent projective-bundle
presentation over `S` and an immersion pulling back the tautological quotient sheaf to `L`. -/
theorem RelativelyVeryAmple.presentation
    (h : RelativelyVeryAmple f L) :
    ∃ (P : Scheme.{u}) (π : P ⟶ S) (ℰ : S.Modules),
      ℰ.IsQuasicoherent ∧
        ∃ (hπ : Scheme.IsProjectiveBundle π ℰ) (i : X ⟶ P),
          RelativelyVeryAmplePresentation f L π ℰ hπ i :=
  h.exists_presentation

/-- A relatively very ample invertible module has separated structure morphism. -/
theorem RelativelyVeryAmple.isSeparated
    (h : RelativelyVeryAmple f L) :
    IsSeparated f := sorry

/-- A relatively very ample invertible module is relatively ample. -/
theorem RelativelyVeryAmple.toRelativelyAmple
    (h : RelativelyVeryAmple f L) :
    RelativelyAmple f L := sorry

/-- A relatively very ample invertible module is relatively ample. -/
instance instRelativelyAmpleOfRelativelyVeryAmple
    [h : RelativelyVeryAmple f L] :
    RelativelyAmple f L :=
  h.toRelativelyAmple

end

end AlgebraicGeometry
