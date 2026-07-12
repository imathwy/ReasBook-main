import Mathlib
import StacksProject_2024.Chap10.Lemma_10_57_9
import StacksProject_2024.Chap17.Definition_17_25_7
import StacksProject_2024.Chap17.Lemma_17_25_10
import StacksProject_2024.Chap28.Lemma_28_17_1

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry DirectSum SectionNonvanishingOpen

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

local notation "ModX" => X.Modules
local notation "IsInvertibleX" =>
  (fun ℒ : ModX ↦ Functor.IsEquivalence (CategoryTheory.MonoidalCategory.tensorRight ℒ))

-- Source/core/bridge triage:
-- - source-facing: the displayed localized twisted graded module
--   `Γ_*(X, ℒ, ℱ)_(s)` and its comparison map to `Γ(X_s, ℱ|_{X_s})`;
-- - core/canonical: `awayDegreeZeroPart` for homogeneous localization, the Chapter 17 graded
--   twisted global-sections owners, and the Chapter 17 nonvanishing-open owner `(X)_[s]`;
-- - bridge/view: comparison maps out of the localized graded source, controlled by their values on
--   the standard fractions `m / s^n`.

/- 28.17.1.1: for an invertible `\mathcal O_X`-module `\mathcal L`, a section
`s : \Gamma(X, \mathcal L)`, and an `\mathcal O_X`-module `\mathcal F`, the displayed map
`Γ_*(X, \mathcal L, \mathcal F)_(s) \to \Gamma(X_s, \mathcal F|_{X_s})` is the canonical bridge
from the degree-zero part of the homogeneous localization of the graded twisted global sections
module away from `s` to the sections of `\mathcal F` on the nonvanishing open `X_s`.

In the current repository, the source-facing localized graded module is canonically realized as an
`awayDegreeZeroPart` of the Chapter 17 graded twisted global-sections module. The nonvanishing
open `X_s` is already owned by the Chapter 17 RingedSpace construction `(X.toRingedSpace)_[s]`.
This file therefore keeps the source object itself as a concrete declaration and exposes the
comparison-map layer through its standard fraction generators, rather than collapsing the item to a
recall-only block or introducing a new wrapper owner. -/

/-- The degree-`n` summand of `Γ_*(X, \mathcal L)` as a graded submodule of the direct sum. -/
abbrev gradedGlobalSectionsSubmodule (ℒ : ModX) (n : ℕ) :
    Submodule Γ(X, ⊤) Γ_*(ℒ) :=
  LinearMap.range <|
    DirectSum.lof Γ(X, ⊤) ℕ
      (fun i ↦ AlgebraicGeometry.RingedSpace.gradedGlobalSectionsDegree ℒ i) n

/-- The nonnegative twisted degree pieces of `Γ_*(X, \mathcal L, \mathcal F)` as graded
submodules of the direct sum. This is the source-facing family used for
`Γ_*(X, \mathcal L, \mathcal F)_(s)`. -/
abbrev gradedTwistedGlobalSectionsSubmodule
    (ℒ : ModX) [IsInvertibleX ℒ] (ℱ : ModX) (n : ℕ) :
    Submodule Γ(X, ⊤) Γ_*(ℒ, ℱ) :=
  LinearMap.range <|
    DirectSum.lof Γ(X, ⊤) ℤ
      (fun i ↦ AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSectionsDegree ℒ ℱ i) (n : ℤ)

/-- A section `s : Γ(X, \mathcal L)` viewed as the degree-`1` homogeneous element of
`Γ_*(X, \mathcal L)`. -/
abbrev gradedGlobalSectionsDegreeOne
    (ℒ : ModX) (s : Γ(ℒ, ⊤)) :
    gradedGlobalSectionsSubmodule (X := X) ℒ 1 := by
  refine ⟨DirectSum.lof Γ(X, ⊤) ℕ
      (fun i ↦ AlgebraicGeometry.RingedSpace.gradedGlobalSectionsDegree ℒ i) 1
      (SheafOfModules.sectionsMap ((ρ_ ℒ).inv) s), ?_⟩
  exact ⟨SheafOfModules.sectionsMap ((ρ_ ℒ).inv) s, rfl⟩

/-- The source-facing localized graded module `Γ_*(X, \mathcal L, \mathcal F)_(s)` from
28.17.1.1, realized canonically as the degree-zero homogeneous localization of
`Γ_*(X, \mathcal L, \mathcal F)` away from the degree-`1` element defined by `s`. -/
abbrev localizedTwistedGlobalSections
    (ℒ : ModX) [IsInvertibleX ℒ] (ℱ : ModX) (s : Γ(ℒ, ⊤)) :=
  awayDegreeZeroPart
    (gradedGlobalSectionsSubmodule (X := X) ℒ)
    (gradedTwistedGlobalSectionsSubmodule (X := X) ℒ ℱ)
    (gradedGlobalSectionsDegreeOne (X := X) ℒ s)

/-- The standard fraction `m / s^n` in `Γ_*(X, \mathcal L, \mathcal F)_(s)`. -/
abbrev localizedTwistedGlobalSectionsMk
    (ℒ : ModX) [IsInvertibleX ℒ] (ℱ : ModX) (s : Γ(ℒ, ⊤))
    (n : ℕ)
    (m : AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSectionsDegree ℒ ℱ (n : ℤ)) :
    localizedTwistedGlobalSections (X := X) ℒ ℱ s := by
  refine ⟨LocalizedModule.mk
      (DirectSum.lof Γ(X, ⊤) ℤ
        (fun i ↦ AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSectionsDegree ℒ ℱ i)
        (n : ℤ) m)
      ⟨((gradedGlobalSectionsDegreeOne (X := X) ℒ s :
          gradedGlobalSectionsSubmodule (X := X) ℒ 1) : Γ_*(ℒ)) ^ n, by
          exact ⟨n, rfl⟩⟩, ?_⟩
  exact awayDegreeZeroPart_mk_mem
    (gradedGlobalSectionsSubmodule (X := X) ℒ)
    (gradedTwistedGlobalSectionsSubmodule (X := X) ℒ ℱ)
    (gradedGlobalSectionsDegreeOne (X := X) ℒ s)
    (by exact ⟨m, rfl⟩)

/-- Every element of `Γ_*(X, \mathcal L, \mathcal F)_(s)` is represented by a standard fraction
`m / s^n` with `m` homogeneous of degree `n`. -/
theorem exists_localizedTwistedGlobalSectionsMk_eq
    (ℒ : ModX) [IsInvertibleX ℒ] (ℱ : ModX) (s : Γ(ℒ, ⊤))
    (z : localizedTwistedGlobalSections (X := X) ℒ ℱ s) :
    ∃ n : ℕ,
      ∃ m : AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSectionsDegree ℒ ℱ (n : ℤ),
        z = localizedTwistedGlobalSectionsMk (X := X) ℒ ℱ s n m := by
  rcases (mem_awayDegreeZeroPart_iff
      (gradedGlobalSectionsSubmodule (X := X) ℒ)
      (gradedTwistedGlobalSectionsSubmodule (X := X) ℒ ℱ)
      (gradedGlobalSectionsDegreeOne (X := X) ℒ s)).1 z.2 with ⟨n, m, hz⟩
  rcases m.2 with ⟨m0, rfl⟩
  refine ⟨n, m0, ?_⟩
  apply Subtype.ext
  simpa [localizedTwistedGlobalSectionsMk] using hz

/-- Extensionality for maps defined on `Γ_*(X, \mathcal L, \mathcal F)_(s)`: it suffices to check
the values on the standard fractions `m / s^n`. -/
theorem localizedTwistedGlobalSections_hom_ext
    (ℒ : ModX) [IsInvertibleX ℒ] (ℱ : ModX) (s : Γ(ℒ, ⊤))
    {M : Type*} {f g : localizedTwistedGlobalSections (X := X) ℒ ℱ s → M}
    (h :
      ∀ n (m : AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSectionsDegree ℒ ℱ (n : ℤ)),
        f (localizedTwistedGlobalSectionsMk (X := X) ℒ ℱ s n m) =
          g (localizedTwistedGlobalSectionsMk (X := X) ℒ ℱ s n m)) :
    f = g := by
  funext z
  rcases exists_localizedTwistedGlobalSectionsMk_eq (X := X) ℒ ℱ s z with ⟨n, m, rfl⟩
  exact h n m

/-- The target of the comparison map from 28.17.1.1, written using the canonical Chapter 17
nonvanishing-open owner `(X.toRingedSpace)_[s]`. -/
abbrev nonvanishingOpenSections
    (ℒ : ModX) [IsInvertibleX ℒ] (ℱ : ModX) (s : Γ(ℒ, ⊤)) :=
  Γ(ℱ, show X.Opens from (X.toRingedSpace)_[show ℒ.val.sections from s])

/-- Specification data for a comparison map
`Γ_*(X, \mathcal L, \mathcal F)_(s) \to \Gamma(X_s, \mathcal F|_{X_s})`: a value on each
standard fraction `m / s^n`. This is a bridge/view interface, not a second owner. -/
abbrev LocalizedTwistedGlobalSectionsComparisonSpec
    (ℒ : ModX) [IsInvertibleX ℒ] (ℱ : ModX) (s : Γ(ℒ, ⊤)) :=
  ∀ n : ℕ,
    AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSectionsDegree ℒ ℱ (n : ℤ) →
      nonvanishingOpenSections (X := X) ℒ ℱ s

/-- A comparison map out of `Γ_*(X, \mathcal L, \mathcal F)_(s)` is determined by its values on
the standard fractions `m / s^n`. -/
theorem localizedTwistedGlobalSectionsComparison_ext
    (ℒ : ModX) [IsInvertibleX ℒ] (ℱ : ModX) (s : Γ(ℒ, ⊤))
    {f g :
      localizedTwistedGlobalSections (X := X) ℒ ℱ s →
        nonvanishingOpenSections (X := X) ℒ ℱ s}
    (h :
      ∀ n (m : AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSectionsDegree ℒ ℱ (n : ℤ)),
        f (localizedTwistedGlobalSectionsMk (X := X) ℒ ℱ s n m) =
          g (localizedTwistedGlobalSectionsMk (X := X) ℒ ℱ s n m)) :
    f = g :=
  localizedTwistedGlobalSections_hom_ext (X := X) ℒ ℱ s h

/-- Source-facing existence surface for the comparison layer in 28.17.1.1: any textbook
construction of the displayed map is equivalent to giving its values on the standard fractions
`m / s^n`. -/
theorem exists_comparisonMap_iff
    (ℒ : ModX) [IsInvertibleX ℒ] (ℱ : ModX) (s : Γ(ℒ, ⊤)) :
    Nonempty
      (localizedTwistedGlobalSections (X := X) ℒ ℱ s →
        nonvanishingOpenSections (X := X) ℒ ℱ s) ↔
      Nonempty (LocalizedTwistedGlobalSectionsComparisonSpec (X := X) ℒ ℱ s) := by
  constructor
  · rintro ⟨φ⟩
    refine ⟨fun n m ↦ φ (localizedTwistedGlobalSectionsMk (X := X) ℒ ℱ s n m)⟩
  · rintro ⟨ψ⟩
    refine ⟨fun z ↦ by
      rcases exists_localizedTwistedGlobalSectionsMk_eq (X := X) ℒ ℱ s z with ⟨n, m, rfl⟩
      exact ψ n m⟩

end AlgebraicGeometry.Scheme.Modules
