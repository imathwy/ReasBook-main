import Mathlib
import StacksProject_2024.stacks_project.Chap26.Lemma_26_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped PrimeSpectrum

universe u

section

variable {R : Type u} [CommRing R]

namespace PrimeSpectrum

-- Semantic recall: `D(f)` is the canonical notation for standard opens, and the general notion is
-- a finite basic-open cover of `D(f)`. The `Spec(R)` case is the source-facing
-- special case `f = 1`.

/-- Definition 26.5.2 (2): a standard open covering of `D(f)` is a finite family of basic opens
`D(gᵢ)` whose supremum is `D(f)`. -/
structure StandardOpenCoverOf (f : R) where
  /-- The finite index type of the covering family. -/
  index : Type u
  /-- The covering family is finite. -/
  finiteIndex : Finite index
  /-- The ring elements defining the basic opens in the covering family. -/
  generator : index → R
  /-- The associated basic opens cover `D(f)`. -/
  cover :
    D(f) = ⨆ i, D(generator i)

attribute [instance] StandardOpenCoverOf.finiteIndex

/-- The basic opens of a standard open covering of `D(f)`. -/
def StandardOpenCoverOf.opens {f : R} (U : StandardOpenCoverOf f) :
    U.index → TopologicalSpace.Opens (PrimeSpectrum R) :=
  fun i ↦ D(U.generator i)

/-- A standard open cover of `D(f)` can be used as its underlying finite family of basic opens. -/
instance {f : R} : CoeFun (StandardOpenCoverOf f)
    (fun U ↦ U.index → TopologicalSpace.Opens (PrimeSpectrum R)) where
  coe := StandardOpenCoverOf.opens

@[simp] theorem StandardOpenCoverOf.coeFn_apply {f : R} (U : StandardOpenCoverOf f)
    (i : U.index) :
    U i = D(U.generator i) := rfl

/-- The basic opens in a standard open cover of `D(f)` have supremum `D(f)`. -/
theorem StandardOpenCoverOf.iSup_eq {f : R} (U : StandardOpenCoverOf f) :
    (⨆ i, U i) = D(f) := by
  simpa [StandardOpenCoverOf.opens] using U.cover.symm

/-- Each member of a standard open covering of `D(f)` is contained in `D(f)`. -/
theorem StandardOpenCoverOf.le {f : R} (U : StandardOpenCoverOf f) (i : U.index) :
    U i ≤ D(f) := by
  rw [← U.iSup_eq]
  exact le_iSup (fun j ↦ U j) i

/-- The canonical localization map attached to the inclusion of the `i`-th member of a standard
open cover of `D(f)`. -/
noncomputable abbrev StandardOpenCoverOf.restrictionRingHom {f : R} (U : StandardOpenCoverOf f)
    (i : U.index) :
    Localization.Away f →+* Localization.Away (U.generator i) :=
  awayToAwayRingHom f (U.generator i) (U.le i)

@[simp] theorem StandardOpenCoverOf.restrictionRingHom_algebraMap {f : R}
    (U : StandardOpenCoverOf f) (i : U.index) (r : R) :
    U.restrictionRingHom i (algebraMap R (Localization.Away f) r) =
      algebraMap R (Localization.Away (U.generator i)) r := by
  simpa [StandardOpenCoverOf.restrictionRingHom] using
    awayToAwayRingHom_algebraMap f (U.generator i) (U.le i) r

section ModuleMap

variable {M : Type*} [AddCommMonoid M] [Module R M]

/-- The canonical localized-module restriction map attached to the inclusion of the `i`-th member
of a standard open cover of `D(f)`. -/
noncomputable abbrev StandardOpenCoverOf.restrictionModuleMap {f : R}
    (U : StandardOpenCoverOf f) (i : U.index) :
    LocalizedModule.Away f M →ₗ[R] LocalizedModule.Away (U.generator i) M :=
  awayToAwayModuleMap f (U.generator i) (U.le i)

@[simp] theorem StandardOpenCoverOf.restrictionModuleMap_mkLinearMap {f : R}
    (U : StandardOpenCoverOf f) (i : U.index) (m : M) :
    U.restrictionModuleMap i
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M m) =
      LocalizedModule.mkLinearMap (Submonoid.powers (U.generator i)) M m := by
  simpa [StandardOpenCoverOf.restrictionModuleMap] using
    awayToAwayModuleMap_mkLinearMap f (U.generator i) (U.le i) m

end ModuleMap

/-- The generators of a standard open covering of `D(f)` generate the unit ideal after localizing
away from `f`. -/
  theorem StandardOpenCoverOf.span_eq_top_localization {f : R} (U : StandardOpenCoverOf f) :
    Ideal.span
        (Set.range fun i : U.index ↦ algebraMap R (Localization.Away f) (U.generator i)) = ⊤ := by
  exact
    (basicOpen_le_iSup_basicOpen_iff_span_eq_top f U.generator).mp <| by
      rw [U.cover]

/-- Source-facing specification for Definition 26.5.2 (2): a standard open covering of `D(f)`
is a finite family of basic opens whose supremum is `D(f)`, equivalently whose generators span the
unit ideal after localizing away from `f`. -/
theorem StandardOpenCoverOf.source_spec {f : R} (U : StandardOpenCoverOf f) :
    (⨆ i, U i) = D(f) ∧
      Ideal.span
          (Set.range fun i : U.index ↦ algebraMap R (Localization.Away f) (U.generator i)) = ⊤ := by
  exact ⟨U.iSup_eq, U.span_eq_top_localization⟩

/-- Definition 26.5.2 (1): a standard open covering of `Spec(R)` is a standard open covering of
`D(1) = Spec(R)`. -/
abbrev StandardOpenCover : Type _ := StandardOpenCoverOf (1 : R)

/-- The basic opens in a standard open cover of `Spec(R)` have supremum `⊤`. -/
theorem StandardOpenCover.iSup_eq_top (U : StandardOpenCover) :
    (⨆ i, U i) = (⊤ : TopologicalSpace.Opens (PrimeSpectrum R)) := by
  simpa [StandardOpenCover, basicOpen_one] using
    StandardOpenCoverOf.iSup_eq U

/-- The generators of a standard open covering of `Spec(R)` generate the unit ideal. -/
theorem StandardOpenCover.span_eq_top (U : StandardOpenCover) :
    (Ideal.span (Set.range U.generator) : Ideal R) = ⊤ := by
  exact iSup_basicOpen_eq_top_iff.mp (StandardOpenCover.iSup_eq_top U)

/-- Source-facing specification for Definition 26.5.2 (1): a standard open cover of `Spec(R)` is a
finite family of basic opens with supremum `⊤`, equivalently generators spanning the unit ideal.
-/
theorem StandardOpenCover.source_spec (U : StandardOpenCover) :
    (⨆ i, U i) = (⊤ : TopologicalSpace.Opens (PrimeSpectrum R)) ∧
      (Ideal.span (Set.range U.generator) : Ideal R) = ⊤ := by
  exact ⟨U.iSup_eq_top, U.span_eq_top⟩

end PrimeSpectrum

end
