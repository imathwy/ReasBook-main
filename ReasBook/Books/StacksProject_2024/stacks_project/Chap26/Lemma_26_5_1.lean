import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Away.Basic
import StacksProject_2024.stacks_project.Chap10.Definition_10_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum
open scoped PrimeSpectrum

noncomputable section

universe u v

section

variable {R : Type u} [CommRing R]
variable (f g : R)

-- Mathlib owner API used here: `basicOpen_le_basicOpen_iff_algebraMap_isUnit`, `IsLocalization.lift`,
-- `LocalizedModule.lift`, and `iSup_basicOpen_eq_top_iff`.

/- Lemma 26.5.1 (1): if `D(g) ⊆ D(f)`, then the image of `f` is invertible in `R_g`. This is the
source-facing forward direction of the canonical mathlib theorem
`basicOpen_le_basicOpen_iff_algebraMap_isUnit`. -/
@[stacks 01HS]
theorem algebraMap_isUnit_of_basicOpen_le
    (h : D(g) ≤ D(f)) :
    IsUnit (algebraMap R (Localization.Away g) f) :=
  basicOpen_le_basicOpen_iff_algebraMap_isUnit.mp h

/-- Lemma 26.5.1 (2): if `D(g) ⊆ D(f)`, then some positive power of `g` is a multiple of `f`. -/
@[stacks 01HS]
theorem exists_pow_eq_mul_of_basicOpen_le
    (h : D(g) ≤ D(f)) :
    ∃ e : ℕ, 0 < e ∧ ∃ a : R, g ^ e = a * f := by
  sorry

/-- Companion to Lemma 26.5.1 (2): inclusion of basic opens is equivalent to a positive power of
`g` becoming a multiple of `f`. -/
theorem basicOpen_le_basicOpen_iff_exists_pow_eq_mul :
    D(g) ≤ D(f) ↔ ∃ e : ℕ, 0 < e ∧ ∃ a : R, g ^ e = a * f := by
  sorry

/-- Lemma 26.5.1 (3): if `D(g) ⊆ D(f)`, then there is a canonical ring map `R_f → R_g`. -/
@[stacks 01HS]
noncomputable abbrev awayToAwayRingHom
    (h : D(g) ≤ D(f)) :
    Localization.Away f →+* Localization.Away g :=
  IsLocalization.Away.lift f
    (algebraMap_isUnit_of_basicOpen_le f g h)

/-- The canonical map `R_f → R_g` agrees with the ambient localization maps on elements of `R`. -/
@[simp] theorem awayToAwayRingHom_algebraMap
    (h : D(g) ≤ D(f)) (r : R) :
    awayToAwayRingHom f g h (algebraMap R (Localization.Away f) r) =
      algebraMap R (Localization.Away g) r := by
  sorry

section ModuleMap

variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- Helper for Lemma 26.5.1: if `D(g) ≤ D(f)`, then every power of `f` acts invertibly on
`M_g`. -/
private theorem moduleEnd_isUnit_of_basicOpen_le
    (h : D(g) ≤ D(f)) (x : Submonoid.powers f) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule.Away g M)) x) := by
  sorry

/-- Lemma 26.5.1 (4): if `D(g) ⊆ D(f)`, then there is a canonical comparison map `M_f → M_g`.
Mathlib's clean owner for this comparison is the underlying `R`-linear map; by
`LinearMap.extendScalarsOfIsLocalizationEquiv`, this is canonically equivalent to the source's
`R_f`-linear map. -/
@[stacks 01HS]
noncomputable abbrev awayToAwayModuleMap
    (h : D(g) ≤ D(f)) :
    LocalizedModule.Away f M →ₗ[R] LocalizedModule.Away g M :=
  LocalizedModule.lift (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M)
    (moduleEnd_isUnit_of_basicOpen_le f g h)

/-- The canonical map `M_f → M_g` agrees with the localization maps on elements of `M`. -/
@[simp] theorem awayToAwayModuleMap_mkLinearMap
    (h : D(g) ≤ D(f)) (m : M) :
    awayToAwayModuleMap f g h
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M m) =
      LocalizedModule.mkLinearMap (Submonoid.powers g) M m := by
  sorry

end ModuleMap

/-- Lemma 26.5.1 (5): any open cover of `D(f)` admits a finite refinement by standard opens
contained in members of the original cover. The refinement is exposed as a genuine finite family
of generators rather than a `Finset`-encoded subtype family. -/
@[stacks 01HS]
theorem basicOpen_has_finite_refinement_of_open_cover
    {ι : Type v} (U : ι → TopologicalSpace.Opens (PrimeSpectrum R))
    (hcover : D(f) ≤ ⨆ i, U i) :
    ∃ (σ : Type v) (_ : Finite σ) (g' : σ → R),
      D(f) = ⨆ i, D(g' i) ∧
        ∀ i, ∃ j, D(g' i) ≤ U j := by
  sorry

/-- Lemma 26.5.1 (6): for a finite family `gᵢ`, the inclusion
`D(f) ⊆ ⋃ᵢ D(gᵢ)` is equivalent to the images of the `gᵢ` generating the unit ideal in `R_f`. -/
@[stacks 01HS]
theorem basicOpen_le_iSup_basicOpen_iff_span_eq_top
    {ι : Type v} [Finite ι] (g' : ι → R) :
    D(f) ≤ ⨆ i, D(g' i) ↔
      Ideal.span (Set.range fun i : ι ↦ algebraMap R (Localization.Away f) (g' i)) = ⊤ := by
  sorry

end
