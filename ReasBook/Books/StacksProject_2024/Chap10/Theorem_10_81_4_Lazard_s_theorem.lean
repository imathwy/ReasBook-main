import Mathlib
import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import StacksProject_2024.Chap10.Lemma_10_11_4
import StacksProject_2024.Chap10.Lemma_10_39_3
import StacksProject_2024.Chap10.Lemma_10_81_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.ObjectProperty
open CategoryTheory Limits

universe u

section

variable {R : Type u} [CommRing R]
variable (M : ModuleCat.{u} R)

/-- Helper for Theorem 10.81.4 (Lazard's theorem): the object property of finite free
`R`-modules. -/
abbrev finite_free_property : ObjectProperty (ModuleCat.{u} R) :=
  fun N ↦ Module.Free R N ∧ Module.Finite R N

/-- Helper for Theorem 10.81.4 (Lazard's theorem): the full subcategory of finite free
`R`-modules. -/
abbrev finite_free_subcategory :=
  (finite_free_property (R := R) : ObjectProperty (ModuleCat.{u} R)).FullSubcategory

/-- Helper for Theorem 10.81.4 (Lazard's theorem): the standard rank-`k` finite free module. -/
noncomputable abbrev finite_free_rank (k : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (Fin k →₀ R)

/-- Helper for Theorem 10.81.4 (Lazard's theorem): a finite free `R`-module is finitely
presentable as an object of `ModuleCat R`. -/
lemma finite_free_isFinitelyPresentable_moduleCat
    {N : ModuleCat.{u} R} (hN : finite_free_property (R := R) N) :
    IsFinitelyPresentable.{u} N := by
  letI : Module.Free R N := hN.1
  letI : Module.Finite R N := hN.2
  letI : Module.Projective R N := Module.Projective.of_free
  letI : Module.FinitePresentation R N := Module.finitePresentation_of_projective R N
  -- Finite free modules are finitely presented algebraically, and Lemma `10.11.4` transports
  -- that statement to the categorical owner `IsFinitelyPresentable`.
  exact
    (module_finitePresentation_iff_isFinitelyPresentable (R := R) (M := N)).mp inferInstance

/-- Helper for Theorem 10.81.4 (Lazard's theorem): the full subcategory of finite free modules is
essentially small because it embeds fully faithfully into `FGModuleCat R`. -/
lemma finite_free_fullSubcategory_essentiallySmall :
    EssentiallySmall.{u} (finite_free_subcategory (R := R)) := by
  -- Route correction: keep the source-faithful finite-free indexing category, but realize its
  -- smallness through the canonical fully faithful inclusion into `FGModuleCat.{u} R`.
  let F :
      finite_free_subcategory (R := R) ⥤ FGModuleCat.{u} R :=
    ObjectProperty.ιOfLE (fun N hN ↦ hN.2)
  -- The ambient category of finitely generated modules is essentially small in the same universe.
  letI : EssentiallySmall.{u} (FGModuleCat.{u} R) := by infer_instance
  exact essentiallySmall_of_fully_faithful F

/-- Helper for Theorem 10.81.4 (Lazard's theorem): finite free arrows into a flat module form a
filtered category. -/
lemma finite_free_costructuredArrow_isFiltered
    (hM : Module.Flat R M) :
    IsFiltered (CostructuredArrow
      ((finite_free_property (R := R) : ObjectProperty (ModuleCat.{u} R)).ι) M) := by
  -- Route correction: the same-universe smallness bridge is now closed, so the remaining
  -- source-faithful work is purely the explicit filteredness packaging.
  -- TODO: build the zero stage, the two-object upper bound, and the equalizer stage from
  -- `Module.Flat.exists_factorization_of_comp_eq_zero_of_free`, keeping the coercions inside
  -- `ObjectProperty.homMk` and `CostructuredArrow.homMk` aligned.
  let _ := hM
  sorry

/-- Helper for Theorem 10.81.4 (Lazard's theorem): a filtered colimit of finite free modules is
flat. -/
lemma flat_of_ind_finite_free
    (hM : ind (finite_free_property (R := R)) M) :
    Module.Flat R M := by
  -- TODO: map the small filtered presentation into the universe expected by
  -- `flat_of_isColimit_filtered_system` and transport flatness back along the canonical
  -- universe-lift equivalence on `ModuleCat`.
  sorry

/-- Helper for Theorem 10.81.4 (Lazard's theorem): a flat module lies in the filtered-colimit
closure of the finite free modules. -/
lemma ind_finite_free_of_flat
    (hM : Module.Flat R M) :
    ind (finite_free_property (R := R)) M := by
  -- TODO: after `finite_free_costructuredArrow_isFiltered` is in place, the remaining step is to
  -- package the tautological cocone and prove it is colimiting via
  -- `Types.FilteredColimit.isColimitOf'` together with `forget_reflectsFilteredColimits`.
  sorry

-- Proof sketch: if `M` is the colimit of a directed system of finite free modules, then each stage
-- is flat and filtered colimits of modules preserve exactness, so `M` is flat. Conversely, the
-- finite free arrows into a flat module form a filtered dense diagram by Lemma `10.81.2`.
/-- Theorem 10.81.4 (Lazard's theorem): an `R`-module `M` is flat if and only if it is isomorphic
to the colimit of a directed system of finite free `R`-modules. In the canonical owner
formulation, this says that `M`, viewed as an object of `ModuleCat R`, belongs to the
filtered-colimit closure of the finite free `R`-modules. -/
theorem flat_iff_isomorphic_colimit_of_directed_system_of_finite_free :
    Module.Flat R M ↔
      ind (finite_free_property (R := R)) M := by
  constructor
  · -- For a flat module, finite free arrows into `M` form a filtered dense diagram.
    exact ind_finite_free_of_flat (R := R) (M := M)
  · -- For a filtered colimit of finite free stages, apply stability of flatness under colimits.
    exact flat_of_ind_finite_free (R := R) (M := M)

end
