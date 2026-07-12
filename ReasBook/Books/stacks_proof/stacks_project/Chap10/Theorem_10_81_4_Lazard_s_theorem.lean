import Mathlib
import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import StacksProject_2024.Chap10.Lemma_10_11_3
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

/-- Helper for Chap10 Theorem 10 81 4 Lazard s theorem: the object property of finite free
`R`-modules. -/
abbrev finite_free_property : ObjectProperty (ModuleCat.{u} R) :=
  fun N ↦ Module.Free R N ∧ Module.Finite R N

/-- Helper for Chap10 Theorem 10 81 4 Lazard s theorem: the full subcategory of finite free
`R`-modules. -/
abbrev finite_free_subcategory :=
  (finite_free_property (R := R) : ObjectProperty (ModuleCat.{u} R)).FullSubcategory

/-- Helper for Chap10 Theorem 10 81 4 Lazard s theorem: the standard rank-`k` finite free module. -/
noncomputable abbrev finite_free_rank (k : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (Fin k →₀ R)

/-- Helper for Chap10 Theorem 10 81 4 Lazard s theorem: a finite free `R`-module is finitely
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

/-- Helper for Chap10 Theorem 10 81 4 Lazard s theorem: categorical finite presentability of a
`ModuleCat R` object gives the algebraic finite-presentation instance on its underlying module. -/
lemma finitePresentation_of_isFinitelyPresentable_moduleCat
    {N : ModuleCat.{u} R} [IsFinitelyPresentable.{u} N] :
    Module.FinitePresentation R N := by
  -- Proof comment: Lemma `10.11.4` is stated for `ModuleCat.of R N`; `simpa` identifies that
  -- spelling with the bundled object `N`.
  have hN : IsFinitelyPresentable.{u} (ModuleCat.of R N) := by
    simpa using (inferInstance : IsFinitelyPresentable.{u} N)
  exact (module_finitePresentation_iff_isFinitelyPresentable (R := R) (M := N)).2 hN

/-- Helper for Chap10 Theorem 10 81 4 Lazard s theorem: every module admits a filtered colimit
presentation by finitely presentable objects of `ModuleCat R`. -/
lemma finitelyPresentable_colimitOfShape :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J),
      Nonempty
        ((CategoryTheory.ObjectProperty.isFinitelyPresentable.{u} (ModuleCat.{u} R)).ColimitOfShape
          J M) := by
  have hInd :
      ind.{u} (fun N : ModuleCat.{u} R ↦ Module.FinitePresentation R N) M := by
    simpa using
      (module_is_isomorphic_to_colimit_of_directed_system_of_finitelyPresented
        (R := R) (M := M))
  obtain ⟨J, hJ, hJf, pres, hpres⟩ := hInd
  refine ⟨J, hJ, hJf, ⟨?_⟩⟩
  -- Proof comment: convert the algebraic finite-presentation stages from Lemma `10.11.3`
  -- into the categorical object property used by `ObjectProperty.ColimitOfShape`.
  refine
    { toColimitPresentation := pres
      prop_diag_obj := ?_ }
  intro j
  have hj : IsFinitelyPresentable.{u} (ModuleCat.of R (pres.diag.obj j)) :=
    (module_finitePresentation_iff_isFinitelyPresentable (R := R) (M := pres.diag.obj j)).mp
      (hpres j)
  simpa using hj

/-- Helper for Chap10 Theorem 10 81 4 Lazard s theorem: a filtered presentation by finitely presentable
objects induces a final functor to the corresponding costructured-arrow category. -/
lemma finitelyPresentable_toCostructuredArrow_final
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (p : (CategoryTheory.ObjectProperty.isFinitelyPresentable.{u} (ModuleCat.{u} R)).ColimitOfShape
      J M) :
    p.toCostructuredArrow.Final := by
  letI : Fact Cardinal.aleph0.IsRegular := Cardinal.fact_isRegular_aleph0
  letI : IsCardinalFiltered J Cardinal.aleph0 :=
    (isCardinalFiltered_aleph0_iff J).2 inferInstance
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨fun f ↦ ?_, fun {f j} g₁ g₂ ↦ ?_⟩
  · obtain ⟨j, g, hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit p.isColimit f.hom
    exact ⟨j, ⟨CostructuredArrow.homMk (ObjectProperty.homMk g) hg⟩⟩
  · obtain ⟨k, a, h⟩ := IsCardinalPresentable.exists_eq_of_isColimit' Cardinal.aleph0
      p.isColimit
      g₁.left.hom g₂.left.hom ((CostructuredArrow.w g₁).trans (CostructuredArrow.w g₂).symm)
    -- Proof comment: finite presentability equalizes the two factorizations after moving to a
    -- later stage of the filtered diagram.
    refine ⟨k, a, ?_⟩
    cat_disch

/-- Helper for Chap10 Theorem 10 81 4 Lazard s theorem: finitely presentable arrows into `M` form a
filtered category. -/
lemma finitelyPresentable_costructuredArrow_isFiltered :
    IsFiltered (CostructuredArrow
      ((CategoryTheory.ObjectProperty.isFinitelyPresentable.{u} (ModuleCat.{u} R)).ι) M) := by
  obtain ⟨J, _, _, ⟨p⟩⟩ := finitelyPresentable_colimitOfShape (R := R) (M := M)
  letI : p.toCostructuredArrow.Final :=
    finitelyPresentable_toCostructuredArrow_final (R := R) (M := M) p
  exact IsFiltered.of_final p.toCostructuredArrow

/-- Helper for Chap10 Theorem 10 81 4 Lazard s theorem: the inclusion of finitely presentable modules is
dense at every module object. -/
lemma finitelyPresentable_isDenseAt :
    ((CategoryTheory.ObjectProperty.isFinitelyPresentable.{u} (ModuleCat.{u} R)).ι).isDenseAt M := by
  obtain ⟨J, _, _, ⟨p⟩⟩ := finitelyPresentable_colimitOfShape (R := R) (M := M)
  letI : p.toCostructuredArrow.Final :=
    finitelyPresentable_toCostructuredArrow_final (R := R) (M := M) p
  exact
    ⟨(Functor.Final.isColimitWhiskerEquiv (F := p.toCostructuredArrow) _).1
      (IsColimit.ofIsoColimit p.isColimit (Cocone.ext (Iso.refl _)))⟩

/-- Helper for Chap10 Theorem 10 81 4 Lazard s theorem: the full subcategory of finite free modules is
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

/-- Helper for Chap10 Theorem 10 81 4 Lazard s theorem: finite free arrows into a flat module form a
filtered category. -/
lemma finite_free_costructuredArrow_isFiltered
    (hM : Module.Flat R M) :
    IsFiltered (CostructuredArrow
      ((finite_free_property (R := R) : ObjectProperty (ModuleCat.{u} R)).ι) M) := by
  let Q : ObjectProperty (ModuleCat.{u} R) :=
    CategoryTheory.ObjectProperty.isFinitelyPresentable.{u} (ModuleCat.{u} R)
  let incl :
      finite_free_subcategory (R := R) ⥤ Q.FullSubcategory :=
    ObjectProperty.ιOfLE (fun N hN ↦ finite_free_isFinitelyPresentable_moduleCat (R := R) hN)
  let F := CostructuredArrow.pre incl Q.ι M
  letI : F.Full := by
    dsimp [F]
    infer_instance
  letI : F.Faithful := by
    dsimp [F]
    infer_instance
  letI : IsFiltered (CostructuredArrow Q.ι M) :=
    finitelyPresentable_costructuredArrow_isFiltered (R := R) (M := M)
  -- Proof comment: finite free arrows form a fully faithful subcategory of finitely presentable
  -- arrows, so it is enough to show every finitely presentable arrow into a flat module factors
  -- through some finite free arrow.
  have hExists :
      ∀ d : CostructuredArrow Q.ι M,
        ∃ c : CostructuredArrow (incl ⋙ Q.ι) M,
          Nonempty (d ⟶ F.obj c) := by
    intro d
    letI : IsFinitelyPresentable.{u} d.left.obj := d.left.2
    letI : Module.FinitePresentation R (Q.ι.obj d.left) :=
      finitePresentation_of_isFinitelyPresentable_moduleCat (R := R)
    obtain ⟨n, h, g, hg⟩ :=
      (flat_iff_factorization_through_finite_free_of_finitelyPresented
        (R := R) (M := M)).1 hM d.hom.hom
    let Y : (finite_free_property (R := R)).FullSubcategory :=
      FullSubcategory.mk (finite_free_rank (R := R) n) ⟨inferInstance, inferInstance⟩
    let c : CostructuredArrow (incl ⋙ Q.ι) M :=
      CostructuredArrow.mk (Y := Y) (ModuleCat.ofHom g)
    refine ⟨c, ?_⟩
    refine ⟨CostructuredArrow.homMk (ObjectProperty.homMk (ModuleCat.ofHom h)) ?_⟩
    -- Proof comment: the factorization from Lemma `10.81.2` is exactly the commutative triangle
    -- required for a morphism in the costructured-arrow category.
    change ModuleCat.ofHom h ≫ ModuleCat.ofHom g = d.hom
    apply ModuleCat.hom_ext
    ext x
    exact LinearMap.congr_fun hg.symm x
  simpa [F, incl, Q, finite_free_subcategory, finite_free_property] using
    IsFiltered.of_exists_of_isFiltered_of_fullyFaithful F hExists

/-- Helper for Chap10 Theorem 10 81 4 Lazard s theorem: a filtered colimit of finite free modules is
flat. -/
lemma flat_of_ind_finite_free
    (hM : ind.{u} (finite_free_property (R := R)) M) :
    Module.Flat R M := by
  obtain ⟨J, _, _, pres, hpres⟩ :=
    (show ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
        (pres : ColimitPresentation J M), ∀ j, finite_free_property (R := R) (pres.diag.obj j) from
      by simpa [CategoryTheory.ObjectProperty.ind] using hM)
  letI : ∀ j, Module.Flat R (pres.diag.obj j) := fun j ↦ by
    letI : Module.Free R (pres.diag.obj j) := (hpres j).1
    -- Proof comment: each finite free stage is flat because freeness implies flatness.
    exact Module.Flat.of_free
  -- Proof comment: once the `ind` witness is unpacked into a filtered colimit presentation,
  -- Lemma `10.39.3` applies directly to the stagewise flat diagram.
  simpa using
    flat_of_isColimit_filtered_system (R := R) (F := pres.diag) (c := pres.cocone)
      (hc := pres.isColimit)

/-- Helper for Chap10 Theorem 10 81 4 Lazard s theorem: a flat module lies in the filtered-colimit
closure of the finite free modules. -/
lemma ind_finite_free_of_flat
    (hM : Module.Flat R M) :
    ind.{u} (finite_free_property (R := R)) M := by
  let P : ObjectProperty (ModuleCat.{u} R) := finite_free_property (R := R)
  let Q : ObjectProperty (ModuleCat.{u} R) :=
    CategoryTheory.ObjectProperty.isFinitelyPresentable.{u} (ModuleCat.{u} R)
  have hP :
      P ≤ Q := by
    intro N hN
    exact finite_free_isFinitelyPresentable_moduleCat (R := R) hN
  let incl : P.FullSubcategory ⥤ Q.FullSubcategory := ObjectProperty.ιOfLE hP
  let F := CostructuredArrow.pre incl Q.ι M
  letI : F.Full := by
    dsimp [F]
    infer_instance
  letI : F.Faithful := by
    dsimp [F]
    infer_instance
  letI : IsFiltered (CostructuredArrow Q.ι M) :=
    finitelyPresentable_costructuredArrow_isFiltered (R := R) (M := M)
  have hExists :
      ∀ d : CostructuredArrow Q.ι M,
        ∃ c : CostructuredArrow (incl ⋙ Q.ι) M,
          Nonempty (d ⟶ F.obj c) := by
    intro d
    letI : IsFinitelyPresentable.{u} d.left.obj := d.left.2
    letI : Module.FinitePresentation R (Q.ι.obj d.left) :=
      finitePresentation_of_isFinitelyPresentable_moduleCat (R := R)
    obtain ⟨n, h, g, hg⟩ :=
      (flat_iff_factorization_through_finite_free_of_finitelyPresented
        (R := R) (M := M)).1 hM d.hom.hom
    let Y : P.FullSubcategory :=
      FullSubcategory.mk (finite_free_rank (R := R) n) ⟨inferInstance, inferInstance⟩
    let c : CostructuredArrow (incl ⋙ Q.ι) M :=
      CostructuredArrow.mk (Y := Y) (ModuleCat.ofHom g)
    refine ⟨c, ?_⟩
    refine ⟨CostructuredArrow.homMk (ObjectProperty.homMk (ModuleCat.ofHom h)) ?_⟩
    -- Proof comment: the factorization from Lemma `10.81.2` is exactly the commutative triangle
    -- required for a morphism in the costructured-arrow category.
    change ModuleCat.ofHom h ≫ ModuleCat.ofHom g = d.hom
    apply ModuleCat.hom_ext
    ext x
    exact LinearMap.congr_fun hg.symm x
  have hfinal : F.Final :=
    Functor.final_of_exists_of_isFiltered_of_fullyFaithful F hExists
  letI : F.Final := hfinal
  have hQdense : Q.ι.isDenseAt M := finitelyPresentable_isDenseAt (R := R) (M := M)
  have hPdense : P.ι.isDenseAt M := by
    simpa using Functor.IsDenseAt.of_final (F := Q.ι) (Y := M) incl hQdense
  have : EssentiallySmall.{u} (CostructuredArrow P.ι M) := by
    letI : EssentiallySmall.{u} (P.FullSubcategory) :=
      finite_free_fullSubcategory_essentiallySmall (R := R)
    infer_instance
  have : IsFiltered (CostructuredArrow P.ι M) := by
    simpa using IsFiltered.of_exists_of_isFiltered_of_fullyFaithful F hExists
  obtain ⟨hc⟩ : P.ι.isDenseAt M := hPdense
  exact CategoryTheory.ObjectProperty.of_essentiallySmall_index ⟨_, _, hc⟩ fun Y ↦ Y.left.2

-- Proof sketch: if `M` is the colimit of a directed system of finite free modules, then each stage
-- is flat and filtered colimits of modules preserve exactness, so `M` is flat. Conversely, the
-- finite free arrows into a flat module form a filtered dense diagram by Lemma `10.81.2`.
/-- Chap10 Theorem 10 81 4 (Lazard's theorem): an `R`-module `M` is flat if and only if it is isomorphic
to the colimit of a directed system of finite free `R`-modules. In the canonical owner
formulation, this says that `M`, viewed as an object of `ModuleCat R`, belongs to the
filtered-colimit closure of the finite free `R`-modules. -/
@[stacks 058G]
theorem flat_iff_isomorphic_colimit_of_directed_system_of_finite_free :
    Module.Flat R M ↔
      ind.{u} (finite_free_property (R := R)) M := by
  constructor
  · -- For a flat module, finite free arrows into `M` form a filtered dense diagram.
    exact ind_finite_free_of_flat (R := R) (M := M)
  · -- For a filtered colimit of finite free stages, apply stability of flatness under colimits.
    exact flat_of_ind_finite_free (R := R) (M := M)

end
