import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksProject_2024.stacks_project.Chap05.Lemma_5_22_4
import StacksProject_2024.stacks_project.Chap06.Remark_6_7_2
import StacksProject_2024.stacks_project.Chap12.Lemma_12_7_2
import StacksProject_2024.stacks_project.Chap18.Lemma_18_3_1
import StacksProject_2024.stacks_project.Chap20.OpensInstances
import StacksProject_2024.stacks_project.Chap20.«20_2_0_3»
import StacksProject_2024.stacks_project.Chap21.SiteAbelianDerived

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Presheaf Opposite

attribute [local instance] HasDerivedCategory.standard

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

/-
Domain-style sampling for Lemma 20.22.3:
- primary domain: higher sheaf cohomology vanishing on profinite spaces via clopen refinements and
  exactness of global sections;
- same-domain owner declarations inspected:
  `Profinite`,
  `siteAbelianSectionsFunctor`,
  `TopologicalSpace.IsOpenCover.exists_finite_nonempty_disjoint_clopen_cover`,
  `CategoryTheory.Sheaf.isLocallySurjective_iff_epi'`;
- best owner abstraction: the public owner is the bundled profinite space `Profinite`, and the
  companion exactness statement should use the canonical sections owner
  `siteAbelianSectionsFunctor JX (⊤ : Opens X)`; the proof should stay on the
  source route "global sections are exact" rather than switching to a later spectral-space
  induction statement.
-/

variable {X : Profinite.{u}}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

local notation "JX" => Opens.grothendieckTopology X

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
/-- Helper for Lemma 20.22.3: every clopen subset is contained in the top open. -/
private theorem clopen_toOpens_le_top (W : Clopens X) :
    W.toOpens ≤ (⊤ : Opens X) := by
  intro x hx
  simp

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
/-- Helper for Lemma 20.22.3: an open cover of `⊤` yields a `CoversTop` family in the site of
opens. -/
private theorem open_cover_coversTop
    {ι : Type*} (U : ι → Opens X) (hU : TopologicalSpace.IsOpenCover U) :
    (Opens.grothendieckTopology X).CoversTop U := by
  -- Convert pointwise topological coverage into the site-level `CoversTop` predicate.
  intro W x hx
  obtain ⟨i, hxi⟩ := hU.exists_mem x
  refine ⟨W ⊓ U i, homOfLE inf_le_left, ?_, ⟨hx, hxi⟩⟩
  exact ⟨i, ⟨homOfLE inf_le_right⟩⟩

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
/-- Helper for Lemma 20.22.3: every open cover of a profinite space admits a finite pairwise
disjoint clopen refinement. This isolates the geometric input from Lemma `5.22.4`. -/
private theorem exists_finite_disjoint_clopen_refinement
    {ι : Type*} (U : ι → Opens X) (hU : TopologicalSpace.IsOpenCover U) :
    ∃ (n : ℕ) (W : Fin n → Clopens X),
      (∀ j, W j ≠ ⊥ ∧ ∃ i, ((W j : Clopens X) : Set X) ⊆ (U i : Set X)) ∧
        Set.univ ⊆ ⋃ j, ((W j : Clopens X) : Set X) ∧
          _root_.Pairwise (fun i j ↦ Disjoint (W i) (W j)) := by
  -- Follow the source route exactly: refine by a finite pairwise disjoint clopen cover.
  exact hU.exists_finite_nonempty_disjoint_clopen_cover

omit [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
/-- Helper for Lemma 20.22.3: an epimorphism of abelian sheaves is locally surjective on the
underlying site. This is the categorical bridge needed before applying the profinite refinement.
-/
private theorem epi_isLocallySurjective
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (π : F ⟶ G) [Epi π] :
    Sheaf.IsLocallySurjective π := by
  -- Convert the categorical epi hypothesis to the local lifting predicate on sheaves.
  exact (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} π).2 inferInstance

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
/-- Helper for Lemma 20.22.3: on a pairwise disjoint clopen family, the overlap of two distinct
pieces is the empty open, so the corresponding underlying restrictions automatically agree. -/
private theorem underlying_restrictions_agree_on_disjoint_overlap
    (F : Sheaf JX AddCommGrpCat.{u}) {n : ℕ} (W : Fin n → Clopens X)
    (hW : _root_.Pairwise (fun i j ↦ Disjoint (W i) (W j)))
    (s : ∀ i, F.1.obj (op (W i).toOpens)) {i j : Fin n} (hij : i ≠ j) :
    ((sheafForget JX).obj F).1.map (homOfLE inf_le_left).op (s i) =
      ((sheafForget JX).obj F).1.map (homOfLE inf_le_right).op (s j) := by
  let F₀ : Sheaf JX (Type u) := (sheafForget JX).obj F
  -- Proof comment: pairwise disjointness identifies the overlap open with `⊥`, and sections over
  -- `⊥` of a sheaf of types are unique.
  have hbot : (W i).toOpens ⊓ (W j).toOpens = (⊥ : Opens X) := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ (((W i) ⊓ (W j) : Clopens X) : Set X) := hx
      simpa [(hW hij).eq_bot] using hx'
    · intro hx
      exact False.elim (by simpa using hx)
  haveI :
      Subsingleton (((sheafForget JX).obj F).1.obj
        (op ((W i).toOpens ⊓ (W j).toOpens))) := by
    rw [hbot]
    infer_instance
  exact Subsingleton.elim _ _

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
/-- Helper for Lemma 20.22.3: a family of sections on a pairwise disjoint clopen cover is a
compatible family for the underlying `Type`-valued sheaf. -/
private theorem underlying_pairwise_disjoint_sections_isCompatible
    (F : Sheaf JX AddCommGrpCat.{u}) {n : ℕ} (W : Fin n → Clopens X)
    (hW : _root_.Pairwise (fun i j ↦ Disjoint (W i) (W j)))
    (s : FamilyOfElementsOnObjects ((sheafForget JX).obj F).1 (fun i ↦ (W i).toOpens)) :
    s.IsCompatible := by
  let F₀ : Sheaf JX (Type u) := (sheafForget JX).obj F
  intro Z i j f g
  by_cases hij : i = j
  · subst hij
    rw [Subsingleton.elim f g]
  · let hfg : Z ⟶ (W i).toOpens ⊓ (W j).toOpens :=
      homOfLE <| le_inf (leOfHom f) (leOfHom g)
    have hf : f = hfg ≫ homOfLE inf_le_left := Subsingleton.elim _ _
    have hg : g = hfg ≫ homOfLE inf_le_right := Subsingleton.elim _ _
    -- Proof comment: reduce compatibility on an arbitrary test open to the explicit overlap
    -- equality on `W i ∩ W j`, then pull that equality back along the common factorization.
    calc
      F₀.1.map f.op (s i)
          = F₀.1.map hfg.op
              (F₀.1.map (homOfLE inf_le_left).op (s i)) := by
                rw [hf, op_comp, FunctorToTypes.map_comp_apply]
                rfl
      _ = F₀.1.map hfg.op
            (F₀.1.map (homOfLE inf_le_right).op (s j)) := by
              exact congrArg (F₀.1.map hfg.op)
                (underlying_restrictions_agree_on_disjoint_overlap F W hW s hij)
      _ = F₀.1.map g.op (s j) := by
            rw [hg, op_comp, FunctorToTypes.map_comp_apply]
            rfl

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
/-- Helper for Lemma 20.22.3: for a disjoint clopen refinement of the local-lift cover of a
global section, the restricted local lifts should glue to a top section. -/
private theorem exists_top_section_of_pairwise_disjoint_cover
    (F : Sheaf JX AddCommGrpCat.{u}) {n : ℕ} (W : Fin n → Clopens X)
    (hcover : Set.univ ⊆ ⋃ i, ((W i : Clopens X) : Set X))
    (hW : _root_.Pairwise (fun i j ↦ Disjoint (W i) (W j)))
    (s : ∀ i, F.1.obj (op (W i).toOpens)) :
    ∃ t : F.1.obj (op (⊤ : Opens X)),
      ∀ i, F.1.map (homOfLE (clopen_toOpens_le_top (W i))).op t = s i := by
  let F₀ : Sheaf JX (Type u) := (sheafForget JX).obj F
  let family :
      FamilyOfElementsOnObjects F₀.1 (fun i ↦ (W i).toOpens) := s
  have hOpenCover : TopologicalSpace.IsOpenCover (fun i ↦ (W i).toOpens) := by
    -- Proof comment: the clopen family covers `X` exactly because its underlying sets cover
    -- `Set.univ`.
    rw [TopologicalSpace.IsOpenCover]
    ext x
    constructor
    · intro hx
      simp
    · intro hx
      have hx' : x ∈ (Set.univ : Set X) := by simp
      simpa using hcover hx'
  let hTopCover := open_cover_coversTop (fun i ↦ (W i).toOpens) hOpenCover
  have hfamily : family.IsCompatible :=
    underlying_pairwise_disjoint_sections_isCompatible F W hW s
  let σ := hfamily.section_ hTopCover F₀.2
  refine ⟨σ.1 (op (⊤ : Opens X)), ?_⟩
  intro i
  -- Proof comment: evaluate the glued global section at the terminal object `⊤`, then recover the
  -- prescribed value on `W i` by naturality of that section and `section_apply`.
  let topToClopen : op (⊤ : Opens X) ⟶ op ((W i).toOpens) :=
    (homOfLE (clopen_toOpens_le_top (W i))).op
  have hσ :
      F₀.1.map topToClopen (σ.1 (op (⊤ : Opens X))) =
        σ.1 (op ((W i).toOpens)) := by
    simpa [topToClopen] using σ.2 topToClopen
  have hσvalue :
      σ.1 (op ((W i).toOpens)) = s i := by
    simpa [family, σ] using hfamily.section_apply hTopCover F₀.2 i
  have hσtop :
      F.1.map (homOfLE (clopen_toOpens_le_top (W i))).op
          (σ.1 (op (⊤ : Opens X))) =
        σ.1 (op ((W i).toOpens)) := by
    exact hσ
  exact hσtop.trans hσvalue

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
/-- Helper for Lemma 20.22.3: two global sections of an abelian sheaf agree once their
restrictions agree on every member of a finite clopen cover of `X`. -/
private theorem top_section_eq_of_restrict_eq_on_finite_clopen_cover
    (G : Sheaf JX AddCommGrpCat.{u}) {n : ℕ} (W : Fin n → Clopens X)
    (hcover : Set.univ ⊆ ⋃ i, ((W i : Clopens X) : Set X))
    (a b : G.1.obj (op (⊤ : Opens X)))
    (h : ∀ i,
      G.1.map (homOfLE (clopen_toOpens_le_top (W i))).op a =
        G.1.map (homOfLE (clopen_toOpens_le_top (W i))).op b) :
    a = b := by
  let G₀ : Sheaf JX (Type u) := (sheafForget JX).obj G
  have hOpenCover : TopologicalSpace.IsOpenCover (fun i ↦ (W i).toOpens) := by
    -- Proof comment: the finite clopen family covers `X` exactly because its underlying sets
    -- cover `Set.univ`.
    rw [TopologicalSpace.IsOpenCover]
    ext x
    constructor
    · intro hx
      simp
    · intro hx
      have hx' : x ∈ (Set.univ : Set X) := by simp
      simpa using hcover hx'
  let hTopCover := open_cover_coversTop (fun i ↦ (W i).toOpens) hOpenCover
  -- Proof comment: pass to the underlying `Type`-valued sheaf, where `sections_ext` detects
  -- equality of sections on `⊤` from equality on a covering family.
  have hToTop : ∀ V : (Opens X)ᵒᵖ, V.unop ≤ (⊤ : Opens X) := by
    intro V x hx
    simp
  let sectionFun :=
    fun (s : G₀.1.obj (op (⊤ : Opens X))) (V : (Opens X)ᵒᵖ) ↦
      G₀.1.map (homOfLE (hToTop V)).op s
  have hSectionFun : ∀ s : G₀.1.obj (op (⊤ : Opens X)), sectionFun s ∈ G₀.obj.sections := by
    intro s j j' f
    simp only [sectionFun]
    have hcomp : (homOfLE (hToTop j)).op ≫ f = (homOfLE (hToTop j')).op := Subsingleton.elim _ _
    rw [← FunctorToTypes.map_comp_apply, hcomp]
  let a₀ : G₀.obj.sections := ⟨sectionFun a, hSectionFun a⟩
  let b₀ : G₀.obj.sections := ⟨sectionFun b, hSectionFun b⟩
  have hab : a₀ = b₀ := by
    apply hTopCover.sections_ext G₀
    intro i
    simpa [a₀, b₀, sectionFun, hToTop] using h i
  have htop := congrArg (fun z ↦ z.1 (op (⊤ : Opens X))) hab
  have htopId : (homOfLE (hToTop (op (⊤ : Opens X)))).op = 𝟙 (op (⊤ : Opens X)) :=
    Subsingleton.elim _ _
  simpa [a₀, b₀, sectionFun, htopId] using htop

/-
The local surjectivity-on-epis argument uses only sheafification and the exactness of sections,
not the ambient `HasExt` package.
-/
omit [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
/-- Helper for Lemma 20.22.3: an epimorphism of abelian sheaves on a profinite space is
surjective on global sections. -/
private theorem surjective_top_open_sections_map_of_epi_of_profinite
    {F G : Sheaf JX AddCommGrpCat.{u}} (π : F ⟶ G) [Epi π] :
    Function.Surjective ((siteAbelianSectionsFunctor JX (⊤ : Opens X)).map π) := by
  classical
  -- Route correction: instead of ad hoc pointwise transport, use the owner image-sieve cover of
  -- `t`, refine it by Lemma 5.22.4, glue the restricted local lifts, and then apply coverwise
  -- extensionality on the refined clopen cover.
  let hπ : Sheaf.IsLocallySurjective π := epi_isLocallySurjective π
  change Function.Surjective (π.hom.app (op (⊤ : Opens X)))
  intro t
  change Presheaf.IsLocallySurjective JX π.hom at hπ
  letI : Presheaf.IsLocallySurjective JX π.hom := hπ
  let T : (Opens.grothendieckTopology X).Cover (⊤ : Opens X) :=
    ⟨Presheaf.imageSieve π.hom t, Presheaf.imageSieve_mem JX π.hom t⟩
  let U : T.Arrow → Opens X := fun I ↦ I.Y
  have hU : TopologicalSpace.IsOpenCover U := by
    -- Proof comment: the arrows in the image-sieve cover of `t` cover the top open by
    -- definition of `JX.Cover`.
    rw [TopologicalSpace.IsOpenCover]
    ext x
    constructor
    · intro hx
      simp
    · intro hx
      rcases T.condition x (by simpa using hx) with ⟨V, i, hi, hxV⟩
      let I : T.Arrow := ⟨V, i, hi⟩
      exact (le_iSup U I) hxV
  obtain ⟨n, W, hW, hcoverW, hWdisj⟩ :=
    exists_finite_disjoint_clopen_refinement U hU
  have hrefine : ∀ j, ∃ I : T.Arrow, ((W j : Clopens X) : Set X) ⊆ (U I : Set X) := by
    intro j
    exact (hW j).2
  choose coverArrow hsubset using hrefine
  have hlocal :
      ∀ j, ∃ s : F.1.obj (op (coverArrow j).Y),
        π.hom.app (op (coverArrow j).Y) s = G.1.map (coverArrow j).f.op t := by
    intro j
    have hmem : (Presheaf.imageSieve π.hom t).arrows (coverArrow j).f := (coverArrow j).hf
    rw [Presheaf.imageSieve_apply] at hmem
    simpa using hmem
  choose localLift hlocalLift using hlocal
  let refineIncl : ∀ j, (W j).toOpens ⟶ (coverArrow j).Y := fun j ↦
    homOfLE (hsubset j)
  let refinedLift : ∀ j, F.1.obj (op (W j).toOpens) := fun j ↦
    F.1.map (refineIncl j).op (localLift j)
  obtain ⟨u, hu⟩ :=
    exists_top_section_of_pairwise_disjoint_cover F W hcoverW hWdisj refinedLift
  refine ⟨u, ?_⟩
  apply top_section_eq_of_restrict_eq_on_finite_clopen_cover G W hcoverW
  intro j
  let topIncl : (W j).toOpens ⟶ (⊤ : Opens X) :=
    homOfLE (clopen_toOpens_le_top (W j))
  let refIncl : (W j).toOpens ⟶ (coverArrow j).Y := refineIncl j
  -- Proof comment: on each refined clopen piece, naturality identifies the image of the glued
  -- section with the restriction of the chosen local lift, which was selected from the image sieve
  -- of `t`.
  calc
    G.1.map topIncl.op (π.hom.app (op (⊤ : Opens X)) u)
        = π.hom.app (op (W j).toOpens) (F.1.map topIncl.op u) := by
            simpa using (ConcreteCategory.congr_hom (π.hom.naturality topIncl.op) u).symm
    _ = π.hom.app (op (W j).toOpens) (refinedLift j) := by rw [hu j]
    _ = G.1.map refIncl.op (π.hom.app (op (coverArrow j).Y) (localLift j)) := by
          simpa [refinedLift, refIncl] using
            ConcreteCategory.congr_hom (π.hom.naturality refIncl.op) (localLift j)
    _ = G.1.map refIncl.op (G.1.map (coverArrow j).f.op t) := by rw [hlocalLift j]
    _ = G.1.map topIncl.op t := by
          have hcomp : refIncl ≫ (coverArrow j).f = topIncl := Subsingleton.elim _ _
          have hcompOp : (coverArrow j).f.op ≫ refIncl.op = topIncl.op := by
            simpa using congrArg Quiver.Hom.op hcomp
          simpa [Functor.map_comp] using congrArg (fun f ↦ G.1.map f t) hcompOp

omit [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
/-- Helper for Lemma 20.22.3: exactness of global sections on a profinite space follows from the
surjectivity-on-epis step above and formal left exactness of evaluation. -/
theorem profinite_sectionsFunctor_exact :
    exactFunctor _ _ (siteAbelianSectionsFunctor JX (⊤ : Opens X)) := by
  have hLeft :
      leftExactFunctor (Sheaf JX AddCommGrpCat.{u}) AddCommGrpCat.{u}
        (siteAbelianSectionsFunctor JX (⊤ : Opens X)) := by
    simpa [leftExactFunctor_iff] using
      (inferInstance :
        PreservesFiniteLimits (siteAbelianSectionsFunctor JX (⊤ : Opens X)))
  exact
    (CategoryTheory.functor_exact_iff_maps_shortExact_to_exact_mono_epi
      (siteAbelianSectionsFunctor JX (⊤ : Opens X))).2 fun S hS ↦ by
        have hLeftMap :
            (ComposableArrows.mk₂
              ((siteAbelianSectionsFunctor JX (⊤ : Opens X)).map S.f)
              ((siteAbelianSectionsFunctor JX (⊤ : Opens X)).map S.g)).Exact ∧
              Mono ((siteAbelianSectionsFunctor JX (⊤ : Opens X)).map S.f) :=
          (CategoryTheory.functor_leftExact_iff_maps_shortExact_to_exact_mono
            (siteAbelianSectionsFunctor JX (⊤ : Opens X))).1 hLeft S hS
        have hsurj :
            Function.Surjective ((siteAbelianSectionsFunctor JX (⊤ : Opens X)).map S.g) := by
          letI : Epi S.g := hS.epi_g
          exact surjective_top_open_sections_map_of_epi_of_profinite S.g
        have hEpi : Epi ((siteAbelianSectionsFunctor JX (⊤ : Opens X)).map S.g) :=
          (AddCommGrpCat.epi_iff_surjective _).2 hsurj
        exact ⟨hLeftMap.1, hLeftMap.2, hEpi⟩

section

variable {Y : Profinite.{u}}
variable [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]

local notation "JY" => Opens.grothendieckTopology Y

/-- Helper for Lemma 20.22.3: exactness of `Γ(X,-)` forces positive sheaf cohomology on `⊤` to
vanish. -/
private theorem higherCohomology_isZero_of_exact
    (F : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) (n : ℕ)
    (hExact : exactFunctor _ _ (siteAbelianSectionsFunctor JY (⊤ : Opens Y))) :
    IsZero (F.H' (n + 1) (⊤ : Opens Y)) := by
  let Γ : Sheaf JY AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
    siteAbelianSectionsFunctor JY (⊤ : Opens Y)
  let I : InjectiveResolution F := injectiveResolution F
  let K := (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  letI : Γ.Additive := by
    simpa [Γ] using
      (siteAbelianSectionsFunctor_additive JY (⊤ : Opens Y))
  letI : PreservesFiniteLimits Γ := (exactFunctor_iff Γ).1 hExact |>.1
  letI : PreservesFiniteColimits Γ := (exactFunctor_iff Γ).1 hExact |>.2
  have hScExact : (I.cocomplex.sc (n + 1)).Exact := by
    exact (HomologicalComplex.exactAt_iff I.cocomplex (n + 1)).1 (I.cocomplex_exactAt_succ n)
  have hKExactAt : K.ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff]
    simpa [K, Γ, HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      Functor.mapShortComplex_obj, Functor.mapHomologicalComplex_obj_X,
      Functor.mapHomologicalComplex_obj_d] using ShortComplex.Exact.map hScExact Γ
  have hHomology : IsZero (K.homology (n + 1)) :=
    HomologicalComplex.ExactAt.isZero_homology hKExactAt
  rcases
      cohomologyAtObject_isomorphic_to_homology_sections_of_injectiveResolution JY I (n + 1) with
    ⟨e⟩
  refine e.isZero_iff.2 ?_
  simpa [K, Γ] using hHomology

end

/-- Lemma 20.22.3: if `X` is a profinite topological space, then every abelian sheaf on `X` has
vanishing higher global cohomology. -/
@[stacks 0A3F]
theorem isZero_higherCohomology_of_profinite
    (F : Sheaf JX AddCommGrpCat.{u}) {q : ℕ} (hq : 0 < q) :
    IsZero (F.H' q (⊤ : Opens X)) := by
  -- Route correction: finish the textbook argument by making `Γ(X, -)` exact and then invoking
  -- the canonical injective-resolution computation of `H'` by the homology of the sections
  -- complex.
  have hExact :
      exactFunctor _ _ (siteAbelianSectionsFunctor JX (⊤ : Opens X)) :=
    profinite_sectionsFunctor_exact
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hq
  simpa [Nat.zero_add] using higherCohomology_isZero_of_exact F n hExact

end Sheaf
end CategoryTheory
