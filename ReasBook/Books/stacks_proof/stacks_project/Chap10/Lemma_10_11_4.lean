import Mathlib
import StacksProject_2024.Chap10.Lemma_10_11_1
import StacksProject_2024.Chap10.Lemma_10_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

section

variable (R : Type u) (M : Type (max u v)) [Ring R] [AddCommGroup M] [Module R M]

/-- Helper for Lemma 10.11.4: if `r : Q → P` admits a section `s`, then `ker r` is the range of
the projector `id - s ∘ r`, so it is finitely generated once `Q` is finite. -/
lemma ker_fg_of_split_surjection
    {P Q : Type (max u v)} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q]
    (s : P →ₗ[R] Q) (r : Q →ₗ[R] P) (hsr : r.comp s = LinearMap.id) :
    (LinearMap.ker r).FG := by
  let e : Q →ₗ[R] Q := LinearMap.id - s.comp r
  have hsr_apply (x : P) : r (s x) = x := by
    -- The section identity is used pointwise to simplify the projector calculation.
    simpa using LinearMap.congr_fun hsr x
  have hker_range : LinearMap.ker r = LinearMap.range e := by
    ext x
    constructor
    · intro hx
      refine ⟨x, ?_⟩
      -- Elements of the kernel are fixed by `id - s ∘ r`.
      change x - s (r x) = x
      rw [show r x = 0 from hx, map_zero, sub_zero]
    · rintro ⟨y, rfl⟩
      -- The projector lands in `ker r` because `r ∘ s = id`.
      change r (e y) = 0
      simp [e, hsr_apply]
  -- A range of a map out of a finite module is finitely generated.
  simpa [hker_range] using (Submodule.fg_range e)

/-- Helper for Lemma 10.11.4: a split surjection from a finitely presented stage descends finite
presentation to the target module. -/
lemma module_finitePresentation_of_split_surjection_from_finitelyPresented_stage
    {P Q : Type (max u v)} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [Module.FinitePresentation R Q]
    (s : P →ₗ[R] Q) (r : Q →ₗ[R] P) (hsr : r.comp s = LinearMap.id) :
    Module.FinitePresentation R P := by
  have hr_surj : Function.Surjective r := by
    -- The section gives explicit preimages under `r`.
    intro x
    refine ⟨s x, ?_⟩
    simpa using LinearMap.congr_fun hsr x
  have hker_fg : (LinearMap.ker r).FG :=
    ker_fg_of_split_surjection (R := R) s r hsr
  -- Descend finite presentation across the split surjection.
  exact Module.finitePresentation_of_surjective r hr_surj hker_fg

/-- Helper for Lemma 10.11.4: two maps out of a quotient module agree once their composites with
the quotient map agree. -/
lemma linearMap_eq_of_comp_mkQ_eq
    {n : ℕ} {K : Submodule R (Fin n → R)} {P : Type (max u v)}
    [AddCommGroup P] [Module R P]
    {f g : ((Fin n → R) ⧸ K) →ₗ[R] P}
    (h : f.comp (Submodule.mkQ K) = g.comp (Submodule.mkQ K)) :
    f = g := by
  -- The quotient map is surjective, so it is enough to compare both maps on representatives.
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective K q
  simpa using LinearMap.congr_fun h x

/-- Helper for Lemma 10.11.4: a linear map from a finite free module into a filtered colimit of
modules factors through one stage. -/
lemma linearMap_from_fin_factor_through_filtered_colimit_stage
    {J : Type (max u v)} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{max u v} R) [HasColimit F]
    (n : ℕ) (f : (Fin n → R) →ₗ[R] (colimit F : ModuleCat.{max u v} R)) :
    ∃ (j : J) (g : (Fin n → R) →ₗ[R] F.obj j), (colimit.ι F j).hom.comp g = f := by
  classical
  letI : PreservesColimit F (forget (ModuleCat.{max u v} R)) :=
    modulecat_forget_preserves_colimit_filtered (R := R) F
  let hc :
      IsColimit ((forget (ModuleCat.{max u v} R)).mapCocone (colimit.cocone F)) :=
    isColimitOfPreserves (forget (ModuleCat.{max u v} R)) (colimit.isColimit F)
  choose j x hx using fun i : Fin n =>
    Types.jointly_surjective_of_isColimit hc (f ((Pi.basisFun R (Fin n)) i))
  obtain ⟨k, ⟨u⟩⟩ : ∃ k : J, Nonempty (∀ i : Fin n, j i ⟶ k) := by
    -- Filteredness merges the finitely many chosen lifts of the basis vectors into one stage.
    have : ∃ k : J, ∀ i : Fin n, Nonempty (j i ⟶ k) := by
      simpa using IsFiltered.sup_objs_exists (Finset.univ.image j)
    simpa [← exists_true_iff_nonempty, Classical.skolem, -exists_const_iff] using this
  let g : (Fin n → R) →ₗ[R] F.obj k :=
    { toFun := fun z => ∑ i, z i • (F.map (u i)) (x i)
      map_add' := by
        intro z z'
      -- The stagewise lift is defined by the standard linear combination of the chosen basis
      -- images at the common stage.
        simp [Finset.sum_add_distrib, add_smul]
      map_smul' := by
        intro r z
        simp [Finset.smul_sum, mul_smul] }
  refine ⟨k, g, ?_⟩
  -- The constructed map matches `f` on the standard basis, hence everywhere.
  apply (Pi.basisFun R (Fin n)).ext
  intro i
  have htransport :
      (colimit.ι F k).hom ((F.map (u i)) (x i)) =
        (colimit.ι F (j i)).hom (x i) := by
    -- Naturality of the colimit cocone transports each chosen lift to the common stage.
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (colimit.w F (u i))) (x i)
  calc
    ((colimit.ι F k).hom.comp g) ((Pi.basisFun R (Fin n)) i)
        = (colimit.ι F k).hom ((F.map (u i)) (x i)) := by
            simp [g, Pi.basisFun_apply]
    _ = (colimit.ι F (j i)).hom (x i) := htransport
    _ = f ((Pi.basisFun R (Fin n)) i) := hx i

/-- Helper for Lemma 10.11.4: if a finitely generated submodule of a finite free module vanishes in
the filtered colimit, then it already vanishes at some later stage. -/
lemma fg_submodule_eventually_le_ker_of_colimit_vanishing
    {n : ℕ} {K : Submodule R (Fin n → R)} (hK : K.FG)
    {J : Type (max u v)} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{max u v} R) [HasColimit F]
    {i : J}
    (g : (Fin n → R) →ₗ[R] F.obj i)
    (hg : K ≤ LinearMap.ker ((colimit.ι F i).hom.comp g)) :
    ∃ (j : J) (u : i ⟶ j), K ≤ LinearMap.ker ((F.map u).hom.comp g) := by
  letI : Module.Finite R K := Module.Finite.of_fg hK
  let a : ModuleCat.of R (ULift.{v} K) ⟶ F.obj i :=
    ModuleCat.ofHom (((g.comp K.subtype).comp ULift.moduleEquiv.toLinearMap))
  let b : ModuleCat.of R (ULift.{v} K) ⟶ F.obj i := 0
  have ha_colim : a ≫ colimit.ι F i = b ≫ colimit.ι F i := by
    apply ModuleCat.hom_ext
    ext x
    -- The restricted map is zero in the colimit because every relation already vanishes there.
    have hx0 : (colimit.ι F i).hom (g (K.subtype x.down)) = 0 := hg x.down.property
    simpa [a, b, Category.assoc] using hx0
  obtain ⟨j, u, hu⟩ :=
    eventually_equal_of_hom_to_colimit_of_finite_module
      (R := R) (N := ModuleCat.of R (ULift.{v} K)) F a b ha_colim
  refine ⟨j, u, ?_⟩
  intro x hx
  let xK : K := ⟨x, hx⟩
  have hxu :
      ((a ≫ F.map u).hom) (ULift.up xK) =
        ((b ≫ F.map u).hom) (ULift.up xK) :=
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hu) (ULift.up xK)
  -- Evaluating the eventual equality on a representative of `K` gives the desired kernel bound.
  simpa [a, b, Category.assoc] using hxu

/-- Helper for Lemma 10.11.4: the filtered-colimit comparison map is surjective for a quotient of a
finite free module by a finitely generated submodule. -/
lemma quotient_of_fin_surjective_filteredColimitHomComparison
    {n : ℕ} (K : Submodule R (Fin n → R)) (hK : K.FG)
    {J : Type (max u v)} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{max u v} R) [HasColimit F] :
    Function.Surjective
      (colimit.post F
        (coyoneda.obj
          (op (ModuleCat.of R (ULift.{v} ((Fin n → R) ⧸ K)))))) := by
  let Q : Type (max u v) := ULift.{v} ((Fin n → R) ⧸ K)
  let A : ModuleCat.{max u v} R := ModuleCat.of R Q
  intro f
  let f₀ : ((Fin n → R) ⧸ K) →ₗ[R] (colimit F : ModuleCat.{max u v} R) :=
    f.hom.comp ULift.moduleEquiv.symm.toLinearMap
  obtain ⟨i, gᵢ, hgᵢ⟩ :=
    linearMap_from_fin_factor_through_filtered_colimit_stage
      (R := R) (F := F) n (f₀.comp (Submodule.mkQ K))
  have hvanish : K ≤ LinearMap.ker ((colimit.ι F i).hom.comp gᵢ) := by
    -- The original map already factors through the quotient, so the defining relations vanish in
    -- the colimit at the chosen stage.
    intro x hx
    have hx0 : (Submodule.mkQ K) x = 0 := by
      exact (Submodule.Quotient.mk_eq_zero _).2 hx
    have hcomp :
        ((colimit.ι F i).hom.comp gᵢ) x = (f₀.comp (Submodule.mkQ K)) x := by
      simpa [LinearMap.comp_assoc] using LinearMap.congr_fun hgᵢ x
    rw [LinearMap.mem_ker, hcomp]
    simpa using congrArg f₀ hx0
  obtain ⟨j, u, hu⟩ :=
    fg_submodule_eventually_le_ker_of_colimit_vanishing
      (R := R) (K := K) hK F gᵢ hvanish
  let gⱼ₀ : ((Fin n → R) ⧸ K) →ₗ[R] F.obj j :=
    K.liftQ ((F.map u).hom.comp gᵢ) hu
  let gⱼ : A ⟶ F.obj j :=
    ModuleCat.ofHom (gⱼ₀.comp ULift.moduleEquiv.toLinearMap)
  let y : colimit (F ⋙ coyoneda.obj (op A)) := colimit.ι (F ⋙ coyoneda.obj (op A)) j gⱼ
  refine ⟨y, ?_⟩
  have hgⱼ₀ :
      (colimit.ι F j).hom.comp gⱼ₀ = f₀ := by
    -- Descending through the quotient is justified because the relations already vanish at stage
    -- `j`, and the colimit cocone then identifies the descended map with `f₀`.
    apply linearMap_eq_of_comp_mkQ_eq (R := R) (K := K)
    calc
      ((colimit.ι F j).hom.comp gⱼ₀).comp (Submodule.mkQ K)
          = (colimit.ι F j).hom.comp (((F.map u).hom.comp gᵢ)) := by
              rw [LinearMap.comp_assoc, Submodule.liftQ_mkQ]
      _ = ((colimit.ι F i).hom.comp gᵢ) := by
            have hcolim :
                (colimit.ι F j).hom.comp (F.map u).hom = (colimit.ι F i).hom := by
              ext x
              simpa using
                LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (colimit.w F u)) x
            simpa [LinearMap.comp_assoc] using congrArg (fun φ => φ.comp gᵢ) hcolim
      _ = f₀.comp (Submodule.mkQ K) := hgᵢ
  have hgⱼ_post :
      gⱼ ≫ colimit.ι F j = f := by
    -- The descended stage map matches `f` after composing with the colimit cocone, and the ULift
    -- transport is only the canonical equivalence on the source module.
    apply ModuleCat.hom_ext
    ext x
    simpa [gⱼ, f₀, LinearMap.comp_assoc] using
      LinearMap.congr_fun hgⱼ₀ x.down
  -- The source colimit element represented by `gⱼ` maps to `f` under `colimit.post`.
  simpa [y, hgⱼ_post] using
    colimit_post_coyoneda_ι_app
      (A := A) (B := F) j gⱼ

/-- Helper for Lemma 10.11.4: for a quotient of a finite free module by a finitely generated
submodule, the filtered-colimit comparison map on the represented functor is bijective. -/
lemma quotient_of_fin_bijective_filteredColimitHomComparison
    {n : ℕ} (K : Submodule R (Fin n → R)) (hK : K.FG)
    {J : Type (max u v)} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{max u v} R) [HasColimit F] :
    Function.Bijective
      (colimit.post F
        (coyoneda.obj
          (op (ModuleCat.of R (ULift.{v} ((Fin n → R) ⧸ K)))))) := by
  constructor
  · let _ : Module.FinitePresentation R ((Fin n → R) ⧸ K) :=
      Module.finitePresentation_of_surjective (Submodule.mkQ K)
        (Submodule.mkQ_surjective _) <| by
          change (LinearMap.ker (Submodule.mkQ K)).FG
          simpa [Submodule.ker_mkQ] using hK
    let _ : Module.Finite R (ULift.{v} ((Fin n → R) ⧸ K)) := inferInstance
    -- Injectivity is exactly Lemma 10.11.1 applied to the finite quotient module.
    exact
      (module_finite_iff_injective_filteredColimitHomComparison
        (R := R) (N := ModuleCat.of R (ULift.{v} ((Fin n → R) ⧸ K)))).1 inferInstance F
  · -- Surjectivity follows from factoring a free-module lift through one stage and descending it
    -- through the quotient once the finitely generated relations vanish at a later stage.
    exact quotient_of_fin_surjective_filteredColimitHomComparison
      (R := R) K hK F

/-- Helper for Lemma 10.11.4: a finitely presented module has represented functor preserving
filtered colimits. -/
lemma finitePresentation_preservesFilteredColimits_coyoneda
    [Module.FinitePresentation R M] :
    PreservesFilteredColimits (coyoneda.obj (op (ModuleCat.of R M))) := by
  classical
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin R M
  let Q : Type (max u v) := ULift.{v} ((Fin n → R) ⧸ K)
  let A : ModuleCat.{max u v} R := ModuleCat.of R Q
  let eModule :
      ModuleCat.of R M ≅ A :=
    (e.trans ULift.moduleEquiv.symm).toModuleIso
  refine ⟨fun J _ _ ↦ ?_⟩
  refine ⟨fun {F} ↦ ?_⟩
  have hbij :
      Function.Bijective
        (colimit.post F (coyoneda.obj (op A))) :=
    quotient_of_fin_bijective_filteredColimitHomComparison
      (R := R) K hK F
  let _ :
      IsIso (colimit.post F (coyoneda.obj (op A))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hbij
  let β : coyoneda.obj (op A) ≅ coyoneda.obj (op (ModuleCat.of R M)) :=
    coyoneda.mapIso eModule.op
  -- The presentation equivalence identifies the represented functor of `M` with that of the
  -- quotient presentation, so preservation transports along the induced natural isomorphism.
  let _ : PreservesColimit F (coyoneda.obj (op A)) :=
    preservesColimit_of_isIso_post (coyoneda.obj (op A)) F
  exact preservesColimit_of_natIso F β

-- Source/core/bridge triage:
-- * source-facing: `Module.FinitePresentation R M`
-- * core/canonical: `CategoryTheory.IsFinitelyPresentable (ModuleCat.of R M)`
-- * bridge/view: preservation of filtered colimits by the represented functor `Hom_R(M, -)`
--
-- The owner abstraction is `IsFinitelyPresentable (ModuleCat.of R M)`. The filtered-colimit
-- statement is then obtained by composing with the owner theorem
-- `isFinitelyPresentable_iff_preservesFilteredColimits`.

/-- Lemma 10.11.4 (1): an `R`-module is finitely presented if and only if the corresponding object of
`ModuleCat R` is finitely presentable. -/
-- Proof sketch: use the standard equivalence in mathlib between finite presentation of an
-- `R`-module and finite presentability of the associated object of `ModuleCat R`.
@[stacks 0G8P]
theorem module_finitePresentation_iff_isFinitelyPresentable :
    Module.FinitePresentation R M ↔ IsFinitelyPresentable.{max u v} (ModuleCat.of R M) := by
  constructor
  · intro hM
    let _ : Module.FinitePresentation R M := hM
    -- Route correction: execute the source proof through the quotient presentation supplied by
    -- `Module.FinitePresentation.exists_fin`, then apply the owner criterion for finite
    -- presentability in `ModuleCat`.
    exact (isFinitelyPresentable_iff_preservesFilteredColimits).2
      (finitePresentation_preservesFilteredColimits_coyoneda (R := R) (M := M))
  · intro hM
    -- Route correction: instead of rebuilding the source proof's finite-free exact sequence, use
    -- Lemma 10.11.3 to obtain a filtered colimit by finitely presented modules and factor `id_M`
    -- through one stage because `M` is finitely presentable in `ModuleCat`.
    obtain ⟨J, _, _, pres, hpres⟩ :=
      (show CategoryTheory.ObjectProperty.ind.{max u v}
          (fun N : ModuleCat.{max u v} R ↦ Module.FinitePresentation R N)
          (ModuleCat.of R M) from by
        simpa [CategoryTheory.ObjectProperty.ind] using
          (module_is_isomorphic_to_colimit_of_directed_system_of_finitelyPresented
            (R := R) (M := ModuleCat.of R M)))
    have hpreserve :
        PreservesFilteredColimits (coyoneda.obj (op (ModuleCat.of R M))) := by
      exact (isFinitelyPresentable_iff_preservesFilteredColimits).mp hM
    obtain ⟨j, u, hu⟩ :=
      Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves (F := coyoneda.obj (op (ModuleCat.of R M))) pres.isColimit)
        (𝟙 (ModuleCat.of R M))
    let v' : pres.diag.obj j ⟶ ModuleCat.of R M := pres.ι.app j
    have huv : v'.hom.comp u.hom = LinearMap.id := by
      simpa [v'] using congrArg ModuleCat.Hom.hom hu
    letI : Module.FinitePresentation R (pres.diag.obj j) := hpres j
    -- The split surjection from a finitely presented stage back onto `M` now descends finite
    -- presentation to `M` through the kernel-range projector from the source proof.
    exact module_finitePresentation_of_split_surjection_from_finitelyPresented_stage
      (R := R) u.hom v'.hom huv

/-- Lemma 10.11.4 (2): an `R`-module is finitely presented if and only if its represented functor
`Hom_R(M, -)` preserves filtered colimits. -/
-- Proof sketch: combine the previous equivalence with the owner-abstraction theorem
-- `isFinitelyPresentable_iff_preservesFilteredColimits` for the represented functor.
@[stacks 0G8P]
theorem module_finitePresentation_iff_preservesFilteredColimits_coyoneda :
    Module.FinitePresentation R M ↔
      PreservesFilteredColimits (coyoneda.obj (op (ModuleCat.of R M))) := by
  -- Rewrite through finite presentability in `ModuleCat`, then apply the owner characterization of
  -- finitely presentable objects by preservation of filtered colimits of the represented functor.
  rw [module_finitePresentation_iff_isFinitelyPresentable]
  exact isFinitelyPresentable_iff_preservesFilteredColimits

end
