import Mathlib
import StacksProject_2024.Chap10.Lemma_10_11_3
import StacksProject_2024.Chap10.Lemma_10_88_11
import StacksProject_2024.Chap10.Proposition_10_88_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u v w

namespace Module

section

variable {R : Type u} [CommRing R]
variable {M : Type (max u v)} [AddCommGroup M]

/- Source/core/bridge triage:
* source-facing: the quotient-ring comparison statement from Lemma `10.88.12`.
* core/canonical: the chapter owner `Module.MittagLeffler` from `Definition_10_88_7`.
* bridge/view: choose a directed presentation of the quotient module, restrict that same diagram to
  `R`, and use quotient surjectivity to identify the Hom systems over `R` and over `R ⧸ I`.
-/
-- Proof sketch: one direction is Lemma `10.88.11` applied to the quotient map `R → R ⧸ I`. For
-- the converse, choose a directed colimit presentation of `M` by finitely presented `R ⧸ I`-modules;
-- since `I` is finitely generated, the quotient algebra `R ⧸ I` is finite and finitely presented
-- over `R`, so the same stages are finitely presented over `R`, and the Hom inverse systems over
-- `R` and `R ⧸ I` agree because the quotient map is surjective.
/-- Helper for Lemma 10.88.12: restricting scalars on a compatible quotient module does not change
the underlying `R`-module. -/
private noncomputable def restrictScalars_obj_iso
    {S : Type w} [CommRing S] [Algebra R S]
    [Module S M] [Module R M] [IsScalarTower R S M] :
    (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S M) ≅ ModuleCat.of R M :=
  (show ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S M)) ≃ₗ[R] M from
    { __ := AddEquiv.refl M
      map_smul' := fun _ _ ↦ by simp [ModuleCat.restrictScalars.smul_def] }).toModuleIso

/-- Helper for Lemma 10.88.12: an `R`-linear map between quotient modules already commutes with
the quotient scalar action because every quotient scalar lifts to `R`. -/
private lemma quotient_restrictScalars_map_smul
    (I : Ideal R) {X Y : ModuleCat.{max u v} (R ⧸ I)}
    (φ : ((ModuleCat.restrictScalars (algebraMap R (R ⧸ I))).obj X) ⟶
      ((ModuleCat.restrictScalars (algebraMap R (R ⧸ I))).obj Y))
    (s : R ⧸ I) (x : X) :
    φ (s • x) = s • φ x := by
  -- Rewrite the quotient scalar through a preimage in `R` and apply `R`-linearity.
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
  simpa [ModuleCat.restrictScalars.smul_def] using φ.hom.map_smul r x

/-- Helper for Lemma 10.88.12: on quotient modules, an `R`-linear map is automatically
`R ⧸ I`-linear because every quotient scalar lifts along `R → R ⧸ I`. -/
private noncomputable def quotient_linearMap_equiv
    (I : Ideal R) {X Y : Type (max u v)} [AddCommGroup X] [AddCommGroup Y]
    [Module (R ⧸ I) X] [Module (R ⧸ I) Y] [Module R X] [Module R Y]
    [IsScalarTower R (R ⧸ I) X] [IsScalarTower R (R ⧸ I) Y] :
    (X →ₗ[R] Y) ≃ (X →ₗ[R ⧸ I] Y) where
  toFun φ :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := by
        intro s x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
        simpa only [RingHom.id_apply, ← Ideal.Quotient.algebraMap_eq,
          IsScalarTower.algebraMap_smul] using
          φ.map_smul r x }
  invFun φ := φ.restrictScalars R
  left_inv φ := by
    ext x
    rfl
  right_inv φ := by
    ext x
    rfl

/-- Helper for Lemma 10.88.12: every quotient module admits a filtered colimit presentation by
finitely presented quotient modules in the universe used by the target module. -/
private lemma quotient_filtered_presentation_fixed_universe
    (I : Ideal R) [Module (R ⧸ I) M] :
    ∃ (J : Type (max u v)) (_ : SmallCategory J) (_ : IsFiltered J)
      (pres : ColimitPresentation J (ModuleCat.of.{max u v} (R ⧸ I) M)),
        ∀ j, Module.FinitePresentation (R ⧸ I) (pres.diag.obj j) := by
  -- Reuse the earlier owner theorem and unpack its filtered colimit presentation witness
  -- directly in the universe of the target quotient module.
  let QM : ModuleCat.{max u v} (R ⧸ I) := ModuleCat.of.{max u v} (R ⧸ I) M
  simpa [CategoryTheory.ObjectProperty.ind] using
    (show CategoryTheory.ObjectProperty.ind.{max u v}
        (fun N : ModuleCat.{max u v} (R ⧸ I) ↦ Module.FinitePresentation (R ⧸ I) N)
        QM from
      (module_is_isomorphic_to_colimit_of_directed_system_of_finitelyPresented.{u, max u v}
        (R := R ⧸ I) (M := QM)))

/-- Helper for Lemma 10.88.12: restricting scalars along the quotient map does not change the
underlying function of a module morphism. This is the transport-stable rewrite used before the
source-proof Hom comparison is rebundled into an inverse-system statement. -/
private lemma quotient_restrictScalars_map_apply
    (I : Ideal R) {X Y : ModuleCat.{max u v} (R ⧸ I)}
    (f : X ⟶ Y) (x : X) :
    (ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I))).map f x = f x := by
  rfl

/-- Helper for Lemma 10.88.12: after restricting scalars, precomposing with a stage map still acts
by the same underlying function. This isolates the function-level rewrite needed for the future
`Hom_R = Hom_{R ⧸ I}` naturality comparison. -/
private lemma quotient_restrictScalars_precomp_apply
    (I : Ideal R) {X' X N : ModuleCat.{max u v} (R ⧸ I)} (f : X' ⟶ X)
    (ψ : ((ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I))).obj X) ⟶
      ((ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I))).obj N)) (x : X') :
    (((ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I))).map f) ≫ ψ) x = ψ (f x) := by
  -- Both restriction of scalars and categorical composition keep the same underlying function.
  rfl

/-- Helper for Lemma 10.88.12: reindexing a filtered quotient presentation along a final directed
functor preserves finite presentation of every stage. -/
private lemma quotient_reindexed_stage_finitePresentation
    (I : Ideal R) [Module (R ⧸ I) M]
    {J : Type (max u v)} [SmallCategory J] [IsFiltered J]
    (pres : ColimitPresentation J (ModuleCat.of.{max u v} (R ⧸ I) M))
    (hfp : ∀ j, Module.FinitePresentation (R ⧸ I) (pres.diag.obj j))
    {K : Type (max u v)} [PartialOrder K] [IsDirected K (· ≤ ·)] [Nonempty K]
    (FJ : K ⥤ J) [FJ.Final] :
    ∀ k, Module.FinitePresentation (R ⧸ I) ((pres.reindex FJ).diag.obj k) := by
  -- Reindexing only relabels the same quotient modules, so the stagewise hypothesis is unchanged.
  intro k
  simpa using hfp (FJ.obj k)

/-- Helper for Lemma 10.88.12: for one fixed target quotient module, the `R`-linear and
`R ⧸ I`-linear Hom stages in the chosen presentation are identified by the surjectivity of
`R → R ⧸ I`. -/
private noncomputable def quotient_hom_inverseSystem_stage_equiv
    (I : Ideal R) {K : Type (max u v)} [Preorder K]
    (F : K ⥤ ModuleCat.{max u v} (R ⧸ I))
    (N : ModuleCat.{max u v} (R ⧸ I)) (j : Kᵒᵖ) :
    ((colimitPresentationHomInverseSystem
        (F ⋙ ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I)))
        ((ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I))).obj N)).obj j) ≃
      ((colimitPresentationHomInverseSystem F N).obj j) :=
  let _ : Module R (F.obj (Opposite.unop j)) :=
    Module.compHom (F.obj (Opposite.unop j)) (algebraMap R (R ⧸ I))
  let _ : Module R N := Module.compHom N (algebraMap R (R ⧸ I))
  let _ : IsScalarTower R (R ⧸ I) (F.obj (Opposite.unop j)) :=
    IsScalarTower.restrictScalars R (R ⧸ I) (F.obj (Opposite.unop j))
  let _ : IsScalarTower R (R ⧸ I) N := IsScalarTower.restrictScalars R (R ⧸ I) N
  { toFun := fun ψ ↦
      ModuleCat.ofHom <|
        (quotient_linearMap_equiv (R := R) (I := I)
          (X := F.obj (Opposite.unop j)) (Y := N)) ψ.hom
    invFun := fun ψ ↦
      ModuleCat.ofHom <|
        ((quotient_linearMap_equiv (R := R) (I := I)
          (X := F.obj (Opposite.unop j)) (Y := N)).symm ψ.hom)
    left_inv := by
      intro ψ
      apply ModuleCat.hom_ext
      ext x
      rfl
    right_inv := by
      intro ψ
      apply ModuleCat.hom_ext
      ext x
      rfl }

/-- Helper for Lemma 10.88.12: the stagewise quotient-Hom identifications commute with the
transition maps in the inverse systems `Hom_R(Mᵢ, N)` and `Hom_{R ⧸ I}(Mᵢ, N)`. -/
private lemma quotient_hom_inverseSystem_stage_equiv_naturality
    (I : Ideal R) {K : Type (max u v)} [Preorder K]
    (F : K ⥤ ModuleCat.{max u v} (R ⧸ I))
    (N : ModuleCat.{max u v} (R ⧸ I)) {i j : Kᵒᵖ} (g : j ⟶ i)
    (ψ : ((colimitPresentationHomInverseSystem
        (F ⋙ ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I)))
        ((ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I))).obj N)).obj j)) :
    quotient_hom_inverseSystem_stage_equiv (R := R) I F N i
        (((colimitPresentationHomInverseSystem
            (F ⋙ ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I)))
            ((ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I))).obj N)).map g) ψ) =
      ((colimitPresentationHomInverseSystem F N).map g)
        (quotient_hom_inverseSystem_stage_equiv (R := R) I F N j ψ) := by
  -- Both sides are the same precomposition map; only the scalar-linearity packaging differs.
  change ModuleCat.ofHom _ = ModuleCat.ofHom _
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- Helper for Lemma 10.88.12: if the fixed-target inverse system of `R`-linear maps is
Mittag-Leffler after restricting scalars, then the equal inverse system of quotient-linear maps is
Mittag-Leffler as well. -/
private lemma quotient_hom_inverseSystem_isMittagLeffler_of_restrictScalars
    (I : Ideal R) {K : Type (max u v)} [Preorder K] [Nonempty K] [IsDirectedOrder K]
    (F : K ⥤ ModuleCat.{max u v} (R ⧸ I))
    (N : ModuleCat.{max u v} (R ⧸ I))
    (hR :
      (colimitPresentationHomInverseSystem
        (F ⋙ ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I)))
        ((ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I))).obj N)).IsMittagLeffler) :
    (colimitPresentationHomInverseSystem F N).IsMittagLeffler := by
  let G := ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I))
  let FR := colimitPresentationHomInverseSystem (F ⋙ G) (G.obj N)
  let FS := colimitPresentationHomInverseSystem F N
  rw [Functor.isMittagLeffler_iff_subset_range_comp] at hR ⊢
  intro j
  obtain ⟨i, f, hf⟩ := hR j
  refine ⟨i, f, ?_⟩
  intro k g y hy
  rcases hy with ⟨x, rfl⟩
  let xR := (quotient_hom_inverseSystem_stage_equiv (R := R) I F N i).symm x
  -- Transport the range witness to the restricted-scalar Hom inverse system.
  have hxR : FR.map f xR ∈ Set.range (FR.map (g ≫ f)) := by
    exact hf g ⟨xR, rfl⟩
  rcases hxR with ⟨zR, hzR⟩
  refine ⟨quotient_hom_inverseSystem_stage_equiv (R := R) I F N k zR, ?_⟩
  -- Apply the stagewise identifications at the source and target stages.
  calc
    FS.map (g ≫ f) (quotient_hom_inverseSystem_stage_equiv (R := R) I F N k zR)
        = quotient_hom_inverseSystem_stage_equiv (R := R) I F N j (FR.map (g ≫ f) zR) := by
            symm
            exact quotient_hom_inverseSystem_stage_equiv_naturality
              (R := R) I F N (g ≫ f) zR
    _ = quotient_hom_inverseSystem_stage_equiv (R := R) I F N j (FR.map f xR) := by
          rw [hzR]
    _ = FS.map f (quotient_hom_inverseSystem_stage_equiv (R := R) I F N i xR) := by
          exact quotient_hom_inverseSystem_stage_equiv_naturality (R := R) I F N f xR
    _ = FS.map f x := by
          rw [Equiv.apply_symm_apply]

/-- Lemma 10.88.12: if `S = R ⧸ I` for a finitely generated ideal `I`, then an `S`-module `M` is
Mittag-Leffler over `R` if and only if it is Mittag-Leffler over `S`. -/
@[stacks 05CR]
theorem mittagLeffler_iff_over_ring_and_quotient (I : Ideal R) (hI : I.FG)
    [Module (R ⧸ I) M] [Module R M] [IsScalarTower R (R ⧸ I) M] :
    MittagLeffler.{u, max u v} R M ↔ MittagLeffler.{u, max u v} (R ⧸ I) M := by
  constructor
  · intro hM
    letI : Algebra.FinitePresentation R (R ⧸ I) := Algebra.FinitePresentation.quotient hI
    letI : Module.Finite R (R ⧸ I) := by infer_instance
    classical
    -- Route correction: keep the source-faithful quotient presentation, but transfer the final
    -- Hom inverse systems targetwise instead of rebundling factorization maps.
    obtain ⟨J, _, _, pres, hfpFilt⟩ :=
      quotient_filtered_presentation_fixed_universe (R := R) (M := M) I
    obtain ⟨K, _, _, _, FJ, _⟩ := CategoryTheory.IsFiltered.exists_directed J
    let P : ColimitPresentation K (ModuleCat.of.{max u v} (R ⧸ I) M) := pres.reindex FJ
    let F : K ⥤ ModuleCat.{max u v} (R ⧸ I) := P.diag
    let cS : colimit F ≅ ModuleCat.of.{max u v} (R ⧸ I) M :=
      (P.isColimit.coconePointUniqueUpToIso (colimit.isColimit F)).symm
    have hfpS : ∀ k, Module.FinitePresentation (R ⧸ I) (F.obj k) := by
      -- Reindexing only changes the directed index set, not the quotient-module stages.
      intro k
      exact quotient_reindexed_stage_finitePresentation (R := R) (M := M) I pres hfpFilt FJ k
    let G := ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I))
    let cR : colimit (F ⋙ G) ≅ ModuleCat.of.{max u v} R M :=
      (preservesColimitIso G F).symm ≪≫ G.mapIso cS ≪≫
        restrictScalars_obj_iso (R := R) (S := R ⧸ I)
    have hfpR : ∀ k, Module.FinitePresentation R ((F ⋙ G).obj k) := by
      -- Lemma `10.36.23` upgrades each finitely presented quotient stage to a finitely presented
      -- `R`-module stage because `R ⧸ I` is finite and finitely presented over `R`.
      intro k
      let _ : Module R (F.obj k) := Module.compHom (F.obj k) (algebraMap R (R ⧸ I))
      let _ : IsScalarTower R (R ⧸ I) (F.obj k) :=
        IsScalarTower.restrictScalars R (R ⧸ I) (F.obj k)
      simpa [F, G] using
        (Module.FinitePresentation.iff_of_finite_finitePresentation
          (R := R) (S := R ⧸ I) (M := F.obj k)).2 (hfpS k)
    letI : MittagLeffler.{u, max u v} R M := hM
    let PR : MittagLefflerPresentation R M := Classical.choice (MittagLeffler.exists_presentation
      (R := R) (M := M))
    letI : Preorder PR.index := PR.indexPreorder
    letI : Nonempty PR.index := PR.indexNonempty
    letI : IsDirectedOrder PR.index := PR.indexDirected
    let cPR : colimit PR.diagram ≅ ModuleCat.of.{max u v} R M := Classical.choice PR.colimitIso
    have hdom :
        ∀ (Q : ModuleCat.{max u v} R) [Module.FinitePresentation R Q] (f : Q →ₗ[R] M),
          ∃ (Q' : ModuleCat.{max u v} R) (_ : Module.FinitePresentation R Q') (g : Q →ₗ[R] Q'),
            ∀ N : ModuleCat.{max u v} R,
              LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) := by
      rcases PR.presentation_isMittagLeffler with ⟨hfpPR, hallPR⟩
      -- Clause `(1)` in Proposition `10.88.6` depends only on `M`, not on the chosen presentation.
      exact ((directed_colimit_presentation_mittag_leffler_tfae PR.diagram hfpPR cPR).out 3 0).mp
        hallPR
    have hallR :
        ∀ N : ModuleCat.{max u v} R, (colimitPresentationHomInverseSystem (F ⋙ G) N).IsMittagLeffler :=
      ((directed_colimit_presentation_mittag_leffler_tfae (F ⋙ G) hfpR cR).out 0 3).mp hdom
    have hallS :
        ∀ N : ModuleCat.{max u v} (R ⧸ I), (colimitPresentationHomInverseSystem F N).IsMittagLeffler := by
      -- For each target quotient module, the textbook equality
      -- `Hom_R(Mᵢ, N) = Hom_{R ⧸ I}(Mᵢ, N)` transfers the Mittag-Leffler condition.
      intro N
      exact quotient_hom_inverseSystem_isMittagLeffler_of_restrictScalars
        (R := R) I F N (hallR (G.obj N))
    -- Package the chosen directed quotient presentation as a Mittag-Leffler presentation over
    -- `R ⧸ I`.
    exact ⟨⟨{
      index := K
      indexPreorder := inferInstance
      indexNonempty := inferInstance
      indexDirected := inferInstance
      diagram := F
      presentation_isMittagLeffler := ⟨hfpS, hallS⟩
      colimitIso := ⟨cS⟩
    }⟩⟩
  · intro hM
    letI : Algebra.FinitePresentation R (R ⧸ I) := Algebra.FinitePresentation.quotient hI
    letI : Module.Finite R (R ⧸ I) := by infer_instance
    letI : MittagLeffler.{u, max u v} (R ⧸ I) M := hM
    -- The reverse implication is exactly the finite, finitely presented restriction-of-scalars
    -- bridge from Lemma `10.88.11`.
    simpa using
      (mittagLeffler_restrictScalars_of_finite_finitePresentation
        (R := R) (S := R ⧸ I) (M := M))

end

end Module
