import Mathlib
import Mathlib.Algebra.Category.Grp.Ulift
import StacksProject_2024.stacks_project.Chap13.Definition_13_14_10
import StacksProject_2024.stacks_project.Chap13.Lemma_13_14_3
import StacksProject_2024.stacks_project.Chap13.Lemma_13_14_16
import StacksProject_2024.stacks_project.Chap13.Lemma_13_19_6
import StacksProject_2024.stacks_project.Chap15.Definition_15_75_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_67_13
import StacksProject_2024.stacks_project.Chap15.«15_60_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedTensorWithAlgebra

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

/- Domain-style sampling for filtered-colimit descent of perfect derived complexes:
- primary domain: derived scalar extension of perfect objects over filtered colimits of
  commutative rings;
- owner declarations inspected in this domain:
  - `DerivedCategory.IsPerfect` from `Definition_15_75_1`;
  - the scalar-extension owner `derivedTensorWithAlgebra` and its notation
    `K ⊗[R]^L[A]` from `Lemma_15_60_1`;
  - the owner comparison `derivedTensorWithAlgebraCompIso` for iterated-vs-direct derived scalar
    extension from `Lemma_15_60_1`;
  - the source-facing filtered-colimit comparison for stagewise Hom-sets, whose public content is
    the factorization, transition-compatibility, and eventual-equality trio rather than a
    packaged colimit witness;
- best owner abstraction: the public surface here should be organized around the stagewise and
  colimit base-change owners together with the source-facing factorization and eventual-equality
  theorems, while the filtered-cocone packaging remains only an internal proof model if needed;
- primitive vs. derived:
  - primitive data are the filtered ring diagram `F`, the chosen base stage `i₀`, and the
    canonical ring maps `F.obj i₀ → F.obj j` and `F.obj j → colimit F`;
  - the stagewise transition maps and comparison morphisms into the colimit ring are primitive
    data for the explicit Hom-colimit construction;
  - the factorization, transition-compatibility, and eventual-equality assertions are the public
    source-facing API for part `(2)`, rather than a separate public `Functor` / `Cocone` /
    `IsColimit` package.

Source/core/bridge triage:
- `source-facing`: the perfect-complex descent theorem together with the stagewise factorization
  and eventual-equality statements for Homs after base change;
- `core/canonical`: `DerivedCategory.IsPerfect`, `derivedTensorWithAlgebra`, and the canonical
  iterated-scalar-extension owner `derivedTensorWithAlgebraCompIso`;
- `bridge/view`: the canonical comparison between iterated scalar extension through a stage and
  direct scalar extension to the colimit, used to define the source-facing transition maps on Hom
  sets without introducing a parallel public functor owner. -/

variable {I : Type v} [Preorder I] [IsFiltered I]
variable (F : I ⥤ CommRingCat.{u}) [HasColimit F]

/-- The filtered colimit ring `\operatorname{colim}_i R_i`. -/
private abbrev ringColimit : CommRingCat.{u} :=
  colimit F

/-- Base change from the stage ring `R_i` to the filtered colimit ring. -/
private abbrev baseChangeToColimit (i : I) :
    DerivedCategory (ModuleCat (F.obj i)) ⥤
      DerivedCategory (ModuleCat (ringColimit F)) :=
  derivedTensorWithAlgebra (colimit.ι F i).hom

/-- Helper for Lemma 15.75.18: the raw directed system of stage rings underlying the filtered
diagram. -/
private abbrev ringStageSystem : I → Type u :=
  fun i ↦ F.obj i

/-- Helper for Lemma 15.75.18: the transition map in the raw directed system of stage rings. -/
private abbrev ringStageMap (i j : I) (hij : i ≤ j) :
    ringStageSystem F i →+* ringStageSystem F j :=
  (F.map (homOfLE hij)).hom

/-- Helper for Lemma 15.75.18: the stage-ring transition maps form a directed system. -/
private instance ringStageMap_directedSystem :
    DirectedSystem (ringStageSystem F) (fun i j hij ↦ ringStageMap F i j hij) where
  map_self i := by
    -- Proof comment: functoriality identifies the self-transition with the identity map.
    change ((F.map (𝟙 i)).hom) = RingHom.id _
    simpa using congrArg CommRingCat.Hom.hom (F.map_id i)
  map_map := by
    intro i j k hij hjk
    -- Proof comment: the transition to `k` through `j` is exactly the functorial composite.
    change ((F.map (homOfLE hjk)).hom).comp ((F.map (homOfLE hij)).hom) =
      (F.map (homOfLE (hij.trans hjk))).hom
    simpa [ringStageMap, CommRingCat.hom_comp] using
      congrArg CommRingCat.Hom.hom
        ((F.map_comp (homOfLE hij) (homOfLE hjk)).symm)

/-- Helper for Lemma 15.75.18: every cocone over the filtered ring diagram is a compatible family
for the explicit ring direct limit. -/
private theorem ringStageDirectLimit_cocone_compat
    (s : Cocone F) {i j : I} (hij : i ≤ j) :
    (s.ι.app j).hom.comp (ringStageMap F i j hij) = (s.ι.app i).hom := by
  -- Proof comment: this is exactly the cocone naturality square specialized to the unique map
  -- `i ⟶ j` in the preorder.
  simpa [ringStageMap, CommRingCat.hom_comp] using
    congrArg CommRingCat.Hom.hom (s.w (homOfLE hij))

/-- Helper for Lemma 15.75.18: the explicit ring direct limit of the stage system, viewed as a
cocone over the original filtered diagram. -/
private noncomputable def ringStageDirectLimitCocone : Cocone F where
  pt :=
    CommRingCat.of
      (Ring.DirectLimit (ringStageSystem F) (fun i j hij ↦ ringStageMap F i j hij))
  ι :=
    { app := fun i ↦
        CommRingCat.ofHom
          (Ring.DirectLimit.of
            (ringStageSystem F) (fun i j hij ↦ ringStageMap F i j hij) i)
      naturality := by
        intro i j f
        let hij : i ≤ j := homOfLE_leOfHom f
        -- Proof comment: the direct-limit structure map satisfies the cocone relation by the
        -- defining equation `of_f`.
        ext x
        subst f
        simpa [ringStageMap] using
          (Ring.DirectLimit.of_f
            (G := ringStageSystem F)
            (f := fun i j hij ↦ ringStageMap F i j hij)
            hij x) }

/-- Helper for Lemma 15.75.18: the explicit ring direct-limit cocone satisfies the colimit
universal property. -/
private noncomputable def ringStageDirectLimitCoconeIsColimit :
    IsColimit (ringStageDirectLimitCocone F) where
  desc s :=
    CommRingCat.ofHom <|
      Ring.DirectLimit.lift
        (ringStageSystem F)
        (fun i j hij ↦ ringStageMap F i j hij)
        s.pt
        (fun i ↦ (s.ι.app i).hom)
        (fun i j hij x ↦ by
          -- Proof comment: apply the cocone compatibility to the stage element `x`.
          simpa [RingHom.comp_apply] using
            congrArg
              (fun φ : ringStageSystem F i →+* s.pt ↦ φ x)
              (ringStageDirectLimit_cocone_compat (F := F) s hij))
  fac s i := by
    -- Proof comment: the universal lift recovers the original cocone leg on each stage.
    ext x
    simpa [ringStageDirectLimitCocone] using
      (Ring.DirectLimit.lift_of
        (G := ringStageSystem F)
        (f := fun i j hij ↦ ringStageMap F i j hij)
        (P := s.pt)
        (g := fun i ↦ (s.ι.app i).hom)
        (Hg := fun i j hij x ↦ by
          simpa [RingHom.comp_apply] using
            congrArg
              (fun φ : ringStageSystem F i →+* s.pt ↦ φ x)
              (ringStageDirectLimit_cocone_compat (F := F) s hij))
        i x)
  uniq s m hm := by
    -- Proof comment: every direct-limit element comes from some stage, so equality of cocone legs
    -- determines the induced map uniquely.
    ext x
    rcases Ring.DirectLimit.exists_of
      (G := ringStageSystem F)
      (f := fun i j hij ↦ ringStageMap F i j hij)
      x with ⟨i, xi, rfl⟩
    simpa [ringStageDirectLimitCocone, CommRingCat.hom_comp] using
      congrArg
        (fun φ :
          F.obj i ⟶ s.pt ↦ φ.hom xi)
        (hm i)

/-- Helper for Lemma 15.75.18: the categorical colimit ring is canonically identified with the
explicit ring direct limit of the stage system. -/
private noncomputable abbrev ringColimitIsoRingDirectLimit :
    ringColimit F ≅
      CommRingCat.of
        (Ring.DirectLimit (ringStageSystem F) (fun i j hij ↦ ringStageMap F i j hij)) :=
  IsColimit.coconePointUniqueUpToIso
    (colimit.isColimit F)
    (ringStageDirectLimitCoconeIsColimit F)

/-- Helper for Lemma 15.75.18: after transport along the categorical-colimit/direct-limit
comparison, the chosen stage map is the canonical direct-limit structure map. -/
private theorem ringColimitIsoRingDirectLimit_ι (i : I) :
    colimit.ι F i ≫ (ringColimitIsoRingDirectLimit F).hom =
      (ringStageDirectLimitCocone F).ι.app i := by
  -- Proof comment: this is the standard leg comparison for the two colimit cocones.
  simpa [ringStageDirectLimitCocone] using
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit F)
      (ringStageDirectLimitCoconeIsColimit F)
      i

/-- Helper for Lemma 15.75.18: on ring homs, the stage map into the explicit direct limit is the
composite of the stage map into the categorical colimit with the colimit/direct-limit comparison.
-/
private theorem ringColimitIsoRingDirectLimit_ι_hom (i : I) :
    (ringColimitIsoRingDirectLimit F).hom.hom.comp (colimit.ι F i).hom =
      Ring.DirectLimit.of
        (ringStageSystem F) (fun i j hij ↦ ringStageMap F i j hij) i := by
  -- Proof comment: this is just the previous cocone-leg identity after forgetting from
  -- `CommRingCat` morphisms to underlying ring homomorphisms.
  simpa [CommRingCat.hom_comp, ringStageDirectLimitCocone] using
    congrArg CommRingCat.Hom.hom (ringColimitIsoRingDirectLimit_ι (F := F) i)

/-- Helper for Lemma 15.75.18: after extending scalars from a stage to the categorical colimit
and then transporting across `ringColimitIsoRingDirectLimit`, one recovers the direct scalar
extension to the explicit ring direct limit. -/
private noncomputable def module_baseChange_transport_of_ringColimitIsoRingDirectLimit
    (i : I) (Mi : ModuleCat (F.obj i)) :
    ((ModuleCat.extendScalars (ringColimitIsoRingDirectLimit F).hom.hom).obj
      ((ModuleCat.extendScalars (colimit.ι F i).hom).obj Mi)) ≅
    ((ModuleCat.extendScalars
      (Ring.DirectLimit.of
        (ringStageSystem F) (fun i j hij ↦ ringStageMap F i j hij) i)).obj Mi) := by
  -- Route correction: package the repeated categorical-colimit/direct-limit tensor transport once
  -- using `ModuleCat.extendScalarsComp`, so the later descent argument can stay in the explicit
  -- direct-limit API without ad hoc coercion rewrites.
  -- Proof comment: first collapse the two successive scalar extensions, then rewrite the composite
  -- ring map by the normalized stage-leg formula above.
  exact
    ((ModuleCat.extendScalarsComp (colimit.ι F i).hom
        (ringColimitIsoRingDirectLimit F).hom.hom).symm ≪≫
      eqToIso
        (congrArg
          (fun σ ↦ ModuleCat.extendScalars σ)
          (ringColimitIsoRingDirectLimit_ι_hom (F := F) i))).app Mi

/-- Helper for Lemma 15.75.18: termwise scalar extension from a stage ring to the filtered
colimit ring. -/
private abbrev extendScalarsComplexToColimit (i : I) :
    CochainComplex (ModuleCat (F.obj i)) ℤ ⥤
      CochainComplex (ModuleCat (ringColimit F)) ℤ :=
  ((ModuleCat.extendScalars (colimit.ι F i).hom).mapHomologicalComplex (ComplexShape.up ℤ))

/-- Helper for Lemma 15.75.18: a bounded finite-projective complex is bounded above, hence belongs
to `CochainComplex.minus`. -/
private theorem bounded_finite_projective_minus
    {R : Type u} [CommRing R]
    (L : CochainComplex (ModuleCat R) ℤ)
    (hL : CochainComplex.IsBoundedFiniteProjective L) :
    CochainComplex.minus (ModuleCat R) L := by
  rcases hL.bounded with ⟨_, b, _, hLLE⟩
  exact (CochainComplex.minus_iff (ModuleCat R) L).2 ⟨b, hLLE⟩

/-- Helper for Lemma 15.75.18: the derived object of a bounded finite-projective complex is
perfect. -/
private theorem q_obj_isPerfect_of_isBoundedFiniteProjective
    {R : Type u} [CommRing R]
    (L : CochainComplex (ModuleCat R) ℤ)
    (hL : CochainComplex.IsBoundedFiniteProjective L) :
    (DerivedCategory.Q.obj L).IsPerfect := by
  -- Proof comment: the defining bounded finite-projective witness is already in the required
  -- shape.
  exact ⟨L, Iso.refl _, hL⟩

/-- Helper for Lemma 15.75.18: a finite projective module is a split summand of a finite free
module. This is the module-level input used by the source proof to descend finite projectives
through the filtered colimit system. -/
private theorem exists_split_finiteFree_cover
    {R : Type u} [CommRing R]
    (M : ModuleCat R) [Module.Finite R M] [Module.Projective R M] :
    ∃ n : ℕ,
      ∃ π : ModuleCat.of R (Fin n → R) ⟶ M,
        ∃ ι : M ⟶ ModuleCat.of R (Fin n → R),
          Epi π ∧ ι ≫ π = 𝟙 M := by
  -- Proof comment: choose a finite free cover together with a section from the standard
  -- projective-module splitting theorem, then package the linear maps as `ModuleCat` morphisms.
  obtain ⟨n, π, ι, hπsurj, _, hιπ⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective R M
  refine ⟨n, ModuleCat.ofHom π, ModuleCat.ofHom ι, ?_, ?_⟩
  · -- The chosen cover is surjective, hence epi in `ModuleCat`.
    exact (ModuleCat.epi_iff_surjective _).2 hπsurj
  · -- The chosen section is a literal splitting of the cover.
    ext x
    simpa [LinearMap.comp_apply] using congrArg (fun f : M →ₗ[R] M ↦ f x) hιπ

/-- Helper for Lemma 15.75.18: once a stage module is exhibited as a split summand of a finite
free module, it is automatically finite and projective. -/
private theorem finite_projective_of_split_finite_free
    {R : Type u} [CommRing R]
    {M : ModuleCat R} {n : ℕ}
    (π : ModuleCat.of R (Fin n → R) ⟶ M)
    (ι : M ⟶ ModuleCat.of R (Fin n → R))
    (hsplit : ι ≫ π = 𝟙 M) :
    Module.Finite R M ∧ Module.Projective R M := by
  constructor
  · -- Proof comment: the retraction identity makes `π` surjective, so `M` is a quotient of the
    -- finite free module `R^n`.
    refine Module.Finite.of_surjective π.hom ?_
    intro x
    refine ⟨ι.hom x, ?_⟩
    have hpoint := congrArg (fun f : M ⟶ M ↦ f.hom x) hsplit
    simpa [Category.assoc] using hpoint
  · -- Proof comment: the same splitting identity exhibits `M` as a retract of a projective free
    -- module.
    exact Module.Projective.of_split ι.hom π.hom (by
      ext x
      have hpoint := congrArg (fun f : M ⟶ M ↦ f.hom x) hsplit
      simpa [Category.assoc] using hpoint)

/-- Helper for Lemma 15.75.18: base change of a finite free stage module to the explicit ring
direct limit is canonically the corresponding finite free module over the direct-limit ring. -/
private noncomputable abbrev directLimit_free_baseChange_iso
    (i : I) (n : ℕ) :
    ((ModuleCat.extendScalars
      (Ring.DirectLimit.of
        (ringStageSystem F) (fun i j hij ↦ ringStageMap F i j hij) i)).obj
      (ModuleCat.of (F.obj i) (Fin n → F.obj i))) ≅
    ModuleCat.of
      (Ring.DirectLimit (ringStageSystem F) (fun i j hij ↦ ringStageMap F i j hij))
      (Fin n →
        Ring.DirectLimit (ringStageSystem F) (fun i j hij ↦ ringStageMap F i j hij)) :=
  -- Proof comment: tensoring a finite product with the direct-limit ring is computed componentwise,
  -- and each tensor factor `R∞ ⊗[R_i] R_i` collapses by the right-unit equivalence.
  ((TensorProduct.piScalarRight
        (F.obj i)
        (Ring.DirectLimit (ringStageSystem F) (fun i j hij ↦ ringStageMap F i j hij))
        (F.obj i)
        (Fin n)).trans
      (LinearEquiv.piCongrRight fun _ : Fin n ↦
        TensorProduct.rid
          (F.obj i)
          (Ring.DirectLimit (ringStageSystem F) (fun i j hij ↦ ringStageMap F i j hij)))).toModuleIso

/-- Helper for Lemma 15.75.18: a bounded finite-projective strict complex should compute derived
scalar extension by ordinary termwise scalar extension. -/
private theorem derivedTensorWithAlgebra_Q_obj_iso_of_isBoundedFiniteProjective
    {R A : Type u} [CommRing R] [CommRing A]
    (σ : R →+* A)
    (L : CochainComplex (ModuleCat R) ℤ)
    (hL : CochainComplex.IsBoundedFiniteProjective L) :
    (derivedTensorWithAlgebra σ).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.extendScalars σ).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) := by
  -- Route correction: reuse the earlier bounded-above termwise-flat comparison from
  -- `Lemma_15_67_13` instead of rebuilding a new derived-counit computation here.
  letI : Algebra R A := σ.toAlgebra
  rcases hL.bounded with ⟨_, b, _, hLLE⟩
  have hLFlat : L.IsTermwiseFlat := by
    -- Proof comment: each term is projective, hence flat, so the whole strict complex is
    -- termwise flat.
    intro n
    let _ : Module.Projective R (L.X n) := hL.projective n
    infer_instance
  -- Proof comment: the bounded-above termwise-flat model computes derived scalar extension by the
  -- canonical comparison from Lemma `15.67.13`.
  simpa using
    (CategoryTheory.derivedTensorWithAlgebra_obj_iso_of_termwiseFlat_of_isStrictlyLE
      (A := R) (B := A) (E := L) hLFlat hLLE)

/-- Helper for Lemma 15.75.18: a bounded finite-projective complex over the filtered colimit ring
should descend to one stage together with a strict scalar-extension isomorphism. -/
private theorem bounded_finite_projective_complex_descends_to_stage
    (P∞ : CochainComplex (ModuleCat (ringColimit F)) ℤ)
    (hP∞ : CochainComplex.IsBoundedFiniteProjective P∞) :
    ∃ (i : I) (Pi : CochainComplex (ModuleCat (F.obj i)) ℤ),
      CochainComplex.IsBoundedFiniteProjective Pi ∧
        Nonempty (((extendScalarsComplexToColimit F i).obj Pi) ≅ P∞) := by
  -- TODO: use `ringColimitIsoRingDirectLimit` to rewrite the ambient colimit ring as the explicit
  -- direct limit of the stage system. For each nonzero term, first descend the underlying
  -- finitely presented module, then descend the split cover maps to a common later stage and
  -- recover finiteness/projectivity there with `finite_projective_of_split_finite_free`; the
  -- finite free side is normalized by `directLimit_free_baseChange_iso`. After that, descend the
  -- finitely many differentials and stabilize the finitely many relations `d ≫ d = 0` at one
  -- common later stage.
  sorry

-- Proof sketch: represent `K` by a bounded complex of finite projective modules over the colimit
-- ring, descend the finitely many finite projective terms to some stage using the filtered-colimit
-- results for finitely presented modules, and then descend the whole bounded complex.
/-- Lemma 15.75.18 (1): any perfect complex over a filtered colimit of commutative rings descends
to a perfect complex over some stage. -/
theorem exists_perfectComplex_stage_of_isPerfect
    (K : DerivedCategory (ModuleCat (ringColimit F)))
    (hK : K.IsPerfect) :
    ∃ (i : I) (Ki : DerivedCategory (ModuleCat (F.obj i))),
      Ki.IsPerfect ∧
        IsIsomorphic K ((baseChangeToColimit F i).obj Ki) := by
  rcases hK with ⟨P∞, eK, hP∞⟩
  obtain ⟨i, Pi, hPi, hdesc⟩ :=
    bounded_finite_projective_complex_descends_to_stage (F := F) P∞ hP∞
  rcases hdesc with ⟨ePi⟩
  let Ki : DerivedCategory (ModuleCat (F.obj i)) := DerivedCategory.Q.obj Pi
  have hKi : Ki.IsPerfect := by
    -- Proof comment: the descended stage complex is again bounded finite-projective.
    simpa [Ki] using q_obj_isPerfect_of_isBoundedFiniteProjective Pi hPi
  have hBase :
      ((baseChangeToColimit F i).obj Ki) ≅
        DerivedCategory.Q.obj ((extendScalarsComplexToColimit F i).obj Pi) := by
    -- Proof comment: this is the strict bounded finite-projective scalar-extension comparison for
    -- the descended representative.
    simpa [Ki, baseChangeToColimit, extendScalarsComplexToColimit] using
      (derivedTensorWithAlgebra_Q_obj_iso_of_isBoundedFiniteProjective
        ((colimit.ι F i).hom) Pi hPi)
  refine ⟨i, Ki, hKi, ?_⟩
  -- Proof comment: compare `K` to the scalar extension of `Ki` by chaining the original perfect
  -- representative, the strict descended complex isomorphism, and the K-flat comparison.
  exact ⟨eK ≪≫ (DerivedCategory.Q.mapIso ePi).symm ≪≫ hBase.symm⟩

section

variable (i₀ : I)

/-- Base change from the fixed stage `R₀` to a later stage `R_j`. -/
private abbrev stageBaseChange (j : Set.Ici i₀) :
    DerivedCategory (ModuleCat (F.obj i₀)) ⥤
      DerivedCategory (ModuleCat (F.obj j.1)) :=
  derivedTensorWithAlgebra (F.map (homOfLE j.2)).hom

/-- Base change from `R₀` to the filtered colimit ring. -/
private abbrev colimitBaseChange :
    DerivedCategory (ModuleCat (F.obj i₀)) ⥤
      DerivedCategory (ModuleCat (ringColimit F)) :=
  baseChangeToColimit F i₀

/-- Helper for Lemma 15.75.18: this is the homotopy-level scalar-extension bridge from the fixed
stage `R₀` to the colimit ring. It is the direct source functor whose total left derived functor
is `colimitBaseChange`. -/
private noncomputable abbrev stageToColimitHomotopyFunctor :
    HomotopyCategory (ModuleCat (F.obj i₀)) (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleCat (ringColimit F)) :=
  let F₀ : ModuleCat (F.obj i₀) ⥤ ModuleCat (ringColimit F) :=
    ModuleCat.extendScalars ((colimit.ι F i₀).hom)
  letI : F₀.Additive :=
    (ModuleCat.extendRestrictScalarsAdj ((colimit.ι F i₀).hom)).left_adjoint_additive
  mapHomotopyCategoryToDerived F₀

/-- Helper for Lemma 15.75.18: the direct homotopy scalar-extension bridge
`R₀ → colim_i R_i` admits the expected total left derived functor. -/
private theorem stageToColimitHomotopyFunctor_hasLeftDerivedFunctor :
    (stageToColimitHomotopyFunctor F i₀).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat (F.obj i₀)) (ComplexShape.up ℤ)) := by
  -- The direct `R₀ → colim` scalar extension is the same owner construction as in `15_60_1_1`.
  simpa [stageToColimitHomotopyFunctor, mapHomotopyCategoryToDerived] using
    (extendScalarsToDerived_hasLeftDerivedFunctor ((colimit.ι F i₀).hom))

/-- Base change from a stage `R_j` to the filtered colimit ring. -/
private abbrev stageToColimitBaseChange (j : Set.Ici i₀) :
    DerivedCategory (ModuleCat (F.obj j.1)) ⥤
      DerivedCategory (ModuleCat (ringColimit F)) :=
  baseChangeToColimit F j.1

/-- Base change along a transition map `R_j → R_k`. -/
private abbrev stageTransitionBaseChange {j k : Set.Ici i₀} (hjk : j ⟶ k) :
    DerivedCategory (ModuleCat (F.obj j.1)) ⥤
      DerivedCategory (ModuleCat (F.obj k.1)) :=
  derivedTensorWithAlgebra (F.map hjk).hom

omit [IsFiltered I] in
private theorem stageToColimitBaseChange_comp_eq (j : Set.Ici i₀) :
    (colimit.ι F j.1).hom.comp (F.map (homOfLE j.2)).hom = (colimit.ι F i₀).hom := by
  rw [← CommRingCat.hom_comp]
  simpa using congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE j.2))

omit [IsFiltered I] [HasColimit F] in
private theorem stageTransitionBaseChange_comp_eq {j k : Set.Ici i₀} (hjk : j ⟶ k) :
    (F.map hjk).hom.comp (F.map (homOfLE j.2)).hom = (F.map (homOfLE k.2)).hom := by
  -- The direct map `R₀ → R_k` is the functorial composite `R₀ → R_j → R_k`.
  rw [← CommRingCat.hom_comp]
  have hcomp : homOfLE j.2 ≫ hjk = homOfLE k.2 := Subsingleton.elim _ _
  rw [← F.map_comp, hcomp]

/-- The canonical comparison between base change `R₀ → R_j → \operatorname{colim} R_i` and
direct base change `R₀ → \operatorname{colim} R_i`. -/
private noncomputable abbrev stageToColimitBaseChangeIso (j : Set.Ici i₀) :
    stageBaseChange F i₀ j ⋙ stageToColimitBaseChange F i₀ j ≅ colimitBaseChange F i₀ :=
  derivedTensorWithAlgebraCompIso
    (F.map (homOfLE j.2)).hom
    (colimit.ι F j.1).hom
    (colimit.ι F i₀).hom
    (stageToColimitBaseChange_comp_eq F i₀ j)

/-- The canonical comparison between base change `R₀ → R_j → R_k` and direct base change
`R₀ → R_k`. -/
private noncomputable abbrev stageTransitionBaseChangeIso {j k : Set.Ici i₀} (hjk : j ⟶ k) :
    stageBaseChange F i₀ j ⋙ stageTransitionBaseChange F i₀ hjk ≅ stageBaseChange F i₀ k :=
  derivedTensorWithAlgebraCompIso
    (F.map (homOfLE j.2)).hom
    (F.map hjk).hom
    (F.map (homOfLE k.2)).hom
    (stageTransitionBaseChange_comp_eq F i₀ hjk)

omit [IsFiltered I] in
private theorem stageToColimitThroughTransitionBaseChange_comp_eq
    {j k : Set.Ici i₀} (hjk : j ⟶ k) :
    (colimit.ι F k.1).hom.comp (F.map hjk).hom = (colimit.ι F j.1).hom := by
  rw [← CommRingCat.hom_comp]
  simpa using congrArg CommRingCat.Hom.hom (colimit.w F hjk)

/-- The canonical comparison between base change `R_j → R_k → \operatorname{colim} R_i` and
direct base change `R_j → \operatorname{colim} R_i`. -/
private noncomputable abbrev stageToColimitThroughTransitionBaseChangeIso
    {j k : Set.Ici i₀} (hjk : j ⟶ k) :
    stageTransitionBaseChange F i₀ hjk ⋙ stageToColimitBaseChange F i₀ k ≅
      stageToColimitBaseChange F i₀ j :=
  derivedTensorWithAlgebraCompIso
    (F.map hjk).hom
    (colimit.ι F k.1).hom
    (colimit.ι F j.1).hom
    (stageToColimitThroughTransitionBaseChange_comp_eq F i₀ hjk)

/-- The canonical image in the colimit Hom-set of a stagewise morphism. -/
noncomputable def stageToColimitHomMap (j : Set.Ici i₀)
    {K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀))}
    (β : (stageBaseChange F i₀ j).obj K₀ ⟶ (stageBaseChange F i₀ j).obj L₀) :
    (colimitBaseChange F i₀).obj K₀ ⟶ (colimitBaseChange F i₀).obj L₀ :=
  let e := stageToColimitBaseChangeIso F i₀ j
  (e.app K₀).inv ≫ (stageToColimitBaseChange F i₀ j).map β ≫ (e.app L₀).hom

/-- The canonical image in a later-stage Hom-set of a stagewise morphism. -/
noncomputable def stageTransitionHomMap {j k : Set.Ici i₀} (hjk : j ⟶ k)
    {K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀))}
    (β : (stageBaseChange F i₀ j).obj K₀ ⟶ (stageBaseChange F i₀ j).obj L₀) :
    (stageBaseChange F i₀ k).obj K₀ ⟶ (stageBaseChange F i₀ k).obj L₀ :=
  let e := stageTransitionBaseChangeIso F i₀ hjk
  (e.app K₀).inv ≫ (stageTransitionBaseChange F i₀ hjk).map β ≫ (e.app L₀).hom

/-- Helper for Lemma 15.75.18: transporting a stage morphism first to a later stage and then to
the colimit is a single conjugation by the whiskered transition comparison. -/
private theorem stageToColimitHomMap_through_whiskered_transition
    {K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀))}
    {j k : Set.Ici i₀} (hjk : j ⟶ k)
    (β : (stageBaseChange F i₀ j).obj K₀ ⟶ (stageBaseChange F i₀ j).obj L₀) :
    stageToColimitHomMap F i₀ k (stageTransitionHomMap F i₀ hjk β) =
      let eK :=
        (stageToColimitBaseChange F i₀ k).mapIso
          ((stageTransitionBaseChangeIso F i₀ hjk).app K₀) ≪≫
            (stageToColimitBaseChangeIso F i₀ k).app K₀
      let eL :=
        (stageToColimitBaseChange F i₀ k).mapIso
          ((stageTransitionBaseChangeIso F i₀ hjk).app L₀) ≪≫
            (stageToColimitBaseChangeIso F i₀ k).app L₀
      eK.inv ≫
        ((stageTransitionBaseChange F i₀ hjk ⋙ stageToColimitBaseChange F i₀ k).map β) ≫
          eL.hom := by
  -- Collapse the two successive conjugations into the single whiskered comparison iso.
  simpa [stageToColimitHomMap, stageTransitionHomMap, Functor.mapIso, Functor.comp_map,
    Category.assoc]

/-- Helper for Lemma 15.75.18: after regrouping the three-step scalar extension and replacing the
last two steps by the direct stage-to-colimit comparison, the resulting conjugation is the
original direct map to the colimit. -/
private theorem stageToColimitHomMap_through_stageToColimitComparison
    {K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀))}
    {j k : Set.Ici i₀} (hjk : j ⟶ k)
    (β : (stageBaseChange F i₀ j).obj K₀ ⟶ (stageBaseChange F i₀ j).obj L₀) :
    stageToColimitHomMap F i₀ j β =
      let eK :=
        (stageToColimitThroughTransitionBaseChangeIso F i₀ hjk).app
          ((stageBaseChange F i₀ j).obj K₀) ≪≫
            (stageToColimitBaseChangeIso F i₀ j).app K₀
      let eL :=
        (stageToColimitThroughTransitionBaseChangeIso F i₀ hjk).app
          ((stageBaseChange F i₀ j).obj L₀) ≪≫
            (stageToColimitBaseChangeIso F i₀ j).app L₀
      eK.inv ≫
        ((stageTransitionBaseChange F i₀ hjk ⋙ stageToColimitBaseChange F i₀ k).map β) ≫
          eL.hom := by
  -- Regroup the three-step scalar extension, then use naturality of the direct `R_j → colim`
  -- comparison to recover the original transport formula.
  dsimp [stageToColimitHomMap]
  have hmiddle :
      (stageToColimitBaseChange F i₀ j).map β =
        ((stageToColimitThroughTransitionBaseChangeIso F i₀ hjk).app
            ((stageBaseChange F i₀ j).obj K₀)).inv ≫
          ((stageTransitionBaseChange F i₀ hjk ⋙ stageToColimitBaseChange F i₀ k).map β) ≫
            ((stageToColimitThroughTransitionBaseChangeIso F i₀ hjk).app
              ((stageBaseChange F i₀ j).obj L₀)).hom := by
    -- This is the naturality square of the direct `R_j → colim` comparison iso.
    have hnat :=
      (stageToColimitThroughTransitionBaseChangeIso F i₀ hjk).hom.naturality β
    have hmiddle' :
        ((stageToColimitThroughTransitionBaseChangeIso F i₀ hjk).app
            ((stageBaseChange F i₀ j).obj K₀)).inv ≫
          ((stageTransitionBaseChange F i₀ hjk ⋙ stageToColimitBaseChange F i₀ k).map β) ≫
            ((stageToColimitThroughTransitionBaseChangeIso F i₀ hjk).app
              ((stageBaseChange F i₀ j).obj L₀)).hom =
          (stageToColimitBaseChange F i₀ j).map β := by
      calc
        ((stageToColimitThroughTransitionBaseChangeIso F i₀ hjk).app
            ((stageBaseChange F i₀ j).obj K₀)).inv ≫
          ((stageTransitionBaseChange F i₀ hjk ⋙ stageToColimitBaseChange F i₀ k).map β) ≫
            ((stageToColimitThroughTransitionBaseChangeIso F i₀ hjk).app
              ((stageBaseChange F i₀ j).obj L₀)).hom =
            ((stageToColimitThroughTransitionBaseChangeIso F i₀ hjk).app
                ((stageBaseChange F i₀ j).obj K₀)).inv ≫
              ((stageToColimitThroughTransitionBaseChangeIso F i₀ hjk).app
                ((stageBaseChange F i₀ j).obj K₀)).hom ≫
                (stageToColimitBaseChange F i₀ j).map β := by
              simpa [Category.assoc] using
                congrArg
                  (fun f ↦
                    ((stageToColimitThroughTransitionBaseChangeIso F i₀ hjk).app
                        ((stageBaseChange F i₀ j).obj K₀)).inv ≫ f)
                  hnat
        _ = (stageToColimitBaseChange F i₀ j).map β := by
              simpa using
                (Iso.inv_hom_id_assoc
                  ((stageToColimitThroughTransitionBaseChangeIso F i₀ hjk).app
                    ((stageBaseChange F i₀ j).obj K₀))
                  ((stageToColimitBaseChange F i₀ j).map β))
    exact hmiddle'.symm
  rw [hmiddle]
  simp [Category.assoc]

/-- Helper for Lemma 15.75.18: whiskering the forward map of `leftDerivedNatIso` by the
localization functor and then composing with the target counit recovers the original
prederived comparison morphism. -/
private theorem Functor.leftDerivedNatIso_hom_assoc_totalLeftDerivedCounit
    {C D H : Type*} [Category C] [Category D] [Category H]
    {L : C ⥤ D} {W : MorphismProperty C} [L.IsLocalization W]
    {F F' : C ⥤ H} {LF LF' : D ⥤ H}
    {α : L ⋙ LF ⟶ F} {α' : L ⋙ LF' ⟶ F'}
    [LF.IsLeftDerivedFunctor α W] [LF'.IsLeftDerivedFunctor α' W]
    (e : F' ≅ F) :
    Functor.whiskerLeft L (Functor.leftDerivedNatIso LF' LF α' α W e).hom ≫ α =
      α' ≫ e.hom := by
  -- Expand `leftDerivedNatIso` to the underlying `leftDerivedNatTrans`, then use the defining
  -- left-derived factorization identity.
  simpa [Functor.leftDerivedNatIso] using
    (Functor.leftDerivedNatTrans_fac LF' LF α' α W e.hom)

/-- Helper for Lemma 15.75.18: after whiskering by `Qh` and postcomposing with the direct
colimit counit, the two parenthesizations of the three-step scalar-extension comparison become a
single homotopy-level normalization problem. -/
private theorem stageToColimitComparison_assoc_coherence_qh_normalized
    {j k : Set.Ici i₀} (hjk : j ⟶ k) :
    let qhR₀ :
        HomotopyCategory (ModuleCat (F.obj i₀)) (ComplexShape.up ℤ) ⥤
          DerivedCategory (ModuleCat (F.obj i₀)) :=
      DerivedCategory.Qh
    let qisR₀ :=
      HomotopyCategory.quasiIso (ModuleCat (F.obj i₀)) (ComplexShape.up ℤ)
    letI :
        (stageToColimitHomotopyFunctor F i₀).HasLeftDerivedFunctor qisR₀ :=
      stageToColimitHomotopyFunctor_hasLeftDerivedFunctor (F := F) (i₀ := i₀)
    Functor.whiskerLeft qhR₀
        (((Functor.isoWhiskerRight (stageTransitionBaseChangeIso F i₀ hjk)
              (stageToColimitBaseChange F i₀ k)) ≪≫
            stageToColimitBaseChangeIso F i₀ k).hom) ≫
          Functor.totalLeftDerivedCounit
            (stageToColimitHomotopyFunctor F i₀) qhR₀ qisR₀ =
      Functor.whiskerLeft qhR₀
        (((Functor.isoWhiskerLeft (stageBaseChange F i₀ j)
              (stageToColimitThroughTransitionBaseChangeIso F i₀ hjk)) ≪≫
            stageToColimitBaseChangeIso F i₀ j).hom) ≫
          Functor.totalLeftDerivedCounit
            (stageToColimitHomotopyFunctor F i₀) qhR₀ qisR₀ := by
  -- Route correction: the opaque tail is the `leftDerivedNatIso` factor inside
  -- `derivedTensorWithAlgebraCompIso`. The helper above reduces that tail to the visible
  -- homotopy-level comparison data before the three stage/colimit ring-map equalities are used.
  -- Proof comment: after unfolding the three comparison isomorphisms, each side is a
  -- `leftDerivedLift` followed by a `leftDerivedNatIso`. Composing with the total-left-derived
  -- counit removes the `leftDerivedNatIso` tail, so both parenthesizations reduce to the same
  -- homotopy-level scalar-extension comparison determined by the equal ring-map composites.
  dsimp [stageTransitionBaseChangeIso, stageToColimitBaseChangeIso,
    stageToColimitThroughTransitionBaseChangeIso]
  rw [Functor.leftDerivedNatIso_hom_assoc_totalLeftDerivedCounit,
    Functor.leftDerivedNatIso_hom_assoc_totalLeftDerivedCounit]
  simp [derivedTensorWithAlgebraCompIso, stageTransitionBaseChange_comp_eq,
    stageToColimitThroughTransitionBaseChange_comp_eq, stageToColimitBaseChange_comp_eq,
    Category.assoc]

/-- Helper for Lemma 15.75.18: the direct stage-to-colimit left derived functor is determined by
its `Qh`-whiskered counit composite. This packages the universal-property ext step so later
proofs can work entirely with the normalized homotopy-side comparison. -/
private theorem leftDerived_hom_ext_of_qh_counit_equality
    {G :
      DerivedCategory (ModuleCat (F.obj i₀)) ⥤
        DerivedCategory (ModuleCat (ringColimit F))}
    (η θ : G ⟶ colimitBaseChange F i₀) :
    let qhR₀ :
        HomotopyCategory (ModuleCat (F.obj i₀)) (ComplexShape.up ℤ) ⥤
          DerivedCategory (ModuleCat (F.obj i₀)) :=
      DerivedCategory.Qh
    let qisR₀ :=
      HomotopyCategory.quasiIso (ModuleCat (F.obj i₀)) (ComplexShape.up ℤ)
    letI :
        (stageToColimitHomotopyFunctor F i₀).HasLeftDerivedFunctor qisR₀ :=
      stageToColimitHomotopyFunctor_hasLeftDerivedFunctor (F := F) (i₀ := i₀)
    Functor.whiskerLeft qhR₀ η ≫
        Functor.totalLeftDerivedCounit
          (stageToColimitHomotopyFunctor F i₀) qhR₀ qisR₀ =
      Functor.whiskerLeft qhR₀ θ ≫
        Functor.totalLeftDerivedCounit
          (stageToColimitHomotopyFunctor F i₀) qhR₀ qisR₀ →
      η = θ := by
  intro qhR₀ qisR₀ hηθ
  letI :
      (stageToColimitHomotopyFunctor F i₀).HasLeftDerivedFunctor qisR₀ :=
    stageToColimitHomotopyFunctor_hasLeftDerivedFunctor (F := F) (i₀ := i₀)
  -- Upgrade the direct stage-to-colimit base change to the canonical left-derived owner.
  letI :
      (colimitBaseChange F i₀).IsLeftDerivedFunctor
        (Functor.totalLeftDerivedCounit
          (stageToColimitHomotopyFunctor F i₀) qhR₀ qisR₀)
        qisR₀ := by
    change
      (Functor.totalLeftDerived
        (stageToColimitHomotopyFunctor F i₀) qhR₀ qisR₀).IsLeftDerivedFunctor
          (Functor.totalLeftDerivedCounit
            (stageToColimitHomotopyFunctor F i₀) qhR₀ qisR₀)
          qisR₀
    infer_instance
  -- The right Kan extension universal property says that equality after whiskering by `Qh`
  -- and composing with the counit already determines the map into the derived functor.
  let hkan :
      (colimitBaseChange F i₀).IsRightKanExtension
        (Functor.totalLeftDerivedCounit
          (stageToColimitHomotopyFunctor F i₀) qhR₀ qisR₀) :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension
      (LF := colimitBaseChange F i₀)
      (α := Functor.totalLeftDerivedCounit
        (stageToColimitHomotopyFunctor F i₀) qhR₀ qisR₀)
      (W := qisR₀)
  obtain ⟨huniv⟩ := hkan.nonempty_isUniversal
  exact huniv.hom_ext hηθ

/-- Helper for Lemma 15.75.18: the two canonical comparison isomorphisms from the three-step
scalar extension `R₀ → R_j → R_k → colim R_i` to the direct scalar extension
`R₀ → colim R_i` agree. -/
private theorem stageToColimitComparison_assoc_coherence_hom
    {X : DerivedCategory (ModuleCat (F.obj i₀))}
    {j k : Set.Ici i₀} (hjk : j ⟶ k) :
    (((stageToColimitBaseChange F i₀ k).mapIso
          ((stageTransitionBaseChangeIso F i₀ hjk).app X) ≪≫
        (stageToColimitBaseChangeIso F i₀ k).app X).hom) =
      (((stageToColimitThroughTransitionBaseChangeIso F i₀ hjk).app
            ((stageBaseChange F i₀ j).obj X) ≪≫
          (stageToColimitBaseChangeIso F i₀ j).app X).hom) := by
  let qhR₀ :
      HomotopyCategory (ModuleCat (F.obj i₀)) (ComplexShape.up ℤ) ⥤
        DerivedCategory (ModuleCat (F.obj i₀)) :=
    DerivedCategory.Qh
  let qisR₀ :=
    HomotopyCategory.quasiIso (ModuleCat (F.obj i₀)) (ComplexShape.up ℤ)
  letI :
      (stageToColimitHomotopyFunctor F i₀).HasLeftDerivedFunctor qisR₀ :=
    stageToColimitHomotopyFunctor_hasLeftDerivedFunctor (F := F) (i₀ := i₀)
  have hnormalized :
      Functor.whiskerLeft qhR₀
          (((Functor.isoWhiskerRight (stageTransitionBaseChangeIso F i₀ hjk)
                (stageToColimitBaseChange F i₀ k)) ≪≫
              stageToColimitBaseChangeIso F i₀ k).hom) ≫
            Functor.totalLeftDerivedCounit
              (stageToColimitHomotopyFunctor F i₀) qhR₀ qisR₀ =
        Functor.whiskerLeft qhR₀
          (((Functor.isoWhiskerLeft (stageBaseChange F i₀ j)
                (stageToColimitThroughTransitionBaseChangeIso F i₀ hjk)) ≪≫
              stageToColimitBaseChangeIso F i₀ j).hom) ≫
            Functor.totalLeftDerivedCounit
              (stageToColimitHomotopyFunctor F i₀) qhR₀ qisR₀ :=
    stageToColimitComparison_assoc_coherence_qh_normalized (F := F) (i₀ := i₀) hjk
  -- Route correction: the app-level equality now depends only on lifting the normalized
  -- homotopy-side equality through the left-derived uniqueness principle.
  have hcomparison :
      (((Functor.isoWhiskerRight (stageTransitionBaseChangeIso F i₀ hjk)
            (stageToColimitBaseChange F i₀ k)) ≪≫
          stageToColimitBaseChangeIso F i₀ k).hom) =
        (((Functor.isoWhiskerLeft (stageBaseChange F i₀ j)
              (stageToColimitThroughTransitionBaseChangeIso F i₀ hjk)) ≪≫
            stageToColimitBaseChangeIso F i₀ j).hom) := by
    -- Compare the two derived comparison maps at the natural-transformation level first.
    apply leftDerived_hom_ext_of_qh_counit_equality (F := F) (i₀ := i₀)
    exact hnormalized
  -- Evaluate the recovered natural-transformation equality at the object `X`.
  simpa using congrArg (fun τ ↦ τ.app X) hcomparison

/-- Helper for Lemma 15.75.18: once the comparison morphisms agree, the corresponding three-step
scalar-extension comparison isomorphisms are equal. -/
private theorem stageToColimitComparison_assoc_coherence
    {X : DerivedCategory (ModuleCat (F.obj i₀))}
    {j k : Set.Ici i₀} (hjk : j ⟶ k) :
    ((stageToColimitBaseChange F i₀ k).mapIso
        ((stageTransitionBaseChangeIso F i₀ hjk).app X) ≪≫
      (stageToColimitBaseChangeIso F i₀ k).app X) =
      ((stageToColimitThroughTransitionBaseChangeIso F i₀ hjk).app
          ((stageBaseChange F i₀ j).obj X) ≪≫
        (stageToColimitBaseChangeIso F i₀ j).app X) := by
  -- Reduce the comparison of isomorphisms to the equality of their forward morphisms.
  apply Iso.ext
  exact stageToColimitComparison_assoc_coherence_hom (F := F) (i₀ := i₀) (X := X) hjk

-- Proof sketch: the colimit cocone relation `R_j → R_k → colim F = R_j → colim F` gives a
-- canonical comparison between the two iterated scalar-extension functors from stage `j` to the
-- colimit. Naturality of the comparison isomorphisms then shows that passing from stage `j`
-- directly to the colimit agrees with first base-changing to a later stage `k` and then to the
-- colimit.
/-- The canonical images in the colimit Hom-set are compatible with the transition maps between
stages. This is the coherence needed for the source-facing filtered Hom-colimit comparison in
Lemma `15.75.18 (2)`. -/
theorem stageToColimitHomMap_transition
    {K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀))}
    {j k : Set.Ici i₀} (hjk : j ⟶ k)
    (β : (stageBaseChange F i₀ j).obj K₀ ⟶ (stageBaseChange F i₀ j).obj L₀) :
    stageToColimitHomMap F i₀ k (stageTransitionHomMap F i₀ hjk β) =
      stageToColimitHomMap F i₀ j β := by
  -- Route correction: isolate the formal transport identities first, so the only remaining issue
  -- is the coherence between the two canonical comparison isomorphisms for the three-step scalar
  -- extension `R₀ → R_j → R_k → colim`.
  rw [stageToColimitHomMap_through_whiskered_transition F i₀ hjk β]
  rw [stageToColimitHomMap_through_stageToColimitComparison F i₀ hjk β]
  -- The remaining input is exactly the stage-specialized associativity coherence for the three
  -- comparison isomorphisms.
  have hK := stageToColimitComparison_assoc_coherence (F := F) (i₀ := i₀) (X := K₀) hjk
  have hL := stageToColimitComparison_assoc_coherence (F := F) (i₀ := i₀) (X := L₀) hjk
  rw [hK, hL]
  rfl

/-- Helper for Lemma 15.75.18: a morphism from a bounded-above projective source complex into a
derived object can be represented by a strict cochain map to the chosen `Q.objPreimage`
representative. -/
private theorem exists_strict_preimage_map_of_projectiveMinus
    {R : Type u} [CommRing R]
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    {L : DerivedCategory (ModuleCat R)}
    (α : DerivedCategory.Q.obj (P : CochainComplex (ModuleCat R) ℤ) ⟶ L) :
    ∃ f : (P : CochainComplex (ModuleCat R) ℤ) ⟶ DerivedCategory.Q.objPreimage L,
      α = DerivedCategory.Q.map f ≫ (DerivedCategory.Q.objObjPreimageIso L).hom := by
  let β :
      DerivedCategory.Q.obj (P : CochainComplex (ModuleCat R) ℤ) ⟶
        DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage L) :=
    α ≫ (DerivedCategory.Q.objObjPreimageIso L).inv
  obtain ⟨M, σ, hσ, f, hβ⟩ := DerivedCategory.right_fac β
  have hσ_quasi : QuasiIso σ := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso] at hσ
    exact hσ
  letI : QuasiIso σ := hσ_quasi
  obtain ⟨g, hg⟩ :=
    CochainComplex.exists_homotopy_factor_through_quasiIso_from_boundedAbove_projective
      P σ (𝟙 (P : CochainComplex (ModuleCat R) ℤ))
  obtain ⟨hg⟩ := hg
  have hgQ :
      DerivedCategory.Q.map g ≫ DerivedCategory.Q.map σ =
        𝟙 (DerivedCategory.Q.obj (P : CochainComplex (ModuleCat R) ℤ)) := by
    -- Proof comment: pass the homotopy `g ≫ σ ∼ 𝟙` through the homotopy quotient and then through
    -- `Qh`, since `DerivedCategory.Q` is exactly the composite `quotient ⋙ Qh`.
    have hquot :
        (HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map (g ≫ σ) =
          (HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map
            (𝟙 (P : CochainComplex (ModuleCat R) ℤ)) := by
      exact HomotopyCategory.eq_of_homotopy _ _ hg
    simpa [DerivedCategory.Q, Functor.comp_map, Functor.map_comp] using
      congrArg
        (fun k ↦
          (DerivedCategory.Qh :
            HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ) ⥤
              DerivedCategory (ModuleCat R)).map k)
        hquot
  have hβ_strict :
      β = DerivedCategory.Q.map (g ≫ f) := by
    -- Proof comment: `right_fac` writes `β` with a quasi-isomorphic denominator `σ`; the
    -- projective-source lift of the identity cancels that denominator.
    calc
      β = 𝟙 _ ≫ β := by simp
      _ = (DerivedCategory.Q.map g ≫ DerivedCategory.Q.map σ) ≫ β := by
            rw [hgQ]
      _ = DerivedCategory.Q.map g ≫ (DerivedCategory.Q.map σ ≫ β) := by
            simp [Category.assoc]
      _ =
          DerivedCategory.Q.map g ≫
            (DerivedCategory.Q.map σ ≫
              (inv (DerivedCategory.Q.map σ) ≫ DerivedCategory.Q.map f)) := by
            rw [hβ]
      _ = DerivedCategory.Q.map g ≫ DerivedCategory.Q.map f := by
            simp [Category.assoc]
      _ = DerivedCategory.Q.map (g ≫ f) := by
            simp [Functor.map_comp]
  refine ⟨g ≫ f, ?_⟩
  -- Proof comment: now restore the target isomorphism `Q.obj (Q.objPreimage L) ≅ L`.
  calc
    α = β ≫ (DerivedCategory.Q.objObjPreimageIso L).hom := by
          simp [β, Category.assoc]
    _ = DerivedCategory.Q.map (g ≫ f) ≫ (DerivedCategory.Q.objObjPreimageIso L).hom := by
          rw [hβ_strict]

/-- Helper for Lemma 15.75.18: equality of derived morphisms out of a bounded-above projective
source complex is already equality up to homotopy on strict representatives. -/
private theorem homotopic_of_equal_Q_map_from_projectiveMinus
    {R : Type u} [CommRing R]
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    {L : CochainComplex (ModuleCat R) ℤ}
    {f g : (P : CochainComplex (ModuleCat R) ℤ) ⟶ L}
    (hfg : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    Nonempty (Homotopy f g) := by
  let Q := HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
  have hQmap :
      (DerivedCategory.Qh :
        HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ) ⥤
          DerivedCategory (ModuleCat R)).map (Q.map f) =
        (DerivedCategory.Qh :
          HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ) ⥤
            DerivedCategory (ModuleCat R)).map (Q.map g) := by
    -- Proof comment: rewrite `Q.map` through the factorization `quotient ⋙ Qh`.
    simpa [Q, DerivedCategory.Q, Functor.comp_map] using hfg
  have hbij :=
    CochainComplex.homotopyCategory_to_derived_bijective_of_boundedAbove_projective P L
  have hquot : Q.map f = Q.map g :=
    hbij.injective hQmap
  -- Proof comment: equality in the homotopy category is exactly a homotopy of strict cochain
  -- maps.
  exact ⟨HomotopyCategory.homotopyOfEq _ _ hquot⟩

/-- Helper for Lemma 15.75.18: the two source-facing Hom-colimit assertions for a perfect source
should be proved together from one strict-model package. The eventual proof will choose a bounded
finite-projective representative of `K₀`, resolve `L₀` by a strict K-flat complex, compare the
degree-zero represented-Hom rows over the tail system `j : Set.Ici i₀`, and then read off both
surjectivity and eventual equality from the same left-homology colimit statement. -/
private theorem stage_factorization_and_eventual_eq_of_isPerfect
    (K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀))) (hK₀ : K₀.IsPerfect) :
    (∀ α : (colimitBaseChange F i₀).obj K₀ ⟶ (colimitBaseChange F i₀).obj L₀,
      ∃ (j : Set.Ici i₀)
        (β : (stageBaseChange F i₀ j).obj K₀ ⟶ (stageBaseChange F i₀ j).obj L₀),
        α = stageToColimitHomMap F i₀ j β) ∧
    (∀ (j : Set.Ici i₀)
      (β₁ β₂ : (stageBaseChange F i₀ j).obj K₀ ⟶ (stageBaseChange F i₀ j).obj L₀),
      stageToColimitHomMap F i₀ j β₁ = stageToColimitHomMap F i₀ j β₂ →
        ∃ (k : Set.Ici i₀) (hjk : j ⟶ k),
          stageTransitionHomMap F i₀ hjk β₁ =
            stageTransitionHomMap F i₀ hjk β₂) := by
  -- TODO: follow the source proof literally. First choose a bounded finite-projective strict
  -- representative of `K₀` and a strict K-flat model of `L₀`; then identify derived morphisms
  -- with degree-zero left homology of the represented-Hom rows, apply filtered-colimit exactness
  -- to that three-term row, and finally transport the resulting factorization and eventual
  -- equality statements back to the source-facing stage and colimit Hom-sets.
  sorry

-- Proof sketch: represent `K₀` by a bounded complex of finite projective modules over `R_{i₀}`,
-- compute the target morphism in the derived category by a bounded Hom complex after base change
-- to the colimit ring, and descend the finitely many terms of that calculation to a sufficiently
-- large stage `R_j`.
/-- Lemma 15.75.18 (2), surjectivity part: every morphism after base change from `R_{i₀}` to the
filtered colimit ring comes from some later stage. -/
theorem exists_stage_factorization_of_isPerfect
    (K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀))) (hK₀ : K₀.IsPerfect)
    (α : (colimitBaseChange F i₀).obj K₀ ⟶ (colimitBaseChange F i₀).obj L₀) :
    ∃ (j : Set.Ici i₀)
      (β : (stageBaseChange F i₀ j).obj K₀ ⟶ (stageBaseChange F i₀ j).obj L₀),
      α = stageToColimitHomMap F i₀ j β := by
  -- Proof comment: the surjectivity statement is the first projection of the combined strict-model
  -- package above, so the public theorem stays aligned with the source proof architecture.
  exact (stage_factorization_and_eventual_eq_of_isPerfect (F := F) (i₀ := i₀) K₀ L₀ hK₀).1 α

-- Proof sketch: represent equality in the colimit Hom group by the same bounded Hom-complex
-- calculation as in part `(2)`; exactness of filtered colimits then implies that two stage
-- morphisms with the same image in the colimit already agree after further base change to a later
-- stage.
/-- Lemma 15.75.18 (2), injectivity part: if two stagewise morphisms have the same image after
base change to the filtered colimit ring, then they agree after further base change to a common
later stage. -/
theorem eventually_eq_of_stage_morphisms_with_equal_colimit_images_of_isPerfect
    (K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀))) (hK₀ : K₀.IsPerfect)
    (j : Set.Ici i₀)
    (β₁ β₂ : (stageBaseChange F i₀ j).obj K₀ ⟶ (stageBaseChange F i₀ j).obj L₀)
    (hβ : stageToColimitHomMap F i₀ j β₁ = stageToColimitHomMap F i₀ j β₂) :
    ∃ (k : Set.Ici i₀) (hjk : j ⟶ k),
      stageTransitionHomMap F i₀ hjk β₁ =
        stageTransitionHomMap F i₀ hjk β₂ := by
  -- Proof comment: the injectivity/eventual-equality statement is the second projection of the
  -- same strict-model package, so both public theorems continue to share one source-faithful
  -- proof route.
  exact
    (stage_factorization_and_eventual_eq_of_isPerfect (F := F) (i₀ := i₀) K₀ L₀ hK₀).2
      j β₁ β₂ hβ

/- The declarations above give the essential-surjectivity and filtered Hom-colimit description for
perfect complexes over a filtered colimit of commutative rings, with part `(2)` exposed directly
through the source-facing stage-factorization, transition-compatibility, and eventual-equality
theorems rather than through wrapper names for stagewise Hom-sets or a public `Functor` /
`Cocone` / `IsColimit` package. -/

end

end

end CategoryTheory
