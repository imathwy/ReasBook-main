import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_90_3
import stacks_proof.stacks_project.Chap10.Definition_10_5_1
import stacks_proof.stacks_project.Chap13.Definition_13_11_3
import stacks_proof.stacks_project.Chap10.Lemma_10_90_4
import stacks_proof.stacks_project.Chap15.Definition_15_65_1
import stacks_proof.stacks_project.Chap15.Lemma_15_65_3
import stacks_proof.stacks_project.Chap15.Lemma_15_65_5
import stacks_proof.stacks_project.Chap15.Lemma_15_65_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe u v

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} [Ring R] [Module.Coherent R R]
variable {M : Type u} [AddCommGroup M] [Module R M]

-- Domain sampling:
-- * primary domain: pseudo-coherence for bounded-above derived complexes of `R`-modules over a
--   coherent ring;
-- * sampled owner API: `DerivedCategory.IsMPseudoCoherent`, `DerivedCategory.IsPseudoCoherent`,
--   `DerivedCategory.homologyFunctor`, the bounded-above homology criterion of Lemma `15.65.10`,
--   `isPseudoCoherent_iff_forall_isMPseudoCoherent`,
--   `moduleCat_isMinusOnePseudoCoherent_iff_finitePresentation`, and
--   `module_coherent_iff_finitePresentation`;
-- * layer triage: the source-facing statements below reformulate the canonical derived-category
--   owners in terms of cohomology coherence / finite presentation, so the bounded-above complex is
--   primitive data while the cohomology predicates are derived companion views.
local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "DModMinus" => boundedAboveDerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single0" => (ModuleCat.single0Functor : ModuleCat R ⥤ DMod)

/-- Helper for Lemma 15.65.18: a length-`n` finite free resolution is defined recursively by
choosing a finite free cover and resolving its kernel for one fewer step. -/
def Module.HasLengthFiniteFreeResolution
    (R : Type u) [Ring R] (M : Type u) [AddCommGroup M] [Module R M] : ℕ → Prop
  | 0 => Module.Finite R M
  | n + 1 =>
      ∃ (F : Type u) (_ : AddCommGroup F) (_ : Module R F),
        Module.Free R F ∧ Module.Finite R F ∧
        ∃ f : F →ₗ[R] M, Function.Surjective f ∧
          Module.HasLengthFiniteFreeResolution R (LinearMap.ker f) n

/-- Helper for Lemma 15.65.18: unfold the recursive definition of a successor-length finite free
resolution. -/
theorem Module.hasLengthFiniteFreeResolution_succ_iff
    (R : Type u) [Ring R] (M : Type u) [AddCommGroup M] [Module R M] (n : ℕ) :
    Module.HasLengthFiniteFreeResolution R M (n + 1) ↔
      ∃ (F : Type u) (_ : AddCommGroup F) (_ : Module R F),
        Module.Free R F ∧ Module.Finite R F ∧
        ∃ f : F →ₗ[R] M, Function.Surjective f ∧
          Module.HasLengthFiniteFreeResolution R (LinearMap.ker f) n := by
  rfl

/-- Helper for Lemma 15.65.18: pseudo-coherence is equivalent to `m`-pseudo-coherence in every
degree. -/
theorem isPseudoCoherent_iff_forall_isMPseudoCoherent (K : DMod) :
    K.IsPseudoCoherent ↔ ∀ m : ℤ, K.IsMPseudoCoherent m := by
  -- TODO for Lemma 15.65.18: the source-faithful proof goes through
  -- `DerivedCategory.Q.objPreimage K` and `cochainComplex_pseudoCoherent_tfae`, but in this file
  -- the local `DMod` notation still leaves a hidden module-object universe parameter unresolved.
  -- After freezing that universe at the notation layer, the proof from Lemma `15.65.6` should
  -- replay verbatim.
  sorry

-- Route correction: instead of waiting on the broken downstream bounded-above package, rebuild the
-- module-side coherent-to-pseudo-coherent bridge locally from the source-faithful finite free
-- resolution recursion.
/-- Helper for Lemma 15.65.18: the zero cochain complex over `ModuleCat R`. -/
private abbrev zeroCpx : CochainComplex (ModuleCat R) ℤ := HomologicalComplex.zero

/-- Helper for Lemma 15.65.18: the zero complex is termwise finite free. -/
private instance zero_isTermwiseFiniteFree : (zeroCpx (R := R)).IsTermwiseFiniteFree where
  out i := by
    let E0 : CochainComplex (ModuleCat R) ℤ := zeroCpx (R := R)
    let hzeroCpx : IsZero (zeroCpx (R := R)) := by
      simpa [zeroCpx] using
        (HomologicalComplex.isZero_zero :
          IsZero (HomologicalComplex.zero : CochainComplex (ModuleCat R) ℤ))
    -- Proof comment: every term of the zero complex is the zero module.
    let hzero : IsZero (E0.X i) := by
      simpa [zeroCpx] using
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i).map_isZero
          hzeroCpx
    letI : Subsingleton (E0.X i) :=
      ModuleCat.subsingleton_of_isZero hzero
    refine ⟨Module.Free.of_subsingleton (R := R) (N := E0.X i), ?_⟩
    exact Module.Finite.equiv hzero.isoZero.toLinearEquiv

/-- Helper for Lemma 15.65.18: a degree-zero module object is automatically `n`-pseudo-coherent
for every positive bound `n`. -/
lemma moduleCat_isMPseudoCoherent_of_pos
    (N : ModuleCat R) (n : ℤ) (hn : 0 < n) :
    N.IsMPseudoCoherent n := by
  let E : Cpx := zeroCpx (R := R)
  let α : DerivedCategory.Q.obj E ⟶ ModuleCat.single0Functor.obj N := 0
  refine ⟨E, ?_, inferInstance, α, ?_, ?_⟩
  · -- Proof comment: the zero complex is bounded on both sides by the chosen positive cutoff.
    refine ⟨n, n, ?_, ?_⟩
    · rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      simpa [E, zeroCpx] using
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i).map_isZero
          (HomologicalComplex.isZero_zero :
            IsZero (HomologicalComplex.zero : CochainComplex (ModuleCat R) ℤ))
    · rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      simpa [E, zeroCpx] using
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i).map_isZero
          (HomologicalComplex.isZero_zero :
            IsZero (HomologicalComplex.zero : CochainComplex (ModuleCat R) ℤ))
  · intro i hi
    let hsrc : IsZero ((H i).obj (DerivedCategory.Q.obj E)) := by
      simpa [E, zeroCpx] using
        (H i).map_isZero
          ((DerivedCategory.Q).map_isZero
            (HomologicalComplex.isZero_zero :
              IsZero (HomologicalComplex.zero : CochainComplex (ModuleCat R) ℤ)))
    let htgt : IsZero ((H i).obj (ModuleCat.single0Functor.obj N)) := by
      exact DerivedCategory.isZero_of_isLE _ 0 i (lt_trans hn hi)
    exact hsrc.isIso htgt ((H i).map α)
  · -- Proof comment: the degree-`n` target homology also vanishes because `n` is positive.
    let hsrc : IsZero ((H n).obj (DerivedCategory.Q.obj E)) := by
      simpa [E, zeroCpx] using
        (H n).map_isZero
          ((DerivedCategory.Q).map_isZero
            (HomologicalComplex.isZero_zero :
              IsZero (HomologicalComplex.zero : CochainComplex (ModuleCat R) ℤ)))
    let htgt : IsZero ((H n).obj (ModuleCat.single0Functor.obj N)) := by
      exact DerivedCategory.isZero_of_isLE _ 0 n hn
    letI : IsIso ((H n).map α) := hsrc.isIso htgt ((H n).map α)
    infer_instance

/-- Helper for Lemma 15.65.18: the degree-zero homology of the single cochain complex is the
original module. -/
noncomputable abbrev single_zero_complex_homology_iso
    (N : ModuleCat R) :
    (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N).homology 0) ≅ N :=
  HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) (0 : ℤ) N

/-- Helper for Lemma 15.65.18: the derived homology of a degree-zero single object vanishes away
from degree `0`. -/
theorem single_zero_complex_homology_isZero_of_ne
    (N : ModuleCat R) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((H i).obj (ModuleCat.single0Functor.obj N)) := by
  -- Proof comment: the degree-zero single object lies in both `D^{≥ 0}` and `D^{≤ 0}`.
  by_cases hlt : i < 0
  · exact DerivedCategory.isZero_of_isGE _ 0 i hlt
  · have hgt : 0 < i := by
      omega
    exact DerivedCategory.isZero_of_isLE _ 0 i hgt

/-- Helper for Lemma 15.65.18: the `Q`-comparison for a degree-zero single complex is the
identity on zeroth derived homology. -/
theorem homology_map_singleFunctorIsoCompQ_app_zero_eq_id
    (N : ModuleCat R) :
    (H 0).map (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app N).hom) =
      𝟙 _ := by
  -- Proof comment: in degree `0`, the `singleFunctorIsoCompQ` comparison is definitionally the
  -- identity morphism.
  change
    (H 0).map
        (𝟙 (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N))) =
      𝟙 _
  simp

/-- Helper for Lemma 15.65.18: if `f ≫ e.hom` is epi and `e` is an isomorphism, then `f` is
already epi. -/
theorem epi_of_epi_comp_iso
    {X Y Z : ModuleCat R} (f : X ⟶ Y) (e : Y ≅ Z) [Epi (f ≫ e.hom)] :
    Epi f := by
  -- Proof comment: cancel the postcomposition by `e.hom` after inserting `e.inv`.
  rw [CategoryTheory.epi_iff_forall_injective]
  intro W
  let hcomp :=
    (CategoryTheory.epi_iff_forall_injective (f ≫ e.hom)).1
      (show Epi (f ≫ e.hom) by infer_instance) W
  intro u v huv
  have huv' : (f ≫ e.hom) ≫ (e.inv ≫ u) = (f ≫ e.hom) ≫ (e.inv ≫ v) := by
    simpa [Category.assoc] using huv
  have heq : e.inv ≫ u = e.inv ≫ v := hcomp huv'
  exact (cancel_epi e.inv).1 heq

/-- Helper for Lemma 15.65.18: the canonical kernel inclusion composed with a module map is zero. -/
lemma kernel_subtype_comp_eq_zero
    {F N : ModuleCat R} (f : F ⟶ N) :
    f.hom.comp (LinearMap.ker f.hom).subtype = 0 := by
  -- Proof comment: every element of the kernel maps to zero by definition.
  ext x
  exact x.2

/-- Helper for Lemma 15.65.18: the kernel sequence of a surjective module map is short exact. -/
theorem kernel_cover_shortExact
    {F N : ModuleCat R} (f : F ⟶ N) (hf : Function.Surjective f.hom) :
    (ShortComplex.moduleCatMk (LinearMap.ker f.hom).subtype f.hom
      (kernel_subtype_comp_eq_zero f)).ShortExact := by
  -- Proof comment: this is the standard short exact sequence `0 → ker f → F → N → 0`.
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    simpa using LinearMap.exact_subtype_ker_map f.hom
  · exact (ModuleCat.mono_iff_injective _).2 (LinearMap.ker f.hom).injective_subtype
  · exact (ModuleCat.epi_iff_surjective _).2 hf

/-- Helper for Lemma 15.65.18: the single cochain complex on a finite free module is termwise
finite free. -/
lemma single_zero_complex_isTermwiseFiniteFree
    (F : ModuleCat R) [Module.Free R F] [Module.Finite R F] :
    ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj F).IsTermwiseFiniteFree := by
  -- Proof comment: degree `0` is the original finite free module, and every other term is zero.
  refine ⟨fun i ↦ ?_⟩
  by_cases hi : i = 0
  · let e :
        (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj F).X i) ≅ F := by
        subst hi
        simpa using HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) F
    exact ⟨Module.Free.of_equiv e.symm.toLinearEquiv, Module.Finite.equiv e.symm.toLinearEquiv⟩
  · let E : CochainComplex (ModuleCat R) ℤ :=
      (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj F
    let hzero : IsZero (E.X i) := by
      simpa [E] using
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) F i hi)
    letI : Subsingleton ↥(E.X i) := ModuleCat.subsingleton_of_isZero hzero
    have hfree : Module.Free R (E.X i) :=
      Module.Free.of_subsingleton (R := R) (N := ↥(E.X i))
    have hfinite : Module.Finite R (E.X i) := by
      let e : ModuleCat.of R PUnit ≅ E.X i :=
        (ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)).isoZero ≪≫ hzero.isoZero.symm
      exact Module.Finite.equiv e.toLinearEquiv
    exact ⟨hfree, hfinite⟩

/-- Helper for Lemma 15.65.18: the degree-zero homology map induced by a finite free cover is the
cover map after the canonical `H⁰(single₀ -)` identifications. -/
theorem single_zero_cover_homology_map_eq
    {F N : ModuleCat.{u} R} (f : F ⟶ N) :
    let α :
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj F) ⟶
          ModuleCat.single0Functor.obj N :=
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app F).hom ≫
        (ModuleCat.single0Functor.map f)
    (H 0).map α ≫
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) (0 : ℤ)).app N).hom =
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) (0 : ℤ)).app F).hom ≫ f := by
  let α :
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj F) ⟶
        ModuleCat.single0Functor.obj N :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app F).hom ≫
      ModuleCat.single0Functor.map f
  let eF :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) (0 : ℤ)).app F
  let eN :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) (0 : ℤ)).app N
  have hnat :=
    NatIso.naturality_1
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) (0 : ℤ)) f
  have hnat' :
      (DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map
          (ModuleCat.single0Functor.map f) ≫
        eN.hom =
      eF.hom ≫ f := by
    -- Proof comment: insert `eF.hom ≫ eF.inv = 𝟙` so naturality matches the target composite.
    have hinner :
        eF.inv ≫
            (DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map
              (ModuleCat.single0Functor.map f) ≫
            eN.hom = f := by
      simpa [eF, eN, Category.assoc] using hnat
    have hinsert :
        (DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map
            (ModuleCat.single0Functor.map f) ≫
          eN.hom =
        eF.hom ≫
          (eF.inv ≫
            (DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map
              (ModuleCat.single0Functor.map f) ≫
            eN.hom) := by
      simpa [Category.assoc] using
        (Iso.hom_inv_id_assoc eF
          ((DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map
            (ModuleCat.single0Functor.map f) ≫
              eN.hom)).symm
    rw [hinsert, hinner]
    simp
  -- Proof comment: separate the `Q(single)` comparison from the cover map, then apply `hnat'`.
  dsimp [α]
  rw [Functor.map_comp, Category.assoc]
  let β := (H 0).map ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).hom.app F)
  have hstep :
      β ≫ ((H 0).map (ModuleCat.single0Functor.map f) ≫ eN.hom) =
        β ≫ (eF.hom ≫ f) := by
    simpa [β, Category.assoc] using congrArg (fun k ↦ β ≫ k) hnat'
  have hβ :
      β ≫ eF.hom = eF.hom := by
    simpa [β, Category.assoc] using
      congrArg (fun k ↦ k ≫ eF.hom)
        (homology_map_singleFunctorIsoCompQ_app_zero_eq_id (R := R) F)
  refine hstep.trans ?_
  simpa [β, Category.assoc] using congrArg (fun k ↦ k ≫ f) hβ

/-- Helper for Lemma 15.65.18: a surjective finite free cover induces an epimorphism on
degree-zero derived homology. -/
theorem single_zero_cover_homology_epi_of_surjective
    {F N : ModuleCat.{u} R} (f : F ⟶ N) (hf : Function.Surjective f.hom) :
    let α :
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj F) ⟶
          ModuleCat.single0Functor.obj N :=
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app F).hom ≫
        (ModuleCat.single0Functor.map f)
    Epi ((H 0).map α) := by
  let α :
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj F) ⟶
        ModuleCat.single0Functor.obj N :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app F).hom ≫
      ModuleCat.single0Functor.map f
  let eF :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) (0 : ℤ)).app F
  have hcomp :
      Epi ((H 0).map α ≫
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) (0 : ℤ)).app N).hom) := by
    -- Proof comment: after identifying degree-zero homology of the source single complex,
    -- the comparison is just the original surjection `f`.
    rw [single_zero_cover_homology_map_eq (R := R) f]
    exact
      (ModuleCat.epi_iff_surjective _).2 <| by
        simpa [eF, Category.assoc] using hf.comp eF.toLinearEquiv.surjective
  exact
    epi_of_epi_comp_iso
      ((H 0).map α)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) (0 : ℤ)).app N)

/-- Helper for Lemma 15.65.18: an `m`-pseudo-coherent witness also works for every larger index. -/
lemma isMPseudoCoherent_mono
    {K : DMod} {m n : ℤ} (hmn : m ≤ n) (hK : K.IsMPseudoCoherent m) :
    K.IsMPseudoCoherent n := by
  rcases hK with ⟨E, hbounds, hfree, α, hαgt, hαm⟩
  -- Proof comment: keep the same bounded finite-free model and weaken only the homology range.
  refine ⟨E, hbounds, hfree, α, ?_, ?_⟩
  · intro i hi
    exact hαgt i (lt_of_le_of_lt hmn hi)
  · by_cases hnm : n = m
    · subst hnm
      simpa using hαm
    · have hmn' : m < n := by
        omega
      letI : IsIso ((H n).map α) := hαgt n hmn'
      infer_instance

/-- Helper for Lemma 15.65.18: a finite free module is `m`-pseudo-coherent for every integer
bound. -/
lemma finite_free_module_isMPseudoCoherent
    (F : ModuleCat.{u} R) (m : ℤ) [Module.Free R F] [Module.Finite R F] :
    F.IsMPseudoCoherent m := by
  let E : Cpx := (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj F
  let hEfree : E.IsTermwiseFiniteFree := single_zero_complex_isTermwiseFiniteFree F
  let α : DerivedCategory.Q.obj E ⟶ ModuleCat.single0Functor.obj F :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app F).hom
  -- Proof comment: the degree-zero single complex is already a bounded finite-free witness.
  refine ⟨E, ⟨0, 0, inferInstance, inferInstance⟩, hEfree, α, ?_, ?_⟩
  · intro i hi
    letI : IsIso ((H i).map α) := Functor.map_isIso (H i) α
    infer_instance
  · letI : IsIso ((H m).map α) := Functor.map_isIso (H m) α
    infer_instance

/-- Helper for Lemma 15.65.18: the kernel of a surjective finite free cover of a
`(-(d + 1))`-pseudo-coherent module is `(-d)`-pseudo-coherent. -/
lemma kernel_of_surjective_finite_free_cover_isMPseudoCoherent
    {F N : ModuleCat.{u} R} (f : F ⟶ N) (hf : Function.Surjective f.hom) (d : ℕ)
    [Module.Free R F] [Module.Finite R F]
    (hN : N.IsMPseudoCoherent (-(d + 1 : ℤ))) :
    (ModuleCat.of R (LinearMap.ker f.hom)).IsMPseudoCoherent (-(d : ℤ)) := by
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.moduleCatMk (LinearMap.ker f.hom).subtype f.hom
      (kernel_subtype_comp_eq_zero f)
  have hS : S.ShortExact := kernel_cover_shortExact f hf
  let T : Triangle DMod := hS.singleTriangle
  have hF : T.obj₂.IsMPseudoCoherent (-(d : ℤ)) := by
    -- Proof comment: the middle term is the chosen finite free cover.
    simpa [T, S, ModuleCat.IsMPseudoCoherent] using
      finite_free_module_isMPseudoCoherent F (-(d : ℤ))
  have hN' : T.obj₃.IsMPseudoCoherent (-(d + 1 : ℤ)) := by
    -- Proof comment: the third term is the original quotient module.
    simpa [T, S, ModuleCat.IsMPseudoCoherent] using hN
  have hF' : T.obj₂.IsMPseudoCoherent ((-(d + 1 : ℤ)) + 1) := by
    simpa using hF
  have hK :
      T.obj₁.IsMPseudoCoherent ((-(d + 1 : ℤ)) + 1) :=
    isMPseudoCoherent_obj₁_of_distinguishedTriangle
      (R := R) T hS.singleTriangle_distinguished hF' hN'
  -- Proof comment: simplify the shifted index `(-(d + 1)) + 1 = -d`.
  simpa [T, S, ModuleCat.IsMPseudoCoherent] using hK

/-- Helper for Lemma 15.65.18: an `R`-module is `0`-pseudo-coherent exactly when it is finite. -/
theorem moduleCat_isZeroPseudoCoherent_iff_finite
    (N : ModuleCat.{u} R) :
    N.IsMPseudoCoherent 0 ↔ Module.Finite R ↥N := by
  constructor
  · intro hN
    let E : Cpx := (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N
    have hE : E.IsMPseudoCoherent 0 := by
      -- Proof comment: move the pseudo-coherent witness from `N[0]` back to the explicit
      -- degree-zero single complex.
      exact
        isMPseudoCoherent_of_iso
          (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app N).symm) 0 hN
    have hfiniteH : Module.Finite R (E.homology 0) := by
      -- Proof comment: all off-zero homology groups vanish for a single complex, so the
      -- degree-zero homology is finite by the finite-homology owner.
      exact CochainComplex.homology_finite_of_isMPseudoCoherent
        (R := R) hE
        (fun i hi ↦
          HomologicalComplex.isZero_single_obj_homology
            (ComplexShape.up ℤ) (0 : ℤ) N i (by omega))
    letI : Module.Finite R (E.homology 0) := hfiniteH
    -- Proof comment: identify the zeroth homology of the single complex with `N`.
    exact Module.Finite.equiv (single_zero_complex_homology_iso (R := R) N).toLinearEquiv
  · intro hN
    rcases (Module.Finite.iff_exists_surjective_free R ↥N).1 hN with ⟨n, f, hf⟩
    let F : ModuleCat R := ModuleCat.of R (Fin n → R)
    let g : F ⟶ N := ModuleCat.ofHom f
    let E : Cpx := (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj F
    let hEfree : E.IsTermwiseFiniteFree := single_zero_complex_isTermwiseFiniteFree F
    let α : DerivedCategory.Q.obj E ⟶ ModuleCat.single0Functor.obj N :=
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app F).hom ≫
        ModuleCat.single0Functor.map g
    -- Proof comment: a surjective finite free cover of `N` is already the required bounded
    -- finite-free witness in degree `0`.
    refine ⟨E, ⟨0, 0, inferInstance, inferInstance⟩, hEfree, α, ?_, ?_⟩
    · intro i hi
      have hi0 : i ≠ 0 := by
        omega
      let hsrcSingle :
          IsZero ((H i).obj (ModuleCat.single0Functor.obj F)) :=
        single_zero_complex_homology_isZero_of_ne (R := R) F i hi0
      let hsrc :
          IsZero ((H i).obj (DerivedCategory.Q.obj E)) := by
        exact
          ((((H i).mapIso
            ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app F)).isZero_iff).2
            hsrcSingle)
      let htgt :
          IsZero ((H i).obj (ModuleCat.single0Functor.obj N)) :=
        single_zero_complex_homology_isZero_of_ne (R := R) N i hi0
      exact hsrc.isIso htgt ((H i).map α)
    · exact single_zero_cover_homology_epi_of_surjective (R := R) g hf

/-- Helper for Lemma 15.65.18: an `R`-module is `(-1)`-pseudo-coherent exactly when it is
finitely presented. -/
theorem moduleCat_isMinusOnePseudoCoherent_iff_finitePresentation
    (N : ModuleCat.{u} R) :
    N.IsMPseudoCoherent (-1) ↔ Module.FinitePresentation R ↥N := by
  constructor
  · intro hN
    have hN0 : N.IsMPseudoCoherent 0 := by
      -- Proof comment: forget the stronger negative bound and retain only degree-zero
      -- pseudo-coherence.
      rw [ModuleCat.IsMPseudoCoherent] at hN ⊢
      exact isMPseudoCoherent_mono (R := R) (show (-1 : ℤ) ≤ 0 by omega) hN
    have hfiniteN : Module.Finite R ↥N :=
      (moduleCat_isZeroPseudoCoherent_iff_finite (R := R) N).1 hN0
    rcases (Module.Finite.iff_exists_surjective_free R ↥N).1 hfiniteN with ⟨n, f, hf⟩
    let F : ModuleCat R := ModuleCat.of R (Fin n → R)
    let g : F ⟶ N := ModuleCat.ofHom f
    have hkerPc :
        (ModuleCat.of R (LinearMap.ker g.hom)).IsMPseudoCoherent 0 :=
      kernel_of_surjective_finite_free_cover_isMPseudoCoherent (R := R) g hf 0 hN
    have hkerFinite :
        Module.Finite R (LinearMap.ker g.hom) :=
      (moduleCat_isZeroPseudoCoherent_iff_finite (R := R)
        (ModuleCat.of R (LinearMap.ker g.hom))).1 hkerPc
    letI : Module.Finite R (LinearMap.ker g.hom) := hkerFinite
    have hkerFG : (LinearMap.ker g.hom).FG := by
      -- Proof comment: finite modules have finitely generated underlying submodules.
      have hkerEq :
          LinearMap.ker g.hom = LinearMap.range (LinearMap.ker g.hom).subtype := by
        ext x
        constructor
        · intro hx
          exact ⟨⟨x, hx⟩, rfl⟩
        · rintro ⟨x, rfl⟩
          exact x.2
      rw [hkerEq]
      exact Submodule.fg_range (LinearMap.ker g.hom).subtype
    -- Proof comment: a finite free cover with finitely generated kernel is a finite presentation.
    exact Module.finitePresentation_of_surjective g.hom hf hkerFG
  · intro hN
    rcases (Module.FinitePresentation.iff_exists_exact_free_sequence R ↥N).1 hN with
      ⟨n, m, f, g, hfg, hg⟩
    let F₀ : ModuleCat R := ModuleCat.of R (Fin n → R)
    let q : F₀ ⟶ N := ModuleCat.ofHom g
    have hkerEq : LinearMap.ker g = LinearMap.range f := LinearMap.exact_iff.mp hfg
    letI : Module.Finite R (Fin m → R) := inferInstance
    have hkerFinite : Module.Finite R (LinearMap.ker g) := by
      have hrangeFinite : Module.Finite R (LinearMap.range f) :=
        Module.Finite.of_fg (Submodule.fg_range f)
      exact hkerEq.symm ▸ hrangeFinite
    have hkerPc :
        (ModuleCat.of R (LinearMap.ker g)).IsMPseudoCoherent 0 :=
      (moduleCat_isZeroPseudoCoherent_iff_finite (R := R) (ModuleCat.of R (LinearMap.ker g))).2
        hkerFinite
    let S : ShortComplex (ModuleCat R) :=
      ShortComplex.moduleCatMk (LinearMap.ker q.hom).subtype q.hom
        (kernel_subtype_comp_eq_zero q)
    have hS : S.ShortExact := by
      simpa [S] using kernel_cover_shortExact (R := R) q hg
    let T : Triangle DMod := hS.singleTriangle
    have hleft : T.obj₁.IsMPseudoCoherent 0 := by
      -- Proof comment: the left vertex is the kernel of the chosen presentation map.
      simpa [T, S, ModuleCat.IsMPseudoCoherent] using hkerPc
    have hmiddle : T.obj₂.IsMPseudoCoherent (-1) := by
      -- Proof comment: the middle vertex is finite free, hence pseudo-coherent in every degree.
      simpa [T, S, ModuleCat.IsMPseudoCoherent] using
        finite_free_module_isMPseudoCoherent (R := R) F₀ (-1)
    -- Proof comment: the distinguished triangle attached to the presentation yields the target.
    simpa [T, S, ModuleCat.IsMPseudoCoherent] using
      (isMPseudoCoherent_obj₃_of_distinguishedTriangle
        (R := R) T hS.singleTriangle_distinguished hleft hmiddle)

/-- Helper for Lemma 15.65.18: for `d : ℕ`, `(-d)`-pseudo-coherence is equivalent to admitting a
length-`d` finite free resolution. -/
theorem moduleCat_isNegPseudoCoherent_iff_hasFiniteFreeResolutionLength
    (N : ModuleCat.{u} R) (d : ℕ) :
    N.IsMPseudoCoherent (-(d : ℤ)) ↔ Module.HasLengthFiniteFreeResolution R ↥N d := by
  induction d generalizing N with
  | zero =>
      -- Proof comment: a length-zero finite free resolution is exactly finite generation.
      simpa [Module.HasLengthFiniteFreeResolution] using
        (moduleCat_isZeroPseudoCoherent_iff_finite (R := R) N)
  | succ d ih =>
      constructor
      · intro hN
        have hN0 : N.IsMPseudoCoherent 0 := by
          -- Proof comment: a negative-degree pseudo-coherent module is in particular
          -- degree-zero pseudo-coherent.
          rw [ModuleCat.IsMPseudoCoherent] at hN ⊢
          exact isMPseudoCoherent_mono (R := R) (show (-(d + 1 : ℤ)) ≤ 0 by omega) hN
        have hfiniteN : Module.Finite R N :=
          (moduleCat_isZeroPseudoCoherent_iff_finite (R := R) N).1 hN0
        rcases (Module.Finite.iff_exists_surjective_free R N).1 hfiniteN with ⟨n, f, hf⟩
        let F : ModuleCat R := ModuleCat.of R (Fin n → R)
        let g : F ⟶ N := ModuleCat.ofHom f
        have hkerPc :
            (ModuleCat.of R (LinearMap.ker g.hom)).IsMPseudoCoherent (-(d : ℤ)) :=
          kernel_of_surjective_finite_free_cover_isMPseudoCoherent (R := R) g hf d hN
        have hkerRes :
            Module.HasLengthFiniteFreeResolution R (LinearMap.ker g.hom) d :=
          (ih (ModuleCat.of R (LinearMap.ker g.hom))).1 hkerPc
        -- Proof comment: package the chosen finite free cover and the recursive kernel
        -- resolution into the successor case.
        exact
          (Module.hasLengthFiniteFreeResolution_succ_iff (R := R) (M := ↥N) d).2
            ⟨Fin n → R, inferInstance, inferInstance, inferInstance, inferInstance, f, hf, hkerRes⟩
      · intro hN
        rcases (Module.hasLengthFiniteFreeResolution_succ_iff (R := R) (M := ↥N) d).1 hN with
          ⟨F, _hFadd, _hFmod, hfree, hfinite, f, hf, hker⟩
        let F₀ : ModuleCat R := ModuleCat.of R F
        let q : F₀ ⟶ N := ModuleCat.ofHom f
        letI : Module.Free R F := hfree
        letI : Module.Finite R F := hfinite
        have hkerPc :
            (ModuleCat.of R (LinearMap.ker f)).IsMPseudoCoherent (-(d : ℤ)) :=
          (ih (ModuleCat.of R (LinearMap.ker f))).2 hker
        let S : ShortComplex (ModuleCat R) :=
          ShortComplex.moduleCatMk (LinearMap.ker q.hom).subtype q.hom
            (kernel_subtype_comp_eq_zero q)
        have hS : S.ShortExact := by
          simpa [S] using kernel_cover_shortExact (R := R) q hf
        let T : Triangle DMod := hS.singleTriangle
        have hleft : T.obj₁.IsMPseudoCoherent (-(d : ℤ)) := by
          -- Proof comment: the left vertex is the recursively resolved kernel.
          simpa [T, S, ModuleCat.IsMPseudoCoherent] using hkerPc
        have hmiddle : T.obj₂.IsMPseudoCoherent (-(d + 1 : ℤ)) := by
          -- Proof comment: the middle vertex is finite free, hence pseudo-coherent in every
          -- degree.
          simpa [T, S, ModuleCat.IsMPseudoCoherent] using
            finite_free_module_isMPseudoCoherent (R := R) F₀ (-(d + 1 : ℤ))
        have hleft' : T.obj₁.IsMPseudoCoherent ((-(d + 1 : ℤ)) + 1) := by
          simpa using hleft
        -- Proof comment: the distinguished triangle for the short exact row advances the
        -- pseudo-coherent resolution by one step.
        simpa [T, S, ModuleCat.IsMPseudoCoherent] using
          (isMPseudoCoherent_obj₃_of_distinguishedTriangle
            (R := R) T hS.singleTriangle_distinguished hleft' hmiddle)

/-- Helper for Lemma 15.65.18: a coherent module admits a finite free resolution of every finite
length by iterating coherent kernels of finite free covers. -/
lemma coherent_hasLengthFiniteFreeResolution
    (hM : Module.Coherent R M) (d : ℕ) :
    Module.HasLengthFiniteFreeResolution R M d := by
  induction d generalizing M with
  | zero =>
      -- Proof comment: length `0` is exactly finite generation.
      letI : Module.Coherent R M := hM
      simpa [Module.HasLengthFiniteFreeResolution] using (inferInstance : Module.Finite R M)
  | succ d ih =>
      letI : Module.Coherent R M := hM
      have hfinite : Module.Finite R M := inferInstance
      rcases (Module.Finite.iff_exists_surjective_free R M).1 hfinite with ⟨n, f, hf⟩
      have hfreeCoherent : Module.Coherent R (Fin n → R) := by
        -- Proof comment: finite free modules are finitely presented, hence coherent over a
        -- coherent ring.
        exact
          (module_coherent_iff_finitePresentation (R := R) (M := Fin n → R)).2 inferInstance
      have hker : Module.Coherent R (LinearMap.ker f) := by
        letI : Module.Coherent R (Fin n → R) := hfreeCoherent
        exact ker_coherent_of_coherent f
      -- Proof comment: peel off a finite free cover and recurse on its coherent kernel.
      refine (Module.hasLengthFiniteFreeResolution_succ_iff (R := R) (M := M) d).2 ?_
      refine ⟨Fin n → R, inferInstance, inferInstance, inferInstance, inferInstance, f, hf, ?_⟩
      exact ih hker

/-- Helper for Lemma 15.65.18: a length-`d` finite free resolution gives `(-d)`-pseudo-coherence
for the corresponding module object. -/
lemma moduleCat_isNegPseudoCoherent_of_hasLengthFiniteFreeResolution
    (N : ModuleCat.{u} R) (d : ℕ) (hN : Module.HasLengthFiniteFreeResolution R ↥N d) :
    N.IsMPseudoCoherent (-(d : ℤ)) := by
  -- Proof comment: this is exactly the reverse implication of Lemma `15.65.4 (3)`.
  exact
    (moduleCat_isNegPseudoCoherent_iff_hasFiniteFreeResolutionLength
      (R := R) N d).2 hN

/-- Helper for Lemma 15.65.18: coherent modules over a coherent ring are `m`-pseudo-coherent in
every degree. -/
lemma moduleCat_isMPseudoCoherent_of_coherent
    (N : ModuleCat.{u} R) (n : ℤ) (hN : Module.Coherent R ↥N) :
    N.IsMPseudoCoherent n := by
  by_cases hn : 0 < n
  · -- Proof comment: positive degrees are immediate from the zero-complex witness.
    exact moduleCat_isMPseudoCoherent_of_pos N n hn
  · have hnonpos : n ≤ 0 := le_of_not_gt hn
    let d : ℕ := Int.toNat (-n)
    have hd : n = -(d : ℤ) := by
      -- Proof comment: rewrite a nonpositive integer as the negative of its natural absolute
      -- value.
      dsimp [d]
      have hneg : 0 ≤ -n := by
        omega
      rw [Int.toNat_of_nonneg hneg]
      omega
    rw [hd]
    exact
      moduleCat_isNegPseudoCoherent_of_hasLengthFiniteFreeResolution (R := R) N d
        (coherent_hasLengthFiniteFreeResolution (R := R) (M := ↥N) hN d)

/-- Helper for Lemma 15.65.18: the degree-zero pseudo-coherent versus finite bridge should also
work for homology objects living in arbitrary `ModuleCat` universes. -/
lemma moduleCat_isZeroPseudoCoherent_iff_finite_univ
    (N : ModuleCat.{v} R) :
    N.IsMPseudoCoherent 0 ↔ Module.Finite R ↥N := by
  -- TODO for Lemma 15.65.18: replay `moduleCat_isZeroPseudoCoherent_iff_finite` without fixing
  -- the module-object universe to the ring universe, so it applies directly to homology objects.
  sorry

/-- Helper for Lemma 15.65.18: coherent modules in arbitrary `ModuleCat` universes are
`m`-pseudo-coherent in every degree. -/
lemma moduleCat_isMPseudoCoherent_of_coherent_univ
    (N : ModuleCat.{v} R) (n : ℤ) (hN : Module.Coherent R ↥N) :
    N.IsMPseudoCoherent n := by
  -- TODO for Lemma 15.65.18: generalize `moduleCat_isMPseudoCoherent_of_coherent` so the module
  -- universe of `N` matches the homology objects coming from `DerivedCategory.homologyFunctor`.
  sorry

/-- Helper for Lemma 15.65.18: coherence transports across linear equivalences by moving through
finite presentation. -/
lemma module_coherent_of_equiv
    {M' : Type*} [AddCommGroup M'] [Module R M']
    {N' : Type*} [AddCommGroup N'] [Module R N']
    (e : M' ≃ₗ[R] N') [Module.Coherent R M'] :
    Module.Coherent R N' := by
  -- Proof comment: over a coherent ring, coherence is equivalent to finite presentation, and
  -- finite presentation is invariant under linear equivalence.
  have hfp : Module.FinitePresentation R M' :=
    (module_coherent_iff_finitePresentation (R := R) (M := M')).1 inferInstance
  have hfp' : Module.FinitePresentation R N' :=
    Module.FinitePresentation.of_equiv e
  exact (module_coherent_iff_finitePresentation (R := R) (M := N')).2 hfp'

/-- Helper for Lemma 15.65.18: homology of a termwise finite free cochain complex over a coherent
ring is finitely presented in every degree. -/
lemma termwiseFiniteFree_homology_finitePresentation
    {E : CochainComplex (ModuleCat R) ℤ} [E.IsTermwiseFiniteFree] (i : ℤ) :
    Module.FinitePresentation R (E.homology i) := by
  let S : ShortComplex (ModuleCat R) := E.sc i
  letI : Module.Finite R ↥(S.X₁) := by
    simpa [S] using
      (show Module.Finite R ↥(E.X ((ComplexShape.up ℤ).prev i)) by infer_instance)
  letI : Module.Free R ↥(S.X₂) := by
    simpa [S] using (show Module.Free R ↥(E.X i) by infer_instance)
  letI : Module.Finite R ↥(S.X₂) := by
    simpa [S] using (show Module.Finite R ↥(E.X i) by infer_instance)
  letI : Module.Free R ↥(S.X₃) := by
    simpa [S] using
      (show Module.Free R ↥(E.X ((ComplexShape.up ℤ).next i)) by infer_instance)
  letI : Module.Finite R ↥(S.X₃) := by
    simpa [S] using
      (show Module.Finite R ↥(E.X ((ComplexShape.up ℤ).next i)) by infer_instance)
  letI : Module.Projective R ↥(S.X₂) := Module.Projective.of_free
  letI : Module.Projective R ↥(S.X₃) := Module.Projective.of_free
  have hX₂coherent : Module.Coherent R ↥(S.X₂) := by
    -- Proof comment: the middle term of `E.sc i` is finite free, hence finitely presented and
    -- therefore coherent over the coherent ring `R`.
    let hfp : Module.FinitePresentation R ↥(S.X₂) :=
      Module.finitePresentation_of_projective R ↥(S.X₂)
    exact (module_coherent_iff_finitePresentation (R := R) (M := ↥(S.X₂))).2 hfp
  have hX₃coherent : Module.Coherent R ↥(S.X₃) := by
    -- Proof comment: the same finite-free argument applies to the outgoing degree.
    let hfp : Module.FinitePresentation R ↥(S.X₃) :=
      Module.finitePresentation_of_projective R ↥(S.X₃)
    exact (module_coherent_iff_finitePresentation (R := R) (M := ↥(S.X₃))).2 hfp
  have hkerCoherent : Module.Coherent R (LinearMap.ker S.g.hom) := by
    -- Proof comment: cycles are the kernel of the outgoing differential in the owner short
    -- complex.
    letI : Module.Coherent R ↥(S.X₂) := hX₂coherent
    letI : Module.Coherent R ↥(S.X₃) := hX₃coherent
    exact ker_coherent_of_coherent S.g.hom
  letI : Module.Coherent R S.moduleCatLeftHomologyData.K := by
    change Module.Coherent R (LinearMap.ker S.g.hom)
    exact hkerCoherent
  have hcyclesCoherent : Module.Coherent R S.cycles := by
    -- Proof comment: transport the kernel coherence to the categorical cycles object once.
    exact module_coherent_of_equiv (R := R) S.moduleCatCyclesIso.symm.toLinearEquiv
  have hquotCoherent : Module.Coherent R S.moduleCatLeftHomologyData.H := by
    -- Proof comment: left homology is the cokernel of the boundary map into cycles, and the
    -- boundary source is finite because each term of `E` is finite free.
    letI : Module.Coherent R S.cycles := hcyclesCoherent
    have hfp_cycles : Module.FinitePresentation R ↥S.cycles :=
      (module_coherent_iff_finitePresentation (R := R) (M := ↥S.cycles)).1 hcyclesCoherent
    letI : Module.FinitePresentation R ↥S.cycles := hfp_cycles
    letI : Module.FinitePresentation R (LinearMap.ker S.g.hom) :=
      Module.FinitePresentation.of_equiv S.moduleCatCyclesIso.toLinearEquiv
    letI : Module.FinitePresentation R S.moduleCatLeftHomologyData.K := by
      change Module.FinitePresentation R (LinearMap.ker S.g.hom)
      infer_instance
    have hfg_kernel :
        Submodule.FG (LinearMap.ker S.moduleCatLeftHomologyData.π.hom) := by
      -- Proof comment: the quotient kernel is exactly the range of the previous differential.
      change Submodule.FG (LinearMap.ker ((LinearMap.range S.moduleCatToCycles).mkQ))
      simpa [Submodule.ker_mkQ] using
        (CochainComplex.fg_range_moduleCatToCycles (R := R) (E := E) i)
    have hfp_quotient : Module.FinitePresentation R S.moduleCatLeftHomologyData.H :=
      Module.finitePresentation_of_surjective S.moduleCatLeftHomologyData.π.hom
        (CochainComplex.mkQ_surjective_range_moduleCatToCycles (R := R) S) hfg_kernel
    exact
      (module_coherent_iff_finitePresentation
        (R := R) (M := S.moduleCatLeftHomologyData.H)).2 hfp_quotient
  have hleftCoherent : Module.Coherent R S.leftHomology := by
    -- Proof comment: move from the concrete quotient owner to the abstract left homology object.
    letI : Module.Coherent R S.moduleCatLeftHomologyData.H := hquotCoherent
    exact
      module_coherent_of_equiv (R := R)
        S.moduleCatLeftHomologyData.leftHomologyIso.symm.toLinearEquiv
  have hhomologyCoherent : Module.Coherent R (E.homology i) := by
    -- Proof comment: finally transport left homology along the standard comparison with
    -- cochain-complex homology.
    letI : Module.Coherent R S.leftHomology := hleftCoherent
    exact
      module_coherent_of_equiv (R := R)
        (CochainComplex.sc_leftHomology_iso_homology (R := R) (E := E) i).toLinearEquiv
  exact
    (module_coherent_iff_finitePresentation (R := R) (M := E.homology i)).1
      hhomologyCoherent

/-- Helper for Lemma 15.65.18: `m`-pseudo-coherence of a bounded-above derived complex yields a
finite degree-`m` homology module and finitely presented higher homology modules. -/
lemma boundedAbove_homology_finite_and_finitePresentation_of_isMPseudoCoherent
    (K : DModMinus) (m : ℤ) (hK : K.obj.IsMPseudoCoherent m) :
    Module.Finite R ((H m).obj K.obj) ∧
      ∀ i : ℤ, m < i → Module.FinitePresentation R ((H i).obj K.obj) := by
  rcases hK with ⟨E, hbounds, hfree, α, hαgt, hαm⟩
  constructor
  · -- Proof comment: in degree `m`, the defining map is only an epimorphism, but finite
    -- presentation of the witness homology still descends finite generation to `H^m(K)`.
    have hEfp : Module.FinitePresentation R (E.homology m) :=
      termwiseFiniteFree_homology_finitePresentation (R := R) (E := E) m
    have hQfp : Module.FinitePresentation R ((H m).obj (DerivedCategory.Q.obj E)) := by
      let eQ : ((H m).obj (DerivedCategory.Q.obj E)) ≅ E.homology m :=
        CochainComplex.derived_homology_iso (R := R) E m
      exact Module.FinitePresentation.of_equiv eQ.symm.toLinearEquiv
    let _ : Module.FinitePresentation R ((H m).obj (DerivedCategory.Q.obj E)) := hQfp
    let _ : Module.Finite R ((H m).obj (DerivedCategory.Q.obj E)) := inferInstance
    exact Module.Finite.of_surjective
      ((H m).map α).hom
      ((ModuleCat.epi_iff_surjective _).1 hαm)
  · intro i hi
    -- Proof comment: above degree `m`, the witness comparison is an isomorphism, so finite
    -- presentation transports directly from the termwise finite-free model to `H^i(K)`.
    have hEfp : Module.FinitePresentation R (E.homology i) :=
      termwiseFiniteFree_homology_finitePresentation (R := R) (E := E) i
    have hQfp : Module.FinitePresentation R ((H i).obj (DerivedCategory.Q.obj E)) := by
      let eQ : ((H i).obj (DerivedCategory.Q.obj E)) ≅ E.homology i :=
        CochainComplex.derived_homology_iso (R := R) E i
      exact Module.FinitePresentation.of_equiv eQ.symm.toLinearEquiv
    let eH : ((H i).obj (DerivedCategory.Q.obj E)) ≅ ((H i).obj K.obj) := by
      let _ : IsIso ((H i).map α) := hαgt i hi
      exact asIso ((H i).map α)
    let _ : Module.FinitePresentation R ((H i).obj (DerivedCategory.Q.obj E)) := hQfp
    exact Module.FinitePresentation.of_equiv eH.toLinearEquiv

-- Degree-zero bridge: over a coherent ring, pseudo-coherent modules are exactly coherent modules.
-- The forward implication factors through finite presentation via Lemma `15.65.4` and
-- Lemma `10.90.4`; the reverse implication is the reusable module-level input for the bounded-above
-- homology criterion below.
-- TODO for Lemma 15.65.18: finish the negative-degree module bridge by converting
-- `coherent_hasLengthFiniteFreeResolution` into `m`-pseudo-coherence via the owner lemmas from
-- `Lemma_15_65_4`.
/-- Over a coherent ring, an `R`-module is pseudo-coherent exactly when it is coherent. -/
theorem _root_.Module.isPseudoCoherent_iff_coherent :
    (ModuleCat.of R M).IsPseudoCoherent ↔ Module.Coherent R M := by
  constructor
  · intro hM
    -- Proof comment: evaluate the all-`m` pseudo-coherence criterion at `m = -1`, identify that
    -- degree with finite presentation, and then convert finite presentation to coherence.
    rw [ModuleCat.IsPseudoCoherent, isPseudoCoherent_iff_forall_isMPseudoCoherent] at hM
    have hMfp : Module.FinitePresentation R M := by
      simpa using
        (moduleCat_isMinusOnePseudoCoherent_iff_finitePresentation
          (R := R) (ModuleCat.of R M)).1 (hM (-1))
    exact (module_coherent_iff_finitePresentation (R := R) (M := M)).2 hMfp
  · intro hM
    -- Proof comment: coherent modules over a coherent ring are `m`-pseudo-coherent in every
    -- degree, so the global pseudo-coherent criterion follows from the repaired adapter.
    rw [ModuleCat.IsPseudoCoherent, isPseudoCoherent_iff_forall_isMPseudoCoherent]
    intro m
    simpa using
      moduleCat_isMPseudoCoherent_of_coherent
        (R := R) (ModuleCat.of R M) m hM

-- Proof sketch: the second and third conditions differ only by Lemma `10.90.4`, which identifies
-- coherent and finitely presented modules over a coherent ring. For the implication to
-- `m`-pseudo-coherence, first use that coherent modules over a coherent ring are pseudo-coherent,
-- upgrade this to all `m` with `isPseudoCoherent_iff_forall_isMPseudoCoherent`, and then apply
-- `boundedAbove_isMPseudoCoherent_of_homology`; the finiteness of `H^m(K)` is the degree-`m`
-- clause recorded separately in the source statement.
-- TODO: complete the TFAE after restoring the prerequisite module bridge above and a working
-- bounded-above homology criterion replacing the currently broken `Lemma_15_65_10`.
/-- Lemma 15.65.18: for a bounded-above derived `R`-complex over a coherent ring, the following
are equivalent: `K` is `m`-pseudo-coherent; `H^m(K)` is finite and all higher cohomology modules
are coherent; and `H^m(K)` is finite and all higher cohomology modules are finitely presented. -/
-- TODO: prove `1 → 3` by extracting finite presentation of each higher homology module from the
-- bounded-above witness, then use `boundedAbove_isMPseudoCoherent_of_homology` plus the module
-- bridge above for `2 → 1`.
theorem boundedAbove_isMPseudoCoherent_tfae_of_coherentRing
    (K : DModMinus) (m : ℤ) :
    ([ K.obj.IsMPseudoCoherent m
      , Module.Finite R ((H m).obj K.obj) ∧
          ∀ i : ℤ, m < i → Module.Coherent R ((H i).obj K.obj)
      , Module.Finite R ((H m).obj K.obj) ∧
          ∀ i : ℤ, m < i → Module.FinitePresentation R ((H i).obj K.obj)
      ] : List Prop).TFAE := by
  tfae_have 1 → 3 := by
    intro hK
    -- Proof comment: the forward edge is exactly the witness-transport package proved above.
    exact
      boundedAbove_homology_finite_and_finitePresentation_of_isMPseudoCoherent
        (R := R) K m hK
  tfae_have 3 → 2 := by
    rintro ⟨hmfinite, hhighfp⟩
    constructor
    · exact hmfinite
    · intro i hi
      exact
        (module_coherent_iff_finitePresentation (R := R) (M := ↥((H i).obj K.obj))).2
          (hhighfp i hi)
  tfae_have 2 → 1 := by
    rintro ⟨hmfinite, hhighcoh⟩
    -- Proof comment: feed Lemma `15.65.10` degreewise, splitting the homology into the three
    -- source cases `i < m`, `i = m`, and `m < i`.
    exact boundedAbove_isMPseudoCoherent_of_homology (R := R) K m <| by
      intro i
      by_cases him : i < m
      · have hpos : 0 < m - i := by
          omega
        exact
          moduleCat_isMPseudoCoherent_of_pos
            (R := R) ((((H i).obj K.obj) : ModuleCat R)) (m - i) hpos
      · by_cases hieq : i = m
        · subst i
          simpa using
            (moduleCat_isZeroPseudoCoherent_iff_finite_univ
              (R := R) ((((H m).obj K.obj) : ModuleCat R))).2 hmfinite
        · have hmi : m < i := by
            omega
          have hcoh : Module.Coherent R ↥((((H i).obj K.obj) : ModuleCat R)) :=
            hhighcoh i hmi
          exact
            moduleCat_isMPseudoCoherent_of_coherent_univ
              (R := R) ((((H i).obj K.obj) : ModuleCat R)) (m - i) hcoh
  tfae_finish

-- Proof sketch: apply the previous equivalence for every `m`. If `K` is pseudo-coherent, then it
-- is `m`-pseudo-coherent for all `m`, so each cohomology module is coherent. Conversely, if every
-- cohomology module is coherent, then for each `m` the second clause of the previous theorem
-- holds, so `K` is `m`-pseudo-coherent for every `m`; now use the canonical owner theorem
-- `isPseudoCoherent_iff_forall_isMPseudoCoherent` to recover `K.obj.IsPseudoCoherent`.
-- TODO: deduce this from the preceding TFAE once the bounded-above theorem is finished.
/-- A bounded-above derived complex over a coherent ring is pseudo-coherent exactly when all of
its cohomology modules are coherent. -/
-- TODO: apply the preceding `TFAE` degreewise once the bounded-above theorem is available.
theorem boundedAbove_isPseudoCoherent_iff_homology_coherent
    (K : DModMinus) :
    K.obj.IsPseudoCoherent ↔
      ∀ i : ℤ, Module.Coherent R ((H i).obj K.obj) := by
  constructor
  · intro hK i
    -- Proof comment: pseudo-coherence gives `m`-pseudo-coherence for every `m`; applying the
    -- bounded-above TFAE at `m = i - 1` puts `H^i(K)` in the coherent tail.
    have hKm :
        ∀ m : ℤ, K.obj.IsMPseudoCoherent m :=
      (isPseudoCoherent_iff_forall_isMPseudoCoherent (R := R) K.obj).1 hK
    have hTail :
        Module.Finite R ((H (i - 1)).obj K.obj) ∧
          ∀ j : ℤ, i - 1 < j → Module.Coherent R ((H j).obj K.obj) :=
      ((boundedAbove_isMPseudoCoherent_tfae_of_coherentRing (R := R) K (i - 1)).out 0 1).mp
        (hKm (i - 1))
    exact hTail.2 i (by omega)
  · intro hH
    -- Proof comment: for each cutoff `m`, the assumed coherence of all homology objects gives the
    -- middle clause of the bounded-above TFAE; then the all-`m` criterion recovers
    -- pseudo-coherence.
    exact (isPseudoCoherent_iff_forall_isMPseudoCoherent (R := R) K.obj).2 <| by
      intro m
      have hmfp : Module.FinitePresentation R ((H m).obj K.obj) :=
        (module_coherent_iff_finitePresentation (R := R) (M := ↥((H m).obj K.obj))).1 (hH m)
      let _ : Module.FinitePresentation R ((H m).obj K.obj) := hmfp
      have hmfinite : Module.Finite R ((H m).obj K.obj) := inferInstance
      have hmid :
          Module.Finite R ((H m).obj K.obj) ∧
            ∀ i : ℤ, m < i → Module.Coherent R ((H i).obj K.obj) := by
        refine ⟨hmfinite, ?_⟩
        intro i hi
        exact hH i
      exact
        ((boundedAbove_isMPseudoCoherent_tfae_of_coherentRing (R := R) K m).out 1 0).mp
          hmid

end
