import Mathlib
import StacksProject_2024.Chap10.Definition_10_5_1
import StacksProject_2024.Chap13.Lemma_13_28_2
import StacksProject_2024.Chap10.Definition_10_71_2
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Lemma_15_65_2
import StacksProject_2024.Chap15.Lemma_15_65_3
import StacksProject_2024.Chap13.Lemma_13_15_4
import StacksProject_2024.Chap13.Lemma_13_19_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DerivedCategory.TStructure

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace Module

/- Domain-style sampling for Lemma 15.65.4:
- primary domain: pseudo-coherence of modules concentrated in degree `0`, finite generation,
  finite presentation, and recursive finite free resolutions by syzygies;
- sampled owner declarations:
  `Module.Finite`,
  `Module.FinitePresentation`,
  `Module.Finite.iff_exists_surjective_free`,
  `ChainComplex.IsFiniteFreeResolution`;
- best owner abstraction: the source-facing recursive owner
  `Module.HasLengthFiniteFreeResolution`;
- primitive vs. derived:
  primitive data are finite generation in length `0` and, in the successor step, a surjective map
  from some finite free `R`-module onto `M`;
  derived API is the successor unpacking theorem and the pseudo-coherence characterizations below.

The local cover wrapper added no mathematical content beyond the canonical finite-generation owner
and the raw finite-free-surjection data needed for the recursive step, so it should be deleted
rather than preserved as a parallel public API.
-/

/-- `M` has a length-`n` finite free resolution if one can recursively resolve the kernel of a
surjection from a finite free module onto `M` for `n` steps. For `n = 0`, this is just finite
generation of `M`. -/
def HasLengthFiniteFreeResolution
    (R : Type u) [Ring R] (M : Type w) [AddCommGroup M] [Module R M] : ℕ → Prop
  | 0 => Module.Finite R M
  | n + 1 =>
      ∃ (F : Type w) (_ : AddCommGroup F) (_ : Module R F),
        Module.Free R F ∧ Module.Finite R F ∧
        ∃ f : F →ₗ[R] M, Function.Surjective f ∧
        HasLengthFiniteFreeResolution R (LinearMap.ker f) n

variable (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]

-- Proof sketch: unfold the recursive definition of `HasLengthFiniteFreeResolution` at `n + 1`.
/-- A successor-length finite free resolution is obtained by first taking a finite free cover and
then resolving its kernel for one fewer step. -/
theorem hasLengthFiniteFreeResolution_succ_iff (n : ℕ) :
    HasLengthFiniteFreeResolution R M (n + 1) ↔
      ∃ (F : Type v) (_ : AddCommGroup F) (_ : Module R F),
        Module.Free R F ∧ Module.Finite R F ∧
        ∃ f : F →ₗ[R] M, Function.Surjective f ∧
        HasLengthFiniteFreeResolution R (LinearMap.ker f) n := by
  rfl

end Module

section

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "KQ" => (HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ))

/-- Helper for Lemma 15.65.4: the degree-zero homology of the cochain single complex is the
original module. -/
noncomputable abbrev single_zero_complex_homology_iso
    (M : ModuleCat.{u} R) :
    (((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj M).homology 0) ≅ M :=
  HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) (0 : ℤ) M

/-- Helper for Lemma 15.65.4: the canonical kernel inclusion composed with the quotient map is
zero. -/
lemma kernel_subtype_comp_eq_zero
    {F M : ModuleCat.{u} R} (f : F ⟶ M) :
    f.hom.comp (LinearMap.ker f.hom).subtype = 0 := by
  -- Proof comment: every kernel element maps to zero by definition.
  ext x
  simpa [LinearMap.comp_apply, LinearMap.mem_ker] using x.2

/-- Helper for Lemma 15.65.4: the kernel sequence `0 → ker f → F → M → 0` is short exact when
`f` is surjective. -/
theorem kernel_cover_shortExact
    {F M : ModuleCat.{u} R} (f : F ⟶ M) (hf : Function.Surjective f.hom) :
    (ShortComplex.moduleCatMk (LinearMap.ker f.hom).subtype f.hom
      (kernel_subtype_comp_eq_zero (R := R) f)).ShortExact := by
  -- Proof comment: this is the standard kernel presentation of a surjective module map.
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    simpa using LinearMap.exact_subtype_ker_map f.hom
  · exact (ModuleCat.mono_iff_injective _).2 (LinearMap.ker f.hom).injective_subtype
  · exact (ModuleCat.epi_iff_surjective _).2 hf

/-- Helper for Lemma 15.65.4: the single complex on a finite free module is termwise finite
free. -/
lemma single_zero_complex_isTermwiseFiniteFree
    (F : ModuleCat.{u} R) [Module.Free R F] [Module.Finite R F] :
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj F).IsTermwiseFiniteFree := by
  -- Proof comment: degree `0` is the original finite free module, and every other degree is the
  -- zero module.
  refine ⟨fun i ↦ ?_⟩
  by_cases hi : i = 0
  · let e :
        (((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj F).X i) ≅ F := by
        subst hi
        simpa using HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) F
    exact ⟨Module.Free.of_equiv e.symm.toLinearEquiv, Module.Finite.equiv e.symm.toLinearEquiv⟩
  · let E : CochainComplex (ModuleCat.{u} R) ℤ :=
      (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj F
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

/-- Helper for Lemma 15.65.4: an `m`-pseudo-coherent witness also serves for every larger
pseudo-coherence index. -/
lemma isMPseudoCoherent_mono
    {K : DerivedCategory (ModuleCat.{u} R)} {m n : ℤ} (hmn : m ≤ n)
    (hK : K.IsMPseudoCoherent m) :
    K.IsMPseudoCoherent n := by
  rcases hK with ⟨E, hbounds, hfree, α, hαgt, hαm⟩
  -- Proof comment: keep the same bounded finite-free model and weaken the degree condition.
  refine ⟨E, hbounds, hfree, α, ?_, ?_⟩
  · intro i hi
    exact hαgt i (lt_of_le_of_lt hmn hi)
  · by_cases hnm : n = m
    · subst hnm
      simpa using hαm
    · have hmn' : m < n := by
        omega
      letI : IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) n).map α) := hαgt n hmn'
      infer_instance

/-- Helper for Lemma 15.65.4: the cohomology of a degree-zero derived module vanishes away from
degree `0`. -/
lemma single_zero_complex_homology_isZero_of_ne_local
    (M : ModuleCat.{u} R) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj (ModuleCat.single0Functor.obj M)) := by
  -- Proof comment: a degree-zero object lies in both `D^{≥ 0}` and `D^{≤ 0}`, so every nonzero
  -- cohomology object vanishes.
  by_cases hlt : i < 0
  · exact DerivedCategory.isZero_of_isGE _ 0 i hlt
  · have hgt : 0 < i := by
      omega
    exact DerivedCategory.isZero_of_isLE _ 0 i hgt

/-- Helper for Lemma 15.65.4: the `Q`-comparison on a degree-zero single complex is the identity
on zeroth homology. -/
lemma homology_map_singleFunctorIsoCompQ_app_zero_eq_id
    (M : ModuleCat.{u} R) :
    (DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map
        (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app M).hom) =
      𝟙 _ := by
  -- Proof comment: in degree `0`, the comparison from `Q(single M)` to `M[0]` is definitionally
  -- the identity once the owner is normalized.
  change
    (DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map
        (𝟙 (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj
          M))) =
      𝟙 _
  simp

/-- Helper for Lemma 15.65.4: if `f ≫ e.hom` is epi and `e` is an isomorphism, then `f` is epi. -/
lemma epi_of_epi_comp_iso
    {X Y Z : ModuleCat.{u} R} (f : X ⟶ Y) (e : Y ≅ Z) [Epi (f ≫ e.hom)] :
    Epi f := by
  -- Proof comment: postcompose parallel arrows with `e.inv` and cancel the resulting
  -- epimorphism.
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

/-- Helper for Lemma 15.65.4: after the canonical `H⁰(single₀ -)` identifications, the homology
map induced by a cover is the original module map. -/
lemma single_zero_cover_homology_map_eq
    {F M : ModuleCat.{u} R} (f : F ⟶ M) :
    let α :
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj F) ⟶
          ModuleCat.single0Functor.obj M :=
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app F).hom ≫
        ModuleCat.single0Functor.map f
    (DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map α ≫
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) (0 : ℤ)).app M).hom =
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) (0 : ℤ)).app F).hom ≫
        f := by
  -- Proof comment: first split off the `Q(single)` comparison, then apply naturality of the
  -- canonical `H⁰(single₀ -)` comparison.
  let α :
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj F) ⟶
        ModuleCat.single0Functor.obj M :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app F).hom ≫
      ModuleCat.single0Functor.map f
  let eF :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) (0 : ℤ)).app F
  let eM :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) (0 : ℤ)).app M
  have hnat :=
    NatIso.naturality_1
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) (0 : ℤ)) f
  have hnat' :
      (DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map
          (ModuleCat.single0Functor.map f) ≫
        eM.hom =
      eF.hom ≫ f := by
    have hstep1 :
        (DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map
            (ModuleCat.single0Functor.map f) ≫ eM.hom =
          eF.hom ≫
            (eF.inv ≫
              (DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map
                (ModuleCat.single0Functor.map f) ≫
                eM.hom) := by
      simpa [Category.assoc] using
        (Iso.hom_inv_id_assoc eF
          ((DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map
            (ModuleCat.single0Functor.map f) ≫
              eM.hom)).symm
    have hstep2 :
        eF.hom ≫
            (eF.inv ≫
              (DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map
                (ModuleCat.single0Functor.map f) ≫
                eM.hom) =
          eF.hom ≫ f := by
      simpa [eF, eM, Category.assoc] using congrArg (fun k ↦ eF.hom ≫ k) hnat
    exact hstep1.trans hstep2
  have hsplit :
      (DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map α ≫ eM.hom =
        (DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map
            (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app F).hom) ≫
          ((DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map
              (ModuleCat.single0Functor.map f) ≫
            eM.hom) := by
    dsimp [α]
    rw [Functor.map_comp]
    rfl
  have hmid :
      (DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map α ≫ eM.hom =
        (DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map
            (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app F).hom) ≫
          eF.hom ≫ f := by
    have hstep3 :
        (DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map
            (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app F).hom) ≫
          (DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map
              (ModuleCat.single0Functor.map f) ≫
            eM.hom =
          (DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map
            (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app F).hom) ≫
              eF.hom ≫ f := by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦
            (DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map
                (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app F).hom) ≫
              k)
          hnat'
    exact hsplit.trans hstep3
  have hfinal :
      (DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map
          (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app F).hom) ≫
        eF.hom ≫ f =
      eF.hom ≫ f := by
    rw [homology_map_singleFunctorIsoCompQ_app_zero_eq_id (R := R) F]
    change
      𝟙 ((DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).obj
        ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj F)) ≫
          (eF.hom ≫ f) =
        eF.hom ≫ f
    simpa using Category.id_comp (eF.hom ≫ f)
  exact hmid.trans hfinal

/-- Helper for Lemma 15.65.4: a surjective finite free cover induces an epimorphism on zeroth
derived homology. -/
lemma single_zero_cover_homology_epi_of_surjective
    {F M : ModuleCat.{u} R} (f : F ⟶ M) (hf : Function.Surjective f.hom) :
    let α :
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj F) ⟶
          ModuleCat.single0Functor.obj M :=
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app F).hom ≫
        ModuleCat.single0Functor.map f
    Epi ((DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map α) := by
  -- Proof comment: after the degree-zero comparison, the homology map is the original surjection
  -- followed by an isomorphism.
  let α :
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj F) ⟶
        ModuleCat.single0Functor.obj M :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app F).hom ≫
      ModuleCat.single0Functor.map f
  let eF :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) (0 : ℤ)).app F
  have hcomp :
      Epi ((DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map α ≫
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) (0 : ℤ)).app M).hom) := by
    rw [single_zero_cover_homology_map_eq (R := R) f]
    exact
      (ModuleCat.epi_iff_surjective _).2 <| by
        simpa [eF, Category.assoc] using hf.comp eF.toLinearEquiv.surjective
  exact
    epi_of_epi_comp_iso
      ((DerivedCategory.homologyFunctor (ModuleCat R) (0 : ℤ)).map α)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) (0 : ℤ)).app M)

/-- Helper for Lemma 15.65.4: a finite free module is `m`-pseudo-coherent for every integer
bound. -/
lemma finite_free_module_isMPseudoCoherent
    (F : ModuleCat.{u} R) (m : ℤ) [Module.Free R F] [Module.Finite R F] :
    F.IsMPseudoCoherent m := by
  let E : Cpx := (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj F
  let hEfree : E.IsTermwiseFiniteFree := single_zero_complex_isTermwiseFiniteFree (R := R) F
  let α : DerivedCategory.Q.obj E ⟶ ModuleCat.single0Functor.obj F :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app F).hom
  -- Proof comment: the single finite free complex itself is the bounded witness, and its
  -- comparison to `F[0]` is an isomorphism in every degree.
  refine ⟨E, ⟨0, 0, inferInstance, inferInstance⟩, hEfree, α, ?_, ?_⟩
  · intro i hi
    letI : IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) i).map α) :=
      Functor.map_isIso (DerivedCategory.homologyFunctor (ModuleCat R) i) α
    infer_instance
  · letI : IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) m).map α) :=
      Functor.map_isIso (DerivedCategory.homologyFunctor (ModuleCat R) m) α
    infer_instance

/-- Helper for Lemma 15.65.4: the kernel of a surjective finite free cover of a
`(-(d + 1))`-pseudo-coherent module is `(-d)`-pseudo-coherent. -/
lemma kernel_of_surjective_finite_free_cover_isMPseudoCoherent
    {F M : ModuleCat.{u} R} (f : F ⟶ M) (hf : Function.Surjective f.hom) (d : ℕ)
    [Module.Free R F] [Module.Finite R F]
    (hM : M.IsMPseudoCoherent (-(d + 1 : ℤ))) :
    (ModuleCat.of R (LinearMap.ker f.hom)).IsMPseudoCoherent (-(d : ℤ)) := by
  let S : ShortComplex (ModuleCat.{u} R) :=
    ShortComplex.moduleCatMk (LinearMap.ker f.hom).subtype f.hom
      (kernel_subtype_comp_eq_zero (R := R) f)
  have hS : S.ShortExact := by
    simpa [S] using kernel_cover_shortExact (R := R) f hf
  let T : Triangle DMod := hS.singleTriangle
  have hF : T.obj₂.IsMPseudoCoherent (-(d : ℤ)) := by
    -- Proof comment: the middle vertex is the finite free cover itself.
    simpa [T, S, ModuleCat.IsMPseudoCoherent] using
      finite_free_module_isMPseudoCoherent (R := R) F (-(d : ℤ))
  have hF' : T.obj₂.IsMPseudoCoherent ((-(d + 1 : ℤ)) + 1) := by
    simpa using hF
  have hM' : T.obj₃.IsMPseudoCoherent (-(d + 1 : ℤ)) := by
    -- Proof comment: the right vertex is the original module.
    simpa [T, S, ModuleCat.IsMPseudoCoherent] using hM
  have hK :
      T.obj₁.IsMPseudoCoherent ((-(d + 1 : ℤ)) + 1) :=
    isMPseudoCoherent_obj₁_of_distinguishedTriangle
      (R := R) T hS.singleTriangle_distinguished hF' hM'
  -- Proof comment: the index simplifies to `-d`.
  simpa [T, S, ModuleCat.IsMPseudoCoherent] using hK

-- Proof sketch: use Lemma `15.65.3` with `m = 0` and the vanishing of the higher cohomology of
-- `M[0]` for the forward implication; for the reverse implication, a surjection from a finite free
-- module onto `M` gives the required bounded finite free approximation concentrated in degree `0`.
/-- Lemma 15.65.4 (1): an `R`-module is `0`-pseudo-coherent exactly when it is finite. -/
@[stacks 064T]
theorem moduleCat_isZeroPseudoCoherent_iff_finite
    (M : ModuleCat.{u} R) :
    M.IsMPseudoCoherent 0 ↔ Module.Finite R M := by
  constructor
  · intro hM
    let E : Cpx := (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj M
    have hE : E.IsMPseudoCoherent 0 := by
      -- Proof comment: transport the pseudo-coherent witness from `M[0]` back to the chosen
      -- degree-zero cochain representative.
      exact
        isMPseudoCoherent_of_iso
          (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) (0 : ℤ)).app M).symm) 0 hM
    have hfiniteH : Module.Finite R (E.homology 0) := by
      -- Proof comment: all nonzero homology groups of a single complex vanish, so Lemma `15.65.3`
      -- applies in degree `0`.
      exact CochainComplex.homology_finite_of_isMPseudoCoherent
        (R := R) hE
        (fun i hi ↦ HomologicalComplex.isZero_single_obj_homology
          (ComplexShape.up ℤ) (0 : ℤ) M i (by omega))
    letI : Module.Finite R (E.homology 0) := hfiniteH
    -- Proof comment: identify the zeroth homology of the single complex with the original module.
    exact Module.Finite.equiv (single_zero_complex_homology_iso (R := R) M).toLinearEquiv
  · intro hM
    rcases (Module.Finite.iff_exists_surjective_free R M).1 hM with ⟨n, f, hf⟩
    let F : ModuleCat.{u} R := ModuleCat.of R (Fin n → R)
    let g : F ⟶ M := ModuleCat.ofHom f
    let E : Cpx := (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj F
    let hEfree : E.IsTermwiseFiniteFree := single_zero_complex_isTermwiseFiniteFree (R := R) F
    let α : DerivedCategory.Q.obj E ⟶ ModuleCat.single0Functor.obj M :=
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app F).hom ≫
        ModuleCat.single0Functor.map g
    -- Proof comment: the chosen finite free cover supplies the bounded finite-free witness.
    refine ⟨E, ⟨0, 0, inferInstance, inferInstance⟩, hEfree, α, ?_, ?_⟩
    · intro i hi
      have hi0 : i ≠ 0 := by
        omega
      let hsrcSingle :
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
            (ModuleCat.single0Functor.obj F)) :=
        single_zero_complex_homology_isZero_of_ne_local (R := R) F i hi0
      let hsrc :
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj (DerivedCategory.Q.obj E)) := by
        exact
          ((((DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
            ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app
            F)).isZero_iff).2 hsrcSingle)
      let htgt :
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
            (ModuleCat.single0Functor.obj M)) :=
        single_zero_complex_homology_isZero_of_ne_local (R := R) M i hi0
      exact hsrc.isIso htgt ((DerivedCategory.homologyFunctor (ModuleCat R) i).map α)
    · exact single_zero_cover_homology_epi_of_surjective (R := R) g hf

-- Proof sketch: if `M` is `(-1)`-pseudo-coherent, combine part `(1)` with Lemma `15.65.2` for the
-- kernel of a finite free cover to prove finite presentation; conversely, a finite presentation is
-- a length-one finite free resolution and hence a `(-1)`-pseudo-coherent approximation.
/-- Lemma 15.65.4 (2): an `R`-module is `(-1)`-pseudo-coherent exactly when it is finitely
presented. -/
@[stacks 064T]
theorem moduleCat_isMinusOnePseudoCoherent_iff_finitePresentation
    (M : ModuleCat.{u} R) :
    M.IsMPseudoCoherent (-1) ↔ Module.FinitePresentation R M := by
  constructor
  · intro hM
    have hM0 : M.IsMPseudoCoherent 0 := by
      -- Proof comment: first forget the stronger negative bound and keep only the degree-zero
      -- pseudo-coherence information.
      rw [ModuleCat.IsMPseudoCoherent] at hM ⊢
      exact isMPseudoCoherent_mono (R := R) (show (-1 : ℤ) ≤ 0 by omega) hM
    have hfiniteM : Module.Finite R M :=
      (moduleCat_isZeroPseudoCoherent_iff_finite (R := R) M).1 hM0
    rcases (Module.Finite.iff_exists_surjective_free R M).1 hfiniteM with ⟨n, f, hf⟩
    let F : ModuleCat.{u} R := ModuleCat.of R (Fin n → R)
    let g : F ⟶ M := ModuleCat.ofHom f
    have hkerPc :
        (ModuleCat.of R (LinearMap.ker g.hom)).IsMPseudoCoherent 0 :=
      kernel_of_surjective_finite_free_cover_isMPseudoCoherent (R := R) g hf 0 hM
    have hkerFinite :
        Module.Finite R (LinearMap.ker g.hom) :=
      (moduleCat_isZeroPseudoCoherent_iff_finite (R := R) (ModuleCat.of R (LinearMap.ker g.hom))).1
        hkerPc
    letI : Module.Finite R (LinearMap.ker g.hom) := hkerFinite
    have hkerFG : (LinearMap.ker g.hom).FG := by
      -- Proof comment: a finite module has finitely generated underlying submodule.
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
    -- Proof comment: a surjection from a finite free module with finitely generated kernel is a
    -- finite presentation.
    exact Module.finitePresentation_of_surjective g.hom hf hkerFG
  · intro hM
    rcases (Module.FinitePresentation.iff_exists_exact_free_sequence R M).1 hM with
      ⟨n, m, f, g, hfg, hg⟩
    let F₀ : ModuleCat.{u} R := ModuleCat.of R (Fin n → R)
    let q : F₀ ⟶ M := ModuleCat.ofHom g
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
    let S : ShortComplex (ModuleCat.{u} R) :=
      ShortComplex.moduleCatMk (LinearMap.ker q.hom).subtype q.hom
        (kernel_subtype_comp_eq_zero (R := R) q)
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

-- Proof sketch: argue by induction on `d`. The cases `d = 0` and `d = 1` are parts `(1)` and
-- `(2)`. For the inductive step, peel off a finite free cover of `M`, apply Lemma `15.65.2` to the
-- kernel, and translate the recursive kernel condition using `Module.HasLengthFiniteFreeResolution`.
/-- Lemma 15.65.4 (3): for `d : ℕ`, an `R`-module is `(-d)`-pseudo-coherent exactly when it admits
a length-`d` finite free resolution. -/
-- TODO: run the induction on `d` from the source proof, using the finite free cover plus kernel
-- syzygy step from part `(2)` as the successor step in `Module.HasLengthFiniteFreeResolution`.
theorem moduleCat_isNegPseudoCoherent_iff_hasFiniteFreeResolutionLength
    (M : ModuleCat.{u} R) (d : ℕ) :
    M.IsMPseudoCoherent (-(d : ℤ)) ↔ Module.HasLengthFiniteFreeResolution R M d := by
  induction d generalizing M with
  | zero =>
      -- Proof comment: the length-zero resolution condition is exactly finite generation.
      simpa [Module.HasLengthFiniteFreeResolution] using
        (moduleCat_isZeroPseudoCoherent_iff_finite (R := R) M)
  | succ d ih =>
      constructor
      · intro hM
        have hM0 : M.IsMPseudoCoherent 0 := by
          -- Proof comment: a negative-degree pseudo-coherent module is in particular
          -- degree-zero pseudo-coherent.
          rw [ModuleCat.IsMPseudoCoherent] at hM ⊢
          exact isMPseudoCoherent_mono (R := R) (show (-(d + 1 : ℤ)) ≤ 0 by omega) hM
        have hfiniteM : Module.Finite R M :=
          (moduleCat_isZeroPseudoCoherent_iff_finite (R := R) M).1 hM0
        rcases (Module.Finite.iff_exists_surjective_free R M).1 hfiniteM with ⟨n, f, hf⟩
        let F : ModuleCat.{u} R := ModuleCat.of R (Fin n → R)
        let g : F ⟶ M := ModuleCat.ofHom f
        have hkerPc :
            (ModuleCat.of R (LinearMap.ker g.hom)).IsMPseudoCoherent (-(d : ℤ)) :=
          kernel_of_surjective_finite_free_cover_isMPseudoCoherent (R := R) g hf d hM
        have hkerRes :
            Module.HasLengthFiniteFreeResolution R (LinearMap.ker g.hom) d :=
          (ih (ModuleCat.of R (LinearMap.ker g.hom))).1 hkerPc
        -- Proof comment: this is exactly the recursive resolution step from the source proof.
        exact
          (Module.hasLengthFiniteFreeResolution_succ_iff (R := R) (M := M) d).2
            ⟨Fin n → R, inferInstance, inferInstance, inferInstance, inferInstance, f, hf, hkerRes⟩
      · intro hM
        rcases (Module.hasLengthFiniteFreeResolution_succ_iff (R := R) (M := M) d).1 hM with
          ⟨F, _hFadd, _hFmod, hfree, hfinite, f, hf, hker⟩
        let F₀ : ModuleCat.{u} R := ModuleCat.of R F
        let q : F₀ ⟶ M := ModuleCat.ofHom f
        letI : Module.Free R F := hfree
        letI : Module.Finite R F := hfinite
        have hkerPc :
            (ModuleCat.of R (LinearMap.ker f)).IsMPseudoCoherent (-(d : ℤ)) :=
          (ih (ModuleCat.of R (LinearMap.ker f))).2 hker
        let S : ShortComplex (ModuleCat.{u} R) :=
          ShortComplex.moduleCatMk (LinearMap.ker q.hom).subtype q.hom
            (kernel_subtype_comp_eq_zero (R := R) q)
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
        -- Proof comment: the distinguished triangle for the short exact sequence produces the
        -- target module as the next pseudo-coherent syzygy.
        simpa [T, S, ModuleCat.IsMPseudoCoherent] using
          (isMPseudoCoherent_obj₃_of_distinguishedTriangle
            (R := R) T hS.singleTriangle_distinguished hleft' hmiddle)

/-- Helper for Lemma 15.65.4: conjugating the `Qh`-image of a cochain map along the canonical
comparison `quotientCompQhIso` recovers its `Q`-image. -/
lemma quotientCompQhIso_homCongr_map
    {K L : Cpx} (f : K ⟶ L) :
    (Iso.homCongr ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app K)
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app L))
      (DerivedCategory.Qh.map ((KQ).map f)) =
    DerivedCategory.Q.map f := by
  -- Proof comment: this is the naturality square of `quotientCompQhIso`, rewritten as an
  -- equality after conjugating from the homotopy-category presentation back to `Q`.
  change
    (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app K ≫
        DerivedCategory.Qh.map ((KQ).map f) ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app L =
      DerivedCategory.Q.map f
  have hnat :
      DerivedCategory.Qh.map ((KQ).map f) ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app L =
        (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app K ≫
          DerivedCategory.Q.map f := by
    simpa [Functor.comp_map] using
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.naturality f).symm
  calc
    (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app K ≫
        DerivedCategory.Qh.map ((KQ).map f) ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app L =
      (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app K ≫
        ((DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app K ≫
          DerivedCategory.Q.map f) := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app K ≫ k)
                hnat
    _ = DerivedCategory.Q.map f := by
      simpa [Category.assoc] using
        Iso.inv_hom_id_assoc
          ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app K)
          (DerivedCategory.Q.map f)

/-- Helper for Lemma 15.65.4: a bounded-above termwise finite free witness for `M[0]` can be
strictified to an actual cochain map into the degree-zero single complex. -/
lemma exists_strict_single0_map_of_pseudoCoherent_witness
    {E : Cpx} {M : ModuleCat.{u} R} [E.IsTermwiseFiniteFree]
    (b : ℤ) (hEb : E.IsStrictlyLE b)
    (α : DerivedCategory.Q.obj E ⟶ ModuleCat.single0Functor.obj M) [IsIso α] :
    ∃ β : E ⟶ (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M,
      QuasiIso β ∧
        DerivedCategory.Q.map β =
          α ≫ ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app M).inv := by
  let P : CochainComplex.ProjectiveMinus (ModuleCat R) :=
    ⟨⟨E, (CochainComplex.minus_iff (ModuleCat R) E).2 ⟨b, hEb⟩⟩, fun n ↦ by
      -- Proof comment: every term of the finite free witness is projective.
      let _ : Module.Free R (E.X n) := inferInstance
      infer_instance⟩
  let S : Cpx := (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M
  let α' : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj S :=
    α ≫ ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app M).inv
  let αh :
      DerivedCategory.Qh.obj ((KQ).obj E) ⟶ DerivedCategory.Qh.obj ((KQ).obj S) :=
    ((Iso.homCongr ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app E)
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app S)).symm) α'
  obtain ⟨βh, hβh⟩ :=
    (CochainComplex.homotopyCategory_to_derived_bijective_of_boundedAbove_projective
      (𝒜 := ModuleCat R) P S).surjective αh
  obtain ⟨β, hβ⟩ := (KQ).map_surjective βh
  have hQhβ : DerivedCategory.Qh.map ((KQ).map β) = αh := by
    simpa [hβ] using hβh
  have hQβ :
      DerivedCategory.Q.map β =
        α ≫ ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app M).inv := by
    -- Proof comment: transport the homotopy-category lift back through `quotientCompQhIso`.
    calc
      DerivedCategory.Q.map β =
        (Iso.homCongr ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app E)
          ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app S))
          (DerivedCategory.Qh.map ((KQ).map β)) := by
            symm
            exact quotientCompQhIso_homCongr_map (R := R) β
      _ =
        (Iso.homCongr ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app E)
          ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app S))
          αh := by
            rw [hQhβ]
      _ = α' := by
            simpa [αh] using
              Equiv.apply_symm_apply
                (Iso.homCongr ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app E)
                  ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app S))
                α'
      _ =
        α ≫ ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app M).inv := by
            rfl
  refine ⟨β, ?_, hQβ⟩
  -- Proof comment: the strictified map is a quasi-isomorphism because its image in `D(R)` is the
  -- original isomorphism witness.
  letI : IsIso α := inferInstance
  letI : IsIso
      (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app M).inv) := by
    infer_instance
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  rw [hQβ]
  let eα : DerivedCategory.Q.obj E ≅ ModuleCat.single0Functor.obj M := asIso α
  let eS : DerivedCategory.Q.obj S ≅ ModuleCat.single0Functor.obj M :=
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app M
  change IsIso (eα.hom ≫ eS.inv)
  infer_instance

/-- Helper for Lemma 15.65.4: restricting the extension of a chain complex along
`embeddingDownNat` recovers the original chain complex. -/
lemma restriction_extend_embeddingDownNat_iso
    (F : ChainComplex (ModuleCat R) ℕ) :
    Nonempty (((F.extend ComplexShape.embeddingDownNat).restriction
      ComplexShape.embeddingDownNat) ≅ F) := by
  -- Proof comment: both component identifications are the canonical `restrictionXIso` followed
  -- by `extendXIso` at degree `-n`.
  refine ⟨HomologicalComplex.Hom.isoOfComponents (fun n ↦ ?_) (fun i j hij ↦ ?_)⟩
  · exact
      (F.extend ComplexShape.embeddingDownNat).restrictionXIso
          ComplexShape.embeddingDownNat
          (i := n) (i' := -((n : ℕ) : ℤ)) rfl ≪≫
        (F.extendXIso ComplexShape.embeddingDownNat
          (i := n) (i' := -((n : ℕ) : ℤ)) rfl)
  · -- Proof comment: after rewriting both restriction and extension differentials, the square
    -- becomes the defining naturality of the two canonical degree identifications.
    rw [HomologicalComplex.restriction_d_eq
      (K := F.extend ComplexShape.embeddingDownNat)
      (e := ComplexShape.embeddingDownNat)
      (i := i) (j := j)
      (i' := -((i : ℕ) : ℤ)) (j' := -((j : ℕ) : ℤ)) rfl rfl]
    rw [HomologicalComplex.extend_d_eq
      (K := F) (e := ComplexShape.embeddingDownNat)
      (i := i) (j := j)
      (i' := -((i : ℕ) : ℤ)) (j' := -((j : ℕ) : ℤ)) rfl rfl]
    simp [Category.assoc]

/-- Helper for Lemma 15.65.4: restricting the degree-zero cochain single complex along
`embeddingDownNat` gives the standard chain single complex. -/
lemma restriction_single0_iso
    (M : ModuleCat.{u} R) :
    Nonempty
      ((((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M).restriction
        ComplexShape.embeddingDownNat) ≅
        (ChainComplex.single₀ (ModuleCat R)).obj M) := by
  let e₁ :
      (((((ChainComplex.single₀ (ModuleCat R)).obj M).extend ComplexShape.embeddingDownNat).restriction
        ComplexShape.embeddingDownNat) ≅
        (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M).restriction
          ComplexShape.embeddingDownNat)) :=
    ((ComplexShape.embeddingDownNat.restrictionFunctor (ModuleCat R)).mapIso
      (HomologicalComplex.extendSingleIso
        ComplexShape.embeddingDownNat M (0 : ℕ) (0 : ℤ) rfl))
  obtain ⟨e₂⟩ := restriction_extend_embeddingDownNat_iso (R := R)
    ((ChainComplex.single₀ (ModuleCat R)).obj M)
  -- Proof comment: first identify the restricted cochain single complex with the restricted
  -- extension of the chain single complex, then collapse restriction-after-extension.
  exact ⟨e₁.symm ≪≫ e₂⟩

/-- Helper for Lemma 15.65.4: restriction along `embeddingDownNat` transports the termwise finite
free data of a bounded-above cochain witness to the resulting chain complex. -/
lemma restriction_embeddingDownNat_termwise_free_finite
    {E : Cpx} [E.IsTermwiseFiniteFree] :
    ChainComplex.IsTermwiseFree (R := R) (E.restriction ComplexShape.embeddingDownNat) ∧
      ChainComplex.IsTermwiseFinite (R := R) (E.restriction ComplexShape.embeddingDownNat) := by
  constructor
  · intro n
    -- Proof comment: each restricted degree is canonically the original degree `-n`.
    let e :
        (E.restriction ComplexShape.embeddingDownNat).X n ≅ E.X (-((n : ℕ) : ℤ)) :=
      E.restrictionXIso ComplexShape.embeddingDownNat rfl
    letI : Module.Free R (E.X (-((n : ℕ) : ℤ))) := inferInstance
    exact Module.Free.of_equiv e.symm.toLinearEquiv
  · intro n
    -- Proof comment: the same degree identification transports finite generation as well.
    let e :
        (E.restriction ComplexShape.embeddingDownNat).X n ≅ E.X (-((n : ℕ) : ℤ)) :=
      E.restrictionXIso ComplexShape.embeddingDownNat rfl
    letI : Module.Finite R (E.X (-((n : ℕ) : ℤ))) := inferInstance
    exact Module.Finite.equiv e.symm.toLinearEquiv

/-- Helper for Lemma 15.65.4: in positive chain degrees, restricting a quasi-isomorphism to the
degree-zero single complex preserves the quasi-isomorphism property. -/
lemma restriction_single_quasiIsoAt_succ_of_quasiIso
    {E : Cpx} {M : ModuleCat.{u} R}
    (β : E ⟶ (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)
    (hβ : QuasiIso β) (n : ℕ) :
    QuasiIsoAt
      (HomologicalComplex.restrictionMap β ComplexShape.embeddingDownNat ≫
        (Classical.choice (restriction_single0_iso (R := R) M)).hom)
      (n + 1) := by
  let γ := HomologicalComplex.restrictionMap β ComplexShape.embeddingDownNat
  have hγ : QuasiIsoAt γ (n + 1) := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have hβat : QuasiIsoAt β (-((n + 1 : ℕ) : ℤ)) := hβ.quasiIsoAt (-((n + 1 : ℕ) : ℤ))
    rw [quasiIsoAt_iff_isIso_homologyMap] at hβat
    let eβ :
        E.homology (-((n + 1 : ℕ) : ℤ)) ≅
          ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M).homology
            (-((n + 1 : ℕ) : ℤ)) :=
      asIso (HomologicalComplex.homologyMap β (-((n + 1 : ℕ) : ℤ)))
    have htarget_full :
        IsZero
          (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M).homology
            (-((n + 1 : ℕ) : ℤ))) := by
      -- Proof comment: the degree-zero single complex has no homology in negative degrees.
      exact
        HomologicalComplex.isZero_single_obj_homology
          (ComplexShape.up ℤ) (0 : ℤ) M (-((n + 1 : ℕ) : ℤ)) (by omega)
    have hsource_full : IsZero (E.homology (-((n + 1 : ℕ) : ℤ))) :=
      IsZero.of_iso htarget_full eβ
    let eSource :
        (E.restriction ComplexShape.embeddingDownNat).homology (n + 1) ≅
          E.homology (-((n + 1 : ℕ) : ℤ)) := by
      -- Proof comment: away from degree `0`, the standard restriction-homology comparison
      -- applies directly.
      simpa using
        (HomologicalComplex.restrictionHomologyIso
          E ComplexShape.embeddingDownNat (n + 2) (n + 1) n
          (by simp) (by simp)
          (by simp : ComplexShape.embeddingDownNat.f (n + 2) = -((n + 2 : ℕ) : ℤ))
          (by simp : ComplexShape.embeddingDownNat.f (n + 1) = -((n + 1 : ℕ) : ℤ))
          (by simp : ComplexShape.embeddingDownNat.f n = -((n : ℕ) : ℤ))
          (by
            calc
              (ComplexShape.up ℤ).prev (-((n + 1 : ℕ) : ℤ)) =
                  -((n + 1 : ℕ) : ℤ) - 1 := by
                    simpa using (CochainComplex.prev ℤ (-((n + 1 : ℕ) : ℤ)))
              _ = -((n + 2 : ℕ) : ℤ) := by omega)
          (by
            calc
              (ComplexShape.up ℤ).next (-((n + 1 : ℕ) : ℤ)) =
                  -((n + 1 : ℕ) : ℤ) + 1 := by
                    simpa using (CochainComplex.next ℤ (-((n + 1 : ℕ) : ℤ)))
              _ = -((n : ℕ) : ℤ) := by omega))
    have hsource :
        IsZero ((E.restriction ComplexShape.embeddingDownNat).homology (n + 1)) :=
      (Iso.isZero_iff eSource).2 hsource_full
    obtain ⟨eSingle⟩ := restriction_single0_iso (R := R) M
    have htarget_single :
        IsZero (((ChainComplex.single₀ (ModuleCat R)).obj M).homology (n + 1)) := by
      -- Proof comment: the target chain single complex has no positive-degree homology.
      exact
        HomologicalComplex.isZero_single_obj_homology
          (ComplexShape.down ℕ) (0 : ℕ) M (n + 1) (by omega)
    have htarget :
        IsZero
          ((((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M).restriction
              ComplexShape.embeddingDownNat).homology (n + 1)) :=
      (Iso.isZero_iff (HomologicalComplex.homologyMapIso eSingle (n + 1))).2 htarget_single
    -- Proof comment: any morphism between zero homology objects is an isomorphism.
    exact IsZero.isIso hsource htarget (HomologicalComplex.homologyMap γ (n + 1))
  -- Proof comment: postcomposing with the canonical restriction-to-`single₀` isomorphism does not
  -- change the quasi-isomorphism property in this degree.
  rw [quasiIsoAt_iff_isIso_homologyMap] at hγ ⊢
  letI :
      IsIso
        (HomologicalComplex.homologyMap
          (HomologicalComplex.restrictionMap β ComplexShape.embeddingDownNat) (n + 1)) := hγ
  letI :
      IsIso
        (HomologicalComplex.homologyMap
          ((Classical.choice (restriction_single0_iso (R := R) M)).hom) (n + 1)) := by
    infer_instance
  let e₁ :
      ((E.restriction ComplexShape.embeddingDownNat).homology (n + 1)) ≅
        ((((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M).restriction
            ComplexShape.embeddingDownNat).homology (n + 1)) :=
    asIso
      (HomologicalComplex.homologyMap
        (HomologicalComplex.restrictionMap β ComplexShape.embeddingDownNat) (n + 1))
  let e₂ :
      ((((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M).restriction
          ComplexShape.embeddingDownNat).homology (n + 1)) ≅
        ((ChainComplex.single₀ (ModuleCat R)).obj M).homology (n + 1) :=
    asIso
      (HomologicalComplex.homologyMap
        ((Classical.choice (restriction_single0_iso (R := R) M)).hom) (n + 1))
  refine ⟨⟨e₂.inv ≫ e₁.inv, ?_, ?_⟩⟩
  · simp [HomologicalComplex.homologyMap_comp, Category.assoc, e₁, e₂]
  · simp [HomologicalComplex.homologyMap_comp, Category.assoc, e₁, e₂]

/-- Helper for Lemma 15.65.4: in the degree-zero single chain complex, the incoming differential
vanishes after identifying the zeroth term with the underlying module. -/
lemma single0_objXSelf_comp_d_eq_zero
    (M : ModuleCat.{u} R) :
    ((ChainComplex.single₀ (ModuleCat R)).obj M).d 1 0 ≫
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) (0 : ℕ) M).hom = 0 := by
  -- Proof comment: the degree-`1` term of a degree-zero single complex is zero, so its incoming
  -- differential into degree `0` vanishes.
  rw [HomologicalComplex.single_obj_d]
  simp [ChainComplex.single₀ObjXSelf]
  rfl

/-- Helper for Lemma 15.65.4: on a degree-zero single chain complex, the canonical map from
zeroth opcycles to the module is the descended degree-zero term map. -/
lemma single0_opcycles_self_inv_eq_descOpcycles
    (M : ModuleCat.{u} R) :
    (HomologicalComplex.singleObjOpcyclesSelfIso
      (ComplexShape.down ℕ) (0 : ℕ) M).inv =
    ((ChainComplex.single₀ (ModuleCat R)).obj M).descOpcycles
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) (0 : ℕ) M).hom
      1 (by simp) (single0_objXSelf_comp_d_eq_zero (R := R) M) := by
  -- Proof comment: both maps out of zeroth opcycles are determined by their composites with
  -- `pOpcycles`.
  apply (cancel_epi (((ChainComplex.single₀ (ModuleCat R)).obj M).pOpcycles 0)).1
  calc
    ((ChainComplex.single₀ (ModuleCat R)).obj M).pOpcycles 0 ≫
        (HomologicalComplex.singleObjOpcyclesSelfIso
          (ComplexShape.down ℕ) (0 : ℕ) M).inv =
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) (0 : ℕ) M).hom := by
          simpa [ChainComplex.single₀ObjXSelf] using
            (HomologicalComplex.pOpcycles_singleObjOpcyclesSelfIso_inv
              (c := ComplexShape.down ℕ) (j := (0 : ℕ)) (A := M))
    _ =
      ((ChainComplex.single₀ (ModuleCat R)).obj M).pOpcycles 0 ≫
        ((ChainComplex.single₀ (ModuleCat R)).obj M).descOpcycles
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.down ℕ) (0 : ℕ) M).hom
          1 (by simp) (single0_objXSelf_comp_d_eq_zero (R := R) M) := by
            symm
            simpa using
              (HomologicalComplex.p_descOpcycles
                (K := (ChainComplex.single₀ (ModuleCat R)).obj M)
                (i := (0 : ℕ))
                (k := (HomologicalComplex.singleObjXSelf
                  (ComplexShape.down ℕ) (0 : ℕ) M).hom)
                (j := 1)
                (hj := by simp)
                (hk := single0_objXSelf_comp_d_eq_zero (R := R) M))

/-- Helper for Lemma 15.65.4: a chain map to the degree-zero single complex is a quasi-isomorphism
in degree `0` once its degree-zero augmentation is exact and surjective. -/
lemma single_zero_chain_quasiIsoAt_zero_of_exact_epi
    {F : ChainComplex (ModuleCat.{u} R) ℕ} {M : ModuleCat.{u} R}
    (π : F ⟶ (ChainComplex.single₀ (ModuleCat R)).obj M)
    (hExact :
      Function.Exact (F.d 1 0).hom
        ((π.f 0 ≫
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.down ℕ) (0 : ℕ) M).hom).hom))
    (hEpi :
      Epi
        (π.f 0 ≫
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.down ℕ) (0 : ℕ) M).hom)) :
    QuasiIsoAt π 0 := by
  -- Proof comment: at degree `0`, `single₀ M` has zero outgoing and incoming differentials, so
  -- `ChainComplex.quasiIsoAt₀_iff` reduces the claim to exactness and epimorphy of the
  -- augmentation map.
  rw [ChainComplex.quasiIsoAt₀_iff]
  refine
    (CategoryTheory.ShortComplex.quasiIso_iff_of_zeros' _
      (by
        simp [HomologicalComplex.shortComplexFunctor']
        rfl)
      (by
        simp [HomologicalComplex.shortComplexFunctor']
        rfl)
      (by
        simp [HomologicalComplex.shortComplexFunctor']
        rfl)).2 ?_
  refine ⟨?_, ?_⟩
  · let S : CategoryTheory.ShortComplex (ModuleCat R) :=
      CategoryTheory.ShortComplex.mk (F.d 1 0) (π.f 0) (by
        simpa using (π.comm 1 0).symm)
    change S.Exact
    rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S]
    simpa using hExact
  · simpa using hEpi

/-- Helper for Lemma 15.65.4: the remaining degree-`0` restriction step is the only place where
the standard restriction-homology API must be replaced by a direct boundary comparison. -/
lemma restriction_single_quasiIsoAt_zero_of_quasiIso
    {E : Cpx} {M : ModuleCat.{u} R}
    (β : E ⟶ (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)
    (hβ : QuasiIso β) :
    QuasiIsoAt
      (HomologicalComplex.restrictionMap β ComplexShape.embeddingDownNat ≫
        (Classical.choice (restriction_single0_iso (R := R) M)).hom)
      0 := by
  -- Route correction: the source proof computes degree `0` by comparing the restricted chain
  -- homology short complex with an augmentation that is already exact at degree `0`. The current
  -- route only strictifies a derived isomorphism to a raw cochain map `β`, and `QuasiIso β` alone
  -- does not imply exactness of the restricted degree-zero augmentation.
  --
  -- TODO: replace `exists_strict_single0_map_of_pseudoCoherent_witness` by a source-faithful
  -- strictification/truncation lemma that produces a bounded-above finite free model whose
  -- restricted degree-zero augmentation is exact and surjective, then apply
  -- `single_zero_chain_quasiIsoAt_zero_of_exact_epi`.
  sorry

/-- Helper for Lemma 15.65.4: once the boundary degree is handled separately, the restricted
augmentation is a quasi-isomorphism degreewise. -/
lemma restriction_single_quasiIso_of_quasiIso
    {E : Cpx} {M : ModuleCat.{u} R}
    (β : E ⟶ (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)
    (hβ : QuasiIso β) :
    QuasiIso
      (HomologicalComplex.restrictionMap β ComplexShape.embeddingDownNat ≫
        (Classical.choice (restriction_single0_iso (R := R) M)).hom) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
      exact restriction_single_quasiIsoAt_zero_of_quasiIso (R := R) β hβ
  | succ n =>
      exact restriction_single_quasiIsoAt_succ_of_quasiIso (R := R) β hβ n

/-- Helper for Lemma 15.65.4: a strict quasi-isomorphism from a termwise finite free cochain
complex to the degree-zero single complex restricts to a finite free chain resolution. -/
lemma restriction_single_quasiIso_isFiniteFreeResolution
    {E : Cpx} [E.IsTermwiseFiniteFree] {M : ModuleCat.{u} R}
    (β : E ⟶ (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)
    (hβ : QuasiIso β) :
    ChainComplex.IsFiniteFreeResolution
      (HomologicalComplex.restrictionMap β ComplexShape.embeddingDownNat ≫
        (Classical.choice (restriction_single0_iso (R := R) M)).hom) := by
  let π :
      E.restriction ComplexShape.embeddingDownNat ⟶
        (ChainComplex.single₀ (ModuleCat R)).obj M :=
    HomologicalComplex.restrictionMap β ComplexShape.embeddingDownNat ≫
      (Classical.choice (restriction_single0_iso (R := R) M)).hom
  have hπquasi : QuasiIso π :=
    restriction_single_quasiIso_of_quasiIso (R := R) β hβ
  have hterm :
      ChainComplex.IsTermwiseFree (R := R) (E.restriction ComplexShape.embeddingDownNat) ∧
        ChainComplex.IsTermwiseFinite (R := R) (E.restriction ComplexShape.embeddingDownNat) :=
    restriction_embeddingDownNat_termwise_free_finite (R := R) (E := E)
  -- Proof comment: after isolating the degree-`0` transport into
  -- `restriction_single_quasiIsoAt_zero_of_quasiIso`, the remaining resolution data are just the
  -- restricted quasi-isomorphism together with the transported termwise finite-free structure.
  exact
    { toIsFreeResolution :=
        { toQuasiIso := hπquasi
          termwise_free := hterm.1 }
      termwise_finite := hterm.2 }

/-- Helper for Lemma 15.65.4: extending a finite free chain resolution along `embeddingDownNat`
gives a bounded-above termwise finite free cochain complex. -/
lemma extend_embeddingDownNat_isTermwiseFiniteFree
    {M : ModuleCat.{u} R} {F : ChainComplex (ModuleCat R) ℕ}
    (π : F ⟶ (ChainComplex.single₀ (ModuleCat R)).obj M)
    [ChainComplex.IsFiniteFreeResolution π] :
    CochainComplex.IsTermwiseFiniteFree (F.extend ComplexShape.embeddingDownNat) := by
  -- Proof comment: nonpositive cochain degrees come from the original finite free chain terms,
  -- while positive cochain degrees vanish after extension.
  refine ⟨fun n ↦ ?_⟩
  by_cases hnonpos : n ≤ 0
  · let e :
        (F.extend ComplexShape.embeddingDownNat).X n ≅ F.X (Int.toNat (-n)) :=
      F.extendXIso ComplexShape.embeddingDownNat (by
        have hneg : 0 ≤ -n := by
          omega
        simpa [ComplexShape.embeddingDownNat, Int.toNat_of_nonneg hneg] using
          (show -((Int.toNat (-n) : ℕ) : ℤ) = n by
            rw [Int.toNat_of_nonneg hneg]
            omega))
    have hfree : Module.Free R (F.X (Int.toNat (-n))) :=
      ChainComplex.IsFreeResolution.free (R := R) π (Int.toNat (-n))
    have hfinite : Module.Finite R (F.X (Int.toNat (-n))) :=
      ChainComplex.IsFiniteFreeResolution.finite (R := R) π (Int.toNat (-n))
    letI : Module.Free R (F.X (Int.toNat (-n))) := hfree
    letI : Module.Finite R (F.X (Int.toNat (-n))) := hfinite
    exact
      ⟨Module.Free.of_equiv e.symm.toLinearEquiv,
        Module.Finite.equiv e.symm.toLinearEquiv⟩
  · have hpos : 0 < n := by
      omega
    let hzero : IsZero ((F.extend ComplexShape.embeddingDownNat).X n) :=
      F.isZero_extend_X ComplexShape.embeddingDownNat n fun j hj ↦ by
        have hnonpos' : (ComplexShape.embeddingDownNat.f j : ℤ) ≤ 0 := by
          simp [ComplexShape.embeddingDownNat]
        rw [hj] at hnonpos'
        omega
    letI : Subsingleton ↥((F.extend ComplexShape.embeddingDownNat).X n) :=
      ModuleCat.subsingleton_of_isZero hzero
    have hfree : Module.Free R ((F.extend ComplexShape.embeddingDownNat).X n) :=
      Module.Free.of_subsingleton (R := R) (N := ↥((F.extend ComplexShape.embeddingDownNat).X n))
    have hfinite : Module.Finite R ((F.extend ComplexShape.embeddingDownNat).X n) := by
      let e : ModuleCat.of R PUnit ≅ (F.extend ComplexShape.embeddingDownNat).X n :=
        (ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)).isoZero ≪≫ hzero.isoZero.symm
      exact Module.Finite.equiv e.toLinearEquiv
    exact ⟨hfree, hfinite⟩

/-- Helper for Lemma 15.65.4: the cochain view of a finite free chain resolution represents the
degree-zero derived object of the resolved module. -/
lemma extend_resolution_single0_iso
    {M : ModuleCat.{u} R} {F : ChainComplex (ModuleCat R) ℕ}
    (π : F ⟶ (ChainComplex.single₀ (ModuleCat R)).obj M)
    [ChainComplex.IsFiniteFreeResolution π] :
    Nonempty
      (DerivedCategory.Q.obj (F.extend ComplexShape.embeddingDownNat) ≅
        ModuleCat.single0Functor.obj M) := by
  let f :
      DerivedCategory.Q.obj (F.extend ComplexShape.embeddingDownNat) ⟶
        DerivedCategory.Q.obj (((ChainComplex.single₀ (ModuleCat R)).obj M).extend
          ComplexShape.embeddingDownNat) :=
    DerivedCategory.Q.map (HomologicalComplex.extendMap π ComplexShape.embeddingDownNat)
  have hf : IsIso f := by
    -- Proof comment: extending the augmentation preserves the chosen quasi-isomorphism.
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  let e :
      DerivedCategory.Q.obj (F.extend ComplexShape.embeddingDownNat) ≅
        DerivedCategory.Q.obj (((ChainComplex.single₀ (ModuleCat R)).obj M).extend
          ComplexShape.embeddingDownNat) :=
    asIso f
  -- Proof comment: normalize the extended chain single complex back to the canonical `M[0]`.
  exact ⟨e ≪≫
      (DerivedCategory.Q.mapIso
        (HomologicalComplex.extendSingleIso
          ComplexShape.embeddingDownNat M (0 : ℕ) (0 : ℤ) rfl)) ≪≫
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app M).symm⟩

/-- Helper for Lemma 15.65.4: a finite free chain resolution gives a pseudo-coherent witness for
the resolved module. -/
lemma isPseudoCoherent_of_finite_free_resolution
    {M : ModuleCat.{u} R} {F : ChainComplex (ModuleCat R) ℕ}
    (π : F ⟶ (ChainComplex.single₀ (ModuleCat R)).obj M)
    [ChainComplex.IsFiniteFreeResolution π] :
    M.IsPseudoCoherent := by
  let E : Cpx := F.extend ComplexShape.embeddingDownNat
  have hE : E.IsTermwiseFiniteFree :=
    extend_embeddingDownNat_isTermwiseFiniteFree (R := R) π
  obtain ⟨e⟩ := extend_resolution_single0_iso (R := R) π
  -- Proof comment: the extended resolution is bounded above by `0`, termwise finite free, and
  -- quasi-isomorphic to `M[0]`.
  rw [ModuleCat.IsPseudoCoherent]
  exact ⟨E, ⟨0, inferInstance⟩, hE, e.hom, by infer_instance⟩

-- Proof sketch: an infinite finite free resolution gives `(-d)`-pseudo-coherence for every `d` by
-- truncation. Conversely, recursively choose the finite free covers supplied by part `(3)` for all
-- lengths to assemble an exact infinite resolution by finite free modules.
/-- Lemma 15.65.4 (4): an `R`-module is pseudo-coherent exactly when it admits an infinite
resolution by finite free `R`-modules. -/
-- TODO: for `←`, transport an infinite finite free resolution to a bounded-above finite-free
-- representative in `D(R)`; for `→`, recursively extract finite free covers of successive
-- pseudo-coherent syzygies and package them into a chain complex.
theorem moduleCat_isPseudoCoherent_iff_exists_infiniteFiniteFreeResolution
    (M : ModuleCat.{u} R) :
    M.IsPseudoCoherent ↔
      ∃ (F : ChainComplex (ModuleCat.{u} R) ℕ)
        (π : F ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj M),
        ChainComplex.IsFiniteFreeResolution π := by
  constructor
  · intro hM
    rw [ModuleCat.IsPseudoCoherent] at hM
    rcases hM with ⟨E, ⟨b, hEb⟩, hEfree, α, hα⟩
    letI : E.IsTermwiseFiniteFree := hEfree
    letI : IsIso α := hα
    obtain ⟨β, hβ, _hQβ⟩ :=
      exists_strict_single0_map_of_pseudoCoherent_witness
        (R := R) (E := E) (M := M) b hEb α
    let F : ChainComplex (ModuleCat R) ℕ := E.restriction ComplexShape.embeddingDownNat
    let π :
        F ⟶ (ChainComplex.single₀ (ModuleCat R)).obj M :=
      HomologicalComplex.restrictionMap β ComplexShape.embeddingDownNat ≫
        (Classical.choice (restriction_single0_iso (R := R) M)).hom
    have hπ : ChainComplex.IsFiniteFreeResolution π :=
      restriction_single_quasiIso_isFiniteFreeResolution (R := R) β hβ
    -- Proof comment: after strictifying the derived comparison to `M[0]`, the negative part of
    -- the bounded-above finite free complex is exactly the desired infinite finite free
    -- resolution.
    exact ⟨F, π, hπ⟩
  · rintro ⟨F, π, hπ⟩
    letI : ChainComplex.IsFiniteFreeResolution π := hπ
    -- Proof comment: reindex the chain resolution as a bounded-above cochain complex and use its
    -- augmentation as the pseudo-coherent model of `M[0]`.
    exact isPseudoCoherent_of_finite_free_resolution (R := R) π

end
