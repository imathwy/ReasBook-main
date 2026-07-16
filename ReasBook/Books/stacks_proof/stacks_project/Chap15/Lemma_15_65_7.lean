import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_5_1
import stacks_proof.stacks_project.Chap13.Definition_13_11_3
import stacks_proof.stacks_project.Chap13.Lemma_13_27_9
import stacks_proof.stacks_project.Chap13.Remark_13_12_4
import stacks_proof.stacks_project.Chap13.Situation_13_15_1
import stacks_proof.stacks_project.Chap15.Definition_15_65_1
import stacks_proof.stacks_project.Chap15.Lemma_15_65_2
import stacks_proof.stacks_project.Chap15.Lemma_15_65_3
import stacks_proof.stacks_project.Chap15.Lemma_15_65_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DerivedCategory.TStructure
open scoped ZeroObject

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CochainComplex

section

variable {R : Type u} [Ring R]

local abbrev ModR := ModuleCat.{u} R
local abbrev Cpx := CochainComplex (ModuleCat.{u} R) ℤ
local abbrev DMod := DerivedCategory (ModuleCat.{u} R)
local abbrev H := DerivedCategory.homologyFunctor (ModuleCat.{u} R)
private abbrev Q : Cpx ⥤ DMod := DerivedCategory.Q

/-- Helper for Lemma 15.65.7: the zero cochain complex over `ModuleCat R`. -/
private abbrev zeroCpx : Cpx := 0

/- Domain-style sampling for Lemma 15.65.7:
- primary domain: recognition of `m`-pseudo-coherence for cochain complexes from cohomology
  vanishing and finiteness conditions on the top surviving cohomology objects;
- sampled owner declarations:
  `CochainComplex.IsMPseudoCoherent`,
  `homology_finite_of_isMPseudoCoherent`,
  `homology_finitePresentation_of_isMPseudoCoherent`,
  `DerivedCategory.IsLE`;
- best owner abstraction: the pseudo-coherence owner stays `K.IsMPseudoCoherent m`; the explicit
  cohomology-vanishing hypotheses below are source-facing bridge data rather than a second owner,
  and the canonical derived `t`-structure bound `((DerivedCategory.Q : Cpx ⥤ _).obj K).IsLE _`
  remains a downstream view;
- primitive vs. derived:
  primitive data are the cochain complex `K`, the homology vanishing ranges, and the finiteness
  / finite-presentation hypotheses on the surviving cohomology modules;
  derived API is the resulting `m`-pseudo-coherence conclusion, whose converse finiteness
  consequences already belong to Lemma `15.65.3`;
- source/core/bridge triage:
  `source-facing`: the three recognition statements below in textbook homology language;
  `core/canonical`: the owner predicate `K.IsMPseudoCoherent m`;
  `bridge/view`: the cohomology-vanishing input and the derived `IsLE` reformulation of that
    input, which should not replace the source-facing statements here.
-/

/-- Helper for Lemma 15.65.7: the zero cochain complex is termwise finite free. -/
private instance zero_isTermwiseFiniteFree : (zeroCpx (R := R)).IsTermwiseFiniteFree where
  out i := by
    let E0 : Cpx := zeroCpx (R := R)
    change Module.Free R ↥(E0.X i) ∧ Module.Finite R ↥(E0.X i)
    let hzero : IsZero (E0.X i) := by
      simpa using
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i).map_isZero
          (isZero_zero Cpx : IsZero (0 : Cpx))
    letI : Subsingleton ↥(E0.X i) :=
      ModuleCat.subsingleton_of_isZero hzero
    refine
      ⟨Module.Free.of_subsingleton (R := R) (N := ↥(E0.X i)), ?_⟩
    let e : ModuleCat.of R PUnit ≅ E0.X i :=
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)).isoZero ≪≫ hzero.isoZero.symm
    exact Module.Finite.equiv e.toLinearEquiv

/-- Helper for Lemma 15.65.7: if all derived homology objects vanish in degrees `≥ m`, then the
derived object is `m`-pseudo-coherent. -/
private theorem isMPseudoCoherent_of_derived_homology_isZero_ge
    {K : DMod} {m : ℤ}
    (hK : ∀ i : ℤ, m ≤ i → IsZero ((H i).obj K)) :
    K.IsMPseudoCoherent m := by
  let E0 : Cpx := zeroCpx (R := R)
  let α : Q.obj E0 ⟶ K := 0
  refine ⟨E0, ?_, inferInstance, α, ?_, ?_⟩
  · -- The zero complex is bounded on both sides at the chosen cutoff.
    refine ⟨m, m, ?_, ?_⟩
    · simpa [E0, zeroCpx] using (inferInstance : (zeroCpx (R := R)).IsStrictlyGE m)
    · simpa [E0, zeroCpx] using (inferInstance : (zeroCpx (R := R)).IsStrictlyLE m)
  · intro i hi
    -- Both source and target homology vanish, so the zero map is an isomorphism.
    let hsrc : IsZero ((H i).obj (Q.obj E0)) := by
      simpa [E0, zeroCpx] using
        (H i).map_isZero
          ((Q).map_isZero
            (HomologicalComplex.isZero_zero : IsZero (0 : Cpx)))
    let htgt : IsZero ((H i).obj K) := hK i (le_of_lt hi)
    exact hsrc.isIso htgt ((H i).map α)
  · -- The same zero-object argument gives the required epimorphism in degree `m`.
    let hsrc : IsZero ((H m).obj (Q.obj E0)) := by
      simpa [E0, zeroCpx] using
        (H m).map_isZero
          ((Q).map_isZero
            (HomologicalComplex.isZero_zero : IsZero (0 : Cpx)))
    let htgt : IsZero ((H m).obj K) := hK m le_rfl
    letI : IsIso ((H m).map α) := hsrc.isIso htgt ((H m).map α)
    infer_instance

/-- Helper for Lemma 15.65.7: finite cochain homology transfers to the corresponding derived
homology object via the canonical comparison isomorphism. -/
private theorem finite_derived_homology_of_finite_homology
    {K : Cpx} {i : ℤ}
    (hi : Module.Finite R (K.homology i)) :
    Module.Finite R ((H i).obj (Q.obj K)) := by
  let e : (H i).obj (Q.obj K) ≅ K.homology i := derived_homology_iso (R := R) K i
  -- Transport finite generation across the canonical module isomorphism.
  letI : Module.Finite R (K.homology i) := hi
  exact Module.Finite.equiv e.symm.toLinearEquiv

/-- Helper for Lemma 15.65.7: finite presentation of cochain homology transfers to the
corresponding derived homology object via the canonical comparison isomorphism. -/
private theorem finitePresentation_derived_homology_of_finitePresentation_homology
    {K : Cpx} {i : ℤ}
    (hi : Module.FinitePresentation R (K.homology i)) :
    Module.FinitePresentation R ((H i).obj (Q.obj K)) := by
  let e : (H i).obj (Q.obj K) ≅ K.homology i := derived_homology_iso (R := R) K i
  -- Transport finite presentation across the same comparison isomorphism.
  letI : Module.FinitePresentation R (K.homology i) := hi
  exact Module.FinitePresentation.of_equiv e.symm.toLinearEquiv

/-- Helper for Lemma 15.65.7: the degree-zero homology of the single cochain complex is the
original module. -/
private noncomputable abbrev single_zero_complex_homology_iso
    (M : ModR) :
    (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M).homology 0) ≅ M :=
  _root_.single_zero_complex_homology_iso (R := R) M

/-- Helper for Lemma 15.65.7: the cohomology of a degree-zero complex vanishes away from degree
`0`. -/
private theorem single_zero_complex_homology_isZero_of_ne_local
    (M : ModR) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((H i).obj (ModuleCat.single0Functor.obj M)) := by
  -- Proof comment: reuse the earlier degree-zero vanishing result for single complexes.
  simpa using _root_.single_zero_complex_homology_isZero_of_ne_local (R := R) M i hi

/-- Helper for Lemma 15.65.7: the `singleFunctorIsoCompQ` comparison is the identity on zeroth
homology. -/
private theorem homology_map_singleFunctorIsoCompQ_app_zero_eq_id
    (M : ModR) :
    (H 0).map (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app M).hom) =
      𝟙 _ := by
  -- Proof comment: the comparison `singleFunctorIsoCompQ` is definitionally the identity in this
  -- degree-zero case.
  change
    (H 0).map
        (𝟙 (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M))) =
      𝟙 _
  simp

/-- Helper for Lemma 15.65.7: if `f ≫ e.hom` is epi and `e` is an isomorphism, then `f` is epi. -/
private theorem epi_of_epi_comp_iso
    {X Y Z : ModR} (f : X ⟶ Y) (e : Y ≅ Z) [Epi (f ≫ e.hom)] :
    Epi f := by
  -- Proof comment: postcompose two parallel arrows with `e.inv` and cancel the resulting
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

/-- Helper for Lemma 15.65.7: the canonical kernel inclusion followed by the quotient map is
zero. -/
private lemma kernel_subtype_comp_eq_zero
    {F M : ModR} (f : F ⟶ M) :
    f.hom.comp (LinearMap.ker f.hom).subtype = 0 := by
  -- Proof comment: this is the standard kernel inclusion identity from the earlier module API.
  simpa using _root_.kernel_subtype_comp_eq_zero (R := R) f

/-- Helper for Lemma 15.65.7: a surjective module map fits into the standard kernel short exact
sequence. -/
private theorem kernel_cover_shortExact
    {F M : ModR} (f : F ⟶ M) (hf : Function.Surjective f.hom) :
    (ShortComplex.moduleCatMk (LinearMap.ker f.hom).subtype f.hom
      (kernel_subtype_comp_eq_zero f)).ShortExact := by
  -- Proof comment: reuse the standard short exact sequence attached to a surjective cover.
  simpa [kernel_subtype_comp_eq_zero] using _root_.kernel_cover_shortExact (R := R) f hf

/-- Helper for Lemma 15.65.7: the single complex on a finite free module is termwise finite
free. -/
private lemma single_zero_complex_isTermwiseFiniteFree
    (F : ModR) [Module.Free R F] [Module.Finite R F] :
    ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj F).IsTermwiseFiniteFree := by
  -- Proof comment: the earlier module-side single-complex construction already provides this.
  simpa using _root_.single_zero_complex_isTermwiseFiniteFree (R := R) F

/-- Helper for Lemma 15.65.7: after the canonical `H⁰(single₀ -)` identifications, the homology
map induced by a cover is the original module map. -/
private theorem single_zero_cover_homology_map_eq
    {F M : ModR} (f : F ⟶ M) :
    let α :
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj F) ⟶
          ModuleCat.single0Functor.obj M :=
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app F).hom ≫
        ModuleCat.single0Functor.map f
    (H 0).map α ≫
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) (0 : ℤ)).app M).hom =
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) (0 : ℤ)).app F).hom ≫
        f := by
  -- Proof comment: this is exactly the earlier module-side comparison theorem.
  simpa using _root_.single_zero_cover_homology_map_eq (R := R) f

/-- Helper for Lemma 15.65.7: a surjective finite free cover induces an epimorphism on degree-zero
homology of the corresponding single-complex map. -/
private theorem single_zero_cover_homology_epi_of_surjective
    {F M : ModR} (f : F ⟶ M) (hf : Function.Surjective f.hom) :
    let α :
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj F) ⟶
          ModuleCat.single0Functor.obj M :=
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app F).hom ≫
        ModuleCat.single0Functor.map f
    Epi ((H 0).map α) := by
  -- Proof comment: reuse the established degree-zero homology epimorphism criterion.
  simpa using _root_.single_zero_cover_homology_epi_of_surjective (R := R) f hf

/-- Helper for Lemma 15.65.7: an `m`-pseudo-coherent witness also works for every larger bound. -/
private lemma isMPseudoCoherent_mono
    {K : DMod} {m n : ℤ} (hmn : m ≤ n)
    (hK : K.IsMPseudoCoherent m) :
    K.IsMPseudoCoherent n := by
  -- Proof comment: enlarge the bound using the earlier monotonicity lemma.
  simpa using _root_.isMPseudoCoherent_mono (R := R) hmn hK

/-- Helper for Lemma 15.65.7: a finite free module is `m`-pseudo-coherent for every `m`. -/
private lemma finite_free_module_isMPseudoCoherent
    (F : ModR) (m : ℤ) [Module.Free R F] [Module.Finite R F] :
    F.IsMPseudoCoherent m := by
  -- Proof comment: this is the earlier finite-free module criterion.
  simpa using _root_.finite_free_module_isMPseudoCoherent (R := R) F m

/-- Helper for Lemma 15.65.7: the kernel of a surjective finite free cover of a
`(-(d + 1))`-pseudo-coherent module is `(-d)`-pseudo-coherent. -/
private lemma kernel_of_surjective_finite_free_cover_isMPseudoCoherent
    {F M : ModR} (f : F ⟶ M) (hf : Function.Surjective f.hom) (d : ℕ)
    [Module.Free R F] [Module.Finite R F]
    (hM : M.IsMPseudoCoherent (-(d + 1 : ℤ))) :
    (ModuleCat.of R (LinearMap.ker f.hom)).IsMPseudoCoherent (-(d : ℤ)) := by
  -- Proof comment: reuse the kernel descent lemma from the earlier module-side file.
  simpa using _root_.kernel_of_surjective_finite_free_cover_isMPseudoCoherent (R := R) f hf d hM

/-- Helper for Lemma 15.65.7: a module that is `(m - n)`-pseudo-coherent gives an `m`-pseudo-
coherent single derived object supported in degree `n`. -/
private theorem singleFunctor_isMPseudoCoherent_of_module
    (M : ModR) (n m : ℤ)
    (hM : M.IsMPseudoCoherent (m - n)) :
    ((DerivedCategory.singleFunctor (ModuleCat R) n).obj M).IsMPseudoCoherent m := by
  let e :
      (((DerivedCategory.singleFunctor (ModuleCat R) n).obj M)⟦n⟧) ≅
        ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj M) :=
    ((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso n 0 n (by simp)).app M
  have hShift :
      (((DerivedCategory.singleFunctor (ModuleCat R) n).obj M)⟦n⟧).IsMPseudoCoherent (m - n) := by
    -- Proof comment: after shifting by `n`, the degree-`n` single object becomes the degree-zero
    -- single object on `M`.
    rw [ModuleCat.IsMPseudoCoherent] at hM
    exact isMPseudoCoherent_of_iso e.symm (m - n) hM
  -- Proof comment: shift the pseudo-coherence bound back to the original unshifted object.
  exact
    (isMPseudoCoherent_shift_iff
      ((DerivedCategory.singleFunctor (ModuleCat R) n).obj M) n m).1 hShift

/-- Helper for Lemma 15.65.7: theorem-local fallback for the prerequisite that `0`-pseudo-
coherent modules are exactly the finite modules. -/
private theorem moduleCat_isZeroPseudoCoherent_iff_finite_local
    (M : ModR) :
    M.IsMPseudoCoherent 0 ↔ Module.Finite R M := by
  -- Proof comment: this is the earlier characterization of `0`-pseudo-coherent modules.
  simpa using _root_.moduleCat_isZeroPseudoCoherent_iff_finite (R := R) M

/-- Helper for Lemma 15.65.7: theorem-local fallback for the prerequisite that `(-1)`-pseudo-
coherent modules are exactly the finitely presented modules. -/
private theorem moduleCat_isMinusOnePseudoCoherent_iff_finitePresentation_local
    (M : ModR) :
    M.IsMPseudoCoherent (-1) ↔ Module.FinitePresentation R M := by
  -- Proof comment: this is the earlier characterization of `(-1)`-pseudo-coherent modules.
  simpa using _root_.moduleCat_isMinusOnePseudoCoherent_iff_finitePresentation (R := R) M

/-- Helper for Lemma 15.65.7: a derived object bounded above by `m` is `m`-pseudo-coherent once
its top degree-`m` homology is finite. -/
private theorem isMPseudoCoherent_of_isLE_and_top_homology_finite
    {K : DMod} {m : ℤ}
    (hLE : K.IsLE m)
    (hm : Module.Finite R ((H m).obj K)) :
    K.IsMPseudoCoherent m := by
  let T := truncLE_step_homologyTriangle K (m - 1)
  have hT : T ∈ distTriang DMod := truncLE_step_homology_triangle K (m - 1)
  have hLeft :
      T.obj₁.IsMPseudoCoherent m := by
    -- Proof comment: the lower truncation piece has no homology in degrees `≥ m`.
    refine isMPseudoCoherent_of_derived_homology_isZero_ge ?_
    intro i hi
    have hLE₁ : T.obj₁.IsLE (m - 1) := by
      dsimp [T, truncLE_step_homologyTriangle]
      infer_instance
    exact DerivedCategory.isZero_of_isLE T.obj₁ (m - 1) i (by omega)
  have hRight :
      T.obj₃.IsMPseudoCoherent m := by
    -- Proof comment: the third vertex is the top homology module placed in degree `m`.
    have hm0 : ((H m).obj K).IsMPseudoCoherent (m - m) := by
      simpa using
        ((moduleCat_isZeroPseudoCoherent_iff_finite_local ((H m).obj K)).2 hm)
    simpa [T, truncLE_step_homologyTriangle] using
      singleFunctor_isMPseudoCoherent_of_module
        ((H m).obj K) m m
        hm0
  have hMid : T.obj₂.IsMPseudoCoherent m :=
    isMPseudoCoherent_obj₂_of_distinguishedTriangle T hT hLeft hRight
  letI : IsIso ((t.truncLTι (m + 1)).app K) :=
    (t.isLE_iff_isIso_truncLTι_app m (m + 1) (by omega) K).1 hLE
  have hMid' : ((t.truncLT (m + 1)).obj K).IsMPseudoCoherent m := by
    -- Proof comment: boundedness identifies the middle truncation with the original object.
    simpa [T, truncLE_step_homologyTriangle, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using hMid
  exact isMPseudoCoherent_of_iso (asIso ((t.truncLTι (m + 1)).app K)) m hMid'

/-- Helper for Lemma 15.65.7: if `K` is bounded above by `m + 1` and its top homology is finitely
presented, then the upper truncation `τ_{\ge m + 1} K` is `m`-pseudo-coherent. -/
private theorem truncGE_isMPseudoCoherent_of_isLE_and_top_homology_finitePresentation
    {K : DMod} {m : ℤ}
    (hLE : K.IsLE (m + 1))
    (hm_succ : Module.FinitePresentation R ((H (m + 1)).obj K)) :
    ((t.truncGE (m + 1)).obj K).IsMPseudoCoherent m := by
  let T := truncGE_step_homologyTriangle K (m + 1)
  have hT : T ∈ distTriang DMod := truncGE_step_homology_triangle K (m + 1)
  have hHead :
      T.obj₁.IsMPseudoCoherent m := by
    -- Proof comment: the first vertex is the degree-`m + 1` homology term placed in degree
    -- `m + 1`, and finite presentation is exactly the `(-1)`-pseudo-coherent criterion there.
    have hm_succ' :
        ((H (m + 1)).obj K).IsMPseudoCoherent (m - (m + 1)) := by
      simpa using
        ((moduleCat_isMinusOnePseudoCoherent_iff_finitePresentation_local ((H (m + 1)).obj K)).2
          hm_succ)
    simpa [T, truncGE_step_homologyTriangle] using
      singleFunctor_isMPseudoCoherent_of_module
        ((H (m + 1)).obj K) (m + 1) m
        hm_succ'
  have hTail :
      T.obj₃.IsMPseudoCoherent m := by
    -- Proof comment: the tail truncation is simultaneously in `D^{≥ m + 2}` and `D^{≤ m + 1}`,
    -- hence all of its homology objects vanish.
    refine isMPseudoCoherent_of_derived_homology_isZero_ge ?_
    intro i hi
    have hGEtail : T.obj₃.IsGE (m + 2) := by
      simpa [T, truncGE_step_homologyTriangle, add_assoc] using
        (inferInstance : ((t.truncGE (m + 1 + 1)).obj K).IsGE (m + 1 + 1))
    have hLEtail : T.obj₃.IsLE (m + 1) := by
      dsimp [T, truncGE_step_homologyTriangle]
      infer_instance
    by_cases hlt : i < m + 2
    · exact DerivedCategory.isZero_of_isGE T.obj₃ (m + 2) i hlt
    · have hgt : m + 1 < i := by
        omega
      exact DerivedCategory.isZero_of_isLE T.obj₃ (m + 1) i hgt
  have hMid :
      T.obj₂.IsMPseudoCoherent m :=
    isMPseudoCoherent_obj₂_of_distinguishedTriangle T hT hHead hTail
  -- Proof comment: `T.obj₂` is exactly the upper truncation `τ_{\ge m + 1} K`.
  simpa [T, truncGE_step_homologyTriangle] using hMid

-- Proof sketch: transport the homology vanishing hypothesis to the derived category and apply the
-- zero-complex witness.
/-- Lemma 15.65.7 (1): if a cochain complex `K^•` of `R`-modules has vanishing cohomology
in every degree `i ≥ m`, then `K^•` is `m`-pseudo-coherent. -/
@[stacks 064W]
theorem isMPseudoCoherent_of_homology_isZero_ge
    {K : Cpx} {m : ℤ}
    (hvanish : ∀ i : ℤ, m ≤ i → IsZero (K.homology i)) :
    K.IsMPseudoCoherent m := by
  -- The canonical derived homology objects vanish in the same range by `derived_homology_iso`.
  refine isMPseudoCoherent_of_derived_homology_isZero_ge ?_
  intro i hi
  let e : (H i).obj (Q.obj K) ≅ K.homology i := derived_homology_iso (R := R) K i
  exact e.isZero_iff.2 (hvanish i hi)

-- Proof sketch: rewrite the cohomology vanishing as an `IsLE m` bound on the derived object and
-- apply the one-step truncation lemma with the finite top homology.
/-- Lemma 15.65.7 (2): if a cochain complex `K^•` of `R`-modules has vanishing cohomology
in every degree `i > m` and `H^m(K^•)` is finite, then `K^•` is `m`-pseudo-coherent. -/
@[stacks 064W]
theorem isMPseudoCoherent_of_homology_isZero_gt_and_finite
    {K : Cpx} {m : ℤ}
    (hvanish : ∀ i : ℤ, m < i → IsZero (K.homology i))
    (hm : Module.Finite R (K.homology m)) :
    K.IsMPseudoCoherent m := by
  have hLE : (Q.obj K).IsLE m := by
    -- Vanishing above `m` is exactly the `t`-structure boundedness condition.
    rw [DerivedCategory.isLE_iff]
    intro i hi
    let e : (H i).obj (Q.obj K) ≅ K.homology i := derived_homology_iso (R := R) K i
    exact e.isZero_iff.2 (hvanish i hi)
  have hm' : Module.Finite R ((H m).obj (Q.obj K)) :=
    finite_derived_homology_of_finite_homology (R := R) hm
  -- Apply the bounded-above one-step truncation argument in the derived category.
  exact isMPseudoCoherent_of_isLE_and_top_homology_finite hLE hm'

-- Proof sketch: prove the upper truncation is `m`-pseudo-coherent from the finitely presented
-- `H^(m + 1)`, prove the lower truncation is `m`-pseudo-coherent from the finite `H^m`, and glue
-- them with the standard truncation triangle.
/-- Lemma 15.65.7 (3): if a cochain complex `K^•` of `R`-modules has vanishing cohomology
in every degree `i > m + 1`, `H^(m + 1)(K^•)` is finitely presented, and `H^m(K^•)` is finite,
then `K^•` is `m`-pseudo-coherent. -/
@[stacks 064W]
theorem isMPseudoCoherent_of_homology_isZero_gt_add_one_and_finite
    {K : Cpx} {m : ℤ}
    (hvanish : ∀ i : ℤ, m + 1 < i → IsZero (K.homology i))
    (hm_succ : Module.FinitePresentation R (K.homology (m + 1)))
    (hm : Module.Finite R (K.homology m)) :
    K.IsMPseudoCoherent m := by
  have hLE : (Q.obj K).IsLE (m + 1) := by
    -- Proof comment: vanishing above `m + 1` is the same as the `D^{≤ m + 1}` boundedness
    -- condition.
    rw [DerivedCategory.isLE_iff]
    intro i hi
    let e : (H i).obj (Q.obj K) ≅ K.homology i := derived_homology_iso (R := R) K i
    exact e.isZero_iff.2 (hvanish i hi)
  have hUpper :
      ((t.truncGE (m + 1)).obj (Q.obj K)).IsMPseudoCoherent m := by
    have hm_succ' :
        Module.FinitePresentation R ((H (m + 1)).obj (Q.obj K)) :=
      finitePresentation_derived_homology_of_finitePresentation_homology (R := R) hm_succ
    exact truncGE_isMPseudoCoherent_of_isLE_and_top_homology_finitePresentation hLE hm_succ'
  have hLower :
      ((t.truncLT (m + 1)).obj (Q.obj K)).IsMPseudoCoherent m := by
    have hLElower : ((t.truncLT (m + 1)).obj (Q.obj K)).IsLE m := by
      simpa using
        (inferInstance : ((t.truncLT (m + 1)).obj (Q.obj K)).IsLE ((m + 1) - 1))
    have hIso : IsIso ((H m).map ((t.truncLTι (m + 1)).app (Q.obj K))) := by
      simpa using
        (homology_map_truncLTι_isIso_of_lt (𝒜 := ModuleCat R) (Q.obj K) m (m + 1) (by omega))
    let eH :
        (H m).obj ((t.truncLT (m + 1)).obj (Q.obj K)) ≅ (H m).obj (Q.obj K) :=
      @asIso _ _ _ _ ((H m).map ((t.truncLTι (m + 1)).app (Q.obj K))) hIso
    have hm_lower :
        Module.Finite R ((H m).obj ((t.truncLT (m + 1)).obj (Q.obj K))) := by
      have hm' : Module.Finite R ((H m).obj (Q.obj K)) :=
        finite_derived_homology_of_finite_homology (R := R) hm
      letI : Module.Finite R ((H m).obj (Q.obj K)) := hm'
      exact
        Module.Finite.of_surjective
          eH.symm.toLinearEquiv.toLinearMap
          eH.symm.toLinearEquiv.surjective
    exact isMPseudoCoherent_of_isLE_and_top_homology_finite hLElower hm_lower
  let T : Triangle DMod := (t.triangleLEGE m (m + 1) rfl).obj (Q.obj K)
  have hT : T ∈ distTriang DMod := by
    simpa [T] using truncation_triangle_distinguished (K := Q.obj K) (a := m)
  have hMid : T.obj₂.IsMPseudoCoherent m :=
    isMPseudoCoherent_obj₂_of_distinguishedTriangle T hT
      (by simpa [T] using hLower)
      (by simpa [T] using hUpper)
  -- Proof comment: the canonical truncation triangle glues the lower and upper pieces back to
  -- the original complex.
  simpa [T] using hMid

end

end CochainComplex
