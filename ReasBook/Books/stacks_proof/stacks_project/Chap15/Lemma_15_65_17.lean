import Mathlib
import StacksProject_2024.Chap10.Lemma_10_71_1
import StacksProject_2024.Chap13.Definition_13_11_3
import StacksProject_2024.Chap13.Lemma_13_27_9
import StacksProject_2024.Chap13.Lemma_13_28_2
import StacksProject_2024.Chap13.Lemma_13_35_7
import StacksProject_2024.Chap13.Remark_13_12_4
import StacksProject_2024.Chap13.Situation_13_15_1
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Lemma_15_65_2
import StacksProject_2024.Chap15.Lemma_15_65_3
import StacksProject_2024.Chap15.Lemma_15_65_6

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DerivedCategory.TStructure
open scoped ZeroObject

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R] [IsNoetherianRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "DModMinus" => boundedAboveDerivedCategory (ModuleCat R)
local notation "BoundedAbove" => (t.minus : ObjectProperty DMod)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => (ModuleCat.single0Functor : ModuleCat R ⥤ DMod)
local notation "singleCpx₀" => (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ))

/- Domain-style sampling for Lemma 15.65.17:
- primary domain: pseudo-coherence in the derived category of modules over a Noetherian ring and
  its degree-zero module specialization;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `boundedAboveDerivedCategory`,
  `ModuleCat.IsPseudoCoherent`;
- best owner abstraction: the source-facing statements in parts `(1)` and `(2)` stay on the
  chapter owners `K.IsMPseudoCoherent` and `K.IsPseudoCoherent`, while the module theorem in part
  `(3)` should use the ordinary unbundled module bridge surface rather than a parallel bundled
  `ModuleCat`-only theorem;
- primitive vs. derived:
  primitive data are the derived owner predicates and the bounded-above owner subcategory from
  Lemma `15.65.10`;
  derived API is the bounded-above finite-homology characterization below, together with the
  degree-zero module bridge in part `(3)`;
- source/core/bridge triage:
  `source-facing`: the three numbered criteria of Lemma `15.65.17`;
  `core/canonical`: `K.IsMPseudoCoherent`, `K.IsPseudoCoherent`, and
    `boundedAboveDerivedCategory (ModuleCat R)`;
  `bridge/view`: the ordinary module surface `(ModuleCat.of R M).IsPseudoCoherent`.
-/

/-- Helper for Lemma 15.65.17: a zero `R`-module is finite free. -/
private lemma moduleCat_finite_free_of_isZero
    (M : ModuleCat R) (hM : IsZero M) :
    Module.Free R M ∧ Module.Finite R M := by
  -- Proof comment: a zero module is free by subsingleton, and finite because it is equivalent to
  -- the one-point free module.
  let _ : Subsingleton M := ModuleCat.subsingleton_of_isZero hM
  refine ⟨Module.Free.of_subsingleton (R := R) (N := M), ?_⟩
  let e : ModuleCat.of R PUnit ≅ M :=
    (ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)).isoZero ≪≫ hM.isoZero.symm
  exact Module.Finite.equiv e.toLinearEquiv

/-- Helper for Lemma 15.65.17: the augmentation map of a projective-resolution cochain model is
an isomorphism in the derived category. -/
private theorem projectiveResolution_cochain_map_isIso
    {N : ModuleCat R} (P : ProjectiveResolution N) :
    IsIso (DerivedCategory.Q.map P.π') := by
  -- Proof comment: projective-resolution augmentations are quasi-isomorphisms, so they become
  -- isomorphisms after applying `Q`.
  infer_instance

/-- Helper for Lemma 15.65.17: the cochain complex attached to a projective resolution of `N`
represents the degree-zero single object `N[0]`. -/
private noncomputable def projectiveResolution_cochain_single0_iso
    {N : ModuleCat R} (P : ProjectiveResolution N) :
    DerivedCategory.Q.obj P.cochainComplex ≅ (single₀).obj N :=
  let _ : IsIso (DerivedCategory.Q.map P.π') :=
    projectiveResolution_cochain_map_isIso (R := R) P
  asIso (DerivedCategory.Q.map P.π') ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app N).symm

/-- Helper for Lemma 15.65.17: the cochain complex attached to a finite free resolution is
termwise finite free. -/
private lemma projectiveResolution_cochain_isTermwiseFiniteFree
    {N : ModuleCat R} {F : ChainComplex (ModuleCat R) ℕ}
    (π : F ⟶ CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) N)
    [hπ : ChainComplex.IsFiniteFreeResolution (R := R) (M := N) π] :
    (ChainComplex.IsFreeResolution.toProjectiveResolution (R := R) (M := N)
      (π := π)).cochainComplex.IsTermwiseFiniteFree := by
  let P := ChainComplex.IsFreeResolution.toProjectiveResolution (R := R) (M := N) (π := π)
  refine ⟨fun i ↦ ?_⟩
  by_cases hi : i ≤ 0
  · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat hi
    let e : P.cochainComplex.X (-k) ≅ P.complex.X k :=
      P.cochainComplexXIso (-k) k rfl
    have hfree : Module.Free R (P.complex.X k) := by
      simpa [P] using ChainComplex.IsFreeResolution.free (R := R) (M := N) π k
    have hfinite : Module.Finite R (P.complex.X k) := by
      simpa [P] using ChainComplex.IsFiniteFreeResolution.finite (R := R) (M := N) π k
    let _ : Module.Free R (P.complex.X k) := hfree
    let _ : Module.Finite R (P.complex.X k) := hfinite
    exact ⟨Module.Free.of_equiv e.symm.toLinearEquiv, Module.Finite.equiv e.symm.toLinearEquiv⟩
  · have hi' : 0 < i := by
      omega
    have hzero : IsZero (P.cochainComplex.X i) := P.cochainComplex.isZero_of_isStrictlyLE 0 i hi'
    exact moduleCat_finite_free_of_isZero (R := R) (P.cochainComplex.X i) hzero

/-- Helper for Lemma 15.65.17: over a Noetherian ring, a finite module is pseudo-coherent. -/
private lemma moduleCat_isPseudoCoherent_of_finite
    (N : ModuleCat R) [Module.Finite R N] :
    N.IsPseudoCoherent := by
  -- Proof comment: choose a finite free resolution of `N`, pass to its cochain model, and use
  -- the canonical derived isomorphism from that model to `N[0]`.
  rcases module_exists_finite_free_resolution (R := R) (M := N) with ⟨F, π, hπ⟩
  let P := ChainComplex.IsFreeResolution.toProjectiveResolution (R := R) (M := N) (π := π)
  rw [ModuleCat.IsPseudoCoherent]
  refine ⟨P.cochainComplex, ?_, ?_, ?_⟩
  · -- Proof comment: the cochain model of a projective resolution is supported in degrees `≤ 0`.
    exact ⟨0, inferInstance⟩
  · exact projectiveResolution_cochain_isTermwiseFiniteFree (R := R) (π := π)
  · refine ⟨(projectiveResolution_cochain_single0_iso (R := R) P).hom, ?_⟩
    infer_instance

/-- Helper for Lemma 15.65.17: a finite module is `n`-pseudo-coherent for every nonpositive
bound `n`. -/
private lemma moduleCat_isMPseudoCoherent_of_nonpos_of_finite
    (N : ModuleCat R) [Module.Finite R N] (n : ℤ) (hn : n ≤ 0) :
    N.IsMPseudoCoherent n := by
  -- Route correction: the finite-resolution truncation route is unnecessary here. Over a
  -- Noetherian ring, finite modules are already pseudo-coherent, and pseudo-coherence gives every
  -- fixed `m`-pseudo-coherence bound.
  have hN : N.IsPseudoCoherent :=
    moduleCat_isPseudoCoherent_of_finite (R := R) N
  rw [ModuleCat.IsPseudoCoherent, isPseudoCoherent_iff_forall_isMPseudoCoherent] at hN
  exact hN n

/-- Helper for Lemma 15.65.17: termwise finite free cochain complexes have finite homology over a
Noetherian ring. -/
private lemma homology_finite_of_termwiseFiniteFree
    {E : CochainComplex (ModuleCat R) ℤ} [E.IsTermwiseFiniteFree] (i : ℤ) :
    Module.Finite R (E.homology i) := by
  have hcycles : Module.Finite R (E.cycles i) := by
    -- Proof comment: cycles form a submodule of the finite degree-`i` term.
    exact Module.Finite.of_injective
      (E.iCycles i).hom
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
  let _ : Module.Finite R (E.cycles i) := hcycles
  -- Proof comment: homology is the quotient of cycles by the boundary submodule.
  exact Module.Finite.of_surjective
    (E.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

/-- Helper for Lemma 15.65.17: the zero cochain complex over `ModuleCat R`. -/
private abbrev zeroCpx : CochainComplex (ModuleCat R) ℤ := 0

/-- Helper for Lemma 15.65.17: the zero cochain complex is termwise finite free. -/
private instance zero_isTermwiseFiniteFree : (zeroCpx (R := R)).IsTermwiseFiniteFree where
  out i := by
    -- Proof comment: every term of the zero complex is a zero module, so the zero-module bridge
    -- above gives the required finite free structure.
    let E0 : CochainComplex (ModuleCat R) ℤ := zeroCpx (R := R)
    let hzero : IsZero (E0.X i) := by
      simpa [zeroCpx] using
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i).map_isZero
          (isZero_zero _)
    exact moduleCat_finite_free_of_isZero (R := R) (E0.X i) hzero

/-- Helper for Lemma 15.65.17: module-level `m`-pseudo-coherence transports across module
isomorphisms. -/
private theorem moduleCat_isMPseudoCoherent_of_iso
    {M N : ModuleCat R} (e : M ≅ N) (a : ℤ)
    (hM : M.IsMPseudoCoherent a) :
    N.IsMPseudoCoherent a := by
  -- Proof comment: move the module isomorphism through the degree-zero embedding into `D(R)`.
  rw [ModuleCat.IsMPseudoCoherent] at hM ⊢
  exact isMPseudoCoherent_of_iso ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).mapIso e) a hM

/-- Helper for Lemma 15.65.17: if all homology in degrees `≥ m` vanishes, then the derived object
is `m`-pseudo-coherent. -/
private theorem isMPseudoCoherent_of_homology_vanishes_ge
    {K : DMod} {m : ℤ}
    (hK : ∀ i : ℤ, m ≤ i → IsZero ((H i).obj K)) :
    K.IsMPseudoCoherent m := by
  let E0 : CochainComplex (ModuleCat R) ℤ := zeroCpx (R := R)
  let α : DerivedCategory.Q.obj E0 ⟶ K := 0
  refine ⟨E0, ?_, inferInstance, α, ?_, ?_⟩
  · -- Proof comment: the zero complex is bounded on both sides by any chosen cutoff.
    exact ⟨m, m, inferInstance, inferInstance⟩
  · intro i hi
    -- Proof comment: both source and target homology vanish in degree `i`, so the zero map is an
    -- isomorphism there.
    let hsrc : IsZero ((H i).obj (DerivedCategory.Q.obj E0)) := by
      simpa [zeroCpx] using
        (H i).map_isZero
          ((DerivedCategory.Q).map_isZero (isZero_zero _))
    let htgt : IsZero ((H i).obj K) := hK i (le_of_lt hi)
    exact hsrc.isIso htgt ((H i).map α)
  · -- Proof comment: the same zero-object argument makes the degree-`m` map an epimorphism.
    let hsrc : IsZero ((H m).obj (DerivedCategory.Q.obj E0)) := by
      simpa [zeroCpx] using
        (H m).map_isZero
          ((DerivedCategory.Q).map_isZero (isZero_zero _))
    let htgt : IsZero ((H m).obj K) := hK m le_rfl
    letI : IsIso ((H m).map α) := hsrc.isIso htgt ((H m).map α)
    infer_instance

/-- Helper for Lemma 15.65.17: a degree-zero module object is `n`-pseudo-coherent for every
positive integer bound `n`. -/
private lemma moduleCat_isMPseudoCoherent_of_positive
    (N : ModuleCat R) (n : ℤ) (hn : 0 < n) :
    N.IsMPseudoCoherent n := by
  -- Proof comment: the degree-zero derived object has vanishing homology in every degree `≥ n`.
  refine isMPseudoCoherent_of_homology_vanishes_ge ?_
  intro i hi
  have hi0 : i ≠ 0 := by
    omega
  exact single_zero_complex_homology_isZero_of_ne (𝒜 := ModuleCat R) N i hi0

/-- Helper for Lemma 15.65.17: upper truncation preserves homology below the cutoff. -/
private theorem isIso_homologyMap_truncLTι_local
    (K : DMod) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    IsIso ((H n₀).map ((t.truncLTι n₁).app K)) := by
  -- Proof comment: the successor-step truncation comparison is the Chapter 13 public API.
  simpa using isIso_homologyMap_truncLTι (A := ModuleCat R) K n₀ n₁ h

/-- Helper for Lemma 15.65.17: upper truncation preserves homology below the cutoff. -/
private theorem homology_map_truncLTι_isIso_of_lt_local
    (K : DMod) (i c : ℤ) (hi : i < c) :
    IsIso ((H i).map ((t.truncLTι c).app K)) := by
  -- Proof comment: compare the desired truncation map with the adjacent successor truncation,
  -- where the Chapter 13 one-step isomorphism is already available.
  let f : (t.truncLT c).obj K ⟶ K := (t.truncLTι c).app K
  let Y : DMod := (t.truncLT c).obj K
  letI : IsIso ((H i).map ((t.truncLTι (i + 1)).app K)) :=
    isIso_homologyMap_truncLTι_local (R := R) K i (i + 1) rfl
  letI : IsIso ((H i).map ((t.truncLTι (i + 1)).app Y)) :=
    isIso_homologyMap_truncLTι_local (R := R) Y i (i + 1) rfl
  let eK : (H i).obj K ≅ (H i).obj ((t.truncLT (i + 1)).obj K) :=
    (asIso ((H i).map ((t.truncLTι (i + 1)).app K))).symm
  let eY : (H i).obj Y ≅ (H i).obj ((t.truncLT (i + 1)).obj Y) :=
    (asIso ((H i).map ((t.truncLTι (i + 1)).app Y))).symm
  have hnat :
      (H i).map ((t.truncLT (i + 1)).map f) ≫ (H i).map ((t.truncLTι (i + 1)).app K) =
        (H i).map ((t.truncLTι (i + 1)).app Y) ≫ (H i).map f := by
    simpa [Functor.map_comp, f, Y] using
      congrArg ((H i).map) (NatTrans.naturality (t.truncLTι (i + 1)) f)
  have hYinv :
      eY.hom ≫ (H i).map ((t.truncLTι (i + 1)).app Y) = 𝟙 _ := by
    simp [eY]
  have hKinv :
      eK.hom ≫ (H i).map ((t.truncLTι (i + 1)).app K) = 𝟙 _ := by
    simp [eK]
  have hf :
      eY.hom ≫ (H i).map ((t.truncLT (i + 1)).map f) =
        (H i).map f ≫ eK.hom := by
    apply (cancel_mono ((H i).map ((t.truncLTι (i + 1)).app K))).1
    have h₁ :
        eY.hom ≫ (H i).map ((t.truncLT (i + 1)).map f) ≫
            (H i).map ((t.truncLTι (i + 1)).app K) =
          eY.hom ≫ (H i).map ((t.truncLTι (i + 1)).app Y) ≫ (H i).map f := by
      simpa [Category.assoc] using congrArg (fun m ↦ eY.hom ≫ m) hnat
    have h₂ :
        eY.hom ≫ (H i).map ((t.truncLTι (i + 1)).app Y) ≫ (H i).map f =
          (H i).map f := by
      simpa [Category.assoc] using congrArg (fun m ↦ m ≫ (H i).map f) hYinv
    have h₃ :
        (H i).map f =
          (H i).map f ≫ eK.hom ≫ (H i).map ((t.truncLTι (i + 1)).app K) := by
      symm
      simpa [Category.assoc] using congrArg (fun m ↦ (H i).map f ≫ m) hKinv
    simpa [Category.assoc] using h₁.trans (h₂.trans h₃)
  have hmiddle : IsIso ((H i).map ((t.truncLT (i + 1)).map f)) := by
    haveI : IsIso ((t.truncLT (i + 1)).map f) :=
      t.isIso_truncLT_map_truncLTι_app (i + 1) c (by omega) K
    exact Functor.map_isIso (H i) ((t.truncLT (i + 1)).map f)
  have hcomp : IsIso ((H i).map f ≫ eK.hom) := by
    rw [← hf]
    letI : IsIso ((H i).map ((t.truncLT (i + 1)).map f)) := hmiddle
    infer_instance
  letI : IsIso ((H i).map f ≫ eK.hom) := hcomp
  exact IsIso.of_isIso_comp_right ((H i).map f) eK.hom

/-- Helper for Lemma 15.65.17: a module that is `(m - n)`-pseudo-coherent yields an
`m`-pseudo-coherent single object in degree `n`. -/
private theorem singleFunctor_isMPseudoCoherent_of_module
    (M : ModuleCat R) (n m : ℤ)
    (hM : M.IsMPseudoCoherent (m - n)) :
    ((DerivedCategory.singleFunctor (ModuleCat R) n).obj M).IsMPseudoCoherent m := by
  let e :
      (((DerivedCategory.singleFunctor (ModuleCat R) n).obj M)⟦n⟧) ≅
        ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj M) :=
    singleFunctor_shifted_single0_iso_canonical (𝒜 := ModuleCat R) M n
  have hShift :
      (((DerivedCategory.singleFunctor (ModuleCat R) n).obj M)⟦n⟧).IsMPseudoCoherent (m - n) := by
    -- Proof comment: after shifting by `n`, the degree-`n` single object becomes the degree-zero
    -- single object on the same module.
    rw [ModuleCat.IsMPseudoCoherent] at hM
    exact isMPseudoCoherent_of_iso e.symm (m - n) hM
  -- Proof comment: now shift the bound back from degree `0` to degree `n`.
  exact
    (isMPseudoCoherent_shift_iff
      ((DerivedCategory.singleFunctor (ModuleCat R) n).obj M) n m).1 hShift

/-- Helper for Lemma 15.65.17: if `K` is bounded above by `m + k`, then the degreewise module
hypotheses up to that bound imply that `K` is `m`-pseudo-coherent. -/
private theorem isMPseudoCoherent_of_isLE_and_homology_bounds
    (m : ℤ) :
    ∀ (k : ℕ) (K : DMod), K.IsLE (m + k) →
      (∀ i : ℤ, i ≤ m + k → ((H i).obj K).IsMPseudoCoherent (m - i)) →
      K.IsMPseudoCoherent m := by
  intro k
  induction k with
  | zero =>
      intro K hLE hH
      have hLE0 : K.IsLE m := by
        simpa using hLE
      let T := truncLE_step_homologyTriangle K (m - 1)
      have hT : T ∈ distTriang DMod := truncLE_step_homology_triangle K (m - 1)
      have hLeft :
          T.obj₁.IsMPseudoCoherent m := by
        -- Proof comment: the lower truncation has no homology in degrees `≥ m`.
        refine isMPseudoCoherent_of_homology_vanishes_ge ?_
        intro i hi
        have hLE₁ : T.obj₁.IsLE (m - 1) := by
          dsimp [T, truncLE_step_homologyTriangle]
          infer_instance
        exact DerivedCategory.isZero_of_isLE T.obj₁ (m - 1) i (by omega)
      have hRight :
          T.obj₃.IsMPseudoCoherent m := by
        -- Proof comment: the third vertex is the top homology module placed in degree `m`.
        simpa [T, truncLE_step_homologyTriangle] using
          singleFunctor_isMPseudoCoherent_of_module
            ((H m).obj K) m m (by simpa using hH m (by simp))
      have hMid : T.obj₂.IsMPseudoCoherent m :=
        isMPseudoCoherent_obj₂_of_distinguishedTriangle T hT hLeft hRight
      letI : IsIso ((t.truncLTι (m + 1)).app K) :=
        (t.isLE_iff_isIso_truncLTι_app m (m + 1) (by omega) K).1 hLE0
      have hMid' : ((t.truncLT (m + 1)).obj K).IsMPseudoCoherent m := by
        -- Proof comment: boundedness identifies the middle truncation with `K` itself.
        simpa [T, truncLE_step_homologyTriangle, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          using hMid
      exact isMPseudoCoherent_of_iso (asIso ((t.truncLTι (m + 1)).app K)) m hMid'
  | succ k ih =>
      intro K hLE hH
      let a : ℤ := m + k
      let T := truncLE_step_homologyTriangle K a
      have hT : T ∈ distTriang DMod := truncLE_step_homology_triangle K a
      have hLeft :
          T.obj₁.IsMPseudoCoherent m := by
        have hLE₁ : T.obj₁.IsLE (m + k) := by
          dsimp [T, a, truncLE_step_homologyTriangle]
          infer_instance
        have hH₁ :
            ∀ i : ℤ, i ≤ m + k → ((H i).obj T.obj₁).IsMPseudoCoherent (m - i) := by
          intro i hi
          have hi' : i < m + k + 1 := by
            omega
          have hIso : IsIso ((H i).map ((t.truncLTι (m + k + 1)).app K)) := by
            exact homology_map_truncLTι_isIso_of_lt_local K i (m + k + 1) hi'
          let eH :
              (H i).obj T.obj₁ ≅ (H i).obj K :=
            @asIso _ _ _ _
              ((H i).map ((t.truncLTι (m + k + 1)).app K))
              hIso
          -- Proof comment: below the top degree, upper truncation does not change homology.
          exact moduleCat_isMPseudoCoherent_of_iso eH.symm (m - i) (hH i (by omega))
        exact ih T.obj₁ hLE₁ hH₁
      have hRight :
          T.obj₃.IsMPseudoCoherent m := by
        -- Proof comment: the new top cohomology term contributes the single-degree third vertex.
        simpa [T, a, truncLE_step_homologyTriangle] using
          singleFunctor_isMPseudoCoherent_of_module
            ((H (m + k + 1)).obj K) (m + k + 1) m
            (by simpa using hH (m + k + 1) (by simp))
      have hMid : T.obj₂.IsMPseudoCoherent m :=
        isMPseudoCoherent_obj₂_of_distinguishedTriangle T hT hLeft hRight
      have hLEs : K.IsLE (m + k + 1) := by
        simpa [add_assoc] using hLE
      letI : IsIso ((t.truncLTι (m + k + 2)).app K) :=
        (t.isLE_iff_isIso_truncLTι_app (m + k + 1) (m + k + 2) (by omega) K).1 hLEs
      have hMid' : ((t.truncLT (m + k + 2)).obj K).IsMPseudoCoherent m := by
        -- Proof comment: boundedness again identifies the middle truncation with the original
        -- object.
        simpa [T, a, truncLE_step_homologyTriangle] using hMid
      exact isMPseudoCoherent_of_iso (asIso ((t.truncLTι (m + k + 2)).app K)) m hMid'

/-- Helper for Lemma 15.65.17: bounded-above degreewise pseudo-coherent homology implies
`m`-pseudo-coherence. -/
private theorem boundedAbove_isMPseudoCoherent_of_homology_local
    (K : DModMinus) (m : ℤ)
    (hH : ∀ i : ℤ, ((H i).obj K.obj).IsMPseudoCoherent (m - i)) :
    K.obj.IsMPseudoCoherent m := by
  obtain ⟨n, hn⟩ := (derivedCategory_t_minus_iff (K := K.obj)).1 K.property
  let b : ℤ := max n m
  have hb : m ≤ b := le_max_right n m
  have hLE : K.obj.IsLE b := by
    -- Proof comment: above the bound `b`, the homology already vanishes because `b ≥ n`.
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact hn i (lt_of_le_of_lt (le_max_left n m) hi)
  have hwidth : m + Int.toNat (b - m) = b := by
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hb)]
    omega
  have hLE' : K.obj.IsLE (m + Int.toNat (b - m)) := by
    exact hwidth.symm ▸ hLE
  -- Proof comment: reduce to the natural-distance induction from the cutoff `m` up to `b`.
  simpa [b, hwidth] using
    isMPseudoCoherent_of_isLE_and_homology_bounds
      m (Int.toNat (b - m)) K.obj hLE' (fun i _ ↦ hH i)

/-- Helper for Lemma 15.65.17: bounded-above degreewise pseudo-coherent homology implies
pseudo-coherence. -/
private theorem boundedAbove_isPseudoCoherent_of_homology_local
    (K : DModMinus)
    (hH : ∀ i : ℤ, ((H i).obj K.obj).IsPseudoCoherent) :
    K.obj.IsPseudoCoherent := by
  -- Proof comment: upgrade each module hypothesis to all fixed pseudo-coherence bounds, then
  -- apply the bounded-above `m`-pseudo-coherent criterion degreewise.
  rw [isPseudoCoherent_iff_forall_isMPseudoCoherent]
  intro m
  exact boundedAbove_isMPseudoCoherent_of_homology_local (K := K) m <| by
    intro i
    have hHi : ((H i).obj K.obj).IsPseudoCoherent := hH i
    rw [ModuleCat.IsPseudoCoherent, isPseudoCoherent_iff_forall_isMPseudoCoherent] at hHi
    exact hHi (m - i)

-- Proof sketch: for the forward implication, use the bounded-above finite-free approximation in
-- the definition of `m`-pseudo-coherence to see that `K` lies in `D^-(R)` and that the cohomology
-- groups in degrees `i ≥ m` are finite. For the reverse implication, combine the bounded-above
-- hypothesis with the finiteness of `H^i(K)` for `i ≥ m`, use that finite modules are
-- pseudo-coherent over a Noetherian ring, and apply Lemma `15.65.10`.
/-- Lemma 15.65.17 (1): a derived `R`-complex is `m`-pseudo-coherent exactly when it lies in
`D^-(R)` and its cohomology modules `H^i` are finite for all `i ≥ m`. -/
@[stacks 066E]
theorem isMPseudoCoherent_iff_boundedAbove_and_homology_finite_ge
    (K : DMod) (m : ℤ) :
    K.IsMPseudoCoherent m ↔
      BoundedAbove K ∧
        ∀ i : ℤ, m ≤ i → Module.Finite R ((H i).obj K) := by
  constructor
  · intro hK
    rcases hK with ⟨E, ⟨a, b, hEa, hEb⟩, hEfree, α, hαgt, hαm⟩
    constructor
    · -- Proof comment: above `max m b`, the source homology already vanishes because `E` is
      -- concentrated in degrees `≤ b`, and the comparison map is an isomorphism there.
      rw [derivedCategory_t_minus_iff]
      refine ⟨max m b, ?_⟩
      intro i hi
      have hib : b < i := by
        omega
      have him : m < i := by
        omega
      have hsource : IsZero ((H i).obj (DerivedCategory.Q.obj E)) := by
        have hQ : (DerivedCategory.Q.obj E).IsLE b := by
          rw [DerivedCategory.isLE_Q_obj_iff]
          let _ : E.IsStrictlyLE b := hEb
          infer_instance
        let _ : (DerivedCategory.Q.obj E).IsLE b := hQ
        exact DerivedCategory.isZero_of_isLE _ b i hib
      let eH : ((H i).obj (DerivedCategory.Q.obj E)) ≅ ((H i).obj K) := by
        let _ : IsIso ((H i).map α) := hαgt i him
        exact asIso ((H i).map α)
      exact eH.isZero_iff.1 hsource
    · intro i hi
      by_cases him : m < i
      · -- Proof comment: in degrees strictly above `m`, homology is identified with that of the
        -- bounded finite-free model `E`.
        have hEhomology : Module.Finite R (E.homology i) :=
          homology_finite_of_termwiseFiniteFree (R := R) i
        have hQhomology : Module.Finite R ((H i).obj (DerivedCategory.Q.obj E)) := by
          let eQ : ((H i).obj (DerivedCategory.Q.obj E)) ≅ E.homology i :=
            CochainComplex.derived_homology_iso (R := R) E i
          let _ : Module.Finite R (E.homology i) := hEhomology
          exact Module.Finite.of_surjective
            eQ.symm.toLinearEquiv.toLinearMap
            eQ.symm.toLinearEquiv.surjective
        let eH : ((H i).obj (DerivedCategory.Q.obj E)) ≅ ((H i).obj K) := by
          let _ : IsIso ((H i).map α) := hαgt i him
          exact asIso ((H i).map α)
        let _ : Module.Finite R ((H i).obj (DerivedCategory.Q.obj E)) := hQhomology
        exact Module.Finite.of_surjective
          eH.toLinearEquiv.toLinearMap
          eH.toLinearEquiv.surjective
      · have hieq : i = m := by
          omega
        subst i
        -- Proof comment: in degree `m`, the defining map is only epi, but that is enough to
        -- descend finiteness from the model complex.
        have hEhomology : Module.Finite R (E.homology m) :=
          homology_finite_of_termwiseFiniteFree (R := R) m
        have hQhomology : Module.Finite R ((H m).obj (DerivedCategory.Q.obj E)) := by
          let eQ : ((H m).obj (DerivedCategory.Q.obj E)) ≅ E.homology m :=
            CochainComplex.derived_homology_iso (R := R) E m
          let _ : Module.Finite R (E.homology m) := hEhomology
          exact Module.Finite.of_surjective
            eQ.symm.toLinearEquiv.toLinearMap
            eQ.symm.toLinearEquiv.surjective
        let _ : Module.Finite R ((H m).obj (DerivedCategory.Q.obj E)) := hQhomology
        exact Module.Finite.of_surjective
          ((H m).map α).hom
          ((ModuleCat.epi_iff_surjective _).1 hαm)
  · rintro ⟨hminus, hfinite⟩
    let Kminus : boundedAboveDerivedCategory (ModuleCat R) := ⟨K, hminus⟩
    -- Proof comment: feed the bounded-above object to Lemma `15.65.10`; below degree `m` every
    -- degree-zero module is automatically `(m - i)`-pseudo-coherent, and from degree `m` onward
    -- finite modules need the remaining nonpositive module-level bridge.
    exact boundedAbove_isMPseudoCoherent_of_homology_local (K := Kminus) m <| by
      intro i
      by_cases him : i < m
      · exact moduleCat_isMPseudoCoherent_of_positive (R := R) ((H i).obj K) (m - i) (by omega)
      · let _ : Module.Finite R ((H i).obj K) := hfinite i (by omega)
        exact
          moduleCat_isMPseudoCoherent_of_nonpos_of_finite
            (R := R) ((H i).obj K) (m - i) (by omega)

-- Proof sketch: apply part `(1)` for every integer `m`. If `K` is pseudo-coherent, then it is
-- `m`-pseudo-coherent for all `m`; conversely, bounded-above together with finiteness of every
-- cohomology module makes each cohomology module pseudo-coherent over a Noetherian ring, so
-- Lemma `15.65.10` yields `m`-pseudo-coherence for every `m`, hence pseudo-coherence.
/-- Lemma 15.65.17 (2): a derived `R`-complex is pseudo-coherent exactly when it lies in `D^-(R)`
and all of its cohomology modules are finite. -/
@[stacks 066E]
theorem isPseudoCoherent_iff_boundedAbove_and_homology_finite
    (K : DMod) :
    K.IsPseudoCoherent ↔
      BoundedAbove K ∧
        ∀ i : ℤ, Module.Finite R ((H i).obj K) := by
  constructor
  · intro hK
    rcases hK with ⟨E, ⟨b, hEb⟩, hEfree, α, hα⟩
    let e : DerivedCategory.Q.obj E ≅ K := asIso α
    constructor
    · -- Proof comment: the chosen bounded-above finite-free model already lies in `D^-(R)`, and
      -- bounded-above membership is invariant under isomorphism.
      have hQ : BoundedAbove (DerivedCategory.Q.obj E) := by
        rw [derivedCategory_t_minus_iff]
        refine ⟨b, ?_⟩
        intro i hi
        have hLE : (DerivedCategory.Q.obj E).IsLE b := by
          rw [DerivedCategory.isLE_Q_obj_iff]
          let _ : E.IsStrictlyLE b := hEb
          infer_instance
        let _ : (DerivedCategory.Q.obj E).IsLE b := hLE
        exact DerivedCategory.isZero_of_isLE _ b i hi
      exact (t.minus : ObjectProperty DMod).prop_of_iso e hQ
    · intro i
      -- Proof comment: derived homology is computed on the finite-free model and transported
      -- across the quasi-isomorphism `α`.
      have hEhomology : Module.Finite R (E.homology i) :=
        homology_finite_of_termwiseFiniteFree (R := R) i
      have hQhomology : Module.Finite R ((H i).obj (DerivedCategory.Q.obj E)) := by
        let eQ : ((H i).obj (DerivedCategory.Q.obj E)) ≅ E.homology i :=
          CochainComplex.derived_homology_iso (R := R) E i
        let _ : Module.Finite R (E.homology i) := hEhomology
        exact Module.Finite.of_surjective
          eQ.symm.toLinearEquiv.toLinearMap
          eQ.symm.toLinearEquiv.surjective
      let eH : ((H i).obj (DerivedCategory.Q.obj E)) ≅ ((H i).obj K) := (H i).mapIso e
      let _ : Module.Finite R ((H i).obj (DerivedCategory.Q.obj E)) := hQhomology
      exact Module.Finite.of_surjective
        eH.toLinearEquiv.toLinearMap
        eH.toLinearEquiv.surjective
  · rintro ⟨hminus, hfinite⟩
    let Kminus : boundedAboveDerivedCategory (ModuleCat R) := ⟨K, hminus⟩
    -- Proof comment: bounded-above finite cohomology modules are pseudo-coherent degreewise, so
    -- the bounded-above criterion upgrades the whole complex.
    exact boundedAbove_isPseudoCoherent_of_homology_local (K := Kminus) <| by
      intro i
      let _ : Module.Finite R ((H i).obj K) := hfinite i
      exact moduleCat_isPseudoCoherent_of_finite (R := R) ((H i).obj K)

end

section

variable {R : Type u} [Ring R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => (ModuleCat.single0Functor : ModuleCat R ⥤ DerivedCategory (ModuleCat R))
local notation "singleCpx₀" => (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ))

-- Proof sketch: over a Noetherian ring, every finite module is pseudo-coherent and every
-- pseudo-coherent module is finite. Translate the module into the derived category concentrated in
-- degree `0` and combine these two implications with the module-level definition of
-- pseudo-coherence.
/-- Lemma 15.65.17 (3): an `R`-module is pseudo-coherent exactly when it is finite. -/
@[stacks 066E]
theorem _root_.Module.isPseudoCoherent_iff_finite :
    (ModuleCat.of R M).IsPseudoCoherent ↔ Module.Finite R M := by
  constructor
  · intro hM
    have hfinite :
        Module.Finite R ((H 0).obj ((single₀).obj (ModuleCat.of R M))) :=
      (isPseudoCoherent_iff_boundedAbove_and_homology_finite
        (R := R) ((single₀).obj (ModuleCat.of R M))).1 hM |>.2 0
    let K : CochainComplex (ModuleCat R) ℤ := (singleCpx₀).obj (ModuleCat.of R M)
    let e0 :
        ((H 0).obj ((single₀).obj (ModuleCat.of R M))) ≅ ModuleCat.of R M :=
      ((H 0).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app
          (ModuleCat.of R M))).symm ≪≫
        CochainComplex.derived_homology_iso (R := R) K 0 ≪≫
          (HomologicalComplex.homologyFunctorSingleIso
            (ModuleCat R) (ComplexShape.up ℤ) (0 : ℤ)).app (ModuleCat.of R M)
    let _ : Module.Finite R ((H 0).obj ((single₀).obj (ModuleCat.of R M))) := hfinite
    simpa using
      (Module.Finite.of_surjective
        e0.toLinearEquiv.toLinearMap
        e0.toLinearEquiv.surjective)
  · intro hM
    let _ : Module.Finite R (ModuleCat.of R M) := hM
    exact moduleCat_isPseudoCoherent_of_finite (R := R) (ModuleCat.of R M)

end

end CategoryTheory
