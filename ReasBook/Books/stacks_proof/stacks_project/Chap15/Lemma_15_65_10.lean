import Mathlib
import stacks_proof.stacks_project.Chap13.Definition_13_11_3
import stacks_proof.stacks_project.Chap13.Lemma_13_27_9
import stacks_proof.stacks_project.Chap13.Remark_13_12_4
import stacks_proof.stacks_project.Chap13.Situation_13_15_1
import stacks_proof.stacks_project.Chap15.Definition_15_65_1
import stacks_proof.stacks_project.Chap15.Lemma_15_65_2

noncomputable section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DerivedCategory.TStructure
open scoped ZeroObject

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "DModMinus" => boundedAboveDerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/-- Helper for Lemma 15.65.10: the zero cochain complex over `ModuleCat R`. -/
private abbrev zeroCpx : Cpx := 0

/- Domain-style sampling for Lemma 15.65.10:
- primary domain: pseudo-coherence of bounded-above derived `R`-complexes from degreewise
  pseudo-coherence of their cohomology modules;
- sampled owner declarations:
  `boundedAboveDerivedCategory`,
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `DerivedCategory.homologyFunctor`;
- best owner abstraction: bounded-above complexes should be carried by the chapter owner
  `boundedAboveDerivedCategory (ModuleCat R)` rather than by a separate membership proof in
  `t.minus`;
- primitive vs. derived:
  primitive data are the bounded-above derived object `K : DModMinus` and the degreewise
  cohomology hypotheses;
  derived API is the resulting owner conclusions `K.obj.IsMPseudoCoherent m` and
  `K.obj.IsPseudoCoherent`;
- source/core/bridge triage:
  `source-facing`: the bounded-above cohomology criteria below;
  `core/canonical`: `DModMinus`, `K.IsMPseudoCoherent`, `K.IsPseudoCoherent`, and
    `DerivedCategory.homologyFunctor`;
  `bridge/view`: reading the cohomology hypotheses via `K.obj` in the ambient unbounded derived
    category.
-/

-- Proof sketch: choose a bounded-above representative for `K` and induct on the largest degree
-- with nonvanishing cohomology. If this degree is `< m`, apply Lemma `15.65.7`; otherwise use the
-- truncation triangle with top cohomology `H^n(K)[-n]`, note that the hypothesis makes this shift
-- `m`-pseudo-coherent, and reduce to the lower truncation via Lemma `15.65.2`.
/-- Helper for Lemma 15.65.10: the zero cochain complex is termwise finite free. -/
private instance zero_isTermwiseFiniteFree : (zeroCpx (R := R)).IsTermwiseFiniteFree where
  out i := by
    let E0 : Cpx := zeroCpx (R := R)
    change Module.Free R ↥(E0.X i) ∧ Module.Finite R ↥(E0.X i)
    let hzero : IsZero (E0.X i) := by
      simpa [zeroCpx] using
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i).map_isZero
          (isZero_zero Cpx : IsZero (0 : Cpx))
    letI : Subsingleton ↥(E0.X i) :=
      ModuleCat.subsingleton_of_isZero hzero
    refine
      ⟨Module.Free.of_subsingleton (R := R) (N := ↥(E0.X i)), ?_⟩
    let e : ModuleCat.of R PUnit ≅ E0.X i :=
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)).isoZero ≪≫ hzero.isoZero.symm
    exact Module.Finite.equiv e.toLinearEquiv

/-- Helper for Lemma 15.65.10: module-level `m`-pseudo-coherence transports across module
isomorphisms. -/
private theorem moduleCat_isMPseudoCoherent_of_iso
    {M N : ModuleCat R} (e : M ≅ N) (a : ℤ)
    (hM : M.IsMPseudoCoherent a) :
    N.IsMPseudoCoherent a := by
  -- Proof comment: move the module isomorphism through the degree-zero embedding into `D(R)`.
  rw [ModuleCat.IsMPseudoCoherent] at hM ⊢
  exact isMPseudoCoherent_of_iso ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).mapIso e) a hM

/-- Helper for Lemma 15.65.10: if all homology in degrees `≥ m` vanishes, then the derived object
is `m`-pseudo-coherent. -/
private theorem isMPseudoCoherent_of_homology_vanishes_ge
    {K : DMod} {m : ℤ}
    (hK : ∀ i : ℤ, m ≤ i → IsZero ((H i).obj K)) :
    K.IsMPseudoCoherent m := by
  let E0 : Cpx := zeroCpx (R := R)
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
          ((DerivedCategory.Q).map_isZero (isZero_zero Cpx : IsZero (0 : Cpx)))
    let htgt : IsZero ((H i).obj K) := hK i (le_of_lt hi)
    exact hsrc.isIso htgt ((H i).map α)
  · -- Proof comment: the same zero-object argument makes the degree-`m` map an epimorphism.
    let hsrc : IsZero ((H m).obj (DerivedCategory.Q.obj E0)) := by
      simpa [zeroCpx] using
        (H m).map_isZero
          ((DerivedCategory.Q).map_isZero (isZero_zero Cpx : IsZero (0 : Cpx)))
    let htgt : IsZero ((H m).obj K) := hK m le_rfl
    letI : IsIso ((H m).map α) := hsrc.isIso htgt ((H m).map α)
    infer_instance

/-- Helper for Lemma 15.65.10: upper truncation preserves homology below the cutoff. -/
private theorem homology_map_truncLTι_succ_isIso_local
    (K : DMod) (i : ℤ) :
    IsIso ((H i).map ((t.truncLTι (i + 1)).app K)) := by
  let T : Triangle DMod := (t.triangleLTGE (i + 1)).obj K
  have hT : T ∈ distTriang DMod := by
    simpa [T] using t.triangleLTGE_distinguished (i + 1) K
  have h₃ : T.obj₃.IsGE (i + 1) := by
    dsimp [T]
    infer_instance
  have hmor₂_zero : (H i).map T.mor₂ = 0 := by
    letI := h₃
    exact (DerivedCategory.isZero_of_isGE T.obj₃ (i + 1) i (by omega)).eq_of_tgt _ _
  have hδ_zero : DerivedCategory.HomologySequence.δ T (i - 1) i (by omega) = 0 := by
    letI := h₃
    exact (DerivedCategory.isZero_of_isGE T.obj₃ (i + 1) (i - 1) (by omega)).eq_of_src _ _
  letI : Epi ((H i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).2 hmor₂_zero
  letI : Mono ((H i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
      T hT (i - 1) i (by omega)).2 hδ_zero
  simpa [T] using (isIso_of_mono_of_epi ((H i).map T.mor₁))

/-- Helper for Lemma 15.65.10: upper truncation preserves homology below the cutoff. -/
private theorem homology_map_truncLTι_isIso_of_lt_local
    (K : DMod) (i c : ℤ) (hi : i < c) :
    IsIso ((H i).map ((t.truncLTι c).app K)) := by
  -- Route correction: replay the proof of Lemma `13.27.9` in the specialized `ModuleCat R`
  -- setting so the truncation comparison is cached before the successor-step transport uses it.
  let f : (t.truncLT c).obj K ⟶ K := (t.truncLTι c).app K
  let Y : DMod := (t.truncLT c).obj K
  letI : IsIso ((H i).map ((t.truncLTι (i + 1)).app K)) :=
    homology_map_truncLTι_succ_isIso_local K i
  letI : IsIso ((H i).map ((t.truncLTι (i + 1)).app Y)) :=
    homology_map_truncLTι_succ_isIso_local Y i
  let eK : (H i).obj K ≅ (H i).obj ((t.truncLT (i + 1)).obj K) :=
    (asIso ((H i).map ((t.truncLTι (i + 1)).app K))).symm
  let eY : (H i).obj Y ≅ (H i).obj ((t.truncLT (i + 1)).obj Y) :=
    (asIso ((H i).map ((t.truncLTι (i + 1)).app Y))).symm
  -- Proof comment: naturality of the adjacent truncation inclusion compares the desired homology
  -- map with the same map after truncating once more at `i + 1`.
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
    -- Proof comment: after truncating both source and target at `i + 1`, the comparison map is
    -- an isomorphism because `i + 1 ≤ c`.
    haveI : IsIso ((t.truncLT (i + 1)).map f) :=
      t.isIso_truncLT_map_truncLTι_app (i + 1) c (by omega) K
    exact Functor.map_isIso (H i) ((t.truncLT (i + 1)).map f)
  have hcomp : IsIso ((H i).map f ≫ eK.hom) := by
    rw [← hf]
    letI : IsIso ((H i).map ((t.truncLT (i + 1)).map f)) := hmiddle
    infer_instance
  letI : IsIso ((H i).map f ≫ eK.hom) := hcomp
  exact IsIso.of_isIso_comp_right ((H i).map f) eK.hom

/-- Helper for Lemma 15.65.10: a module that is `(m - n)`-pseudo-coherent yields an
`m`-pseudo-coherent single object in degree `n`. -/
private theorem singleFunctor_isMPseudoCoherent_of_module
    (M : ModuleCat R) (n m : ℤ)
    (hM : M.IsMPseudoCoherent (m - n)) :
    ((DerivedCategory.singleFunctor (ModuleCat R) n).obj M).IsMPseudoCoherent m := by
  let e :
      (((DerivedCategory.singleFunctor (ModuleCat R) n).obj M)⟦n⟧) ≅
        ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj M) :=
    ((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso n 0 n (by simp)).app M
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

/-- Helper for Lemma 15.65.10: if `K` is bounded above by `m + k`, then the degreewise module
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
      -- Proof comment: boundedness identifies the middle truncation with `K` itself.
      have hMid' : ((t.truncLT (m + 1)).obj K).IsMPseudoCoherent m := by
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
      -- Proof comment: boundedness again identifies the middle truncation with the original
      -- object.
      have hMid' : ((t.truncLT (m + k + 2)).obj K).IsMPseudoCoherent m := by
        simpa [T, a, truncLE_step_homologyTriangle] using hMid
      exact isMPseudoCoherent_of_iso (asIso ((t.truncLTι (m + k + 2)).app K)) m hMid'

/-- Lemma 15.65.10: if `K` is a bounded-above derived `R`-complex and every cohomology module
`H^i(K)` is `(m - i)`-pseudo-coherent, then `K` is `m`-pseudo-coherent. -/
@[stacks 066B]
theorem boundedAbove_isMPseudoCoherent_of_homology
    (K : DModMinus) (m : ℤ)
    (hH : ∀ i : ℤ, ((H i).obj K.obj).IsMPseudoCoherent (m - i)) :
    K.obj.IsMPseudoCoherent m := by
  obtain ⟨n, hn⟩ := (derivedCategory_t_minus_iff (K := K.obj)).1 K.property
  let b : ℤ := max n m
  have hb : m ≤ b := le_max_right n m
  have hLE : K.obj.IsLE b := by
    -- Proof comment: above the bound `b`, the cohomology already vanishes because `b ≥ n`.
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

-- Proof sketch: apply the previous theorem for each integer `m`, using that a pseudo-coherent
-- module is `(m - i)`-pseudo-coherent for every `i`, and conclude with the characterization of
-- pseudo-coherence from Lemma `15.65.5`.
/-- If every cohomology module of a bounded-above derived `R`-complex is pseudo-coherent, then the
complex itself is pseudo-coherent. -/
theorem boundedAbove_isPseudoCoherent_of_homology
    (K : DModMinus)
    (hH : ∀ i : ℤ, ((H i).obj K.obj).IsPseudoCoherent) :
    K.obj.IsPseudoCoherent := by
  -- Route correction: the intended reduction uses the earlier bridge
  -- `IsPseudoCoherent ↔ ∀ m, IsMPseudoCoherent m`, but the dependency file providing the needed
  -- cochain-level TFAE currently fails to compile in this workspace.
  -- TODO: once the earlier dependency is repaired, rewrite each module hypothesis through that
  -- bridge and apply `boundedAbove_isMPseudoCoherent_of_homology` for an arbitrary `m`.
  sorry

end

end CategoryTheory
