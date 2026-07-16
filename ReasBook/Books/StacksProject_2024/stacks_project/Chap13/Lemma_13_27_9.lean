import Mathlib
import StacksProject_2024.stacks_project.Chap13.Definition_13_11_3
import StacksProject_2024.stacks_project.Chap13.Definition_13_27_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open CategoryTheory.Abelian
open DerivedCategory
open DerivedCategory.TStructure
open CategoryTheory.Pretriangulated
open scoped CategoryTheory DerivedExt

universe w v u

section

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜] [HasExt.{w} 𝒜]

local notation "H" => DerivedCategory.homologyFunctor 𝒜

/- Domain-style sampling for bounded derived decompositions:
- primary domain: objects of `D(𝒜)`, their cohomology objects in `𝒜`, and finite biproduct
  realizations of the intrinsic shifted-cohomology family over bounded integer intervals;
- sampled owner declarations:
  `CategoryTheory.derivedCategory_t_bounded_iff`,
  `DerivedCategory.isGE_iff`,
  `DerivedCategory.isLE_iff`,
  `DerivedCategory.homologyFunctor`,
  `DerivedCategory.singleFunctor`,
  `Set.Icc`,
  `CategoryTheory.Abelian.Ext`;
- best owner abstraction: the intrinsic family `i ↦ H^i(K)[-i]` is attached directly to
  `K : D(𝒜)`, while explicit bounds `a ≤ * ≤ b` belong only to the bridge that realizes a finite
  subfamily as a biproduct for bounded-amplitude objects;
- primitive data: the derived object `K : D(𝒜)` and the canonical cohomology owners `H^i`;
- derived API: the intrinsic family `shiftedCohomology 𝒜 K`, the interval restriction
  `shiftedCohomologyOn 𝒜 K a b`, the bounded-amplitude splitting theorem with hypotheses
  `K.IsGE a` and `K.IsLE b`, and the bounded-derived specialization obtained from
  `derivedCategory_t_bounded_iff`.

Source/core/bridge triage:
- `source-facing`: the bounded-derived splitting statement for `K : Dᵇ(𝒜)` and the intrinsic
  shifted-cohomology family `i ↦ H^i(K)[-i]`;
- `core/canonical`: `D(𝒜)`, `Set.Icc`, `H^i`, `singleFunctor`,
  `CategoryTheory.derivedCategory_t_bounded_iff`, `DerivedCategory.isGE_iff`,
  `DerivedCategory.isLE_iff`, `CategoryTheory.Abelian.Ext`;
- `bridge/view`: the explicit interval restriction in `D(𝒜)` with bounds `a b` and the bounded
  finite-biproduct realization hypotheses `K.IsGE a`, `K.IsLE b`.
-/

/-- The intrinsic shifted cohomology family `i ↦ H^i(K)[-i]` attached to `K : D(𝒜)`. -/
noncomputable abbrev shiftedCohomology (K : DerivedCategory 𝒜) :
    ℤ → DerivedCategory 𝒜 :=
  fun i ↦ (singleFunctor 𝒜 i).obj ((H^i).obj K)

/-- The restriction of the shifted cohomology family of `K` to the finite interval `[a, b]`. -/
noncomputable abbrev shiftedCohomologyOn (K : DerivedCategory 𝒜) (a b : ℤ) :
    Set.Icc a b → DerivedCategory 𝒜 :=
  fun i ↦ shiftedCohomology 𝒜 K i

/-- Helper for Lemma 13.27.9: the interval `[a, a]` has a single index. -/
noncomputable def intervalSingletonEquiv (a : ℤ) : PUnit.{1} ≃ Set.Icc a a where
  toFun _ := ⟨a, le_rfl, le_rfl⟩
  invFun _ := PUnit.unit
  left_inv _ := rfl
  right_inv i := by
    rcases i with ⟨i, hi⟩
    apply Subtype.ext
    change a = i
    exact (le_antisymm hi.2 hi.1).symm

/-- Helper for Lemma 13.27.9: if `b < a`, then the interval `[a, b]` is empty. -/
noncomputable def intervalEmptyEquiv (a b : ℤ) (hba : b < a) : Set.Icc a b ≃ Empty where
  toFun i := by
    exfalso
    exact not_le_of_gt hba (le_trans i.2.1 i.2.2)
  invFun e := Empty.elim e
  left_inv i := by
    exfalso
    exact not_le_of_gt hba (le_trans i.2.1 i.2.2)
  right_inv e := Empty.elim e

/-- Helper for Lemma 13.27.9: adjoining the top index identifies the sigma-indexed family with
the interval `[a, a + n + 1]`. -/
noncomputable def intervalSuccEquiv (a : ℤ) (n : ℕ) :
    (Σ s : WalkingPair, WalkingPair.casesOn s (Set.Icc a (a + n)) PUnit) ≃
      Set.Icc a (a + (n + 1 : ℕ)) := by
  let eSigma :
      (Σ s : WalkingPair, WalkingPair.casesOn s (Set.Icc a (a + n)) PUnit) ≃
        Set.Icc a (a + n) ⊕ PUnit :=
    { toFun := fun s ↦
        match s with
        | ⟨WalkingPair.left, i⟩ => Sum.inl i
        | ⟨WalkingPair.right, u⟩ => Sum.inr u
      invFun := fun s ↦
        match s with
        | Sum.inl i => ⟨WalkingPair.left, i⟩
        | Sum.inr u => ⟨WalkingPair.right, u⟩
      left_inv := by
        intro s
        rcases s with ⟨s, i⟩
        cases s <;> rfl
      right_inv := by
        intro s
        cases s <;> rfl }
  let eSum : Set.Icc a (a + n) ⊕ PUnit ≃ Set.Icc a (a + (n + 1 : ℕ)) :=
    { toFun := fun s ↦
        match s with
        | Sum.inl i => ⟨i.1, i.2.1, le_trans i.2.2 (by omega)⟩
        | Sum.inr _ => ⟨a + (n + 1 : ℕ), by omega, le_rfl⟩
      invFun := fun i ↦
        if hi : i.1 ≤ a + n then
          Sum.inl ⟨i.1, i.2.1, hi⟩
        else
          Sum.inr PUnit.unit
      left_inv := by
        intro s
        cases s with
        | inl i =>
            rcases i with ⟨i, hi₁, hi₂⟩
            -- The old interval points stay on the left summand.
            simp [hi₂]
        | inr u =>
            -- The adjoined summand is sent to the new top index.
            have htop : ¬ a + (n + 1 : ℕ) ≤ a + n := by
              omega
            simp
      right_inv := by
        intro i
        rcases i with ⟨i, hi₁, hi₂⟩
        by_cases hi : i ≤ a + n
        · -- Points already below the top bound come from the left summand.
          simp [hi]
        · -- The only remaining point of `[a, a + n + 1]` is the new top index.
          have htop : i = a + (n + 1 : ℕ) := by
            omega
          subst htop
          simp }
  -- Factor through the non-dependent sum model to avoid Sigma transport bookkeeping.
  exact eSigma.trans eSum

omit [HasExt 𝒜] in
private theorem isIso_homologyMap_truncGEπ
    (K : DerivedCategory 𝒜) (n : ℤ) :
    IsIso ((H n).map ((t.truncGEπ n).app K)) := by
  let T : Triangle (DerivedCategory 𝒜) := (t.triangleLTGE n).obj K
  have hT : T ∈ distTriang (DerivedCategory 𝒜) := by
    simpa [T] using t.triangleLTGE_distinguished n K
  have h₁ : T.obj₁.IsLE (n - 1) := by
    dsimp [T]
    infer_instance
  have hmor₁_zero : (H n).map T.mor₁ = 0 := by
    letI := h₁
    exact (isZero_of_isLE T.obj₁ (n - 1) n (by omega)).eq_of_src _ _
  have hδ_zero : HomologySequence.δ T n (n + 1) rfl = 0 := by
    letI := h₁
    exact (isZero_of_isLE T.obj₁ (n - 1) (n + 1) (by omega)).eq_of_tgt _ _
  letI : Epi ((H n).map T.mor₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff T hT n (n + 1) rfl).2 hδ_zero
  letI : Mono ((H n).map T.mor₂) :=
    (HomologySequence.mono_homologyMap_mor₂_iff T hT n).2 hmor₁_zero
  simpa [T] using (isIso_of_mono_of_epi ((H n).map T.mor₂))

omit [HasExt 𝒜] in
private theorem isIso_homologyMap_truncLTι
    (K : DerivedCategory 𝒜) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    IsIso ((H n₀).map ((t.truncLTι n₁).app K)) := by
  subst h
  let T : Triangle (DerivedCategory 𝒜) := (t.triangleLTGE (n₀ + 1)).obj K
  have hT : T ∈ distTriang (DerivedCategory 𝒜) := by
    simpa [T] using t.triangleLTGE_distinguished (n₀ + 1) K
  have h₃ : T.obj₃.IsGE (n₀ + 1) := by
    dsimp [T]
    infer_instance
  have hmor₂_zero : (H n₀).map T.mor₂ = 0 := by
    letI := h₃
    exact (isZero_of_isGE T.obj₃ (n₀ + 1) n₀ (by omega)).eq_of_tgt _ _
  have hδ_zero : HomologySequence.δ T (n₀ - 1) n₀ (by omega) = 0 := by
    letI := h₃
    exact (isZero_of_isGE T.obj₃ (n₀ + 1) (n₀ - 1) (by omega)).eq_of_src _ _
  letI : Epi ((H n₀).map T.mor₁) :=
    (HomologySequence.epi_homologyMap_mor₁_iff T hT n₀).2 hmor₂_zero
  letI : Mono ((H n₀).map T.mor₁) :=
    (HomologySequence.mono_homologyMap_mor₁_iff T hT (n₀ - 1) n₀ (by omega)).2 hδ_zero
  simpa [T] using (isIso_of_mono_of_epi ((H n₀).map T.mor₁))

private instance (K : DerivedCategory 𝒜) (n : ℤ) :
    IsIso ((H n).map ((t.truncGEπ n).app K)) :=
  isIso_homologyMap_truncGEπ (𝒜 := 𝒜) K n

private instance (K : DerivedCategory 𝒜) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    IsIso ((H n₀).map ((t.truncLTι n₁).app K)) :=
  isIso_homologyMap_truncLTι (𝒜 := 𝒜) K n₀ n₁ h

/-- Helper for Lemma 13.27.9: an object concentrated in one cohomological degree is the
corresponding single object. -/
private noncomputable def singleFunctorIsoOfIsGEOfIsLE
    (X : DerivedCategory 𝒜) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    X ≅ (singleFunctor 𝒜 n).obj ((H n).obj X) := by
  classical
  let hX := exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  let Y := Classical.choose hX
  let e : X ≅ (singleFunctor 𝒜 n).obj Y := Classical.choice (Classical.choose_spec hX)
  let eH : (H n).obj X ≅ Y :=
    (H n).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso 𝒜 n).app Y
  exact e ≪≫ (singleFunctor 𝒜 n).mapIso eH.symm

/-- Helper for Lemma 13.27.9: the canonical `shiftIso` identifies the degree-`i` single object,
after shifting by `i`, with the degree-zero single object. -/
noncomputable def singleFunctor_shifted_single0_iso_canonical
    (A : 𝒜) (i : ℤ) :
    (((singleFunctor 𝒜 i).obj A)⟦i⟧) ≅ ((singleFunctor 𝒜 0).obj A) :=
  ((singleFunctors 𝒜).shiftIso i 0 i (by simp)).app A

/-- Helper for Lemma 13.27.9: the comparison map from a smaller upper truncation to a larger one
composes with the larger truncation inclusion to the smaller truncation inclusion. -/
lemma natTransTruncLTOfLE_comp_truncLTι_app
    (K : DerivedCategory 𝒜) (i c : ℤ) (hic : i + 1 ≤ c) :
    (t.natTransTruncLTOfLE (i + 1) c hic).app K ≫ (t.truncLTι c).app K =
      (t.truncLTι (i + 1)).app K := by
  -- Reuse the owner truncation naturality identity instead of reproving the same composite.
  simpa using t.natTransTruncLTOfLE_ι_app (i + 1) c hic K

/-- Helper for Lemma 13.27.9: the canonical inclusion `τ_{< c} K ⟶ K` induces an isomorphism on
degree-`i` homology whenever `i < c`. -/
lemma homology_map_truncLTι_isIso_of_lt
    (K : DerivedCategory 𝒜) (i c : ℤ) (hi : i < c) :
    IsIso ((H i).map ((t.truncLTι c).app K)) := by
  let f : (t.truncLT c).obj K ⟶ K := (t.truncLTι c).app K
  let Y : DerivedCategory 𝒜 := (t.truncLT c).obj K
  letI : IsIso ((H i).map ((t.truncLTι (i + 1)).app K)) :=
    isIso_homologyMap_truncLTι (𝒜 := 𝒜) K i (i + 1) rfl
  letI : IsIso ((H i).map ((t.truncLTι (i + 1)).app Y)) :=
    isIso_homologyMap_truncLTι (𝒜 := 𝒜) Y i (i + 1) rfl
  let eK : (H i).obj K ≅ (H i).obj ((t.truncLT (i + 1)).obj K) :=
    (asIso ((H i).map ((t.truncLTι (i + 1)).app K))).symm
  let eY : (H i).obj Y ≅ (H i).obj ((t.truncLT (i + 1)).obj Y) :=
    (asIso ((H i).map ((t.truncLTι (i + 1)).app Y))).symm
  -- Naturality of `t.truncLTι (i + 1)` compares the desired map with its truncation.
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
      simpa [Category.assoc] using congrArg (fun m => eY.hom ≫ m) hnat
    have h₂ :
        eY.hom ≫ (H i).map ((t.truncLTι (i + 1)).app Y) ≫ (H i).map f =
          (H i).map f := by
      simpa [Category.assoc] using congrArg (fun m => m ≫ (H i).map f) hYinv
    have h₃ :
        (H i).map f =
          (H i).map f ≫ eK.hom ≫ (H i).map ((t.truncLTι (i + 1)).app K) := by
      symm
      simpa [Category.assoc] using congrArg (fun m => (H i).map f ≫ m) hKinv
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

/-- Helper for Lemma 13.27.9: the upper truncation does not change cohomology in degrees below
the truncation bound. -/
noncomputable def shiftedCohomology_truncLT_iso
    (K : DerivedCategory 𝒜) (c i : ℤ) (hi : i < c) :
    shiftedCohomology 𝒜 ((t.truncLT c).obj K) i ≅ shiftedCohomology 𝒜 K i :=
  let e :
      (H i).obj ((t.truncLT c).obj K) ≅ (H i).obj K :=
    @asIso _ _ _ _ ((H i).map ((t.truncLTι c).app K))
      (homology_map_truncLTι_isIso_of_lt (𝒜 := 𝒜) K i c hi)
  -- Push the owner-level homology isomorphism through the single-object embedding.
  (singleFunctor 𝒜 i).mapIso e

/-- Helper for Lemma 13.27.9: the top truncation step is canonically the shifted top
cohomology object. -/
private noncomputable def truncLE_step_homologyIso
    (K : DerivedCategory 𝒜) (a : ℤ) :
    (H (a + 1)).obj ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)) ≅
      (H (a + 1)).obj K := by
  -- Compare the source and target through the common middle object `τ_{< a+2} K`.
  have hsucc : a + 1 + 1 = a + 2 := by
    omega
  let eπ :
      (H (a + 1)).obj ((t.truncLT (a + 2)).obj K) ≅
        (H (a + 1)).obj ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)) :=
    @CategoryTheory.asIso _ _ _ _
      ((H (a + 1)).map ((t.truncGEπ (a + 1)).app ((t.truncLT (a + 2)).obj K)))
      (isIso_homologyMap_truncGEπ (𝒜 := 𝒜) ((t.truncLT (a + 2)).obj K) (a + 1))
  let eι : (H (a + 1)).obj ((t.truncLT (a + 2)).obj K) ≅ (H (a + 1)).obj K :=
    @CategoryTheory.asIso _ _ _ _
      ((H (a + 1)).map ((t.truncLTι (a + 2)).app K))
      (isIso_homologyMap_truncLTι (𝒜 := 𝒜) K (a + 1) (a + 2) hsucc)
  exact eπ.symm ≪≫ eι

/-- Helper for Lemma 13.27.9: the third vertex in the truncation step triangle is the shifted top
cohomology object. -/
private noncomputable def truncLE_step_termIso
    (K : DerivedCategory 𝒜) (a : ℤ) :
    ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)) ≅
      shiftedCohomology 𝒜 K (a + 1) := by
  have h : (a + 2) - 1 = a + 1 := by
    omega
  haveI : ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)).IsLE (a + 1) := by
    -- The successive truncation is concentrated in the top surviving degree.
    simpa [h] using
      (inferInstance :
        ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)).IsLE ((a + 2) - 1))
  -- Identify the concentrated object with a single object on its degree-`a+1` homology.
  exact
    singleFunctorIsoOfIsGEOfIsLE (𝒜 := 𝒜)
        ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)) (a + 1) ≪≫
      (singleFunctor 𝒜 (a + 1)).mapIso (truncLE_step_homologyIso (𝒜 := 𝒜) K a)

/-- Helper for Lemma 13.27.9: the source-facing upper truncation step triangle. -/
private noncomputable def truncLE_step_homologyTriangle
    (K : DerivedCategory 𝒜) (a : ℤ) :
    Triangle (DerivedCategory 𝒜) :=
  Triangle.mk
    ((t.natTransTruncLTOfLE (a + 1) (a + 2) (by omega)).app K)
    (((Functor.whiskerLeft (t.truncLT (a + 2)) (t.truncGEπ (a + 1))).app K) ≫
      (truncLE_step_termIso (𝒜 := 𝒜) K a).hom)
    ((truncLE_step_termIso (𝒜 := 𝒜) K a).inv ≫ (t.truncGELTδLT (a + 1) (a + 2)).app K)

private noncomputable def truncLE_step_homologyTriangleIso
    (K : DerivedCategory 𝒜) (a : ℤ) :
    truncLE_step_homologyTriangle (𝒜 := 𝒜) K a ≅
      (t.triangleLTLTGELT (a + 1) (a + 2) (by omega)).obj K := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (truncLE_step_termIso (𝒜 := 𝒜) K a).symm ?_ ?_ ?_
  · simp [truncLE_step_homologyTriangle]
  · simp [truncLE_step_homologyTriangle]
  · simp [truncLE_step_homologyTriangle]

/-- Helper for Lemma 13.27.9: the upper truncation step is a distinguished triangle. -/
private theorem truncLE_step_homology_triangle
    (K : DerivedCategory 𝒜) (a : ℤ) :
    truncLE_step_homologyTriangle (𝒜 := 𝒜) K a ∈ distTriang (DerivedCategory 𝒜) := by
  -- The local source-facing triangle is just the owner truncation triangle with the third
  -- vertex rewritten to the top cohomology single object.
  exact
    isomorphic_distinguished _
      (t.triangleLTLTGELT_distinguished (a + 1) (a + 2) (by omega) K) _
      (truncLE_step_homologyTriangleIso (𝒜 := 𝒜) K a)

/-- Helper for Lemma 13.27.9: if the connecting morphism in the upper truncation step vanishes,
then the next truncation is the binary biproduct of the previous truncation and the top shifted
cohomology term. -/
theorem truncLE_step_split_iso
    (K : DerivedCategory 𝒜) (c : ℤ)
    (hzero : (truncLE_step_homologyTriangle (𝒜 := 𝒜) K c).mor₃ = 0) :
    Nonempty (((t.truncLT (c + 2)).obj K) ≅
      ((t.truncLT (c + 1)).obj K) ⊞ shiftedCohomology 𝒜 K (c + 1)) := by
  let T := truncLE_step_homologyTriangle (𝒜 := 𝒜) K c
  have hT : T ∈ distTriang (DerivedCategory 𝒜) := by
    -- Reuse the concrete truncation-step triangle rather than reopening any transport layer.
    simpa [T] using truncLE_step_homology_triangle (𝒜 := 𝒜) K c
  obtain ⟨e, _, _⟩ := exists_iso_binaryBiproduct_of_distTriang T hT hzero
  have e' :
      ((t.truncLT (c + 2)).obj K) ≅
        ((t.truncLT (c + 1)).obj K) ⊞ shiftedCohomology 𝒜 K (c + 1) := by
    -- The owner split theorem already has the right object order for this triangle.
    simpa [T, truncLE_step_homologyTriangle] using e
  exact ⟨e'⟩

/-- Helper for Lemma 13.27.9: morphisms from a higher-degree single object to a lower-degree
single object shifted once identify with the corresponding `Ext` group. -/
noncomputable def hom_singleFunctor_shift_equiv_ext
    (B A : 𝒜) (i j : ℤ) (hji : j < i) :
    (((singleFunctor 𝒜 i).obj B) ⟶ ((singleFunctor 𝒜 j).obj A)⟦(1 : ℤ)⟧) ≃
      Ext B A (Int.toNat (i - j + 1)) := by
  -- Normalize both single objects to degree `0`, shift the source back across the adjunction,
  -- and then read the resulting shifted Hom as the owner `Ext` group.
  let eB : (singleFunctor 𝒜 i).obj B ≅ ((singleFunctor 𝒜 0).obj B)⟦-i⟧ :=
    (shiftShiftNeg ((singleFunctor 𝒜 i).obj B) i).symm ≪≫
      (shiftFunctor (DerivedCategory 𝒜) (-i)).mapIso
        (singleFunctor_shifted_single0_iso_canonical (𝒜 := 𝒜) B i)
  let eA₁ :
      ((singleFunctor 𝒜 j).obj A)⟦(1 : ℤ)⟧ ≅ (((singleFunctor 𝒜 0).obj A)⟦-j⟧)⟦(1 : ℤ)⟧ :=
    (shiftFunctor (DerivedCategory 𝒜) (1 : ℤ)).mapIso <|
      (shiftShiftNeg ((singleFunctor 𝒜 j).obj A) j).symm ≪≫
        (shiftFunctor (DerivedCategory 𝒜) (-j)).mapIso
          (singleFunctor_shifted_single0_iso_canonical (𝒜 := 𝒜) A j)
  let eA₂ :
      (((singleFunctor 𝒜 0).obj A)⟦-j⟧)⟦(1 : ℤ)⟧ ≅ ((singleFunctor 𝒜 0).obj A)⟦(1 - j : ℤ)⟧ :=
    (shiftFunctorAdd' (DerivedCategory 𝒜) (-j) (1 : ℤ) (1 - j : ℤ) (by omega)).symm.app
      ((singleFunctor 𝒜 0).obj A)
  let eA : ((singleFunctor 𝒜 j).obj A)⟦(1 : ℤ)⟧ ≅ ((singleFunctor 𝒜 0).obj A)⟦(1 - j : ℤ)⟧ :=
    eA₁ ≪≫ eA₂
  let eHom₁ := Iso.homCongr eB eA
  let eHom₂ :
      ((((singleFunctor 𝒜 0).obj B)⟦-i⟧) ⟶ ((singleFunctor 𝒜 0).obj A)⟦(1 - j : ℤ)⟧) ≃
        (((singleFunctor 𝒜 0).obj B) ⟶ (((singleFunctor 𝒜 0).obj A)⟦(1 - j : ℤ)⟧)⟦i⟧) :=
    ((shiftEquiv (DerivedCategory 𝒜) i).symm.toAdjunction.homEquiv
      ((singleFunctor 𝒜 0).obj B) (((singleFunctor 𝒜 0).obj A)⟦(1 - j : ℤ)⟧))
  let eHom₃ :
      (((singleFunctor 𝒜 0).obj B) ⟶ (((singleFunctor 𝒜 0).obj A)⟦(1 - j : ℤ)⟧)⟦i⟧) ≃
        (((singleFunctor 𝒜 0).obj B) ⟶ ((singleFunctor 𝒜 0).obj A)⟦(i - j + 1 : ℤ)⟧) :=
    Iso.homCongr (Iso.refl _) <|
      (shiftFunctorAdd' (DerivedCategory 𝒜) (1 - j : ℤ) i (i - j + 1 : ℤ) (by omega)).symm.app _
  let hi_nonneg : 0 ≤ i - j + 1 := by
    omega
  have hi_cast : (((Int.toNat (i - j + 1) : ℕ) : ℤ)) = i - j + 1 := by
    exact Int.toNat_of_nonneg hi_nonneg
  let eHom₄ :
      (((singleFunctor 𝒜 0).obj B) ⟶ ((singleFunctor 𝒜 0).obj A)⟦(i - j + 1 : ℤ)⟧) ≃
        Ext B A (Int.toNat (i - j + 1)) := by
    simpa [hi_cast] using
      (CategoryTheory.Abelian.Ext.homEquiv (C := 𝒜) (X := B) (Y := A)
        (n := Int.toNat (i - j + 1))).symm
  exact eHom₁.trans (eHom₂.trans (eHom₃.trans eHom₄))

/-- Helper for Lemma 13.27.9: each component of the connecting morphism vanishes because it lands
in a higher `Ext` group covered by the hypothesis. -/
lemma subsingleton_hom_singleFunctor_to_shifted_singleFunctor_of_ext_vanishing
    (B A : 𝒜) (i j : ℤ) (hji : j < i)
    (hBA : ∀ n : ℕ, 2 ≤ n → Subsingleton (Ext B A n)) :
    Subsingleton (((singleFunctor 𝒜 i).obj B) ⟶ ((singleFunctor 𝒜 j).obj A)⟦(1 : ℤ)⟧) := by
  -- Transport the morphism space to the corresponding `Ext` group, then use the vanishing
  -- hypothesis in degree `i - j + 1`.
  have hnonneg : 0 ≤ i - j + 1 := by
    omega
  have htwo : 2 ≤ Int.toNat (i - j + 1) := by
    have htwo' : 2 ≤ i - j + 1 := by
      omega
    simpa using Int.toNat_le_toNat htwo'
  let e := hom_singleFunctor_shift_equiv_ext (𝒜 := 𝒜) B A i j hji
  have hsub : Subsingleton (Ext B A (Int.toNat (i - j + 1))) :=
    hBA (Int.toNat (i - j + 1)) htwo
  refine ⟨fun f g ↦ ?_⟩
  apply e.injective
  exact hsub.elim _ _

/-- Helper for Lemma 13.27.9: evaluating the singleton interval family at its unique index gives
back the degree-`a` shifted cohomology object. -/
lemma shiftedCohomologyOn_singleton_eval
    (K : DerivedCategory 𝒜) (a : ℤ) :
    shiftedCohomologyOn 𝒜 K a a ((intervalSingletonEquiv a) PUnit.unit) =
      shiftedCohomology 𝒜 K a :=
  rfl

/-- Helper for Lemma 13.27.9: the singleton interval biproduct is the single shifted cohomology
object. -/
noncomputable def biproduct_shiftedCohomologyOn_singleton_iso
    (K : DerivedCategory 𝒜) (a : ℤ) :
    shiftedCohomology 𝒜 K a ≅ ⨁ shiftedCohomologyOn 𝒜 K a a :=
  let e : PUnit.{1} ≃ Set.Icc a a := intervalSingletonEquiv a
  let F : PUnit.{1} → DerivedCategory 𝒜 := shiftedCohomologyOn 𝒜 K a a ∘ e
  let eUnique :
      ⨁ F ≅ F PUnit.unit :=
    biproductUniqueIso F
  let eReindex :
      ⨁ F ≅
        ⨁ shiftedCohomologyOn 𝒜 K a a :=
    biproduct.reindex e (shiftedCohomologyOn 𝒜 K a a)
  -- Reindex `[a, a]` by its unique element and identify the resulting one-term biproduct.
  (eqToIso (shiftedCohomologyOn_singleton_eval (𝒜 := 𝒜) K a)).symm ≪≫ eUnique.symm ≪≫ eReindex

/-- Helper for Lemma 13.27.9: the `WalkingPair`-sigma family packages a finite family together
with one extra summand. -/
private noncomputable abbrev walkingPairSigmaFamily {β : Type*}
    (F : β → DerivedCategory 𝒜) (X : DerivedCategory 𝒜) :
    (Σ s : WalkingPair, WalkingPair.casesOn s β PUnit) → DerivedCategory 𝒜 :=
  fun s ↦ Sigma.casesOn s (fun t u => WalkingPair.casesOn t F (fun _ => X) u)

/-- Helper for Lemma 13.27.9: the `WalkingPair`-sigma index set of a finite family is finite. -/
private instance finite_walkingPairSigmaIndex {β : Type*} [Finite β] :
    Finite (Σ s : WalkingPair, WalkingPair.casesOn s β PUnit) := by
  classical
  let e :
      (Σ s : WalkingPair, WalkingPair.casesOn s β PUnit) ≃ β ⊕ PUnit :=
    { toFun := fun s ↦
        match s with
        | ⟨WalkingPair.left, b⟩ => Sum.inl b
        | ⟨WalkingPair.right, u⟩ => Sum.inr u
      invFun := fun s ↦
        match s with
        | Sum.inl b => ⟨WalkingPair.left, b⟩
        | Sum.inr u => ⟨WalkingPair.right, u⟩
      left_inv := by
        intro s
        rcases s with ⟨s, u⟩
        cases s <;> rfl
      right_inv := by
        intro s
        cases s <;> rfl }
  exact Finite.of_equiv (β ⊕ PUnit) e.symm

/-- Helper for Lemma 13.27.9: the `WalkingPair`-sigma index set of a finite family is fintype. -/
private noncomputable instance fintype_walkingPairSigmaIndex {β : Type*} [Finite β] :
    Fintype (Σ s : WalkingPair, WalkingPair.casesOn s β PUnit) :=
  Fintype.ofFinite _

/-- Helper for Lemma 13.27.9: the binary biproduct projection family onto the packaged
`WalkingPair`-sigma summands. -/
private noncomputable abbrev walkingPairSigmaProjection {β : Type*}
    (F : β → DerivedCategory 𝒜) [HasBiproduct F] (X : DerivedCategory 𝒜) :
    (s : Σ t : WalkingPair, WalkingPair.casesOn t β PUnit) →
      ((⨁ F) ⊞ X ⟶ walkingPairSigmaFamily (𝒜 := 𝒜) F X s)
  | ⟨WalkingPair.left, b⟩ => biprod.fst ≫ biproduct.π F b
  | ⟨WalkingPair.right, _⟩ => biprod.snd

/-- Helper for Lemma 13.27.9: the universal map into the binary packaging is obtained by first
lifting the left branch to the finite biproduct and then pairing with the right branch. -/
private noncomputable abbrev walkingPairSigmaLift {β : Type*}
    (F : β → DerivedCategory 𝒜) [HasBiproduct F] (X : DerivedCategory 𝒜)
    {s : Fan (walkingPairSigmaFamily (𝒜 := 𝒜) F X)} :
    s.pt ⟶ (⨁ F) ⊞ X :=
  biprod.lift
    (biproduct.lift fun b ↦ s.proj ⟨WalkingPair.left, b⟩)
    (s.proj ⟨WalkingPair.right, PUnit.unit⟩)

/-- Helper for Lemma 13.27.9: the canonical lift into the binary package has the expected
component formulas. -/
private theorem walkingPairSigmaFan_fac {β : Type*} [Finite β]
    (F : β → DerivedCategory 𝒜) (X : DerivedCategory 𝒜)
    (s : Fan (walkingPairSigmaFamily (𝒜 := 𝒜) F X))
    (j : Σ t : WalkingPair, WalkingPair.casesOn t β PUnit) :
    walkingPairSigmaLift (𝒜 := 𝒜) F X ≫ walkingPairSigmaProjection (𝒜 := 𝒜) F X j =
      s.proj j := by
  rcases j with ⟨j, u⟩
  cases j
  · simp [walkingPairSigmaLift]
  · cases u
    simp [walkingPairSigmaLift]

/-- Helper for Lemma 13.27.9: a morphism into the binary package is determined by its components
on the left finite biproduct and the extra right summand. -/
private theorem walkingPairSigmaFan_uniq {β : Type*} [Finite β]
    (F : β → DerivedCategory 𝒜) (X : DerivedCategory 𝒜)
    (s : Fan (walkingPairSigmaFamily (𝒜 := 𝒜) F X))
    (m : s.pt ⟶ (⨁ F) ⊞ X)
    (hm :
      ∀ j : Σ t : WalkingPair, WalkingPair.casesOn t β PUnit,
        m ≫ walkingPairSigmaProjection (𝒜 := 𝒜) F X j = s.proj j) :
    m = walkingPairSigmaLift (𝒜 := 𝒜) F X := by
  -- Compare the two candidate morphisms by their left finite-biproduct and right projections.
  apply biprod.hom_ext
  · apply biproduct.hom_ext
    intro b
    simpa [walkingPairSigmaLift] using hm ⟨WalkingPair.left, b⟩
  · simpa [walkingPairSigmaLift] using hm ⟨WalkingPair.right, PUnit.unit⟩

/-- Helper for Lemma 13.27.9: the binary biproduct of a finite family with one extra summand is
the limit cone for the corresponding `WalkingPair`-sigma family. -/
private noncomputable def isLimit_walkingPairSigmaFan {β : Type*} [Finite β]
    (F : β → DerivedCategory 𝒜) (X : DerivedCategory 𝒜) :
    IsLimit
      (Fan.mk ((⨁ F) ⊞ X)
        (walkingPairSigmaProjection (𝒜 := 𝒜) F X)) :=
  mkFanLimit _
    (fun s ↦ walkingPairSigmaLift (𝒜 := 𝒜) F X (s := s))
    (walkingPairSigmaFan_fac (𝒜 := 𝒜) F X)
    (walkingPairSigmaFan_uniq (𝒜 := 𝒜) F X)

/-- Helper for Lemma 13.27.9: the binary biproduct of a finite family with one extra summand is
canonically the finite biproduct over the associated `WalkingPair`-sigma family. -/
noncomputable def biprod_iso_biproduct_walkingPair_sigma {β : Type*} [Finite β]
    (F : β → DerivedCategory 𝒜) (X : DerivedCategory 𝒜) :
    ((⨁ F) ⊞ X) ≅ ⨁ walkingPairSigmaFamily (𝒜 := 𝒜) F X :=
  (biproduct.uniqueUpToIso
      (walkingPairSigmaFamily (𝒜 := 𝒜) F X)
      (biconeIsBilimitOfLimitConeOfIsLimit
        (f := walkingPairSigmaFamily (𝒜 := 𝒜) F X)
        (t := Fan.mk ((⨁ F) ⊞ X) (walkingPairSigmaProjection (𝒜 := 𝒜) F X))
        (isLimit_walkingPairSigmaFan (𝒜 := 𝒜) F X)))

/-- Helper for Lemma 13.27.9: on the left branch, `intervalSuccEquiv` keeps the underlying
interval point. -/
private theorem intervalSuccEquiv_apply_left_val
    (a : ℤ) (n : ℕ) (u : Set.Icc a (a + n)) :
    ((intervalSuccEquiv a n ⟨WalkingPair.left, u⟩ :
        Set.Icc a (a + (n + 1 : ℕ))).1) = u.1 := by
  unfold intervalSuccEquiv
  rfl

/-- Helper for Lemma 13.27.9: on the right branch, `intervalSuccEquiv` hits the new top index. -/
private theorem intervalSuccEquiv_apply_right_val
    (a : ℤ) (n : ℕ) :
    ((intervalSuccEquiv a n ⟨WalkingPair.right, PUnit.unit⟩ :
        Set.Icc a (a + (n + 1 : ℕ))).1) = a + n + 1 := by
  have h :
      ((intervalSuccEquiv a n ⟨WalkingPair.right, PUnit.unit⟩ :
          Set.Icc a (a + (n + 1 : ℕ))).1) = a + (n + 1 : ℕ) := by
    unfold intervalSuccEquiv
    rfl
  simpa [add_assoc] using h

/-- Helper for Lemma 13.27.9: reindexing the successor interval identifies the `WalkingPair`-sigma
packaging with the shifted cohomology family on `[a, a + n + 1]`. -/
private theorem walkingPairSigmaFamily_eq_shiftedCohomologyOn_comp_intervalSuccEquiv
    (K : DerivedCategory 𝒜) (a : ℤ) (n : ℕ) :
    walkingPairSigmaFamily (𝒜 := 𝒜)
        (shiftedCohomologyOn 𝒜 K a (a + n))
        (shiftedCohomology 𝒜 K (a + n + 1)) =
      shiftedCohomologyOn 𝒜 K a (a + (n + 1 : ℕ)) ∘ intervalSuccEquiv a n := by
  -- Both families read off the same cohomology object at each sigma index: the left branch keeps
  -- the old interval index and the right branch is the new top degree.
  funext s
  rcases s with ⟨s, u⟩
  cases s
  · -- The successor equivalence preserves the integer value of every old interval point.
    change shiftedCohomology 𝒜 K u.1 =
      shiftedCohomology 𝒜 K ((intervalSuccEquiv a n ⟨WalkingPair.left, u⟩).1)
    rw [intervalSuccEquiv_apply_left_val]
  · cases u
    -- The adjoined right branch is exactly the new top degree.
    change shiftedCohomology 𝒜 K (a + n + 1) =
      shiftedCohomology 𝒜 K ((intervalSuccEquiv a n ⟨WalkingPair.right, PUnit.unit⟩).1)
    rw [intervalSuccEquiv_apply_right_val]

/-- Helper for Lemma 13.27.9: adjoining the top cohomology summand identifies the binary
biproduct with the interval-indexed biproduct one step higher. -/
noncomputable def biproduct_shiftedCohomologyOn_succ_iso
    (K : DerivedCategory 𝒜) (a : ℤ) (n : ℕ) :
    (⨁ shiftedCohomologyOn 𝒜 K a (a + n)) ⊞ shiftedCohomology 𝒜 K (a + n + 1) ≅
      ⨁ shiftedCohomologyOn 𝒜 K a (a + (n + 1 : ℕ)) := by
  -- Route correction: package the binary biproduct through the owner-level `WalkingPair`-sigma
  -- family first, and only then reindex along the interval successor equivalence.
  let eFlatten :
      (⨁ shiftedCohomologyOn 𝒜 K a (a + n)) ⊞ shiftedCohomology 𝒜 K (a + n + 1) ≅
        ⨁ walkingPairSigmaFamily (𝒜 := 𝒜)
          (shiftedCohomologyOn 𝒜 K a (a + n))
          (shiftedCohomology 𝒜 K (a + n + 1)) :=
    biprod_iso_biproduct_walkingPair_sigma (𝒜 := 𝒜)
      (shiftedCohomologyOn 𝒜 K a (a + n))
      (shiftedCohomology 𝒜 K (a + n + 1))
  let eFamily :
      (⨁ walkingPairSigmaFamily (𝒜 := 𝒜)
          (shiftedCohomologyOn 𝒜 K a (a + n))
          (shiftedCohomology 𝒜 K (a + n + 1))) ≅
        ⨁ (shiftedCohomologyOn 𝒜 K a (a + (n + 1 : ℕ)) ∘ intervalSuccEquiv a n) :=
    eqToIso
      (by
        congr 1
        exact walkingPairSigmaFamily_eq_shiftedCohomologyOn_comp_intervalSuccEquiv
          (𝒜 := 𝒜) K a n)
  -- The final step is the standard reindexing isomorphism for finite biproducts.
  exact
    eFlatten ≪≫ eFamily ≪≫
      biproduct.reindex (intervalSuccEquiv a n)
        (shiftedCohomologyOn 𝒜 K a (a + (n + 1 : ℕ)))

/-- Helper for Lemma 13.27.9: the biproduct indexed by the empty type is isomorphic to a zero
object of the derived category. -/
private theorem exists_isZero_iso_biproduct_empty
    (F : Empty → DerivedCategory 𝒜) :
    ∃ Z : DerivedCategory 𝒜, IsZero Z ∧ Nonempty (Z ≅ ⨁ F) := by
  let Z : DerivedCategory 𝒜 := Classical.choose (HasZeroObject.zero (C := DerivedCategory 𝒜))
  let hZ : IsZero Z := Classical.choose_spec (HasZeroObject.zero (C := DerivedCategory 𝒜))
  let t : Fan F := Fan.mk Z (fun e ↦ Empty.elim e)
  let ht : IsLimit t :=
    mkFanLimit t
      (fun s ↦ 0)
      (by
        intro s j
        exact Empty.elim j)
      (by
        intro s m hm
        exact hZ.eq_of_tgt m 0)
  exact ⟨Z, hZ, ⟨biproduct.uniqueUpToIso F
    (biconeIsBilimitOfLimitConeOfIsLimit (f := F) (t := t) ht)⟩⟩

/-- Helper for Lemma 13.27.9: the upper truncations split as the interval biproducts of the
cohomology pieces. -/
theorem truncLT_iso_biproduct_shiftedCohomologyOn
    (K : DerivedCategory 𝒜) (a : ℤ) (hGE : K.IsGE a)
    (hExt : ∀ (n : ℕ) (_ : 2 ≤ n) (i j : ℤ) (_ : j < i),
      Subsingleton (Ext ((H^i).obj K) ((H^j).obj K) n)) :
    ∀ n : ℕ,
      Nonempty (((t.truncLT (a + n + 1)).obj K) ≅ ⨁ shiftedCohomologyOn 𝒜 K a (a + n)) := by
  intro n
  induction n with
  | zero =>
      have hGE' : ((t.truncLT (a + 1)).obj K).IsGE a := by
        infer_instance
      have hLE' : ((t.truncLT (a + 1)).obj K).IsLE a := by
        simpa using (inferInstance : ((t.truncLT (a + 1)).obj K).IsLE ((a + 1) - 1))
      have eSingle :
          ((t.truncLT (a + (0 : ℕ) + 1)).obj K) ≅ shiftedCohomology 𝒜 K a := by
        simpa using
        singleFunctorIsoOfIsGEOfIsLE (𝒜 := 𝒜) ((t.truncLT (a + 1)).obj K) a ≪≫
          shiftedCohomology_truncLT_iso (𝒜 := 𝒜) K (a + 1) a (by omega)
      have eSingleton :
          shiftedCohomology 𝒜 K a ≅
            ⨁ shiftedCohomologyOn 𝒜 K a (a + (0 : ℕ)) := by
        let eIndex :
            Set.Icc a a ≃ Set.Icc a (a + (0 : ℕ)) :=
          { toFun := fun i ↦ ⟨i.1, i.2.1, by simpa using i.2.2⟩
            invFun := fun i ↦ ⟨i.1, i.2.1, by simpa using i.2.2⟩
            left_inv := by
              intro i
              ext
              rfl
            right_inv := by
              intro i
              ext
              rfl }
        have hFamily :
            shiftedCohomologyOn 𝒜 K a (a + (0 : ℕ)) ∘ eIndex =
              shiftedCohomologyOn 𝒜 K a a := by
          funext i
          simp [shiftedCohomologyOn, eIndex]
        let eLeft :
            (⨁ shiftedCohomologyOn 𝒜 K a a) ≅
              ⨁ (shiftedCohomologyOn 𝒜 K a (a + (0 : ℕ)) ∘ eIndex) :=
          eqToIso (congrArg (fun F => ⨁ F) hFamily.symm)
        let eReindex :
            (⨁ shiftedCohomologyOn 𝒜 K a a) ≅
              ⨁ shiftedCohomologyOn 𝒜 K a (a + (0 : ℕ)) := by
          exact eLeft ≪≫ biproduct.reindex eIndex (shiftedCohomologyOn 𝒜 K a (a + (0 : ℕ)))
        exact biproduct_shiftedCohomologyOn_singleton_iso (𝒜 := 𝒜) K a ≪≫ eReindex
      -- In the base case only the degree-`a` cohomology survives, so the truncation is the
      -- one-term biproduct indexed by the singleton interval `[a, a]`.
      exact ⟨eSingle ≪≫ eSingleton⟩
  | succ n ih =>
      rcases ih with ⟨eIH⟩
      let T := truncLE_step_homologyTriangle (𝒜 := 𝒜) K (a + n)
      have hT : T ∈ distTriang (DerivedCategory 𝒜) := by
        simpa [T] using truncLE_step_homology_triangle (𝒜 := 𝒜) K (a + n)
      let eShift :
          ((⨁ shiftedCohomologyOn 𝒜 K a (a + n))⟦(1 : ℤ)⟧) ≅
            ⨁ fun i : Set.Icc a (a + n) ↦ (shiftedCohomologyOn 𝒜 K a (a + n) i)⟦(1 : ℤ)⟧ :=
        Functor.mapBiproduct (shiftFunctor (DerivedCategory 𝒜) (1 : ℤ))
          (shiftedCohomologyOn 𝒜 K a (a + n))
      have hzero_transport :
          T.mor₃ ≫ (shiftFunctor (DerivedCategory 𝒜) (1 : ℤ)).map eIH.hom ≫ eShift.hom = 0 := by
        -- Each shifted projection lands in a Hom-space identified with a higher `Ext` group.
        apply biproduct.hom_ext
        intro i
        have hi : i.1 < a + n + 1 := by
          exact lt_of_le_of_lt i.2.2 (by omega)
        have hsub :
            Subsingleton
              (shiftedCohomology 𝒜 K (a + n + 1) ⟶
                (shiftedCohomologyOn 𝒜 K a (a + n) i)⟦(1 : ℤ)⟧) :=
          subsingleton_hom_singleFunctor_to_shifted_singleFunctor_of_ext_vanishing
            (𝒜 := 𝒜) ((H (a + n + 1)).obj K) ((H i.1).obj K) (a + n + 1) i.1 hi
            (fun m hm ↦ hExt m hm (a + n + 1) i.1 hi)
        -- The projection formula for `Functor.mapBiproduct` reduces the component to the owner
        -- single-to-shifted-single Hom-space controlled by `hExt`.
        have hcomp :
            T.mor₃ ≫ (shiftFunctor (DerivedCategory 𝒜) (1 : ℤ)).map eIH.hom ≫ eShift.hom ≫
                biproduct.π
                  (fun i : Set.Icc a (a + n) ↦
                    (shiftedCohomologyOn 𝒜 K a (a + n) i)⟦(1 : ℤ)⟧) i =
              0 := by
          simpa [eShift, Category.assoc] using
            (hsub.elim
              (T.mor₃ ≫ (shiftFunctor (DerivedCategory 𝒜) (1 : ℤ)).map eIH.hom ≫ eShift.hom ≫
                biproduct.π
                  (fun i : Set.Icc a (a + n) ↦
                    (shiftedCohomologyOn 𝒜 K a (a + n) i)⟦(1 : ℤ)⟧) i)
              0)
        simpa [Category.assoc] using hcomp
      have hzero : T.mor₃ = 0 := by
        simpa using hzero_transport
      rcases truncLE_step_split_iso (𝒜 := 𝒜) K (a + n) hzero with ⟨eStep⟩
      have eSucc :
          ((t.truncLT (a + n.succ + 1)).obj K) ≅
            ⨁ shiftedCohomologyOn 𝒜 K a (a + n.succ) := by
        -- Route correction: specialize the split-triangle theorem first, then compose with the
        -- induction isomorphism and the successor biproduct reindexing.
        simpa [Nat.succ_eq_add_one, add_assoc] using
          (eStep ≪≫ biprod.mapIso eIH (Iso.refl _) ≪≫
            biproduct_shiftedCohomologyOn_succ_iso (𝒜 := 𝒜) K a n)
      exact ⟨eSucc⟩

-- Proof sketch: choose bounds `a ≤ i ≤ b` for the cohomological amplitude of `K` and induct on
-- `b - a`; use the truncation triangle for the top degree, show that its connecting morphism
-- vanishes because it lies in a higher `Ext` group from `H^b(K)` to the lower cohomologies,
-- split the triangle, and iterate.
/-- Once explicit cohomological bounds are fixed, the shifted cohomology pieces of `K` split off
as a finite biproduct over that interval. -/
theorem isomorphic_to_biproduct_shiftedCohomology_of_ext_vanishing_of_isGE_isLE
    (K : DerivedCategory 𝒜) (a b : ℤ) (hGE : K.IsGE a) (hLE : K.IsLE b)
    (hExt : ∀ (n : ℕ) (_ : 2 ≤ n) (i j : ℤ) (_ : j < i),
      Subsingleton (Ext ((H^i).obj K) ((H^j).obj K) n)) :
    Nonempty (K ≅ ⨁ shiftedCohomologyOn 𝒜 K a b) := by
  by_cases hba : b < a
  · let eIndex : Set.Icc a b ≃ Empty := intervalEmptyEquiv a b hba
    let F : Empty → DerivedCategory 𝒜 := shiftedCohomologyOn 𝒜 K a b ∘ eIndex.symm
    rcases exists_isZero_iso_biproduct_empty (𝒜 := 𝒜) F with ⟨Z, hZ, ⟨eZeroBip⟩⟩
    let eZeroK : K ≅ Z := (t.isZero K b a hba).iso hZ
    -- If the support interval is empty, both the object and the indexed biproduct are zero.
    exact
      ⟨eZeroK ≪≫ eZeroBip ≪≫
        biproduct.reindex eIndex.symm (shiftedCohomologyOn 𝒜 K a b)⟩
  · have hab : a ≤ b := by
      omega
    let n : ℕ := Int.toNat (b - a)
    have hb : b = a + n := by
      dsimp [n]
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
      omega
    have hbn : a + n = b := by
      omega
    let eTrunc :
        (t.truncLT (b + 1)).obj K ≅ K := by
      exact @asIso _ _ _ _
        ((t.truncLTι (b + 1)).app K)
        ((t.isLE_iff_isIso_truncLTι_app b (b + 1) (by omega) K).1 hLE)
    rcases truncLT_iso_biproduct_shiftedCohomologyOn
        (𝒜 := 𝒜) K a hGE hExt n with ⟨eSplit⟩
    have eSplit' : (t.truncLT (b + 1)).obj K ≅ ⨁ shiftedCohomologyOn 𝒜 K a b := by
      let eIndex :
          Set.Icc a (a + n) ≃ Set.Icc a b :=
        { toFun := fun i ↦ ⟨i.1, i.2.1, by simpa [hbn] using i.2.2⟩
          invFun := fun i ↦ ⟨i.1, i.2.1, by simpa [hbn] using i.2.2⟩
          left_inv := by
            intro i
            ext
            rfl
          right_inv := by
            intro i
            ext
            rfl }
      have hFamily :
          shiftedCohomologyOn 𝒜 K a b ∘ eIndex =
            shiftedCohomologyOn 𝒜 K a (a + n) := by
        funext i
        rfl
      have eSplit₀ : (t.truncLT (b + 1)).obj K ≅ ⨁ shiftedCohomologyOn 𝒜 K a (a + n) := by
        simpa [hbn, add_assoc] using eSplit
      let eLeft :
          (⨁ shiftedCohomologyOn 𝒜 K a (a + n)) ≅
            ⨁ (shiftedCohomologyOn 𝒜 K a b ∘ eIndex) :=
        eqToIso (congrArg (fun F => ⨁ F) hFamily.symm)
      let eReindex :
          (⨁ shiftedCohomologyOn 𝒜 K a (a + n)) ≅
            ⨁ shiftedCohomologyOn 𝒜 K a b := by
        exact eLeft ≪≫ biproduct.reindex eIndex (shiftedCohomologyOn 𝒜 K a b)
      exact eSplit₀ ≪≫ eReindex
    -- Replace the final upper truncation by `K` using the bounded-above hypothesis.
    exact ⟨eTrunc.symm ≪≫ eSplit'⟩

/-- Lemma 13.27.9: if all higher extension groups in `𝒜` from higher cohomology to lower
cohomology vanish in degrees `n ≥ 2`, then any bounded derived object is isomorphic to the
biproduct of its shifted cohomology objects over some interval containing its cohomological
support. -/
theorem isomorphic_to_biproduct_shiftedCohomology_of_ext_vanishing
    (K : Dᵇ(𝒜))
    (hExt : ∀ (n : ℕ) (_ : 2 ≤ n) (i j : ℤ) (_ : j < i),
      Subsingleton (Ext ((H^i).obj K.obj) ((H^j).obj K.obj) n)) :
    ∃ a b : ℤ, Nonempty (K.obj ≅ ⨁ shiftedCohomologyOn 𝒜 K.obj a b) := by
  rcases (derivedCategory_t_bounded_iff K.obj).1 K.property with
    ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  have hGE : K.obj.IsGE a := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact ha i hi
  have hLE : K.obj.IsLE b := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact hb i hi
  exact ⟨a, b,
    isomorphic_to_biproduct_shiftedCohomology_of_ext_vanishing_of_isGE_isLE
      𝒜 K.obj a b hGE hLE hExt⟩

end
