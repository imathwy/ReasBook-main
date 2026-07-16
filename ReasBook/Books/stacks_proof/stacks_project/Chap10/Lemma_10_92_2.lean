import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_84_1
import stacks_proof.stacks_project.Chap10.Lemma_10_84_3
import stacks_proof.stacks_project.Chap10.Lemma_10_11_1
import stacks_proof.stacks_project.Chap10.Definition_10_88_1
import stacks_proof.stacks_project.Chap10.Definition_10_88_7
import stacks_proof.stacks_project.Chap10.Lemma_10_86_3
import stacks_proof.stacks_project.Chap10.Lemma_10_92_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe u v w

namespace Module

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {P : Type w} [AddCommGroup P] [Module R P] [Module.Finite R P]

/-- Helper for Chap10 Lemma 10 92 2: product-valued Hom Mittag-Leffler stabilization gives a
transition map that factors through every later transition. -/
private lemma productHomMittagLeffler_gives_stageFactorization
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ ModuleCat.{v} R)
    (hML : (colimitPresentationHomInverseSystem F
      (ModuleCat.of.{v} R ((s : I) → (F.obj s : Type v)))).IsMittagLeffler) :
    ∀ i : I, ∃ (j : I) (hij : i ≤ j),
      ∀ (k : I) (hik : i ≤ k), ∃ h : F.obj k ⟶ F.obj j,
        F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h := by
  classical
  intro i
  -- Evaluate Mittag-Leffler stabilization at the product target and the chosen stage `i`.
  let G := colimitPresentationHomInverseSystem F
    (ModuleCat.of.{v} R ((s : I) → (F.obj s : Type v)))
  obtain ⟨jop, f, hf⟩ := (Functor.isMittagLeffler_iff_subset_range_comp G).mp hML (op i)
  let j := unop jop
  have hij : i ≤ j := leOfHom f.unop
  -- Insert the `j`-th stage into the product and project back to isolate a factorization of the
  -- original transition map.
  let insj : F.obj j ⟶ ModuleCat.of.{v} R ((s : I) → (F.obj s : Type v)) :=
    ModuleCat.ofHom (LinearMap.single R (fun s : I ↦ (F.obj s : Type v)) j)
  let projj : ModuleCat.of.{v} R ((s : I) → (F.obj s : Type v)) ⟶ F.obj j :=
    ModuleCat.ofHom (LinearMap.proj j)
  have hins_proj : insj ≫ projj = 𝟙 (F.obj j) := by
    apply ModuleCat.hom_ext
    ext x
    simp [insj, projj]
  refine ⟨j, hij, ?_⟩
  intro k hik
  -- Move both `j` and the requested later stage `k` to a common upper bound, where the stabilized
  -- product-valued range comparison applies.
  obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k
  have hil : i ≤ l := hij.trans hjl
  have hf_unop : f.unop = homOfLE hij := Subsingleton.elim _ _
  have hsubset :
      Set.range (fun g : F.obj j ⟶ ModuleCat.of.{v} R ((s : I) → (F.obj s : Type v)) ↦
        F.map (homOfLE hij) ≫ g) ⊆
        Set.range (fun g : F.obj l ⟶ ModuleCat.of.{v} R ((s : I) → (F.obj s : Type v)) ↦
          F.map (homOfLE hil) ≫ g) := by
    simpa [G, hf_unop] using hf ((homOfLE hjl).op)
  have hmem :
      F.map (homOfLE hij) ≫ insj ∈
        Set.range (fun g : F.obj j ⟶ ModuleCat.of.{v} R ((s : I) → (F.obj s : Type v)) ↦
          F.map (homOfLE hij) ≫ g) := by
    exact ⟨insj, rfl⟩
  obtain ⟨gl, hgl⟩ := hsubset hmem
  refine ⟨F.map (homOfLE hkl) ≫ gl ≫ projj, ?_⟩
  -- Project the stabilized product-valued factorization to the `j`-th coordinate.
  calc
    F.map (homOfLE hij)
        = ((F.map (homOfLE hij) ≫ insj) ≫ projj) := by simp [Category.assoc, hins_proj]
    _ = ((F.map (homOfLE hil) ≫ gl) ≫ projj) := by
          simpa [Category.assoc] using congrArg (fun t ↦ t ≫ projj) hgl.symm
    _ = ((F.map (homOfLE hik) ≫ F.map (homOfLE hkl)) ≫ gl) ≫ projj := by
          have hcomp : homOfLE hil = homOfLE hik ≫ homOfLE hkl := Subsingleton.elim _ _
          rw [← Functor.map_comp, hcomp, Category.assoc]
    _ = F.map (homOfLE hik) ≫ (F.map (homOfLE hkl) ≫ gl ≫ projj) := by
          simp [Category.assoc]

/-- Helper for Chap10 Lemma 10 92 2: finite linear combinations are additive in the coefficient
vector. -/
private lemma finStageLinearCombination_map_add
    {N : Type v} [AddCommGroup N] [Module R N] {n : ℕ} (y : Fin n → N)
    (z z' : Fin n → R) :
    (∑ a, (z + z') a • y a) = (∑ a, z a • y a) + (∑ a, z' a • y a) := by
  -- Expand pointwise addition in the finite free module and distribute the finite sum.
  simp [Finset.sum_add_distrib, add_smul]

/-- Helper for Chap10 Lemma 10 92 2: finite linear combinations are homogeneous in the coefficient
vector. -/
private lemma finStageLinearCombination_map_smul
    {N : Type v} [AddCommGroup N] [Module R N] {n : ℕ} (y : Fin n → N)
    (r : R) (z : Fin n → R) :
    (∑ a, (r • z) a • y a) = r • (∑ a, z a • y a) := by
  -- Associativity of scalar multiplication pulls the common scalar through the finite sum.
  simp [Finset.smul_sum, mul_smul]

/-- Helper for Chap10 Lemma 10 92 2: the linear map from a finite free module determined by
chosen images of the standard basis. -/
private def finStageLinearCombination
    {N : Type v} [AddCommGroup N] [Module R N] {n : ℕ} (y : Fin n → N) :
    (Fin n → R) →ₗ[R] N where
  toFun z := ∑ a, z a • y a
  map_add' := finStageLinearCombination_map_add y
  map_smul' := finStageLinearCombination_map_smul y

/-- Helper for Chap10 Lemma 10 92 2: the finite linear-combination map sends each standard basis
vector to its prescribed image. -/
private lemma finStageLinearCombination_basis
    {N : Type v} [AddCommGroup N] [Module R N] {n : ℕ} (y : Fin n → N) (a : Fin n) :
    finStageLinearCombination (R := R) y ((Pi.basisFun R (Fin n)) a) = y a := by
  -- On a standard basis vector all coefficients vanish except the selected coordinate.
  simp [finStageLinearCombination, Pi.basisFun_apply]

/-- Helper for Chap10 Lemma 10 92 2: a map from a finite free module to a directed colimit of
modules is represented at one stage. -/
private lemma linearMap_from_fin_factor_through_directed_colimit_stage
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ ModuleCat.{v} R)
    (n : ℕ) (f : (Fin n → R) →ₗ[R] (colimit F : ModuleCat.{v} R)) :
    ∃ (i : I) (g : (Fin n → R) →ₗ[R] F.obj i), (colimit.ι F i).hom.comp g = f := by
  classical
  -- Forgetting to types preserves this filtered colimit, so every basis image has a stage
  -- representative.
  letI : PreservesColimit F (forget (ModuleCat.{v} R)) :=
    modulecat_forget_preserves_colimit_filtered (R := R) F
  let hc :
      IsColimit ((forget (ModuleCat.{v} R)).mapCocone (colimit.cocone F)) :=
    isColimitOfPreserves (forget (ModuleCat.{v} R)) (colimit.isColimit F)
  choose j x hx using fun a : Fin n =>
    Types.jointly_surjective_of_isColimit hc (f ((Pi.basisFun R (Fin n)) a))
  -- Directedness synchronizes the finitely many representatives into one common stage.
  obtain ⟨k, ⟨u⟩⟩ : ∃ k : I, Nonempty (∀ a : Fin n, j a ⟶ k) := by
    have : ∃ k : I, ∀ a : Fin n, Nonempty (j a ⟶ k) := by
      simpa using IsFiltered.sup_objs_exists (Finset.univ.image j)
    simpa [← exists_true_iff_nonempty, Classical.skolem, -exists_const_iff] using this
  let g : (Fin n → R) →ₗ[R] F.obj k :=
    finStageLinearCombination (R := R) (fun a ↦ (F.map (u a)) (x a))
  refine ⟨k, g, ?_⟩
  -- The finite-free map is determined by the standard basis, and naturality transports each
  -- chosen representative to the common stage.
  apply (Pi.basisFun R (Fin n)).ext
  intro a
  have htransport :
      (colimit.ι F k).hom ((F.map (u a)) (x a)) =
        (colimit.ι F (j a)).hom (x a) := by
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (colimit.w F (u a))) (x a)
  calc
    ((colimit.ι F k).hom.comp g) ((Pi.basisFun R (Fin n)) a)
        = (colimit.ι F k).hom ((F.map (u a)) (x a)) := by
            have hg_basis :
                g ((Pi.basisFun R (Fin n)) a) = (F.map (u a)) (x a) := by
              simpa [g] using
                (finStageLinearCombination_basis (R := R)
                  (fun b : Fin n ↦ (F.map (u b)) (x b)) a)
            exact congrArg (colimit.ι F k).hom hg_basis
    _ = (colimit.ι F (j a)).hom (x a) := htransport
    _ = f ((Pi.basisFun R (Fin n)) a) := hx a

/-- Helper for Chap10 Lemma 10 92 2: a countable set of indices has a countable directed
superset that contains a prescribed index and is closed under a chosen tail operation. -/
private lemma exists_countable_directed_tailClosed_superset_containing
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (A : Set I) (hA : A.Countable) (next : I → I) (i : I) :
    ∃ S : Set I, A ⊆ S ∧ i ∈ S ∧ Countable S ∧ Nonempty S ∧ IsDirectedOrder S ∧
      ∀ j ∈ S, next j ∈ S := by
  classical
  let i0 : I := Classical.choice inferInstance
  let upper : I × I → I := fun p ↦ Classical.choose (exists_ge_ge p.1 p.2)
  have hupper_left : ∀ p : I × I, p.1 ≤ upper p :=
    fun p ↦ (Classical.choose_spec (exists_ge_ge p.1 p.2)).1
  have hupper_right : ∀ p : I × I, p.2 ≤ upper p :=
    fun p ↦ (Classical.choose_spec (exists_ge_ge p.1 p.2)).2
  let seed : Set I := insert i0 (insert i A)
  let C : ℕ → Set I :=
    Nat.rec seed (fun _ Cn ↦ (Cn ∪ next '' Cn) ∪ upper '' (Cn ×ˢ Cn))
  have hC_mono_step : ∀ n, C n ⊆ C (n + 1) := by
    intro n x hx
    -- The previous closure stage is included as the first summand of the next one.
    change x ∈ (C n ∪ next '' C n) ∪ upper '' (C n ×ˢ C n)
    exact Or.inl (Or.inl hx)
  have hC_mono : ∀ {m n : ℕ}, m ≤ n → C m ⊆ C n := by
    intro m n hmn
    induction hmn with
    | refl => intro x hx; exact hx
    | step hmn ih => exact fun x hx ↦ hC_mono_step _ (ih hx)
  have hC_count : ∀ n, (C n).Countable := by
    intro n
    induction n with
    | zero =>
        simpa [C, seed] using (hA.insert i).insert i0
    | succ n ih =>
        have hnext_count : (next '' C n).Countable := ih.image next
        have hupper_count : (upper '' (C n ×ˢ C n)).Countable := (ih.prod ih).image upper
        simpa [C] using (ih.union hnext_count).union hupper_count
  let S : Set I := ⋃ n, C n
  refine ⟨S, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    -- The original countable seed is placed in closure stage zero.
    exact Set.mem_iUnion.mpr ⟨0, by simpa [C, seed] using Or.inr (Or.inr hx)⟩
  · -- The prescribed fixed stage is also placed in closure stage zero.
    exact Set.mem_iUnion.mpr ⟨0, by simpa [C, seed] using Or.inr (Or.inl rfl)⟩
  · exact Set.countable_iUnion hC_count
  · refine ⟨⟨i0, ?_⟩⟩
    exact Set.mem_iUnion.mpr ⟨0, by simp [C, seed]⟩
  · constructor
    intro a b
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    rcases Set.mem_iUnion.mp ha with ⟨m, ham⟩
    rcases Set.mem_iUnion.mp hb with ⟨n, hbn⟩
    let N := max m n
    have haN : a ∈ C N := hC_mono (Nat.le_max_left m n) ham
    have hbN : b ∈ C N := hC_mono (Nat.le_max_right m n) hbn
    -- The binary upper-bound operation is added at the next closure stage.
    refine ⟨⟨upper (a, b), ?_⟩, hupper_left (a, b), hupper_right (a, b)⟩
    exact Set.mem_iUnion.mpr ⟨N + 1, by
      change upper (a, b) ∈ (C N ∪ next '' C N) ∪ upper '' (C N ×ˢ C N)
      exact Or.inr ⟨(a, b), ⟨haN, hbN⟩, rfl⟩⟩
  · intro j hj
    rcases Set.mem_iUnion.mp hj with ⟨n, hjn⟩
    -- The unary tail operation is added at the next closure stage.
    exact Set.mem_iUnion.mpr ⟨n + 1, by
      change next j ∈ (C n ∪ next '' C n) ∪ upper '' (C n ×ˢ C n)
      exact Or.inl (Or.inr ⟨j, hjn, rfl⟩)⟩

/-- Helper for Chap10 Lemma 10 92 2: every element of a filtered colimit of modules is represented
at some stage. -/
private lemma moduleCat_colimit_stage_representation
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ ModuleCat.{v} R) (x : ↑(colimit F)) :
    ∃ i : I, ∃ y : F.obj i, (colimit.ι F i).hom y = x := by
  -- Forgetting to types exposes the usual jointly-surjective concrete colimit cocone.
  letI : PreservesColimit F (forget (ModuleCat.{v} R)) :=
    modulecat_forget_preserves_colimit_filtered (R := R) F
  let hc : IsColimit ((forget (ModuleCat.{v} R)).mapCocone (colimit.cocone F)) :=
    isColimitOfPreserves (forget (ModuleCat.{v} R)) (colimit.isColimit F)
  simpa using Types.jointly_surjective_of_isColimit hc x

/-- Helper for Chap10 Lemma 10 92 2: a stage element that maps to zero in a filtered module
colimit becomes zero after passing to a later stage. -/
private lemma moduleCat_colimit_eq_zero_eventually
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ ModuleCat.{v} R) {i : I} (x : F.obj i)
    (hx : (colimit.ι F i).hom x = 0) :
    ∃ j : I, ∃ hij : i ≤ j, (F.map (homOfLE hij)).hom x = 0 := by
  -- The concrete filtered-colimit API turns equality to zero into eventual equality to zero.
  letI : PreservesColimit F (forget (ModuleCat.{v} R)) :=
    modulecat_forget_preserves_colimit_filtered (R := R) F
  obtain ⟨j, f, hf⟩ :=
    CategoryTheory.Limits.Concrete.colimit_rep_eq_zero
      (R := R) (F := F) i x hx
  refine ⟨j, leOfHom f, ?_⟩
  have hf_eq : f = homOfLE (leOfHom f) := Subsingleton.elim _ _
  simpa [hf_eq] using hf

/-- Helper for Chap10 Lemma 10 92 2: countable generation supplies a countable directed
tail-closed subsystem, containing a prescribed stage, whose stage images span the colimit. -/
private lemma exists_countable_tailClosed_stageSet_spanning_colimit_containing
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ ModuleCat.{v} R)
    (hcg : Module.CountablyGenerated R ↑(colimit F))
    (next : I → I) (i : I) :
    ∃ S : Set I, i ∈ S ∧ Countable S ∧ Nonempty S ∧ IsDirectedOrder S ∧
      (∀ j ∈ S, next j ∈ S) ∧
      Submodule.span R (⋃ j, ⋃ _ : j ∈ S, Set.range ((colimit.ι F j).hom)) =
        (⊤ : Submodule R ↑(colimit F)) := by
  classical
  -- Choose countably many colimit generators, then choose one stage representative for each.
  obtain ⟨T, hTcount, hTspan⟩ :=
    (Module.countablyGenerated_iff (R := R) (M := ↑(colimit F))).mp hcg
  letI : Countable T := hTcount.to_subtype
  choose stage elem helem using fun t : T =>
    moduleCat_colimit_stage_representation (R := R) F t.1
  let A : Set I := Set.range stage
  have hAcount : A.Countable := Set.countable_range stage
  obtain ⟨S, hAS, hiS, hScount, hSnonempty, hSdirected, hnextS⟩ :=
    exists_countable_directed_tailClosed_superset_containing
      (A := A) hAcount next i
  refine ⟨S, hiS, hScount, hSnonempty, hSdirected, hnextS, ?_⟩
  let U : Set ↑(colimit F) := ⋃ j, ⋃ _ : j ∈ S, Set.range ((colimit.ι F j).hom)
  have hT_subset : T ⊆ U := by
    intro x hx
    let t : T := ⟨x, hx⟩
    have hstageS : stage t ∈ S := hAS ⟨t, rfl⟩
    -- Each chosen generator lies in the selected union of stage images.
    refine Set.mem_iUnion.mpr ⟨stage t, ?_⟩
    refine Set.mem_iUnion.mpr ⟨hstageS, ?_⟩
    exact ⟨elem t, helem t⟩
  -- Since the selected stage images contain the original generators, their span is all of the
  -- colimit.
  have htop_le : (⊤ : Submodule R ↑(colimit F)) ≤ Submodule.span R U := by
    rw [← hTspan]
    exact Submodule.span_mono hT_subset
  exact le_antisymm le_top htop_le

/-- Helper for Chap10 Lemma 10 92 2: a tail-closed directed subset whose stage images span the
whole colimit has an isomorphic restricted colimit. -/
private lemma isIso_colimitPre_of_tailClosed_spanning
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ ModuleCat.{v} R)
    (S : Set I) [Countable S] [Nonempty S] [IsDirectedOrder S]
    (next : I → I) (hnext : ∀ i, i ≤ next i)
    (htail : ∀ i k (hik : i ≤ k), ∃ h : F.obj k ⟶ F.obj (next i),
      F.map (homOfLE (hnext i)) = F.map (homOfLE hik) ≫ h)
    (hnextS : ∀ i ∈ S, next i ∈ S)
    (hspan : Submodule.span R (⋃ i, ⋃ _ : i ∈ S, Set.range ((colimit.ι F i).hom)) =
      (⊤ : Submodule R ↑(colimit F))) :
    IsIso (colimit.pre F (OrderEmbedding.subtype S).toOrderHom.toFunctor) := by
  classical
  let E := (OrderEmbedding.subtype S).toOrderHom.toFunctor
  let H : S ⥤ ModuleCat.{v} R := E ⋙ F
  let g : colimit H ⟶ colimit F := colimit.pre F E
  -- It is enough to prove the concrete comparison map is bijective.
  refine (ConcreteCategory.isIso_iff_bijective g).2 ⟨?_, ?_⟩
  · intro x y hxy
    -- Represent the difference in the restricted colimit at one selected stage.
    obtain ⟨i, z, hz⟩ :=
      moduleCat_colimit_stage_representation (R := R) H (x - y)
    have hgdiff : g.hom (x - y) = 0 := by
      simpa using sub_eq_zero.mpr hxy
    have hpre_apply :
        g.hom ((colimit.ι H i).hom z) = (colimit.ι F i.1).hom z := by
      have hpre := congrArg ModuleCat.Hom.hom (colimit.ι_pre F E i)
      exact LinearMap.congr_fun hpre z
    have hfull_zero : (colimit.ι F i.1).hom z = 0 := by
      rw [← hpre_apply, hz]
      exact hgdiff
    obtain ⟨k, hik, hkzero⟩ :=
      moduleCat_colimit_eq_zero_eventually (R := R) F z hfull_zero
    obtain ⟨q, hfactor⟩ := htail i.1 k hik
    have hnext_zero : (F.map (homOfLE (hnext i.1))).hom z = 0 := by
      -- Tail factorization transports the eventual zero back to the prescribed `next` stage.
      rw [hfactor]
      rw [ModuleCat.hom_comp]
      simpa using congrArg q.hom hkzero
    let j : S := ⟨next i.1, hnextS i.1 i.2⟩
    have hijS : i ≤ j := hnext i.1
    have hstage_zero : (H.map (homOfLE hijS)).hom z = 0 := by
      simpa [H, E] using hnext_zero
    have hrestricted_zero : (colimit.ι H i).hom z = 0 := by
      have hmove :=
        LinearMap.congr_fun
          (congrArg ModuleCat.Hom.hom (colimit.w H (homOfLE hijS))) z
      have hleft_zero :
          (ModuleCat.Hom.hom (H.map (homOfLE hijS) ≫ colimit.ι H j)) z = 0 := by
        rw [ModuleCat.hom_comp]
        change (colimit.ι H j).hom ((H.map (homOfLE hijS)).hom z) = 0
        rw [hstage_zero]
        simp
      exact hmove ▸ hleft_zero
    have hdiff_zero : x - y = 0 := by
      rw [← hz]
      exact hrestricted_zero
    exact sub_eq_zero.mp hdiff_zero
  · intro x
    let U : Set ↑(colimit F) := ⋃ i, ⋃ _ : i ∈ S, Set.range ((colimit.ι F i).hom)
    have hU_le_range : U ≤ LinearMap.range g.hom := by
      intro y hy
      rcases Set.mem_iUnion.mp hy with ⟨i, hyi⟩
      rcases Set.mem_iUnion.mp hyi with ⟨hiS, hyimg⟩
      rcases hyimg with ⟨z, rfl⟩
      -- Each selected full-stage image comes from the corresponding restricted stage image.
      refine ⟨(colimit.ι H ⟨i, hiS⟩).hom z, ?_⟩
      have hpre := congrArg ModuleCat.Hom.hom (colimit.ι_pre F E ⟨i, hiS⟩)
      exact LinearMap.congr_fun hpre z
    have hspan_le_range : Submodule.span R U ≤ LinearMap.range g.hom :=
      Submodule.span_le.mpr hU_le_range
    have hxspan : x ∈ Submodule.span R U := by
      rw [hspan]
      simp
    exact hspan_le_range hxspan

/-- Helper for Chap10 Lemma 10 92 2: a tail-factorization datum restricts the
Mittag-Leffler directed-system structure to a tail-closed subtype diagram. -/
private lemma isMittagLefflerDirectedSystem_subtype_of_tailFactorization
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ ModuleCat.{v} R)
    (S : Set I) [Nonempty S] [IsDirectedOrder S]
    (next : I → I) (hnext : ∀ i, i ≤ next i)
    (htail : ∀ i k (hik : i ≤ k), ∃ h : F.obj k ⟶ F.obj (next i),
      F.map (homOfLE (hnext i)) = F.map (homOfLE hik) ≫ h)
    (hnextS : ∀ i ∈ S, next i ∈ S)
    (hfp : ∀ i, Module.FinitePresentation R (F.obj i)) :
    @IsMittagLefflerDirectedSystem R _ S inferInstance inferInstance inferInstance
      ((OrderEmbedding.subtype S).toOrderHom.toFunctor ⋙ F) := by
  classical
  let E := (OrderEmbedding.subtype S).toOrderHom.toFunctor
  let H : S ⥤ ModuleCat.{v} R := E ⋙ F
  refine ⟨?_, ?_⟩
  · intro s
    -- Finite presentation of restricted stages is inherited from the original system.
    simpa [H, E] using hfp s.1
  · intro N
    -- Work directly with the range formulation of the Hom inverse-system ML condition.  The
    -- chosen tail stage lies in `S`, and the factorization datum supplies the required range
    -- witness for every still later restricted stage.
    rw [Functor.isMittagLeffler_iff_subset_range_comp]
    intro sop
    let s : S := unop sop
    let t : S := ⟨next s.1, hnextS s.1 s.2⟩
    have hst : s ≤ t := hnext s.1
    refine ⟨op t, (homOfLE hst).op, ?_⟩
    intro kop g y hy
    rcases hy with ⟨φ, rfl⟩
    let k : S := unop kop
    have htk : t ≤ k := leOfHom g.unop
    have htkI : t.1 ≤ k.1 := htk
    have hskI : s.1 ≤ k.1 := (hnext s.1).trans htkI
    obtain ⟨q, hq⟩ := htail s.1 k.1 hskI
    let ψ : H.obj k ⟶ N := q ≫ φ
    refine ⟨ψ, ?_⟩
    -- Both Hom-system maps are precomposition; the tail factorization identifies the two
    -- precomposed transition maps.
    have hg_unop : g.unop = homOfLE htk := Subsingleton.elim _ _
    have hcalc :
        F.map (homOfLE (hnext s.1)) ≫ (F.map (homOfLE htkI) ≫ (q ≫ φ)) =
          F.map (homOfLE (hnext s.1)) ≫ φ := by
      calc
        F.map (homOfLE (hnext s.1)) ≫ (F.map (homOfLE htkI) ≫ (q ≫ φ))
            = (F.map (homOfLE (hnext s.1)) ≫ F.map (homOfLE htkI)) ≫ q ≫ φ := by
                simp [Category.assoc]
        _ = F.map (homOfLE hskI) ≫ q ≫ φ := by
                have hcomp :
                    (homOfLE (hnext s.1) : s.1 ⟶ t.1) ≫
                        (homOfLE htkI : t.1 ⟶ k.1) =
                      (homOfLE hskI : s.1 ⟶ k.1) :=
                  Subsingleton.elim _ _
                have hmapcomp :
                    F.map (homOfLE (hnext s.1)) ≫ F.map (homOfLE htkI) =
                      F.map (homOfLE hskI) := by
                  rw [← Functor.map_comp, hcomp]
                rw [hmapcomp]
        _ = F.map (homOfLE (hnext s.1)) ≫ φ := by
                simpa [Category.assoc] using
                  (congrArg (fun m : F.obj s.1 ⟶ F.obj (next s.1) ↦ m ≫ φ) hq).symm
    simpa [H, E, colimitPresentationHomInverseSystem, s, t, k, ψ, hg_unop,
      Category.assoc] using hcalc

/-- Helper for Chap10 Lemma 10 92 2: over a countable index, a Mittag-Leffler presentation has a
stage-image fixer obtained from a compatible Hom-preimage section. -/
private lemma exists_stageImageFactorization_fixing_stageMap_of_countable
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I] [Countable I]
    (F : I ⥤ ModuleCat.{v} R)
    (hF : IsMittagLefflerDirectedSystem F)
    (i : I) :
    ∃ j, ∃ g : ↑(colimit F) →ₗ[R] F.obj j,
      (((colimit.ι F j).hom : F.obj j →ₗ[R] ↑(colimit F)) ∘ₗ g) ∘ₗ
        ((colimit.ι F i).hom : F.obj i →ₗ[R] ↑(colimit F)) =
      ((colimit.ι F i).hom : F.obj i →ₗ[R] ↑(colimit F)) := by
  classical
  -- First choose a stage `j` through which all later transitions out of `i` factor.
  let Nprod : ModuleCat.{v} R := ModuleCat.of.{v} R ((s : I) → (F.obj s : Type v))
  obtain ⟨j, hij, hfac⟩ :=
    productHomMittagLeffler_gives_stageFactorization (F := F) (hF.2 Nprod) i
  let G : Iᵒᵖ ⥤ Type v := colimitPresentationHomInverseSystem F (F.obj j)
  let E := (CategoryTheory.orderDualEquivalence I).functor
  let A : OrderDual I ⥤ Type v :=
    E ⋙ G.toPreimages (Set.singleton (F.map (homOfLE hij)))
  have hGML : (G.toPreimages (Set.singleton (F.map (homOfLE hij)))).IsMittagLeffler :=
    Functor.IsMittagLeffler.toPreimages (F := G)
      (s := Set.singleton (F.map (homOfLE hij))) (hF.2 (F.obj j))
  have hAML' : (E ⋙ G.toPreimages (Set.singleton (F.map (homOfLE hij)))).IsMittagLeffler := by
    intro x
    obtain ⟨y, f, hf⟩ := hGML (E.obj x)
    let y' : OrderDual I := OrderDual.toDual y.unop
    let f' : y' ⟶ x := homOfLE (leOfHom f.unop)
    refine ⟨y', f', ?_⟩
    intro z g
    simpa [E, y', f', CategoryTheory.orderDualEquivalence] using hf (E.map g)
  have hAML : A.IsMittagLeffler := by
    simpa [A] using hAML'
  -- The preimage system is pointwise nonempty: above `i` use the chosen tail factorization, and
  -- away from the upper tail the defining preimage condition is vacuous.
  letI : ∀ x : OrderDual I, Nonempty (A.obj x) := by
    intro x
    let k : I := OrderDual.ofDual x
    by_cases hik : i ≤ k
    · obtain ⟨h, hh⟩ := hfac k hik
      refine ⟨⟨h, ?_⟩⟩
      rw [Set.mem_iInter]
      intro f
      have hf : f.unop = homOfLE hik := Subsingleton.elim _ _
      simpa [A, E, G, k, CategoryTheory.orderDualEquivalence,
        colimitPresentationHomInverseSystem, Functor.toPreimages_obj, hf] using hh.symm
    · have z : G.obj (E.obj x) := by
        simpa [G, E, k, CategoryTheory.orderDualEquivalence,
          colimitPresentationHomInverseSystem] using (0 : F.obj k ⟶ F.obj j)
      refine ⟨⟨z, ?_⟩⟩
      rw [Set.mem_iInter]
      intro f
      exact False.elim (hik (leOfHom f.unop))
  obtain ⟨sec, hsec⟩ :=
    nonempty_sections_of_countable_mittagLeffler_inverse_system (A := A) hAML
  have coc_naturality : ∀ {a b : I} (f : a ⟶ b),
      F.map f ≫ (sec (OrderDual.toDual b)).1 = (sec (OrderDual.toDual a)).1 := by
    intro a b f
    let fd : OrderDual.toDual b ⟶ OrderDual.toDual a := homOfLE (leOfHom f)
    have h := congrArg Subtype.val (hsec fd)
    -- The section compatibility is exactly cocone naturality after translating
    -- `OrderDual I` to `Iᵒᵖ`.
    simpa [A, E, G, fd, CategoryTheory.orderDualEquivalence,
      colimitPresentationHomInverseSystem] using h
  let coc : Cocone F :=
    {
    pt := F.obj j
    ι :=
      { app := fun k ↦ (sec (OrderDual.toDual k)).1
        naturality := fun _ _ f ↦ coc_naturality f }
    }
  let m : colimit F ⟶ F.obj j := colimit.desc F coc
  refine ⟨j, m.hom, ?_⟩
  apply LinearMap.ext
  intro x
  -- The chosen section lies over the transition map at `i`, so the descended map restricts to
  -- `F.map (i ≤ j)` on stage `i`.
  have hm : colimit.ι F i ≫ m = F.map (homOfLE hij) := by
    have hm_coc : colimit.ι F i ≫ m = coc.ι.app i := by
      simpa [m] using colimit.ι_desc (c := coc) i
    have hsec_i : coc.ι.app i = F.map (homOfLE hij) := by
      have hmem : (sec (OrderDual.toDual i)).1 ∈
          ⋂ f : E.obj (OrderDual.toDual i) ⟶ op i,
            G.map f ⁻¹' Set.singleton (F.map (homOfLE hij)) := by
        simpa [A, E, CategoryTheory.orderDualEquivalence, G, Functor.toPreimages_obj] using
          (sec (OrderDual.toDual i)).2
      rw [Set.mem_iInter] at hmem
      have hid := hmem (𝟙 (op i))
      have hid_eq :
          G.map (𝟙 (op i)) ((sec (OrderDual.toDual i)).1) = F.map (homOfLE hij) :=
        Set.mem_singleton_iff.mp hid
      have gid : G.map (𝟙 (op i)) ((sec (OrderDual.toDual i)).1) =
          (sec (OrderDual.toDual i)).1 := by
        simp [G]
      exact gid.symm.trans hid_eq
    exact hm_coc.trans hsec_i
  have hcat : F.map (homOfLE hij) ≫ colimit.ι F j = colimit.ι F i := by
    simpa using (colimit.w F (homOfLE hij)).symm
  have hfix_cat : colimit.ι F i ≫ m ≫ colimit.ι F j = colimit.ι F i := by
    calc
      colimit.ι F i ≫ m ≫ colimit.ι F j =
          F.map (homOfLE hij) ≫ colimit.ι F j := by
            simpa [Category.assoc] using congrArg (fun t ↦ t ≫ colimit.ι F j) hm
      _ = colimit.ι F i := hcat
  have hfix_linear := congrArg ModuleCat.Hom.hom hfix_cat
  exact LinearMap.congr_fun hfix_linear x

/-- Chap10 Lemma 10 92 2: a whole stage image in a countably generated
Mittag-Leffler presentation is fixed by an endomorphism factoring through another stage. -/
lemma exists_stageImageFactorization_fixing_stageMap
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ ModuleCat.{v} R)
    (hF : IsMittagLefflerDirectedSystem F)
    (hcg : Module.CountablyGenerated R ↑(colimit F))
    (i : I) :
    ∃ j, ∃ g : ↑(colimit F) →ₗ[R] F.obj j,
      (((colimit.ι F j).hom : F.obj j →ₗ[R] ↑(colimit F)) ∘ₗ g) ∘ₗ
        ((colimit.ι F i).hom : F.obj i →ₗ[R] ↑(colimit F)) =
      ((colimit.ι F i).hom : F.obj i →ₗ[R] ↑(colimit F)) := by
  classical
  -- Route correction: the public countable-subpresentation theorem forgets the fixed stage and the
  -- tail closure data.  We keep that data locally, apply the proved countable-index fixer to the
  -- restricted diagram, and transport the result through the restricted colimit comparison.
  let Nprod : ModuleCat.{v} R := ModuleCat.of.{v} R ((s : I) → (F.obj s : Type v))
  have htail_raw :=
    productHomMittagLeffler_gives_stageFactorization (F := F) (hF.2 Nprod)
  let next : I → I := fun i ↦ Classical.choose (htail_raw i)
  have hnext : ∀ i : I, i ≤ next i :=
    fun i ↦ Classical.choose (Classical.choose_spec (htail_raw i))
  have htail : ∀ i k (hik : i ≤ k), ∃ h : F.obj k ⟶ F.obj (next i),
      F.map (homOfLE (hnext i)) = F.map (homOfLE hik) ≫ h := by
    intro i
    exact Classical.choose_spec (Classical.choose_spec (htail_raw i))
  obtain ⟨S, hiS, hScount, hSnonempty, hSdirected, hnextS, hspanS⟩ :=
    exists_countable_tailClosed_stageSet_spanning_colimit_containing
      (R := R) F hcg next i
  letI : Countable S := hScount
  letI : Nonempty S := hSnonempty
  letI : IsDirectedOrder S := hSdirected
  let E := (OrderEmbedding.subtype S).toOrderHom.toFunctor
  let H : S ⥤ ModuleCat.{v} R := E ⋙ F
  have hH : IsMittagLefflerDirectedSystem H := by
    -- Tail closure lets the original tail-factorization criterion restrict to the chosen
    -- countable subsystem.
    simpa [H, E] using
      isMittagLefflerDirectedSystem_subtype_of_tailFactorization
        (R := R) F S next hnext htail hnextS hF.1
  have hIsoE : IsIso (colimit.pre F E) := by
    dsimp [E]
    exact isIso_colimitPre_of_tailClosed_spanning
      (R := R) F S next hnext htail hnextS hspanS
  letI : IsIso (colimit.pre F E) := hIsoE
  obtain ⟨jS, gS, hfixS⟩ :=
    exists_stageImageFactorization_fixing_stageMap_of_countable
      (R := R) H hH ⟨i, hiS⟩
  let p : colimit H ⟶ colimit F := colimit.pre F E
  letI : IsIso p := by
    dsimp [p]
    exact hIsoE
  let e : colimit H ≅ colimit F := asIso p
  let g : ↑(colimit F) →ₗ[R] F.obj jS.1 := gS.comp e.inv.hom
  refine ⟨jS.1, g, ?_⟩
  apply LinearMap.ext
  intro x
  -- The inverse comparison sends the fixed original stage leg back to its restricted-stage leg.
  have hpre_i :
      p.hom ((colimit.ι H ⟨i, hiS⟩).hom x) = (colimit.ι F i).hom x := by
    have hpre := congrArg ModuleCat.Hom.hom (colimit.ι_pre F E ⟨i, hiS⟩)
    exact LinearMap.congr_fun hpre x
  have hinv_i :
      e.inv.hom ((colimit.ι F i).hom x) = (colimit.ι H ⟨i, hiS⟩).hom x := by
    calc
      e.inv.hom ((colimit.ι F i).hom x)
          = e.inv.hom (p.hom ((colimit.ι H ⟨i, hiS⟩).hom x)) := by
              rw [hpre_i]
      _ = (colimit.ι H ⟨i, hiS⟩).hom x := by
              have hcat : p ≫ e.inv = 𝟙 (colimit H) := by
                simpa [e] using e.hom_inv_id
              have hlin := congrArg ModuleCat.Hom.hom hcat
              exact LinearMap.congr_fun hlin ((colimit.ι H ⟨i, hiS⟩).hom x)
  have hpre_j (y : H.obj jS) :
      (colimit.ι F jS.1).hom y = p.hom ((colimit.ι H jS).hom y) := by
    have hpre := congrArg ModuleCat.Hom.hom (colimit.ι_pre F E jS)
    exact (LinearMap.congr_fun hpre y).symm
  -- After these two comparison rewrites, the countable subsystem fixer is exactly the desired
  -- identity, then we push it forward again by `p`.
  calc
    (((((colimit.ι F jS.1).hom : F.obj jS.1 →ₗ[R] ↑(colimit F)) ∘ₗ g) ∘ₗ
        ((colimit.ι F i).hom : F.obj i →ₗ[R] ↑(colimit F))) x)
        = (colimit.ι F jS.1).hom
            (gS (e.inv.hom ((colimit.ι F i).hom x))) := by
            rfl
    _ = (colimit.ι F jS.1).hom
            (gS ((colimit.ι H ⟨i, hiS⟩).hom x)) := by
            rw [hinv_i]
    _ = p.hom ((colimit.ι H jS).hom
            (gS ((colimit.ι H ⟨i, hiS⟩).hom x))) := by
            rw [hpre_j]
    _ = p.hom
            (((((colimit.ι H jS).hom : H.obj jS →ₗ[R] ↑(colimit H)) ∘ₗ gS) ∘ₗ
              ((colimit.ι H ⟨i, hiS⟩).hom : H.obj ⟨i, hiS⟩ →ₗ[R] ↑(colimit H))) x) := by
            rfl
    _ = p.hom ((colimit.ι H ⟨i, hiS⟩).hom x) := by
            rw [LinearMap.congr_fun hfixS x]
    _ = (colimit.ι F i).hom x := hpre_i

/-- Helper for Chap10 Lemma 10 92 2: a finite-free map that is already represented at one stage
is fixed by an endomorphism of the colimit factoring through a later stage. -/
private lemma exists_stageFactorization_fixing_fin_stageMap
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ ModuleCat.{v} R)
    (hF : IsMittagLefflerDirectedSystem F)
    (hcg : Module.CountablyGenerated R ↑(colimit F))
    {n : ℕ} {i : I} (φ : (Fin n → R) →ₗ[R] F.obj i) :
    ∃ j, ∃ g : ↑(colimit F) →ₗ[R] F.obj j,
      (((colimit.ι F j).hom : F.obj j →ₗ[R] ↑(colimit F)) ∘ₗ g) ∘ₗ
        (((colimit.ι F i).hom : F.obj i →ₗ[R] ↑(colimit F)) ∘ₗ φ) =
      ((colimit.ι F i).hom : F.obj i →ₗ[R] ↑(colimit F)) ∘ₗ φ := by
  -- The stronger stage-image fixer applies before the finite-free map; evaluating at `φ z`
  -- gives the required equality after postcomposition with `φ`.
  obtain ⟨j, g, hfix⟩ := exists_stageImageFactorization_fixing_stageMap F hF hcg i
  refine ⟨j, g, ?_⟩
  apply LinearMap.ext
  intro z
  exact LinearMap.congr_fun hfix (φ z)

/- Domain triage:
- primary domain: countably generated Mittag-Leffler modules via directed colimit presentations by
  finitely presented modules;
- sampled owner declarations:
  `Module.CountablyGenerated`,
  `Module.MittagLeffler`,
  `IsMittagLefflerDirectedSystem`,
  `exists_countable_directed_subpresentation_of_countably_generated_mittag_leffler`,
  `exists_countable_directed_subpresentation_of_countably_generated_of_isMittagLefflerDirectedSystem`,
  and `Module.MittagLeffler.exists_presentation`;
- best owner abstraction for the ring-general source statement: `Module.MittagLeffler`;
- primitive data:
  the module `M`, the countable-generation hypothesis, and the finite source map `f`;
- derived API:
  a chosen presentation `F : I ⥤ ModuleCat R` with `IsMittagLefflerDirectedSystem F`,
  used only in the bridge theorem below, and the resulting finitely presented factor module.

Layer classification:
- `bridge/view`: the presentation-level theorem below upgrades a chosen presentation to the
  source-facing factorization statement;
- `source-facing`: the second theorem is the textbook ring-general statement for an abstract module
  `M`;
- `core/canonical`: `Module.MittagLeffler` is the owner abstraction, while
  `IsMittagLefflerDirectedSystem` is the presentation data extracted from
  `MittagLeffler.exists_presentation`.
-/
-- Proof sketch: first apply the presentation-level bridge form of Lemma `10.92.1` to replace the
-- given presentation by a countable directed subsystem with the same colimit. Then use Example
-- `10.86.2` and Lemma `10.86.3` on the associated Hom inverse system against the finite source `P`
-- to find a stage where the image of `f` stabilizes. The induced map back to the colimit yields an
-- endomorphism fixing `f`, and this endomorphism factors through a finitely presented stage of the
-- presentation.
/-- Lemma 10.92.2 in presentation form: if `F` is a Mittag-Leffler directed system of finitely
presented `R`-modules with countably generated colimit, then any map from a finite module into
`colimit F` is fixed by an endomorphism of `colimit F` factoring through a single stage `F.obj i`.
This is the bridge from the owner `MittagLeffler R M` to the source-facing finite-presentation
factorization statement; the stage `F.obj i` is already finitely presented by
`IsMittagLefflerDirectedSystem F`. -/
@[stacks 05D2]
theorem exists_stage_factorization_fixing_finite_map
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I] (F : I ⥤ ModuleCat.{v} R)
    (hF : IsMittagLefflerDirectedSystem F)
    (hcg : Module.CountablyGenerated R ↑(colimit F))
    (f : P →ₗ[R] ↑(colimit F)) :
    ∃ i, ∃ g : ↑(colimit F) →ₗ[R] F.obj i,
      (((colimit.ι F i).hom : F.obj i →ₗ[R] ↑(colimit F)) ∘ₗ g) ∘ₗ f = f := by
  classical
  -- Route correction: a map from a merely finite module need not itself factor through a filtered
  -- colimit stage. Instead, pass to a finite free cover and only stage-lift the finitely many basis
  -- images of the composite map.
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R P
  obtain ⟨i, φ, hφ⟩ :=
    linearMap_from_fin_factor_through_directed_colimit_stage (F := F) n (f.comp π)
  -- The remaining structural input fixes the finite-free stage map through a later stage.
  obtain ⟨j, g, hfixπ⟩ :=
    exists_stageFactorization_fixing_fin_stageMap F hF hcg φ
  refine ⟨j, g, ?_⟩
  have hcompπ :
      ((((colimit.ι F j).hom : F.obj j →ₗ[R] ↑(colimit F)) ∘ₗ g) ∘ₗ f).comp π =
        f.comp π := by
    calc
      ((((colimit.ι F j).hom : F.obj j →ₗ[R] ↑(colimit F)) ∘ₗ g) ∘ₗ f).comp π
          = ((((colimit.ι F j).hom : F.obj j →ₗ[R] ↑(colimit F)) ∘ₗ g) ∘ₗ
              (f.comp π)) := by
              rfl
      _ = ((((colimit.ι F j).hom : F.obj j →ₗ[R] ↑(colimit F)) ∘ₗ g) ∘ₗ
              (((colimit.ι F i).hom : F.obj i →ₗ[R] ↑(colimit F)) ∘ₗ φ)) := by
              rw [← hφ]
      _ = ((colimit.ι F i).hom : F.obj i →ₗ[R] ↑(colimit F)) ∘ₗ φ := hfixπ
      _ = f.comp π := hφ
  -- Since the finite free cover is surjective, equality after precomposition by it is equality on
  -- the original finite module.
  apply LinearMap.ext
  intro p
  obtain ⟨y, rfl⟩ := hπ p
  exact LinearMap.congr_fun hcompπ y

/-- Source-facing consequence of Chap10 Lemma 10 92 2: if `M` is a countably generated
Mittag-Leffler `R`-module, then for every map `f : P →ₗ[R] M` from a finite source there is a
finitely presented `R`-module `Q` and maps `M → Q → M` whose composite fixes `f`. This is the
ring-general source-facing statement, with the presentation data kept internal to the owner
`MittagLeffler R M`. -/
@[stacks 05D2]
theorem exists_endomorphism_factorsThroughFinitePresentation_fixing_finite_map
    (hcg : Module.CountablyGenerated R M)
    (hML : MittagLeffler R M)
    (f : P →ₗ[R] M) :
    ∃ (Q : ModuleCat.{v} R) (_ : Module.FinitePresentation R Q)
      (g : M →ₗ[R] Q) (h : Q →ₗ[R] M),
        (h ∘ₗ g) ∘ₗ f = f := by
  classical
  -- Choose the presentation supplied by the owner `MittagLeffler` structure and expose its
  -- preorder instances locally.
  let pres : MittagLefflerPresentation R M := Classical.choice hML.exists_presentation
  letI : Preorder pres.index := pres.indexPreorder
  letI : Nonempty pres.index := pres.indexNonempty
  letI : IsDirectedOrder pres.index := pres.indexDirected
  let c : colimit pres.diagram ≅ ModuleCat.of.{v} R M := Classical.choice pres.colimitIso
  -- Transport countable generation from `M` to the chosen colimit through the presentation
  -- isomorphism.
  have hcg_colimit : Module.CountablyGenerated R ↑(colimit pres.diagram) :=
    Module.countablyGenerated_of_linearEquiv c.toLinearEquiv hcg
  let fColimit : P →ₗ[R] ↑(colimit pres.diagram) := c.inv.hom.comp f
  -- Apply the presentation-level factorization theorem to the transported finite-source map.
  obtain ⟨i, gStage, hfix⟩ :=
    exists_stage_factorization_fixing_finite_map
      (F := pres.diagram) pres.presentation_isMittagLeffler hcg_colimit fColimit
  refine ⟨pres.diagram.obj i, pres.presentation_isMittagLeffler.1 i,
    gStage.comp c.inv.hom, c.hom.hom.comp (colimit.ι pres.diagram i).hom, ?_⟩
  -- Compose the presentation-level fixed-map identity with the colimit isomorphism and cancel the
  -- inverse-isomorphism pair on `M`.
  apply LinearMap.ext
  intro p
  have hfix_apply := LinearMap.congr_fun hfix p
  have hcancel :
      c.hom.hom (c.inv.hom (f p)) = f p := by
    have hcat : c.inv ≫ c.hom = 𝟙 (ModuleCat.of.{v} R M) := c.inv_hom_id
    have hlin := congrArg ModuleCat.Hom.hom hcat
    exact LinearMap.congr_fun hlin (f p)
  calc
    ((c.hom.hom.comp (colimit.ι pres.diagram i).hom).comp
        (gStage.comp c.inv.hom) |>.comp f) p
        = c.hom.hom
            ((((colimit.ι pres.diagram i).hom.comp gStage).comp fColimit) p) := by
            rfl
    _ = c.hom.hom (fColimit p) := by rw [hfix_apply]
    _ = f p := hcancel

end

end Module
