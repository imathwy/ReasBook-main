import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_84_1
import stacks_proof.stacks_project.Chap10.Lemma_10_84_3
import stacks_proof.stacks_project.Chap10.Definition_10_88_1
import stacks_proof.stacks_project.Chap10.Definition_10_88_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe u v

section

variable {R : Type u} [Ring R]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace Module

/-- Helper for Chap10 Lemma 10 92 1: the product Hom inverse-system condition gives the
eventual factorization condition on transition maps. -/
private theorem tailFactorization_of_isMittagLefflerDirectedSystem
    (F : I ⥤ ModuleCat.{v} R)
    (hF : IsMittagLefflerDirectedSystem F) :
    ∀ i : I, ∃ (j : I) (hij : i ≤ j),
      ∀ (k : I) (hik : i ≤ k), ∃ h : F.obj k ⟶ F.obj j,
        F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h := by
  classical
  intro i
  let N : ModuleCat.{v} R := ModuleCat.of.{v} R ((s : I) → (F.obj s : Type v))
  let G : Iᵒᵖ ⥤ Type v := colimitPresentationHomInverseSystem F N
  have hML : G.IsMittagLeffler := hF.2 N
  -- Stabilize the eventual range at `i` in the product-valued Hom inverse system.
  obtain ⟨jop, f, hf⟩ := (Functor.isMittagLeffler_iff_subset_range_comp G).mp hML (op i)
  let j : I := unop jop
  have hij : i ≤ j := leOfHom f.unop
  let insj : F.obj j ⟶ N :=
    ModuleCat.ofHom (LinearMap.single R (fun s : I ↦ (F.obj s : Type v)) j)
  let projj : N ⟶ F.obj j := ModuleCat.ofHom (LinearMap.proj j)
  have hins_proj : insj ≫ projj = 𝟙 (F.obj j) := by
    apply ModuleCat.hom_ext
    ext x
    simp only [insj, projj, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
      Function.comp_apply, ModuleCat.hom_id, LinearMap.id_coe, id_eq]
    rw [LinearMap.single_apply, LinearMap.proj_apply, Pi.single_eq_same]
  refine ⟨j, hij, ?_⟩
  intro k hik
  obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k
  have hil : i ≤ l := hij.trans hjl
  have hf_unop : f.unop = homOfLE hij := Subsingleton.elim _ _
  have hsubset :
      Set.range (fun g : F.obj j ⟶ N ↦ F.map (homOfLE hij) ≫ g) ⊆
        Set.range (fun g : F.obj l ⟶ N ↦ F.map (homOfLE hil) ≫ g) := by
    simpa [G, hf_unop] using hf ((homOfLE hjl).op)
  have hmem :
      F.map (homOfLE hij) ≫ insj ∈
        Set.range (fun g : F.obj j ⟶ N ↦ F.map (homOfLE hij) ≫ g) := by
    exact ⟨insj, rfl⟩
  obtain ⟨gl, hgl⟩ := hsubset hmem
  refine ⟨F.map (homOfLE hkl) ≫ gl ≫ projj, ?_⟩
  -- Project the stabilized product-valued factorization to the `j`-coordinate.
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

/-- Helper for Chap10 Lemma 10 92 1: a Mittag-Leffler directed system presents its own colimit as
a `Module.MittagLeffler` module. -/
private theorem mittagLeffler_colimit_of_isMittagLefflerDirectedSystem
    (F : I ⥤ ModuleCat.{v} R)
    (hF : IsMittagLefflerDirectedSystem F) :
    Module.MittagLeffler R ↑(colimit F) := by
  -- Package the chosen system itself as the witnessing Mittag-Leffler presentation.
  exact ⟨⟨{
    index := I
    indexPreorder := inferInstance
    indexNonempty := inferInstance
    indexDirected := inferInstance
    diagram := F
    presentation_isMittagLeffler := hF
    colimitIso := ⟨Iso.refl _⟩
  }⟩⟩

variable {J : Type v} [Preorder J] [Nonempty J] [IsDirectedOrder J]

/-- Helper for Chap10 Lemma 10 92 1: every element of a filtered module colimit is represented at
some stage, with the index type left generic. -/
private lemma filteredColimit_stageRepresentation
    (F : J ⥤ ModuleCat.{v} R) (x : ↑(colimit F)) :
    ∃ i : J, ∃ y : F.obj i, (colimit.ι F i).hom y = x := by
  -- Forget to `Type`, where filtered colimits have jointly-surjective structure maps.
  letI : PreservesColimit F (forget (ModuleCat.{v} R)) :=
    modulecat_forget_preserves_colimit_filtered (R := R) F
  let hc : IsColimit ((forget (ModuleCat.{v} R)).mapCocone (colimit.cocone F)) :=
    isColimitOfPreserves (forget (ModuleCat.{v} R)) (colimit.isColimit F)
  simpa using Types.jointly_surjective_of_isColimit hc x

/-- Helper for Chap10 Lemma 10 92 1: a stage element that maps to zero in a filtered module
colimit becomes zero after a transition to a later stage. -/
private lemma filteredColimit_eq_zero_eventually
    (F : J ⥤ ModuleCat.{v} R) {i : J} (x : F.obj i)
    (hx : (colimit.ι F i).hom x = 0) :
    ∃ j : J, ∃ hij : i ≤ j, (F.map (homOfLE hij)).hom x = 0 := by
  -- Use the concrete filtered-colimit equality-to-zero API and translate the arrow to an order
  -- inequality in the thin preorder category.
  letI : PreservesColimit F (forget (ModuleCat.{v} R)) :=
    modulecat_forget_preserves_colimit_filtered (R := R) F
  obtain ⟨j, f, hf⟩ :=
    CategoryTheory.Limits.Concrete.colimit_rep_eq_zero
      (R := R) (F := F) i x hx
  refine ⟨j, leOfHom f, ?_⟩
  have hf_eq : f = homOfLE (leOfHom f) := Subsingleton.elim _ _
  simpa [hf_eq] using hf

/-- Helper for Chap10 Lemma 10 92 1: finitely many indices in a directed preorder have a common
upper bound. -/
private lemma exists_fin_common_upper {n : ℕ} (a : Fin n → J) :
    ∃ q : J, ∀ t : Fin n, a t ≤ q := by
  -- Inductively merge the finite family of indices using directedness.
  induction n with
  | zero =>
      refine ⟨Classical.choice inferInstance, ?_⟩
      intro t
      exact Fin.elim0 t
  | succ n ih =>
      obtain ⟨q, hq⟩ := ih (fun t : Fin n ↦ a t.succ)
      obtain ⟨r, h0, hqr⟩ := exists_ge_ge (a 0) q
      refine ⟨r, ?_⟩
      intro t
      exact Fin.cases h0 (fun t ↦ (hq t).trans hqr) t

/-- Helper for Chap10 Lemma 10 92 1: maps from a finite free module into a filtered module colimit
factor through one stage. -/
private lemma finiteFree_hom_factor_through_colimit
    (F : J ⥤ ModuleCat.{v} R) (n : ℕ)
    (f : (Fin n → R) →ₗ[R] (colimit F : ModuleCat.{v} R)) :
    ∃ (j : J) (g : (Fin n → R) →ₗ[R] F.obj j), (colimit.ι F j).hom.comp g = f := by
  classical
  choose j x hx using fun i : Fin n =>
    filteredColimit_stageRepresentation (R := R) F (f ((Pi.basisFun R (Fin n)) i))
  obtain ⟨k, hk⟩ := exists_fin_common_upper (J := J) j
  let g : (Fin n → R) →ₗ[R] F.obj k :=
    { toFun := fun z => ∑ i, z i • (F.map (homOfLE (hk i))).hom (x i)
      map_add' := by
        intro z z'
        -- The chosen basis-image lifts extend linearly to a map from the finite free module.
        simp [Finset.sum_add_distrib, add_smul]
      map_smul' := by
        intro r z
        simp [Finset.smul_sum, mul_smul] }
  refine ⟨k, g, ?_⟩
  -- The constructed lift agrees with `f` on the standard basis, hence everywhere.
  apply (Pi.basisFun R (Fin n)).ext
  intro i
  have htransport :
      (colimit.ι F k).hom ((F.map (homOfLE (hk i))).hom (x i)) =
        (colimit.ι F (j i)).hom (x i) := by
    exact LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom (colimit.w F (homOfLE (hk i)))) (x i)
  calc
    ((colimit.ι F k).hom.comp g) ((Pi.basisFun R (Fin n)) i)
        = (colimit.ι F k).hom ((F.map (homOfLE (hk i))).hom (x i)) := by
            simp [g, Pi.basisFun_apply]
    _ = (colimit.ι F (j i)).hom (x i) := htransport
    _ = f ((Pi.basisFun R (Fin n)) i) := hx i

/-- Helper for Chap10 Lemma 10 92 1: two maps out of a quotient agree when they agree after
precomposition with the quotient map. -/
private lemma quotient_linearMap_ext
    {n : ℕ} {K : Submodule R (Fin n → R)} {P : Type*}
    [AddCommGroup P] [Module R P]
    {f g : ((Fin n → R) ⧸ K) →ₗ[R] P}
    (h : f.comp (Submodule.mkQ K) = g.comp (Submodule.mkQ K)) :
    f = g := by
  -- The quotient map is surjective, so checking representatives is enough.
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective K q
  simpa using LinearMap.congr_fun h x

/-- Helper for Chap10 Lemma 10 92 1: maps from a finitely presented module into a filtered module
colimit factor through one stage. -/
private lemma finitePresentation_hom_factor_through_colimit
    (F : J ⥤ ModuleCat.{v} R) (P : ModuleCat.{v} R)
    [Module.FinitePresentation R P] (f : P ⟶ colimit F) :
    ∃ j, ∃ g : P ⟶ F.obj j, g ≫ colimit.ι F j = f := by
  classical
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin R P
  obtain ⟨m, rel, hrelspan⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hK
  let f₀ : ((Fin n → R) ⧸ K) →ₗ[R] (colimit F : ModuleCat.{v} R) :=
    f.hom.comp e.symm.toLinearMap
  obtain ⟨i, gᵢ, hgᵢ⟩ :=
    finiteFree_hom_factor_through_colimit (R := R) F n (f₀.comp (Submodule.mkQ K))
  have hrel_zero_colimit : ∀ a : Fin m, (colimit.ι F i).hom (gᵢ (rel a)) = 0 := by
    intro a
    have hrelmem : rel a ∈ K := by
      rw [← hrelspan]
      exact Submodule.subset_span ⟨a, rfl⟩
    have hmkQ : Submodule.mkQ K (rel a) = 0 :=
      (Submodule.Quotient.mk_eq_zero K).2 hrelmem
    have hcomp := LinearMap.congr_fun hgᵢ (rel a)
    simpa [LinearMap.comp_apply, hmkQ] using hcomp
  choose z hiz hz using fun a : Fin m =>
    filteredColimit_eq_zero_eventually (R := R) F (gᵢ (rel a)) (hrel_zero_colimit a)
  let stage : Fin (m + 1) → J := Fin.cases i z
  obtain ⟨q, hq⟩ := exists_fin_common_upper (J := J) stage
  have hiq : i ≤ q := hq 0
  have hzq : ∀ a : Fin m, z a ≤ q := fun a => hq a.succ
  let gFree : (Fin n → R) →ₗ[R] F.obj q := (F.map (homOfLE hiq)).hom.comp gᵢ
  have hrel_le : K ≤ LinearMap.ker gFree := by
    rw [← hrelspan]
    apply Submodule.span_le.mpr
    rintro x ⟨a, rfl⟩
    -- The finite generating relations have become zero at the common later stage `q`.
    change (F.map (homOfLE hiq)).hom (gᵢ (rel a)) = 0
    have hcomp : homOfLE (hiz a) ≫ homOfLE (hzq a) = homOfLE hiq :=
      Subsingleton.elim _ _
    rw [← hcomp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hz a]
    simp
  let gQuot : ((Fin n → R) ⧸ K) →ₗ[R] F.obj q := K.liftQ gFree hrel_le
  have hgQuot : (colimit.ι F q).hom.comp gQuot = f₀ := by
    apply quotient_linearMap_ext (R := R) (K := K)
    calc
      ((colimit.ι F q).hom.comp gQuot).comp (Submodule.mkQ K)
          = (colimit.ι F q).hom.comp gFree := by
              rw [LinearMap.comp_assoc, Submodule.liftQ_mkQ]
      _ = (colimit.ι F i).hom.comp gᵢ := by
            have hcolim : (colimit.ι F q).hom.comp (F.map (homOfLE hiq)).hom =
                (colimit.ι F i).hom := by
              ext x
              exact LinearMap.congr_fun
                (congrArg ModuleCat.Hom.hom (colimit.w F (homOfLE hiq))) x
            simpa [gFree, LinearMap.comp_assoc] using congrArg (fun φ ↦ φ.comp gᵢ) hcolim
      _ = f₀.comp (Submodule.mkQ K) := hgᵢ
  let gP : P ⟶ F.obj q := ModuleCat.ofHom (gQuot.comp e.toLinearMap)
  refine ⟨q, gP, ?_⟩
  -- Return from the quotient presentation to the original finitely presented source.
  apply ModuleCat.hom_ext
  ext x
  simpa [gP, f₀, LinearMap.comp_assoc] using LinearMap.congr_fun hgQuot (e x)

/-- Helper for Chap10 Lemma 10 92 1: two maps from a finitely presented module that agree in a
filtered colimit agree after passing to a common later stage. -/
private lemma finitePresentation_hom_eventually_eq_of_colimit
    (F : J ⥤ ModuleCat.{v} R) (P : ModuleCat.{v} R)
    [Module.FinitePresentation R P] {j k : J}
    (a : P ⟶ F.obj j) (b : P ⟶ F.obj k)
    (h : a ≫ colimit.ι F j = b ≫ colimit.ι F k) :
    ∃ l, ∃ hjl : j ≤ l, ∃ hkl : k ≤ l,
      a ≫ F.map (homOfLE hjl) = b ≫ F.map (homOfLE hkl) := by
  classical
  obtain ⟨m, hjm, hkm⟩ := exists_ge_ge j k
  let a' : P ⟶ F.obj m := a ≫ F.map (homOfLE hjm)
  let b' : P ⟶ F.obj m := b ≫ F.map (homOfLE hkm)
  have hcolim : a' ≫ colimit.ι F m = b' ≫ colimit.ι F m := by
    calc
      a' ≫ colimit.ι F m = a ≫ colimit.ι F j := by
        simp [a', Category.assoc, colimit.w]
      _ = b ≫ colimit.ι F k := h
      _ = b' ≫ colimit.ι F m := by
        simp [b', Category.assoc, colimit.w]
  obtain ⟨l, f, hf⟩ :=
    eventually_equal_of_hom_to_colimit_of_finite_module (R := R) (N := P) F a' b' hcolim
  refine ⟨l, hjm.trans (leOfHom f), hkm.trans (leOfHom f), ?_⟩
  have hf_eq : f = homOfLE (leOfHom f) := Subsingleton.elim _ _
  have hleft : homOfLE hjm ≫ homOfLE (leOfHom f) =
      homOfLE (hjm.trans (leOfHom f)) := Subsingleton.elim _ _
  have hright : homOfLE hkm ≫ homOfLE (leOfHom f) =
      homOfLE (hkm.trans (leOfHom f)) := Subsingleton.elim _ _
  simpa [a', b', hf_eq, Category.assoc, ← Functor.map_comp, hleft, hright] using hf

/-- Helper for Chap10 Lemma 10 92 1: the tail-factorization criterion transfers between two
finitely presented filtered colimit presentations of the same module. -/
private theorem tailFactorization_of_colimitIso_of_tailFactorization
    (F : I ⥤ ModuleCat.{v} R) (G : J ⥤ ModuleCat.{v} R)
    (hFfp : ∀ i, Module.FinitePresentation R (F.obj i))
    (hGfp : ∀ j, Module.FinitePresentation R (G.obj j))
    (cF : colimit F ≅ ModuleCat.of R M)
    (cG : colimit G ≅ ModuleCat.of R M)
    (hGtail : ∀ a : J, ∃ (b : J) (hab : a ≤ b),
      ∀ (s : J) (has : a ≤ s), ∃ h : G.obj s ⟶ G.obj b,
        G.map (homOfLE hab) = G.map (homOfLE has) ≫ h) :
    ∀ i : I, ∃ (j : I) (hij : i ≤ j),
      ∀ (k : I) (hik : i ≤ k), ∃ h : F.obj k ⟶ F.obj j,
        F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h := by
  classical
  intro i
  let _ : Module.FinitePresentation R (F.obj i) := hFfp i
  obtain ⟨a, gia, hgia⟩ :=
    finitePresentation_hom_factor_through_colimit (R := R) G (F.obj i)
      (colimit.ι F i ≫ cF.hom ≫ cG.inv)
  obtain ⟨b, hab, hGfac⟩ := hGtail a
  let _ : Module.FinitePresentation R (G.obj b) := hGfp b
  obtain ⟨j₀, gbj, hgbj⟩ :=
    finitePresentation_hom_factor_through_colimit (R := R) F (G.obj b)
      (colimit.ι G b ≫ cG.hom ≫ cF.inv)
  have hnorm_colimit :
      (𝟙 (F.obj i)) ≫ colimit.ι F i =
        (gia ≫ G.map (homOfLE hab) ≫ gbj) ≫ colimit.ι F j₀ := by
    -- Normalize the round trip `Fᵢ → colimit G → G_b → colimit F` in the colimit of `F`.
    calc
      (𝟙 (F.obj i)) ≫ colimit.ι F i = colimit.ι F i := by simp
      _ = (colimit.ι F i ≫ cF.hom ≫ cG.inv) ≫ cG.hom ≫ cF.inv := by
        simp [Category.assoc]
      _ = (gia ≫ colimit.ι G a) ≫ cG.hom ≫ cF.inv := by
        rw [hgia]
      _ = gia ≫ G.map (homOfLE hab) ≫ colimit.ι G b ≫ cG.hom ≫ cF.inv := by
        simp [Category.assoc]
      _ = gia ≫ G.map (homOfLE hab) ≫ gbj ≫ colimit.ι F j₀ := by
        rw [hgbj]
  obtain ⟨j, hij, hj₀j, hnorm_raw⟩ :=
    finitePresentation_hom_eventually_eq_of_colimit (R := R) F (F.obj i)
      (𝟙 (F.obj i)) (gia ≫ G.map (homOfLE hab) ≫ gbj) hnorm_colimit
  let hBj : G.obj b ⟶ F.obj j := gbj ≫ F.map (homOfLE hj₀j)
  have hnorm : F.map (homOfLE hij) = gia ≫ G.map (homOfLE hab) ≫ hBj := by
    simpa [hBj, Category.assoc] using hnorm_raw
  refine ⟨j, hij, ?_⟩
  intro k hik
  let _ : Module.FinitePresentation R (F.obj k) := hFfp k
  obtain ⟨s, gks, hgks⟩ :=
    finitePresentation_hom_factor_through_colimit (R := R) G (F.obj k)
      (colimit.ι F k ≫ cF.hom ≫ cG.inv)
  have hG_colimit :
      gia ≫ colimit.ι G a =
        (F.map (homOfLE hik) ≫ gks) ≫ colimit.ι G s := by
    -- Compare the two maps `Fᵢ → colimit G`: one through `G_a`, one through `F_k` and `G_s`.
    calc
      gia ≫ colimit.ι G a = colimit.ι F i ≫ cF.hom ≫ cG.inv := hgia
      _ = F.map (homOfLE hik) ≫ colimit.ι F k ≫ cF.hom ≫ cG.inv := by
        simp
      _ = F.map (homOfLE hik) ≫ (gks ≫ colimit.ι G s) := by
        rw [hgks]
      _ = (F.map (homOfLE hik) ≫ gks) ≫ colimit.ι G s := by simp [Category.assoc]
  obtain ⟨t, hat, hst, hG_eq⟩ :=
    finitePresentation_hom_eventually_eq_of_colimit (R := R) G (F.obj i)
      gia (F.map (homOfLE hik) ≫ gks) hG_colimit
  obtain ⟨hTB, hTB_eq⟩ := hGfac t hat
  let hFinal : F.obj k ⟶ F.obj j := gks ≫ G.map (homOfLE hst) ≫ hTB ≫ hBj
  refine ⟨hFinal, ?_⟩
  -- The fixed normalization and the `G`-tail factorization produce the desired factorization in
  -- the arbitrary presentation `F`.
  calc
    F.map (homOfLE hij) = gia ≫ G.map (homOfLE hab) ≫ hBj := hnorm
    _ = gia ≫ G.map (homOfLE hat) ≫ hTB ≫ hBj := by
      simpa [Category.assoc] using congrArg (fun q ↦ gia ≫ q ≫ hBj) hTB_eq
    _ = (F.map (homOfLE hik) ≫ gks ≫ G.map (homOfLE hst)) ≫ hTB ≫ hBj := by
      simpa [Category.assoc] using congrArg (fun q ↦ q ≫ hTB ≫ hBj) hG_eq
    _ = F.map (homOfLE hik) ≫ hFinal := by
      simp [hFinal, Category.assoc]

/-- Helper for Chap10 Lemma 10 92 1: the module-level Mittag-Leffler condition transfers the
tail-factorization criterion to any finitely presented directed presentation of the module. -/
private theorem tailFactorization_of_mittagLeffler_colimitIso
    (F : I ⥤ ModuleCat.{v} R)
    (hfp : ∀ i, Module.FinitePresentation R (F.obj i))
    (c : colimit F ≅ ModuleCat.of R M)
    (hML : Module.MittagLeffler R M) :
    ∀ i : I, ∃ (j : I) (hij : i ≤ j),
      ∀ (k : I) (hik : i ≤ k), ∃ h : F.obj k ⟶ F.obj j,
        F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h := by
  classical
  -- Route correction: Proposition `10.88.6` gives the presentation transfer through tensor kernels
  -- only under `[CommRing R]`; here we use the ring-general finite-presentation Hom-colimit
  -- factorization helpers above to compare with the presentation packaged by `hML`.
  let pres : MittagLefflerPresentation R M := Classical.choice hML.exists_presentation
  letI : Preorder pres.index := pres.indexPreorder
  letI : Nonempty pres.index := pres.indexNonempty
  letI : IsDirectedOrder pres.index := pres.indexDirected
  let cG : colimit pres.diagram ≅ ModuleCat.of R M := Classical.choice pres.colimitIso
  have hGtail :
      ∀ a : pres.index, ∃ (b : pres.index) (hab : a ≤ b),
        ∀ (s : pres.index) (has : a ≤ s), ∃ h : pres.diagram.obj s ⟶ pres.diagram.obj b,
          pres.diagram.map (homOfLE hab) = pres.diagram.map (homOfLE has) ≫ h :=
    tailFactorization_of_isMittagLefflerDirectedSystem pres.diagram
      pres.presentation_isMittagLeffler
  exact
    tailFactorization_of_colimitIso_of_tailFactorization
      (R := R) (M := M) F pres.diagram hfp pres.presentation_isMittagLeffler.1 c cG hGtail

end Module

/-- Helper for Chap10 Lemma 10 92 1: a countable set of indices has a countable directed
superset closed under a chosen monotone tail operation. -/
private lemma exists_countable_directed_tailClosed_superset
    (A : Set I) (hA : A.Countable) (next : I → I) :
    ∃ S : Set I, A ⊆ S ∧ Countable S ∧ Nonempty S ∧ IsDirectedOrder S ∧
      ∀ i ∈ S, next i ∈ S := by
  classical
  let i0 : I := Classical.choice inferInstance
  let upper : I × I → I := fun p ↦ Classical.choose (exists_ge_ge p.1 p.2)
  have hupper_left : ∀ p : I × I, p.1 ≤ upper p :=
    fun p ↦ (Classical.choose_spec (exists_ge_ge p.1 p.2)).1
  have hupper_right : ∀ p : I × I, p.2 ≤ upper p :=
    fun p ↦ (Classical.choose_spec (exists_ge_ge p.1 p.2)).2
  let seed : Set I := insert i0 A
  let C : ℕ → Set I :=
    Nat.rec seed (fun _ Cn ↦ (Cn ∪ next '' Cn) ∪ upper '' (Cn ×ˢ Cn))
  have hC_mono_step : ∀ n, C n ⊆ C (n + 1) := by
    intro n x hx
    -- Each closure stage is included in the next one as the first summand.
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
        simpa [C, seed] using hA.insert i0
    | succ n ih =>
        have hnext_count : (next '' C n).Countable := ih.image next
        have hupper_count : (upper '' (C n ×ˢ C n)).Countable := (ih.prod ih).image upper
        simpa [C] using (ih.union hnext_count).union hupper_count
  let S : Set I := ⋃ n, C n
  refine ⟨S, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    -- The original seed is placed in stage zero of the closure.
    exact Set.mem_iUnion.mpr ⟨0, by simpa [C, seed] using Or.inr hx⟩
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
  · intro i hi
    rcases Set.mem_iUnion.mp hi with ⟨n, hin⟩
    -- The unary tail operation is also added at the next closure stage.
    exact Set.mem_iUnion.mpr ⟨n + 1, by
      change next i ∈ (C n ∪ next '' C n) ∪ upper '' (C n ×ˢ C n)
      exact Or.inl (Or.inr ⟨i, hin, rfl⟩)⟩

/-- Helper for Chap10 Lemma 10 92 1: every element of a filtered colimit of modules is represented
at some stage. -/
private lemma moduleCat_colimit_stage_representation
    (F : I ⥤ ModuleCat.{v} R) (x : ↑(colimit F)) :
    ∃ i : I, ∃ y : F.obj i, (colimit.ι F i).hom y = x := by
  -- Forget the module structure to use the standard jointly-surjective colimit cocone in `Type`.
  letI : PreservesColimit F (forget (ModuleCat.{v} R)) :=
    modulecat_forget_preserves_colimit_filtered (R := R) F
  let hc : IsColimit ((forget (ModuleCat.{v} R)).mapCocone (colimit.cocone F)) :=
    isColimitOfPreserves (forget (ModuleCat.{v} R)) (colimit.isColimit F)
  simpa using Types.jointly_surjective_of_isColimit hc x

/-- Helper for Chap10 Lemma 10 92 1: a stage element that maps to zero in a filtered module
colimit becomes zero after passing to a later stage. -/
private lemma moduleCat_colimit_eq_zero_eventually
    (F : I ⥤ ModuleCat.{v} R) {i : I} (x : F.obj i)
    (hx : (colimit.ι F i).hom x = 0) :
    ∃ j : I, ∃ hij : i ≤ j, (F.map (homOfLE hij)).hom x = 0 := by
  -- The concrete colimit API turns zero in the colimit into zero after a transition map.
  letI : PreservesColimit F (forget (ModuleCat.{v} R)) :=
    modulecat_forget_preserves_colimit_filtered (R := R) F
  obtain ⟨j, f, hf⟩ :=
    CategoryTheory.Limits.Concrete.colimit_rep_eq_zero
      (R := R) (F := F) i x hx
  refine ⟨j, leOfHom f, ?_⟩
  have hf_eq : f = homOfLE (leOfHom f) := Subsingleton.elim _ _
  simpa [hf_eq] using hf

/-- Helper for Chap10 Lemma 10 92 1: countable generation of a filtered module colimit supplies a
countable directed tail-closed subsystem whose selected stage images span the colimit. -/
private lemma exists_countable_tailClosed_stageSet_spanning_colimit
    (F : I ⥤ ModuleCat.{v} R)
    (hcg : Module.CountablyGenerated R ↑(colimit F))
    (next : I → I) :
    ∃ S : Set I, Countable S ∧ Nonempty S ∧ IsDirectedOrder S ∧
      (∀ i ∈ S, next i ∈ S) ∧
      Submodule.span R (⋃ i, ⋃ _ : i ∈ S, Set.range ((colimit.ι F i).hom)) =
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
  obtain ⟨S, hAS, hScount, hSnonempty, hSdirected, hnextS⟩ :=
    exists_countable_directed_tailClosed_superset (A := A) hAcount next
  refine ⟨S, hScount, hSnonempty, hSdirected, hnextS, ?_⟩
  let U : Set ↑(colimit F) := ⋃ i, ⋃ _ : i ∈ S, Set.range ((colimit.ι F i).hom)
  have hT_subset : T ⊆ U := by
    intro x hx
    let t : T := ⟨x, hx⟩
    have hstageS : stage t ∈ S := hAS ⟨t, rfl⟩
    -- The chosen representative places each generator in the selected union of stage images.
    refine Set.mem_iUnion.mpr ⟨stage t, ?_⟩
    refine Set.mem_iUnion.mpr ⟨hstageS, ?_⟩
    exact ⟨elem t, helem t⟩
  -- Since the selected stage images contain the original countable generators, their span is all
  -- of the colimit.
  have htop_le : (⊤ : Submodule R ↑(colimit F)) ≤ Submodule.span R U := by
    rw [← hTspan]
    exact Submodule.span_mono hT_subset
  exact le_antisymm le_top htop_le

/-- Helper for Chap10 Lemma 10 92 1: a tail-closed directed subset whose stage images span the
whole colimit has an isomorphic restricted colimit. -/
private lemma isIso_colimitPre_of_tailClosed_spanning
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
      -- Each selected full-stage image is the image under `g` of the corresponding restricted
      -- colimit stage image.
      refine ⟨(colimit.ι H ⟨i, hiS⟩).hom z, ?_⟩
      have hpre := congrArg ModuleCat.Hom.hom (colimit.ι_pre F E ⟨i, hiS⟩)
      exact LinearMap.congr_fun hpre z
    have hspan_le_range : Submodule.span R U ≤ LinearMap.range g.hom :=
      Submodule.span_le.mpr hU_le_range
    have hxspan : x ∈ Submodule.span R U := by
      rw [hspan]
      simp
    exact hspan_le_range hxspan

/- Domain triage:
- primary domain: countable directed subpresentations of finitely presented colimit presentations of
  countably generated Mittag-Leffler modules;
- sampled owner declarations of the same kind:
  `Module.MittagLeffler`,
  `Module.CountablyGenerated`,
  `IsMittagLefflerDirectedSystem`,
  `Module.MittagLefflerPresentation`;
- owner abstraction: `Module.MittagLeffler` is the canonical owner for the source-level
  Mittag-Leffler hypothesis, while `IsMittagLefflerDirectedSystem` is presentation-level bridge
  data attached to one chosen diagram;
- primitive data for the source-facing theorem: the module `M`, a directed system `F` of finitely
  presented modules, a colimit identification `c : colimit F ≅ M`, and the owner hypotheses
  `Module.MittagLeffler R M` and `Module.CountablyGenerated R M`;
- derived API: the presentation-level companion theorem below specializes the source-facing theorem
  to the intrinsic colimit module `colimit F`.
-/
-- Proof sketch: choose a countable generating family of `M`, transfer those generators to the
-- fixed presentation `c : colimit F ≅ M`, and combine countability with the module-level
-- Mittag-Leffler condition to build a countable directed subset of stages that already captures
-- all generators and the eventual factorization data for the chosen presentation. The restricted
-- colimit comparison is then surjective by construction and injective by the stabilization
-- property.
/-- Chap10 Lemma 10 92 1: let `M` be a countably generated Mittag-Leffler `R`-module and let
`c : colimit F ≅ M` be a directed colimit presentation of `M` by finitely presented modules. Then
there is a countable directed sub-preorder of `I`, realized canonically as a subtype, whose
comparison morphism to the original colimit is an isomorphism. Equivalently, the chosen
presentation of `M` admits a countable directed subsystem with the same colimit. -/
@[stacks 059W]
theorem exists_countable_directed_subpresentation_of_countably_generated_mittag_leffler
    (F : I ⥤ ModuleCat.{v} R)
    (hfp : ∀ i, Module.FinitePresentation R (F.obj i))
    (c : colimit F ≅ ModuleCat.of R M)
    (hML : Module.MittagLeffler R M)
    (hcg : Module.CountablyGenerated R M) :
    ∃ (S : Set I) (_ : Countable S) (_ : Nonempty S) (_ : IsDirectedOrder S),
      IsIso (colimit.pre F (OrderEmbedding.subtype S).toOrderHom.toFunctor) := by
  classical
  have htail_raw :=
    Module.tailFactorization_of_mittagLeffler_colimitIso F hfp c hML
  let next : I → I := fun i ↦ Classical.choose (htail_raw i)
  have hnext : ∀ i, i ≤ next i := fun i ↦ Classical.choose (Classical.choose_spec
    (htail_raw i))
  have htail : ∀ i k (hik : i ≤ k), ∃ h : F.obj k ⟶ F.obj (next i),
      F.map (homOfLE (hnext i)) = F.map (homOfLE hik) ≫ h := by
    intro i
    exact Classical.choose_spec (Classical.choose_spec (htail_raw i))
  have hcg_colimit : Module.CountablyGenerated R ↑(colimit F) :=
    Module.countablyGenerated_of_linearEquiv c.toLinearEquiv hcg
  obtain ⟨S, hScount, hSnonempty, hSdirected, hnextS, hspanS⟩ :=
    exists_countable_tailClosed_stageSet_spanning_colimit F hcg_colimit next
  letI : Countable S := hScount
  letI : Nonempty S := hSnonempty
  letI : IsDirectedOrder S := hSdirected
  refine ⟨S, inferInstance, inferInstance, inferInstance, ?_⟩
  -- The restricted comparison is bijective by spanning for surjectivity and tail closure for
  -- injectivity.
  exact isIso_colimitPre_of_tailClosed_spanning F S next hnext htail hnextS hspanS

-- Proof sketch: specialize Lemma `10.92.1` to the intrinsic colimit module `colimit F`, using the
-- finite-presentation component of `hF` and the presentation-level Mittag-Leffler hypothesis to
-- recover the owner hypothesis `Module.MittagLeffler R ↑(colimit F)`.
/-- Presentation-level bridge form of Lemma 10.92.1: if a chosen directed system `F` is
Mittag-Leffler in the sense of Definition `10.88.1` and its colimit is countably generated, then
that presentation has a countable directed subsystem with the same colimit. -/
theorem exists_countable_directed_subpresentation_of_countably_generated_of_isMittagLefflerDirectedSystem
    (F : I ⥤ ModuleCat.{v} R)
    (hF : IsMittagLefflerDirectedSystem F)
    (hcg : Module.CountablyGenerated R ↑(colimit F)) :
    ∃ (S : Set I) (_ : Countable S) (_ : Nonempty S) (_ : IsDirectedOrder S),
      IsIso (colimit.pre F (OrderEmbedding.subtype S).toOrderHom.toFunctor) := by
  have hfp : ∀ i, Module.FinitePresentation R (F.obj i) := hF.1
  have hML : Module.MittagLeffler R ↑(colimit F) :=
    Module.mittagLeffler_colimit_of_isMittagLefflerDirectedSystem F hF
  -- Apply the source-facing form to the identity presentation of the intrinsic colimit module.
  exact
    exists_countable_directed_subpresentation_of_countably_generated_mittag_leffler
      F hfp (Iso.refl _) hML hcg

end
