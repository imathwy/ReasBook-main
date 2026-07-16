import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_11_1
import stacks_proof.stacks_project.Chap10.Lemma_10_11_4

-- Proof rescue support owners for Proposition 10.88.6.

open CategoryTheory
open CategoryTheory.Limits

universe u v w s

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {M : Type (max v w)} [AddCommGroup M] [Module R M]

/-- Helper for Proposition 10.88.6: reindex the directed system along `ULift` so the index lives
in the same universe as the module stages. -/
noncomputable def lifted_index_diagram
    (F : I ⥤ ModuleCat.{max v w} R) :
    ULift.{max v w} I ⥤ ModuleCat.{max v w} R where
  obj i := F.obj i.down
  map {X Y} h :=
    F.map (homOfLE (show X.down ≤ Y.down from h.down.down))
  map_id X := by
    simpa using F.map_id X.down
  map_comp {X Y Z} h₁ h₂ := by
    let h₁' : X.down ≤ Y.down := show X.down ≤ Y.down from h₁.down.down
    let h₂' : Y.down ≤ Z.down := show Y.down ≤ Z.down from h₂.down.down
    simpa using
      F.map_comp (homOfLE h₁') (homOfLE h₂')

/-- Helper for Proposition 10.88.6: the chosen colimit cocone for `F` induces a cocone on the
lifted-index diagram with the same colimit point. -/
noncomputable def lifted_index_cocone
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M) :
    Cocone (lifted_index_diagram (R := R) F) where
  pt := ModuleCat.of R M
  ι :=
    { app := fun i ↦ colimit.ι F i.down ≫ c.hom
      naturality := by
        intro i j h
        let hij : i.down ≤ j.down := show i.down ≤ j.down from h.down.down
        -- Proof comment: naturality is exactly the original colimit cocone naturality, with the
        -- lifted index forgotten by `ULift.down`.
        apply ModuleCat.hom_ext
        ext x
        have hw :
            (colimit.ι F j.down).hom ((F.map (homOfLE hij)).hom x) =
              (colimit.ι F i.down).hom x := by
          simpa using
            LinearMap.congr_fun
              (congrArg ModuleCat.Hom.hom (colimit.w F (homOfLE hij))) x
        simpa [lifted_index_diagram, Category.assoc] using congrArg (c.hom.hom) hw }

/-- Helper for Proposition 10.88.6: the cocone on the lifted-index diagram is still colimiting
after descending cocones back along `ULift.down`. -/
noncomputable def common_universe_lifted_index_isColimit
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M) :
    IsColimit (lifted_index_cocone (R := R) (M := M) F c) := by
  let descendedCocone : Cocone (lifted_index_diagram (R := R) F) → Cocone F :=
    fun s ↦
      { pt := s.pt
        ι :=
          { app := fun i ↦ s.ι.app (ULift.up i)
            naturality := by
              intro i j h
              let hij : (ULift.up i : ULift.{max v w} I) ≤ ULift.up j := h.down.down
              -- Proof comment: forgetting the `ULift` index turns cocone naturality on the lifted
              -- diagram back into cocone naturality on `F`.
              simpa [lifted_index_diagram] using s.w (homOfLE hij) } }
  let hc := colimit.isColimit F
  refine
    { desc := fun s ↦ c.inv ≫ hc.desc (descendedCocone s)
      fac := ?_
      uniq := ?_ }
  · intro s i
    -- Proof comment: the lifted cocone leg is just the original colimit leg followed by `c.hom`,
    -- so the universal factorization descends after cancelling the isomorphism `c`.
    simpa [lifted_index_cocone, descendedCocone, Category.assoc] using
      hc.fac (descendedCocone s) i.down
  · intro s m hm
    have hm' : c.hom ≫ m = hc.desc (descendedCocone s) := by
      apply hc.hom_ext
      intro i
      -- Proof comment: both maps out of `colimit F` agree on every colimit leg, once we rewrite
      -- the lifted cocone condition at `ULift.up i`.
      have hs : colimit.ι F i ≫ c.hom ≫ m = s.ι.app (ULift.up i) := by
        simpa [lifted_index_cocone, Category.assoc] using hm (ULift.up i)
      have hfac : colimit.ι F i ≫ hc.desc (descendedCocone s) = s.ι.app (ULift.up i) := by
        simpa [descendedCocone] using hc.fac (descendedCocone s) i
      exact hs.trans hfac.symm
    calc
      m = c.inv ≫ c.hom ≫ m := by
        simpa [Category.assoc] using (c.inv_hom_id_assoc m).symm
      _ = c.inv ≫ hc.desc (descendedCocone s) := by rw [hm']
      _ = c.inv ≫ hc.desc (descendedCocone s) := rfl

/-- Helper for Chap10 Proposition 10 88 6 Common Universe Owners: `ULift` of a directed preorder
is again directed. -/
private lemma exists_ge_ge_ulift
    {α : Type v} [Preorder α] [IsDirectedOrder α] (a b : ULift.{s} α) :
    ∃ c : ULift.{s} α, a ≤ c ∧ b ≤ c := by
  -- Proof comment: choose a common upper bound downstairs and lift it back to the larger universe.
  obtain ⟨c, hac, hbc⟩ := exists_ge_ge a.down b.down
  exact ⟨ULift.up c, hac, hbc⟩

/-- Chap10 Proposition 10 88 6 Common Universe Owners: the lifted directed preorder is filtered in
its own universe. -/
private lemma isFiltered_ulift
    {α : Type v} [Preorder α] [Nonempty α] [IsDirectedOrder α] :
    IsFiltered (ULift.{s} α) := by
  let hfo : IsFilteredOrEmpty (ULift.{s} α) :=
    { cocone_objs := by
        intro X Y
        -- Proof comment: object cocones are common upper bounds in the original directed preorder.
        obtain ⟨Z, hX, hY⟩ := exists_ge_ge X.down Y.down
        exact ⟨ULift.up Z, homOfLE hX, homOfLE hY, trivial⟩
      cocone_maps := by
        intro X Y f g
        -- Proof comment: a preorder category has at most one morphism between fixed endpoints.
        exact ⟨Y, 𝟙 Y, Subsingleton.elim _ _⟩ }
  let hn : Nonempty (ULift.{s} α) := inferInstance
  exact @IsFiltered.mk (ULift.{s} α) _ hfo hn

/-- Helper for Chap10 Proposition 10 88 6 Common Universe Owners: finitely many elements that
eventually vanish in a filtered system vanish after one common transition. -/
private lemma synchronize_finset_vanishing
    {J : Type s} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{s} R) {i : J} {α : Type*} (g : α → F.obj i)
    {E : Finset α}
    (hE : ∀ x ∈ E, ∃ (j : J) (u : i ⟶ j), (F.map u).hom (g x) = 0) :
    ∃ (j : J) (u : i ⟶ j), ∀ x ∈ E, (F.map u).hom (g x) = 0 := by
  classical
  induction E using Finset.induction_on with
  | empty =>
      -- Proof comment: the empty set needs no transition beyond the identity.
      refine ⟨i, 𝟙 i, ?_⟩
      simp
  | @insert x E hx ih =>
      -- Proof comment: first synchronize the old finite set, then merge that stage with the new
      -- witness through filteredness.
      have hx_vanish :
          ∃ (j : J) (u : i ⟶ j), (F.map u).hom (g x) = 0 :=
        hE x (Finset.mem_insert_self _ _)
      have htail :
          ∀ y ∈ E, ∃ (j : J) (u : i ⟶ j), (F.map u).hom (g y) = 0 := by
        intro y hy
        exact hE y (Finset.mem_insert_of_mem hy)
      obtain ⟨j₁, u₁, hu₁⟩ := ih htail
      obtain ⟨j₂, u₂, hu₂⟩ := hx_vanish
      let k : J := IsFiltered.max j₁ j₂
      let q₁ : j₁ ⟶ k := IsFiltered.leftToMax j₁ j₂
      let q₂ : j₂ ⟶ k := IsFiltered.rightToMax j₁ j₂
      let l : J := IsFiltered.coeq (u₁ ≫ q₁) (u₂ ≫ q₂)
      let r : k ⟶ l := IsFiltered.coeqHom (u₁ ≫ q₁) (u₂ ≫ q₂)
      refine ⟨l, u₁ ≫ q₁ ≫ r, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with hyx | hyE
      · subst y
        have hx_l :
            (F.map (u₂ ≫ q₂ ≫ r)).hom (g x) = 0 := by
          -- Proof comment: the new vanishing persists after postcomposition to the common stage.
          simpa [Functor.map_comp, Category.assoc] using
            congrArg (fun z ↦ (F.map (q₂ ≫ r)).hom z) hu₂
        have hcoeq : u₁ ≫ q₁ ≫ r = u₂ ≫ q₂ ≫ r := by
          simpa [Category.assoc] using IsFiltered.coeq_condition (u₁ ≫ q₁) (u₂ ≫ q₂)
        simpa [hcoeq] using hx_l
      · have hy_l :
            (F.map (u₁ ≫ q₁ ≫ r)).hom (g y) = 0 := by
          -- Proof comment: every previously synchronized vanishing persists after the final
          -- postcomposition.
          simpa [Functor.map_comp, Category.assoc] using
            congrArg (fun z ↦ (F.map (q₁ ≫ r)).hom z) (hu₁ y hyE)
        exact hy_l

/-- Helper for Chap10 Proposition 10 88 6 Common Universe Owners: a map from a finite free module
to a colimiting cocone of modules factors through one stage. -/
private lemma linearMap_from_fin_factor_through_isColimit_stage
    {J : Type s} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{s} R) (c : Cocone F) (hc : IsColimit c)
    (n : ℕ) (f : (Fin n → R) →ₗ[R] c.pt) :
    ∃ (j : J) (g : (Fin n → R) →ₗ[R] F.obj j), (c.ι.app j).hom.comp g = f := by
  classical
  letI : PreservesColimit F (forget (ModuleCat.{s} R)) :=
    modulecat_forget_preserves_colimit_filtered (R := R) F
  let hc_types :
      IsColimit ((forget (ModuleCat.{s} R)).mapCocone c) :=
    isColimitOfPreserves (forget (ModuleCat.{s} R)) hc
  choose j x hx using fun i : Fin n ↦
    Types.jointly_surjective_of_isColimit hc_types
      (f ((Pi.basisFun R (Fin n)) i))
  obtain ⟨k, ⟨u⟩⟩ : ∃ k : J, Nonempty (∀ i : Fin n, j i ⟶ k) := by
    -- Proof comment: filteredness merges the finitely many basis-vector representatives into a
    -- single stage.
    have : ∃ k : J, ∀ i : Fin n, Nonempty (j i ⟶ k) := by
      simpa using IsFiltered.sup_objs_exists (Finset.univ.image j)
    simpa [← exists_true_iff_nonempty, Classical.skolem, -exists_const_iff] using this
  let g : (Fin n → R) →ₗ[R] F.obj k :=
    (Pi.basisFun R (Fin n)).constr R fun i ↦ (F.map (u i)).hom (x i)
  refine ⟨k, g, ?_⟩
  -- Proof comment: equality of linear maps from the finite free module is checked on the standard
  -- basis.
  apply (Pi.basisFun R (Fin n)).ext
  intro i
  have htransport :
      (c.ι.app k).hom ((F.map (u i)).hom (x i)) =
        (c.ι.app (j i)).hom (x i) := by
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (c.w (u i))) (x i)
  rw [LinearMap.comp_apply]
  rw [(Pi.basisFun R (Fin n)).constr_basis]
  exact htransport.trans (by simpa using hx i)

/-- Helper for Chap10 Proposition 10 88 6 Common Universe Owners: finitely generated relations that
vanish in a colimiting cocone already vanish after a single later transition. -/
private lemma fgSubmodule_eventually_le_ker_of_cocone_vanishing
    {n : ℕ} {K : Submodule R (Fin n → R)} (hK : K.FG)
    {J : Type s} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{s} R) (c : Cocone F) (hc : IsColimit c)
    {i : J} (g : (Fin n → R) →ₗ[R] F.obj i)
    (hg : K ≤ LinearMap.ker ((c.ι.app i).hom.comp g)) :
    ∃ (j : J) (u : i ⟶ j), K ≤ LinearMap.ker ((F.map u).hom.comp g) := by
  classical
  letI : PreservesColimit F (forget (ModuleCat.{s} R)) :=
    modulecat_forget_preserves_colimit_filtered (R := R) F
  let hc_types :
      IsColimit ((forget (ModuleCat.{s} R)).mapCocone c) :=
    isColimitOfPreserves (forget (ModuleCat.{s} R)) hc
  letI : Module.Finite R K := Module.Finite.of_fg hK
  obtain ⟨E, hEspan⟩ := Module.Finite.fg_top (R := R) (M := K)
  have hE :
      ∀ x ∈ E, ∃ (j : J) (u : i ⟶ j), (F.map u).hom (g x.1) = 0 := by
    intro x hx
    have hx_colim : (c.ι.app i).hom (g x.1) = (c.ι.app i).hom (0 : F.obj i) := by
      -- Proof comment: each chosen relation generator is killed by the original cocone map.
      have hx_zero : (c.ι.app i).hom (g x.1) = 0 := by
        simpa [LinearMap.mem_ker, LinearMap.comp_apply] using hg x.2
      exact hx_zero.trans (c.ι.app i).hom.map_zero.symm
    obtain ⟨j, u, hu⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' hc_types (g x.1) 0).mp hx_colim
    refine ⟨j, u, ?_⟩
    simpa using hu.trans (F.map u).hom.map_zero
  obtain ⟨j, u, hu⟩ :=
    synchronize_finset_vanishing (R := R) F (fun x : K ↦ g x.1) hE
  refine ⟨j, u, ?_⟩
  let δ : K →ₗ[R] F.obj j := ((F.map u).hom.comp g).comp K.subtype
  have hδ_zero : δ = 0 := by
    apply LinearMap.ext
    intro x
    have hx_span : x ∈ Submodule.span R (E : Set K) := by
      rw [hEspan]
      simp
    -- Proof comment: finite generator vanishing propagates to all of `K` by span induction.
    exact Submodule.span_induction
      (fun y hy ↦ by simpa [δ] using hu y hy)
      (by simp [δ])
      (fun y z _ _ hy hz ↦ by simpa [δ, map_add, hy, hz])
      (fun r y _ hy ↦ by simpa [δ, map_smul, hy])
      hx_span
  intro x hx
  have hxδ : δ ⟨x, hx⟩ = 0 := LinearMap.congr_fun hδ_zero ⟨x, hx⟩
  simpa [δ] using hxδ

/-- Helper for Chap10 Proposition 10 88 6 Common Universe Owners: maps from finitely presented
modules into a filtered colimit cocone factor through one stage. -/
private lemma finitePresentation_factor_through_isColimit
    {J : Type s} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{s} R) (c : Cocone F) (hc : IsColimit c)
    (P : ModuleCat.{s} R) [Module.FinitePresentation R P] (f : P ⟶ c.pt) :
    ∃ (j : J) (g : P ⟶ F.obj j), g ≫ c.ι.app j = f := by
  classical
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin R P
  let f_free : (Fin n → R) →ₗ[R] c.pt :=
    (f.hom.comp e.symm.toLinearMap).comp (Submodule.mkQ K)
  obtain ⟨i, gᵢ, hgᵢ⟩ :=
    linearMap_from_fin_factor_through_isColimit_stage
      (R := R) F c hc n f_free
  have hvanish : K ≤ LinearMap.ker ((c.ι.app i).hom.comp gᵢ) := by
    intro x hx
    have hx0 : (Submodule.mkQ K) x = 0 :=
      (Submodule.Quotient.mk_eq_zero K).mpr hx
    have hcomp :
        ((c.ι.app i).hom.comp gᵢ) x = f_free x :=
      LinearMap.congr_fun hgᵢ x
    -- Proof comment: the free lift kills `K` because it was obtained by composing with the
    -- quotient map.
    rw [LinearMap.mem_ker, hcomp]
    calc
      f_free x = (f.hom.comp e.symm.toLinearMap) ((Submodule.mkQ K) x) := rfl
      _ = (f.hom.comp e.symm.toLinearMap) 0 := by rw [hx0]
      _ = 0 := by simp
  obtain ⟨j, u, hu⟩ :=
    fgSubmodule_eventually_le_ker_of_cocone_vanishing
      (R := R) (K := K) hK F c hc gᵢ hvanish
  let g_quot : ((Fin n → R) ⧸ K) →ₗ[R] F.obj j :=
    K.liftQ ((F.map u).hom.comp gᵢ) hu
  let g_stage : P →ₗ[R] F.obj j := g_quot.comp e.toLinearMap
  refine ⟨j, ModuleCat.ofHom g_stage, ?_⟩
  have hquot :
      (c.ι.app j).hom.comp g_quot = f.hom.comp e.symm.toLinearMap := by
    -- Proof comment: compare quotient maps after precomposing with the quotient projection.
    apply Submodule.linearMap_qext
    rw [LinearMap.comp_assoc, Submodule.liftQ_mkQ]
    have hcocone :
        (c.ι.app j).hom.comp (F.map u).hom = (c.ι.app i).hom := by
      ext x
      exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (c.w u)) x
    rw [← LinearMap.comp_assoc, hcocone]
    simpa [f_free] using hgᵢ
  -- Proof comment: transport the descended quotient map back across the chosen finite
  -- presentation of `P`.
  apply ModuleCat.hom_ext
  ext x
  have hx := LinearMap.congr_fun hquot (e x)
  calc
    ((c.ι.app j).hom.comp g_stage) x = ((c.ι.app j).hom.comp g_quot) (e x) := rfl
    _ = (f.hom.comp e.symm.toLinearMap) (e x) := hx
    _ = f.hom x := by simp

/-- Helper for Chap10 Proposition 10 88 6 Common Universe Owners: after lifting the preorder index
to the common universe, any map from a finitely presented module into the chosen colimit cocone
factors through one stage. -/
theorem ulifted_factor_through_given_filtered_cocone_stage_of_finitePresentation
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    (P : ModuleCat.{max v w} R)
    [Module.FinitePresentation R P]
    (f : P ⟶ ModuleCat.of R M) :
    ∃ (i : I) (g : P ⟶ F.obj i), g ≫ (colimit.ι F i ≫ c.hom) = f := by
  letI : IsFiltered (ULift.{max v w} I) :=
    (isFiltered_ulift (α := I) : IsFiltered (ULift.{max v w} I))
  obtain ⟨i, g, hg⟩ :=
    finitePresentation_factor_through_isColimit
      (R := R)
      (F := lifted_index_diagram (R := R) F)
      (c := lifted_index_cocone (R := R) (M := M) F c)
      (hc := common_universe_lifted_index_isColimit (R := R) (M := M) F c)
      P f
  -- Proof comment: the lifted stage `i` descends to `i.down`, and the lifted cocone leg unfolds to
  -- the original colimit leg followed by the chosen isomorphism.
  refine ⟨i.down, g, ?_⟩
  simpa [lifted_index_cocone] using hg

/-- Helper for Proposition 10.88.6: after lifting the preorder index to the common universe,
equality of two maps in the colimit descends to equality after one later transition map.
-/
theorem ulift_index_eventually_equal_of_hom_to_colimit_of_finite_module
    (F : I ⥤ ModuleCat.{max v w} R)
    {N : Type (max v w)} [AddCommGroup N] [Module R N] [Module.Finite R N]
    {i : I}
    (a b : ModuleCat.of R N ⟶ F.obj i)
    (h : a ≫ colimit.ι F i = b ≫ colimit.ι F i) :
    ∃ (j : I) (hij : i ≤ j), a ≫ F.map (homOfLE hij) = b ≫ F.map (homOfLE hij) := by
  letI : IsDirectedOrder (ULift.{max v w} I) :=
    ⟨fun a b => by
      obtain ⟨j, haj, hbj⟩ := exists_ge_ge a.down b.down
      exact ⟨ULift.up j, haj, hbj⟩⟩
  let hcolim :
      colimit F =
        ModuleCat.of R ((colimit F : ModuleCat.{max v w} R) : Type (max v w)) := rfl
  let liftedCocone :
      Cocone (lifted_index_diagram (R := R) F) :=
    lifted_index_cocone (R := R)
      (M := ((colimit F : ModuleCat.{max v w} R) : Type (max v w)))
      F (eqToIso hcolim)
  let liftedIsColimit :
      IsColimit liftedCocone :=
    common_universe_lifted_index_isColimit (R := R)
      (M := ((colimit F : ModuleCat.{max v w} R) : Type (max v w)))
      F (eqToIso hcolim)
  let e : liftedCocone.pt ≅ colimit (lifted_index_diagram (R := R) F) :=
    liftedIsColimit.coconePointUniqueUpToIso
      (colimit.isColimit (lifted_index_diagram (R := R) F))
  have hleg :
      liftedCocone.ι.app (ULift.up i) ≫ e.hom =
        colimit.ι (lifted_index_diagram (R := R) F) (ULift.up i) :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      liftedIsColimit (colimit.isColimit (lifted_index_diagram (R := R) F)) (ULift.up i)
  have h_post :
      a ≫ liftedCocone.ι.app (ULift.up i) ≫ e.hom =
        b ≫ liftedCocone.ι.app (ULift.up i) ≫ e.hom := by
    have h' : a ≫ liftedCocone.ι.app (ULift.up i) = b ≫ liftedCocone.ι.app (ULift.up i) := by
      simpa [liftedCocone, lifted_index_cocone] using h
    -- Proof comment: postcompose the original colimit equality with the comparison isomorphism to
    -- move to the canonical colimit cocone of the lifted diagram.
    simpa [Category.assoc] using congrArg (fun t ↦ t ≫ e.hom) h'
  have h_lifted :
      a ≫ colimit.ι (lifted_index_diagram (R := R) F) (ULift.up i) =
        b ≫ colimit.ι (lifted_index_diagram (R := R) F) (ULift.up i) := by
    -- Proof comment: identify the explicit lifted cocone with the canonical lifted colimit cocone
    -- via the unique comparison isomorphism.
    calc
      a ≫ colimit.ι (lifted_index_diagram (R := R) F) (ULift.up i)
          = a ≫ liftedCocone.ι.app (ULift.up i) ≫ e.hom := by
              simpa [Category.assoc] using congrArg (fun t ↦ a ≫ t) hleg.symm
      _ = b ≫ liftedCocone.ι.app (ULift.up i) ≫ e.hom := h_post
      _ = b ≫ colimit.ι (lifted_index_diagram (R := R) F) (ULift.up i) := by
              simpa [Category.assoc] using congrArg (fun t ↦ b ≫ t) hleg
  -- Proof comment: apply the finite-module eventual-equality owner to the lifted diagram and
  -- then descend the later lifted index back to `I`.
  obtain ⟨j, hij, hj_eq⟩ :=
    eventually_equal_of_hom_to_colimit_of_finite_module
      (R := R) (N := ModuleCat.of R N) (lifted_index_diagram (R := R) F) a b h_lifted
  refine ⟨j.down, hij.down.down, ?_⟩
  simpa [lifted_index_diagram] using hj_eq

end
