import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_11_1 (from Chap10) -/
open CategoryTheory
open CategoryTheory.Limits Opposite

universe u v

section FiniteModule

variable {R : Type u} [Ring R]
variable (N : ModuleCat.{v} R)

/-- Helper for Lemma 10.11.1: finitely many stagewise equalities can be synchronized to one later
stage of a filtered diagram. -/
lemma synchronize_generator_equalities
    {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ ModuleCat R) {i : J}
    (a b : N ⟶ F.obj i) {E : Finset N}
    (hE : ∀ x ∈ E, ∃ (j : J) (f : i ⟶ j), (a ≫ F.map f) x = (b ≫ F.map f) x) :
    ∃ (j : J) (f : i ⟶ j), ∀ x ∈ E, (a ≫ F.map f) x = (b ≫ F.map f) x := by
  classical
  induction E using Finset.induction_on with
  | empty =>
      -- The empty generating set needs no synchronization.
      refine ⟨i, 𝟙 i, ?_⟩
      simp
  | @insert x E hx ih =>
      -- Synchronize the tail first, then merge the new witness through filteredness.
      have hx :
          ∃ (j : J) (f : i ⟶ j), (a ≫ F.map f) x = (b ≫ F.map f) x :=
        hE x (Finset.mem_insert_self _ _)
      have htail :
          ∀ y ∈ E, ∃ (j : J) (f : i ⟶ j), (a ≫ F.map f) y = (b ≫ F.map f) y := by
        intro y hy
        exact hE y (Finset.mem_insert_of_mem hy)
      obtain ⟨j₁, f₁, hf₁⟩ := ih htail
      obtain ⟨j₂, f₂, hf₂⟩ := hx
      let k : J := IsFiltered.max j₁ j₂
      let g₁ : j₁ ⟶ k := IsFiltered.leftToMax j₁ j₂
      let g₂ : j₂ ⟶ k := IsFiltered.rightToMax j₁ j₂
      let l : J := IsFiltered.coeq (f₁ ≫ g₁) (f₂ ≫ g₂)
      let q : k ⟶ l := IsFiltered.coeqHom (f₁ ≫ g₁) (f₂ ≫ g₂)
      refine ⟨l, f₁ ≫ g₁ ≫ q, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with hyx | hyE
      · -- Route correction: the new generator is controlled through its own witness, then
        -- transported to the synchronized arrow by the coequalizer relation.
        subst y
        have hxk :
            (a ≫ F.map (f₂ ≫ g₂)) x = (b ≫ F.map (f₂ ≫ g₂)) x := by
          simpa [Functor.map_comp, Category.assoc] using
            congrArg (fun z ↦ (F.map g₂) z) hf₂
        have hxl :
            (a ≫ F.map (f₂ ≫ g₂ ≫ q)) x = (b ≫ F.map (f₂ ≫ g₂ ≫ q)) x := by
          simpa [Functor.map_comp, Category.assoc] using
            congrArg (fun z ↦ (F.map q) z) hxk
        have hcoeq : f₁ ≫ g₁ ≫ q = f₂ ≫ g₂ ≫ q := by
          simpa [Category.assoc] using IsFiltered.coeq_condition (f₁ ≫ g₁) (f₂ ≫ g₂)
        rw [hcoeq]
        exact hxl
      · -- Existing synchronized equalities remain equal after further postcomposition.
        have hyk :
            (a ≫ F.map (f₁ ≫ g₁)) y = (b ≫ F.map (f₁ ≫ g₁)) y := by
          simpa [Functor.map_comp, Category.assoc] using
            congrArg (fun z ↦ (F.map g₁) z) (hf₁ y hyE)
        simpa [Functor.map_comp, Category.assoc] using
          congrArg (fun z ↦ (F.map q) z) hyk

/-- Helper for Lemma 10.11.1: the additive forgetful functor out of `ModuleCat R` already
preserves the relevant filtered colimit. -/
lemma modulecat_forget2_preserves_colimit
    {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ ModuleCat.{v} R) :
    PreservesColimit F (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}) := by
  -- The generic `ModuleCat` colimit API already handles the additive layer.
  infer_instance

/-- Helper for Lemma 10.11.1: the forgetful functor from `ModuleCat R` preserves each filtered
colimit needed by the forward implication. -/
lemma modulecat_forget_preserves_colimit_filtered
    {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ ModuleCat.{v} R) :
    PreservesColimit F (forget (ModuleCat.{v} R)) := by
  -- Route correction: the blocker is the composite forgetful functor, not a new cocone model.
  haveI : PreservesColimit F (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}) :=
    modulecat_forget2_preserves_colimit (R := R) F
  haveI :
      PreservesColimit (F ⋙ forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})
        (forget AddCommGrpCat.{v}) := by
    -- Filtered colimits in additive commutative groups are preserved by forgetting to types.
    infer_instance
  -- The usual forgetful functor is definitionally the composite through additive groups.
  simpa using
    (show PreservesColimit F
      ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}) ⋙ forget AddCommGrpCat.{v}) from
      inferInstance)

/-- Helper for Lemma 10.11.1: a linear map out of `N` is zero once it vanishes on a finite
spanning set. -/
lemma linear_map_eq_zero_of_vanishes_on_spanning_finset {M : ModuleCat R} {E : Finset N}
    (hspan : Submodule.span R (E : Set N) = ⊤) (g : N ⟶ M) (hg : ∀ x ∈ E, g x = 0) :
    g = 0 := by
  apply ModuleCat.hom_ext
  ext x
  have hx : x ∈ Submodule.span R (E : Set N) := by
    rw [hspan]
    simp
  -- Every element of `N` lies in the span of the generators, so span induction propagates the
  -- vanishing of `g` from the generators to all of `N`.
  exact Submodule.span_induction
    (fun y hy ↦ hg y hy)
    (by simpa using g.map_zero)
    (fun y z _ _ hy hz ↦ by simpa [map_add, hy, hz])
    (fun r y _ hy ↦ by simpa [map_smul, hy])
    hx

/-- Helper for Lemma 10.11.1: after passing to a sufficiently large stage, two maps from a finite
module into one stage of a filtered colimit agree whenever they agree in the colimit. -/
lemma eventually_equal_of_hom_to_colimit_of_finite_module [Module.Finite R N]
    {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ ModuleCat R) {i : J}
    (a b : N ⟶ F.obj i) (h : a ≫ colimit.ι F i = b ≫ colimit.ι F i) :
    ∃ (j : J) (f : i ⟶ j), a ≫ F.map f = b ≫ F.map f := by
  -- Route correction: the source proof only needs the single map `a - b` to become zero on
  -- finitely many generators, not a stronger same-stage representative equality bridge.
  classical
  letI : PreservesColimit F (forget (ModuleCat R)) :=
    modulecat_forget_preserves_colimit_filtered (R := R) F
  let δ : N ⟶ F.obj i := a - b
  have hδ_colim : δ ≫ colimit.ι F i = 0 := by
    -- Equality in the colimit means the difference map is already zero there.
    apply ModuleCat.hom_ext
    ext x
    have hx : (a ≫ colimit.ι F i) x = (b ≫ colimit.ι F i) x :=
      LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp h) x
    simpa [δ] using sub_eq_zero.mpr hx
  obtain ⟨E, hEspan⟩ := Module.Finite.fg_top (R := R) (M := N)
  have hE :
      ∀ x ∈ E, ∃ (j : J) (f : i ⟶ j), (δ ≫ F.map f) x = ((0 : N ⟶ F.obj i) ≫ F.map f) x := by
    intro x hx
    have hx_colim : colimit.ι F i (δ x) = 0 := by
      exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp hδ_colim) x
    obtain ⟨j, f, hf⟩ :=
      CategoryTheory.Limits.Concrete.colimit_rep_eq_zero
        (R := R) (F := F) i (δ x) hx_colim
    refine ⟨j, f, ?_⟩
    simpa using hf
  obtain ⟨j, f, hf⟩ :=
    synchronize_generator_equalities (N := N) F δ 0 (E := E) hE
  have hδ_zero_on_generators : ∀ x ∈ E, (δ ≫ F.map f) x = 0 := by
    intro x hx
    simpa using hf x hx
  have hδ_zero : δ ≫ F.map f = 0 :=
    linear_map_eq_zero_of_vanishes_on_spanning_finset
      (R := R) (N := N) (M := F.obj j) hEspan (δ ≫ F.map f) hδ_zero_on_generators
  refine ⟨j, f, ?_⟩
  -- Once the difference vanishes at one later stage, the two maps agree there.
  apply ModuleCat.hom_ext
  ext x
  have hx : (δ ≫ F.map f) x = 0 :=
    LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp hδ_zero) x
  exact sub_eq_zero.mp <| by simpa [δ] using hx

/-- Helper for Lemma 10.11.1: inclusion of finite subsets gives inclusion of the corresponding
spans. -/
lemma finite_span_le_of_subset {E E' : Finset N} (h : E ⊆ E') :
    Submodule.span R (E : Set N) ≤ Submodule.span R (E' : Set N) :=
  Submodule.span_mono fun x hx ↦ h hx

/-- Helper for Lemma 10.11.1: the filtered diagram of quotients by spans of finite subsets. -/
lemma finite_span_le_comap_id_of_subset {E E' : Finset N} (h : E ⊆ E') :
    Submodule.span R (E : Set N) ≤
      (Submodule.span R (E' : Set N)).comap (LinearMap.id : N →ₗ[R] N) := by
  intro x hx
  change x ∈ Submodule.span R (E' : Set N)
  exact finite_span_le_of_subset (R := R) (N := N) h hx

/-- Helper for Lemma 10.11.1: the quotient map induced by enlarging the chosen finite subset. -/
def finite_span_quotient_map [DecidableEq N] {E E' : Finset N} (h : E ⊆ E') :
    ModuleCat.of R (N ⧸ Submodule.span R (E : Set N)) ⟶
      ModuleCat.of R (N ⧸ Submodule.span R (E' : Set N)) :=
  ModuleCat.ofHom <|
    Submodule.mapQ (Submodule.span R (E : Set N)) (Submodule.span R (E' : Set N))
      LinearMap.id (finite_span_le_comap_id_of_subset (R := R) (N := N) h)

/-- Helper for Lemma 10.11.1: the identity inclusion induces the identity quotient map. -/
lemma finite_span_quotient_map_id [DecidableEq N] (E : Finset N) :
    finite_span_quotient_map (R := R) (N := N) (E := E) (E' := E) (fun _ hx ↦ hx) = 𝟙 _ := by
  apply ModuleCat.hom_ext
  simpa [finite_span_quotient_map] using
    (Submodule.mapQ_id
      (p := Submodule.span R (E : Set N))
      (h := finite_span_le_comap_id_of_subset (R := R) (N := N) (fun _ hx ↦ hx)))

/-- Helper for Lemma 10.11.1: quotient maps compose under nested finite subsets. -/
lemma finite_span_quotient_map_comp [DecidableEq N] {E E' E'' : Finset N}
    (h₁ : E ⊆ E') (h₂ : E' ⊆ E'') :
    finite_span_quotient_map (R := R) (N := N) (E := E) (E' := E'') (h₁.trans h₂) =
      finite_span_quotient_map (R := R) (N := N) (E := E) (E' := E') h₁ ≫
        finite_span_quotient_map (R := R) (N := N) (E := E') (E' := E'') h₂ := by
  apply ModuleCat.hom_ext
  simpa [finite_span_quotient_map, LinearMap.comp_assoc] using
    (Submodule.mapQ_comp
      (p := Submodule.span R (E : Set N))
      (p₂ := Submodule.span R (E' : Set N))
      (p₃ := Submodule.span R (E'' : Set N))
      (f := LinearMap.id)
      (g := LinearMap.id)
      (hf := finite_span_le_comap_id_of_subset (R := R) (N := N) h₁)
      (hg := finite_span_le_comap_id_of_subset (R := R) (N := N) h₂))

/-- Helper for Lemma 10.11.1: the filtered diagram `E ↦ N / span(E)` indexed by finite subsets. -/
def finite_span_quotient_diagram [DecidableEq N] : Finset N ⥤ ModuleCat R where
  obj E := ModuleCat.of R (N ⧸ Submodule.span R (E : Set N))
  map {E E'} h := finite_span_quotient_map (R := R) (N := N) h.le
  map_id E := finite_span_quotient_map_id (R := R) (N := N) E
  map_comp h g := finite_span_quotient_map_comp (R := R) (N := N) h.le g.le

/-- Helper for Lemma 10.11.1: the zero cocone on the finite-span quotient diagram is natural. -/
lemma finite_span_quotient_zero_cocone_naturality [DecidableEq N] {E E' : Finset N} (f : E ⟶ E') :
    (0 : (finite_span_quotient_diagram (R := R) (N := N)).obj E ⟶ ModuleCat.of R PUnit) ≫
        0 =
      (finite_span_quotient_diagram (R := R) (N := N)).map f ≫
        (0 : (finite_span_quotient_diagram (R := R) (N := N)).obj E' ⟶ ModuleCat.of R PUnit) := by
  rfl

/-- Helper for Lemma 10.11.1: the finite-span quotient diagram admits the canonical zero cocone. -/
def finite_span_quotient_zero_cocone [DecidableEq N] :
    Cocone (finite_span_quotient_diagram (R := R) (N := N)) :=
  { pt := ModuleCat.of R PUnit
    ι :=
      { app := fun _ ↦ 0
        naturality := fun _ _ f ↦
          finite_span_quotient_zero_cocone_naturality (R := R) (N := N) f } }

/-- Helper for Lemma 10.11.1: every element of a finite-span quotient becomes zero after adjoining
one representative to the chosen finite subset. -/
lemma finite_span_quotient_eventually_zero [DecidableEq N] (E : Finset N)
    (q : (finite_span_quotient_diagram (R := R) (N := N)).obj E) :
    ∃ (E' : Finset N) (f : E ⟶ E'),
      (finite_span_quotient_diagram (R := R) (N := N)).map f q = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (Submodule.span R (E : Set N)) q
  let E' : Finset N := insert x E
  let f : E ⟶ E' := homOfLE (Finset.subset_insert x E)
  refine ⟨E', f, ?_⟩
  change
    finite_span_quotient_map (R := R) (N := N) (E := E) (E' := E')
        (Finset.subset_insert x E) ((Submodule.span R (E : Set N)).mkQ x) = 0
  -- The chosen representative lies in the larger span, so its quotient class vanishes there.
  change (Submodule.span R (E' : Set N)).mkQ x = 0
  exact (Submodule.Quotient.mk_eq_zero _).2 <| Submodule.subset_span <| by
    simp [E']

/-- Helper for Lemma 10.11.1: the zero cocone on the finite-span quotient diagram is colimiting. -/
lemma finite_span_quotient_zero_cocone_isColimit [DecidableEq N] :
    Nonempty (IsColimit (finite_span_quotient_zero_cocone (R := R) (N := N))) := by
  classical
  refine ⟨?_⟩
  refine
    { desc := fun s ↦ 0
      fac := ?_
      uniq := ?_ }
  · intro s E
    -- Every cocone leg must vanish because every quotient class becomes zero at a later stage.
    apply ModuleCat.hom_ext
    ext q
    obtain ⟨E', f, hf⟩ := finite_span_quotient_eventually_zero (R := R) (N := N) E q
    let Q := finite_span_quotient_diagram (R := R) (N := N)
    have hw := ModuleCat.hom_ext_iff.mp (s.w f)
    have hq :
        (s.ι.app E) q =
          (s.ι.app E') (Q.map f q) := by
      have hq' := LinearMap.congr_fun hw q
      change (Q.map f ≫ s.ι.app E') q = (s.ι.app E) q at hq'
      change (s.ι.app E) q = (Q.map f ≫ s.ι.app E') q
      exact hq'.symm
    have hs : (s.ι.app E) q = 0 := by
      calc
        (s.ι.app E) q = (s.ι.app E') (Q.map f q) := hq
        _ = (s.ι.app E') 0 := by simp [Q, hf]
        _ = 0 := by simpa using (s.ι.app E').hom.map_zero
    simpa using hs.symm
  · intro s m hm
    -- The source is the zero module, so any morphism out of it is forced to be zero.
    apply ModuleCat.hom_ext
    ext x
    cases x
    exact m.hom.map_zero

/-- Helper for Lemma 10.11.1: the empty-stage quotient map has zero image in the colimit of the
finite-span quotient diagram. -/
lemma empty_stage_quotient_map_eq_zero [DecidableEq N] :
    (ModuleCat.ofHom (Submodule.mkQ (Submodule.span R (((∅ : Finset N) : Set N)))) :
        N ⟶ (finite_span_quotient_diagram (R := R) (N := N)).obj ∅) ≫
      colimit.ι (finite_span_quotient_diagram (R := R) (N := N)) ∅ = 0 := by
  let Q := finite_span_quotient_diagram (R := R) (N := N)
  obtain ⟨hQ⟩ := finite_span_quotient_zero_cocone_isColimit (R := R) (N := N)
  let u := hQ.desc (colimit.cocone Q)
  -- The colimit coprojection from the empty stage factors through the zero cocone.
  have hι : colimit.ι Q ∅ = 0 := by
    apply ModuleCat.hom_ext
    ext q
    have hw := ModuleCat.hom_ext_iff.mp (hQ.fac (colimit.cocone Q) ∅)
    have hq := LinearMap.congr_fun hw q
    change (((finite_span_quotient_zero_cocone (R := R) (N := N)).ι.app ∅) ≫ u) q =
        (colimit.ι Q ∅) q at hq
    have hzero :
        (((finite_span_quotient_zero_cocone (R := R) (N := N)).ι.app ∅) ≫ u) q = 0 := by
      change u (((finite_span_quotient_zero_cocone (R := R) (N := N)).ι.app ∅) q) = 0
      rw [show ((finite_span_quotient_zero_cocone (R := R) (N := N)).ι.app ∅) q = 0 by
        rfl]
      exact u.hom.map_zero
    exact hq.symm.trans hzero
  -- Postcompose the empty-stage quotient map with this zero coprojection.
  rw [hι]
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- Helper for Lemma 10.11.1: the empty-stage quotient map becomes the later-stage quotient map
after applying the transition map out of the empty stage. -/
lemma empty_stage_transition_comp_eq_mkQ [DecidableEq N] {E : Finset N} (f : (∅ : Finset N) ⟶ E) :
    (ModuleCat.ofHom (Submodule.mkQ (Submodule.span R (((∅ : Finset N) : Set N)))) :
        N ⟶ (finite_span_quotient_diagram (R := R) (N := N)).obj ∅) ≫
      (finite_span_quotient_diagram (R := R) (N := N)).map f =
        ModuleCat.ofHom (Submodule.mkQ (Submodule.span R (E : Set N))) := by
  -- Unfold the transition map and identify the composite with the induced quotient map.
  apply ModuleCat.hom_ext
  simpa [finite_span_quotient_diagram, finite_span_quotient_map, LinearMap.comp_assoc] using
    (Submodule.mapQ_mkQ
      (p := Submodule.span R (((∅ : Finset N) : Set N)))
      (q := Submodule.span R (E : Set N))
      (f := LinearMap.id)
      (h := finite_span_le_comap_id_of_subset (R := R) (N := N) f.le))

-- Source/core/bridge triage:
-- * primitive owner data: `Module.Finite R N`
-- * core/canonical owner map: `colimit.post F (coyoneda.obj (op N))`
-- * source-facing bridge: injectivity of that comparison map for filtered colimits
--
-- This item already uses the canonical owner object `ModuleCat R` and the canonical comparison
-- map from 19.2.0.1, so the refinement here is to use `colimit.post` directly rather than keep a
-- parallel local wrapper API.
-- Proof sketch: for the forward implication, choose finitely many generators of `N` and use
-- filteredness to find one stage where all of their images vanish, which forces eventual
-- vanishing of the whole map. For the converse, apply the injectivity criterion to the filtered
-- system of quotients `N / N_E` indexed by finite subsets `E ⊆ N`; the identity of `N` must come
-- from one stage, showing that some finite subset generates `N`.
/-- Lemma 10.11.1: an `R`-module `N` is finite if and only if for every filtered colimit of
`R`-modules, the canonical map `colim_i Hom_R(N, M_i) → Hom_R(N, colim_i M_i)` is injective. -/
lemma module_finite_iff_injective_filteredColimitHomComparison :
    Module.Finite R N ↔
      ∀ ⦃J : Type v⦄ [SmallCategory J] [IsFiltered J] (F : J ⥤ ModuleCat R),
        Function.Injective (colimit.post F (coyoneda.obj (op N))) := by
  constructor
  · intro hN J _ _ F
    -- Reduce source-colimit equality to one common stage, then use finite generation to
    -- synchronize the resulting stagewise equalities.
    letI : Module.Finite R N := hN
    intro x y hxy
    obtain ⟨i, a, b, rfl, rfl⟩ :=
      Types.FilteredColimit.jointly_surjective_of_isColimit₂
        (F := F ⋙ coyoneda.obj (op N))
        (colimit.isColimit (F ⋙ coyoneda.obj (op N))) x y
    have ha_post :
        (colimit.post F (coyoneda.obj (op N)))
            (colimit.ι (F ⋙ coyoneda.obj (op N)) i a) =
          a ≫ colimit.ι F i := by
      simpa using colimit_post_coyoneda_ι_app (A := N) (B := F) i a
    have hb_post :
        (colimit.post F (coyoneda.obj (op N)))
            (colimit.ι (F ⋙ coyoneda.obj (op N)) i b) =
          b ≫ colimit.ι F i := by
      simpa using colimit_post_coyoneda_ι_app (A := N) (B := F) i b
    have hcolim : a ≫ colimit.ι F i = b ≫ colimit.ι F i := by
      have hmid :
          (colimit.post F (coyoneda.obj (op N)))
              (colimit.ι (F ⋙ coyoneda.obj (op N)) i a) =
            (colimit.post F (coyoneda.obj (op N)))
              (colimit.ι (F ⋙ coyoneda.obj (op N)) i b) := by
        simpa [hxy]
      exact ha_post.symm.trans (hmid.trans hb_post)
    obtain ⟨j, f, hf⟩ :=
      eventually_equal_of_hom_to_colimit_of_finite_module (R := R) (N := N) F a b hcolim
    have hstage :
        ((coyoneda.obj (op N)).map (F.map f)) a =
          ((coyoneda.obj (op N)).map (F.map f)) b := by
      simpa using hf
    exact
      (Types.FilteredColimit.isColimit_eq_iff'
        (F := F ⋙ coyoneda.obj (op N))
        (t := colimit.cocone (F ⋙ coyoneda.obj (op N)))
        (ht := colimit.isColimit (F ⋙ coyoneda.obj (op N)))
        a b).2 ⟨j, f, hstage⟩
  · intro hcmp
    classical
    rw [Module.finite_def]
    let Q := finite_span_quotient_diagram (R := R) (N := N)
    let q₀ :
        N ⟶ Q.obj ∅ :=
      ModuleCat.ofHom (Submodule.mkQ (Submodule.span R (((∅ : Finset N) : Set N))))
    have hq₀_post :
        (colimit.post Q (coyoneda.obj (op N)))
            (colimit.ι (Q ⋙ coyoneda.obj (op N)) ∅ q₀) =
          q₀ ≫ colimit.ι Q ∅ := by
      simpa using colimit_post_coyoneda_ι_app (A := N) (B := Q) ∅ q₀
    have hzero_post :
        (colimit.post Q (coyoneda.obj (op N)))
            (colimit.ι (Q ⋙ coyoneda.obj (op N)) ∅ (0 : N ⟶ Q.obj ∅)) =
          (0 : N ⟶ Q.obj ∅) ≫ colimit.ι Q ∅ := by
      simpa using
        colimit_post_coyoneda_ι_app (A := N) (B := Q) ∅ (0 : N ⟶ Q.obj ∅)
    have hq₀_zero : q₀ ≫ colimit.ι Q ∅ = 0 := by
      simpa [Q, q₀] using empty_stage_quotient_map_eq_zero (R := R) (N := N)
    -- Compare the empty-stage quotient map with the zero morphism in the source colimit.
    have himage :
        (colimit.post Q (coyoneda.obj (op N)))
            (colimit.ι (Q ⋙ coyoneda.obj (op N)) ∅ q₀) =
          (colimit.post Q (coyoneda.obj (op N)))
            (colimit.ι (Q ⋙ coyoneda.obj (op N)) ∅ (0 : N ⟶ Q.obj ∅)) := by
      rw [hq₀_post, hzero_post]
      -- The empty-stage quotient map is already zero in the colimit of the quotient diagram.
      simp [hq₀_zero]
    have hsource :
        colimit.ι (Q ⋙ coyoneda.obj (op N)) ∅ q₀ =
          colimit.ι (Q ⋙ coyoneda.obj (op N)) ∅ (0 : N ⟶ Q.obj ∅) :=
      hcmp Q himage
    -- Equality in the source colimit gives a later stage where the quotient map is zero.
    obtain ⟨E, f, hf⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff'
        (F := Q ⋙ coyoneda.obj (op N))
        (t := colimit.cocone (Q ⋙ coyoneda.obj (op N)))
        (ht := colimit.isColimit (Q ⋙ coyoneda.obj (op N)))
        q₀ (0 : N ⟶ Q.obj ∅)).1 hsource
    have hmkQ_zero :
        ModuleCat.ofHom (Submodule.mkQ (Submodule.span R (E : Set N))) = 0 := by
      -- Rewrite the eventual equality back to the concrete quotient map at stage `E`.
      simpa [Q, q₀] using
        (empty_stage_transition_comp_eq_mkQ (R := R) (N := N) f).trans (by simpa using hf)
    have hspan_top : Submodule.span R (E : Set N) = ⊤ := by
      -- The quotient map is zero exactly when its kernel, hence the chosen span, is all of `N`.
      have hker_top : LinearMap.ker (Submodule.mkQ (Submodule.span R (E : Set N))) = ⊤ := by
        rw [LinearMap.ker_eq_top]
        exact ModuleCat.hom_ext_iff.mp hmkQ_zero
      simpa using hker_top
    -- The finite subset `E` therefore generates the whole module.
    simpa [hspan_top] using
      (Submodule.fg_span (E.finite_toSet) : (Submodule.span R (E : Set N)).FG)

end FiniteModule

/-! ### Definition_10_11_2 (from Chap10) -/
universe u v w

section ModuleRelations

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {ι : Type w} [Fintype ι]

/- Definition 10.11.2: for a finite family `x : ι → M`, a relation is a coefficient family
`f : ι → R` whose associated linear combination of the `x i` is zero. The owner construction is
the canonical linear map `Fintype.linearCombination`. -/
recall Fintype.linearCombination

variable (x : ι → M) (f : ι → R)

/-- A coefficient family is a relation exactly when its explicit finite sum vanishes. -/
@[simp] theorem linearCombination_eq_zero_iff_sum_eq_zero :
    Fintype.linearCombination R x f = 0 ↔ ∑ i, f i • x i = 0 := by
  rw [Fintype.linearCombination_apply]

end ModuleRelations

/-! ### Lemma_10_11_3 (from Chap10) -/
open CategoryTheory.ObjectProperty
open CategoryTheory
open CategoryTheory.Limits

universe u v

section

variable (R : Type u) [Ring R]
variable (M : ModuleCat.{max u v} R)

/-- Helper for Lemma 10.11.3: a finite stage records finitely many generators of `M`, finitely
many relations among them, and the fact that those relations vanish in `M`. -/
private structure FinitePresentationStage where
  generators : Finset M
  relations : Submodule R (generators →₀ R)
  relations_fg : relations.FG
  relations_le_ker :
    relations ≤ LinearMap.ker (Finsupp.linearCombination R (fun s : generators ↦ (s : M)))

namespace FinitePresentationStage

variable {R M}

/-- Helper for Lemma 10.11.3: the generator embedding attached to an inclusion of finite generator
sets. -/
private def generatorEmbedding (i j : FinitePresentationStage R M)
    (h : i.generators ⊆ j.generators) : i.generators ↪ j.generators where
  toFun s := ⟨s, h s.property⟩
  inj' := by
    intro s t hst
    exact Subtype.ext (by simpa using hst)

/-- Helper for Lemma 10.11.3: enlarging the generator set induces a linear map on the free
modules on those generators. -/
private noncomputable def generatorMap (i j : FinitePresentationStage R M)
    (h : i.generators ⊆ j.generators) :
    (i.generators →₀ R) →ₗ[R] (j.generators →₀ R) :=
  Finsupp.lmapDomain R R (generatorEmbedding i j h)

/-- Helper for Lemma 10.11.3: enlarging generators does not change the induced linear combination
map to `M`. -/
private lemma generatorMap_linearCombination
    (i j : FinitePresentationStage R M)
    (h : i.generators ⊆ j.generators) :
    (Finsupp.linearCombination R (fun s : j.generators ↦ (s : M))).comp
        (generatorMap i j h) =
      Finsupp.linearCombination R (fun s : i.generators ↦ (s : M)) := by
  -- The source proof repeatedly enlarges finite generating sets, so we record the corresponding
  -- compatibility of the free-module maps with the tautological map to `M`.
  simpa [generatorMap, generatorEmbedding]
    using (Finsupp.linearCombination_comp_lmapDomain (R := R)
      (v' := fun s : j.generators ↦ (s : M)) (f := generatorEmbedding i j h))

/-- Helper for Lemma 10.11.3: enlarging a stage by the identity inclusion gives the identity map
on the free module. -/
private lemma generatorMap_id (i : FinitePresentationStage R M) :
    generatorMap i i (fun _ hx ↦ hx) = LinearMap.id := by
  -- On each basis vector, the identity inclusion leaves the generator unchanged.
  ext x s
  simp [generatorMap, generatorEmbedding]

/-- Helper for Lemma 10.11.3: the free-module map only depends on the underlying inclusion of
generator sets, not on a particular proof of that inclusion. -/
private lemma generatorMap_congr
    (i j : FinitePresentationStage R M)
    {h h' : i.generators ⊆ j.generators} :
    generatorMap i j h = generatorMap i j h' := by
  -- Proof irrelevance reduces both maps to the same embedding on generators.
  ext x s
  simp [generatorMap, generatorEmbedding]

/-- Helper for Lemma 10.11.3: any self-inclusion of the generator set induces the identity on the
free module. -/
private lemma generatorMap_self
    (i : FinitePresentationStage R M)
    (h : i.generators ⊆ i.generators) :
    generatorMap i i h = LinearMap.id := by
  -- A self-inclusion fixes every generator, so it fixes every free linear combination.
  ext x s
  simp [generatorMap, generatorEmbedding]

/-- Helper for Lemma 10.11.3: generator enlargement composes as expected. -/
private lemma generatorMap_comp
    (i j k : FinitePresentationStage R M)
    (hij : i.generators ⊆ j.generators) (hjk : j.generators ⊆ k.generators) :
    generatorMap (i := i) (j := k) (fun _ hx ↦ hjk (hij hx)) =
      (generatorMap (i := j) (j := k) hjk).comp (generatorMap (i := i) (j := j) hij) := by
  -- The source-proof route uses repeated enlargements of the finite generating set, so we record
  -- the corresponding linear-map composition explicitly.
  ext x s
  simpa [generatorMap, generatorEmbedding]
    using DFunLike.congr_fun (DFunLike.congr_fun (Finsupp.lmapDomain_comp R R
      (generatorEmbedding i j hij) (generatorEmbedding j k hjk)) x) s

/-- Helper for Lemma 10.11.3: the empty generator set with no relations gives a base stage. -/
private noncomputable def botStage : FinitePresentationStage R M where
  generators := ∅
  relations := ⊥
  relations_fg := by simpa using (Submodule.fg_bot : (⊥ : Submodule R ((∅ : Finset M) →₀ R)).FG)
  relations_le_ker := by
    simpa using (bot_le :
      (⊥ : Submodule R ((∅ : Finset M) →₀ R)) ≤
        LinearMap.ker (Finsupp.linearCombination R (fun s : (∅ : Finset M) ↦ (s : M))))

/-- Helper for Lemma 10.11.3: the explicit stage type is nonempty via the empty stage. -/
instance : Nonempty (FinitePresentationStage R M) :=
  ⟨botStage (R := R) (M := M)⟩

/-- Helper for Lemma 10.11.3: the explicit stages should be ordered by generator enlargement and
transported-relation inclusion. -/
noncomputable instance instPreorder : Preorder (FinitePresentationStage R M) := by
  refine
    { le := fun i j ↦ ∃ hgen : i.generators ⊆ j.generators,
          i.relations ≤ j.relations.comap (generatorMap i j hgen)
      le_refl := ?_
      le_trans := ?_ }
  · intro i
    -- The identity enlargement gives the reflexive stage relation.
    refine ⟨fun _ hx ↦ hx, ?_⟩
    simpa [generatorMap_id] using le_rfl
  · intro i j k hij hjk
    rcases hij with ⟨hij_gen, hij_rel⟩
    rcases hjk with ⟨hjk_gen, hjk_rel⟩
    -- Transported relation inclusion composes along enlargements of generator sets.
    refine ⟨fun _ hx ↦ hjk_gen (hij_gen hx), ?_⟩
    refine hij_rel.trans ?_
    simpa [generatorMap_comp, Submodule.comap_comp]
      using Submodule.comap_mono hjk_rel

/-- Helper for Lemma 10.11.3: the explicit stages form a directed preorder. -/
noncomputable instance instIsDirectedOrder : IsDirectedOrder (FinitePresentationStage R M) := by
  classical
  refine ⟨?_⟩
  intro i j
  let _ : DecidableEq M := Classical.decEq M
  let gens : Finset M := i.generators ∪ j.generators
  let higen : i.generators ⊆ gens := Finset.subset_union_left
  let hjgen : j.generators ⊆ gens := Finset.subset_union_right
  let embi : i.generators ↪ gens :=
    { toFun := fun s ↦ ⟨s, higen s.property⟩
      inj' := fun _ _ hst ↦ Subtype.ext (by simpa using hst) }
  let embj : j.generators ↪ gens :=
    { toFun := fun s ↦ ⟨s, hjgen s.property⟩
      inj' := fun _ _ hst ↦ Subtype.ext (by simpa using hst) }
  let gmi : (i.generators →₀ R) →ₗ[R] (gens →₀ R) := Finsupp.lmapDomain R R embi
  let gmj : (j.generators →₀ R) →ₗ[R] (gens →₀ R) := Finsupp.lmapDomain R R embj
  let lc : (gens →₀ R) →ₗ[R] M := Finsupp.linearCombination R (fun s : gens ↦ (s : M))
  let reli : Submodule R (gens →₀ R) := i.relations.map gmi
  let relj : Submodule R (gens →₀ R) := j.relations.map gmj
  have hfg : (reli ⊔ relj).FG := by
    -- The source upper bound stage transports each finite relation module into the union stage.
    exact (i.relations_fg.map gmi).sup (j.relations_fg.map gmj)
  have hlc_i :
      lc.comp gmi =
        Finsupp.linearCombination R (fun s : i.generators ↦ (s : M)) := by
    -- Enlarging generators to the union stage does not change the induced linear combination.
    simpa [lc, gmi, embi]
      using (Finsupp.linearCombination_comp_lmapDomain (R := R)
        (v' := fun s : gens ↦ (s : M)) (f := embi))
  have hlc_j :
      lc.comp gmj =
        Finsupp.linearCombination R (fun s : j.generators ↦ (s : M)) := by
    -- The same compatibility holds for the second stage.
    simpa [lc, gmj, embj]
      using (Finsupp.linearCombination_comp_lmapDomain (R := R)
        (v' := fun s : gens ↦ (s : M)) (f := embj))
  have hker :
      reli ⊔ relj ≤ LinearMap.ker lc := by
    intro x hx
    rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
    have hy0 : lc y = 0 := by
      rcases Submodule.mem_map.mp hy with ⟨y', hy', rfl⟩
      -- Transported relations from `i` still vanish after passing to the union generators.
      calc
        lc (gmi y') = (Finsupp.linearCombination R (fun s : i.generators ↦ (s : M))) y' := by
          exact congrArg (fun f ↦ f y') hlc_i
        _ = 0 := i.relations_le_ker hy'
    have hz0 : lc z = 0 := by
      rcases Submodule.mem_map.mp hz with ⟨z', hz', rfl⟩
      -- The transported relations from `j` vanish for the same reason.
      calc
        lc (gmj z') = (Finsupp.linearCombination R (fun s : j.generators ↦ (s : M))) z' := by
          exact congrArg (fun f ↦ f z') hlc_j
        _ = 0 := j.relations_le_ker hz'
    -- A sum of two vanishing transported relations still vanishes.
    calc
      lc (y + z) = lc y + lc z := by simp [lc]
      _ = 0 := by simp [hy0, hz0]
  let k : FinitePresentationStage R M :=
    { generators := gens
      relations := reli ⊔ relj
      relations_fg := hfg
      relations_le_ker := hker }
  have hgmi : generatorMap i k higen = gmi := by
    -- Once the target generator set is fixed, the canonical transported map is the same map.
    ext x s
    simp [generatorMap, generatorEmbedding, gmi, embi]
  have hgmj : generatorMap j k hjgen = gmj := by
    -- The same identification holds for the second stage.
    ext x s
    simp [generatorMap, generatorEmbedding, gmj, embj]
  refine ⟨k, ?_, ?_⟩
  · -- The first stage maps into the union stage because its transported relations land in the
    -- first summand of the supremum relation module.
    refine ⟨higen, ?_⟩
    exact Submodule.map_le_iff_le_comap.mp <| by
      simpa [k, reli, hgmi] using (le_sup_left : reli ≤ reli ⊔ relj)
  · -- Symmetrically, the second stage maps into the same union stage.
    refine ⟨hjgen, ?_⟩
    exact Submodule.map_le_iff_le_comap.mp <| by
      simpa [k, relj, hgmj] using (le_sup_right : relj ≤ reli ⊔ relj)

/-- Helper for Lemma 10.11.3: the explicit finite-generator/finite-relation stages form a
directed preorder. -/
lemma finite_presentation_stage_isDirectedOrder :
    IsDirectedOrder (FinitePresentationStage R M) := by
  infer_instance

/-- Helper for Lemma 10.11.3: the quotient module represented by a finite stage. -/
private noncomputable def obj (i : FinitePresentationStage R M) : ModuleCat.{max u v} R :=
  ModuleCat.of R ((i.generators →₀ R) ⧸ i.relations)

/-- Helper for Lemma 10.11.3: each stage quotient is finitely presented. -/
lemma finite_presentation_stage_finitePresentation (i : FinitePresentationStage R M) :
    Module.FinitePresentation R (obj (R := R) (M := M) i) := by
  -- Each stage is a quotient of a finite free module by a finitely generated submodule.
  exact Module.finitePresentation_of_surjective (Submodule.mkQ i.relations)
    (Submodule.mkQ_surjective _) <| by
      change (LinearMap.ker (Submodule.mkQ i.relations)).FG
      simpa [Submodule.ker_mkQ] using i.relations_fg

/-- Helper for Lemma 10.11.3: the morphism between stage quotients induced by enlarging a stage. -/
private noncomputable def map {i j : FinitePresentationStage R M} (h : i ≤ j) :
    obj (R := R) (M := M) i ⟶ obj (R := R) (M := M) j :=
  let hgen : i.generators ⊆ j.generators := Classical.choose h
  let hrel : i.relations ≤ j.relations.comap (generatorMap i j hgen) := Classical.choose_spec h
  -- The stage order is set up so that `Submodule.mapQ` gives the quotient map immediately.
  ModuleCat.ofHom <| Submodule.mapQ i.relations j.relations (generatorMap i j hgen) hrel

/-- Helper for Lemma 10.11.3: the stage map sends a quotient class to the class of the transported
free-module representative. -/
private lemma map_mkQ {i j : FinitePresentationStage R M} (h : i ≤ j)
    (x : i.generators →₀ R) :
    (map (R := R) (M := M) h) ((Submodule.mkQ i.relations) x) =
      (Submodule.mkQ j.relations) ((generatorMap i j (Classical.choose h)) x) := by
  -- This is exactly how `Submodule.mapQ` acts on quotient constructors.
  rfl

/-- Helper for Lemma 10.11.3: the explicit source-proof stages define a diagram in `ModuleCat`. -/
noncomputable def diagram : FinitePresentationStage R M ⥤ ModuleCat.{max u v} R where
  obj i := obj (R := R) (M := M) i
  map h := map (R := R) (M := M) (CategoryTheory.leOfHom h)
  map_id i := by
    -- The quotient map for the identity enlargement is the identity on quotient classes.
    apply ModuleCat.hom_ext
    ext x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective i.relations x
    simpa [generatorMap_self] using
      (map_mkQ (R := R) (M := M) (h := CategoryTheory.leOfHom (𝟙 i)) y)
  map_comp h₁ h₂ := by
    let hij := CategoryTheory.leOfHom h₁
    let hjk := CategoryTheory.leOfHom h₂
    let hik := CategoryTheory.leOfHom (h₁ ≫ h₂)
    let hXZ := Classical.choose hik
    let hXY := Classical.choose hij
    let hYZ := Classical.choose hjk
    have hcomp :
        generatorMap _ _ hXZ = (generatorMap _ _ hYZ).comp (generatorMap _ _ hXY) := by
      -- The chosen proof for the composite order gives the same generator map as the explicit
      -- composite inclusion of finite generator sets.
      calc
        generatorMap _ _ hXZ = generatorMap _ _ (fun s hs ↦ hYZ (hXY hs)) := by
              simpa [hXZ, hXY, hYZ] using
                (generatorMap_congr (i := _) (j := _)
                  (h := hXZ) (h' := fun s hs ↦ hYZ (hXY hs)))
        _ = (generatorMap _ _ hYZ).comp (generatorMap _ _ hXY) := by
              simpa [hXY, hYZ] using generatorMap_comp _ _ _ hXY hYZ
    -- Both composites send a quotient class to the class of the twice-enlarged free-module
    -- representative, so it suffices to compare them on quotient constructors.
    apply ModuleCat.hom_ext
    ext x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [map_mkQ (R := R) (M := M) (h := hik) y, ModuleCat.comp_apply,
      map_mkQ (R := R) (M := M) (h := hij) y,
      map_mkQ (R := R) (M := M) (h := hjk) ((generatorMap _ _ hXY) y)]
    simp [hcomp]

/-- Helper for Lemma 10.11.3: the canonical map from a finite stage quotient to `M`. -/
private noncomputable def coconeLeg (i : FinitePresentationStage R M) :
    obj (R := R) (M := M) i ⟶ M :=
  ModuleCat.ofHom <|
    Submodule.liftQ i.relations
      (Finsupp.linearCombination R (fun s : i.generators ↦ (s : M)))
      i.relations_le_ker

/-- Helper for Lemma 10.11.3: the canonical cocone leg evaluates a quotient class by the
corresponding linear combination in `M`. -/
private lemma coconeLeg_mkQ (i : FinitePresentationStage R M) (x : i.generators →₀ R) :
    coconeLeg (R := R) (M := M) i ((Submodule.mkQ i.relations) x) =
      Finsupp.linearCombination R (fun s : i.generators ↦ (s : M)) x := by
  -- This is the defining computation rule for `Submodule.liftQ`.
  rfl

/-- Helper for Lemma 10.11.3: the canonical cocone from the explicit finite stages to `M`. -/
noncomputable def cocone : Cocone (diagram (R := R) (M := M)) :=
  Cocone.mk M
    { app := coconeLeg (R := R) (M := M)
      naturality := by
        intro i j h
        let hij : i ≤ j := CategoryTheory.leOfHom h
        let hgen : i.generators ⊆ j.generators := Classical.choose hij
        -- Both sides evaluate a quotient class by taking the corresponding linear combination in
        -- `M`; enlarging generators does not change that linear combination.
        apply ModuleCat.hom_ext
        ext x
        obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
        change
          coconeLeg (R := R) (M := M) j
              ((map (R := R) (M := M) hij) ((Submodule.mkQ i.relations) y)) =
            coconeLeg (R := R) (M := M) i ((Submodule.mkQ i.relations) y)
        rw [map_mkQ (R := R) (M := M) (h := hij) y, coconeLeg_mkQ (R := R) (M := M) j,
          coconeLeg_mkQ (R := R) (M := M) i]
        exact congrArg (fun f ↦ f y) (generatorMap_linearCombination i j hgen) }

/-- Helper for Lemma 10.11.3: the singleton finite set used for the stage generated by one
element of `M`. -/
private noncomputable def singletonGenerators (m : M) : Finset M :=
  let _ : DecidableEq M := Classical.decEq M
  {m}

/-- Helper for Lemma 10.11.3: the singleton stage has no relations, hence its relation module is
finitely generated. -/
private lemma singletonStage_relations_fg (m : M) :
    (⊥ : Submodule R ((singletonGenerators (R := R) (M := M) m) →₀ R)).FG := by
  simpa [singletonGenerators] using
    (Submodule.fg_bot :
      (⊥ : Submodule R ((singletonGenerators (R := R) (M := M) m) →₀ R)).FG)

/-- Helper for Lemma 10.11.3: the zero relation module on a singleton stage lies in the kernel of
the tautological linear-combination map. -/
private lemma singletonStage_relations_le_ker (m : M) :
    (⊥ : Submodule R ((singletonGenerators (R := R) (M := M) m) →₀ R)) ≤
      LinearMap.ker
        (Finsupp.linearCombination R
          (fun s : singletonGenerators (R := R) (M := M) m ↦ (s : M))) := by
  simpa using
    (bot_le :
      (⊥ : Submodule R ((singletonGenerators (R := R) (M := M) m) →₀ R)) ≤
        LinearMap.ker
          (Finsupp.linearCombination R
            (fun s : singletonGenerators (R := R) (M := M) m ↦ (s : M))))

/-- Helper for Lemma 10.11.3: the stage generated by one element of `M` with no relations. -/
private noncomputable def singletonStage (m : M) : FinitePresentationStage R M :=
  { generators := singletonGenerators (R := R) (M := M) m
    relations := ⊥
    relations_fg := singletonStage_relations_fg (R := R) (M := M) m
    relations_le_ker := singletonStage_relations_le_ker (R := R) (M := M) m }

/-- Helper for Lemma 10.11.3: the chosen generator lies in the singleton stage generated by
itself. -/
private lemma singletonGenerator_mem (m : M) :
    m ∈ (singletonStage (R := R) (M := M) m).generators := by
  classical
  simp [singletonStage, singletonGenerators]

/-- Helper for Lemma 10.11.3: the distinguished generator of the singleton stage. -/
private noncomputable def singletonGenerator (m : M) :
    (singletonStage (R := R) (M := M) m).generators :=
  ⟨m, singletonGenerator_mem (R := R) (M := M) m⟩

/-- Helper for Lemma 10.11.3: the quotient class of a basis generator in a stage quotient. -/
private noncomputable def generatorClass (i : FinitePresentationStage R M) (s : i.generators) :
    obj (R := R) (M := M) i :=
  (Submodule.mkQ i.relations) (Finsupp.single s 1)

/-- Helper for Lemma 10.11.3: a generator already present in a stage receives a canonical map from
its singleton stage. -/
private lemma singletonStage_le_of_mem {i : FinitePresentationStage R M} (s : i.generators) :
    singletonStage (R := R) (M := M) (s : M) ≤ i := by
  classical
  let hgen : (singletonStage (R := R) (M := M) (s : M)).generators ⊆ i.generators :=
    fun x hx ↦ by
      have hx' : (x : M) = s := by
        simpa [singletonStage, singletonGenerators] using hx
      simpa [hx'] using s.property
  refine ⟨hgen, ?_⟩
  -- The singleton stage has no relations, so the transported relation condition is automatic.
  simpa [singletonStage] using
    (bot_le :
      (⊥ :
        Submodule R
          ((singletonStage (R := R) (M := M) (s : M)).generators →₀ R)) ≤
        i.relations.comap
          (generatorMap (singletonStage (R := R) (M := M) (s : M)) i hgen))

/-- Helper for Lemma 10.11.3: transporting the singleton generator class into a larger stage gives
the corresponding generator class there. -/
private lemma singletonStage_map_generatorClass {i : FinitePresentationStage R M}
    (s : i.generators) :
    (map (R := R) (M := M) (singletonStage_le_of_mem (R := R) (M := M) (i := i) s))
      (generatorClass (R := R) (M := M)
        (singletonStage (R := R) (M := M) (s : M))
        (singletonGenerator (R := R) (M := M) (s : M))) =
      generatorClass (R := R) (M := M) i s :=
by
  let h :=
    singletonStage_le_of_mem (R := R) (M := M) (i := i) s
  let hgen :
      (singletonStage (R := R) (M := M) (s : M)).generators ⊆ i.generators :=
    Classical.choose h
  -- Route correction: first compute the transported singleton basis vector on the free module,
  -- then pass to quotient classes with `map_mkQ`.
  have hsingle :
      generatorMap (singletonStage (R := R) (M := M) (s : M)) i hgen
          (Finsupp.single (singletonGenerator (R := R) (M := M) (s : M)) (1 : R)) =
        Finsupp.single s (1 : R) := by
    -- The singleton inclusion sends the distinguished singleton generator to `s`.
    simp [generatorMap, generatorEmbedding, singletonGenerator]
  -- The quotient map is induced by the transported free-module representative.
  change
      (map (R := R) (M := M) h)
          ((Submodule.mkQ
              (singletonStage (R := R) (M := M) (s : M)).relations)
            (Finsupp.single (singletonGenerator (R := R) (M := M) (s : M)) (1 : R))) =
        (Submodule.mkQ i.relations) (Finsupp.single s (1 : R))
  rw [map_mkQ (R := R) (M := M) (h := h)]
  simpa [generatorClass] using congrArg (Submodule.mkQ i.relations) hsingle

/-- Helper for Lemma 10.11.3: evaluating a cocone on the singleton-stage generator gives the
candidate universal map on `M`. -/
private noncomputable def desc0 (t : Cocone (diagram (R := R) (M := M))) (m : M) : t.pt :=
  (t.ι.app (singletonStage (R := R) (M := M) m))
    (generatorClass (R := R) (M := M)
      (singletonStage (R := R) (M := M) m)
      (singletonGenerator (R := R) (M := M) m))

/-- Helper for Lemma 10.11.3: the singleton-stage formula is additive, using the pair stage with
relation `m + n - (m + n) = 0`. -/
private lemma singleton_desc_add
    (t : Cocone (diagram (R := R) (M := M))) (m n : M) :
    desc0 (R := R) (M := M) t (m + n) =
      desc0 (R := R) (M := M) t m + desc0 (R := R) (M := M) t n :=
  -- TODO: use the pair stage on `{m, n, m + n}` with relation `e_m + e_n - e_{m+n}` and
  -- naturality from the three singleton stages to show the displayed equality.
  sorry

/-- Helper for Lemma 10.11.3: the singleton-stage formula is `R`-linear in scalars, using the
stage with relation `r • m - (r • m) = 0`. -/
private lemma singleton_desc_smul
    (t : Cocone (diagram (R := R) (M := M))) (r : R) (m : M) :
    desc0 (R := R) (M := M) t (r • m) =
      r • desc0 (R := R) (M := M) t m :=
  -- TODO: use the stage on `{m, r • m}` with relation `r • e_m - e_{r • m}` and the same
  -- singleton-stage naturality argument as in `singleton_desc_add`.
  sorry

/-- Helper for Lemma 10.11.3: the singleton-stage formula packages into the universal linear map
out of `M` toward any cocone point. -/
private noncomputable def desc (t : Cocone (diagram (R := R) (M := M))) : M ⟶ t.pt :=
  ModuleCat.ofHom
    { toFun := desc0 (R := R) (M := M) t
      map_add' := singleton_desc_add (R := R) (M := M) t
      map_smul' := singleton_desc_smul (R := R) (M := M) t }

/-- Helper for Lemma 10.11.3: on a stage generator, the universal singleton-stage map agrees with
the corresponding cocone leg. -/
private lemma desc_agrees_on_generator_classes
    (t : Cocone (diagram (R := R) (M := M))) (i : FinitePresentationStage R M)
    (s : i.generators) :
    desc (R := R) (M := M) t (s : M) =
      (t.ι.app i) (generatorClass (R := R) (M := M) i s) :=
by
  let h := singletonStage_le_of_mem (R := R) (M := M) (i := i) s
  let f : singletonStage (R := R) (M := M) (s : M) ⟶ i := CategoryTheory.homOfLE h
  -- Cocone naturality identifies the singleton-stage value with the image of its transported
  -- generator class in the ambient stage.
  have hw := ModuleCat.hom_ext_iff.mp (t.w f)
  have hclass :=
    LinearMap.congr_fun hw
      (generatorClass (R := R) (M := M)
        (singletonStage (R := R) (M := M) (s : M))
        (singletonGenerator (R := R) (M := M) (s : M)))
  change
      (t.ι.app i)
          ((map (R := R) (M := M) h)
            (generatorClass (R := R) (M := M)
              (singletonStage (R := R) (M := M) (s : M))
              (singletonGenerator (R := R) (M := M) (s : M)))) =
        desc0 (R := R) (M := M) t (s : M) at hclass
  rw [singletonStage_map_generatorClass (R := R) (M := M) (i := i) s] at hclass
  simpa [desc, desc0] using hclass.symm

/-- Helper for Lemma 10.11.3: the canonical cocone on explicit finite stages should be colimiting.

The remaining work is the source-proof universal property: define the candidate desc map by
evaluating on singleton stages, then prove additivity and scalar compatibility using the standard
pair and scalar relation stages. -/
noncomputable def finite_presentation_stage_cocone_isColimit :
    IsColimit (cocone (R := R) (M := M)) :=
  -- TODO: define `desc` from the singleton-stage formula, prove `fac` by `Finsupp.induction_linear`
  -- on quotient representatives using `desc_agrees_on_generator_classes`, and prove `uniq` by
  -- evaluating the factorization identity on singleton generators.
  sorry

end FinitePresentationStage

-- Source-facing statement, expressed in the canonical owner abstraction `ObjectProperty.ind`.
-- Working directly with the bundled object `M : ModuleCat R` keeps the statement in the owner
-- category instead of repackaging an unbundled carrier as `ModuleCat.of R M`.
/-- Lemma 10.11.3: every `R`-module admits a filtered colimit presentation by finitely presented
`R`-modules. Equivalently, it is the colimit of a directed system of finitely presented
`R`-modules. -/
theorem module_is_isomorphic_to_colimit_of_directed_system_of_finitelyPresented :
    ind.{max u v} (fun N : ModuleCat.{max u v} R ↦ Module.FinitePresentation R N) M := by
  classical
  -- We follow the source proof literally: stages are finite generators plus finitely many
  -- relations, ordered by enlargement.
  let pres : ColimitPresentation (FinitePresentationStage R M) M :=
    { diag := FinitePresentationStage.diagram (R := R) (M := M)
      ι := (FinitePresentationStage.cocone (R := R) (M := M)).ι
      isColimit := FinitePresentationStage.finite_presentation_stage_cocone_isColimit
        (R := R) (M := M) }
  exact
    ⟨FinitePresentationStage R M, inferInstance, inferInstance, pres,
      fun i ↦ FinitePresentationStage.finite_presentation_stage_finitePresentation
        (R := R) (M := M) i⟩

end

/-! ### Lemma_10_11_4 (from Chap10) -/
open CategoryTheory CategoryTheory.Limits Opposite

universe u v

section

variable (R : Type u) (M : Type (max u v)) [Ring R] [AddCommGroup M] [Module R M]

/-- Helper for Lemma 10.11.4: if `r : Q → P` admits a section `s`, then `ker r` is the range of
the projector `id - s ∘ r`, so it is finitely generated once `Q` is finite. -/
lemma ker_fg_of_split_surjection
    {P Q : Type (max u v)} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q]
    (s : P →ₗ[R] Q) (r : Q →ₗ[R] P) (hsr : r.comp s = LinearMap.id) :
    (LinearMap.ker r).FG := by
  let e : Q →ₗ[R] Q := LinearMap.id - s.comp r
  have hsr_apply (x : P) : r (s x) = x := by
    -- The section identity is used pointwise to simplify the projector calculation.
    simpa using LinearMap.congr_fun hsr x
  have hker_range : LinearMap.ker r = LinearMap.range e := by
    ext x
    constructor
    · intro hx
      refine ⟨x, ?_⟩
      -- Elements of the kernel are fixed by `id - s ∘ r`.
      change x - s (r x) = x
      rw [show r x = 0 from hx, map_zero, sub_zero]
    · rintro ⟨y, rfl⟩
      -- The projector lands in `ker r` because `r ∘ s = id`.
      change r (e y) = 0
      simp [e, hsr_apply]
  -- A range of a map out of a finite module is finitely generated.
  simpa [hker_range] using (Submodule.fg_range e)

/-- Helper for Lemma 10.11.4: a split surjection from a finitely presented stage descends finite
presentation to the target module. -/
lemma module_finitePresentation_of_split_surjection_from_finitelyPresented_stage
    {P Q : Type (max u v)} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [Module.FinitePresentation R Q]
    (s : P →ₗ[R] Q) (r : Q →ₗ[R] P) (hsr : r.comp s = LinearMap.id) :
    Module.FinitePresentation R P := by
  have hr_surj : Function.Surjective r := by
    -- The section gives explicit preimages under `r`.
    intro x
    refine ⟨s x, ?_⟩
    simpa using LinearMap.congr_fun hsr x
  have hker_fg : (LinearMap.ker r).FG :=
    ker_fg_of_split_surjection (R := R) s r hsr
  -- Descend finite presentation across the split surjection.
  exact Module.finitePresentation_of_surjective r hr_surj hker_fg

/-- Helper for Lemma 10.11.4: two maps out of a quotient module agree once their composites with
the quotient map agree. -/
lemma linearMap_eq_of_comp_mkQ_eq
    {n : ℕ} {K : Submodule R (Fin n → R)} {P : Type (max u v)}
    [AddCommGroup P] [Module R P]
    {f g : ((Fin n → R) ⧸ K) →ₗ[R] P}
    (h : f.comp (Submodule.mkQ K) = g.comp (Submodule.mkQ K)) :
    f = g := by
  -- The quotient map is surjective, so it is enough to compare both maps on representatives.
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective K q
  simpa using LinearMap.congr_fun h x

/-- Helper for Lemma 10.11.4: a linear map from a finite free module into a filtered colimit of
modules factors through one stage. -/
lemma linearMap_from_fin_factor_through_filtered_colimit_stage
    {J : Type (max u v)} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{max u v} R) [HasColimit F]
    (n : ℕ) (f : (Fin n → R) →ₗ[R] (colimit F : ModuleCat.{max u v} R)) :
    ∃ (j : J) (g : (Fin n → R) →ₗ[R] F.obj j), (colimit.ι F j).hom.comp g = f := by
  classical
  letI : PreservesColimit F (forget (ModuleCat.{max u v} R)) :=
    modulecat_forget_preserves_colimit_filtered (R := R) F
  let hc :
      IsColimit ((forget (ModuleCat.{max u v} R)).mapCocone (colimit.cocone F)) :=
    isColimitOfPreserves (forget (ModuleCat.{max u v} R)) (colimit.isColimit F)
  choose j x hx using fun i : Fin n =>
    Types.jointly_surjective_of_isColimit hc (f ((Pi.basisFun R (Fin n)) i))
  obtain ⟨k, ⟨u⟩⟩ : ∃ k : J, Nonempty (∀ i : Fin n, j i ⟶ k) := by
    -- Filteredness merges the finitely many chosen lifts of the basis vectors into one stage.
    have : ∃ k : J, ∀ i : Fin n, Nonempty (j i ⟶ k) := by
      simpa using IsFiltered.sup_objs_exists (Finset.univ.image j)
    simpa [← exists_true_iff_nonempty, Classical.skolem, -exists_const_iff] using this
  let g : (Fin n → R) →ₗ[R] F.obj k :=
    { toFun := fun z => ∑ i, z i • (F.map (u i)) (x i)
      map_add' := by
        intro z z'
      -- The stagewise lift is defined by the standard linear combination of the chosen basis
      -- images at the common stage.
        simp [Finset.sum_add_distrib, add_smul]
      map_smul' := by
        intro r z
        simp [Finset.smul_sum, mul_smul] }
  refine ⟨k, g, ?_⟩
  -- The constructed map matches `f` on the standard basis, hence everywhere.
  apply (Pi.basisFun R (Fin n)).ext
  intro i
  have htransport :
      (colimit.ι F k).hom ((F.map (u i)) (x i)) =
        (colimit.ι F (j i)).hom (x i) := by
    -- Naturality of the colimit cocone transports each chosen lift to the common stage.
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (colimit.w F (u i))) (x i)
  calc
    ((colimit.ι F k).hom.comp g) ((Pi.basisFun R (Fin n)) i)
        = (colimit.ι F k).hom ((F.map (u i)) (x i)) := by
            simp [g, Pi.basisFun_apply]
    _ = (colimit.ι F (j i)).hom (x i) := htransport
    _ = f ((Pi.basisFun R (Fin n)) i) := hx i

/-- Helper for Lemma 10.11.4: if a finitely generated submodule of a finite free module vanishes in
the filtered colimit, then it already vanishes at some later stage. -/
lemma fg_submodule_eventually_le_ker_of_colimit_vanishing
    {n : ℕ} {K : Submodule R (Fin n → R)} (hK : K.FG)
    {J : Type (max u v)} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{max u v} R) [HasColimit F]
    {i : J}
    (g : (Fin n → R) →ₗ[R] F.obj i)
    (hg : K ≤ LinearMap.ker ((colimit.ι F i).hom.comp g)) :
    ∃ (j : J) (u : i ⟶ j), K ≤ LinearMap.ker ((F.map u).hom.comp g) := by
  letI : Module.Finite R K := Module.Finite.of_fg hK
  let a : ModuleCat.of R (ULift.{v} K) ⟶ F.obj i :=
    ModuleCat.ofHom (((g.comp K.subtype).comp ULift.moduleEquiv.toLinearMap))
  let b : ModuleCat.of R (ULift.{v} K) ⟶ F.obj i := 0
  have ha_colim : a ≫ colimit.ι F i = b ≫ colimit.ι F i := by
    apply ModuleCat.hom_ext
    ext x
    -- The restricted map is zero in the colimit because every relation already vanishes there.
    have hx0 : (colimit.ι F i).hom (g (K.subtype x.down)) = 0 := hg x.down.property
    simpa [a, b, Category.assoc] using hx0
  obtain ⟨j, u, hu⟩ :=
    eventually_equal_of_hom_to_colimit_of_finite_module
      (R := R) (N := ModuleCat.of R (ULift.{v} K)) F a b ha_colim
  refine ⟨j, u, ?_⟩
  intro x hx
  let xK : K := ⟨x, hx⟩
  have hxu :
      ((a ≫ F.map u).hom) (ULift.up xK) =
        ((b ≫ F.map u).hom) (ULift.up xK) :=
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hu) (ULift.up xK)
  -- Evaluating the eventual equality on a representative of `K` gives the desired kernel bound.
  simpa [a, b, Category.assoc] using hxu

/-- Helper for Lemma 10.11.4: the filtered-colimit comparison map is surjective for a quotient of a
finite free module by a finitely generated submodule. -/
lemma quotient_of_fin_surjective_filteredColimitHomComparison
    {n : ℕ} (K : Submodule R (Fin n → R)) (hK : K.FG)
    {J : Type (max u v)} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{max u v} R) [HasColimit F] :
    Function.Surjective
      (colimit.post F
        (coyoneda.obj
          (op (ModuleCat.of R (ULift.{v} ((Fin n → R) ⧸ K)))))) := by
  let Q : Type (max u v) := ULift.{v} ((Fin n → R) ⧸ K)
  let A : ModuleCat.{max u v} R := ModuleCat.of R Q
  intro f
  let f₀ : ((Fin n → R) ⧸ K) →ₗ[R] (colimit F : ModuleCat.{max u v} R) :=
    f.hom.comp ULift.moduleEquiv.symm.toLinearMap
  obtain ⟨i, gᵢ, hgᵢ⟩ :=
    linearMap_from_fin_factor_through_filtered_colimit_stage
      (R := R) (F := F) n (f₀.comp (Submodule.mkQ K))
  have hvanish : K ≤ LinearMap.ker ((colimit.ι F i).hom.comp gᵢ) := by
    -- The original map already factors through the quotient, so the defining relations vanish in
    -- the colimit at the chosen stage.
    intro x hx
    have hx0 : (Submodule.mkQ K) x = 0 := by
      exact (Submodule.Quotient.mk_eq_zero _).2 hx
    have hcomp :
        ((colimit.ι F i).hom.comp gᵢ) x = (f₀.comp (Submodule.mkQ K)) x := by
      simpa [LinearMap.comp_assoc] using LinearMap.congr_fun hgᵢ x
    rw [LinearMap.mem_ker, hcomp]
    simpa using congrArg f₀ hx0
  obtain ⟨j, u, hu⟩ :=
    fg_submodule_eventually_le_ker_of_colimit_vanishing
      (R := R) (K := K) hK F gᵢ hvanish
  let gⱼ₀ : ((Fin n → R) ⧸ K) →ₗ[R] F.obj j :=
    K.liftQ ((F.map u).hom.comp gᵢ) hu
  let gⱼ : A ⟶ F.obj j :=
    ModuleCat.ofHom (gⱼ₀.comp ULift.moduleEquiv.toLinearMap)
  let y : colimit (F ⋙ coyoneda.obj (op A)) := colimit.ι (F ⋙ coyoneda.obj (op A)) j gⱼ
  refine ⟨y, ?_⟩
  have hgⱼ₀ :
      (colimit.ι F j).hom.comp gⱼ₀ = f₀ := by
    -- Descending through the quotient is justified because the relations already vanish at stage
    -- `j`, and the colimit cocone then identifies the descended map with `f₀`.
    apply linearMap_eq_of_comp_mkQ_eq (R := R) (K := K)
    calc
      ((colimit.ι F j).hom.comp gⱼ₀).comp (Submodule.mkQ K)
          = (colimit.ι F j).hom.comp (((F.map u).hom.comp gᵢ)) := by
              rw [LinearMap.comp_assoc, Submodule.liftQ_mkQ]
      _ = ((colimit.ι F i).hom.comp gᵢ) := by
            have hcolim :
                (colimit.ι F j).hom.comp (F.map u).hom = (colimit.ι F i).hom := by
              ext x
              simpa using
                LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (colimit.w F u)) x
            simpa [LinearMap.comp_assoc] using congrArg (fun φ => φ.comp gᵢ) hcolim
      _ = f₀.comp (Submodule.mkQ K) := hgᵢ
  have hgⱼ_post :
      gⱼ ≫ colimit.ι F j = f := by
    -- The descended stage map matches `f` after composing with the colimit cocone, and the ULift
    -- transport is only the canonical equivalence on the source module.
    apply ModuleCat.hom_ext
    ext x
    simpa [gⱼ, f₀, LinearMap.comp_assoc] using
      LinearMap.congr_fun hgⱼ₀ x.down
  -- The source colimit element represented by `gⱼ` maps to `f` under `colimit.post`.
  simpa [y, hgⱼ_post] using
    colimit_post_coyoneda_ι_app
      (A := A) (B := F) j gⱼ

/-- Helper for Lemma 10.11.4: for a quotient of a finite free module by a finitely generated
submodule, the filtered-colimit comparison map on the represented functor is bijective. -/
lemma quotient_of_fin_bijective_filteredColimitHomComparison
    {n : ℕ} (K : Submodule R (Fin n → R)) (hK : K.FG)
    {J : Type (max u v)} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{max u v} R) [HasColimit F] :
    Function.Bijective
      (colimit.post F
        (coyoneda.obj
          (op (ModuleCat.of R (ULift.{v} ((Fin n → R) ⧸ K)))))) := by
  constructor
  · let _ : Module.FinitePresentation R ((Fin n → R) ⧸ K) :=
      Module.finitePresentation_of_surjective (Submodule.mkQ K)
        (Submodule.mkQ_surjective _) <| by
          change (LinearMap.ker (Submodule.mkQ K)).FG
          simpa [Submodule.ker_mkQ] using hK
    let _ : Module.Finite R (ULift.{v} ((Fin n → R) ⧸ K)) := inferInstance
    -- Injectivity is exactly Lemma 10.11.1 applied to the finite quotient module.
    exact
      (module_finite_iff_injective_filteredColimitHomComparison
        (R := R) (N := ModuleCat.of R (ULift.{v} ((Fin n → R) ⧸ K)))).1 inferInstance F
  · -- Surjectivity follows from factoring a free-module lift through one stage and descending it
    -- through the quotient once the finitely generated relations vanish at a later stage.
    exact quotient_of_fin_surjective_filteredColimitHomComparison
      (R := R) K hK F

/-- Helper for Lemma 10.11.4: a finitely presented module has represented functor preserving
filtered colimits. -/
lemma finitePresentation_preservesFilteredColimits_coyoneda
    [Module.FinitePresentation R M] :
    PreservesFilteredColimits (coyoneda.obj (op (ModuleCat.of R M))) := by
  classical
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin R M
  let Q : Type (max u v) := ULift.{v} ((Fin n → R) ⧸ K)
  let A : ModuleCat.{max u v} R := ModuleCat.of R Q
  let eModule :
      ModuleCat.of R M ≅ A :=
    (e.trans ULift.moduleEquiv.symm).toModuleIso
  refine ⟨fun J _ _ ↦ ?_⟩
  refine ⟨fun {F} ↦ ?_⟩
  have hbij :
      Function.Bijective
        (colimit.post F (coyoneda.obj (op A))) :=
    quotient_of_fin_bijective_filteredColimitHomComparison
      (R := R) K hK F
  let _ :
      IsIso (colimit.post F (coyoneda.obj (op A))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hbij
  let β : coyoneda.obj (op A) ≅ coyoneda.obj (op (ModuleCat.of R M)) :=
    coyoneda.mapIso eModule.op
  -- The presentation equivalence identifies the represented functor of `M` with that of the
  -- quotient presentation, so preservation transports along the induced natural isomorphism.
  let _ : PreservesColimit F (coyoneda.obj (op A)) :=
    preservesColimit_of_isIso_post (coyoneda.obj (op A)) F
  exact preservesColimit_of_natIso F β

-- Source/core/bridge triage:
-- * source-facing: `Module.FinitePresentation R M`
-- * core/canonical: `CategoryTheory.IsFinitelyPresentable (ModuleCat.of R M)`
-- * bridge/view: preservation of filtered colimits by the represented functor `Hom_R(M, -)`
--
-- The owner abstraction is `IsFinitelyPresentable (ModuleCat.of R M)`. The filtered-colimit
-- statement is then obtained by composing with the owner theorem
-- `isFinitelyPresentable_iff_preservesFilteredColimits`.

/-- Lemma 10.11.4 (1): an `R`-module is finitely presented if and only if the corresponding object of
`ModuleCat R` is finitely presentable. -/
-- Proof sketch: use the standard equivalence in mathlib between finite presentation of an
-- `R`-module and finite presentability of the associated object of `ModuleCat R`.
theorem module_finitePresentation_iff_isFinitelyPresentable :
    Module.FinitePresentation R M ↔ IsFinitelyPresentable.{max u v} (ModuleCat.of R M) := by
  constructor
  · intro hM
    let _ : Module.FinitePresentation R M := hM
    -- Route correction: execute the source proof through the quotient presentation supplied by
    -- `Module.FinitePresentation.exists_fin`, then apply the owner criterion for finite
    -- presentability in `ModuleCat`.
    exact (isFinitelyPresentable_iff_preservesFilteredColimits).2
      (finitePresentation_preservesFilteredColimits_coyoneda (R := R) (M := M))
  · intro hM
    -- Route correction: instead of rebuilding the source proof's finite-free exact sequence, use
    -- Lemma 10.11.3 to obtain a filtered colimit by finitely presented modules and factor `id_M`
    -- through one stage because `M` is finitely presentable in `ModuleCat`.
    obtain ⟨J, _, _, pres, hpres⟩ :=
      (show CategoryTheory.ObjectProperty.ind.{max u v}
          (fun N : ModuleCat.{max u v} R ↦ Module.FinitePresentation R N)
          (ModuleCat.of R M) from by
        simpa [CategoryTheory.ObjectProperty.ind] using
          (module_is_isomorphic_to_colimit_of_directed_system_of_finitelyPresented
            (R := R) (M := ModuleCat.of R M)))
    have hpreserve :
        PreservesFilteredColimits (coyoneda.obj (op (ModuleCat.of R M))) := by
      exact (isFinitelyPresentable_iff_preservesFilteredColimits).mp hM
    obtain ⟨j, u, hu⟩ :=
      Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves (F := coyoneda.obj (op (ModuleCat.of R M))) pres.isColimit)
        (𝟙 (ModuleCat.of R M))
    let v' : pres.diag.obj j ⟶ ModuleCat.of R M := pres.ι.app j
    have huv : v'.hom.comp u.hom = LinearMap.id := by
      simpa [v'] using congrArg ModuleCat.Hom.hom hu
    letI : Module.FinitePresentation R (pres.diag.obj j) := hpres j
    -- The split surjection from a finitely presented stage back onto `M` now descends finite
    -- presentation to `M` through the kernel-range projector from the source proof.
    exact module_finitePresentation_of_split_surjection_from_finitelyPresented_stage
      (R := R) u.hom v'.hom huv

/-- Lemma 10.11.4 (2): an `R`-module is finitely presented if and only if its represented functor
`Hom_R(M, -)` preserves filtered colimits. -/
-- Proof sketch: combine the previous equivalence with the owner-abstraction theorem
-- `isFinitelyPresentable_iff_preservesFilteredColimits` for the represented functor.
theorem module_finitePresentation_iff_preservesFilteredColimits_coyoneda :
    Module.FinitePresentation R M ↔
      PreservesFilteredColimits (coyoneda.obj (op (ModuleCat.of R M))) := by
  -- Rewrite through finite presentability in `ModuleCat`, then apply the owner characterization of
  -- finitely presentable objects by preservation of filtered colimits of the represented functor.
  rw [module_finitePresentation_iff_isFinitelyPresentable]
  exact isFinitelyPresentable_iff_preservesFilteredColimits

end
