import Mathlib
import StacksProject_2024.Chap19.«19_2_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

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
@[stacks 0G8N]
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
