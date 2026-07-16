import Mathlib
import Mathlib.Algebra.Category.CommAlgCat.Basic
import stacks_proof.stacks_project.Chap10.Lemma_10_37_17
import stacks_proof.stacks_project.Chap10.Lemma_10_39_3
import stacks_proof.stacks_project.Chap10.Lemma_10_39_16

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.Under
open CommRingCat
open CommRingCat.Hom

universe u v w

/- Domain-style sampling for Lemma 10.39.20:
- primary domain: filtered colimits of commutative `R`-algebras in `Under (CommRingCat.of R)`;
- sampled owner declarations:
  `RingHom.FaithfullyFlat`,
  `CategoryTheory.MorphismProperty.IsStableUnderFilteredColimits`,
  `PrimeSpectrum.comap_surjective_of_faithfullyFlat`,
  `flat_of_isColimit_filtered_system`;
- best owner abstraction: filtered-colimit stability of the morphism property
  `fun f : A ⟶ B ↦ (hom f).FaithfullyFlat`, with the source-facing `Under` theorem below as a
  wrapper around that owner statement;
- primitive data: a filtered diagram `F`, a colimit cocone `c`, and the stagewise owner property
  `(hom (F.obj j).hom).FaithfullyFlat`;
- derived API: the source-facing cocone-point and chosen-colimit faithful-flatness conclusions.

Source/core/bridge triage:
- `source-facing`: faithful flatness of the structural map of a filtered colimit `R`-algebra;
- `core/canonical`: `RingHom.FaithfullyFlat` organized as a morphism property stable under filtered
  colimits;
- `bridge/view`: the `Under (CommRingCat.of R)` presentation, whose underlying ring diagram is the
  target of the owner stability statement.
-/

section

variable {R : Type u} [CommRing R]
variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ Under (CommRingCat.of R))

/-- Helper for Chap10 Lemma 10 39 20: an injective morphism of commutative rings transports
nontriviality from its source to its target. -/
theorem nontrivial_of_injective_commRingCat_hom {A B : CommRingCat} (f : A ⟶ B)
    (hf : Function.Injective f.hom) [Nontrivial A] :
    Nontrivial B := by
  -- Proof comment: the underlying injective function embeds a two-point witness from the source
  -- into the target.
  exact hf.nontrivial

/-- Helper for Chap10 Lemma 10 39 20: a commutative-ring isomorphism transports
nontriviality to the target ring. -/
theorem nontrivial_of_commRingCat_iso {A B : CommRingCat} (e : A ≅ B) [Nontrivial A] :
    Nontrivial B := by
  -- Proof comment: the isomorphism gives an injective underlying ring map, so the preceding
  -- transport lemma applies directly.
  have hinj : Function.Injective e.hom.hom :=
    (ConcreteCategory.bijective_of_isIso e.hom).injective
  exact nontrivial_of_injective_commRingCat_hom e.hom hinj

/-- Helper for Lemma 10.39.20: any colimit cocone of a filtered diagram of nontrivial
commutative rings has a nontrivial cocone point. -/
theorem nontrivial_of_isColimit_filtered_system
    (G : J ⥤ CommRingCat.{max u v}) (c : Cocone G) (hc : IsColimit c)
    [∀ j, Nontrivial (G.obj j)] :
    Nontrivial ↑c.pt := by
  -- Proof comment: transport to the canonical filtered-colimit cocone, where nontriviality is
  -- already available from the earlier filtered-colimit theorem.
  let e := hc.coconePointUniqueUpToIso (CommRingCat.FilteredColimits.colimitCoconeIsColimit G)
  letI : Nontrivial ((CommRingCat.FilteredColimits.colimitCocone G).pt) :=
    filtered_colimit_nontrivial G
  exact nontrivial_of_commRingCat_iso e.symm

/-- Helper for Chap10 Lemma 10 39 20: in the same universe as the filtered index, a colimit
cocone of nontrivial commutative rings has nontrivial point. -/
theorem nontrivial_of_isColimit_filtered_system_sameUniverse
    {G : J ⥤ CommRingCat.{v}} (c : Cocone G) (hc : IsColimit c)
    [∀ j, Nontrivial (G.obj j)] :
    Nontrivial c.pt := by
  -- Proof comment: this is the cocone-level mathlib theorem, isolated here to mark the exact
  -- same-universe boundary that the mixed `CommRingCat.{u}` proof still has to bridge.
  exact CommRingCat.FilteredColimits.nontrivial hc

/-- Helper for Chap10 Lemma 10 39 20: every element of a mixed-universe filtered colimit of
commutative rings is represented by an element from some stage. -/
theorem commRingCatElementRepresentsOfIsColimit
    {G : J ⥤ CommRingCat.{u}} {c : Cocone G} (hc : IsColimit c) (z : c.pt) :
    ∃ (i : J) (x : G.obj i), c.ι.app i x = z := by
  -- Proof comment: the stage images form a subring of the cocone point after taking closure;
  -- the colimit property splits the inclusion of that subring, forcing every element to lie in a
  -- genuine stage image.
  let stageImage : Set c.pt := {z | ∃ i x, z = c.ι.app i x}
  let S : Subring c.pt := Subring.closure stageImage
  have hclosure : ∀ z : c.pt, z ∈ S → ∃ i x, z = c.ι.app i x := by
    intro z hz
    refine Subring.closure_induction (s := stageImage)
      (p := fun z _ ↦ ∃ i x, z = c.ι.app i x) ?mem ?zero ?one ?add ?neg ?mul hz
    · intro z hz
      exact hz
    · obtain ⟨i⟩ := (IsFiltered.nonempty : Nonempty J)
      exact ⟨i, 0, ((c.ι.app i).hom.map_zero).symm⟩
    · obtain ⟨i⟩ := (IsFiltered.nonempty : Nonempty J)
      exact ⟨i, 1, ((c.ι.app i).hom.map_one).symm⟩
    · intro x y _ _ hx hy
      obtain ⟨i, xi, hxi⟩ := hx
      obtain ⟨j, yj, hyj⟩ := hy
      let k := IsFiltered.max i j
      let fi := IsFiltered.leftToMax i j
      let fj := IsFiltered.rightToMax i j
      refine ⟨k, (G.map fi).hom xi + (G.map fj).hom yj, ?_⟩
      have hleft : (c.ι.app i).hom xi = (c.ι.app k).hom ((G.map fi).hom xi) := by
        have hnat := congrArg (fun g : G.obj i ⟶ c.pt ↦ g xi) (c.w fi)
        exact hnat.symm
      have hright : (c.ι.app j).hom yj = (c.ι.app k).hom ((G.map fj).hom yj) := by
        have hnat := congrArg (fun g : G.obj j ⟶ c.pt ↦ g yj) (c.w fj)
        exact hnat.symm
      rw [hxi, hyj, hleft, hright]
      exact ((c.ι.app k).hom.map_add _ _).symm
    · intro x _ hx
      obtain ⟨i, xi, hxi⟩ := hx
      refine ⟨i, -xi, ?_⟩
      rw [hxi]
      exact ((c.ι.app i).hom.map_neg _).symm
    · intro x y _ _ hx hy
      obtain ⟨i, xi, hxi⟩ := hx
      obtain ⟨j, yj, hyj⟩ := hy
      let k := IsFiltered.max i j
      let fi := IsFiltered.leftToMax i j
      let fj := IsFiltered.rightToMax i j
      refine ⟨k, (G.map fi).hom xi * (G.map fj).hom yj, ?_⟩
      have hleft : (c.ι.app i).hom xi = (c.ι.app k).hom ((G.map fi).hom xi) := by
        have hnat := congrArg (fun g : G.obj i ⟶ c.pt ↦ g xi) (c.w fi)
        exact hnat.symm
      have hright : (c.ι.app j).hom yj = (c.ι.app k).hom ((G.map fj).hom yj) := by
        have hnat := congrArg (fun g : G.obj j ⟶ c.pt ↦ g yj) (c.w fj)
        exact hnat.symm
      rw [hxi, hyj, hleft, hright]
      exact ((c.ι.app k).hom.map_mul _ _).symm
  have hmem (i : J) (x : G.obj i) : c.ι.app i x ∈ S :=
    Subring.subset_closure ⟨i, x, rfl⟩
  let app (i : J) : G.obj i ⟶ CommRingCat.of S :=
    CommRingCat.ofHom ((c.ι.app i).hom.codRestrict S (hmem i))
  have app_naturality : ∀ {i j : J} (f : i ⟶ j), G.map f ≫ app j = app i := by
    intro i j f
    ext x
    exact congrArg (fun g : G.obj i ⟶ c.pt ↦ g x) (c.w f)
  let d : Cocone G :=
    { pt := CommRingCat.of S
      ι :=
        { app := app
          naturality := fun _ _ f ↦ app_naturality f } }
  let liftToS : c.pt ⟶ CommRingCat.of S := hc.desc d
  let incl : CommRingCat.of S ⟶ c.pt := CommRingCat.ofHom S.subtype
  have hincl : liftToS ≫ incl = 𝟙 c.pt := by
    apply hc.hom_ext
    intro i
    calc
      c.ι.app i ≫ liftToS ≫ incl = d.ι.app i ≫ incl := by
        simpa [Category.assoc, liftToS] using congrArg (fun f ↦ f ≫ incl) (hc.fac d i)
      _ = c.ι.app i ≫ 𝟙 c.pt := by
        ext x
        rfl
  have hz : z = incl (liftToS z) := by
    have happly := congrArg (fun f : c.pt ⟶ c.pt ↦ f z) hincl
    exact happly.symm
  obtain ⟨i, x, hx⟩ := hclosure (incl (liftToS z)) (liftToS z).property
  exact ⟨i, x, (hz.trans hx).symm⟩

/-- Helper for Chap10 Lemma 10 39 20: equality of two elements in a filtered colimit of
commutative rings descends to a later stage when the concrete forgetful functor preserves the
given colimit. -/
theorem commRingCat_eq_descends_of_isColimit_of_preserves_forget
    {G : J ⥤ CommRingCat.{u}} {c : Cocone G} (hc : IsColimit c)
    [PreservesColimit G (CategoryTheory.forget CommRingCat.{u})]
    {i : J} {x y : G.obj i} (hxy : c.ι.app i x = c.ι.app i y) :
    ∃ (k : J) (f : i ⟶ k), (G.map f).hom x = (G.map f).hom y := by
  -- Proof comment: after applying the preserved forgetful functor, equality in the colimit of
  -- types is exactly the filtered equivalence relation at some later stage.
  let d : Cocone (G ⋙ CategoryTheory.forget CommRingCat.{u}) :=
    (CategoryTheory.forget CommRingCat.{u}).mapCocone c
  have hd : IsColimit d := by
    exact isColimitOfPreserves (CategoryTheory.forget CommRingCat.{u}) hc
  have hxy' : d.ι.app i x = d.ι.app i y := by
    simpa [d] using hxy
  exact (Types.FilteredColimit.isColimit_eq_iff' hd x y).mp hxy'

/-- Helper for Chap10 Lemma 10 39 20: a filtered colimit cocone of commutative rings has
nontrivial point when the concrete forgetful functor preserves that particular colimit. -/
theorem nontrivial_of_isColimit_filtered_system_of_preserves_forget
    {G : J ⥤ CommRingCat.{u}} (c : Cocone G) (hc : IsColimit c)
    [∀ j, Nontrivial (G.obj j)] [PreservesColimit G (CategoryTheory.forget CommRingCat.{u})] :
    Nontrivial ↑c.pt := by
  let i : J := IsFiltered.nonempty.some
  refine ⟨c.ι.app i 0, c.ι.app i 1, fun h01 ↦ ?_⟩
  obtain ⟨k, f, hk⟩ :=
    commRingCat_eq_descends_of_isColimit_of_preserves_forget (G := G) hc h01
  have hne : (0 : G.obj k) ≠ 1 := zero_ne_one
  -- Proof comment: the descended equality says the transition map sends `0` and `1` to the same
  -- element at a nontrivial stage, contradicting preservation of zero and one.
  exact hne (((G.map f).hom.map_zero.symm.trans hk).trans (G.map f).hom.map_one)

/-- Helper for Chap10 Lemma 10 39 20: equality of two elements in a mixed-universe filtered
colimit of commutative rings descends to a common later stage. -/
theorem commRingCatElementEqDescendsOfIsColimit
    {G : J ⥤ CommRingCat.{u}} {c : Cocone G} (hc : IsColimit c)
    {i j : J} (x : G.obj i) (y : G.obj j)
    (hxy : (c.ι.app i).hom x = (c.ι.app j).hom y) :
    ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k), (G.map f).hom x = (G.map g).hom y := by
  -- TODO: prove this by constructing a dependency-closed mixed-universe concrete equality
  -- descent theorem for supplied `CommRingCat.{u}` colimits, or by a non-circular finite-free
  -- presentability route that does not assume preservation by the concrete forgetful functor.
  -- Proof comment: this isolates the exact structural descent fact needed by both the
  -- nontriviality argument and the finite-relation flatness criterion below.
  sorry

/-- Helper for Chap10 Lemma 10 39 20: a filtered colimit cocone of nontrivial commutative
rings is nontrivial even when the indexing category and ring carriers live in different
universes. -/
theorem commRingCat_nontrivial_of_isColimit_filtered_system_mixed
    {G : J ⥤ CommRingCat.{u}} (c : Cocone G) (hc : IsColimit c)
    [∀ j, Nontrivial (G.obj j)] :
    Nontrivial c.pt := by
  -- Proof comment: choose one stage and descend a hypothetical equality `0 = 1` in the colimit
  -- to a later stage, where stagewise nontriviality contradicts preservation of zero and one.
  let i : J := IsFiltered.nonempty.some
  refine ⟨c.ι.app i 0, c.ι.app i 1, fun h01 ↦ ?_⟩
  obtain ⟨k, f, g, hfg⟩ :=
    commRingCatElementEqDescendsOfIsColimit (G := G) hc (0 : G.obj i) (1 : G.obj i) h01
  let l := IsFiltered.coeq f g
  let e := IsFiltered.coeqHom f g
  have hzero_one : (0 : G.obj l) = 1 := by
    calc
      (0 : G.obj l) = (G.map (f ≫ e)).hom 0 := by
        exact ((G.map (f ≫ e)).hom.map_zero).symm
      _ = (G.map e).hom ((G.map f).hom 0) := by
        simp [Functor.map_comp]
      _ = (G.map e).hom ((G.map g).hom 1) := by
        rw [hfg]
      _ = (G.map (g ≫ e)).hom 1 := by
        simp [Functor.map_comp]
      _ = (G.map (f ≫ e)).hom 1 := by
        have hcoeq : G.map (f ≫ e) = G.map (g ≫ e) := by
          exact congrArg (fun h : i ⟶ l ↦ G.map h) (IsFiltered.coeq_condition f g)
        rw [hcoeq]
      _ = 1 := by
        exact (G.map (f ≫ e)).hom.map_one
  exact zero_ne_one hzero_one

/-- Helper for Lemma 10.39.20: an object under `CommRingCat.of R` carries its canonical
`R`-algebra structure. -/
private instance underAlgebra (B : Under (CommRingCat.of R)) : Algebra R B.right :=
  B.hom.hom.toAlgebra

/-- Helper for Lemma 10.39.20: an object under `CommRingCat.of R` is naturally an `R`-module. -/
private instance underModule (B : Under (CommRingCat.of R)) : Module R B.right :=
  (underAlgebra (R := R) B).toModule

/-- Helper for Chap10 Lemma 10 39 20: a finite tuple in an under-category mixed-universe
filtered colimit is represented at one common stage. -/
theorem existsStageTupleOfUnderIsColimit
    {G : J ⥤ Under (CommRingCat.of R)} {c : Cocone G} (hc : IsColimit c)
    {n : ℕ} (x : Fin n → c.pt.right) :
    ∃ (j : J) (xj : Fin n → (G.obj j).right),
      ∀ t, (c.ι.app j).right.hom (xj t) = x t := by
  classical
  -- Proof comment: first represent each component after forgetting to commutative rings, then
  -- filteredness moves the finitely many representing stages to a single common stage.
  let U := Under.forget (CommRingCat.of R)
  let d : Cocone (G ⋙ U) := U.mapCocone c
  have hd : IsColimit d := by
    exact isColimitOfPreserves U hc
  choose j y hy using fun t ↦
    commRingCatElementRepresentsOfIsColimit (G := G ⋙ U) hd (x t)
  obtain ⟨k, ⟨toK⟩⟩ : ∃ k : J, Nonempty (∀ t : Fin n, j t ⟶ k) := by
    have : ∃ k : J, ∀ t : Fin n, Nonempty (j t ⟶ k) := by
      simpa using IsFiltered.sup_objs_exists (Finset.univ.image j)
    simpa [← exists_true_iff_nonempty, Classical.skolem, -exists_const_iff] using this
  refine ⟨k, fun t ↦ (G.map (toK t)).right.hom (y t), fun t ↦ ?_⟩
  have hmove :
      d.ι.app k (((G ⋙ U).map (toK t)) (y t)) = d.ι.app (j t) (y t) := by
    have hnat := congrArg (fun g : (G ⋙ U).obj (j t) ⟶ d.pt ↦ g (y t)) (d.w (toK t))
    simpa using hnat
  exact hmove.trans (hy t)

/-- Helper for Chap10 Lemma 10 39 20: equality of two elements in an under-category filtered
colimit descends to a later stage when the concrete forgetful functor preserves the underlying
commutative-ring colimit. -/
theorem underElementEqDescends_of_isColimit_of_preserves_forget
    {G : J ⥤ Under (CommRingCat.of R)} {c : Cocone G} (hc : IsColimit c)
    [PreservesColimit (G ⋙ Under.forget (CommRingCat.of R))
      (CategoryTheory.forget CommRingCat.{u})]
    {i : J} {x y : (G.obj i).right}
    (hxy : (c.ι.app i).right.hom x = (c.ι.app i).right.hom y) :
    ∃ (k : J) (f : i ⟶ k), (G.map f).right.hom x = (G.map f).right.hom y := by
  -- Proof comment: forget the under-category cocone, then use the concrete equality-descent
  -- theorem for commutative rings with the supplied preservation hypothesis.
  let U := Under.forget (CommRingCat.of R)
  let d : Cocone (G ⋙ U) := U.mapCocone c
  have hd : IsColimit d := by
    exact isColimitOfPreserves U hc
  have hxy' : d.ι.app i x = d.ι.app i y := by
    simpa [d, U] using hxy
  obtain ⟨k, f, hf⟩ :=
    commRingCat_eq_descends_of_isColimit_of_preserves_forget (G := G ⋙ U) hd hxy'
  exact ⟨k, f, by simpa [U] using hf⟩

/-- Helper for Chap10 Lemma 10 39 20: equality of two elements in an under-category filtered
colimit descends to a common later stage, using mixed-universe commutative-ring descent. -/
theorem underElementEqDescendsOfIsColimit
    {G : J ⥤ Under (CommRingCat.of R)} {c : Cocone G} (hc : IsColimit c)
    {i : J} {x y : (G.obj i).right}
    (hxy : (c.ι.app i).right.hom x = (c.ι.app i).right.hom y) :
    ∃ (k : J) (f : i ⟶ k), (G.map f).right.hom x = (G.map f).right.hom y := by
  -- Proof comment: forget the under-category to commutative rings, descend equality there, then
  -- coequalize the two arrows from the common source so the relation lives over one transition.
  let U := Under.forget (CommRingCat.of R)
  let d : Cocone (G ⋙ U) := U.mapCocone c
  have hd : IsColimit d := by
    exact isColimitOfPreserves U hc
  have hxy' : d.ι.app i x = d.ι.app i y := by
    simpa [d, U] using hxy
  obtain ⟨k, f, g, hfg⟩ :=
    commRingCatElementEqDescendsOfIsColimit (G := G ⋙ U) hd x y hxy'
  let l := IsFiltered.coeq f g
  let e := IsFiltered.coeqHom f g
  refine ⟨l, f ≫ e, ?_⟩
  calc
    (G.map (f ≫ e)).right.hom x = (G.map e).right.hom ((G.map f).right.hom x) := by
      simp [Functor.map_comp]
    _ = (G.map e).right.hom ((G.map g).right.hom y) := by
      exact congrArg (fun z ↦ (G.map e).right.hom z) (by simpa [U] using hfg)
    _ = (G.map (g ≫ e)).right.hom y := by
      simp [Functor.map_comp]
    _ = (G.map (f ≫ e)).right.hom y := by
      have hcoeq : G.map (f ≫ e) = G.map (g ≫ e) := by
        exact congrArg (fun h : i ⟶ l ↦ G.map h) (IsFiltered.coeq_condition f g)
      rw [hcoeq]

/-- Helper for Chap10 Lemma 10 39 20: a finite `R`-linear relation in an under-category
filtered colimit descends to a later stage when the underlying concrete colimit is preserved. -/
theorem underRelationDescends_of_isColimit_of_preserves_forget
    {G : J ⥤ Under (CommRingCat.of R)} {c : Cocone G} (hc : IsColimit c)
    [PreservesColimit (G ⋙ Under.forget (CommRingCat.of R))
      (CategoryTheory.forget CommRingCat.{u})]
    {n : ℕ} {i : J} (a : Fin n → R) (x : Fin n → (G.obj i).right)
    (h : ∑ t, a t • (c.ι.app i).right.hom (x t) = 0) :
    ∃ (k : J) (f : i ⟶ k), ∑ t, a t • (G.map f).right.hom (x t) = 0 := by
  -- Proof comment: package the finite relation as equality of the stage sum with zero after
  -- mapping to the colimit, then descend that equality and expand it back into the relation.
  let s : (G.obj i).right := ∑ t, a t • x t
  have hsum_colimit : (c.ι.app i).right.hom s = 0 := by
    calc
      (c.ι.app i).right.hom s =
          ∑ t, (CommRingCat.toAlgHom (c.ι.app i)) (a t • x t) := by
        simpa [s] using
          map_sum (CommRingCat.toAlgHom (c.ι.app i)) (fun t ↦ a t • x t) Finset.univ
      _ = ∑ t, a t • (c.ι.app i).right.hom (x t) := by
        exact Finset.sum_congr rfl fun t _ ↦ by
          simpa using map_smul (CommRingCat.toAlgHom (c.ι.app i)) (a t) (x t)
      _ = 0 := h
  obtain ⟨k, f, hf⟩ :=
    underElementEqDescends_of_isColimit_of_preserves_forget (G := G) hc
      (x := s) (y := 0) (hsum_colimit.trans (map_zero (c.ι.app i).right.hom).symm)
  refine ⟨k, f, ?_⟩
  calc
    ∑ t, a t • (G.map f).right.hom (x t) =
        ∑ t, (CommRingCat.toAlgHom (G.map f)) (a t • x t) := by
      exact Finset.sum_congr rfl fun t _ ↦ by
        simpa only [CommRingCat.toAlgHom_apply] using
          (map_smul (CommRingCat.toAlgHom (G.map f)) (a t) (x t)).symm
    _ = (CommRingCat.toAlgHom (G.map f)) s := by
      change ∑ t, (CommRingCat.toAlgHom (G.map f)) (a t • x t) =
        (CommRingCat.toAlgHom (G.map f)) (∑ t, a t • x t)
      exact
        (map_sum (CommRingCat.toAlgHom (G.map f)) (fun t ↦ a t • x t) Finset.univ).symm
    _ = (G.map f).right.hom s := CommRingCat.toAlgHom_apply (G.map f) s
    _ = 0 := by
      simpa using hf

/-- Helper for Chap10 Lemma 10 39 20: a finite `R`-linear relation in an under-category
filtered colimit descends to a later stage. -/
theorem underRelationDescendsOfIsColimit
    {G : J ⥤ Under (CommRingCat.of R)} {c : Cocone G} (hc : IsColimit c)
    {n : ℕ} {i : J} (a : Fin n → R) (x : Fin n → (G.obj i).right)
    (h : ∑ t, a t • (c.ι.app i).right.hom (x t) = 0) :
    ∃ (k : J) (f : i ⟶ k), ∑ t, a t • (G.map f).right.hom (x t) = 0 := by
  -- Proof comment: package the finite relation as equality between the stage sum and zero,
  -- descend that equality as an under-category element equality, then unpack the stage sum.
  let s : (G.obj i).right := ∑ t, a t • x t
  have hsum_colimit : (c.ι.app i).right.hom s = 0 := by
    calc
      (c.ι.app i).right.hom s =
          ∑ t, (CommRingCat.toAlgHom (c.ι.app i)) (a t • x t) := by
        simpa [s] using
          map_sum (CommRingCat.toAlgHom (c.ι.app i)) (fun t ↦ a t • x t) Finset.univ
      _ = ∑ t, a t • (c.ι.app i).right.hom (x t) := by
        exact Finset.sum_congr rfl fun t _ ↦ by
          simpa using map_smul (CommRingCat.toAlgHom (c.ι.app i)) (a t) (x t)
      _ = 0 := h
  obtain ⟨k, f, hf⟩ :=
    underElementEqDescendsOfIsColimit (G := G) hc
      (x := s) (y := 0) (hsum_colimit.trans (map_zero (c.ι.app i).right.hom).symm)
  refine ⟨k, f, ?_⟩
  calc
    ∑ t, a t • (G.map f).right.hom (x t) =
        ∑ t, (CommRingCat.toAlgHom (G.map f)) (a t • x t) := by
      exact Finset.sum_congr rfl fun t _ ↦ by
        simpa only [CommRingCat.toAlgHom_apply] using
          (map_smul (CommRingCat.toAlgHom (G.map f)) (a t) (x t)).symm
    _ = (CommRingCat.toAlgHom (G.map f)) s := by
      change ∑ t, (CommRingCat.toAlgHom (G.map f)) (a t • x t) =
        (CommRingCat.toAlgHom (G.map f)) (∑ t, a t • x t)
      exact
        (map_sum (CommRingCat.toAlgHom (G.map f)) (fun t ↦ a t • x t) Finset.univ).symm
    _ = (G.map f).right.hom s := CommRingCat.toAlgHom_apply (G.map f) s
    _ = 0 := by
      simpa using hf

/-- Helper for Chap10 Lemma 10 39 20: trivial finite `R`-linear relations are preserved by
morphisms in the under-category of `CommRingCat.of R`. -/
theorem isTrivialRelation_map_underHom
    {B C : Under (CommRingCat.of R)} (f : B ⟶ C)
    {n : ℕ} {a : Fin n → R} {x : Fin n → B.right} :
    Module.IsTrivialRelation a x →
      Module.IsTrivialRelation a (fun t ↦ f.right.hom (x t)) := by
  intro h
  -- Proof comment: reuse the same trivializing coefficients and map the witness vectors through
  -- the `R`-linear morphism underlying the under-category map.
  obtain ⟨k, b, y, hy, hrel⟩ := h
  refine ⟨k, b, fun s ↦ f.right.hom (y s), ?_, hrel⟩
  intro t
  calc
    (fun t ↦ f.right.hom (x t)) t = f.right.hom (∑ s, b t s • y s) := by
      exact congrArg f.right.hom (hy t)
    _ =
        ∑ s, f.right.hom (b t s • y s) := by
      exact map_sum f.right.hom (fun s ↦ b t s • y s) Finset.univ
    _ = ∑ s, b t s • f.right.hom (y s) := by
      exact Finset.sum_congr rfl fun s _ ↦ by
        simpa only [CommRingCat.toAlgHom_apply] using
          map_smul (CommRingCat.toAlgHom f) (b t s) (y s)

omit [SmallCategory J] [IsFiltered J] in
/-- Helper for Chap10 Lemma 10 39 20: the finite polynomial `R`-algebra
`MvPolynomial (Fin n) R` is finitely presentable as an object under `CommRingCat.of R` in the
carrier universe. -/
theorem underPolynomial_isFinitelyPresentable (n : ℕ) :
    IsFinitelyPresentable.{u}
      (Under.mk (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R)))) := by
  -- Proof comment: the algebraic finite-presentation instance for finite polynomial algebras
  -- feeds directly into the commutative-ring under-category finite-presentability bridge.
  have hfp : (algebraMap R (MvPolynomial (Fin n) R)).FinitePresentation := by
    exact RingHom.finitePresentation_algebraMap.mpr
      (inferInstance : Algebra.FinitePresentation R (MvPolynomial (Fin n) R))
  exact CommRingCat.isFinitelyPresentable_under (CommRingCat.of R) _ hfp

omit [SmallCategory J] [IsFiltered J] in
/-- Helper for Chap10 Lemma 10 39 20: in the carrier universe, a finite tuple in a filtered
colimit of commutative `R`-algebras under `R` is represented at some stage. -/
theorem existsStageTupleOfUnderIsColimitSameUniverse
    {K : Type u} [SmallCategory K] [IsFiltered K]
    (G : K ⥤ Under (CommRingCat.of R)) (c : Cocone G) (hc : IsColimit c)
    {n : ℕ} (x : Fin n → c.pt.right) :
    ∃ (j : K) (xj : Fin n → (G.obj j).right),
      ∀ i, (c.ι.app j).right.hom (xj i) = x i := by
  -- Proof comment: represent the tuple by the universal map from the finite polynomial
  -- `R`-algebra, then use finite presentability to factor that map through a stage.
  let S : Under (CommRingCat.of R) :=
    CommRingCat.mkUnder (CommRingCat.of R) (MvPolynomial (Fin n) R)
  have hS : IsFinitelyPresentable.{u} S := by
    have hfp : (algebraMap R (MvPolynomial (Fin n) R)).FinitePresentation := by
      exact RingHom.finitePresentation_algebraMap.mpr
        (inferInstance : Algebra.FinitePresentation R (MvPolynomial (Fin n) R))
    exact CommRingCat.isFinitelyPresentable_under (CommRingCat.of R) S hfp
  letI : IsFinitelyPresentable.{u} S := hS
  have hp_comm : S.hom ≫ CommRingCat.ofHom (MvPolynomial.aeval x).toRingHom = c.pt.hom := by
    apply CommRingCat.hom_ext
    ext r
    simpa [S, RingHom.comp_apply] using (MvPolynomial.aeval_C x r)
  let p : S ⟶ c.pt :=
    Under.homMk (CommRingCat.ofHom (MvPolynomial.aeval x).toRingHom) hp_comm
  obtain ⟨j, q, hq⟩ := IsFinitelyPresentable.exists_hom_of_isColimit (X := S) hc p
  refine ⟨j, fun i ↦ q.right.hom (MvPolynomial.X i), fun i ↦ ?_⟩
  -- Proof comment: evaluating the factored polynomial map on each variable recovers the
  -- corresponding component of the original tuple.
  have hright : q.right ≫ (c.ι.app j).right = p.right := by
    simpa using congrArg (fun f ↦ f.right) hq
  have happ := congrArg CommRingCat.Hom.hom hright
  calc
    (hom (c.ι.app j).right) ((hom q.right) (MvPolynomial.X i)) =
        (hom p.right) (MvPolynomial.X i) := by
      simpa [CommRingCat.comp_apply] using RingHom.congr_fun happ (MvPolynomial.X i)
    _ = x i := by
      exact MvPolynomial.aeval_X x i

/-- Helper for Lemma 10.39.20: after quotienting by a maximal ideal, each faithfully flat stage
has a nontrivial closed fiber. -/
theorem stage_pushout_nontrivial_of_faithfully_flat
    {j : J} (hF : ∀ j, (hom (F.obj j).hom).FaithfullyFlat)
    (m : Ideal R) [m.IsMaximal] :
    Nontrivial (((Under.pushout (CommRingCat.ofHom (Ideal.Quotient.mk m))).obj (F.obj j)).right) := by
  letI : Algebra R (F.obj j).right := (F.obj j).hom.hom.toAlgebra
  letI : Module R (F.obj j).right := (F.obj j).hom.hom.toAlgebra.toModule
  letI : Module.FaithfullyFlat R (F.obj j).right := by
    exact
      (RingHom.faithfullyFlat_algebraMap_iff
        (R := R) (S := (F.obj j).right)).mp <| by
          simpa [RingHom.algebraMap_toAlgebra] using hF j
  have hm_ne_top : m ≠ ⊤ := (inferInstance : m.IsMaximal).ne_top
  letI : Nontrivial (R ⧸ m) := by
    exact (Ideal.Quotient.nontrivial_iff).2 hm_ne_top
  letI : Nontrivial (TensorProduct R (R ⧸ m) ((F.obj j).right)) := by
    exact
      (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_left
        (R := R) (M := R ⧸ m) (N := (F.obj j).right)).2 inferInstance
  let e :=
    CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of (R ⧸ m)) (F.obj j)
  -- Proof comment: the pushout-model fiber ring is canonically the tensor-product fiber ring.
  obtain ⟨x, y, hxy⟩ :=
    Nontrivial.exists_pair_ne (α := TensorProduct R (R ⧸ m) ((F.obj j).right))
  have hinj : Function.Injective e.hom.right :=
    (ConcreteCategory.bijective_of_isIso e.hom.right).injective
  exact ⟨e.hom.right x, e.hom.right y, fun h ↦ hxy (hinj h)⟩

/-- Helper for Lemma 10.39.20: forget a commutative ring under `R` to its underlying
`R`-module. -/
private abbrev underForgetToModule : Under (CommRingCat.of R) ⥤ ModuleCat.{u} R where
  obj B := ModuleCat.of R B.right
  map f := ModuleCat.ofHom (CommRingCat.toAlgHom f).toLinearMap

/-- Helper for Chap10 Lemma 10 39 20: flatness of the structure map of an under-object is the
same as flatness of its underlying module over the base. -/
theorem moduleFlat_of_under_flat {B : Under (CommRingCat.of R)} (hB : (hom B.hom).Flat) :
    Module.Flat R B.right := by
  -- Proof comment: the algebra structure on an under-object is induced by its structure map, so
  -- the ring-hom flatness criterion converts directly to module flatness.
  exact (RingHom.flat_algebraMap_iff
    (R := R) (S := B.right)).mp <| by
      simpa [RingHom.algebraMap_toAlgebra] using hB

/-- Helper for Chap10 Lemma 10 39 20: faithful flatness of an under-object supplies flatness of
its underlying module over the base. -/
theorem moduleFlat_of_under_faithfullyFlat {B : Under (CommRingCat.of R)}
    (hB : (hom B.hom).FaithfullyFlat) :
    Module.Flat R B.right := by
  -- Proof comment: faithful flatness includes ring-hom flatness, and the existing bridge converts
  -- that flatness to the module carried by the under-object.
  exact moduleFlat_of_under_flat (R := R) (B := B) hB.1

omit [IsFiltered J] in
/-- Helper for Chap10 Lemma 10 39 20: a stagewise linear map induces a natural transformation
after tensoring a mixed-universe filtered module diagram on the right. -/
def lTensor_natTrans_mixed
    (M : J ⥤ ModuleCat.{u} R)
    {N N' : ModuleCat.{u} R} (f : N ⟶ N') :
    M ⋙ tensorRight N ⟶ M ⋙ tensorRight N' where
  app j := ModuleCat.ofHom (f.hom.lTensor (M.obj j))
  naturality _ _ g := lTensor_naturality (R := R) (M.map g) f

omit [IsFiltered J] in
/-- Helper for Chap10 Lemma 10 39 20: the tensorized mixed-universe cocone maps are compatible
with tensoring by a chosen linear map. -/
theorem lTensor_natTrans_colimit_compat_mixed
    (M : J ⥤ ModuleCat.{u} R) (c : Cocone M)
    {N N' : Type u} [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
    (f : N →ₗ[R] N') :
    ∀ j,
      ((tensorRight (ModuleCat.of R N)).mapCocone c).ι.app j ≫
          ModuleCat.ofHom (f.lTensor c.pt) =
        (lTensor_natTrans_mixed (R := R) M (ModuleCat.ofHom f)).app j ≫
          ((tensorRight (ModuleCat.of R N')).mapCocone c).ι.app j := by
  intro j
  -- Proof comment: this is the ordinary tensor naturality square, with no dependence on the
  -- universe of the filtered indexing category.
  simpa [lTensor_natTrans_mixed] using
    lTensor_naturality (R := R) (c.ι.app j) (ModuleCat.ofHom f)

omit [IsFiltered J] in
/-- Helper for Chap10 Lemma 10 39 20: right tensoring preserves a supplied mixed-universe
colimit cocone of `R`-modules. -/
noncomputable def moduleCat_tensorRight_mapCocone_isColimit_mixed
    (M : J ⥤ ModuleCat.{u} R) (c : Cocone M) (hc : IsColimit c) (N : ModuleCat.{u} R) :
    IsColimit ((tensorRight N).mapCocone c) :=
  Limits.isColimitOfPreserves (tensorRight N) hc

/-- Helper for Chap10 Lemma 10 39 20: the larger `R`-module category has exact filtered
colimits for the mixed-universe index category. -/
theorem moduleCat_hasExactColimitsOfShape_large :
    HasExactColimitsOfShape J (ModuleCat.{max u v} R) := by
  -- Proof comment: exactness is pulled back from additive groups in the large universe, where
  -- `AB5OfSize_shrink` supplies exact filtered colimits of the required shape.
  haveI : AB5OfSize.{v, v} AddCommGrpCat.{max u v} :=
    AB5OfSize_shrink AddCommGrpCat.{max u v}
  exact HasExactColimitsOfShape.domain_of_functor J
    (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})

/-- Helper for Chap10 Lemma 10 39 20: filtered colimits in the larger `R`-module category
preserve monomorphisms for the mixed-universe index category. -/
theorem moduleCat_colim_preservesMonomorphisms_large :
    (colim (J := J) (C := ModuleCat.{max u v} R)).PreservesMonomorphisms := by
  -- Proof comment: exactness of the large filtered colimit functor implies preservation of
  -- monomorphisms, which is the categorical endpoint needed for the lifted mono bridge.
  haveI : HasExactColimitsOfShape J (ModuleCat.{max u v} R) :=
    moduleCat_hasExactColimitsOfShape_large (R := R) (J := J)
  infer_instance

/-- Helper for Chap10 Lemma 10 39 20: a stagewise monomorphism between mixed-universe filtered
module diagrams induces a monomorphism between supplied colimit cocone points. -/
theorem moduleCat_mono_of_isColimit_of_mono_app_mixed
    {X₁ X₂ : J ⥤ ModuleCat.{u} R}
    [PreservesColimit X₁ (CategoryTheory.forget (ModuleCat.{u} R))]
    [PreservesColimit X₂ (CategoryTheory.forget (ModuleCat.{u} R))]
    (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂)
    (φ : X₁ ⟶ X₂) (f : c₁.pt ⟶ c₂.pt)
    (hf : ∀ j, c₁.ι.app j ≫ f = φ.app j ≫ c₂.ι.app j)
    (hmono : ∀ j, Mono (φ.app j)) :
    Mono f := by
  -- Route correction: the earlier `ULift` route needed preservation of supplied cocones through
  -- universe lift. Once the two module diagrams are known to have colimits preserved by the
  -- concrete forgetful functor, the standard filtered-colimit injectivity argument applies.
  rw [ModuleCat.mono_iff_injective]
  let c₁' : Cocone (X₁ ⋙ CategoryTheory.forget (ModuleCat.{u} R)) :=
    (CategoryTheory.forget (ModuleCat.{u} R)).mapCocone c₁
  let c₂' : Cocone (X₂ ⋙ CategoryTheory.forget (ModuleCat.{u} R)) :=
    (CategoryTheory.forget (ModuleCat.{u} R)).mapCocone c₂
  have hc₁' : IsColimit c₁' := by
    -- Proof comment: the source cocone remains colimiting after forgetting to types.
    simpa [c₁'] using
      Limits.isColimitOfPreserves (CategoryTheory.forget (ModuleCat.{u} R)) hc₁
  have hc₂' : IsColimit c₂' := by
    -- Proof comment: the target cocone is converted to the underlying filtered colimit of types.
    simpa [c₂'] using
      Limits.isColimitOfPreserves (CategoryTheory.forget (ModuleCat.{u} R)) hc₂
  have hmono_fun : ∀ j, Function.Injective (φ.app j) := by
    intro j
    exact (ModuleCat.mono_iff_injective (φ.app j)).1 (hmono j)
  have hcompat_fun (j : J) (x : X₁.obj j) :
      f (c₁'.ι.app j x) = c₂'.ι.app j (φ.app j x) := by
    -- Proof comment: rewrite the categorical compatibility square as an equality of functions.
    simpa [c₁', c₂'] using DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp (hf j)) x
  -- Proof comment: represent both source elements at one filtered stage, descend equality after
  -- applying `f` to a later stage, then use stagewise injectivity there.
  intro x₁ y₁ hxy
  obtain ⟨j, x₁', y₁', rfl, rfl⟩ : ∃ (j : J) (x₁' y₁' : X₁.obj j),
      x₁ = c₁'.ι.app j x₁' ∧ y₁ = c₁'.ι.app j y₁' := by
    obtain ⟨j, x₁', rfl⟩ := Types.jointly_surjective_of_isColimit hc₁' x₁
    obtain ⟨l, y₁', rfl⟩ := Types.jointly_surjective_of_isColimit hc₁' y₁
    exact ⟨_, _, _, congr_fun (c₁'.w (IsFiltered.leftToMax j l)).symm x₁',
      congr_fun (c₁'.w (IsFiltered.rightToMax j l)).symm y₁'⟩
  rw [hcompat_fun j x₁', hcompat_fun j y₁'] at hxy
  obtain ⟨k, α, hk⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc₂' _ _).1 hxy
  have hk' :
      φ.app k ((X₁ ⋙ CategoryTheory.forget (ModuleCat.{u} R)).map α x₁') =
        φ.app k ((X₁ ⋙ CategoryTheory.forget (ModuleCat.{u} R)).map α y₁') := by
    have hnatx :
        φ.app k ((X₁ ⋙ CategoryTheory.forget (ModuleCat.{u} R)).map α x₁') =
          (X₂ ⋙ CategoryTheory.forget (ModuleCat.{u} R)).map α (φ.app j x₁') := by
      simpa using DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp (φ.naturality α)) x₁'
    have hnaty :
        φ.app k ((X₁ ⋙ CategoryTheory.forget (ModuleCat.{u} R)).map α y₁') =
          (X₂ ⋙ CategoryTheory.forget (ModuleCat.{u} R)).map α (φ.app j y₁') := by
      simpa using DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp (φ.naturality α)) y₁'
    exact hnatx.trans (hk.trans hnaty.symm)
  have hmap :
      (X₁ ⋙ CategoryTheory.forget (ModuleCat.{u} R)).map α x₁' =
        (X₁ ⋙ CategoryTheory.forget (ModuleCat.{u} R)).map α y₁' := hmono_fun _ hk'
  have hxk :
      c₁'.ι.app j x₁' =
        c₁'.ι.app k ((X₁ ⋙ CategoryTheory.forget (ModuleCat.{u} R)).map α x₁') := by
    exact congr_fun (c₁'.w α).symm x₁'
  have hyk :
      c₁'.ι.app j y₁' =
        c₁'.ι.app k ((X₁ ⋙ CategoryTheory.forget (ModuleCat.{u} R)).map α y₁') := by
    exact congr_fun (c₁'.w α).symm y₁'
  have hι :
      c₁'.ι.app k ((X₁ ⋙ CategoryTheory.forget (ModuleCat.{u} R)).map α x₁') =
        c₁'.ι.app k ((X₁ ⋙ CategoryTheory.forget (ModuleCat.{u} R)).map α y₁') := by
    rw [hmap]
  exact hxk.trans (hι.trans hyk.symm)

/-- Helper for Chap10 Lemma 10 39 20: a stagewise monomorphism between mixed-universe filtered
module diagrams induces a monomorphism between cocone points once the `ULift`ed supplied cocones
are known to be colimiting. -/
theorem moduleCat_mono_of_isColimit_of_mono_app_ulift
    {X₁ X₂ : J ⥤ ModuleCat.{u} R}
    (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (hc₁U : IsColimit ((ModuleCat.uliftFunctor.{v, u} R).mapCocone c₁))
    (hc₂U : IsColimit ((ModuleCat.uliftFunctor.{v, u} R).mapCocone c₂))
    (φ : X₁ ⟶ X₂) (f : c₁.pt ⟶ c₂.pt)
    (hf : ∀ j, c₁.ι.app j ≫ f = φ.app j ≫ c₂.ι.app j)
    (hmono : ∀ j, Mono (φ.app j)) :
    Mono f := by
  -- Proof comment: lift the supplied colimit cocones to the larger module universe where the
  -- standard exact-filtered-colimit mono theorem applies.
  let U := ModuleCat.uliftFunctor.{v, u} R
  have hmonoU_app : ∀ j, Mono (U.map (φ.app j)) := by
    intro j
    -- Proof comment: functoriality preserves each stagewise monomorphism after universe lift.
    exact inferInstance
  have hcompatU :
      ∀ j, (U.mapCocone c₁).ι.app j ≫ U.map f =
        U.map (φ.app j) ≫ (U.mapCocone c₂).ι.app j := by
    intro j
    -- Proof comment: the compatibility square is transported through the `ULift` functor.
    simpa [U, Functor.map_comp] using congrArg (fun g ↦ U.map g) (hf j)
  have hmonoUf : Mono (U.map f) := by
    -- Proof comment: in the lifted universe, filtered colimits preserve monomorphisms, so the
    -- induced map between the two lifted colimit points is mono.
    haveI : (colim (J := J) (C := ModuleCat.{max u v} R)).PreservesMonomorphisms :=
      moduleCat_colim_preservesMonomorphisms_large (R := R) (J := J)
    let φU : X₁ ⋙ U ⟶ X₂ ⋙ U := Functor.whiskerRight φ U
    have hφU_app : ∀ j, Mono (φU.app j) := by
      intro j
      exact hmonoU_app j
    have hcompatφU :
        ∀ j, (U.mapCocone c₁).ι.app j ≫ U.map f =
          φU.app j ≫ (U.mapCocone c₂).ι.app j := by
      intro j
      simpa [φU, Functor.whiskerRight_app] using hcompatU j
    letI : ∀ j, Mono (φU.app j) := hφU_app
    letI : Mono φU := NatTrans.mono_of_mono_app φU
    exact Limits.colim.map_mono' φU (by simpa [U] using hc₁U) (by simpa [U] using hc₂U)
      (U.map f) hcompatφU
  -- Proof comment: `ULift` is faithful, so monicity of the lifted map reflects to the original
  -- cocone-point map.
  exact U.mono_of_mono_map hmonoUf

/-- Helper for Lemma 10.39.20: forgetting a filtered diagram of commutative `R`-algebras to
`R`-modules sends stagewise flatness to flatness of the colimit algebra. -/
theorem flat_of_isColimit_filtered_system_under
    (c : Cocone F) (hc : IsColimit c) (hF : ∀ j, (hom (F.obj j).hom).Flat) :
    (hom c.pt.hom).Flat := by
  -- Route correction: rather than proving a mixed-universe `ModuleCat` colimit preservation
  -- theorem, use the equational criterion and descend only the finite tuple and relation needed.
  have hModuleFlat : Module.Flat R c.pt.right := by
    refine Module.Flat.of_forall_isTrivialRelation ?_
    intro n a x h
    obtain ⟨i, xi, hxi⟩ := existsStageTupleOfUnderIsColimit (G := F) hc x
    have hrel_colimit :
        ∑ t, a t • (c.ι.app i).right.hom (xi t) = 0 := by
      calc
        ∑ t, a t • (c.ι.app i).right.hom (xi t) = ∑ t, a t • x t := by
          exact Finset.sum_congr rfl fun t _ ↦ congrArg (fun y ↦ a t • y) (hxi t)
        _ = 0 := h
    obtain ⟨k, f, hrel_stage⟩ :=
      underRelationDescendsOfIsColimit (G := F) hc a xi hrel_colimit
    have hflat_stage : Module.Flat R (F.obj k).right :=
      moduleFlat_of_under_flat (R := R) (B := F.obj k) (hF k)
    letI : Module.Flat R (F.obj k).right := hflat_stage
    have htriv_stage :
        Module.IsTrivialRelation a (fun t ↦ (F.map f).right.hom (xi t)) :=
      Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel_stage
    have htriv_colimit :
        Module.IsTrivialRelation a
          (fun t ↦ (c.ι.app k).right.hom ((F.map f).right.hom (xi t))) :=
      isTrivialRelation_map_underHom (R := R) (f := c.ι.app k) htriv_stage
    -- Proof comment: naturality of the cocone identifies the mapped stage tuple with the
    -- original tuple `x`, so the trivial relation transported from the stage proves the goal.
    obtain ⟨l, b, y, hy, hby⟩ := htriv_colimit
    refine ⟨l, b, y, ?_, hby⟩
    intro t
    have hnat :
        (c.ι.app k).right.hom ((F.map f).right.hom (xi t)) =
          (c.ι.app i).right.hom (xi t) := by
      have hright : (F.map f).right ≫ (c.ι.app k).right = (c.ι.app i).right := by
        have hright0 := congrArg (fun g : F.obj i ⟶ c.pt ↦ g.right) (c.w f)
        simpa only [Under.comp_right] using hright0
      have happ := congrArg CommRingCat.Hom.hom hright
      simpa [CommRingCat.comp_apply] using RingHom.congr_fun happ (xi t)
    have hxk : (c.ι.app k).right.hom ((F.map f).right.hom (xi t)) = x t :=
      hnat.trans (hxi t)
    exact hxk.symm.trans (hy t)
  have hAlgFlat : (algebraMap R c.pt.right).Flat :=
    (RingHom.flat_algebraMap_iff (R := R) (S := c.pt.right)).mpr hModuleFlat
  -- Proof comment: the under-object algebra structure is induced by its structure morphism, so
  -- module flatness converts back to flatness of the source-facing ring map.
  simpa [RingHom.algebraMap_toAlgebra] using hAlgFlat

/-- Helper for Lemma 10.39.20: after quotienting by a maximal ideal, the pushed-out colimit
ring stays nontrivial because filtered colimits preserve the inequality `1 ≠ 0`. -/
theorem pushout_colimit_nontrivial_of_filtered_faithfully_flat_system
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, (hom (F.obj j).hom).FaithfullyFlat)
    (m : Ideal R) [m.IsMaximal] :
    Nontrivial (((Under.pushout (CommRingCat.ofHom (Ideal.Quotient.mk m))).obj c.pt).right) := by
  let P := Under.pushout (CommRingCat.ofHom (Ideal.Quotient.mk m))
  let G : J ⥤ Under (CommRingCat.of (R ⧸ m)) := F ⋙ P
  let cP : Cocone G := P.mapCocone c
  have hcP : IsColimit cP := by
    -- Proof comment: pushout is a left adjoint on under-categories, hence preserves the given
    -- filtered colimit cocone.
    exact isColimitOfPreserves P hc
  let U := Under.forget (CommRingCat.of (R ⧸ m))
  let d : Cocone (G ⋙ U) := U.mapCocone cP
  have hd : IsColimit d := by
    -- Proof comment: the under-category forgetful functor preserves filtered colimits, so the
    -- pushed-out cocone is colimiting as a diagram of commutative rings.
    exact isColimitOfPreserves U hcP
  letI : ∀ j, Nontrivial ((G ⋙ U).obj j) := fun j ↦ by
    -- Proof comment: each stagewise closed fiber is nontrivial by faithful flatness after the
    -- maximal-ideal base change.
    exact stage_pushout_nontrivial_of_faithfully_flat (F := F) hF m
  -- Proof comment: the pushed-out colimit is now reduced to the precise mixed-universe
  -- nontriviality theorem for filtered colimits of commutative rings.
  exact commRingCat_nontrivial_of_isColimit_filtered_system_mixed d hd

/-- Helper for Lemma 10.39.20: a nontrivial pushed-out colimit over `R ⧸ m` yields a prime of the
colimit ring whose contraction back to `R` is the maximal ideal `m`. -/
theorem pushout_colimit_closed_point_lift
    (c : Cocone F) (m : Ideal R) [m.IsMaximal]
    [Nontrivial (((Under.pushout (CommRingCat.ofHom (Ideal.Quotient.mk m))).obj c.pt).right)] :
    (⟨m, inferInstance⟩ : PrimeSpectrum R) ∈
      Set.range (PrimeSpectrum.comap (hom c.pt.hom)) := by
  classical
  obtain ⟨y'⟩ := PrimeSpectrum.nonempty_iff_nontrivial.mpr
    (show Nontrivial (((Under.pushout (CommRingCat.ofHom (Ideal.Quotient.mk m))).obj c.pt).right)
      from inferInstance)
  let y : PrimeSpectrum c.pt.right :=
    PrimeSpectrum.comap
      (pushout.inl c.pt.hom (CommRingCat.ofHom (Ideal.Quotient.mk m))).hom y'
  refine ⟨y, ?_⟩
  -- Proof comment: contract first along the pushout leg into `c.pt.right`, then rewrite the
  -- composite through the quotient square and use maximality to identify the contraction.
  change PrimeSpectrum.comap
      ((pushout.inl c.pt.hom (CommRingCat.ofHom (Ideal.Quotient.mk m))).hom.comp
        (hom c.pt.hom)) y' = _
  rw [show
      (pushout.inl c.pt.hom (CommRingCat.ofHom (Ideal.Quotient.mk m))).hom.comp (hom c.pt.hom) =
        (pushout.inr c.pt.hom (CommRingCat.ofHom (Ideal.Quotient.mk m))).hom.comp
          (Ideal.Quotient.mk m) by
        simpa using congrArg CommRingCat.Hom.hom
          (pushout.condition (f := c.pt.hom)
            (g := CommRingCat.ofHom (Ideal.Quotient.mk m)))]
  change PrimeSpectrum.comap (Ideal.Quotient.mk m)
      (PrimeSpectrum.comap
        (pushout.inr c.pt.hom (CommRingCat.ofHom (Ideal.Quotient.mk m))).hom y') = _
  apply PrimeSpectrum.ext
  -- Proof comment: every contraction from the quotient ring contains the kernel of the quotient
  -- map, which is exactly `m`.
  have hle :
      m ≤ (PrimeSpectrum.comap (Ideal.Quotient.mk m)
        (PrimeSpectrum.comap
          (pushout.inr c.pt.hom (CommRingCat.ofHom (Ideal.Quotient.mk m))).hom y')).asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal, Ideal.mk_ker] using
      (Ideal.ker_le_comap (Ideal.Quotient.mk m))
  exact
    (Ideal.IsMaximal.eq_of_le
      (I := m)
      (J := (PrimeSpectrum.comap (Ideal.Quotient.mk m)
        (PrimeSpectrum.comap
          (pushout.inr c.pt.hom (CommRingCat.ofHom (Ideal.Quotient.mk m))).hom y')).asIdeal)
      (show m.IsMaximal from inferInstance)
      (PrimeSpectrum.comap (Ideal.Quotient.mk m)
        (PrimeSpectrum.comap
          (pushout.inr c.pt.hom (CommRingCat.ofHom (Ideal.Quotient.mk m))).hom y')).2.ne_top
      hle).symm

/-- Helper for Lemma 10.39.20: every closed point of `Spec R` lifts to the colimit ring of a
filtered faithfully flat system. -/
theorem closed_points_subset_range_of_filtered_faithfully_flat_system
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, (hom (F.obj j).hom).FaithfullyFlat) :
    closedPoints (PrimeSpectrum R) ⊆
      Set.range (PrimeSpectrum.comap (hom c.pt.hom)) := by
  intro x hx
  have hxmax : x.asIdeal.IsMaximal := by
    -- Proof comment: a closed point of the prime spectrum is exactly a maximal ideal.
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp (by simpa [closedPoints] using hx)
  letI : x.asIdeal.IsMaximal := hxmax
  letI :
      Nontrivial (((Under.pushout
        (CommRingCat.ofHom (Ideal.Quotient.mk x.asIdeal))).obj c.pt).right) :=
    pushout_colimit_nontrivial_of_filtered_faithfully_flat_system
      (F := F) c hc hF x.asIdeal
  -- Proof comment: the nontrivial quotient fiber over the closed point supplies a prime of the
  -- pushed-out colimit, and its contraction gives back the original closed point.
  simpa using pushout_colimit_closed_point_lift (F := F) c x.asIdeal

-- Proof sketch: use Lemma 10.39.3 for the flatness part after forgetting the `R`-algebra diagram
-- to `R`-modules, then apply Lemma 10.39.16 to the closed-point lifting statement above.
/-- Lemma 10.39.20: if `c` is a colimit cocone of a filtered diagram of faithfully flat
commutative `R`-algebras, then its cocone point is faithfully flat over `R`. This is the
canonical filtered-diagram formulation in `Under (CommRingCat.of R)`. -/
@[stacks 090N]
theorem faithfullyFlat_of_isColimit_filtered_system
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, (hom (F.obj j).hom).FaithfullyFlat) :
    (hom c.pt.hom).FaithfullyFlat := by
  have hflat : (hom c.pt.hom).Flat :=
    flat_of_isColimit_filtered_system_under (F := F) c hc (fun j ↦ (hF j).1)
  -- Proof comment: Lemma `10.39.16` reduces faithful flatness to flatness plus the closed-point
  -- lifting statement proved above.
  rw [faithfullyFlat_iff_closedPoints_subset_range _ hflat]
  exact closed_points_subset_range_of_filtered_faithfully_flat_system F c hc hF

/-- Companion form of Lemma 10.39.20 for the chosen colimit object `colimit F`. -/
theorem faithfullyFlat_colimit_of_filtered_system
    [HasColimit F]
    (hF : ∀ j, (hom (F.obj j).hom).FaithfullyFlat) :
    (hom (colimit F).hom).FaithfullyFlat := by
  simpa using faithfullyFlat_of_isColimit_filtered_system F (colimit.cocone F)
    (colimit.isColimit F) hF

end
