import Mathlib.Tactic.StacksAttribute
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import stacks_proof.stacks_project.Chap04.Definition_4_22_2
import stacks_proof.stacks_project.Chap04.Lemma_4_22_3
import stacks_proof.stacks_project.Chap10.Lemma_10_86_4
import stacks_proof.stacks_project.Chap12.Definition_12_19_3
import stacks_proof.stacks_project.Chap12.Definition_12_31_2
import stacks_proof.stacks_project.Chap12.Lemma_12_31_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite Limits ComplexShape
open OrderDual (ofDual toDual)

noncomputable section

namespace CategoryTheory

namespace SequentialInverseSystem

/-- Helper for Lemma 12.31.7: shorthand for sequential inverse systems of abelian groups. -/
private abbrev AbSeq := SequentialInverseSystem AddCommGrpCat.{0}

/-- Helper for Lemma 12.31.7: shorthand for sequential inverse systems of cochain complexes of
abelian groups. -/
private abbrev AbCpxSeq := SequentialInverseSystem (CochainComplex AddCommGrpCat.{0} ℤ)

/-- Helper for Lemma 12.31.7: shorthand for evaluation in a fixed degree. -/
private abbrev ev := HomologicalComplex.eval AddCommGrpCat (up ℤ)

/-- Helper for Lemma 12.31.7: shorthand for the homology functor in a fixed degree. -/
private abbrev H := HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ)

/-- Helper for Lemma 12.31.7: shorthand for the cycles functor in a fixed degree. -/
private abbrev CyclesF := HomologicalComplex.cyclesFunctor AddCommGrpCat (up ℤ)

/-- Helper for Lemma 12.31.7: shorthand for the canonical projection from cycles to homology. -/
private abbrev πH := HomologicalComplex.natTransHomologyπ AddCommGrpCat (up ℤ)

/-- Helper for Lemma 12.31.7: evaluation functors jointly reflect isomorphisms in a functor
category. -/
private theorem functorEvaluationJointlyReflectsIsomorphisms
    (J : Type*) [Category J] (C : Type*) [Category C] :
    JointlyReflectIsomorphisms ((evaluation J C).obj : J → (J ⥤ C) ⥤ C) := by
  refine ⟨fun {X Y} f hf ↦ ?_⟩
  rw [NatTrans.isIso_iff_isIso_app]
  intro j
  simpa using hf j

/-- Helper for Lemma 12.31.7: evaluating a short exact sequence of sequential inverse systems of
abelian groups at a stage preserves short exactness. -/
private lemma shortExact_eval {S : ShortComplex AbSeq} {n : ℕ} (hS : S.ShortExact) :
    (S.map ((evaluation ℕᵒᵖ AddCommGrpCat).obj (op n))).ShortExact := by
  let ev₀ := (evaluation ℕᵒᵖ AddCommGrpCat).obj (op n)
  have hExactMono : (S.map ev₀).Exact ∧ Mono (S.map ev₀).f := by
    -- Evaluation preserves kernels, so the left exact part descends stagewise.
    simpa using
      (S.map ev₀).exact_and_mono_f_iff_f_is_kernel.2
        ⟨KernelFork.mapIsLimit _ hS.fIsKernel ev₀⟩
  refine ShortComplex.ShortExact.mk' hExactMono.1 hExactMono.2 ?_
  -- Epimorphy of the right map is also checked componentwise.
  exact (NatTrans.epi_iff_epi_app S.g).1 hS.epi_g (op n)

/-- Helper for Lemma 12.31.7: transition maps compose along chains of indices. -/
private theorem transitionMap_comp
    (F : AbSeq) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    F.transitionMap (Nat.le_trans hij hjk) = F.transitionMap hjk ≫ F.transitionMap hij := by
  have hcomp :
      (homOfLE (Nat.le_trans hij hjk)).op = (homOfLE hjk).op ≫ (homOfLE hij).op := by
    subsingleton
  simpa [SequentialInverseSystem.transitionMap, hcomp] using
    (Functor.map_comp F ((homOfLE hjk).op) ((homOfLE hij).op)).symm

/-- Helper for Lemma 12.31.7: stagewise short exactness gives exactness of the underlying
group homomorphisms. -/
private theorem shortExact_eval_function_exact {S : ShortComplex AbSeq} {n : ℕ}
    (hS : S.ShortExact) :
    Function.Exact (S.f.app (op n)).hom (S.g.app (op n)).hom := by
  -- Proof comment: after evaluating at stage `n`, exactness in `AddCommGrpCat` is equivalent to
  -- exactness of the underlying group homomorphisms.
  exact
    ((ShortComplex.ab_exact_iff_function_exact
      (S.map ((evaluation ℕᵒᵖ AddCommGrpCat).obj (op n)))).1
      (shortExact_eval hS).exact
    )

/-- Helper for Lemma 12.31.7: in `AddCommGrpCat`, precomposing with an epimorphism does not alter
the image subobject. -/
private lemma imageSubobject_comp_eq_of_epi_left
    {X Y Z : AddCommGrpCat} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi f] :
    imageSubobject (f ≫ g) = imageSubobject g := by
  let h := imageSubobject_comp_le f g
  let φ := Subobject.ofLE _ _ h
  haveI : Epi φ := by
    -- The comparison map out of the composite image is epi because the left factor is epi.
    dsimp [φ, h]
    infer_instance
  haveI : IsIso φ := isIso_of_mono_of_epi φ
  -- An isomorphism of subobjects gives the desired equality.
  exact Subobject.eq_of_comm (asIso φ) (by simp [φ])

/-- Helper for Lemma 12.31.7: the concrete inclusion of the range subgroup. -/
private abbrev rangeSubtypeHom {X Y : AddCommGrpCat.{0}} (f : X ⟶ Y) :
    AddCommGrpCat.of f.hom.range ⟶ Y := by
  let R := f.hom.range
  exact AddCommGrpCat.ofHom R.subtype

/-- Helper for Lemma 12.31.7: the concrete range inclusion in `AddCommGrpCat` is monic. -/
private instance rangeSubtype_mono {X Y : AddCommGrpCat.{0}} (f : X ⟶ Y) :
    Mono (rangeSubtypeHom f) :=
  ConcreteCategory.mono_of_injective _ Subtype.val_injective

/-- Helper for Lemma 12.31.7: the chosen representative of `imageSubobject f` maps to the
concrete range subgroup of `f`. -/
private theorem imageSubobject_to_range_arrow {X Y : AddCommGrpCat.{0}} (f : X ⟶ Y) :
    ((imageSubobjectIso f).hom ≫ (AddCommGrpCat.imageIsoRange f).hom) ≫
      rangeSubtypeHom f = (imageSubobject f).arrow := by
  rw [Category.assoc]
  change (imageSubobjectIso f).hom ≫ (AddCommGrpCat.imageIsoRange f).hom ≫
      AddCommGrpCat.image.ι f = (imageSubobject f).arrow
  rw [show (AddCommGrpCat.imageIsoRange f).hom ≫ AddCommGrpCat.image.ι f = image.ι f by
    simpa [AddCommGrpCat.imageIsoRange] using
      (IsImage.isoExt_hom_m (Image.isImage f) (AddCommGrpCat.isImage f))]
  simp

/-- Helper for Lemma 12.31.7: inclusion of image subobjects implies inclusion of the underlying
set-theoretic ranges in `AddCommGrpCat`. -/
private theorem range_subset_of_imageSubobject_le
    {X₁ X₂ Y : AddCommGrpCat.{0}} {f : X₁ ⟶ Y} {g : X₂ ⟶ Y}
    (h : imageSubobject f ≤ imageSubobject g) : Set.range f.hom ⊆ Set.range g.hom := by
  intro y hy
  rcases hy with ⟨x, rfl⟩
  let φ : X₁ ⟶ AddCommGrpCat.of g.hom.range :=
    factorThruImageSubobject f ≫ Subobject.ofLE _ _ h ≫
      (imageSubobjectIso g).hom ≫ (AddCommGrpCat.imageIsoRange g).hom
  have hφmor : φ ≫ rangeSubtypeHom g = f := by
    -- Compare the factorization through `imageSubobject g` with the original map `f`.
    dsimp [φ]
    calc
      factorThruImageSubobject f ≫
          Subobject.ofLE (imageSubobject f) (imageSubobject g) h ≫
            (imageSubobjectIso g).hom ≫
              (AddCommGrpCat.imageIsoRange g).hom ≫
                rangeSubtypeHom g
          = factorThruImageSubobject f ≫
              Subobject.ofLE (imageSubobject f) (imageSubobject g) h ≫
                (((imageSubobjectIso g).hom ≫ (AddCommGrpCat.imageIsoRange g).hom) ≫
                  rangeSubtypeHom g) := by
              simp [Category.assoc]
      _ = factorThruImageSubobject f ≫
            Subobject.ofLE (imageSubobject f) (imageSubobject g) h ≫
              (imageSubobject g).arrow := by
            rw [imageSubobject_to_range_arrow]
      _ = factorThruImageSubobject f ≫ (imageSubobject f).arrow := by
            rw [Subobject.ofLE_arrow]
      _ = f := by
            rw [imageSubobject_arrow_comp]
  -- Read off an explicit preimage from the concrete range subgroup.
  refine ⟨(φ.hom x).2.choose, ?_⟩
  have hφ := congrArg (fun u ↦ u.hom x) hφmor
  exact ((φ.hom x).2.choose_spec).trans hφ

/-- Helper for Lemma 12.31.7: equality of image subobjects gives equality of concrete ranges in
`AddCommGrpCat`. -/
private theorem range_eq_of_imageSubobject_eq
    {X₁ X₂ Y : AddCommGrpCat.{0}} {f : X₁ ⟶ Y} {g : X₂ ⟶ Y}
    (h : imageSubobject f = imageSubobject g) :
    Set.range f.hom = Set.range g.hom := by
  refine Set.Subset.antisymm ?_ ?_
  · exact range_subset_of_imageSubobject_le h.le
  · exact range_subset_of_imageSubobject_le h.ge

/-- Helper for Lemma 12.31.7: in `AddCommGrpCat`, the image subobject is the concrete range
subgroup viewed as a subobject. -/
private theorem imageSubobject_eq_range_mk {X Y : AddCommGrpCat.{0}} (f : X ⟶ Y) :
    imageSubobject f = Subobject.mk (rangeSubtypeHom f) := by
  exact CategoryTheory.Subobject.eq_mk_of_comm
    (rangeSubtypeHom f)
    ((imageSubobjectIso f).trans (AddCommGrpCat.imageIsoRange f))
    (imageSubobject_to_range_arrow f)

/-- Helper for Lemma 12.31.7: equality of concrete ranges induces an additive equivalence between
the corresponding range subgroups. -/
private noncomputable def rangeSubgroupAddEquivOfRangeEq
    {X₁ X₂ Y : AddCommGrpCat.{0}} {f : X₁ ⟶ Y} {g : X₂ ⟶ Y}
    (h : Set.range f.hom = Set.range g.hom) :
    f.hom.range ≃+ g.hom.range := by
  refine
    { toFun := fun x ↦ by
        refine ⟨x.1, ?_⟩
        change x.1 ∈ Set.range g.hom
        exact h ▸ x.2
      invFun := fun y ↦ by
        refine ⟨y.1, ?_⟩
        change y.1 ∈ Set.range f.hom
        exact h.symm ▸ y.2
      left_inv := by
        intro x
        ext
        rfl
      right_inv := by
        intro y
        ext
        rfl
      map_add' := by
        intro x y
        ext
        rfl }

/-- Helper for Lemma 12.31.7: equality of concrete ranges induces an isomorphism between the
corresponding range subgroups. -/
private noncomputable def rangeSubgroupIsoOfRangeEq
    {X₁ X₂ Y : AddCommGrpCat.{0}} {f : X₁ ⟶ Y} {g : X₂ ⟶ Y}
    (h : Set.range f.hom = Set.range g.hom) :
    AddCommGrpCat.of f.hom.range ≅ AddCommGrpCat.of g.hom.range :=
  (rangeSubgroupAddEquivOfRangeEq h).toAddCommGrpIso

/-- Helper for Lemma 12.31.7: equality of concrete ranges gives equality of image subobjects in
`AddCommGrpCat`. -/
private theorem imageSubobject_eq_of_range_eq
    {X₁ X₂ Y : AddCommGrpCat.{0}} {f : X₁ ⟶ Y} {g : X₂ ⟶ Y}
    (h : Set.range f.hom = Set.range g.hom) :
    imageSubobject f = imageSubobject g := by
  let e : AddCommGrpCat.of f.hom.range ≅ AddCommGrpCat.of g.hom.range :=
    rangeSubgroupIsoOfRangeEq h
  have he :
      e.hom ≫ rangeSubtypeHom g = rangeSubtypeHom f := by
    ext x
    change ((rangeSubgroupAddEquivOfRangeEq h) x).1 = x.1
    rfl
  calc
    imageSubobject f = Subobject.mk (rangeSubtypeHom f) :=
      imageSubobject_eq_range_mk f
    _ = Subobject.mk (rangeSubtypeHom g) :=
      CategoryTheory.Subobject.mk_eq_mk_of_comm
        (rangeSubtypeHom f)
        (rangeSubtypeHom g)
        e
        he
    _ = imageSubobject g := (imageSubobject_eq_range_mk g).symm

/-- Helper for Lemma 12.31.7: a morphism and a split-mono factor with the same two-sided
factorization have the same concrete range in `AddCommGrpCat`. -/
private theorem range_eq_of_splitMono_factorization
    {X Y Z : AddCommGrpCat.{0}} (f : X ⟶ Y) (g : Z ⟶ Y) (r : Y ⟶ Z)
    (hf : f = f ≫ r ≫ g)
    (hg : ∃ p : Z ⟶ X, p ≫ f = g) :
    Set.range f.hom = Set.range g.hom := by
  refine Set.Subset.antisymm ?_ ?_
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨r.hom (f.hom x), ?_⟩
    have hh := congrArg (fun t ↦ t.hom x) hf
    simpa [Category.assoc] using hh.symm
  · intro y hy
    rcases hg with ⟨p, hp⟩
    rcases hy with ⟨z, rfl⟩
    refine ⟨p.hom z, ?_⟩
    have hh := congrArg (fun t ↦ t.hom z) hp
    simpa [Category.assoc] using hh

/-- Helper for Lemma 12.31.7: cone legs of a sequential inverse system satisfy the expected
transition identity. -/
private theorem coneLeg_transition {F : AbSeq} {c : Cone F} {i j : ℕ} (hij : i ≤ j) :
    c.π.app (op j) ≫ F.transitionMap hij = c.π.app (op i) := by
  simpa [SequentialInverseSystem.transitionMap] using c.w ((homOfLE hij).op)

/-- Helper for Lemma 12.31.7: reindexing a short exact row along the `OrderDual ℕ`/`ℕᵒᵖ`
comparison preserves short exactness. -/
private lemma orderDual_shortExact_of_shortExact {S : ShortComplex AbSeq}
    (hS : S.ShortExact) :
    let e := CategoryTheory.orderDualEquivalence ℕ
    let W := (Functor.whiskeringLeft (OrderDual ℕ) ℕᵒᵖ AddCommGrpCat).obj e.functor
    (S.map W).ShortExact := by
  let e := CategoryTheory.orderDualEquivalence ℕ
  let W := (Functor.whiskeringLeft (OrderDual ℕ) ℕᵒᵖ AddCommGrpCat).obj e.functor
  -- Reindexing only precomposes the row, so exactness and mono/epi are preserved objectwise.
  simpa [W] using hS.map_of_exact W

/-- Helper for Lemma 12.31.7: the sequential Mittag-Leffler condition converts to the owner
`Type`-valued one after reindexing from `ℕᵒᵖ` to `OrderDual ℕ`. -/
private lemma orderDual_owner_isMittagLeffler_of_source_isMittagLeffler
    (F : AbSeq) (hF : F.IsMittagLeffler) :
    (((CategoryTheory.orderDualEquivalence ℕ).functor ⋙ F) ⋙
      forget AddCommGrpCat).IsMittagLeffler := by
  let e := CategoryTheory.orderDualEquivalence ℕ
  refine
    (Functor.isMittagLeffler_iff_subset_range_comp (((e.functor ⋙ F) ⋙ forget AddCommGrpCat))).2
      ?_
  intro i
  obtain ⟨c, hic, hstable⟩ := hF (ofDual i)
  refine ⟨toDual c, ?_, ?_⟩
  · -- Proof comment: the reindexed owner witness is the same stabilized transition morphism.
    simpa using (homOfLE hic : toDual c ⟶ toDual (ofDual i))
  · intro k g
    have hcg : c ≤ ofDual k := leOfHom g
    have hg : g = (homOfLE hcg : k ⟶ toDual c) := Subsingleton.elim _ _
    let f' : F.obj (op c) ⟶ F.obj (op (ofDual i)) := F.transitionMap hic
    let g' : F.obj (op (ofDual k)) ⟶ F.obj (op (ofDual i)) := F.transitionMap (hic.trans hcg)
    have himage : imageSubobject f' ≤ imageSubobject g' := by
      -- Proof comment: the source ML hypothesis already identifies these two image subobjects.
      simpa [f', g'] using (hstable hcg).symm.le
    have hsubset : Set.range f'.hom ⊆ Set.range g'.hom := by
      -- Proof comment: convert the stabilized image-subobject statement into a concrete range
      -- inclusion for the owner-valued ML criterion.
      exact
        @range_subset_of_imageSubobject_le
          (F.obj (op c)) (F.obj (op (ofDual k))) (F.obj (op (ofDual i)))
          f' g' himage
    simpa [e, hg, SequentialInverseSystem.transitionMap] using hsubset

/-- Helper for Lemma 12.31.7: the first square in the reindexed inverse-limit comparison
commutes. -/
private lemma orderDual_limit_map_shortComplex_iso_comm₁₂ (S : ShortComplex AbSeq) :
    let e := CategoryTheory.orderDualEquivalence ℕ
    let i₁ : limit (e.functor ⋙ S.X₁) ≅ limit S.X₁ :=
      HasLimit.isoOfEquivalence e (Iso.refl _)
    let i₂ : limit (e.functor ⋙ S.X₂) ≅ limit S.X₂ :=
      HasLimit.isoOfEquivalence e (Iso.refl _)
    i₁.hom ≫ limMap S.f = limMap (e.functor.whiskerLeft S.f) ≫ i₂.hom := by
  let e := CategoryTheory.orderDualEquivalence ℕ
  let i₁ : limit (e.functor ⋙ S.X₁) ≅ limit S.X₁ :=
    HasLimit.isoOfEquivalence e (Iso.refl _)
  let i₂ : limit (e.functor ⋙ S.X₂) ≅ limit S.X₂ :=
    HasLimit.isoOfEquivalence e (Iso.refl _)
  apply limit.hom_ext
  intro k
  simp_rw [Category.assoc]
  have hleft :
      i₁.hom ≫ limit.π S.X₁ k ≫ S.f.app k =
        limit.π (e.functor ⋙ S.X₁) (e.inverse.obj k) ≫
          (Iso.refl (e.functor ⋙ S.X₁)).inv.app (e.inverse.obj k) ≫
            S.X₁.map (e.counit.app k) ≫ S.f.app k := by
    simpa only [Category.assoc] using
      congrArg (fun φ ↦ φ ≫ S.f.app k)
        (HasLimit.isoOfEquivalence_hom_π e (Iso.refl (e.functor ⋙ S.X₁)) k)
  have hright :
      limMap (e.functor.whiskerLeft S.f) ≫
          limit.π (e.functor ⋙ S.X₂) (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₂)).inv.app (e.inverse.obj k) ≫
              S.X₂.map (e.counit.app k) =
        limit.π (e.functor ⋙ S.X₁) (e.inverse.obj k) ≫
          (e.functor.whiskerLeft S.f).app (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₂)).inv.app (e.inverse.obj k) ≫
              S.X₂.map (e.counit.app k) := by
    simpa only [Category.assoc] using
      congrArg
        (fun φ ↦
          φ ≫ (Iso.refl (e.functor ⋙ S.X₂)).inv.app (e.inverse.obj k) ≫
            S.X₂.map (e.counit.app k))
        (Limits.limMap_π (e.functor.whiskerLeft S.f) (e.inverse.obj k))
  have hmiddle :
      limit.π (e.functor ⋙ S.X₁) (e.inverse.obj k) ≫
          (Iso.refl (e.functor ⋙ S.X₁)).inv.app (e.inverse.obj k) ≫
            S.X₁.map (e.counit.app k) ≫ S.f.app k =
        limit.π (e.functor ⋙ S.X₁) (e.inverse.obj k) ≫
          (e.functor.whiskerLeft S.f).app (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₂)).inv.app (e.inverse.obj k) ≫
              S.X₂.map (e.counit.app k) := by
    simpa [CategoryTheory.orderDualEquivalence, Category.assoc] using
      congrArg
        (fun φ ↦
          limit.π (e.functor ⋙ S.X₁) (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₂)).inv.app (e.inverse.obj k) ≫ φ)
        (S.f.naturality (e.counit.app k))
  have hfinal :
      i₁.hom ≫ limit.π S.X₁ k ≫ S.f.app k =
        limMap (e.functor.whiskerLeft S.f) ≫
          limit.π (e.functor ⋙ S.X₂) (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₂)).inv.app (e.inverse.obj k) ≫
              S.X₂.map (e.counit.app k) := by
    exact hleft.trans (hmiddle.trans hright.symm)
  simpa [e, CategoryTheory.orderDualEquivalence, Category.assoc] using hfinal

/-- Helper for Lemma 12.31.7: the second square in the reindexed inverse-limit comparison
commutes. -/
private lemma orderDual_limit_map_shortComplex_iso_comm₂₃ (S : ShortComplex AbSeq) :
    let e := CategoryTheory.orderDualEquivalence ℕ
    let i₂ : limit (e.functor ⋙ S.X₂) ≅ limit S.X₂ :=
      HasLimit.isoOfEquivalence e (Iso.refl _)
    let i₃ : limit (e.functor ⋙ S.X₃) ≅ limit S.X₃ :=
      HasLimit.isoOfEquivalence e (Iso.refl _)
    i₂.hom ≫ limMap S.g = limMap (e.functor.whiskerLeft S.g) ≫ i₃.hom := by
  let e := CategoryTheory.orderDualEquivalence ℕ
  let i₂ : limit (e.functor ⋙ S.X₂) ≅ limit S.X₂ :=
    HasLimit.isoOfEquivalence e (Iso.refl _)
  let i₃ : limit (e.functor ⋙ S.X₃) ≅ limit S.X₃ :=
    HasLimit.isoOfEquivalence e (Iso.refl _)
  apply limit.hom_ext
  intro k
  simp_rw [Category.assoc]
  have hleft :
      i₂.hom ≫ limit.π S.X₂ k ≫ S.g.app k =
        limit.π (e.functor ⋙ S.X₂) (e.inverse.obj k) ≫
          (Iso.refl (e.functor ⋙ S.X₂)).inv.app (e.inverse.obj k) ≫
            S.X₂.map (e.counit.app k) ≫ S.g.app k := by
    simpa only [Category.assoc] using
      congrArg (fun φ ↦ φ ≫ S.g.app k)
        (HasLimit.isoOfEquivalence_hom_π e (Iso.refl (e.functor ⋙ S.X₂)) k)
  have hright :
      limMap (e.functor.whiskerLeft S.g) ≫
          limit.π (e.functor ⋙ S.X₃) (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₃)).inv.app (e.inverse.obj k) ≫
              S.X₃.map (e.counit.app k) =
        limit.π (e.functor ⋙ S.X₂) (e.inverse.obj k) ≫
          (e.functor.whiskerLeft S.g).app (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₃)).inv.app (e.inverse.obj k) ≫
              S.X₃.map (e.counit.app k) := by
    simpa only [Category.assoc] using
      congrArg
        (fun φ ↦
          φ ≫ (Iso.refl (e.functor ⋙ S.X₃)).inv.app (e.inverse.obj k) ≫
            S.X₃.map (e.counit.app k))
        (Limits.limMap_π (e.functor.whiskerLeft S.g) (e.inverse.obj k))
  have hmiddle :
      limit.π (e.functor ⋙ S.X₂) (e.inverse.obj k) ≫
          (Iso.refl (e.functor ⋙ S.X₂)).inv.app (e.inverse.obj k) ≫
            S.X₂.map (e.counit.app k) ≫ S.g.app k =
        limit.π (e.functor ⋙ S.X₂) (e.inverse.obj k) ≫
          (e.functor.whiskerLeft S.g).app (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₃)).inv.app (e.inverse.obj k) ≫
              S.X₃.map (e.counit.app k) := by
    simpa [CategoryTheory.orderDualEquivalence, Category.assoc] using
      congrArg
        (fun φ ↦
          limit.π (e.functor ⋙ S.X₂) (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₃)).inv.app (e.inverse.obj k) ≫ φ)
        (S.g.naturality (e.counit.app k))
  have hfinal :
      i₂.hom ≫ limit.π S.X₂ k ≫ S.g.app k =
        limMap (e.functor.whiskerLeft S.g) ≫
          limit.π (e.functor ⋙ S.X₃) (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₃)).inv.app (e.inverse.obj k) ≫
              S.X₃.map (e.counit.app k) := by
    exact hleft.trans (hmiddle.trans hright.symm)
  simpa [e, CategoryTheory.orderDualEquivalence, Category.assoc] using hfinal

/-- Helper for Lemma 12.31.7: after applying `lim`, the reindexed short complex is canonically
isomorphic to the original one. -/
private noncomputable def orderDual_limit_map_shortComplex_iso (S : ShortComplex AbSeq) :
    let e := CategoryTheory.orderDualEquivalence ℕ
    let W := (Functor.whiskeringLeft (OrderDual ℕ) ℕᵒᵖ AddCommGrpCat).obj e.functor
    ((S.map W).map (lim : (OrderDual ℕ ⥤ AddCommGrpCat) ⥤ AddCommGrpCat)) ≅
      S.map (lim : (ℕᵒᵖ ⥤ AddCommGrpCat) ⥤ AddCommGrpCat) :=
  let e := CategoryTheory.orderDualEquivalence ℕ
  let i₁ : limit (e.functor ⋙ S.X₁) ≅ limit S.X₁ :=
    HasLimit.isoOfEquivalence e (Iso.refl _)
  let i₂ : limit (e.functor ⋙ S.X₂) ≅ limit S.X₂ :=
    HasLimit.isoOfEquivalence e (Iso.refl _)
  let i₃ : limit (e.functor ⋙ S.X₃) ≅ limit S.X₃ :=
    HasLimit.isoOfEquivalence e (Iso.refl _)
  ShortComplex.isoMk i₁ i₂ i₃
    (orderDual_limit_map_shortComplex_iso_comm₁₂ S)
    (orderDual_limit_map_shortComplex_iso_comm₂₃ S)

/-- Helper for Lemma 12.31.7: in a short exact sequence of sequential inverse systems of abelian
groups, Mittag-Leffler on the middle term implies Mittag-Leffler on the quotient term. -/
private theorem isMittagLeffler_right_of_shortExact {S : ShortComplex AbSeq}
    (hS : S.ShortExact)
    (hML : S.X₂.IsMittagLeffler) :
    S.X₃.IsMittagLeffler := by
  intro i
  obtain ⟨c, hic, hstable⟩ := hML i
  refine ⟨c, hic, ?_⟩
  intro k hck
  have hnat_k :
      S.X₂.transitionMap (hic.trans hck) ≫ S.g.app (op i) =
        S.g.app (op k) ≫ S.X₃.transitionMap (hic.trans hck) := by
    -- Rewrite the transition map through naturality of the right morphism in the short complex.
    simpa [transitionMap] using S.g.naturality ((homOfLE (hic.trans hck)).op)
  have hnat_c :
      S.X₂.transitionMap hic ≫ S.g.app (op i) =
        S.g.app (op c) ≫ S.X₃.transitionMap hic := by
    -- The same naturality identity at the stabilizing stage `c`.
    simpa [transitionMap] using S.g.naturality ((homOfLE hic).op)
  letI : Epi (S.g.app (op k)) := (shortExact_eval hS).epi_g
  letI : Epi (S.g.app (op c)) := (shortExact_eval hS).epi_g
  -- Transport stabilized images in the middle row across the stagewise quotient maps.
  calc
    imageSubobject (S.X₃.transitionMap (hic.trans hck))
        = imageSubobject (S.g.app (op k) ≫ S.X₃.transitionMap (hic.trans hck)) := by
            symm
            simpa using
              imageSubobject_comp_eq_of_epi_left
                (S.g.app (op k)) (S.X₃.transitionMap (hic.trans hck))
    _ = imageSubobject (S.X₂.transitionMap (hic.trans hck) ≫ S.g.app (op i)) := by
          rw [← hnat_k]
    _ = imageSubobject
          ((imageSubobject (S.X₂.transitionMap (hic.trans hck))).arrow ≫ S.g.app (op i)) := by
          rw [Limits.imageSubobject_comp_eq_imageSubobject_restriction]
    _ = imageSubobject ((imageSubobject (S.X₂.transitionMap hic)).arrow ≫ S.g.app (op i)) := by
          rw [hstable hck]
    _ = imageSubobject (S.X₂.transitionMap hic ≫ S.g.app (op i)) := by
          rw [← Limits.imageSubobject_comp_eq_imageSubobject_restriction]
    _ = imageSubobject (S.g.app (op c) ≫ S.X₃.transitionMap hic) := by
          rw [hnat_c]
    _ = imageSubobject (S.X₃.transitionMap hic) := by
          simpa using
            imageSubobject_comp_eq_of_epi_left
              (S.g.app (op c)) (S.X₃.transitionMap hic)

/-- Helper for Lemma 12.31.7: if the left term of a short exact sequence of sequential inverse
systems of abelian groups is Mittag-Leffler, then the induced sequence on inverse limits is short
exact. -/
private theorem inverseLimit_shortExact_of_isMittagLeffler_left {S : ShortComplex AbSeq}
    (hS : S.ShortExact)
    (hML : S.X₁.IsMittagLeffler) :
    (S.map lim).ShortExact := by
  let e := CategoryTheory.orderDualEquivalence ℕ
  let W := (Functor.whiskeringLeft (OrderDual ℕ) ℕᵒᵖ AddCommGrpCat).obj e.functor
  let hReindexed :
      ((S.map W).map (lim : (OrderDual ℕ ⥤ AddCommGrpCat) ⥤ AddCommGrpCat)).ShortExact :=
    inverseSystem_limit_shortExact_of_countable_and_isMittagLeffler_left
      (S.map W)
      (orderDual_shortExact_of_shortExact hS)
      (orderDual_owner_isMittagLeffler_of_source_isMittagLeffler S.X₁ hML)
  -- Transport the short exactness statement back across the limit comparison isomorphism.
  exact ShortComplex.shortExact_of_iso
    (orderDual_limit_map_shortComplex_iso S)
    hReindexed

/-- Helper for Lemma 12.31.7: in a short exact sequence of sequential inverse systems of abelian
groups, Mittag-Leffler on the left and right terms implies Mittag-Leffler on the middle term. -/
private theorem isMittagLeffler_middle_of_shortExact_local
    (S : ShortComplex AbSeq)
    (hS : S.ShortExact)
    (hA : S.X₁.IsMittagLeffler)
    (hC : S.X₃.IsMittagLeffler) :
    S.X₂.IsMittagLeffler := by
  -- Proof comment: stabilize the left images first, then use the right-term stabilization to
  -- correct a chosen lift stagewise and recover equality of middle images.
  intro i
  obtain ⟨cA, hicA, hAstable⟩ := hA i
  obtain ⟨c, hcA, hCstable⟩ := hC cA
  let hic : i ≤ c := Nat.le_trans hicA hcA
  refine ⟨c, hic, ?_⟩
  intro k hck
  apply imageSubobject_eq_of_range_eq
  refine Set.Subset.antisymm ?_ ?_
  · intro b hb
    rcases hb with ⟨bk, rfl⟩
    refine ⟨(S.X₂.transitionMap hck).hom bk, ?_⟩
    have hcomp := congrArg
      (fun t ↦ t.hom bk)
      (transitionMap_comp S.X₂ hic hck)
    simpa [hic] using hcomp.symm
  · intro b hb
    rcases hb with ⟨bc, rfl⟩
    have hkA : cA ≤ k := Nat.le_trans hcA hck
    have hCrange :
        Set.range ((S.X₃.transitionMap (Nat.le_trans hcA hck)).hom) =
          Set.range ((S.X₃.transitionMap hcA).hom) := by
      exact range_eq_of_imageSubobject_eq (hCstable hck)
    let zcA : S.X₃.obj (op cA) := (S.X₃.transitionMap hcA).hom ((S.g.app (op c)).hom bc)
    have hz_mem :
        zcA ∈ Set.range ((S.X₃.transitionMap (Nat.le_trans hcA hck)).hom) := by
      rw [hCrange]
      exact ⟨(S.g.app (op c)).hom bc, rfl⟩
    obtain ⟨zk, hzk⟩ := hz_mem
    have hsurj_gk :
        Function.Surjective (S.g.app (op k)).hom := by
      exact (AddCommGrpCat.epi_iff_surjective (S.g.app (op k))).1
        ((shortExact_eval hS).epi_g)
    obtain ⟨bk', hbk'⟩ := hsurj_gk zk
    let diff : S.X₂.obj (op cA) :=
      (S.X₂.transitionMap hcA).hom bc -
        (S.X₂.transitionMap (Nat.le_trans hcA hck)).hom bk'
    have hnat_c_mor :
        S.X₂.transitionMap hcA ≫ S.g.app (op cA) =
          S.g.app (op c) ≫ S.X₃.transitionMap hcA := by
      simpa [SequentialInverseSystem.transitionMap] using
        S.g.naturality ((homOfLE hcA).op)
    have hnat_c := congrArg
      (fun t ↦ (ConcreteCategory.hom t) bc)
      hnat_c_mor
    have hnat_k_mor :
        S.X₂.transitionMap (Nat.le_trans hcA hck) ≫ S.g.app (op cA) =
          S.g.app (op k) ≫ S.X₃.transitionMap (Nat.le_trans hcA hck) := by
      simpa [SequentialInverseSystem.transitionMap] using
        S.g.naturality ((homOfLE (Nat.le_trans hcA hck)).op)
    have hnat_k := congrArg
      (fun t ↦ (ConcreteCategory.hom t) bk')
      hnat_k_mor
    have hzero_diff : (S.g.app (op cA)).hom diff = 0 := by
      have hnat_c' :
          (S.g.app (op cA)).hom ((S.X₂.transitionMap hcA).hom bc) = zcA := by
        simpa [zcA, Category.assoc] using hnat_c
      have hnat_k' :
          (S.g.app (op cA)).hom ((S.X₂.transitionMap (Nat.le_trans hcA hck)).hom bk') = zcA := by
        simpa [zcA, hbk', hzk, Category.assoc] using hnat_k
      simp [diff, map_sub, hnat_c', hnat_k']
    have hExact_cA : Function.Exact (S.f.app (op cA)).hom (S.g.app (op cA)).hom :=
      shortExact_eval_function_exact hS
    have hdiff_mem :
        diff ∈ Set.range (S.f.app (op cA)).hom := (hExact_cA diff).1 hzero_diff
    obtain ⟨acA, hacA⟩ := hdiff_mem
    have hA_mem :
        (S.X₁.transitionMap hicA).hom acA ∈
          Set.range ((S.X₁.transitionMap (Nat.le_trans hicA hkA)).hom) := by
      have hArange :
          Set.range ((S.X₁.transitionMap (Nat.le_trans hicA hkA)).hom) =
            Set.range ((S.X₁.transitionMap hicA).hom) := by
        exact range_eq_of_imageSubobject_eq (hAstable hkA)
      rw [hArange]
      exact ⟨acA, rfl⟩
    obtain ⟨ak, hak⟩ := hA_mem
    have hnat_f_cA_mor :
        S.X₁.transitionMap hicA ≫ S.f.app (op i) =
          S.f.app (op cA) ≫ S.X₂.transitionMap hicA := by
      simpa [SequentialInverseSystem.transitionMap] using
        S.f.naturality ((homOfLE hicA).op)
    have hnat_f_cA := congrArg
      (fun t ↦ (ConcreteCategory.hom t) acA)
      hnat_f_cA_mor
    have hEq1 :
        (S.f.app (op i)).hom ((S.X₁.transitionMap hicA).hom acA) =
          (S.X₂.transitionMap hic).hom bc -
            (S.X₂.transitionMap (Nat.le_trans hic hck)).hom bk' := by
      calc
        (S.f.app (op i)).hom ((S.X₁.transitionMap hicA).hom acA)
            = (S.X₂.transitionMap hicA).hom ((S.f.app (op cA)).hom acA) := by
                simpa [Category.assoc] using hnat_f_cA
        _ = (S.X₂.transitionMap hicA).hom diff := by
              rw [hacA]
        _ = (S.X₂.transitionMap hicA).hom ((S.X₂.transitionMap hcA).hom bc) -
              (S.X₂.transitionMap hicA).hom
                ((S.X₂.transitionMap (Nat.le_trans hcA hck)).hom bk') := by
              simp [diff, map_sub]
        _ = (S.X₂.transitionMap hic).hom bc -
              (S.X₂.transitionMap (Nat.le_trans hic hck)).hom bk' := by
              have hcomp_c :
                  (S.X₂.transitionMap hicA).hom ((S.X₂.transitionMap hcA).hom bc) =
                    (S.X₂.transitionMap hic).hom bc := by
                have hcomp := congrArg
                  (fun t ↦ t.hom bc)
                  (transitionMap_comp S.X₂ hicA hcA)
                simpa [hic, Category.assoc] using hcomp.symm
              have hcomp_k :
                  (S.X₂.transitionMap hicA).hom
                      ((S.X₂.transitionMap (Nat.le_trans hcA hck)).hom bk') =
                    (S.X₂.transitionMap (Nat.le_trans hic hck)).hom bk' := by
                have hcomp := congrArg
                  (fun t ↦ t.hom bk')
                  (transitionMap_comp S.X₂ hicA (Nat.le_trans hcA hck))
                simpa [hic, Category.assoc] using hcomp.symm
              rw [hcomp_c, hcomp_k]
    have hsum :
        (S.X₂.transitionMap hic).hom bc =
          (S.X₂.transitionMap (Nat.le_trans hic hck)).hom bk' +
            (S.f.app (op i)).hom ((S.X₁.transitionMap hicA).hom acA) := by
      rw [eq_sub_iff_add_eq] at hEq1
      simpa [add_comm, add_left_comm, add_assoc] using hEq1.symm
    have hnat_f_k_mor :
        S.X₁.transitionMap (Nat.le_trans hic hck) ≫ S.f.app (op i) =
          S.f.app (op k) ≫ S.X₂.transitionMap (Nat.le_trans hic hck) := by
      simpa [SequentialInverseSystem.transitionMap] using
        S.f.naturality ((homOfLE (Nat.le_trans hic hck)).op)
    have hnat_f_k := congrArg
      (fun t ↦ (ConcreteCategory.hom t) ak)
      hnat_f_k_mor
    have hmap_ak :
        (S.X₂.transitionMap (Nat.le_trans hic hck)).hom ((S.f.app (op k)).hom ak) =
          (S.f.app (op i)).hom ((S.X₁.transitionMap hicA).hom acA) := by
      have hmap_ak' :
          (S.f.app (op i)).hom ((S.X₁.transitionMap (Nat.le_trans hic hck)).hom ak) =
            (S.X₂.transitionMap (Nat.le_trans hic hck)).hom ((S.f.app (op k)).hom ak) := by
        simpa [Category.assoc] using hnat_f_k
      simpa [hak, hic] using hmap_ak'.symm
    refine ⟨bk' + (S.f.app (op k)).hom ak, ?_⟩
    calc
      (S.X₂.transitionMap (Nat.le_trans hic hck)).hom (bk' + (S.f.app (op k)).hom ak)
          = (S.X₂.transitionMap (Nat.le_trans hic hck)).hom bk' +
              (S.X₂.transitionMap (Nat.le_trans hic hck)).hom ((S.f.app (op k)).hom ak) := by
                simp
      _ = (S.X₂.transitionMap (Nat.le_trans hic hck)).hom bk' +
            (S.f.app (op i)).hom ((S.X₁.transitionMap hicA).hom acA) := by
              rw [hmap_ak]
      _ = (S.X₂.transitionMap hic).hom bc := by
              simpa [add_comm, add_left_comm, add_assoc] using hsum.symm

/-- Helper for Lemma 12.31.7: the degreewise cocycle tower of a sequential inverse system of
cochain complexes. -/
noncomputable abbrev cyclesTower (A : AbCpxSeq) (n : ℤ) :
    SequentialInverseSystem AddCommGrpCat :=
  A ⋙ CyclesF n

/-- Helper for Lemma 12.31.7: the degreewise cohomology tower of a sequential inverse system of
cochain complexes. -/
noncomputable abbrev homologyTower (A : AbCpxSeq) (n : ℤ) :
    SequentialInverseSystem AddCommGrpCat :=
  A ⋙ H n

/-- Helper for Lemma 12.31.7: the natural transformation from cocycles to the ambient degree. -/
@[simps! app]
noncomputable def cyclesInclusionNatTrans (n : ℤ) :
    CyclesF n ⟶ ev n where
  app K := K.iCycles n
  naturality {K L} f := by
    -- Naturality is exactly the standard `cyclesMap_i` identity.
    simpa using (HomologicalComplex.cyclesMap_i f n)

/-- Helper for Lemma 12.31.7: naturality of the degreewise differential map between evaluation
functors. -/
private theorem differentialNatTrans_naturality
    {K L : CochainComplex AddCommGrpCat.{0} ℤ} (f : K ⟶ L) (i j : ℤ) :
    f.f i ≫ L.d i j = K.d i j ≫ f.f j := by
  -- Proof comment: this is exactly the chain-map compatibility with the differential.
  simpa using f.comm i j

/-- Helper for Lemma 12.31.7: the degreewise differential as a natural transformation between
evaluation functors. -/
@[simps! app]
private noncomputable def differentialBetweenNatTrans (i j : ℤ) :
    ev i ⟶ ev j where
  app K := K.d i j
  naturality {_ _} f := differentialNatTrans_naturality f i j

/-- Helper for Lemma 12.31.7: the degreewise differential as a natural transformation between
successive evaluations. -/
@[simps! app]
noncomputable def differentialNatTrans (n : ℤ) :
    ev n ⟶ ev (n + 1) :=
  differentialBetweenNatTrans n (n + 1)

/-- Helper for Lemma 12.31.7: the canonical `toCycles` map is natural in the complex variable. -/
private theorem toCyclesNatTrans_naturality
    (n : ℤ) {K L : CochainComplex AddCommGrpCat.{0} ℤ} (f : K ⟶ L) :
    f.f (n - 1) ≫ L.toCycles (n - 1) n =
      K.toCycles (n - 1) n ≫ HomologicalComplex.cyclesMap f n := by
  -- Proof comment: compare after the monomorphism from cycles into degree `n`.
  apply (cancel_mono (L.iCycles n)).1
  simpa [Category.assoc] using
    differentialNatTrans_naturality f (n - 1) n

/-- Helper for Lemma 12.31.7: the shifted `toCycles` map is natural in the complex variable. -/
private theorem toCyclesNatTransSucc_naturality
    (n : ℤ) {K L : CochainComplex AddCommGrpCat.{0} ℤ} (f : K ⟶ L) :
    f.f n ≫ L.toCycles n (n + 1) =
      K.toCycles n (n + 1) ≫ HomologicalComplex.cyclesMap f (n + 1) := by
  -- Proof comment: this is the same naturality argument one degree higher.
  apply (cancel_mono (L.iCycles (n + 1))).1
  simpa [Category.assoc] using
    differentialNatTrans_naturality f n (n + 1)

/-- Helper for Lemma 12.31.7: the natural transformation induced by the previous differential on
degreewise cocycles. -/
-- Route correction: the source proof uses the canonical boundary map `A_i^{n - 1} → Z_i^n`,
-- so we package the owner `ShortComplex.toCycles` map instead of unfolding the differential by
-- hand.
noncomputable def toCyclesNatTrans (n : ℤ) :
    ev (n - 1) ⟶ CyclesF n where
  app K := K.toCycles (n - 1) n
  naturality {_ _} f := toCyclesNatTrans_naturality n f

/-- Helper for Lemma 12.31.7: the natural transformation induced by the differential
`A_i^n ⟶ Z_i^(n + 1)`. -/
noncomputable def toCyclesNatTransSucc (n : ℤ) :
    ev n ⟶ CyclesF (n + 1) where
  app K := K.toCycles n (n + 1)
  naturality {_ _} f := toCyclesNatTransSucc_naturality n f

/-- Helper for Lemma 12.31.7: the cocycle inclusion followed by the ambient differential
vanishes stagewise. -/
@[reassoc (attr := simp)]
theorem cyclesInclusionNatTrans_comp_differentialNatTrans_zero (n : ℤ) :
    cyclesInclusionNatTrans n ≫ differentialNatTrans n = 0 := by
  -- Proof comment: cocycles land in the kernel of the next differential.
  apply NatTrans.ext
  funext K
  change K.iCycles n ≫ K.d n (n + 1) = 0
  exact HomologicalComplex.iCycles_d K n (n + 1)

/-- Helper for Lemma 12.31.7: the canonical map to degree-`n` cycles followed by the inclusion
back into degree `n` is the ambient differential from degree `n - 1`. -/
@[reassoc (attr := simp)]
theorem toCyclesNatTrans_comp_cyclesInclusionNatTrans (n : ℤ) :
    toCyclesNatTrans n ≫ cyclesInclusionNatTrans n = differentialBetweenNatTrans (n - 1) n := by
  -- Proof comment: stagewise, `toCycles` followed by the cycle inclusion is the differential.
  apply NatTrans.ext
  funext K
  change (toCyclesNatTrans n).app K ≫ K.iCycles n = K.d (n - 1) n
  exact HomologicalComplex.toCycles_i K (n - 1) n

/-- Helper for Lemma 12.31.7: the canonical map to degree-`n` cycles dies in degree-`n`
homology. -/
@[reassoc (attr := simp)]
theorem toCyclesNatTrans_comp_homologyπ_zero (n : ℤ) :
    toCyclesNatTrans n ≫ πH n = 0 := by
  -- Proof comment: boundaries die in homology stagewise.
  apply NatTrans.ext
  funext K
  change (toCyclesNatTrans n).app K ≫ K.homologyπ n = 0
  exact HomologicalComplex.toCycles_comp_homologyπ K (n - 1) n

/-- Helper for Lemma 12.31.7: stagewise, a cocycle maps to zero under the next `toCycles` map. -/
private theorem iCycles_comp_toCycles_succ_zero
    (K : CochainComplex AddCommGrpCat.{0} ℤ) (n : ℤ) :
    K.iCycles n ≫ K.toCycles n (n + 1) = 0 := by
  -- Proof comment: after the target cycles inclusion, this becomes `iCycles_d`.
  apply (cancel_mono (K.iCycles (n + 1))).1
  rw [Category.assoc, HomologicalComplex.toCycles_i]
  simpa using (HomologicalComplex.iCycles_d K n (n + 1))

/-- Helper for Lemma 12.31.7: the cocycle inclusion followed by the next `toCycles` map vanishes
stagewise. -/
@[reassoc (attr := simp)]
theorem cyclesInclusionNatTrans_comp_toCyclesNatTrans_succ_zero (n : ℤ) :
    cyclesInclusionNatTrans n ≫ toCyclesNatTransSucc n = 0 := by
  -- Proof comment: this is the stagewise identity `iCycles ≫ toCycles = 0`.
  apply NatTrans.ext
  funext K
  exact iCycles_comp_toCycles_succ_zero K n

/-- Helper for Lemma 12.31.7: the shifted `toCycles` map also dies in homology. -/
@[reassoc (attr := simp)]
private theorem toCyclesNatTransSucc_comp_homologyπ_zero (n : ℤ) :
    toCyclesNatTransSucc n ≫ πH (n + 1) = 0 := by
  -- Proof comment: this is the same boundary-to-homology vanishing one degree higher.
  apply NatTrans.ext
  funext K
  change (toCyclesNatTransSucc n).app K ≫ K.homologyπ (n + 1) = 0
  exact HomologicalComplex.toCycles_comp_homologyπ K n (n + 1)

/-- Helper for Lemma 12.31.7: whiskering the vanishing `toCycles ≫ πH` identity along the inverse
system still gives zero. -/
private theorem whiskerLeft_toCyclesNatTrans_comp_homologyπ_zero
    (A : AbCpxSeq) (n : ℤ) :
    Functor.whiskerLeft A (toCyclesNatTrans n) ≫ Functor.whiskerLeft A (πH n) = 0 := by
  -- Proof comment: evaluate the whiskered natural transformations stagewise.
  apply NatTrans.ext
  funext i
  exact NatTrans.congr_app (toCyclesNatTrans_comp_homologyπ_zero n) (A.obj i)

/-- Helper for Lemma 12.31.7: whiskering the shifted vanishing identity still gives zero. -/
private theorem whiskerLeft_toCyclesNatTransSucc_comp_homologyπ_zero
    (A : AbCpxSeq) (n : ℤ) :
    Functor.whiskerLeft A (toCyclesNatTransSucc n) ≫
      Functor.whiskerLeft A (πH (n + 1)) = 0 := by
  -- Proof comment: evaluate the shifted identity stagewise.
  apply NatTrans.ext
  funext i
  exact NatTrans.congr_app (toCyclesNatTransSucc_comp_homologyπ_zero n) (A.obj i)

/-- Helper for Lemma 12.31.7: the tower of boundaries in degree `n`, realized as the kernel of the
cycle-to-homology map. -/
noncomputable abbrev boundaryTower (A : AbCpxSeq) (n : ℤ) :
    SequentialInverseSystem AddCommGrpCat :=
  kernel (Functor.whiskerLeft A (πH n))

/-- Helper for Lemma 12.31.7: the canonical inclusion of the boundary tower into the cocycle
tower. -/
noncomputable abbrev boundaryInclusion (A : AbCpxSeq) (n : ℤ) :
    boundaryTower A n ⟶ cyclesTower A n :=
  kernel.ι (Functor.whiskerLeft A (πH n))

/-- Helper for Lemma 12.31.7: the map from degree `n - 1` terms to degree-`n` boundaries induced
by the previous differential. -/
-- This is the textbook map `A_i^{n - 1} → I_i^n`, expressed in the kernel model of boundaries.
noncomputable def degreeToBoundaryNatTrans (A : AbCpxSeq) (n : ℤ) :
    A ⋙ ev (n - 1) ⟶ boundaryTower A n :=
  kernel.lift (Functor.whiskerLeft A (πH n))
    (Functor.whiskerLeft A (toCyclesNatTrans n))
    (whiskerLeft_toCyclesNatTrans_comp_homologyπ_zero A n)

/-- Helper for Lemma 12.31.7: the map from degree `n` terms to degree-`n + 1` boundaries induced
by the differential `A_i^n ⟶ A_i^{n + 1}`. -/
noncomputable def degreeToBoundaryNatTransSucc (A : AbCpxSeq) (n : ℤ) :
    A ⋙ ev n ⟶ boundaryTower A (n + 1) :=
  kernel.lift (Functor.whiskerLeft A (πH (n + 1)))
    (Functor.whiskerLeft A (toCyclesNatTransSucc n))
    (whiskerLeft_toCyclesNatTransSucc_comp_homologyπ_zero A n)

/-- Helper for Lemma 12.31.7: the degree-to-boundary map followed by the boundary inclusion is the
usual `toCycles` map. -/
@[reassoc (attr := simp)]
theorem degreeToBoundaryNatTrans_comp_boundaryInclusion (A : AbCpxSeq) (n : ℤ) :
    degreeToBoundaryNatTrans A n ≫ boundaryInclusion A n =
      Functor.whiskerLeft A (toCyclesNatTrans n) := by
  -- Proof comment: this is exactly the defining equation of the kernel lift.
  simp [degreeToBoundaryNatTrans, boundaryInclusion]

/-- Helper for Lemma 12.31.7: the shifted degree-to-boundary map followed by the boundary
inclusion is the shifted `toCycles` map. -/
@[reassoc (attr := simp)]
private theorem degreeToBoundaryNatTransSucc_comp_boundaryInclusion
    (A : AbCpxSeq) (n : ℤ) :
    degreeToBoundaryNatTransSucc A n ≫ boundaryInclusion A (n + 1) =
      Functor.whiskerLeft A (toCyclesNatTransSucc n) := by
  -- Proof comment: the shifted boundary map is defined by the same kernel-lift construction.
  simp [degreeToBoundaryNatTransSucc, boundaryInclusion]

/-- Helper for Lemma 12.31.7: the boundary inclusion followed by the quotient-to-homology map
vanishes. -/
theorem boundaryInclusion_comp_homologyπ_zero (A : AbCpxSeq) (n : ℤ) :
    boundaryInclusion A n ≫ Functor.whiskerLeft A (πH n) = 0 := by
  -- The boundary tower was defined as the kernel of the quotient-to-homology map.
  simp [boundaryInclusion]

/-- Helper for Lemma 12.31.7: the canonical short complex
`0 ⟶ B^n ⟶ Z^n ⟶ H^n`. -/
noncomputable abbrev boundaryToCyclesToHomologyShortComplex (A : AbCpxSeq) (n : ℤ) :
    ShortComplex (SequentialInverseSystem AddCommGrpCat) :=
  ShortComplex.mk (boundaryInclusion A n) (Functor.whiskerLeft A (πH n))
    (boundaryInclusion_comp_homologyπ_zero A n)

/-- Helper for Lemma 12.31.7: the boundary tower sits in a short exact sequence
`0 ⟶ B^n ⟶ Z^n ⟶ H^n ⟶ 0`. -/
theorem boundary_to_cycles_to_homology_shortExact (A : AbCpxSeq) (n : ℤ) :
    (boundaryToCyclesToHomologyShortComplex A n).ShortExact := by
  let S : ShortComplex (SequentialInverseSystem AddCommGrpCat) :=
    boundaryToCyclesToHomologyShortComplex A n
  refine ShortComplex.ShortExact.mk' ?_ inferInstance ?_
  -- The left map is the defining kernel inclusion of `Functor.whiskerLeft A (πH n)`.
  · exact ShortComplex.exact_of_f_is_kernel S
      (kernelIsKernel (Functor.whiskerLeft A (πH n)))
  -- The homology projection is stagewise surjective in `AddCommGrpCat`, hence epi as a
  -- natural transformation.
  · exact (NatTrans.epi_iff_epi_app (Functor.whiskerLeft A (πH n))).2 fun i ↦ by
      simpa [πH] using (inferInstance : Epi ((A.obj i).homologyπ n))

/-- Helper for Lemma 12.31.7: stagewise, the row `0 ⟶ Z^n ⟶ A^n ⟶ Z^(n+1)` is exact. -/
private theorem stage_cycles_to_degree_to_cycles_exact
    (K : CochainComplex AddCommGrpCat.{0} ℤ) (n : ℤ) :
    let T : ShortComplex AddCommGrpCat.{0} :=
      ShortComplex.mk (K.iCycles n) (K.toCycles n (n + 1))
        (iCycles_comp_toCycles_succ_zero K n)
    T.Exact := by
  -- Proof comment: a morphism killed by `toCycles` is already a cycle, so it factors uniquely
  -- through `K.iCycles n`.
  apply ShortComplex.exact_of_f_is_kernel
  exact KernelFork.IsLimit.ofι' _ _ (fun {A} k hk ↦ by
    have hk' : k ≫ K.d n (n + 1) = 0 := by
      have hkι := congrArg (fun t ↦ t ≫ K.iCycles (n + 1)) hk
      simpa [Category.assoc] using hkι
    refine ⟨K.liftCycles k (n + 1) (CochainComplex.next ℤ n) hk', ?_⟩
    simpa using K.liftCycles_i k (n + 1) (CochainComplex.next ℤ n) hk')

/-- Helper for Lemma 12.31.7: stagewise, the source-proof row
`0 ⟶ Z^n ⟶ A^n ⟶ B^(n+1)` is exact. -/
private theorem stage_cycles_to_degree_to_boundary_exact
    (K : CochainComplex AddCommGrpCat.{0} ℤ) (n : ℤ) :
    let T : ShortComplex AddCommGrpCat.{0} :=
      ShortComplex.mk (K.iCycles n)
        (kernel.lift (K.homologyπ (n + 1)) (K.toCycles n (n + 1))
          (HomologicalComplex.toCycles_comp_homologyπ K n (n + 1)))
        (by
          -- The boundary lift still vanishes on cocycles by the previous exact row.
          apply (cancel_mono (kernel.ι (K.homologyπ (n + 1)))).1
          rw [Category.assoc, kernel.lift_ι, zero_comp]
          simpa using iCycles_comp_toCycles_succ_zero K n)
    T.Exact := by
  let U : ShortComplex AddCommGrpCat.{0} :=
    ShortComplex.mk (K.iCycles n) (K.toCycles n (n + 1))
      (iCycles_comp_toCycles_succ_zero K n)
  have hU : U.Exact := by
    -- Reuse the previous exactness lemma after unfolding the local abbreviation.
    simpa [U] using stage_cycles_to_degree_to_cycles_exact K n
  let T : ShortComplex AddCommGrpCat.{0} :=
    ShortComplex.mk (K.iCycles n)
      (kernel.lift (K.homologyπ (n + 1)) (K.toCycles n (n + 1))
        (HomologicalComplex.toCycles_comp_homologyπ K n (n + 1)))
      (by
        apply (cancel_mono (kernel.ι (K.homologyπ (n + 1)))).1
        rw [Category.assoc, kernel.lift_ι, zero_comp]
        simpa using iCycles_comp_toCycles_succ_zero K n)
  let φ : T ⟶ U :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι (K.homologyπ (n + 1))
      comm₁₂ := by simp [T, U]
      comm₂₃ := by
        -- The boundary map is the kernel lift of the `toCycles` map.
        simp [T, U] }
  -- The kernel inclusion on the right is mono, so exactness transports from the cocycle row.
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hU

/-- Helper for Lemma 12.31.7: exactness of the cocycle row makes the canonical morphism to the
kernel subobject of the homology projection stagewise epi. -/
theorem stage_factorThruKernelSubobject_epi_of_cycles_exact
    (K : CochainComplex AddCommGrpCat.{0} ℤ) (n : ℤ) :
    Epi
      (factorThruKernelSubobject (K.homologyπ (n + 1)) (K.toCycles n (n + 1))
        (HomologicalComplex.toCycles_comp_homologyπ K n (n + 1))) := by
  let S : ShortComplex AddCommGrpCat.{0} :=
    ShortComplex.mk (K.toCycles n (n + 1)) (K.homologyπ (n + 1))
      (HomologicalComplex.toCycles_comp_homologyπ K n (n + 1))
  have hS : S.Exact := by
    -- Proof comment: the canonical short complex defining `H^(n + 1)` is exact by construction.
    have hCokernel : IsColimit (CokernelCofork.ofπ S.g S.zero) := by
      simpa [S] using
        (K.homologyIsCokernel n (n + 1) (by simp))
    exact ShortComplex.exact_of_g_is_cokernel S hCokernel
  have hImageToKernel : Epi (imageToKernel S.f S.g S.zero) := by
    -- Proof comment: exactness identifies the kernel subobject with the image of the previous map.
    exact (ShortComplex.exact_iff_epi_imageToKernel S).1 hS
  letI : Epi (factorThruImageSubobject S.f ≫ imageToKernel S.f S.g S.zero) := by
    infer_instance
  have hfactor :
      factorThruImageSubobject S.f ≫ imageToKernel S.f S.g S.zero =
        factorThruKernelSubobject S.g S.f S.zero := by
    -- Proof comment: the canonical map through the image is exactly the kernel-subobject factor.
    simpa using
      factorThruImageSubobject_comp_imageToKernel S.f S.g S.zero
  simpa [S, hfactor] using
    (inferInstance : Epi (factorThruImageSubobject S.f ≫ imageToKernel S.f S.g S.zero))

/-- Helper for Lemma 12.31.7: transporting the kernel-subobject epi across the canonical kernel
isomorphism gives the actual stagewise boundary map. -/
theorem stage_degreeToBoundary_epi_of_kernelSubobject
    (K : CochainComplex AddCommGrpCat.{0} ℤ) (n : ℤ) :
    Epi
      (kernel.lift (K.homologyπ (n + 1)) (K.toCycles n (n + 1))
        (HomologicalComplex.toCycles_comp_homologyπ K n (n + 1))) := by
  let g := K.homologyπ (n + 1)
  let f := K.toCycles n (n + 1)
  let hzero : f ≫ g = 0 :=
    HomologicalComplex.toCycles_comp_homologyπ K n (n + 1)
  letI : Epi (factorThruKernelSubobject g f hzero) := by
    simpa [g, f, hzero] using stage_factorThruKernelSubobject_epi_of_cycles_exact K n
  letI : Epi (factorThruKernelSubobject g f hzero ≫ (kernelSubobjectIso g).hom) := by
    infer_instance
  have hcomp :
      factorThruKernelSubobject g f hzero ≫ (kernelSubobjectIso g).hom =
        kernel.lift g f hzero := by
    simpa using factorThruKernelSubobject_comp_kernelSubobjectIso g f hzero
  simpa [g, f, hzero, hcomp] using
    (inferInstance : Epi (factorThruKernelSubobject g f hzero ≫ (kernelSubobjectIso g).hom))

/-- Helper for Lemma 12.31.7: evaluating the shifted degree-to-boundary map and then including
into cocycles recovers the stagewise `toCycles` map. -/
private theorem degreeToBoundaryNatTransSucc_app_comp_boundaryInclusion
    (A : AbCpxSeq) (n : ℤ) (i : ℕᵒᵖ) :
    (degreeToBoundaryNatTransSucc A n).app i ≫ (boundaryInclusion A (n + 1)).app i =
      (A.obj i).toCycles n (n + 1) := by
  -- Proof comment: evaluate the global kernel-lift identity at stage `i`.
  change
    (degreeToBoundaryNatTransSucc A n ≫ boundaryInclusion A (n + 1)).app i =
      (Functor.whiskerLeft A (toCyclesNatTransSucc n)).app i
  exact NatTrans.congr_app (degreeToBoundaryNatTransSucc_comp_boundaryInclusion A n) i

/-- Helper for Lemma 12.31.7: the cocycle inclusion followed by the boundary map vanishes. -/
theorem cyclesInclusionNatTrans_comp_degreeToBoundaryNatTrans_succ_zero
    (A : AbCpxSeq) (n : ℤ) :
    Functor.whiskerLeft A (cyclesInclusionNatTrans n) ≫ degreeToBoundaryNatTransSucc A n = 0 := by
  -- Proof comment: compare after the mono boundary inclusion, where the composite becomes the
  -- whiskered stagewise identity `iCycles ≫ toCycles = 0`.
  apply NatTrans.ext
  funext i
  change
    (Functor.whiskerLeft A (cyclesInclusionNatTrans n)).app i ≫
      (degreeToBoundaryNatTransSucc A n).app i = 0
  letI : Mono ((boundaryInclusion A (n + 1)).app i) :=
    (NatTrans.mono_iff_mono_app (boundaryInclusion A (n + 1))).1 inferInstance i
  apply (cancel_mono ((boundaryInclusion A (n + 1)).app i)).1
  rw [Category.assoc, degreeToBoundaryNatTransSucc_app_comp_boundaryInclusion]
  rw [zero_comp]
  simpa using iCycles_comp_toCycles_succ_zero (A.obj i) n

/-- Helper for Lemma 12.31.7: the source-proof row `0 ⟶ Z^n ⟶ A^n ⟶ B^(n+1) ⟶ 0`. -/
noncomputable abbrev cyclesToDegreeToBoundaryShortComplex (A : AbCpxSeq) (n : ℤ) :
    ShortComplex (SequentialInverseSystem AddCommGrpCat) :=
  ShortComplex.mk
    (Functor.whiskerLeft A (cyclesInclusionNatTrans n))
    (degreeToBoundaryNatTransSucc A n)
    (cyclesInclusionNatTrans_comp_degreeToBoundaryNatTrans_succ_zero A n)

/-- Helper for Lemma 12.31.7: the textbook second row
`0 ⟶ Z^n ⟶ A^n ⟶ B^(n+1) ⟶ 0` is short exact. -/
theorem cycles_to_degree_to_boundary_succ_shortExact (A : AbCpxSeq) (n : ℤ) :
    (cyclesToDegreeToBoundaryShortComplex A n).ShortExact := by
  -- Route correction: in this file the evaluated boundary tower is already definitionally the
  -- stagewise kernel object, so the short exact row is recovered directly after evaluation.
  refine
    ((functorEvaluationJointlyReflectsIsomorphisms ℕᵒᵖ AddCommGrpCat).shortExact_iff
      (cyclesToDegreeToBoundaryShortComplex A n)).2 ?_
  intro i
  let Sstage : ShortComplex AddCommGrpCat.{0} :=
    ShortComplex.mk
      ((A.obj i).iCycles n)
      (kernel.lift ((A.obj i).homologyπ (n + 1)) ((A.obj i).toCycles n (n + 1))
        (HomologicalComplex.toCycles_comp_homologyπ (A.obj i) n (n + 1)))
      (by
        -- Proof comment: the stagewise boundary lift still vanishes on cocycles.
        apply (cancel_mono (kernel.ι ((A.obj i).homologyπ (n + 1)))).1
        rw [Category.assoc, kernel.lift_ι, zero_comp]
        simpa using iCycles_comp_toCycles_succ_zero (A.obj i) n)
  have hSstage : Sstage.ShortExact := by
    -- Proof comment: this is the already-proved stagewise short exact row.
    refine ShortComplex.ShortExact.mk' ?_ inferInstance ?_
    · simpa [Sstage] using stage_cycles_to_degree_to_boundary_exact (A.obj i) n
    · simpa [Sstage] using stage_degreeToBoundary_epi_of_kernelSubobject (A.obj i) n
  let Seval : ShortComplex AddCommGrpCat.{0} :=
    (cyclesToDegreeToBoundaryShortComplex A n).map ((evaluation ℕᵒᵖ AddCommGrpCat).obj i)
  let e₃ : Seval.X₃ ≅ Sstage.X₃ := by
    simpa [Seval, Sstage, cyclesToDegreeToBoundaryShortComplex, boundaryTower, πH] using
      (PreservesKernel.iso ((evaluation ℕᵒᵖ AddCommGrpCat).obj i)
        (Functor.whiskerLeft A (πH (n + 1))))
  have hBoundaryInclusion :
      (boundaryInclusion A (n + 1)).app i =
        e₃.hom ≫ kernel.ι ((A.obj i).homologyπ (n + 1)) := by
    have hι :
        e₃.inv ≫ (boundaryInclusion A (n + 1)).app i =
          kernel.ι ((A.obj i).homologyπ (n + 1)) := by
      simpa [e₃, Seval, Sstage, boundaryInclusion, boundaryTower, πH] using
        (PreservesKernel.iso_inv_ι ((evaluation ℕᵒᵖ AddCommGrpCat).obj i)
          (Functor.whiskerLeft A (πH (n + 1))))
    have hcomp :
        (boundaryInclusion A (n + 1)).app i =
          e₃.hom ≫ e₃.inv ≫ (boundaryInclusion A (n + 1)).app i := by
      simpa [Category.assoc] using
        (Iso.hom_inv_id_assoc e₃ ((boundaryInclusion A (n + 1)).app i)).symm
    have hpost :
        e₃.hom ≫ e₃.inv ≫ (boundaryInclusion A (n + 1)).app i =
          e₃.hom ≫ kernel.ι ((A.obj i).homologyπ (n + 1)) := by
      simpa [Category.assoc] using congrArg (fun t ↦ e₃.hom ≫ t) hι
    exact hcomp.trans hpost
  have hSeval_g :
      Seval.g ≫ e₃.hom =
        kernel.lift ((A.obj i).homologyπ (n + 1)) ((A.obj i).toCycles n (n + 1))
          (HomologicalComplex.toCycles_comp_homologyπ (A.obj i) n (n + 1)) := by
    -- Proof comment: the evaluated degree-to-boundary morphism becomes the stagewise kernel lift
    -- after the canonical comparison of the evaluated kernel object.
    apply (cancel_mono (kernel.ι ((A.obj i).homologyπ (n + 1)))).1
    change (degreeToBoundaryNatTransSucc A n).app i ≫ e₃.hom ≫
        kernel.ι ((A.obj i).homologyπ (n + 1)) =
      kernel.lift ((A.obj i).homologyπ (n + 1)) ((A.obj i).toCycles n (n + 1))
        (HomologicalComplex.toCycles_comp_homologyπ (A.obj i) n (n + 1)) ≫
          kernel.ι ((A.obj i).homologyπ (n + 1))
    rw [kernel.lift_ι]
    simpa [Category.assoc, hBoundaryInclusion, Seval] using
      degreeToBoundaryNatTransSucc_app_comp_boundaryInclusion A n i
  let e : Sstage ≅ Seval :=
    { hom :=
        { τ₁ := 𝟙 _
          τ₂ := 𝟙 _
          τ₃ := e₃.inv
          comm₁₂ := by simp [Sstage, Seval, cyclesToDegreeToBoundaryShortComplex]
          comm₂₃ := by
            apply (cancel_mono e₃.hom).1
            simpa [Sstage, Seval, Category.assoc] using hSeval_g }
      inv :=
        { τ₁ := 𝟙 _
          τ₂ := 𝟙 _
          τ₃ := e₃.hom
          comm₁₂ := by simp [Sstage, Seval, cyclesToDegreeToBoundaryShortComplex]
          comm₂₃ := by simpa [Sstage, Seval, Category.assoc] using hSeval_g.symm }
      hom_inv_id := by ext <;> simp [Sstage, Seval]
      inv_hom_id := by ext <;> simp [Sstage, Seval] }
  -- Proof comment: after evaluation, only the right map needs this explicit normal-form rewrite.
  exact ShortComplex.shortExact_of_iso e hSstage

/-- Helper for Lemma 12.31.7: the image of a composite is the image of the right map restricted
to the image of the left map. -/
private theorem imageSubobject_comp_eq_imageSubobject_restriction
    {X Y Z : AddCommGrpCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    imageSubobject (f ≫ g) = imageSubobject ((imageSubobject f).arrow ≫ g) := by
  let h := imageSubobject_comp_le (factorThruImageSubobject f) ((imageSubobject f).arrow ≫ g)
  let φ := Subobject.ofLE _ _ h
  haveI : Epi φ := by
    -- The comparison map out of the composite image is epi because the left factor is epi.
    dsimp [φ, h]
    infer_instance
  haveI : IsIso φ := isIso_of_mono_of_epi φ
  have :
      imageSubobject (factorThruImageSubobject f ≫ (imageSubobject f).arrow ≫ g) =
        imageSubobject ((imageSubobject f).arrow ≫ g) :=
    Subobject.eq_of_comm (asIso φ) (by simp [φ])
  simpa [Category.assoc] using this

/-- Helper for Lemma 12.31.7: an essentially constant sequential inverse system of abelian groups
is Mittag-Leffler. -/
private theorem isMittagLeffler_of_essentiallyConstant_local
    (F : AbSeq)
    (hF : IsEssentiallyConstantCofilteredDiagram F) :
    F.IsMittagLeffler := by
  obtain ⟨c, hc⟩ :=
    essentiallyConstantCofilteredDiagram_exists_essentiallyConstant_limitCone F hF
  rcases (isEssentiallyConstantCofilteredCone_iff c.cone).1 hc with ⟨i₀, σ, hfac⟩
  let N : ℕ := i₀.unop
  intro i
  rcases hfac (op i) with ⟨k, ki, kj, hk⟩
  let m : ℕ := k.unop
  have hNm : N ≤ m := leOfHom ki.unop
  have him : i ≤ m := leOfHom kj.unop
  let stable : F.obj (op N) ⟶ F.obj (op i) := σ.retraction ≫ c.cone.π.app (op i)
  have hbase : F.transitionMap him = F.transitionMap hNm ≫ stable := by
    -- Proof comment: the distinguished retraction writes the chosen transition to stage `i`
    -- through the fixed stage `N`.
    simpa [N, m, stable, SequentialInverseSystem.transitionMap, Category.assoc] using hk
  refine ⟨m, him, ?_⟩
  intro l hml
  have hil : i ≤ l := Nat.le_trans him hml
  have hfactor :
      F.transitionMap hil = F.transitionMap hml ≫ F.transitionMap hNm ≫ stable := by
    rw [transitionMap_comp F him hml, hbase]
  have hstable_factor :
      stable = (σ.retraction ≫ c.cone.π.app (op l)) ≫ F.transitionMap hil := by
    -- Proof comment: the stable map is recovered from any later stage by projecting to the cone
    -- point and then back to stage `i`.
    have hcone : c.cone.π.app (op l) ≫ F.transitionMap hil = c.cone.π.app (op i) :=
      coneLeg_transition hil
    have hleg :=
      congrArg (fun t ↦ σ.retraction ≫ t) hcone
    simpa [stable, Category.assoc] using hleg.symm
  have hRange :
      Set.range (F.transitionMap hil).hom = Set.range stable.hom := by
    refine Set.Subset.antisymm ?_ ?_
    · intro y hy
      rcases hy with ⟨x, rfl⟩
      refine ⟨(F.transitionMap hml ≫ F.transitionMap hNm).hom x, ?_⟩
      have hh := congrArg (fun t ↦ t.hom x) hfactor
      simpa [Category.assoc] using hh.symm
    · intro y hy
      rcases hy with ⟨x, rfl⟩
      refine ⟨(σ.retraction ≫ c.cone.π.app (op l)).hom x, ?_⟩
      have hh := congrArg (fun t ↦ t.hom x) hstable_factor
      simpa [Category.assoc] using hh
  have hRangeBase :
      Set.range (F.transitionMap him).hom = Set.range stable.hom := by
    refine Set.Subset.antisymm ?_ ?_
    · intro y hy
      rcases hy with ⟨x, rfl⟩
      refine ⟨(F.transitionMap hNm).hom x, ?_⟩
      have hh := congrArg (fun t ↦ t.hom x) hbase
      simpa [Category.assoc] using hh.symm
    · intro y hy
      rcases hy with ⟨x, rfl⟩
      refine ⟨(σ.retraction ≫ c.cone.π.app (op m)).hom x, ?_⟩
      have hstable_base :
          stable = (σ.retraction ≫ c.cone.π.app (op m)) ≫ F.transitionMap him := by
        have hcone : c.cone.π.app (op m) ≫ F.transitionMap him = c.cone.π.app (op i) :=
          coneLeg_transition him
        have hleg :=
          congrArg (fun t ↦ σ.retraction ≫ t) hcone
        simpa [stable, Category.assoc] using hleg.symm
      have hh := congrArg (fun t ↦ t.hom x) hstable_base
      simpa [Category.assoc] using hh
  exact imageSubobject_eq_of_range_eq (hRange.trans hRangeBase.symm)

/-- Helper for Lemma 12.31.7: the middle term of a short exact sequence of sequential inverse
systems of abelian groups is Mittag-Leffler when the left term is Mittag-Leffler and the right
term is essentially constant. -/
theorem isMittagLeffler_middle_of_shortExact_of_essentiallyConstant_right_local
    {S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{0})}
    (hS : S.ShortExact)
    (hML : S.X₁.IsMittagLeffler)
    (hC : IsEssentiallyConstantCofilteredDiagram S.X₃) :
    S.X₂.IsMittagLeffler := by
  -- Proof comment: essentially constant quotient towers are already Mittag-Leffler, so the
  -- existing short-exactness argument upgrades the middle term directly.
  let T : ShortComplex AbSeq := S
  have hT : T.ShortExact := by
    simpa [T] using hS
  have hTML : T.X₁.IsMittagLeffler := by
    simpa [T] using hML
  have hTC : T.X₃.IsMittagLeffler := by
    simpa [T] using isMittagLeffler_of_essentiallyConstant_local T.X₃ hC
  simpa [T] using isMittagLeffler_middle_of_shortExact_local T hT hTML hTC

/-- Helper for Lemma 12.31.7: the source row `0 ⟶ Z^n ⟶ A^n ⟶ B^(n+1) ⟶ 0` transports the
Mittag-Leffler property from the degree-`n` evaluation tower to the degree-`n + 1` boundary
tower. -/
private theorem boundaryTower_isMittagLeffler_of_eval
    (A : AbCpxSeq) (n : ℤ)
    (hA : IsMittagLeffler (A ⋙ ev n)) :
    IsMittagLeffler (boundaryTower A (n + 1)) := by
  let T : ShortComplex (SequentialInverseSystem AddCommGrpCat) :=
    cyclesToDegreeToBoundaryShortComplex A n
  have hT : T.ShortExact := by
    -- Proof comment: this is exactly the textbook row `0 ⟶ Z^n ⟶ A^n ⟶ B^(n+1) ⟶ 0`.
    simpa [T] using cycles_to_degree_to_boundary_succ_shortExact A n
  have hTmid : T.X₂.IsMittagLeffler := by
    simpa [T, cyclesToDegreeToBoundaryShortComplex] using hA
  -- Proof comment: the right-hand tower of a short exact row inherits Mittag-Leffler from the
  -- middle tower, matching the source proof's passage from `A^n` to `B^(n+1)`.
  simpa [T, cyclesToDegreeToBoundaryShortComplex, boundaryTower] using
    isMittagLeffler_right_of_shortExact hT hTmid

/-- Helper for Lemma 12.31.7: the source row `0 ⟶ B^n ⟶ Z^n ⟶ H^n ⟶ 0` upgrades the
Mittag-Leffler property from boundaries to cycles once the degree-`n` homology tower is
essentially constant. -/
private theorem cyclesTower_isMittagLeffler_of_boundary_and_essentiallyConstantHomology
    (A : AbCpxSeq) (n : ℤ)
    (hBoundary : IsMittagLeffler (boundaryTower A n))
    (hH : IsEssentiallyConstantCofilteredDiagram (A ⋙ H n)) :
    IsMittagLeffler (cyclesTower A n) := by
  let T : ShortComplex (SequentialInverseSystem AddCommGrpCat) :=
    boundaryToCyclesToHomologyShortComplex A n
  have hT : T.ShortExact := by
    -- Proof comment: this is the textbook row `0 ⟶ B^n ⟶ Z^n ⟶ H^n ⟶ 0`.
    simpa [T] using boundary_to_cycles_to_homology_shortExact A n
  -- Proof comment: Lemma 12.31.6 turns essential constancy of the quotient tower into
  -- Mittag-Leffler for the middle tower of this short exact row.
  simpa [T, boundaryToCyclesToHomologyShortComplex, cyclesTower, homologyTower] using
    isMittagLeffler_middle_of_shortExact_of_essentiallyConstant_right_local
      hT hBoundary hH

/-- Helper for Lemma 12.31.7: taking the degree-`n` term of the inverse limit of a sequential
inverse system of cochain complexes is canonically the inverse limit of the degree-`n` terms. -/
noncomputable def limit_degree_iso (A : AbCpxSeq) (n : ℤ) :
    (limit A).X n ≅ limit (A ⋙ ev n) :=
  (isLimitOfPreserves (ev n) (limit.isLimit A)).conePointUniqueUpToIso
    (limit.isLimit (A ⋙ ev n))

/-- Helper for Lemma 12.31.7: the degreewise limit isomorphism intertwines each projection with
the corresponding evaluated projection. -/
lemma limit_degree_iso_hom_π (A : AbCpxSeq) (n : ℤ) (j : ℕᵒᵖ) :
    (limit_degree_iso A n).hom ≫ limit.π (A ⋙ ev n) j =
      (limit.π A j).f n := by
  -- Proof comment: this is the universal property of the preserved limit under evaluation.
  simpa [limit_degree_iso] using
    (isLimitOfPreserves (ev n) (limit.isLimit A)).conePointUniqueUpToIso_hom_comp
      (limit.isLimit (A ⋙ ev n)) j

/-- Helper for Lemma 12.31.7: the inverse of the degreewise limit isomorphism recovers the
canonical projection to each stage. -/
lemma limit_degree_iso_inv_π (A : AbCpxSeq) (n : ℤ) (j : ℕᵒᵖ) :
    (limit_degree_iso A n).inv ≫ (limit.π A j).f n =
      limit.π (A ⋙ ev n) j := by
  -- Proof comment: this is the inverse projection formula dual to `limit_degree_iso_hom_π`.
  simpa [limit_degree_iso] using
    (isLimitOfPreserves (ev n) (limit.isLimit A)).conePointUniqueUpToIso_inv_comp
      (limit.isLimit (A ⋙ ev n)) j

/-- Helper for Lemma 12.31.7: after postcomposing with a stage projection, the transported
degreewise differential is the expected stage differential. -/
lemma limit_degree_iso_inv_comp_differential_π (A : AbCpxSeq) (n : ℤ) (j : ℕᵒᵖ) :
    (limit_degree_iso A n).inv ≫ (limit A).d n (n + 1) ≫ (limit.π A j).f (n + 1) =
      limit.π (A ⋙ ev n) j ≫ (differentialNatTrans n).app (A.obj j) := by
  -- Proof comment: rewrite the limit differential against the stage projection, then use the
  -- degreewise projection formula for `limit_degree_iso`.
  rw [← differentialNatTrans_naturality (limit.π A j) n (n + 1)]
  rw [← Category.assoc, limit_degree_iso_inv_π]
  rfl

/-- Helper for Lemma 12.31.7: each degree component of the limit cone satisfies the expected
transition identity. -/
private lemma limitProjection_f_naturality
    (A : AbCpxSeq) {i j : ℕᵒᵖ} (f : i ⟶ j) (n : ℤ) :
    (limit.π A i).f n ≫ (A.map f).f n = (limit.π A j).f n := by
  -- Proof comment: this is the degreewise component of the cone relation for the limit cone.
  exact congrArg (fun t ↦ t.f n) ((limit.cone A).w f)

lemma limit_degree_iso_inv_comp_differential (A : AbCpxSeq) (n : ℤ) :
    (limit_degree_iso A n).inv ≫ (limit A).d n (n + 1) =
      lim.map (Functor.whiskerLeft A (differentialNatTrans n)) ≫
        (limit_degree_iso A (n + 1)).inv := by
  -- Proof comment: compare both morphisms after moving into the degree-`n + 1` inverse limit and
  -- postcomposing with each stage projection.
  apply (cancel_mono ((limit_degree_iso A (n + 1)).hom)).1
  apply limit.hom_ext
  intro j
  have h1 :
      ((limit_degree_iso A n).inv ≫ (limit A).d n (n + 1)) ≫
          (limit_degree_iso A (n + 1)).hom ≫ limit.π (A ⋙ ev (n + 1)) j
        =
      ((limit_degree_iso A n).inv ≫ (limit A).d n (n + 1)) ≫
        (limit.π A j).f (n + 1) := by
    simpa [Category.assoc] using congrArg
      (fun t ↦ ((limit_degree_iso A n).inv ≫ (limit A).d n (n + 1)) ≫ t)
      (limit_degree_iso_hom_π A (n + 1) j)
  have h2 :
      ((limit_degree_iso A n).inv ≫ (limit A).d n (n + 1)) ≫
          (limit.π A j).f (n + 1)
        =
      limit.π (A ⋙ ev n) j ≫ (differentialNatTrans n).app (A.obj j) := by
    exact limit_degree_iso_inv_comp_differential_π A n j
  have h3 :
      limit.π (A ⋙ ev n) j ≫ (differentialNatTrans n).app (A.obj j)
        =
      lim.map (Functor.whiskerLeft A (differentialNatTrans n)) ≫
        limit.π (A ⋙ ev (n + 1)) j := by
    simpa [Category.assoc] using
      (Limits.limMap_π (Functor.whiskerLeft A (differentialNatTrans n)) j).symm
  have h4 :
      lim.map (Functor.whiskerLeft A (differentialNatTrans n)) ≫
          limit.π (A ⋙ ev (n + 1)) j
        =
      ((lim.map (Functor.whiskerLeft A (differentialNatTrans n)) ≫
            (limit_degree_iso A (n + 1)).inv) ≫
          (limit_degree_iso A (n + 1)).hom) ≫
        limit.π (A ⋙ ev (n + 1)) j := by
    simp [Category.assoc]
  exact h1.trans (h2.trans (h3.trans h4))

/-- Helper for Lemma 12.31.7: the candidate cocycle fork over the limit differential satisfies
the kernel condition. -/
private theorem limitCyclesDegreeZeroKernelFork_condition (A : AbCpxSeq) :
    lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
        (limit_degree_iso A 0).inv ≫ (limit A).d 0 1 = 0 := by
  -- Proof comment: rewrite the transported differential stagewise and use that cocycle
  -- inclusions are killed by the next differential.
  apply (cancel_mono ((limit_degree_iso A 1).hom)).1
  apply limit.hom_ext
  intro j
  rw [zero_comp]
  have hzero :=
    NatTrans.congr_app (cyclesInclusionNatTrans_comp_differentialNatTrans_zero 0) (A.obj j)
  have h1 :
      (lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
            (limit_degree_iso A 0).inv ≫ (limit A).d 0 1) ≫
          (limit_degree_iso A 1).hom ≫ limit.π (A ⋙ ev 1) j
        =
      lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
        (limit_degree_iso A 0).inv ≫ (limit A).d 0 1 ≫ (limit.π A j).f 1 := by
    simpa [Category.assoc] using congrArg
      (fun t ↦
        (lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
            (limit_degree_iso A 0).inv ≫ (limit A).d 0 1) ≫ t)
      (limit_degree_iso_hom_π A 1 j)
  have h2a :
      lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
          (limit_degree_iso A 0).inv ≫ (limit A).d 0 1 ≫ (limit.π A j).f 1
        =
      lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
        limit.π (A ⋙ ev 0) j ≫ (differentialNatTrans 0).app (A.obj j) := by
    simpa [Category.assoc] using congrArg
      (fun t ↦ lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫ t)
      (limit_degree_iso_inv_comp_differential_π A 0 j)
  have h2b :
      lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
          limit.π (A ⋙ ev 0) j ≫ (differentialNatTrans 0).app (A.obj j)
        =
      limit.π (cyclesTower A 0) j ≫
        (cyclesInclusionNatTrans 0).app (A.obj j) ≫
          (differentialNatTrans 0).app (A.obj j) := by
    simpa [Category.assoc] using congrArg
      (fun t ↦ t ≫ (differentialNatTrans 0).app (A.obj j))
      (Limits.limMap_π (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) j)
  have h3 :
      limit.π (cyclesTower A 0) j ≫
          (cyclesInclusionNatTrans 0).app (A.obj j) ≫
            (differentialNatTrans 0).app (A.obj j)
        = 0 := by
    simpa [Category.assoc] using
      congrArg (fun t ↦ limit.π (cyclesTower A 0) j ≫ t) hzero
  have h4 : (0 : limit (cyclesTower A 0) ⟶ (A.obj j).X 1) = 0 ≫ limit.π (A ⋙ ev 1) j := by
    simp
  exact h1.trans (h2a.trans (h2b.trans (h3.trans h4)))

/-- Helper for Lemma 12.31.7: the candidate kernel fork comparing inverse-limit degree-`0`
cocycles with the degree-`0` differential of `limit A`. -/
noncomputable def limitCyclesDegreeZeroKernelFork (A : AbCpxSeq) :
    KernelFork ((limit A).d 0 1) :=
  KernelFork.ofι
    (lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫ (limit_degree_iso A 0).inv)
    (limitCyclesDegreeZeroKernelFork_condition A)

/-- Helper for Lemma 12.31.7: a map into the degree-`0` limit object that lands in the kernel of
the limit differential remains a cocycle after projection to each stage. -/
private lemma limitCyclesDegreeZero_stagewiseZero
    {W : AddCommGrpCat.{0}} (A : AbCpxSeq) (k : W ⟶ (limit A).X 0)
    (hk : k ≫ (limit A).d 0 1 = 0) (j : ℕᵒᵖ) :
    k ≫ (limit.π A j).f 0 ≫ (A.obj j).d 0 1 = 0 := by
  -- Proof comment: project the global cocycle condition along the `j`-th cone leg.
  calc
    k ≫ (limit.π A j).f 0 ≫ (A.obj j).d 0 1
        = k ≫ (limit A).d 0 1 ≫ (limit.π A j).f 1 := by
            simp [differentialNatTrans_naturality (limit.π A j) 0 1]
    _ = 0 := by
          simpa [Category.assoc] using congrArg (fun t ↦ t ≫ (limit.π A j).f 1) hk

/-- Helper for Lemma 12.31.7: the direct stagewise cocycle lifts form a cone over the degree-`0`
cocycle tower. -/
private noncomputable def limitCyclesDegreeZeroLiftCone
    {W : AddCommGrpCat.{0}} (A : AbCpxSeq) (k : W ⟶ (limit A).X 0)
    (hk : k ≫ (limit A).d 0 1 = 0) :
    Cone (cyclesTower A 0) :=
  { pt := W
    π :=
      { app := fun j ↦
          (A.obj j).liftCycles (k ≫ (limit.π A j).f 0) 1 (by simp)
            (limitCyclesDegreeZero_stagewiseZero A k hk j)
        naturality := by
          intro i j f
          -- Proof comment: compare the chosen cocycle lifts after composing with the target
          -- cocycle inclusion, where the equality becomes the cone relation for `limit A`.
          apply (cancel_mono ((A.obj j).iCycles 0)).1
          simpa [Category.assoc] using
            congrArg (fun t ↦ k ≫ t) (limitProjection_f_naturality A f 0).symm } }

/-- Helper for Lemma 12.31.7: the direct stagewise cocycle lifts recover the original map after
composing with the cocycle inclusion into the degreewise limit. -/
private theorem limitCyclesDegreeZeroLiftCone_lift_ι
    {W : AddCommGrpCat.{0}} (A : AbCpxSeq) (k : W ⟶ (limit A).X 0)
    (hk : k ≫ (limit A).d 0 1 = 0) :
    limit.lift (cyclesTower A 0) (limitCyclesDegreeZeroLiftCone A k hk) ≫
        lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
          (limit_degree_iso A 0).inv =
      k := by
  -- Proof comment: compare after composing with the degreewise limit isomorphism and then with
  -- each stage projection of `A^0`.
  apply (cancel_mono ((limit_degree_iso A 0).hom)).1
  apply limit.hom_ext
  intro j
  have hπincl :
      lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
          limit.π (A ⋙ ev 0) j =
        limit.π (cyclesTower A 0) j ≫ (A.obj j).iCycles 0 := by
    simpa using (Limits.limMap_π (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) j)
  have h1 :
      ((limit.lift (cyclesTower A 0) (limitCyclesDegreeZeroLiftCone A k hk) ≫
              lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
                (limit_degree_iso A 0).inv) ≫
            (limit_degree_iso A 0).hom) ≫
          limit.π (A ⋙ ev 0) j
        =
      limit.lift (cyclesTower A 0) (limitCyclesDegreeZeroLiftCone A k hk) ≫
        lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
          limit.π (A ⋙ ev 0) j := by
    simp [Category.assoc]
  have h2 :
      limit.lift (cyclesTower A 0) (limitCyclesDegreeZeroLiftCone A k hk) ≫
          lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
            limit.π (A ⋙ ev 0) j
        =
      limit.lift (cyclesTower A 0) (limitCyclesDegreeZeroLiftCone A k hk) ≫
        limit.π (cyclesTower A 0) j ≫ (A.obj j).iCycles 0 := by
    simpa [Category.assoc] using congrArg
      (fun t ↦ limit.lift (cyclesTower A 0) (limitCyclesDegreeZeroLiftCone A k hk) ≫ t)
      hπincl
  have h3 :
      limit.lift (cyclesTower A 0) (limitCyclesDegreeZeroLiftCone A k hk) ≫
          limit.π (cyclesTower A 0) j ≫ (A.obj j).iCycles 0
        =
      k ≫ (limit.π A j).f 0 := by
    simpa [limitCyclesDegreeZeroLiftCone, Category.assoc] using
      congrArg (fun t ↦ t ≫ (A.obj j).iCycles 0)
        (limit.lift_π (limitCyclesDegreeZeroLiftCone A k hk) j)
  have h4 :
      k ≫ (limit.π A j).f 0 =
        (k ≫ (limit_degree_iso A 0).hom) ≫ limit.π (A ⋙ ev 0) j := by
    simpa [Category.assoc] using
      (congrArg (fun t ↦ k ≫ t) (limit_degree_iso_hom_π A 0 j)).symm
  exact h1.trans (h2.trans (h3.trans h4))

/-- Helper for Lemma 12.31.7: the inverse limit of the degree-`0` cocycle tower is a kernel of
the differential of the limit complex. -/
private noncomputable def limit_cycles_degree_zero_isKernel_aux (A : AbCpxSeq) :
    IsLimit (limitCyclesDegreeZeroKernelFork A) :=
  -- Proof comment: a map into `(limit A)^0` lands in the kernel exactly when its stagewise
  -- projections are cocycles, and the chosen `liftCycles` maps assemble into the required limit
  -- cone over `cyclesTower A 0`.
  KernelFork.IsLimit.ofι
    (lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫ (limit_degree_iso A 0).inv)
    (limitCyclesDegreeZeroKernelFork_condition A)
    (fun {W} k hk ↦
    limit.lift (cyclesTower A 0) (limitCyclesDegreeZeroLiftCone A k hk))
    (fun {W} k hk ↦ limitCyclesDegreeZeroLiftCone_lift_ι A k hk)
    (fun {W} k hk m hm ↦ by
      apply limit.hom_ext
      intro j
      apply (cancel_mono ((A.obj j).iCycles 0)).1
      have hmj := congrArg (fun t ↦ t ≫ (limit.π A j).f 0) hm
      have hliftj := congrArg (fun t ↦ t ≫ (limit.π A j).f 0)
        (limitCyclesDegreeZeroLiftCone_lift_ι A k hk)
      have hπincl :
          lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
              limit.π (A ⋙ ev 0) j =
            limit.π (cyclesTower A 0) j ≫ (A.obj j).iCycles 0 := by
        simpa using (Limits.limMap_π (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) j)
      have hleft :
          m ≫ limit.π (cyclesTower A 0) j ≫ (A.obj j).iCycles 0 =
            k ≫ (limit.π A j).f 0 := by
        have hleft1 :
            m ≫ limit.π (cyclesTower A 0) j ≫ (A.obj j).iCycles 0 =
              m ≫ lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
                limit.π (A ⋙ ev 0) j := by
          simpa [Category.assoc] using congrArg (fun t ↦ m ≫ t) hπincl.symm
        have hleft2 :
            m ≫ lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
                limit.π (A ⋙ ev 0) j =
              m ≫ lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
                (limit_degree_iso A 0).inv ≫ (limit.π A j).f 0 := by
          simpa [Category.assoc] using congrArg
            (fun t ↦ m ≫ lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫ t)
            (limit_degree_iso_inv_π A 0 j).symm
        have hleft3 :
            m ≫ lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
                (limit_degree_iso A 0).inv ≫ (limit.π A j).f 0 =
              k ≫ (limit.π A j).f 0 := by
          simpa [Category.assoc] using hmj
        exact hleft1.trans (hleft2.trans hleft3)
      have hright :
          limit.lift (cyclesTower A 0) (limitCyclesDegreeZeroLiftCone A k hk) ≫
              limit.π (cyclesTower A 0) j ≫ (A.obj j).iCycles 0 =
            k ≫ (limit.π A j).f 0 := by
        have hright1 :
            limit.lift (cyclesTower A 0) (limitCyclesDegreeZeroLiftCone A k hk) ≫
                limit.π (cyclesTower A 0) j ≫ (A.obj j).iCycles 0
              =
            limit.lift (cyclesTower A 0) (limitCyclesDegreeZeroLiftCone A k hk) ≫
              lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
                limit.π (A ⋙ ev 0) j := by
          simpa [Category.assoc] using congrArg
            (fun t ↦ limit.lift (cyclesTower A 0) (limitCyclesDegreeZeroLiftCone A k hk) ≫ t)
            hπincl.symm
        have hright2 :
            limit.lift (cyclesTower A 0) (limitCyclesDegreeZeroLiftCone A k hk) ≫
                lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
                  limit.π (A ⋙ ev 0) j
              =
            limit.lift (cyclesTower A 0) (limitCyclesDegreeZeroLiftCone A k hk) ≫
              lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
                (limit_degree_iso A 0).inv ≫ (limit.π A j).f 0 := by
          simpa [Category.assoc] using congrArg
            (fun t ↦
              limit.lift (cyclesTower A 0) (limitCyclesDegreeZeroLiftCone A k hk) ≫
                lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫ t)
            (limit_degree_iso_inv_π A 0 j).symm
        have hright3 :
            limit.lift (cyclesTower A 0) (limitCyclesDegreeZeroLiftCone A k hk) ≫
                lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
                  (limit_degree_iso A 0).inv ≫ (limit.π A j).f 0
              =
            k ≫ (limit.π A j).f 0 := by
          simpa [Category.assoc] using hliftj
        exact hright1.trans (hright2.trans hright3)
      exact hleft.trans hright.symm
    )

/-- Helper for Lemma 12.31.7: the degree-`0` cocycle inclusion of `limit A` is killed by the
degree-`1` differential. -/
private theorem limit_iCycles_zero_comp_d (A : AbCpxSeq) :
    (limit A).iCycles 0 ≫ (limit A).d 0 1 = 0 := by
  simpa using (HomologicalComplex.iCycles_d (limit A) 0 1)

/-- Helper for Lemma 12.31.7: the canonical map
`(limit A).X (-1) ⟶ (CyclesF 0).obj (limit A)` dies in degree-`0` homology. -/
private theorem limit_toCycles_negOne_zero_comp_homologyπ (A : AbCpxSeq) :
    (limit A).toCycles (-1) 0 ≫ (limit A).homologyπ 0 = 0 := by
  exact HomologicalComplex.toCycles_comp_homologyπ (limit A) (-1) 0

/-- Helper for Lemma 12.31.7: the inverse limit of the degree-`0` cocycle tower is a kernel of
the differential `(limit A)^0 → (limit A)^1`. -/
noncomputable def limit_cycles_degree_zero_isKernel (A : AbCpxSeq) :
    IsLimit (limitCyclesDegreeZeroKernelFork A) :=
  limit_cycles_degree_zero_isKernel_aux A

/-- Helper for Lemma 12.31.7: inverse limit commutes with degree-`0` cocycles for a sequential
inverse system of cochain complexes. -/
noncomputable def limit_cycles_degree_zero_iso (A : AbCpxSeq) :
    limit (cyclesTower A 0) ≅ (CyclesF 0).obj (limit A) :=
  -- Proof comment: both objects represent the same kernel of `(limit A).d 0 1`.
  let hcycles :
      IsLimit
        (KernelFork.ofι ((limit A).iCycles 0)
          (limit_iCycles_zero_comp_d A)) := by
    exact (limit A).cyclesIsKernel 0 1 (by simp)
  (limit_cycles_degree_zero_isKernel A).conePointUniqueUpToIso hcycles

/-- Helper for Lemma 12.31.7: the cocycle comparison isomorphism identifies the chosen kernel map
with the actual degree-`0` cocycle inclusion of `limit A`. -/
@[reassoc]
lemma limit_cycles_degree_zero_iso_hom_comp_iCycles (A : AbCpxSeq) :
    (limit_cycles_degree_zero_iso A).hom ≫ (limit A).iCycles 0 =
      lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
        (limit_degree_iso A 0).inv := by
  -- Proof comment: this is the `ι`-comparison furnished by the universal property of the two
  -- kernel forks.
  let hcycles :
      IsLimit
        (KernelFork.ofι ((limit A).iCycles 0)
          (limit_iCycles_zero_comp_d A)) := by
    exact (limit A).cyclesIsKernel 0 1 (by simp)
  simpa [limit_cycles_degree_zero_iso, limitCyclesDegreeZeroKernelFork] using
    IsLimit.conePointUniqueUpToIso_hom_comp
      (limit_cycles_degree_zero_isKernel A)
      hcycles
      WalkingParallelPair.zero

/-- Helper for Lemma 12.31.7: the inverse of the degree-`0` cocycle comparison identifies the
canonical cocycle inclusion into `\varprojlim A_i^0`. -/
@[reassoc]
lemma limit_cycles_degree_zero_iso_inv_comp_cyclesInclusion (A : AbCpxSeq) :
    (limit_cycles_degree_zero_iso A).inv ≫
        lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) =
      (limit A).iCycles 0 ≫ (limit_degree_iso A 0).hom := by
  -- Proof comment: this is the inverse `ι`-comparison for the same pair of kernel objects.
  let hcycles :
      IsLimit
        (KernelFork.ofι ((limit A).iCycles 0)
          (limit_iCycles_zero_comp_d A)) := by
    exact (limit A).cyclesIsKernel 0 1 (by simp)
  have hcomp :=
    IsLimit.conePointUniqueUpToIso_inv_comp
      (limit_cycles_degree_zero_isKernel A)
      hcycles
      WalkingParallelPair.zero
  simpa [limit_cycles_degree_zero_iso, limitCyclesDegreeZeroKernelFork, Category.assoc] using
    congrArg (fun t ↦ t ≫ (limit_degree_iso A 0).hom) hcomp

/-- Helper for Lemma 12.31.7: the inverse of the degree-`0` cocycle comparison has the expected
stagewise projection formula. -/
lemma limit_cycles_degree_zero_iso_inv_π (A : AbCpxSeq) (j : ℕᵒᵖ) :
    (limit_cycles_degree_zero_iso A).inv ≫ limit.π (cyclesTower A 0) j =
      HomologicalComplex.cyclesMap (limit.π A j) 0 := by
  -- Proof comment: after composing with the cocycle inclusion, both sides become the degreewise
  -- projection from `limit A`.
  apply (cancel_mono ((A.obj j).iCycles 0)).1
  have hπincl :
      lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
          limit.π (A ⋙ ev 0) j =
        limit.π (cyclesTower A 0) j ≫ (A.obj j).iCycles 0 := by
    simpa using (Limits.limMap_π (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) j)
  have h1 :
      (limit_cycles_degree_zero_iso A).inv ≫ limit.π (cyclesTower A 0) j ≫ (A.obj j).iCycles 0
        =
      (limit_cycles_degree_zero_iso A).inv ≫
        lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
          limit.π (A ⋙ ev 0) j := by
    simpa [Category.assoc] using congrArg (fun t ↦ (limit_cycles_degree_zero_iso A).inv ≫ t) hπincl.symm
  have h2 :
      (limit_cycles_degree_zero_iso A).inv ≫
          lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
            limit.π (A ⋙ ev 0) j
        =
      (limit A).iCycles 0 ≫ (limit_degree_iso A 0).hom ≫ limit.π (A ⋙ ev 0) j := by
    simpa [Category.assoc] using congrArg
      (fun t ↦ t ≫ limit.π (A ⋙ ev 0) j)
      (limit_cycles_degree_zero_iso_inv_comp_cyclesInclusion A)
  have h3 :
      (limit A).iCycles 0 ≫ (limit_degree_iso A 0).hom ≫ limit.π (A ⋙ ev 0) j
        =
      (limit A).iCycles 0 ≫ (limit.π A j).f 0 := by
    simpa [Category.assoc] using congrArg
      (fun t ↦ (limit A).iCycles 0 ≫ t) (limit_degree_iso_hom_π A 0 j)
  have h4 :
      (limit A).iCycles 0 ≫ (limit.π A j).f 0 =
        HomologicalComplex.cyclesMap (limit.π A j) 0 ≫ (A.obj j).iCycles 0 := by
    simpa [Category.assoc] using
      (HomologicalComplex.cyclesMap_i (limit.π A j) 0).symm
  exact h1.trans (h2.trans (h3.trans h4))

/-- Helper for Lemma 12.31.7: the boundary map from the degree `-1` limit row factors through the
transported degree-`0` cocycle comparison. -/
private noncomputable def limitBoundaryZeroComparisonComposite (A : AbCpxSeq) :
    limit (A ⋙ ev (-1)) ⟶ (CyclesF 0).obj (limit A) :=
  -- Proof comment: first pass to the inverse limit of boundaries, then include into inverse-limit
  -- cocycles, and finally compare with the cocycles of `limit A`.
  lim.map (degreeToBoundaryNatTrans A 0) ≫
    lim.map (boundaryInclusion A 0) ≫
      (limit_cycles_degree_zero_iso A).hom

/-- Helper for Lemma 12.31.7: the boundary map from the degree `-1` limit row factors through the
transported degree-`0` cocycle comparison. -/
lemma limit_toCycles_negOne_zero_factorization_raw (A : AbCpxSeq) :
    (limit_degree_iso A (-1)).inv ≫ (limit A).toCycles (-1) 0 =
      limitBoundaryZeroComparisonComposite A := by
  -- Proof comment: compare after the cocycle inclusion of `limit A`; the composite then reduces
  -- to the transported degreewise differential identity.
  have hwhisker :
      Functor.whiskerLeft A (toCyclesNatTrans 0) ≫
          Functor.whiskerLeft A (cyclesInclusionNatTrans 0) =
        Functor.whiskerLeft A (differentialNatTrans (-1)) := by
    apply NatTrans.ext
    funext i
    simpa using NatTrans.congr_app (toCyclesNatTrans_comp_cyclesInclusionNatTrans 0) (A.obj i)
  have hmapBoundary :
      lim.map (degreeToBoundaryNatTrans A 0) ≫ lim.map (boundaryInclusion A 0) =
        lim.map (Functor.whiskerLeft A (toCyclesNatTrans 0)) := by
    rw [← Functor.map_comp]
    simpa using congrArg lim.map (degreeToBoundaryNatTrans_comp_boundaryInclusion A 0)
  have hmapWhisker :
      lim.map (Functor.whiskerLeft A (toCyclesNatTrans 0)) ≫
          lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) =
        lim.map (Functor.whiskerLeft A (differentialNatTrans (-1))) := by
    rw [← Functor.map_comp]
    simpa using congrArg lim.map hwhisker
  apply (cancel_mono ((limit A).iCycles 0)).1
  have h1 :
    (limit_degree_iso A (-1)).inv ≫ (limit A).toCycles (-1) 0 ≫ (limit A).iCycles 0
        = (limit_degree_iso A (-1)).inv ≫ (limit A).d (-1) 0 := by
    rw [HomologicalComplex.toCycles_i]
  have h2 :
      (limit_degree_iso A (-1)).inv ≫ (limit A).d (-1) 0 =
        lim.map (Functor.whiskerLeft A (differentialNatTrans (-1))) ≫
          (limit_degree_iso A 0).inv := by
    simpa using limit_degree_iso_inv_comp_differential A (-1)
  have h3 :
      lim.map (Functor.whiskerLeft A (differentialNatTrans (-1))) ≫
          (limit_degree_iso A 0).inv =
        lim.map (Functor.whiskerLeft A (toCyclesNatTrans 0)) ≫
          lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
            (limit_degree_iso A 0).inv := by
    have h' := congrArg (fun t ↦ t ≫ (limit_degree_iso A 0).inv) hmapWhisker.symm
    simpa [Category.assoc] using h'
  have h4 :
      lim.map (Functor.whiskerLeft A (toCyclesNatTrans 0)) ≫
          lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
            (limit_degree_iso A 0).inv =
        lim.map (degreeToBoundaryNatTrans A 0) ≫
          lim.map (boundaryInclusion A 0) ≫
            (limit_cycles_degree_zero_iso A).hom ≫ (limit A).iCycles 0 := by
    have h4a :
        lim.map (Functor.whiskerLeft A (toCyclesNatTrans 0)) ≫
            lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
              (limit_degree_iso A 0).inv =
          (lim.map (degreeToBoundaryNatTrans A 0) ≫ lim.map (boundaryInclusion A 0)) ≫
            lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
              (limit_degree_iso A 0).inv := by
      rw [hmapBoundary.symm]
    have h4b :
        (lim.map (degreeToBoundaryNatTrans A 0) ≫ lim.map (boundaryInclusion A 0)) ≫
            lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
              (limit_degree_iso A 0).inv =
          lim.map (degreeToBoundaryNatTrans A 0) ≫
            lim.map (boundaryInclusion A 0) ≫
              (limit_cycles_degree_zero_iso A).hom ≫ (limit A).iCycles 0 := by
      simpa [Category.assoc] using congrArg
        (fun t ↦ lim.map (degreeToBoundaryNatTrans A 0) ≫ lim.map (boundaryInclusion A 0) ≫ t)
        (limit_cycles_degree_zero_iso_hom_comp_iCycles A).symm
    exact h4a.trans h4b
  exact h1.trans (h2.trans (h3.trans h4))

/-- Helper for Lemma 12.31.7: the degree `-1` map into cocycles of the limit factors through the
inverse-limit boundary and cocycle comparison rows. -/
lemma limit_toCycles_negOne_zero_factorization
    (A : AbCpxSeq) :
    (limit_degree_iso A (-1)).inv ≫ (limit A).toCycles (-1) 0 =
      limitBoundaryZeroComparisonComposite A := by
  -- Proof comment: the raw factorization already states the desired normalization.
  exact limit_toCycles_negOne_zero_factorization_raw A

/-- Helper for Lemma 12.31.7: once the inverse-limit degree-`0` boundary row is short exact and
the inverse-limit boundary map from degree `-1` is surjective, the canonical comparison
`H^0(\varprojlim A_i) → \varprojlim H^0(A_i)` is an isomorphism. -/
theorem limit_homology_degree_zero_comparison_isIso_of_shortExact
    (A : AbCpxSeq)
    (hBoundaryZeroLimit :
      ((boundaryToCyclesToHomologyShortComplex A 0).map lim).ShortExact)
    (hCyclesNegOneBoundaryZeroLimit :
      ((cyclesToDegreeToBoundaryShortComplex A (-1)).map lim).ShortExact) :
    IsIso (limit.post A (H 0)) := by
  let π0 :
      (CyclesF 0).obj (limit A) ⟶ limit (A ⋙ H 0) :=
    (limit_cycles_degree_zero_iso A).inv ≫
      lim.map (Functor.whiskerLeft A (πH 0))
  let b0 :
      limit (boundaryTower A 0) ⟶ (CyclesF 0).obj (limit A) :=
    lim.map (boundaryInclusion A 0) ≫ (limit_cycles_degree_zero_iso A).hom
  have hBoundaryCondition :
      lim.map (boundaryInclusion A 0) ≫ lim.map (Functor.whiskerLeft A (πH 0)) = 0 := by
    -- Proof comment: the limit functor preserves the stagewise identity `B⁰ ⟶ Z⁰ ⟶ H⁰ = 0`.
    rw [← Functor.map_comp]
    rw [boundaryInclusion_comp_homologyπ_zero]
    simpa using
      (Functor.map_zero (lim : (ℕᵒᵖ ⥤ AddCommGrpCat) ⥤ AddCommGrpCat) (boundaryTower A 0)
        (A ⋙ H 0))
  obtain ⟨hBoundaryCokernel⟩ :
      Nonempty
        (IsColimit
          (CokernelCofork.ofπ
            (lim.map (Functor.whiskerLeft A (πH 0)))
            hBoundaryCondition)) := by
    -- Proof comment: short exactness of the inverse-limit degree-`0` row makes the right map a
    -- cokernel of the boundary inclusion.
    simpa [boundaryToCyclesToHomologyShortComplex] using
      ((((boundaryToCyclesToHomologyShortComplex A 0).map lim).exact_and_epi_g_iff_g_is_cokernel).1
        ⟨hBoundaryZeroLimit.exact, hBoundaryZeroLimit.epi_g⟩)
  have hb0π0 : b0 ≫ π0 = 0 := by
    -- Proof comment: after canceling the cocycle comparison isomorphism, this is exactly the
    -- inverse-limit boundary-to-homology zero relation.
    dsimp [b0, π0]
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact hBoundaryCondition
  have hBoundaryTransport :
      IsColimit (CokernelCofork.ofπ π0 hb0π0) := by
    -- Proof comment: transport the cokernel presentation from `lim Z⁰ᵢ` to `Z⁰(lim A)` using the
    -- cocycle comparison isomorphism.
    simpa [b0, π0, Category.assoc] using
      (CokernelCofork.isColimitOfIsColimitOfIff hBoundaryCokernel b0
        (limit_cycles_degree_zero_iso A).symm fun {W} φ ↦ by
          constructor
          · intro h
            simpa [b0, Category.assoc] using h
          · intro h
            simpa [b0, Category.assoc] using h)
  have hDegreeToBoundaryEpi : Epi (lim.map (degreeToBoundaryNatTrans A 0)) := by
    -- Proof comment: the inverse-limit degree-`-1` row supplies the surjectivity of the
    -- boundary map into `B⁰`.
    simpa [cyclesToDegreeToBoundaryShortComplex, degreeToBoundaryNatTransSucc,
      degreeToBoundaryNatTrans] using hCyclesNegOneBoundaryZeroLimit.epi_g
  letI : Epi (lim.map (degreeToBoundaryNatTrans A 0)) := hDegreeToBoundaryEpi
  have hBoundaryComposite :
      IsColimit
        (CokernelCofork.ofπ π0
          (by
            simpa [Category.assoc] using congrArg
              (fun t ↦ lim.map (degreeToBoundaryNatTrans A 0) ≫ t) hb0π0)) := by
    -- Proof comment: precomposing a cokernel map by an epi leaves the same cokernel object.
    let g : limit (A ⋙ ev (-1)) ⟶ limit (boundaryTower A 0) :=
      lim.map (degreeToBoundaryNatTrans A 0)
    letI : Epi g := hDegreeToBoundaryEpi
    simpa [g] using isCokernelEpiComp hBoundaryTransport g rfl
  have hBoundaryFactorization :
      lim.map (degreeToBoundaryNatTrans A 0) ≫ b0 =
        (limit_degree_iso A (-1)).inv ≫ (limit A).toCycles (-1) 0 := by
    -- Proof comment: this is the previously proved normalization of the boundary map from the
    -- degree `-1` inverse-limit row.
    simpa [b0, limitBoundaryZeroComparisonComposite, Category.assoc] using
      (limit_toCycles_negOne_zero_factorization A).symm
  have hLimitComparisonZero :
      (limit_degree_iso A (-1)).inv ≫ (limit A).toCycles (-1) 0 ≫ π0 = 0 := by
    -- Proof comment: rewrite the source map through the inverse-limit boundary row and then use
    -- the transported cokernel relation.
    have hcompZero :
        (lim.map (degreeToBoundaryNatTrans A 0) ≫ b0) ≫ π0 = 0 := by
      simpa [Category.assoc] using congrArg
        (fun t ↦ lim.map (degreeToBoundaryNatTrans A 0) ≫ t) hb0π0
    calc
      (limit_degree_iso A (-1)).inv ≫ (limit A).toCycles (-1) 0 ≫ π0 =
          lim.map (degreeToBoundaryNatTrans A 0) ≫ b0 ≫ π0 := by
            simpa [Category.assoc] using
              congrArg (fun t ↦ t ≫ π0) hBoundaryFactorization.symm
      _ = 0 := hcompZero
  have hToCyclesZero : (limit A).toCycles (-1) 0 ≫ π0 = 0 := by
    -- Proof comment: cancel the isomorphism comparing `lim A⁻¹ᵢ` with `(lim A)⁻¹`.
    have hcompZero :
        lim.map (degreeToBoundaryNatTrans A 0) ≫ b0 ≫ π0 = 0 := by
      simpa [Category.assoc] using congrArg
        (fun t ↦ lim.map (degreeToBoundaryNatTrans A 0) ≫ t) hb0π0
    apply (cancel_epi ((limit_degree_iso A (-1)).inv)).1
    calc
      (limit_degree_iso A (-1)).inv ≫ (limit A).toCycles (-1) 0 ≫ π0 =
          lim.map (degreeToBoundaryNatTrans A 0) ≫ b0 ≫ π0 := by
            simpa [Category.assoc] using
              congrArg (fun t ↦ t ≫ π0) hBoundaryFactorization.symm
      _ = 0 := hcompZero
  have hToCyclesCokernel :
      IsColimit
        (CokernelCofork.ofπ π0 hToCyclesZero) := by
    let ν : limit (A ⋙ ev (-1)) ⟶ (limit A).X (-1) := (limit_degree_iso A (-1)).inv
    letI : Epi ν := by infer_instance
    -- Proof comment: cancel the degree-`-1` comparison isomorphism from the source of the
    -- cokernel presentation.
    simpa [ν, hToCyclesZero] using
      isCokernelOfComp ν
        (lim.map (degreeToBoundaryNatTrans A 0) ≫ b0) hBoundaryComposite hToCyclesZero
        hBoundaryFactorization.symm
  have hHomologyCokernel :
      IsColimit
        (CokernelCofork.ofπ
          ((limit A).homologyπ 0)
          (limit_toCycles_negOne_zero_comp_homologyπ A)) := by
    exact (limit A).homologyIsCokernel (-1) 0 (by simp)
  let e : limit (A ⋙ H 0) ≅ (H 0).obj (limit A) :=
    hToCyclesCokernel.coconePointUniqueUpToIso hHomologyCokernel
  have hπ0_ehom : π0 ≫ e.hom = (limit A).homologyπ 0 := by
    simpa [e] using
      IsColimit.comp_coconePointUniqueUpToIso_hom hToCyclesCokernel hHomologyCokernel
        WalkingParallelPair.one
  have hHomologyπ_post : (limit A).homologyπ 0 ≫ limit.post A (H 0) = π0 := by
    -- Proof comment: stagewise, both maps are the natural homology comparison induced by the
    -- projection `limit A ⟶ Aⱼ`.
    apply limit.hom_ext
    intro j
    have h1 :
        (limit A).homologyπ 0 ≫ limit.post A (H 0) ≫ limit.π (A ⋙ H 0) j
          = (limit A).homologyπ 0 ≫ HomologicalComplex.homologyMap (limit.π A j) 0 := by
      simpa [Category.assoc] using
        congrArg (fun t ↦ (limit A).homologyπ 0 ≫ t)
          (limit.post_π A (H 0) j)
    have h2 :
        (limit A).homologyπ 0 ≫ HomologicalComplex.homologyMap (limit.π A j) 0
          = HomologicalComplex.cyclesMap (limit.π A j) 0 ≫ (A.obj j).homologyπ 0 := by
      simpa [Category.assoc] using
        (HomologicalComplex.homologyπ_naturality (limit.π A j) 0)
    have h3 :
        HomologicalComplex.cyclesMap (limit.π A j) 0 ≫ (A.obj j).homologyπ 0 =
          π0 ≫ limit.π (A ⋙ H 0) j := by
      have hlast1 :
          HomologicalComplex.cyclesMap (limit.π A j) 0 ≫ (A.obj j).homologyπ 0 =
            (limit_cycles_degree_zero_iso A).inv ≫
              limit.π (cyclesTower A 0) j ≫ (A.obj j).homologyπ 0 := by
        simpa [Category.assoc] using congrArg
          (fun t ↦ t ≫ (A.obj j).homologyπ 0)
          (limit_cycles_degree_zero_iso_inv_π A j).symm
      have hlast2 :
          π0 ≫ limit.π (A ⋙ H 0) j =
            (limit_cycles_degree_zero_iso A).inv ≫
              limit.π (cyclesTower A 0) j ≫ (A.obj j).homologyπ 0 := by
        dsimp [π0]
        simpa [Category.assoc] using congrArg
          (fun t ↦ (limit_cycles_degree_zero_iso A).inv ≫ t)
          (Limits.limMap_π (Functor.whiskerLeft A (πH 0)) j)
      exact hlast1.trans hlast2.symm
    exact h1.trans (h2.trans h3)
  have hhomologyπ_einv : (limit A).homologyπ 0 ≫ e.inv = π0 := by
    simpa [e] using
      IsColimit.comp_coconePointUniqueUpToIso_inv hToCyclesCokernel hHomologyCokernel
        WalkingParallelPair.one
  have he : limit.post A (H 0) = e.inv := by
    -- Proof comment: `homologyπ` is an epimorphism, so equality after precomposition suffices.
    apply (cancel_epi ((limit A).homologyπ 0)).1
    rw [hHomologyπ_post, hhomologyπ_einv]
  -- Proof comment: replace the canonical comparison by the hom of an explicit isomorphism.
  rw [he]
  infer_instance

/- Domain-style sampling for Lemma 12.31.7 in the inverse-limit/cohomology domain:
- owner abstractions:
  * `SequentialInverseSystem.IsMittagLeffler`
  * `IsEssentiallyConstantCofilteredDiagram`
  * `HomologicalComplex.eval`, `HomologicalComplex.homologyFunctor`, and
    `ShortComplex.ShortExact.homology_exact₂`
- sampled supporting declarations:
  * `SequentialInverseSystem.inverseLimit_shortExact_of_isMittagLeffler_left` in
    `Lemma_12_31_3`
  * `ShortComplex.ShortExact.isMittagLeffler_X₁_iff_X₂_of_essentiallyConstant_X₃` in
    `Lemma_12_31_6`
  * `ShortComplex.ShortExact.homology_exact₂` in mathlib's
    `Algebra/Homology/HomologySequence`

This item is `source-facing`: its primitive data are the inverse system `A` together with the
Mittag-Leffler hypotheses on the degree `-2` and `-1` evaluation towers and the essential
constancy hypothesis on the degree `-1` homology tower. The comparison morphism
`limit.post A (HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ) 0)` is derived from the
owner functor `HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ)`, so the public statement
should expose that canonical morphism directly rather than introduce any parallel wrapper API. -/

-- Proof sketch: form the short exact sequences of cocycles, objects, and coboundaries in degrees
-- `-1` and `0`; Lemma `12.31.3` gives exactness after taking inverse limits once the relevant
-- Mittag-Leffler conditions are known, and Lemma `12.31.6` upgrades the essential constancy of
-- `H^{-1}` to the Mittag-Leffler property for the cocycle tower. Chasing the resulting exact
-- sequences shows that the canonical map `H^0(lim A_i) ⟶ lim H^0(A_i)` is an isomorphism.
/-- Lemma 12.31.7: for a sequential inverse system of cochain complexes of abelian groups, if the
systems in degrees `-2` and `-1` are Mittag-Leffler and the degree `-1` cohomology system is
essentially constant, then the canonical comparison morphism
`H^0(\varprojlim A_i) \to \varprojlim H^0(A_i)` given by
`limit.post A (HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ) 0)` is an isomorphism. -/
@[stacks 070E]
theorem limit_homology_degree_zero_comparison_isIso
    (A : AbCpxSeq)
    (hAnegTwo : IsMittagLeffler (A ⋙ ev (-2)))
    (hAnegOne : IsMittagLeffler (A ⋙ ev (-1)))
    (hHnegOne : IsEssentiallyConstantCofilteredDiagram (A ⋙ H (-1))) :
    IsIso (limit.post A (H 0)) := by
  have hBoundaryZero : IsMittagLeffler (boundaryTower A 0) := by
    -- Proof comment: the source row `0 ⟶ Z⁻¹ ⟶ A⁻¹ ⟶ B⁰ ⟶ 0` carries Mittag-Leffler from
    -- degree `-1` to the degree-`0` boundary tower.
    simpa using boundaryTower_isMittagLeffler_of_eval A (-1) hAnegOne
  have hBoundaryNegOne : IsMittagLeffler (boundaryTower A (-1)) := by
    -- Proof comment: the same boundary-row argument in degree `-2` yields Mittag-Leffler for
    -- the degree-`-1` boundary tower.
    simpa using boundaryTower_isMittagLeffler_of_eval A (-2) hAnegTwo
  have hCyclesNegOne : IsMittagLeffler (cyclesTower A (-1)) := by
    -- Proof comment: Lemma 12.31.6 upgrades the essential constancy of `H⁻¹` to Mittag-Leffler
    -- for the cocycle tower once the boundary tower is already Mittag-Leffler.
    exact
      cyclesTower_isMittagLeffler_of_boundary_and_essentiallyConstantHomology A (-1)
        hBoundaryNegOne hHnegOne
  have hBoundaryZeroLimit :
      ((boundaryToCyclesToHomologyShortComplex A 0).map lim).ShortExact := by
    -- Proof comment: inverse limits preserve short exactness in the degree-`0` boundary row
    -- because its left term is Mittag-Leffler.
    exact
      inverseLimit_shortExact_of_isMittagLeffler_left
        (boundary_to_cycles_to_homology_shortExact A 0) hBoundaryZero
  have hCyclesNegOneBoundaryZeroLimit :
      ((cyclesToDegreeToBoundaryShortComplex A (-1)).map lim).ShortExact := by
    -- Proof comment: the same inverse-limit exactness applies to the degree-`-1` cycle row
    -- once the cocycle tower is known to be Mittag-Leffler.
    exact
      inverseLimit_shortExact_of_isMittagLeffler_left
        (cycles_to_degree_to_boundary_succ_shortExact A (-1)) hCyclesNegOne
  -- Proof comment: the packaged comparison theorem performs the final exactness chase relating
  -- `H⁰(lim A)` to `lim H⁰(Aᵢ)` from these two inverse-limit short exact rows.
  exact
    limit_homology_degree_zero_comparison_isIso_of_shortExact A
      hBoundaryZeroLimit hCyclesNegOneBoundaryZeroLimit

end SequentialInverseSystem

end CategoryTheory
