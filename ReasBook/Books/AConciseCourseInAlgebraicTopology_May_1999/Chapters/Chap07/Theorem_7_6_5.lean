import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.CategoryTheory.Quotient
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Homotopy.Equiv
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_6_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Lemma_7_6_4

open CategoryTheory
open FundamentalGroupoid
open Path.Homotopic.Quotient
open scoped ContinuousMap

noncomputable section

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
  [CompactlyGeneratedWeakHausdorffSpace E] [CompactlyGeneratedWeakHausdorffSpace B]

-- Semantic recall via `lean_leansearch`: `FundamentalGroupoid` is the canonical owner for `Π(B)`,
-- and `CategoryTheory.Quotient.functor` is the canonical passage from `TopCat` to the homotopy
-- category of spaces.

/-- Ordinary homotopy, viewed as a relation on morphisms in `TopCat`. -/
def topCatHomotopyRel : HomRel TopCat.{u} := fun _ _ f g ↦ ContinuousMap.Homotopic f.hom g.hom

/-- Ordinary homotopy is a congruence on `TopCat`. -/
instance topCatHomotopyRelCongruence : Congruence topCatHomotopyRel where
  equivalence := by
    intro X Y
    -- Expand the relation on `TopCat` morphisms and reuse the standard equivalence laws.
    refine ⟨?_, ?_, ?_⟩
    · intro f
      exact ContinuousMap.Homotopic.refl f.hom
    · intro f g hfg
      exact ContinuousMap.Homotopic.symm hfg
    · intro f g h hfg hgh
      exact ContinuousMap.Homotopic.trans hfg hgh
  comp_left := by
    intro X Y Z f g g' hg
    -- Precomposition in `TopCat` is postcomposition of continuous maps.
    simpa [topCatHomotopyRel] using
      (ContinuousMap.Homotopic.comp hg (ContinuousMap.Homotopic.refl f.hom))
  comp_right := by
    intro X Y Z f f' g hff'
    -- Postcomposition in `TopCat` is precomposition of continuous maps.
    simpa [topCatHomotopyRel] using
      (ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl g.hom) hff')

/-- The homotopy category of spaces, realized as the quotient of `TopCat` by ordinary homotopy. -/
abbrev TopCatHomotopyCategory :=
  CategoryTheory.Quotient topCatHomotopyRel

/-- The image of a space in `TopCatHomotopyCategory`. -/
abbrev topCatHomotopyCategoryObj (X : Type u) [TopologicalSpace X] : TopCatHomotopyCategory :=
  (CategoryTheory.Quotient.functor topCatHomotopyRel).obj (TopCat.of X)

/-- The homotopy class of a continuous map as a morphism in `TopCatHomotopyCategory`. -/
abbrev topCatHomotopyCategoryMap {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : topCatHomotopyCategoryObj X ⟶ topCatHomotopyCategoryObj Y :=
  (CategoryTheory.Quotient.functor topCatHomotopyRel).map (TopCat.ofHom f)

/-- A morphism in `TopCatHomotopyCategory` is exactly an ordinary homotopy class of continuous
maps. -/
def topCatHomotopyCategoryHomEquiv (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] :
    (topCatHomotopyCategoryObj X ⟶ topCatHomotopyCategoryObj Y) ≃
      continuousMapHomotopyClasses X Y := by
  change Quot
      (@CategoryTheory.HomRel.CompClosure TopCat _ topCatHomotopyRel (TopCat.of X) (TopCat.of Y)) ≃
    continuousMapHomotopyClasses X Y
  let e₁ :
      Quot
          (@CategoryTheory.HomRel.CompClosure TopCat _ topCatHomotopyRel (TopCat.of X)
            (TopCat.of Y)) ≃
        Quot (@topCatHomotopyRel (TopCat.of X) (TopCat.of Y)) :=
    Quot.congrRight (fun f g ↦
      @CategoryTheory.HomRel.compClosure_iff_self TopCat _ topCatHomotopyRel _ _ (TopCat.of X)
        (TopCat.of Y) f g)
  let e₂ : Quot (@topCatHomotopyRel (TopCat.of X) (TopCat.of Y)) ≃
      continuousMapHomotopyClasses X Y :=
    Quot.congr (TopCat.Hom.equivContinuousMap (TopCat.of X) (TopCat.of Y)) (fun _ _ ↦ Iff.rfl)
  exact e₁.trans e₂

/-- The canonical homotopy-category morphism represented by a homotopy class of continuous maps. -/
abbrev topCatHomotopyCategoryMapClass {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (τ : continuousMapHomotopyClasses X Y) :
    topCatHomotopyCategoryObj X ⟶ topCatHomotopyCategoryObj Y :=
  (topCatHomotopyCategoryHomEquiv X Y).symm τ

/-- `topCatHomotopyCategoryHomEquiv` sends the morphism represented by `f` to the homotopy class
`⟦f⟧`. -/
@[simp] theorem topCatHomotopyCategoryHomEquiv_map {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    topCatHomotopyCategoryHomEquiv X Y (topCatHomotopyCategoryMap f) =
      (⟦f⟧ : continuousMapHomotopyClasses X Y) := rfl

/-- A represented homotopy class maps to the corresponding morphism in
`TopCatHomotopyCategory`. -/
@[simp] theorem topCatHomotopyCategoryMapClass_mk {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    topCatHomotopyCategoryMapClass (⟦f⟧ : continuousMapHomotopyClasses X Y) =
      topCatHomotopyCategoryMap f := by
  apply (topCatHomotopyCategoryHomEquiv X Y).injective
  simp

/-- A concrete endpoint map representing fiber translation along a path `β : Path b b'`. -/
noncomputable def fiberTranslationMapOfPath (p : C(E, B)) [IsFibration p] {b b' : B}
    (β : Path b b') : C(fiber p b, fiber p b') :=
  Classical.choose (exists_fiberInclusionHomotopyLiftEndpoint p β)

private theorem isFiberTranslationOfPath_fiberTranslationMapOfPath (p : C(E, B)) [IsFibration p]
    {b b' : B} (β : Path b b') :
    IsFiberTranslationOfPath p β
      (⟦fiberTranslationMapOfPath p β⟧ : fiberMapHomotopyClasses p b b') := by
  rcases Classical.choose_spec (exists_fiberInclusionHomotopyLiftEndpoint p β) with ⟨G, hG⟩
  exact ⟨fiberTranslationMapOfPath p β, G, hG, rfl⟩

private theorem isFiberTranslation_fiberTranslationMapOfPath (p : C(E, B)) [IsFibration p]
    {b b' : B} (β : Path b b') :
    IsFiberTranslation p (mk β)
      (⟦fiberTranslationMapOfPath p β⟧ : fiberMapHomotopyClasses p b b') := by
  rw [isFiberTranslation_mk_iff]
  exact isFiberTranslationOfPath_fiberTranslationMapOfPath p β

/-- The explicit path-level translation map `fiberTranslationMapOfPath p β` represents the
canonical fiber-translation class along `β`. -/
theorem fiberTranslationMapOfPath_class (p : C(E, B)) [IsFibration p] {b b' : B}
    (β : Path b b') :
    (⟦fiberTranslationMapOfPath p β⟧ : fiberMapHomotopyClasses p b b') =
      fiberTranslationClass p (mk β) := by
  symm
  exact fiberTranslationClass_eq p (isFiberTranslation_fiberTranslationMapOfPath p β)

private theorem topCatHomotopyCategoryMap_fiberTranslationMapOfPath_eq_of_homotopic
    (p : C(E, B)) [IsFibration p] {b b' : B} {β₀ β₁ : Path b b'}
    (hβ : β₀.Homotopic β₁) :
    topCatHomotopyCategoryMap (fiberTranslationMapOfPath p β₀) =
      topCatHomotopyCategoryMap (fiberTranslationMapOfPath p β₁) := by
  apply (topCatHomotopyCategoryHomEquiv (fiber p b) (fiber p b')).injective
  rw [topCatHomotopyCategoryHomEquiv_map, topCatHomotopyCategoryHomEquiv_map]
  exact fiberTranslationClass_eq_of_homotopic p hβ
    (isFiberTranslation_fiberTranslationMapOfPath p β₀)
    (isFiberTranslation_fiberTranslationMapOfPath p β₁)

private noncomputable def fiberTranslationHomotopyMap (p : C(E, B)) [IsFibration p]
    {b b' : FundamentalGroupoid B} (α : b ⟶ b') :
    topCatHomotopyCategoryObj (fiber p b.as) ⟶ topCatHomotopyCategoryObj (fiber p b'.as) :=
  Quotient.liftOn α
    (fun β : Path b.as b'.as ↦ topCatHomotopyCategoryMap (fiberTranslationMapOfPath p β))
    (fun _ _ hβ ↦ topCatHomotopyCategoryMap_fiberTranslationMapOfPath_eq_of_homotopic p hβ)

/-- Helper for Theorem 7.6.5: the identity map on a fiber is a translation along the constant
path. -/
private theorem isFiberTranslationOfPath_refl_id (p : C(E, B)) [IsFibration p] {b : B} :
    IsFiberTranslationOfPath p (Path.refl b)
      (⟦ContinuousMap.id (fiber p b)⟧ : fiberMapHomotopyClasses p b b) := by
  let H :
      (fiberInclusion p b).Homotopy
        ((fiberInclusion p b).comp (ContinuousMap.id (fiber p b))) :=
    (ContinuousMap.Homotopy.refl (fiberInclusion p b)).cast rfl (by
      ext x
      rfl)
  refine ⟨ContinuousMap.id (fiber p b), H, ?_, rfl⟩
  -- The stationary lift projects to the constant base homotopy at `b`.
  ext tx
  rcases tx with ⟨t, x⟩
  simpa [H, Path.toHomotopyConst] using (mem_fiber_iff p b x.1).1 x.2

/-- Helper for Theorem 7.6.5: the canonical translation class of a constant path is represented
by the identity map on the fiber. -/
theorem fiberTranslationClass_mk_refl (p : C(E, B)) [IsFibration p] {b : B} :
    fiberTranslationClass p (mk (Path.refl b)) =
      (⟦ContinuousMap.id (fiber p b)⟧ : fiberMapHomotopyClasses p b b) := by
  -- Compare the chosen class with the explicit stationary witness.
  exact fiberTranslationClass_eq p (by
    rw [isFiberTranslation_mk_iff]
    exact isFiberTranslationOfPath_refl_id p)

/-- Helper for Theorem 7.6.5: concatenating path lifts represents composition of the corresponding
fiber-translation maps. -/
theorem fiberTranslationClass_mk_trans (p : C(E, B)) [IsFibration p] {b₀ b₁ b₂ : B}
    (β₀ : Path b₀ b₁) (β₁ : Path b₁ b₂) :
    fiberTranslationClass p (mk (β₀.trans β₁)) =
      (⟦(fiberTranslationMapOfPath p β₁).comp (fiberTranslationMapOfPath p β₀)⟧ :
        fiberMapHomotopyClasses p b₀ b₂) := by
  rcases Classical.choose_spec (exists_fiberInclusionHomotopyLiftEndpoint p β₀) with ⟨G₀, hG₀⟩
  rcases Classical.choose_spec (exists_fiberInclusionHomotopyLiftEndpoint p β₁) with ⟨G₁, hG₁⟩
  let gRaw : C(fiber p b₀, E) :=
    ((fiberInclusion p b₂).comp (fiberTranslationMapOfPath p β₁)).comp
      (fiberTranslationMapOfPath p β₀)
  let Gcomp :
      (fiberInclusion p b₀).Homotopy gRaw :=
    G₀.trans (G₁.compContinuousMap (fiberTranslationMapOfPath p β₀))
  have hgRaw :
      p.comp gRaw = ContinuousMap.const (fiber p b₀) b₂ := by
    -- The raw endpoint still lands in the fiber over `b₂`.
    ext x
    exact ((fiberTranslationMapOfPath p β₁) ((fiberTranslationMapOfPath p β₀) x)).2
  have hGcomp :
      p.comp Gcomp.toContinuousMap = (β₀.trans β₁).toHomotopyConst.toContinuousMap := by
    -- Projecting the concatenated lift recovers the concatenated base path.
    ext tx
    rcases tx with ⟨t, x⟩
    change
        p ((G₀.trans (G₁.compContinuousMap (fiberTranslationMapOfPath p β₀))) (t, x)) =
          (β₀.trans β₁) t
    rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split_ifs with ht
    · have hPoint :=
        ContinuousMap.congr_fun hG₀
          (⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, x)
      simpa [Path.toHomotopyConst] using hPoint
    · have hPoint :=
        ContinuousMap.congr_fun hG₁
          (⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩,
            fiberTranslationMapOfPath p β₀ x)
      simpa [Path.toHomotopyConst] using hPoint
  have hLift :
      (⟦fiberInclusionHomotopyLiftEndpointMap p gRaw hgRaw⟧ : fiberMapHomotopyClasses p b₀ b₂) =
        fiberTranslationClass p (mk (β₀.trans β₁)) := by
    -- The concatenated raw lift represents the canonical translation class of `β₀.trans β₁`.
    exact fiberTranslationClass_eq_of_lift p (β₀.trans β₁)
      (fiberTranslationClass p (mk (β₀.trans β₁))) gRaw hgRaw Gcomp hGcomp
      (isFiberTranslation_fiberTranslationClass p (mk (β₀.trans β₁)))
  have hEndpoint :
      fiberInclusionHomotopyLiftEndpointMap p gRaw hgRaw =
        (fiberTranslationMapOfPath p β₁).comp (fiberTranslationMapOfPath p β₀) := by
    -- The endpoint already lands in the target fiber, so repackaging does not change it.
    ext x
    rfl
  calc
    fiberTranslationClass p (mk (β₀.trans β₁)) =
        (⟦fiberInclusionHomotopyLiftEndpointMap p gRaw hgRaw⟧ :
          fiberMapHomotopyClasses p b₀ b₂) := hLift.symm
    _ = (⟦(fiberTranslationMapOfPath p β₁).comp (fiberTranslationMapOfPath p β₀)⟧ :
          fiberMapHomotopyClasses p b₀ b₂) := by
      rw [hEndpoint]

/-- Helper for Theorem 7.6.5: on a represented path class, `fiberTranslationHomotopyMap` is the
homotopy-category morphism represented by the canonical translation class. -/
@[simp] private theorem fiberTranslationHomotopyMap_fromPath (p : C(E, B)) [IsFibration p]
    {b b' : B} (β : Path b b') :
    fiberTranslationHomotopyMap p (FundamentalGroupoid.fromPath (mk β)) =
      topCatHomotopyCategoryMapClass (fiberTranslationClass p (mk β)) := by
  apply (topCatHomotopyCategoryHomEquiv (fiber p b) (fiber p b')).injective
  simp only [topCatHomotopyCategoryMapClass, Equiv.apply_symm_apply]
  change (topCatHomotopyCategoryHomEquiv (fiber p b) (fiber p b'))
      (Quotient.liftOn (mk β)
        (fun β : Path b b' ↦ topCatHomotopyCategoryMap (fiberTranslationMapOfPath p β))
        (fun β₀ β₁ hβ ↦ topCatHomotopyCategoryMap_fiberTranslationMapOfPath_eq_of_homotopic p hβ)) =
    fiberTranslationClass p (mk β)
  simpa [topCatHomotopyCategoryHomEquiv_map] using fiberTranslationMapOfPath_class p β

/-- Theorem 7.6.5: path-class lifting for a fibration `p : C(E, B)` defines a functor
`FundamentalGroupoid B ⥤ TopCatHomotopyCategory` sending `b` to the fiber `fiber p b` and a path
class to the induced homotopy class of fiber translations. -/
noncomputable def fiberTranslationHomotopyFunctor (p : C(E, B)) [IsFibration p] :
    FundamentalGroupoid B ⥤ TopCatHomotopyCategory where
  obj b := topCatHomotopyCategoryObj (fiber p b.as)
  map {b b'} α := fiberTranslationHomotopyMap p α
  map_id := by
    intro b
    -- Normalize the identity arrow to the constant-path translation class.
    rw [FundamentalGroupoid.id_eq_path_refl b]
    change fiberTranslationHomotopyMap p (FundamentalGroupoid.fromPath (mk (Path.refl b.as))) =
      𝟙 (topCatHomotopyCategoryObj (fiber p b.as))
    rw [fiberTranslationHomotopyMap_fromPath, fiberTranslationClass_mk_refl]
    simp [topCatHomotopyCategoryMap]
  map_comp := by
    intro b₀ b₁ b₂ α β
    -- Reduce to represented paths and then normalize concatenation of translation classes.
    rw [FundamentalGroupoid.comp_eq _ _ _ α β]
    refine Quotient.inductionOn₂ α β ?_
    intro γ₀ γ₁
    change
      fiberTranslationHomotopyMap p (FundamentalGroupoid.fromPath (mk (γ₀.trans γ₁))) =
        fiberTranslationHomotopyMap p (FundamentalGroupoid.fromPath (mk γ₀)) ≫
          fiberTranslationHomotopyMap p (FundamentalGroupoid.fromPath (mk γ₁))
    rw [fiberTranslationHomotopyMap_fromPath, fiberTranslationHomotopyMap_fromPath,
      fiberTranslationHomotopyMap_fromPath, fiberTranslationClass_mk_trans]
    rw [← fiberTranslationMapOfPath_class p γ₀, ← fiberTranslationMapOfPath_class p γ₁]
    simp [topCatHomotopyCategoryMap]

/-- `fiberTranslationHomotopyFunctor p` sends a point of `FundamentalGroupoid B` to the homotopy
category object represented by the fiber over that point. -/
@[simp] theorem fiberTranslationHomotopyFunctor_obj (p : C(E, B)) [IsFibration p]
    (b : FundamentalGroupoid B) :
    (fiberTranslationHomotopyFunctor p).obj b = topCatHomotopyCategoryObj (fiber p b.as) := rfl

/-- `fiberTranslationHomotopyFunctor p` sends a represented path class to the homotopy class of the
corresponding fiber-translation class. -/
@[simp] theorem fiberTranslationHomotopyFunctor_map_fromPath (p : C(E, B)) [IsFibration p]
    {b b' : B}
    (β : Path b b') :
    (fiberTranslationHomotopyFunctor p).map (FundamentalGroupoid.fromPath (mk β)) =
      topCatHomotopyCategoryMapClass (fiberTranslationClass p (mk β)) := by
  -- This is the represented-path normalization of the functor's arrow map.
  exact fiberTranslationHomotopyMap_fromPath p β

/-- A path between basepoints induces a homotopy equivalence between the corresponding fibers. -/
theorem exists_homotopyEquiv_fiberTranslationPath (p : C(E, B)) [IsFibration p] {b b' : B}
    (β : Path b b') :
    ∃ e : fiber p b ≃ₕ fiber p b', ⟦e.toFun⟧ = fiberTranslationClass p (mk β) := by
  have hLeftClass :
      (⟦(fiberTranslationMapOfPath p β.symm).comp (fiberTranslationMapOfPath p β)⟧ :
        fiberMapHomotopyClasses p b b) =
      (⟦ContinuousMap.id (fiber p b)⟧ : fiberMapHomotopyClasses p b b) := by
    -- Compare the translated loop `β.trans β.symm` with the constant path at `b`.
    have hComp :
        IsFiberTranslation p (mk (β.trans β.symm))
          (⟦(fiberTranslationMapOfPath p β.symm).comp (fiberTranslationMapOfPath p β)⟧ :
            fiberMapHomotopyClasses p b b) := by
      rw [isFiberTranslation_mk_iff]
      rw [← fiberTranslationClass_mk_trans]
      exact isFiberTranslationOfPath_fiberTranslationClass_mk p (β.trans β.symm)
    have hId :
        IsFiberTranslation p (mk (Path.refl b))
          (⟦ContinuousMap.id (fiber p b)⟧ : fiberMapHomotopyClasses p b b) := by
      rw [isFiberTranslation_mk_iff]
      exact isFiberTranslationOfPath_refl_id p
    exact fiberTranslationClass_eq_of_homotopic p (Path.Homotopic.trans_symm β) hComp hId
  have hRightClass :
      (⟦(fiberTranslationMapOfPath p β).comp (fiberTranslationMapOfPath p β.symm)⟧ :
        fiberMapHomotopyClasses p b' b') =
      (⟦ContinuousMap.id (fiber p b')⟧ : fiberMapHomotopyClasses p b' b') := by
    -- Compare the translated loop `β.symm.trans β` with the constant path at `b'`.
    have hComp :
        IsFiberTranslation p (mk (β.symm.trans β))
          (⟦(fiberTranslationMapOfPath p β).comp (fiberTranslationMapOfPath p β.symm)⟧ :
            fiberMapHomotopyClasses p b' b') := by
      rw [isFiberTranslation_mk_iff]
      rw [← fiberTranslationClass_mk_trans]
      exact isFiberTranslationOfPath_fiberTranslationClass_mk p (β.symm.trans β)
    have hId :
        IsFiberTranslation p (mk (Path.refl b'))
          (⟦ContinuousMap.id (fiber p b')⟧ : fiberMapHomotopyClasses p b' b') := by
      rw [isFiberTranslation_mk_iff]
      exact isFiberTranslationOfPath_refl_id p
    exact fiberTranslationClass_eq_of_homotopic p (Path.Homotopic.symm_trans β) hComp hId
  refine ⟨
    { toFun := fiberTranslationMapOfPath p β
      invFun := fiberTranslationMapOfPath p β.symm
      left_inv := Quotient.exact hLeftClass
      right_inv := Quotient.exact hRightClass },
    ?_⟩
  -- The chosen forward map represents the canonical translation class along `β`.
  exact fiberTranslationMapOfPath_class p β
