import Mathlib.Logic.Relation
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.UnitInterval
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.CellularPushout

open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval

universe u

/-- The generating relation collapsing the top face `E × {1}` in the unreduced cone on `E`. -/
def unreducedConeRel (E : Type u) : (E × I) → (E × I) → Prop
  | (_, s), (_, t) => s = 1 ∧ t = 1

/-- The setoid presenting the unreduced cone `CE = (E × I) / (E × {1})`. -/
def unreducedConeSetoid (E : Type u) : Setoid (E × I) :=
  Relation.EqvGen.setoid (unreducedConeRel E)

/-- The unreduced cone `CE = (E × I) / (E × {1})` viewed as a topological space. -/
abbrev unreducedCone (E : Type u) [TopologicalSpace E] : TopCat :=
  TopCat.of (Quotient (unreducedConeSetoid E))

/-- The class of `(e, t)` in the unreduced cone `CE`. -/
def unreducedConePoint {E : Type u} [TopologicalSpace E] (e : E) (t : I) : unreducedCone E :=
  Quotient.mk'' (e, t)

/-- The base point of the cone corresponding to `e ∈ E`, represented by `(e, 0)`. -/
def unreducedConeBasePoint {E : Type u} [TopologicalSpace E] (e : E) : unreducedCone E :=
  unreducedConePoint e 0

/-- Any two points of the top face `E × {1}` define the same point of the unreduced cone. -/
theorem unreducedConePoint_top_eq {E : Type u} [TopologicalSpace E] (e e' : E) :
    unreducedConePoint e 1 = unreducedConePoint e' 1 := by
  exact Quotient.sound (Relation.EqvGen.rel (e, 1) (e', 1) ⟨rfl, rfl⟩)

private theorem unreducedCone_eq_or_top_of_eqvGen
    {E : Type u} {x y : E × I}
    (h : Relation.EqvGen (unreducedConeRel E) x y) :
    x = y ∨ x.2 = 1 ∧ y.2 = 1 := by
  induction h with
  | rel x y hxy =>
      exact Or.inr hxy
  | refl x =>
      exact Or.inl rfl
  | symm x y h ih =>
      rcases ih with hEq | htop
      · exact Or.inl hEq.symm
      · exact Or.inr ⟨htop.2, htop.1⟩
  | trans x y z hxy hyz ihxy ihyz =>
      rcases ihxy with hxyEq | hxy_top
      · simpa [hxyEq] using ihyz
      rcases ihyz with hyzEq | hyz_top
      · exact Or.inr ⟨hxy_top.1, by simpa [hyzEq] using hxy_top.2⟩
      · exact Or.inr ⟨hxy_top.1, hyz_top.2⟩

private theorem unreducedConePoint_eq_iff
    {E : Type u} [TopologicalSpace E] {x y : E × I} :
    ((Quotient.mk'' x : Quotient (unreducedConeSetoid E)) = Quotient.mk'' y) ↔
      x = y ∨ x.2 = 1 ∧ y.2 = 1 := by
  constructor
  · intro hxy
    exact unreducedCone_eq_or_top_of_eqvGen (Quotient.exact hxy)
  · intro hxy
    rcases hxy with rfl | htop
    · rfl
    · rcases x with ⟨e, s⟩
      rcases y with ⟨e', t⟩
      rcases htop with ⟨hs, ht⟩
      subst hs
      subst ht
      simpa using unreducedConePoint_top_eq e e'

/-- The open subset of `E × I` away from the cone tip `E × {1}`. -/
def unreducedConeWithoutTip (E : Type u) : Set (E × I) :=
  { x | x.2 ≠ 1 }

/-- The subset `E × I \ (E × {1})` is open. -/
theorem isOpen_unreducedConeWithoutTip (E : Type u) [TopologicalSpace E] :
    IsOpen (unreducedConeWithoutTip E) := by
  have hclosed : IsClosed ({(1 : I)} : Set I) := isClosed_singleton
  have hpre :
      IsClosed ((fun x : E × I ↦ x.2) ⁻¹' ({(1 : I)} : Set I)) :=
    hclosed.preimage (continuous_snd : Continuous fun x : E × I ↦ x.2)
  have hopen :
      IsOpen (((fun x : E × I ↦ x.2) ⁻¹' ({(1 : I)} : Set I))ᶜ) :=
    hpre.isOpen_compl
  simpa [unreducedConeWithoutTip, Set.preimage, Set.compl_setOf] using hopen

/-- Away from the cone tip, the quotient map `E × I ⟶ CE` is represented by `Quotient.mk''`. -/
def unreducedConeWithoutTipPoint {E : Type u} [TopologicalSpace E] :
    unreducedConeWithoutTip E → unreducedCone E
  | ⟨x, _hx⟩ => Quotient.mk'' x

private theorem unreducedConeWithoutTipPoint_injective
    {E : Type u} [TopologicalSpace E] :
    Function.Injective
      (unreducedConeWithoutTipPoint : unreducedConeWithoutTip E → unreducedCone E) := by
  intro x y hxy
  apply Subtype.ext
  rcases unreducedConePoint_eq_iff.mp hxy with hEq | htop
  · exact hEq
  · exact False.elim (x.2 htop.1)

private theorem unreducedConeWithoutTipPoint_preimage_image
    {E : Type u} [TopologicalSpace E]
    (s : Set (unreducedConeWithoutTip E)) :
    (fun x : E × I ↦ (Quotient.mk'' x : Quotient (unreducedConeSetoid E))) ⁻¹'
        (unreducedConeWithoutTipPoint '' s) =
      Subtype.val '' s := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, hxy⟩
    rcases unreducedConePoint_eq_iff.mp hxy.symm with hEq | htop
    · exact ⟨y, hy, hEq.symm⟩
    · exact False.elim (y.2 htop.2)
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

private theorem unreducedConeWithoutTipPoint_isOpenMap
    {E : Type u} [TopologicalSpace E] :
    IsOpenMap
      (unreducedConeWithoutTipPoint : unreducedConeWithoutTip E → unreducedCone E) := by
  intro s hs
  let q : E × I → Quotient (unreducedConeSetoid E) := fun x ↦ Quotient.mk'' x
  have hq : IsQuotientMap q := by
    refine ⟨?_, ?_⟩
    · simpa [q] using
        (Quotient.mk''_surjective : Function.Surjective (Quotient.mk'' : E × I → Quotient _))
    · rfl
  have hs' : IsOpen (Subtype.val '' s) := by
    simpa [unreducedConeWithoutTip] using
      (isOpen_unreducedConeWithoutTip E).isOpenMap_subtype_val s hs
  have hpreimage :
      q ⁻¹' (unreducedConeWithoutTipPoint '' s) = Subtype.val '' s := by
    simpa [q] using unreducedConeWithoutTipPoint_preimage_image s
  refine (hq.isOpen_preimage).mp ?_
  rw [hpreimage]
  exact hs'

/-- Away from the cone tip, the quotient map `E × I ⟶ CE` is an open embedding. -/
theorem unreducedConeWithoutTipPoint_isOpenEmbedding
    {E : Type u} [TopologicalSpace E] :
    IsOpenEmbedding
      (unreducedConeWithoutTipPoint : unreducedConeWithoutTip E → unreducedCone E) := by
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_
    unreducedConeWithoutTipPoint_isOpenMap
  · simpa [unreducedConeWithoutTipPoint] using
      (continuous_quotient_mk'.comp continuous_subtype_val)
  · exact unreducedConeWithoutTipPoint_injective

private theorem unreducedConeBaseWithoutTipPoint_isEmbedding
    {E : Type u} [TopologicalSpace E] :
    IsEmbedding
      (fun e : E ↦
        (⟨(e, (0 : I)), by
          intro h
          norm_num at h⟩ : unreducedConeWithoutTip E)) := by
  let f : E → unreducedConeWithoutTip E := fun e ↦
    ⟨(e, (0 : I)), by
      intro h
      norm_num at h⟩
  refine IsEmbedding.subtypeVal.of_comp_iff.mp ?_
  change IsEmbedding ((Subtype.val : unreducedConeWithoutTip E → E × I) ∘ f)
  have hleft :
      Function.LeftInverse (fun x : E × I ↦ x.1) (fun e : E ↦ (e, (0 : I))) := fun _ ↦ rfl
  simpa using hleft.isEmbedding continuous_fst (continuous_id.prodMk continuous_const)

/-- The copy of `E` inside the unreduced cone, represented by the cone base `E × {0}`. -/
def unreducedConeBaseRange (E : Type u) [TopologicalSpace E] : Set (unreducedCone E) :=
  Set.range (unreducedConeBasePoint : E → unreducedCone E)

/-- The cone base `E × {0}` sits inside `CE` as an embedded subspace. -/
theorem unreducedConeBasePoint_isEmbedding
    {E : Type u} [TopologicalSpace E] :
    IsEmbedding (unreducedConeBasePoint : E → unreducedCone E) := by
  have hopen :
      IsOpenEmbedding
        (unreducedConeWithoutTipPoint : unreducedConeWithoutTip E → unreducedCone E) :=
    unreducedConeWithoutTipPoint_isOpenEmbedding
  simpa [unreducedConeBasePoint, unreducedConePoint, Function.comp] using
    hopen.toIsEmbedding.comp unreducedConeBaseWithoutTipPoint_isEmbedding

/-- The cone base identifies `E` with its range inside `CE`. -/
noncomputable abbrev unreducedConeBaseHomeomorph
    (E : Type u) [TopologicalSpace E] :
    E ≃ₜ unreducedConeBaseRange E :=
  unreducedConeBasePoint_isEmbedding.toHomeomorph

noncomputable section

/-- The map from the cone base `E × {0} ⊆ CE` to `B` induced by `p : E ⟶ B`. -/
def coneAdjunctionAttachMap
    {E : Type u} [TopologicalSpace E] {B : Type u} [TopologicalSpace B]
    (p : C(E, B)) :
    C(unreducedConeBaseRange E, B) :=
  ⟨fun x ↦ p ((unreducedConeBaseHomeomorph E).symm x),
    p.continuous.comp (unreducedConeBaseHomeomorph E).symm.continuous⟩

/-- On the cone-base point represented by `e`, `coneAdjunctionAttachMap p` agrees with `p`. -/
theorem coneAdjunctionAttachMap_apply_basePoint
    {E : Type u} [TopologicalSpace E] {B : Type u} [TopologicalSpace B]
    (p : C(E, B)) (e : E) :
    coneAdjunctionAttachMap p ⟨unreducedConeBasePoint e, ⟨e, rfl⟩⟩ = p e := by
  change p ((unreducedConeBaseHomeomorph E).symm ((unreducedConeBaseHomeomorph E) e)) = p e
  exact congrArg p ((unreducedConeBaseHomeomorph E).left_inv e)

/-- The adjunction space `B ∪ₚ CE` attached along `p : E ⟶ B`, now expressed through the
canonical Chapter 10 pushout owner. -/
abbrev coneAdjunctionSpace
    {E : Type u} [TopologicalSpace E] {B : Type u} [TopologicalSpace B]
    (p : C(E, B)) : TopCat :=
  cellularPushout (unreducedConeBaseRange E) (coneAdjunctionAttachMap p)

/-- The Chapter 4 cone adjunction space is the Chapter 10 pushout along the cone base. -/
theorem coneAdjunctionSpace_def
    {E : Type u} [TopologicalSpace E] {B : Type u} [TopologicalSpace B]
    (p : C(E, B)) :
    coneAdjunctionSpace p =
      cellularPushout (unreducedConeBaseRange E) (coneAdjunctionAttachMap p) :=
  rfl

/-- The point of `B ∪ₚ CE` represented by `b ∈ B`. -/
def coneAdjunctionBasePoint
    {E : Type u} [TopologicalSpace E] {B : Type u} [TopologicalSpace B]
    (p : C(E, B)) (b : B) : coneAdjunctionSpace p :=
  let f : TopCat.of (unreducedConeBaseRange E) ⟶ TopCat.of B :=
    TopCat.ofHom (coneAdjunctionAttachMap p)
  let g : TopCat.of (unreducedConeBaseRange E) ⟶ unreducedCone E :=
    TopCat.subtypeInclusion (unreducedConeBaseRange E)
  (pushout.inl f g).hom b

/-- The point of `B ∪ₚ CE` represented by `x ∈ CE`. -/
def coneAdjunctionConePoint
    {E : Type u} [TopologicalSpace E] {B : Type u} [TopologicalSpace B]
    (p : C(E, B)) (x : unreducedCone E) : coneAdjunctionSpace p :=
  let f : TopCat.of (unreducedConeBaseRange E) ⟶ TopCat.of B :=
    TopCat.ofHom (coneAdjunctionAttachMap p)
  let g : TopCat.of (unreducedConeBaseRange E) ⟶ unreducedCone E :=
    TopCat.subtypeInclusion (unreducedConeBaseRange E)
  (pushout.inr f g).hom x

/-- In `B ∪ₚ CE`, the point `p e ∈ B` is identified with the cone-base point `(e, 0) ∈ CE`. -/
theorem coneAdjunctionBasePoint_eq_conePoint
    {E : Type u} [TopologicalSpace E] {B : Type u} [TopologicalSpace B]
    (p : C(E, B)) (e : E) :
    coneAdjunctionBasePoint p (p e) =
      coneAdjunctionConePoint p (unreducedConeBasePoint e) := by
  let x : unreducedConeBaseRange E := ⟨unreducedConeBasePoint e, ⟨e, rfl⟩⟩
  let f : TopCat.of (unreducedConeBaseRange E) ⟶ TopCat.of B :=
    TopCat.ofHom (coneAdjunctionAttachMap p)
  let g : TopCat.of (unreducedConeBaseRange E) ⟶ unreducedCone E :=
    TopCat.subtypeInclusion (unreducedConeBaseRange E)
  have hx : coneAdjunctionAttachMap p x = p e := by
    simpa [x] using coneAdjunctionAttachMap_apply_basePoint p e
  have hcond : f ≫ pushout.inl f g = g ≫ pushout.inr f g := by
    simpa using (pushout.condition : f ≫ pushout.inl f g = g ≫ pushout.inr f g)
  have hmaps :
      (TopCat.Hom.hom (pushout.inl f g)) ((TopCat.Hom.hom f) x) =
        (TopCat.Hom.hom (pushout.inr f g)) ((TopCat.Hom.hom g) x) :=
    congrArg (fun h ↦ h x) (congrArg TopCat.Hom.hom hcond)
  simpa [x, coneAdjunctionBasePoint, coneAdjunctionConePoint,
    f, g, hx] using hmaps

/-- The subset `U` of `B ∪ₚ CE` coming from `B ∪ (E × [0, 3 / 4))`. -/
def coneAdjunctionSetU
    {E : Type u} [TopologicalSpace E] {B : Type u} [TopologicalSpace B]
    (p : C(E, B)) : Set (coneAdjunctionSpace p) :=
  Set.range (coneAdjunctionBasePoint p) ∪
    { x | ∃ e : E, ∃ t : I, (t : ℝ) < (3 : ℝ) / 4 ∧
        x = coneAdjunctionConePoint p (unreducedConePoint e t) }

/-- The subset `V` of `B ∪ₚ CE` coming from `E × (1 / 4, 1]`. -/
def coneAdjunctionSetV
    {E : Type u} [TopologicalSpace E] {B : Type u} [TopologicalSpace B]
    (p : C(E, B)) : Set (coneAdjunctionSpace p) :=
  { x | ∃ e : E, ∃ t : I, (1 : ℝ) / 4 < (t : ℝ) ∧
      x = coneAdjunctionConePoint p (unreducedConePoint e t) }

/-- The overlap `U ∩ V` in the standard cover of `B ∪ₚ CE`. -/
def coneAdjunctionSetUInterV
    {E : Type u} [TopologicalSpace E] {B : Type u} [TopologicalSpace B]
    (p : C(E, B)) : Set (coneAdjunctionSpace p) :=
  coneAdjunctionSetU p ∩ coneAdjunctionSetV p

/-- The canonical map `B ⟶ B ∪ₚ CE` induced by the left pushout leg. -/
def coneAdjunctionBaseMap
    {E : Type u} [TopologicalSpace E] {B : Type u} [TopologicalSpace B]
    (p : C(E, B)) : C(B, coneAdjunctionSpace p) :=
  let f : TopCat.of (unreducedConeBaseRange E) ⟶ TopCat.of B :=
    TopCat.ofHom (coneAdjunctionAttachMap p)
  let g : TopCat.of (unreducedConeBaseRange E) ⟶ unreducedCone E :=
    TopCat.subtypeInclusion (unreducedConeBaseRange E)
  (pushout.inl f g).hom

@[simp] theorem coneAdjunctionBaseMap_apply
    {E : Type u} [TopologicalSpace E] {B : Type u} [TopologicalSpace B]
    (p : C(E, B)) (b : B) :
    coneAdjunctionBaseMap p b = coneAdjunctionBasePoint p b := by
  simp [coneAdjunctionBaseMap, coneAdjunctionBasePoint]

/-- The canonical map `CE ⟶ B ∪ₚ CE` induced by the right pushout leg. -/
def coneAdjunctionConeMap
    {E : Type u} [TopologicalSpace E] {B : Type u} [TopologicalSpace B]
    (p : C(E, B)) : C(unreducedCone E, coneAdjunctionSpace p) :=
  let f : TopCat.of (unreducedConeBaseRange E) ⟶ TopCat.of B :=
    TopCat.ofHom (coneAdjunctionAttachMap p)
  let g : TopCat.of (unreducedConeBaseRange E) ⟶ unreducedCone E :=
    TopCat.subtypeInclusion (unreducedConeBaseRange E)
  (pushout.inr f g).hom

@[simp] theorem coneAdjunctionConeMap_apply
    {E : Type u} [TopologicalSpace E] {B : Type u} [TopologicalSpace B]
    (p : C(E, B)) (x : unreducedCone E) :
    coneAdjunctionConeMap p x = coneAdjunctionConePoint p x := by
  simp [coneAdjunctionConeMap, coneAdjunctionConePoint]

/-- The inclusion `B ⟶ U` of the base piece into the standard open subset `U`. -/
def coneAdjunctionSetUBaseMap
    {E : Type u} [TopologicalSpace E] {B : Type u} [TopologicalSpace B]
    (p : C(E, B)) : C(B, coneAdjunctionSetU p) where
  toFun b := ⟨coneAdjunctionBaseMap p b, Or.inl ⟨b, by simp⟩⟩
  continuous_toFun :=
    Continuous.subtype_mk (coneAdjunctionBaseMap p).continuous fun b ↦
      Or.inl ⟨b, by simp⟩

@[simp] theorem coneAdjunctionSetUBaseMap_apply
    {E : Type u} [TopologicalSpace E] {B : Type u} [TopologicalSpace B]
    (p : C(E, B)) (b : B) :
    (coneAdjunctionSetUBaseMap p b : coneAdjunctionSpace p) = coneAdjunctionBasePoint p b := by
  simp [coneAdjunctionSetUBaseMap, coneAdjunctionBaseMap_apply]

private def coneAdjunctionMidpoint : I :=
  ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩

/-- The inclusion `E ⟶ U ∩ V` obtained from the cone slice at `t = 1 / 2`. -/
def coneAdjunctionSetUInterVMidpointMap
    {E : Type u} [TopologicalSpace E] {B : Type u} [TopologicalSpace B]
    (p : C(E, B)) : C(E, coneAdjunctionSetUInterV p) where
  toFun e := by
    refine ⟨coneAdjunctionConeMap p (unreducedConePoint e coneAdjunctionMidpoint), ?_⟩
    constructor
    · refine Or.inr ?_
      refine ⟨e, coneAdjunctionMidpoint, ?_, ?_⟩
      · norm_num [coneAdjunctionMidpoint]
      · simpa using coneAdjunctionConeMap_apply p (unreducedConePoint e coneAdjunctionMidpoint)
    · refine ⟨e, coneAdjunctionMidpoint, ?_, ?_⟩
      · norm_num [coneAdjunctionMidpoint]
      · simpa using coneAdjunctionConeMap_apply p (unreducedConePoint e coneAdjunctionMidpoint)
  continuous_toFun := by
    let midpointMap : C(E, unreducedCone E) :=
      { toFun := fun e ↦ unreducedConePoint e coneAdjunctionMidpoint
        continuous_toFun := by
          simpa [unreducedConePoint] using
            (continuous_quotient_mk'.comp (continuous_id.prodMk continuous_const)) }
    exact Continuous.subtype_mk ((coneAdjunctionConeMap p).continuous.comp midpointMap.continuous)
      (fun e ↦ by
        constructor
        · refine Or.inr ?_
          refine ⟨e, coneAdjunctionMidpoint, ?_, ?_⟩
          · norm_num [coneAdjunctionMidpoint]
          · simpa using coneAdjunctionConeMap_apply p (unreducedConePoint e coneAdjunctionMidpoint)
        · refine ⟨e, coneAdjunctionMidpoint, ?_, ?_⟩
          · norm_num [coneAdjunctionMidpoint]
          · simpa using coneAdjunctionConeMap_apply p (unreducedConePoint e coneAdjunctionMidpoint))

@[simp] theorem coneAdjunctionSetUInterVMidpointMap_apply
    {E : Type u} [TopologicalSpace E] {B : Type u} [TopologicalSpace B]
    (p : C(E, B)) (e : E) :
    (coneAdjunctionSetUInterVMidpointMap p e : coneAdjunctionSpace p) =
      coneAdjunctionConePoint p (unreducedConePoint e coneAdjunctionMidpoint) := by
  change coneAdjunctionConeMap p (unreducedConePoint e coneAdjunctionMidpoint) =
    coneAdjunctionConePoint p (unreducedConePoint e coneAdjunctionMidpoint)
  simpa using coneAdjunctionConeMap_apply p (unreducedConePoint e coneAdjunctionMidpoint)
