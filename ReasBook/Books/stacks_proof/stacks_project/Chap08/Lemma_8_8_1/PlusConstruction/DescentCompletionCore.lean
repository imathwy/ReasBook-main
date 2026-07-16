import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomTotal

universe u v uX vX

namespace CategoryTheory

open Bicategory
open FibredCategoryMor
open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace FibredCategoryMor

/-- Helper for Chap08 Lemma 8 8 1, source stage 3.1: an object in the descent-object
completion over a base object `U` is a covering sieve of `U` together with descent data for the
canonical fiber pseudofunctor of `X` on that cover. -/
structure DescentCompletionObjectOver
    (X : FibredCategoryOver.{u, v, uX, vX} C) (U : C) where
  /-- The cover on which the object is locally represented. -/
  cover : J.Cover U
  /-- The descent datum attached to the cover. -/
  datum :
    (canonicalFiberPseudofunctor X.p).DescentData
      (X := fun I : cover.Arrow => I.Y)
      (fun I : cover.Arrow => I.f)

/-- Helper for Chap08 Lemma 8 8 1, source stage 3.1: the total object type of the
descent-object completion, before defining morphisms. -/
structure DescentCompletionObject
    (X : FibredCategoryOver.{u, v, uX, vX} C) where
  /-- The base object over which the descent datum lives. -/
  base : C
  /-- The cover and descent datum over `base`. -/
  object : DescentCompletionObjectOver (J := J) X base

namespace DescentCompletionObjectOver

/-- The local object `x_i` attached to a member of the cover. -/
abbrev localObject
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U : C}
    (D : DescentCompletionObjectOver (J := J) X U) (I : D.cover.Arrow) :
    X.p.Fiber I.Y :=
  D.datum.obj I

/-- The restriction of a local descent object along a further map `W ⟶ U_i`.  This is the
owner-level form of `x_i|_W` used in the source's double-indexed morphisms. -/
noncomputable abbrev restrictedLocalObject
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U : C}
    (D : DescentCompletionObjectOver (J := J) X U)
    {W : C} (I : D.cover.Arrow) (i : W ⟶ I.Y) :
    X.p.Fiber W :=
  ((canonicalFiberPseudofunctor X.p).map i.op.toLoc).toFunctor.obj (D.localObject I)

/-- Canonical comparison between first restricting a local object to `W` and then to `W'`, and
restricting directly to `W'`. -/
noncomputable def restrictedLocalObjectCompIso
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U W W' : C}
    (D : DescentCompletionObjectOver (J := J) X U)
    (I : D.cover.Arrow) (i : W ⟶ I.Y) (m : W' ⟶ W) :
    ((canonicalFiberPseudofunctor X.p).map m.op.toLoc).toFunctor.obj
        (D.restrictedLocalObject I i) ≅
      D.restrictedLocalObject I (m ≫ i) :=
  ((Cat.Hom.toNatIso
      ((canonicalFiberPseudofunctor X.p).mapComp' i.op.toLoc m.op.toLoc
        ((m ≫ i).op.toLoc) (by rfl))).app
      (D.localObject I)).symm

/-- Given an original total-category morphism `x ⟶ y` lying over `b : U ⟶ V`, restrict it to a
test object `W` mapping to both `U` and `V` compatibly with `b`.  This is the source-text local
component used for the singleton-cover embedding `G : S ⟶ S'`. -/
noncomputable def restrictedHomOfTotalHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V W : C}
    (x : X.p.Fiber U) (y : X.p.Fiber V) {b : U ⟶ V}
    (f : x.1 ⟶ y.1) [X.p.IsHomLift b f]
    (sx : W ⟶ U) (ty : W ⟶ V) (h : sx ≫ b = ty) :
    ((canonicalFiberPseudofunctor X.p).map sx.op.toLoc).toFunctor.obj x ⟶
      ((canonicalFiberPseudofunctor X.p).map ty.op.toLoc).toFunctor.obj y := by
  let hc := canonicalPullbackChoice X.p
  let ψ : (((canonicalFiberPseudofunctor X.p).map sx.op.toLoc).toFunctor.obj x).1 ⟶ y.1 :=
    hc.map sx x ≫ f
  have hψ : X.p.IsHomLift ty ψ := by
    have hcomp : X.p.IsHomLift (sx ≫ b) (hc.map sx x ≫ f) := by
      exact
        @IsHomLift.comp _ _ _ _ X.p _ _ _ _ _ _ sx b (hc.map sx x) f
          ((hc.isStronglyCartesian sx x).toIsHomLift) inferInstance
    rw [h] at hcomp
    exact hcomp
  letI : X.p.IsHomLift ty ψ := hψ
  letI : X.p.IsStronglyCartesian ty (hc.map ty y) := hc.isStronglyCartesian ty y
  let hty : ty = 𝟙 W ≫ ty := by
    simp
  let χ :=
    IsStronglyCartesian.map X.p ty (hc.map ty y) (g := 𝟙 W) (f' := ty) hty ψ
  have hχ : X.p.IsHomLift (𝟙 W) χ := by
    simpa [χ] using
      (IsStronglyCartesian.map_isHomLift X.p ty (hc.map ty y) hty ψ)
  exact ⟨χ, hχ⟩

@[reassoc]
theorem restrictedHomOfTotalHom_fac
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V W : C}
    (x : X.p.Fiber U) (y : X.p.Fiber V) {b : U ⟶ V}
    (f : x.1 ⟶ y.1) [X.p.IsHomLift b f]
    (sx : W ⟶ U) (ty : W ⟶ V) (h : sx ≫ b = ty) :
    (restrictedHomOfTotalHom x y f sx ty h).1 ≫
      (canonicalPullbackChoice X.p).map ty y =
        (canonicalPullbackChoice X.p).map sx x ≫ f := by
  let hc := canonicalPullbackChoice X.p
  let ψ : (((canonicalFiberPseudofunctor X.p).map sx.op.toLoc).toFunctor.obj x).1 ⟶ y.1 :=
    hc.map sx x ≫ f
  have hψ : X.p.IsHomLift ty ψ := by
    have hcomp : X.p.IsHomLift (sx ≫ b) (hc.map sx x ≫ f) := by
      exact
        @IsHomLift.comp _ _ _ _ X.p _ _ _ _ _ _ sx b (hc.map sx x) f
          ((hc.isStronglyCartesian sx x).toIsHomLift) inferInstance
    rw [h] at hcomp
    exact hcomp
  letI : X.p.IsHomLift ty ψ := hψ
  letI : X.p.IsStronglyCartesian ty (hc.map ty y) := hc.isStronglyCartesian ty y
  let hty : ty = 𝟙 W ≫ ty := by
    simp
  change (IsStronglyCartesian.map X.p ty (hc.map ty y) hty ψ) ≫ hc.map ty y = ψ
  exact IsStronglyCartesian.fac X.p ty (hc.map ty y) hty ψ

@[reassoc]
theorem restrictedHomOfTotalHom_pullHom_fac
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V W W' : C}
    (x : X.p.Fiber U) (y : X.p.Fiber V) {b : U ⟶ V}
    (f : x.1 ⟶ y.1) [X.p.IsHomLift b f]
    (sx : W ⟶ U) (ty : W ⟶ V) (h : sx ≫ b = ty)
    (m : W' ⟶ W) (msx : W' ⟶ U) (mty : W' ⟶ V)
    (hmsx : m ≫ sx = msx) (hmty : m ≫ ty = mty) :
    (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := canonicalFiberPseudofunctor X.p)
      (restrictedHomOfTotalHom x y f sx ty h)
      m msx mty hmsx hmty).1 ≫
      (canonicalPullbackChoice X.p).map mty y =
        (canonicalPullbackChoice X.p).map msx x ≫ f := by
  let F := canonicalFiberPseudofunctor X.p
  let hc := canonicalPullbackChoice X.p
  let r := restrictedHomOfTotalHom x y f sx ty h
  let α :=
    (F.mapComp' sx.op.toLoc m.op.toLoc msx.op.toLoc
      (by aesop)).hom.toNatTrans.app x
  let β := (F.map m.op.toLoc).toFunctor.map r
  let γ :=
    (F.mapComp' ty.op.toLoc m.op.toLoc mty.op.toLoc
      (by aesop)).inv.toNatTrans.app y
  change (α.1 ≫ β.1 ≫ γ.1) ≫ hc.map mty y = hc.map msx x ≫ f
  have hγ :
      γ.1 ≫ hc.map mty y =
        hc.map m ((F.map ty.op.toLoc).toFunctor.obj y) ≫ hc.map ty y := by
    simpa [γ, F, hc] using
      (FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_inv_app_fac
        X.p ty m mty hmty y)
  have hβ :
      β.1 ≫ hc.map m ((F.map ty.op.toLoc).toFunctor.obj y) =
        hc.map m ((F.map sx.op.toLoc).toFunctor.obj x) ≫ r.1 := by
    simpa [β, F, hc, r] using
      (FibredCategoryMor.canonical_pullbackFunctor_map_fac X.p m r)
  have hα :
      α.1 ≫ hc.map m ((F.map sx.op.toLoc).toFunctor.obj x) ≫ hc.map sx x =
        hc.map msx x := by
    simpa [α, F, hc] using
      (FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
        X.p sx m msx hmsx x)
  have hr : r.1 ≫ hc.map ty y = hc.map sx x ≫ f := by
    simpa [r, hc] using
      (restrictedHomOfTotalHom_fac x y f sx ty h)
  have hβ' :
      α.1 ≫ (β.1 ≫ hc.map m ((F.map ty.op.toLoc).toFunctor.obj y)) ≫ hc.map ty y =
        α.1 ≫ (hc.map m ((F.map sx.op.toLoc).toFunctor.obj x) ≫ r.1) ≫
          hc.map ty y :=
    congrArg (fun t => α.1 ≫ t ≫ hc.map ty y) hβ
  have hr' :
      α.1 ≫ hc.map m ((F.map sx.op.toLoc).toFunctor.obj x) ≫
          (r.1 ≫ hc.map ty y) =
        α.1 ≫ hc.map m ((F.map sx.op.toLoc).toFunctor.obj x) ≫
          (hc.map sx x ≫ f) :=
    congrArg
      (fun t => α.1 ≫ hc.map m ((F.map sx.op.toLoc).toFunctor.obj x) ≫ t) hr
  have hα' :
      (α.1 ≫ hc.map m ((F.map sx.op.toLoc).toFunctor.obj x) ≫ hc.map sx x) ≫ f =
        hc.map msx x ≫ f := by
    simpa using congrArg (fun t => t ≫ f) hα
  calc
    (α.1 ≫ β.1 ≫ γ.1) ≫ hc.map mty y
        = α.1 ≫ β.1 ≫ γ.1 ≫ hc.map mty y := by simp
    _ = α.1 ≫ β.1 ≫ (γ.1 ≫ hc.map mty y) := by simp
    _ = α.1 ≫ β.1 ≫
          (hc.map m ((F.map ty.op.toLoc).toFunctor.obj y) ≫ hc.map ty y) := by
          simpa [Category.assoc] using congrArg (fun t => α.1 ≫ β.1 ≫ t) hγ
    _ = α.1 ≫ (β.1 ≫ hc.map m ((F.map ty.op.toLoc).toFunctor.obj y)) ≫
          hc.map ty y := by
          simp [Category.assoc]
    _ = α.1 ≫ (hc.map m ((F.map sx.op.toLoc).toFunctor.obj x) ≫ r.1) ≫
          hc.map ty y := hβ'
    _ = α.1 ≫ hc.map m ((F.map sx.op.toLoc).toFunctor.obj x) ≫
          (r.1 ≫ hc.map ty y) := by
          simp [Category.assoc]
    _ = α.1 ≫ hc.map m ((F.map sx.op.toLoc).toFunctor.obj x) ≫
          (hc.map sx x ≫ f) := hr'
    _ = (α.1 ≫ hc.map m ((F.map sx.op.toLoc).toFunctor.obj x) ≫ hc.map sx x) ≫
          f := by
          simp [Category.assoc]
    _ = hc.map msx x ≫ f := hα'

/-- The transition isomorphism `φ_{ij}` on an overlap, expressed through mathlib's descent-data
isomorphism owner. -/
noncomputable def transitionIso
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U : C}
    (D : DescentCompletionObjectOver (J := J) X U)
    {W : C} (q : W ⟶ U) {I₁ I₂ : D.cover.Arrow}
    (f₁ : W ⟶ I₁.Y) (f₂ : W ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch)
    (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    ((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.obj (D.localObject I₁) ≅
      ((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.obj (D.localObject I₂) :=
  D.datum.iso q f₁ f₂ hf₁ hf₂

/-- The transition isomorphism on a common overlap, in the exact orientation used in the source
compatibility square for morphisms of descent-completion objects. -/
noncomputable def overlapIso
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U : C}
    (D : DescentCompletionObjectOver (J := J) X U)
    {W : C} {I₁ I₂ : D.cover.Arrow}
    (i₁ : W ⟶ I₁.Y) (i₂ : W ⟶ I₂.Y)
    (h : i₁ ≫ I₁.f = i₂ ≫ I₂.f) :
    D.restrictedLocalObject I₁ i₁ ≅ D.restrictedLocalObject I₂ i₂ :=
  D.transitionIso (i₁ ≫ I₁.f) i₁ i₂ rfl h.symm

/-- Helper for Chap08 Lemma 8 8 1, source stage 3.2: a morphism between descent-completion
objects over a fixed base arrow `f : U ⟶ V`.  It is the source datum `(f, a_{ij})`: for every
source cover member `U_i`, target cover member `V_j`, and every common test object mapping to
`U_i ×_V V_j`, it supplies the local morphism `a_{ij}`.  The compatibility field is the square
with the source and target descent transitions. -/
structure HomOver
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V : C}
    (D : DescentCompletionObjectOver (J := J) X U)
    (E : DescentCompletionObjectOver (J := J) X V)
    (f : U ⟶ V) where
  /-- The local component `a_{ij}` on an arbitrary object mapping to the fibre product
  `U_i ×_V V_j`. -/
  family :
    ∀ {W : C} (I : D.cover.Arrow) (K : E.cover.Arrow)
      (i : W ⟶ I.Y) (k : W ⟶ K.Y),
      i ≫ I.f ≫ f = k ≫ K.f →
        @Quiver.Hom (X.p.Fiber W) _ (D.restrictedLocalObject I i)
          (E.restrictedLocalObject K k)
  /-- Compatibility with the descent transitions on source and target overlaps.  This is the
  commutative square in source stage 3.2. -/
  compatible :
    ∀ {W : C} (I₁ I₂ : D.cover.Arrow) (K₁ K₂ : E.cover.Arrow)
      (i₁ : W ⟶ I₁.Y) (i₂ : W ⟶ I₂.Y)
      (k₁ : W ⟶ K₁.Y) (k₂ : W ⟶ K₂.Y)
      (hD : i₁ ≫ I₁.f = i₂ ≫ I₂.f)
      (hE : k₁ ≫ K₁.f = k₂ ≫ K₂.f)
      (h₁ : i₁ ≫ I₁.f ≫ f = k₁ ≫ K₁.f)
      (h₂ : i₂ ≫ I₂.f ≫ f = k₂ ≫ K₂.f),
        (D.overlapIso i₁ i₂ hD).hom ≫ family I₂ K₂ i₂ k₂ h₂ =
          family I₁ K₁ i₁ k₁ h₁ ≫ (E.overlapIso k₁ k₂ hE).hom

theorem datumHom_congr_base
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U W : C}
    (D : DescentCompletionObjectOver (J := J) X U)
    {I₁ I₂ : D.cover.Arrow}
    {q₁ q₂ : W ⟶ U} (hq : q₁ = q₂)
    (i₁ : W ⟶ I₁.Y) (i₂ : W ⟶ I₂.Y)
    (hf₁a : i₁ ≫ I₁.f = q₁) (hf₂a : i₂ ≫ I₂.f = q₁)
    (hf₁b : i₁ ≫ I₁.f = q₂) (hf₂b : i₂ ≫ I₂.f = q₂) :
    D.datum.hom q₁ i₁ i₂ hf₁a hf₂a = D.datum.hom q₂ i₁ i₂ hf₁b hf₂b := by
  cases hq
  congr

/-- The descent transition maps compose as in the source cocycle condition. -/
theorem overlapIso_hom_comp
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U W : C}
    (D : DescentCompletionObjectOver (J := J) X U)
    {I₁ I₂ I₃ : D.cover.Arrow}
    (i₁ : W ⟶ I₁.Y) (i₂ : W ⟶ I₂.Y) (i₃ : W ⟶ I₃.Y)
    (h₁₂ : i₁ ≫ I₁.f = i₂ ≫ I₂.f)
    (h₂₃ : i₂ ≫ I₂.f = i₃ ≫ I₃.f) :
    (D.overlapIso i₁ i₂ h₁₂).hom ≫ (D.overlapIso i₂ i₃ h₂₃).hom =
      (D.overlapIso i₁ i₃ (h₁₂.trans h₂₃)).hom := by
  dsimp [overlapIso, transitionIso]
  have hsecond :
      D.datum.hom (i₂ ≫ I₂.f) i₂ i₃ rfl h₂₃.symm =
        D.datum.hom (i₁ ≫ I₁.f) i₂ i₃ h₁₂.symm
          ((h₁₂.trans h₂₃).symm) := by
    exact
      datumHom_congr_base (J := J) D h₁₂.symm i₂ i₃
        rfl h₂₃.symm h₁₂.symm ((h₁₂.trans h₂₃).symm)
  rw [hsecond]
  exact
    D.datum.hom_comp (i₁ ≫ I₁.f) i₁ i₂ i₃ rfl h₁₂.symm
      ((h₁₂.trans h₂₃).symm)

/-- The transition map from a local object to itself is the identity; this is the
`φ_{ii} = id` part of the descent datum used in the source proof of composition. -/
theorem overlapIso_self_hom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U W : C}
    (D : DescentCompletionObjectOver (J := J) X U)
    (I : D.cover.Arrow) (i : W ⟶ I.Y) :
    (D.overlapIso i i rfl).hom = 𝟙 (D.restrictedLocalObject I i) := by
  simpa only [overlapIso, transitionIso, Pseudofunctor.DescentData.iso_hom] using
    (D.datum.hom_self (i ≫ I.f) i rfl)

/-- The inverse of an overlap transition is the transition in the opposite direction. -/
theorem overlapIso_inv
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U W : C}
    (D : DescentCompletionObjectOver (J := J) X U)
    {I₁ I₂ : D.cover.Arrow}
    (i₁ : W ⟶ I₁.Y) (i₂ : W ⟶ I₂.Y)
    (h : i₁ ≫ I₁.f = i₂ ≫ I₂.f) :
    (D.overlapIso i₁ i₂ h).inv =
      (D.overlapIso i₂ i₁ h.symm).hom := by
  dsimp [overlapIso, transitionIso]
  exact
    datumHom_congr_base (J := J) D h i₂ i₁ h.symm rfl rfl h

/-- Helper for Chap08 Lemma 8 8 1, source stage 3.6: the identity morphism of a
descent-completion object is given by the descent transition maps themselves. -/
noncomputable def idHomOver
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U : C}
    (D : DescentCompletionObjectOver (J := J) X U) :
    HomOver (J := J) D D (𝟙 U) where
  family I K i k h :=
    (D.overlapIso i k (by simpa [Category.assoc] using h)).hom
  compatible := by
    intro W I₁ I₂ K₁ K₂ i₁ i₂ k₁ k₂ hD hE h₁ h₂
    let h₂b : i₂ ≫ I₂.f = k₂ ≫ K₂.f := by
      simpa [Category.assoc] using h₂
    let h₁b : i₁ ≫ I₁.f = k₁ ≫ K₁.f := by
      simpa [Category.assoc] using h₁
    have hleft := overlapIso_hom_comp (J := J) D i₁ i₂ k₂ hD h₂b
    have hright := overlapIso_hom_comp (J := J) D i₁ k₁ k₂ h₁b hE
    rw [hleft, hright]

@[simp]
theorem idHomOver_family
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U W : C}
    (D : DescentCompletionObjectOver (J := J) X U)
    (I K : D.cover.Arrow) (i : W ⟶ I.Y) (k : W ⟶ K.Y)
    (h : i ≫ I.f ≫ 𝟙 U = k ≫ K.f) :
    (idHomOver (J := J) D).family I K i k h =
      (D.overlapIso i k (by simpa [Category.assoc] using h)).hom :=
  rfl

namespace HomOver

/-- The extra restriction/naturality law needed when a double-indexed morphism family is used as
a section of a Hom presheaf.  The raw source-stage datum `HomOver` records the compatible local
maps `a_ij`; this predicate records that their values on refinements are obtained by the
canonical Hom-presheaf restriction. -/
def familyNaturality'
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {f : U ⟶ V}
    (α : HomOver (J := J) D E f) : Prop :=
  ∀ {W W' : C} (I : D.cover.Arrow) (K : E.cover.Arrow)
    (i : W ⟶ I.Y) (k : W ⟶ K.Y)
    (h : i ≫ I.f ≫ f = k ≫ K.f)
    (m : W' ⟶ W) (mi : W' ⟶ I.Y) (mk : W' ⟶ K.Y)
    (hmi : m ≫ i = mi) (hmk : m ≫ k = mk),
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (α.family I K i k h) m mi mk hmi hmk =
      α.family I K mi mk
        (by
          calc
            mi ≫ I.f ≫ f = m ≫ i ≫ I.f ≫ f := by
              rw [← hmi]
              simp [Category.assoc]
            _ = m ≫ k ≫ K.f := by
              simpa [Category.assoc] using congrArg (fun q => m ≫ q) h
            _ = mk ≫ K.f := by
              simpa [Category.assoc] using congrArg (fun q => q ≫ K.f) hmk)

/-- Extensionality for owner-level descent-completion morphisms over a fixed base arrow:
it is enough to compare the source-text local component family.  The compatibility field is a
proposition and disappears by proof irrelevance once the families agree. -/
theorem ext_family
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {f : U ⟶ V}
    (α β : HomOver (J := J) D E f)
    (hfamily :
      ∀ {W : C} (I : D.cover.Arrow) (K : E.cover.Arrow)
        (i : W ⟶ I.Y) (k : W ⟶ K.Y)
        (h : i ≫ I.f ≫ f = k ≫ K.f),
          α.family I K i k h = β.family I K i k h) :
    α = β := by
  cases α with
  | mk afam acomp =>
    cases β with
    | mk bfam bcomp =>
      dsimp at hfamily
      have hfam : @afam = @bfam := by
        funext (W : C) I K i k h
        exact hfamily I K i k h
      subst hfam
      congr

set_option backward.isDefEq.respectTransparency false in
/-- The identity descent-completion morphism satisfies the restriction/naturality law. -/
theorem idHomOver_familyNaturality'
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U : C}
    (D : DescentCompletionObjectOver (J := J) X U) :
    familyNaturality' (J := J) (idHomOver (J := J) D) := by
  intro W W' I K i k h m mi mk hmi hmk
  let hbase : i ≫ I.f = k ≫ K.f := by
    simpa [Category.assoc] using h
  let hbase' : mi ≫ I.f = mk ≫ K.f := by
    calc
      mi ≫ I.f = m ≫ i ≫ I.f := by
        rw [← hmi]
        simp [Category.assoc]
      _ = m ≫ k ≫ K.f := by
        simpa [Category.assoc] using congrArg (fun q => m ≫ q) hbase
      _ = mk ≫ K.f := by
        simpa [Category.assoc] using congrArg (fun q => q ≫ K.f) hmk
  dsimp [idHomOver, overlapIso, transitionIso]
  have hpull :=
    D.datum.pullHom_hom m (i ≫ I.f) (mi ≫ I.f)
      (by
        rw [← hmi]
        simp [Category.assoc])
      i k rfl hbase.symm mi mk hmi hmk
  simpa [hbase, hbase'] using hpull

set_option backward.isDefEq.respectTransparency false in
/-- Restricting a descent transition map gives the descent transition map on the smaller base. -/
theorem overlapIso_pullHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U W W' : C}
    (D : DescentCompletionObjectOver (J := J) X U)
    (I₁ I₂ : D.cover.Arrow)
    (i₁ : W ⟶ I₁.Y) (i₂ : W ⟶ I₂.Y)
    (hD : i₁ ≫ I₁.f = i₂ ≫ I₂.f)
    (m : W' ⟶ W) (mi₁ : W' ⟶ I₁.Y) (mi₂ : W' ⟶ I₂.Y)
    (hmi₁ : m ≫ i₁ = mi₁) (hmi₂ : m ≫ i₂ = mi₂) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (D.overlapIso i₁ i₂ hD).hom m mi₁ mi₂ hmi₁ hmi₂ =
      (D.overlapIso mi₁ mi₂
        (by
          calc
            mi₁ ≫ I₁.f = m ≫ i₁ ≫ I₁.f := by
              rw [← hmi₁]
              simp [Category.assoc]
            _ = m ≫ i₂ ≫ I₂.f := by
              simpa [Category.assoc] using congrArg (fun q => m ≫ q) hD
            _ = mi₂ ≫ I₂.f := by
              simpa [Category.assoc] using congrArg (fun q => q ≫ I₂.f) hmi₂)).hom := by
  have hnat := idHomOver_familyNaturality' (J := J) D I₁ I₂ i₁ i₂
    (by simpa [Category.assoc] using hD) m mi₁ mi₂ hmi₁ hmi₂
  simpa [idHomOver_family] using hnat

set_option backward.isDefEq.respectTransparency false in
/-- Restricting a descent transition map as a functorial image, normalized by the canonical
restriction-composition comparison isomorphisms. -/
theorem overlapIso_map_eq
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U W W' : C}
    (D : DescentCompletionObjectOver (J := J) X U)
    (I₁ I₂ : D.cover.Arrow)
    (i₁ : W ⟶ I₁.Y) (i₂ : W ⟶ I₂.Y)
    (hD : i₁ ≫ I₁.f = i₂ ≫ I₂.f)
    (m : W' ⟶ W) :
    ((canonicalFiberPseudofunctor X.p).map m.op.toLoc).toFunctor.map
        (D.overlapIso i₁ i₂ hD).hom =
      (D.restrictedLocalObjectCompIso I₁ i₁ m).hom ≫
        (D.overlapIso (m ≫ i₁) (m ≫ i₂)
          (by simpa [Category.assoc] using congrArg (fun q => m ≫ q) hD)).hom ≫
          (D.restrictedLocalObjectCompIso I₂ i₂ m).inv := by
  have hpull := overlapIso_pullHom (J := J) D I₁ I₂ i₁ i₂ hD m
    (m ≫ i₁) (m ≫ i₂) rfl rfl
  dsimp [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, restrictedLocalObjectCompIso] at hpull ⊢
  rw [← hpull]
  simp [Category.assoc]

/-- Helper for Chap08 Lemma 8 8 1, source stage 3.3: on the further cover
`U_i ×_V V_j ×_W W_k`, the would-be composite is the ordinary composite
`b_{jk} ∘ a_{ij}`.  The sheaf-gluing step producing the global `c_{ik}` is a
separate obligation. -/
noncomputable def localComposite
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    {W : C} (I : D.cover.Arrow) (K : E.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (k : W ⟶ K.Y) (l : W ⟶ L.Y)
    (hα : i ≫ I.f ≫ f = k ≫ K.f)
    (hβ : k ≫ K.f ≫ g = l ≫ L.f) :
    D.restrictedLocalObject I i ⟶ H.restrictedLocalObject L l :=
  α.family I K i k hα ≫ β.family K L k l hβ

/-- Source stage 3.5 local associativity calculation: on a common refinement where all three
local factors are visible, both bracketings are the same triple composite.  The global
associativity proof later upgrades this equality by separatedness of the Hom sheaves. -/
theorem localTripleComposite_assoc
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z T W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {KObj : DescentCompletionObjectOver (J := J) X T}
    {f : U ⟶ V} {g : V ⟶ Z} {r : Z ⟶ T}
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (γ : HomOver (J := J) H KObj r)
    (I : D.cover.Arrow) (K : E.cover.Arrow) (L : H.cover.Arrow)
    (M : KObj.cover.Arrow)
    (i : W ⟶ I.Y) (k : W ⟶ K.Y) (l : W ⟶ L.Y) (m : W ⟶ M.Y)
    (hα : i ≫ I.f ≫ f = k ≫ K.f)
    (hβ : k ≫ K.f ≫ g = l ≫ L.f)
    (hγ : l ≫ L.f ≫ r = m ≫ M.f) :
    localComposite (J := J) α β I K L i k l hα hβ ≫
        γ.family L M l m hγ =
      α.family I K i k hα ≫
        localComposite (J := J) β γ K L M k l m hβ hγ := by
  simp [localComposite, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Restricting a local composite is the composite of the restricted local factors, provided the
two `HomOver` families satisfy the explicit restriction/naturality law. -/
theorem localComposite_pullHom_of_familyNaturality'
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (hαnat : familyNaturality' (J := J) α)
    (hβnat : familyNaturality' (J := J) β)
    {W W' : C} (I : D.cover.Arrow) (K : E.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (k : W ⟶ K.Y) (l : W ⟶ L.Y)
    (hα : i ≫ I.f ≫ f = k ≫ K.f)
    (hβ : k ≫ K.f ≫ g = l ≫ L.f)
    (m : W' ⟶ W) (mi : W' ⟶ I.Y) (mk : W' ⟶ K.Y) (ml : W' ⟶ L.Y)
    (hmi : m ≫ i = mi) (hmk : m ≫ k = mk) (hml : m ≫ l = ml) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (localComposite (J := J) α β I K L i k l hα hβ)
        m mi ml hmi hml =
      localComposite (J := J) α β I K L mi mk ml
        (by
          calc
            mi ≫ I.f ≫ f = m ≫ i ≫ I.f ≫ f := by
              rw [← hmi]
              simp [Category.assoc]
            _ = m ≫ k ≫ K.f := by
              simpa [Category.assoc] using congrArg (fun q => m ≫ q) hα
            _ = mk ≫ K.f := by
              simpa [Category.assoc] using congrArg (fun q => q ≫ K.f) hmk)
        (by
          calc
            mk ≫ K.f ≫ g = m ≫ k ≫ K.f ≫ g := by
              rw [← hmk]
              simp [Category.assoc]
            _ = m ≫ l ≫ L.f := by
              simpa [Category.assoc] using congrArg (fun q => m ≫ q) hβ
            _ = ml ≫ L.f := by
              simpa [Category.assoc] using congrArg (fun q => q ≫ L.f) hml) := by
  unfold localComposite
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp
    (F := canonicalFiberPseudofunctor X.p)
    (α.family I K i k hα) (β.family K L k l hβ)
    m mi mk ml hmi hmk hml]
  rw [hαnat I K i k hα m mi mk hmi hmk,
    hβnat K L k l hβ m mk ml hmk hml]

/-- Source stage 3.3 matching-family check: the local composites
`b_{jk} ∘ a_{ij}` are independent of the middle index after passing to an
overlap of two middle cover members. -/
theorem localComposite_middle_compatible
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    {W : C} (I : D.cover.Arrow) (K₁ K₂ : E.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (k₁ : W ⟶ K₁.Y) (k₂ : W ⟶ K₂.Y) (l : W ⟶ L.Y)
    (hK : k₁ ≫ K₁.f = k₂ ≫ K₂.f)
    (hα₁ : i ≫ I.f ≫ f = k₁ ≫ K₁.f)
    (hα₂ : i ≫ I.f ≫ f = k₂ ≫ K₂.f)
    (hβ₁ : k₁ ≫ K₁.f ≫ g = l ≫ L.f)
    (hβ₂ : k₂ ≫ K₂.f ≫ g = l ≫ L.f) :
    localComposite (J := J) α β I K₁ L i k₁ l hα₁ hβ₁ =
      localComposite (J := J) α β I K₂ L i k₂ l hα₂ hβ₂ := by
  unfold localComposite
  have hαcompat := α.compatible I I K₁ K₂ i i k₁ k₂ rfl hK hα₁ hα₂
  rw [overlapIso_self_hom (J := J) D I i] at hαcompat
  simp only [Category.id_comp] at hαcompat
  have hβcompat := β.compatible K₁ K₂ L L k₁ k₂ l l hK rfl hβ₁ hβ₂
  rw [overlapIso_self_hom (J := J) H L l] at hβcompat
  simp only [Category.comp_id] at hβcompat
  calc
    α.family I K₁ i k₁ hα₁ ≫ β.family K₁ L k₁ l hβ₁
        = α.family I K₁ i k₁ hα₁ ≫
            ((E.overlapIso k₁ k₂ hK).hom ≫ β.family K₂ L k₂ l hβ₂) := by
              rw [hβcompat]
    _ = (α.family I K₁ i k₁ hα₁ ≫ (E.overlapIso k₁ k₂ hK).hom) ≫
            β.family K₂ L k₂ l hβ₂ := by
              rw [Category.assoc]
    _ = α.family I K₂ i k₂ hα₂ ≫ β.family K₂ L k₂ l hβ₂ := by
              rw [← hαcompat]

/-- Source stage 3.4 local calculation: with the middle index fixed, the local composites are
compatible with the source and target descent transition maps.  This is the equality checked on
the cover `Q_j` in the source proof before separatedness/sheafness upgrades it to the global
compatibility of the glued components. -/
theorem localComposite_outer_compatible
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    {W : C} (I₁ I₂ : D.cover.Arrow) (K : E.cover.Arrow) (L₁ L₂ : H.cover.Arrow)
    (i₁ : W ⟶ I₁.Y) (i₂ : W ⟶ I₂.Y)
    (k : W ⟶ K.Y) (l₁ : W ⟶ L₁.Y) (l₂ : W ⟶ L₂.Y)
    (hD : i₁ ≫ I₁.f = i₂ ≫ I₂.f)
    (hH : l₁ ≫ L₁.f = l₂ ≫ L₂.f)
    (hα₁ : i₁ ≫ I₁.f ≫ f = k ≫ K.f)
    (hα₂ : i₂ ≫ I₂.f ≫ f = k ≫ K.f)
    (hβ₁ : k ≫ K.f ≫ g = l₁ ≫ L₁.f)
    (hβ₂ : k ≫ K.f ≫ g = l₂ ≫ L₂.f) :
    (D.overlapIso i₁ i₂ hD).hom ≫
        localComposite (J := J) α β I₂ K L₂ i₂ k l₂ hα₂ hβ₂ =
      localComposite (J := J) α β I₁ K L₁ i₁ k l₁ hα₁ hβ₁ ≫
        (H.overlapIso l₁ l₂ hH).hom := by
  unfold localComposite
  have hαcompat := α.compatible I₁ I₂ K K i₁ i₂ k k hD rfl hα₁ hα₂
  rw [overlapIso_self_hom (J := J) E K k] at hαcompat
  simp only [Category.comp_id] at hαcompat
  have hβcompat := β.compatible K K L₁ L₂ k k l₁ l₂ rfl hH hβ₁ hβ₂
  rw [overlapIso_self_hom (J := J) E K k] at hβcompat
  simp only [Category.id_comp] at hβcompat
  calc
    (D.overlapIso i₁ i₂ hD).hom ≫
        (α.family I₂ K i₂ k hα₂ ≫ β.family K L₂ k l₂ hβ₂)
        = ((D.overlapIso i₁ i₂ hD).hom ≫
            α.family I₂ K i₂ k hα₂) ≫ β.family K L₂ k l₂ hβ₂ := by
              rw [Category.assoc]
    _ = α.family I₁ K i₁ k hα₁ ≫ β.family K L₂ k l₂ hβ₂ := by
              rw [hαcompat]
    _ = α.family I₁ K i₁ k hα₁ ≫
          (β.family K L₁ k l₁ hβ₁ ≫ (H.overlapIso l₁ l₂ hH).hom) := by
              rw [hβcompat]
    _ = (α.family I₁ K i₁ k hα₁ ≫ β.family K L₁ k l₁ hβ₁) ≫
          (H.overlapIso l₁ l₂ hH).hom := by
              rw [← Category.assoc]

/-- Variant of `localComposite_outer_compatible` allowing the middle cover index to be represented
on the two sides by two arrows `K₁`, `K₂` whose maps to `V` agree over the local base.  This is the
owner-level form needed when the same source-text cover member `Q_j` is seen through two
definitionally different pullback covers. -/
theorem localComposite_outer_compatible_of_middle
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    {W : C} (I₁ I₂ : D.cover.Arrow) (K₁ K₂ : E.cover.Arrow) (L₁ L₂ : H.cover.Arrow)
    (i₁ : W ⟶ I₁.Y) (i₂ : W ⟶ I₂.Y)
    (k₁ : W ⟶ K₁.Y) (k₂ : W ⟶ K₂.Y) (l₁ : W ⟶ L₁.Y) (l₂ : W ⟶ L₂.Y)
    (hD : i₁ ≫ I₁.f = i₂ ≫ I₂.f)
    (hK : k₁ ≫ K₁.f = k₂ ≫ K₂.f)
    (hH : l₁ ≫ L₁.f = l₂ ≫ L₂.f)
    (hα₁ : i₁ ≫ I₁.f ≫ f = k₁ ≫ K₁.f)
    (hα₂ : i₂ ≫ I₂.f ≫ f = k₂ ≫ K₂.f)
    (hβ₁ : k₁ ≫ K₁.f ≫ g = l₁ ≫ L₁.f)
    (hβ₂ : k₂ ≫ K₂.f ≫ g = l₂ ≫ L₂.f) :
    (D.overlapIso i₁ i₂ hD).hom ≫
        localComposite (J := J) α β I₂ K₂ L₂ i₂ k₂ l₂ hα₂ hβ₂ =
      localComposite (J := J) α β I₁ K₁ L₁ i₁ k₁ l₁ hα₁ hβ₁ ≫
        (H.overlapIso l₁ l₂ hH).hom := by
  unfold localComposite
  have hαcompat := α.compatible I₁ I₂ K₁ K₂ i₁ i₂ k₁ k₂ hD hK hα₁ hα₂
  have hβcompat := β.compatible K₁ K₂ L₁ L₂ k₁ k₂ l₁ l₂ hK hH hβ₁ hβ₂
  calc
    (D.overlapIso i₁ i₂ hD).hom ≫
        (α.family I₂ K₂ i₂ k₂ hα₂ ≫ β.family K₂ L₂ k₂ l₂ hβ₂)
        = ((D.overlapIso i₁ i₂ hD).hom ≫
            α.family I₂ K₂ i₂ k₂ hα₂) ≫ β.family K₂ L₂ k₂ l₂ hβ₂ := by
              rw [Category.assoc]
    _ = (α.family I₁ K₁ i₁ k₁ hα₁ ≫ (E.overlapIso k₁ k₂ hK).hom) ≫
          β.family K₂ L₂ k₂ l₂ hβ₂ := by
              rw [hαcompat]
    _ = α.family I₁ K₁ i₁ k₁ hα₁ ≫
          ((E.overlapIso k₁ k₂ hK).hom ≫ β.family K₂ L₂ k₂ l₂ hβ₂) := by
              rw [Category.assoc]
    _ = α.family I₁ K₁ i₁ k₁ hα₁ ≫
          (β.family K₁ L₁ k₁ l₁ hβ₁ ≫ (H.overlapIso l₁ l₂ hH).hom) := by
              rw [hβcompat]
    _ = (α.family I₁ K₁ i₁ k₁ hα₁ ≫ β.family K₁ L₁ k₁ l₁ hβ₁) ≫
          (H.overlapIso l₁ l₂ hH).hom := by
              rw [← Category.assoc]

/-- Helper for Chap08 Lemma 8 8 1, source stage 3.3: after fixing a source
cover arrow `I`, a target cover arrow `L`, and a test object mapping to the
formal fibre product `U_i ×_Z Z_l`, the middle cover is the pullback of the
middle descent cover along `W ⟶ U ⟶ V`.  This is the cover denoted
`P_{ijk} → P_{ik}` in the source-faithful draft. -/
noncomputable def compositionMiddleCover
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (I : D.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (_h : i ≫ I.f ≫ f ≫ g = l ≫ L.f) :
    J.Cover W :=
  E.cover.pullback (i ≫ I.f ≫ f)

/-- Helper for Chap08 Lemma 8 8 1, source stage 3.3: on one member of the
middle cover, the local piece of the composite is exactly
`d_ijk = b_jk ∘ a_ij`. -/
noncomputable def compositionMiddleCoverComposite
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (I : D.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ f ≫ g = l ≫ L.f)
    (Kp : (compositionMiddleCover (J := J)
      (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h).Arrow) :
    D.restrictedLocalObject I (Kp.f ≫ i) ⟶
      H.restrictedLocalObject L (Kp.f ≫ l) :=
  localComposite (J := J) α β I Kp.base L
    (Kp.f ≫ i) (𝟙 Kp.Y) (Kp.f ≫ l)
    (by simp [compositionMiddleCover, Category.assoc])
    (by
      simpa [compositionMiddleCover, Category.assoc] using
        congrArg (fun q => Kp.f ≫ q) h)

set_option backward.isDefEq.respectTransparency false in
/-- Source stage 3.3 comparison on the source side: restricting
`x_i|_{P_ik}` along a middle-cover arrow is canonically identified with
`x_i|_{P_ijk}`. -/
noncomputable def compositionMiddleCoverSourceIso
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (I : D.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ f ≫ g = l ≫ L.f)
    (Kp : (compositionMiddleCover (J := J)
      (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h).Arrow) :
    ((canonicalFiberPseudofunctor X.p).map Kp.f.op.toLoc).toFunctor.obj
        (D.restrictedLocalObject I i) ≅
      D.restrictedLocalObject I (Kp.f ≫ i) :=
  ((Cat.Hom.toNatIso
      ((canonicalFiberPseudofunctor X.p).mapComp' i.op.toLoc Kp.f.op.toLoc
        ((Kp.f ≫ i).op.toLoc) (by rfl))).app
      (D.localObject I)).symm

set_option backward.isDefEq.respectTransparency false in
/-- Source stage 3.3 comparison on the target side: restricting
`z_l|_{P_ik}` along a middle-cover arrow is canonically identified with
`z_l|_{P_ijk}`. -/
noncomputable def compositionMiddleCoverTargetIso
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (I : D.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ f ≫ g = l ≫ L.f)
    (Kp : (compositionMiddleCover (J := J)
      (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h).Arrow) :
    ((canonicalFiberPseudofunctor X.p).map Kp.f.op.toLoc).toFunctor.obj
        (H.restrictedLocalObject L l) ≅
      H.restrictedLocalObject L (Kp.f ≫ l) :=
  ((Cat.Hom.toNatIso
      ((canonicalFiberPseudofunctor X.p).mapComp' l.op.toLoc Kp.f.op.toLoc
        ((Kp.f ≫ l).op.toLoc) (by rfl))).app
      (H.localObject L)).symm

set_option backward.isDefEq.respectTransparency false in
/-- Restricting the source comparison isomorphism from a middle-cover member to a further slice
object gives the standard source comparison over the further base object. -/
theorem sourceIso_pullHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (I : D.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ f ≫ g = l ≫ L.f)
    (Kp : (compositionMiddleCover (J := J)
      (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h).Arrow)
    {A : Over W} (a : A ⟶ Over.mk Kp.f) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (compositionMiddleCoverSourceIso (J := J)
          (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h Kp).hom
        a.left A.hom (A.hom ≫ i)
        (by simpa using a.w)
        (by simpa [Category.assoc] using congrArg (fun q => q ≫ i) a.w) =
      ((Cat.Hom.toNatIso
        ((canonicalFiberPseudofunctor X.p).mapComp' i.op.toLoc A.hom.op.toLoc
          ((A.hom ≫ i).op.toLoc) (by rfl))).app
        (D.localObject I)).symm.hom := by
  simpa [compositionMiddleCoverSourceIso, Category.assoc] using
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom_mapComp'_inv_of_fac
      (F := canonicalFiberPseudofunctor X.p)
      i Kp.f a.left A.hom (by simpa using a.w) (D.localObject I)

set_option backward.isDefEq.respectTransparency false in
/-- Restricting the inverse target comparison from a middle-cover member to a further slice
object gives the standard inverse target comparison over the further base object. -/
theorem targetIso_inv_pullHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (I : D.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ f ≫ g = l ≫ L.f)
    (Kp : (compositionMiddleCover (J := J)
      (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h).Arrow)
    {A : Over W} (a : A ⟶ Over.mk Kp.f) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (compositionMiddleCoverTargetIso (J := J)
          (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h Kp).inv
        a.left (A.hom ≫ l) A.hom
        (by simpa [Category.assoc] using congrArg (fun q => q ≫ l) a.w)
        (by simpa using a.w) =
      ((Cat.Hom.toNatIso
        ((canonicalFiberPseudofunctor X.p).mapComp' l.op.toLoc A.hom.op.toLoc
          ((A.hom ≫ l).op.toLoc) (by rfl))).app
        (H.localObject L)).hom := by
  simpa [compositionMiddleCoverTargetIso, Category.assoc] using
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom_mapComp'_hom_of_fac
      (F := canonicalFiberPseudofunctor X.p)
      l Kp.f a.left A.hom (by simpa using a.w) (H.localObject L)

set_option backward.isDefEq.respectTransparency false in
/-- Source stage 3.3: the local composite `d_ijk` as an actual section of the
Hom presheaf on the slice object `P_ijk → P_ik`.  This is the form needed for
the next sheaf-amalgamation step producing `c_ik`. -/
noncomputable def compositionMiddleCoverSection
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (I : D.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ f ≫ g = l ≫ L.f)
    (Kp : (compositionMiddleCover (J := J)
      (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h).Arrow) :
    ((canonicalFiberPseudofunctor X.p).presheafHom
      (D.restrictedLocalObject I i) (H.restrictedLocalObject L l)).obj
        (op (Over.mk Kp.f)) :=
  (compositionMiddleCoverSourceIso (J := J)
      (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h Kp).hom ≫
    compositionMiddleCoverComposite (J := J) α β I L i l h Kp ≫
      (compositionMiddleCoverTargetIso (J := J)
        (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h Kp).inv

set_option backward.isDefEq.respectTransparency false in
/-- Normal form for restricting the section `d_ijk` to a further slice object.  It is the
source comparison over the smaller base, followed by the restricted local composite, followed by
the target comparison over the smaller base. -/
theorem compositionMiddleCoverSection_map_eq_of_familyNaturality
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (hαnat : familyNaturality' (J := J) α)
    (hβnat : familyNaturality' (J := J) β)
    (I : D.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ f ≫ g = l ≫ L.f)
    (Kp : (compositionMiddleCover (J := J)
      (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h).Arrow)
    {A : Over W} (a : A ⟶ Over.mk Kp.f) :
    ((canonicalFiberPseudofunctor X.p).presheafHom
      (D.restrictedLocalObject I i) (H.restrictedLocalObject L l)).map a.op
        (compositionMiddleCoverSection (J := J) α β I L i l h Kp) =
      ((Cat.Hom.toNatIso
        ((canonicalFiberPseudofunctor X.p).mapComp' i.op.toLoc A.hom.op.toLoc
          ((A.hom ≫ i).op.toLoc) (by rfl))).app
        (D.localObject I)).symm.hom ≫
        localComposite (J := J) α β I Kp.base L
          (A.hom ≫ i) a.left (A.hom ≫ l)
          (by
            have ha : a.left ≫ Kp.f = A.hom := by
              simpa using (Over.w a)
            calc
              (A.hom ≫ i) ≫ I.f ≫ f
                  = a.left ≫ Kp.f ≫ i ≫ I.f ≫ f := by
                    rw [← ha]
                    simp [Category.assoc]
              _ = a.left ≫ Kp.base.f := by
                    simp [compositionMiddleCover])
          (by
            have ha : a.left ≫ Kp.f = A.hom := by
              simpa using (Over.w a)
            calc
              a.left ≫ Kp.base.f ≫ g
                  = A.hom ≫ i ≫ I.f ≫ f ≫ g := by
                    rw [← ha]
                    simp [compositionMiddleCover, Category.assoc]
              _ = (A.hom ≫ l) ≫ L.f := by
                    simpa [Category.assoc] using congrArg (fun q => A.hom ≫ q) h) ≫
          ((Cat.Hom.toNatIso
            ((canonicalFiberPseudofunctor X.p).mapComp' l.op.toLoc A.hom.op.toLoc
              ((A.hom ≫ l).op.toLoc) (by rfl))).app
            (H.localObject L)).hom := by
  rw [Pseudofunctor.presheafHom_map]
  dsimp [compositionMiddleCoverSection, compositionMiddleCoverComposite]
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp₃
    (F := canonicalFiberPseudofunctor X.p)
    (compositionMiddleCoverSourceIso (J := J)
      (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h Kp).hom
    (localComposite (J := J) α β I Kp.base L
      (Kp.f ≫ i) (𝟙 Kp.Y) (Kp.f ≫ l)
      (by simp [compositionMiddleCover, Category.assoc])
      (by
        simpa [compositionMiddleCover, Category.assoc] using
          congrArg (fun q => Kp.f ≫ q) h))
    (compositionMiddleCoverTargetIso (J := J)
      (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h Kp).inv
    a.left A.hom (A.hom ≫ i) (A.hom ≫ l) A.hom
    (by simpa using a.w)
    (by simpa [Category.assoc] using congrArg (fun q => q ≫ i) a.w)
    (by simpa [Category.assoc] using congrArg (fun q => q ≫ l) a.w)
    (by simpa using a.w)]
  rw [sourceIso_pullHom (J := J)
    (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h Kp a]
  rw [targetIso_inv_pullHom (J := J)
    (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h Kp a]
  rw [localComposite_pullHom_of_familyNaturality' (J := J)
    α β hαnat hβnat I Kp.base L
    (Kp.f ≫ i) (𝟙 Kp.Y) (Kp.f ≫ l)
    (by simp [compositionMiddleCover, Category.assoc])
    (by
      simpa [compositionMiddleCover, Category.assoc] using
        congrArg (fun q => Kp.f ≫ q) h)
    a.left (A.hom ≫ i) a.left (A.hom ≫ l)
    (by simpa [Category.assoc] using congrArg (fun q => q ≫ i) a.w)
    (by simp)
    (by simpa [Category.assoc] using congrArg (fun q => q ≫ l) a.w)]
  simp

/-- The middle cover, viewed as the corresponding covering family of the identity object in
the slice site over `P_ik`. -/
theorem compositionMiddleCover_overFamily_covering
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (I : D.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ f ≫ g = l ≫ L.f) :
    Sieve.ofArrows
      (fun Kp : (compositionMiddleCover (J := J)
        (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h).Arrow =>
          Over.mk Kp.f)
      (fun Kp => (Over.homMk Kp.f : Over.mk Kp.f ⟶ Over.mk (𝟙 W))) ∈
      (J.over W) (Over.mk (𝟙 W)) := by
  let S := compositionMiddleCover (J := J)
    (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h
  rw [GrothendieckTopology.mem_over_iff]
  have hEq :
      Sieve.overEquiv (Over.mk (𝟙 W))
        (Sieve.ofArrows
          (fun Kp : S.Arrow => Over.mk Kp.f)
          (fun Kp => (Over.homMk Kp.f : Over.mk Kp.f ⟶ Over.mk (𝟙 W)))) =
        Sieve.ofArrows (fun Kp : S.Arrow => Kp.Y) (fun Kp => Kp.f) := by
    ext A q
    rw [Sieve.overEquiv_iff, Sieve.mem_ofArrows_iff, Sieve.mem_ofArrows_iff]
    constructor
    · rintro ⟨Kp, a, hfac⟩
      refine ⟨Kp, a.left, ?_⟩
      exact congrArg (fun k => k.left) hfac
    · rintro ⟨Kp, a, hfac⟩
      refine ⟨Kp, Over.homMk a ?_, ?_⟩
      · simp [hfac]
      · ext
        exact hfac
  rw [hEq]
  rw [GrothendieckTopology.Cover.ofArrows_eq S]
  exact S.condition

/-- Source stage 3.3 sheaf-gluing obligation for the middle-cover sections:
the sections `d_ijk` agree after restriction to any common refinement in the
slice over `P_ik`.  This is the exact hypothesis needed by
`Presheaf.IsSheaf.amalgamateOfArrows`; the preceding
`compositionMiddleCover_relation_compatible` is its fiber-level core. -/
def compositionMiddleCoverSectionCompatible
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (I : D.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ f ≫ g = l ≫ L.f) : Prop :=
  let S := compositionMiddleCover (J := J)
    (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h
  let P := (canonicalFiberPseudofunctor X.p).presheafHom
    (D.restrictedLocalObject I i) (H.restrictedLocalObject L l)
  ∀ ⦃A : Over W⦄ ⦃K₁ K₂ : S.Arrow⦄
    (a : A ⟶ Over.mk K₁.f) (b : A ⟶ Over.mk K₂.f),
      a ≫ (Over.homMk K₁.f : Over.mk K₁.f ⟶ Over.mk (𝟙 W)) =
        b ≫ (Over.homMk K₂.f : Over.mk K₂.f ⟶ Over.mk (𝟙 W)) →
        P.map a.op (compositionMiddleCoverSection (J := J) α β I L i l h K₁) =
          P.map b.op (compositionMiddleCoverSection (J := J) α β I L i l h K₂)

set_option backward.isDefEq.respectTransparency false in
/-- The source stage 3.3 matching condition for the sheaf-gluing step follows from the
restriction/naturality laws for the two input `HomOver` families. -/
theorem compositionMiddleCoverSectionCompatible_of_familyNaturality
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (hαnat : familyNaturality' (J := J) α)
    (hβnat : familyNaturality' (J := J) β)
    (I : D.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ f ≫ g = l ≫ L.f) :
    compositionMiddleCoverSectionCompatible (J := J) α β I L i l h := by
  intro A K₁ K₂ a b hab
  have ha : a.left ≫ K₁.f = A.hom := by
    simpa using (Over.w a)
  have hb : b.left ≫ K₂.f = A.hom := by
    simpa using (Over.w b)
  have hbase : a.left ≫ K₁.f = b.left ≫ K₂.f := ha.trans hb.symm
  have hK : a.left ≫ K₁.base.f = b.left ≫ K₂.base.f := by
    simpa [compositionMiddleCover, Category.assoc] using
      congrArg (fun q => q ≫ i ≫ I.f ≫ f) hbase
  have hα₁ : (A.hom ≫ i) ≫ I.f ≫ f = a.left ≫ K₁.base.f := by
    calc
      (A.hom ≫ i) ≫ I.f ≫ f
          = a.left ≫ K₁.f ≫ i ≫ I.f ≫ f := by
            rw [← ha]
            simp [Category.assoc]
      _ = a.left ≫ K₁.base.f := by
            simp [compositionMiddleCover]
  have hα₂ : (A.hom ≫ i) ≫ I.f ≫ f = b.left ≫ K₂.base.f := by
    calc
      (A.hom ≫ i) ≫ I.f ≫ f
          = b.left ≫ K₂.f ≫ i ≫ I.f ≫ f := by
            rw [← hb]
            simp [Category.assoc]
      _ = b.left ≫ K₂.base.f := by
            simp [compositionMiddleCover]
  have hβ₁ : a.left ≫ K₁.base.f ≫ g = (A.hom ≫ l) ≫ L.f := by
    calc
      a.left ≫ K₁.base.f ≫ g
          = A.hom ≫ i ≫ I.f ≫ f ≫ g := by
            rw [← ha]
            simp [compositionMiddleCover, Category.assoc]
      _ = (A.hom ≫ l) ≫ L.f := by
            simpa [Category.assoc] using congrArg (fun q => A.hom ≫ q) h
  have hβ₂ : b.left ≫ K₂.base.f ≫ g = (A.hom ≫ l) ≫ L.f := by
    calc
      b.left ≫ K₂.base.f ≫ g
          = A.hom ≫ i ≫ I.f ≫ f ≫ g := by
            rw [← hb]
            simp [compositionMiddleCover, Category.assoc]
      _ = (A.hom ≫ l) ≫ L.f := by
            simpa [Category.assoc] using congrArg (fun q => A.hom ≫ q) h
  have hmid :
      localComposite (J := J) α β I K₁.base L
          (A.hom ≫ i) a.left (A.hom ≫ l) hα₁ hβ₁ =
        localComposite (J := J) α β I K₂.base L
          (A.hom ≫ i) b.left (A.hom ≫ l) hα₂ hβ₂ :=
    localComposite_middle_compatible (J := J) α β I K₁.base K₂.base L
      (A.hom ≫ i) a.left b.left (A.hom ≫ l) hK hα₁ hα₂ hβ₁ hβ₂
  rw [compositionMiddleCoverSection_map_eq_of_familyNaturality
      (J := J) α β hαnat hβnat I L i l h K₁ a,
    compositionMiddleCoverSection_map_eq_of_familyNaturality
      (J := J) α β hαnat hβnat I L i l h K₂ b]
  simpa [Category.assoc] using
    congrArg
      (fun q =>
        ((Cat.Hom.toNatIso
          ((canonicalFiberPseudofunctor X.p).mapComp' i.op.toLoc A.hom.op.toLoc
            ((A.hom ≫ i).op.toLoc) (by rfl))).app
          (D.localObject I)).symm.hom ≫ q ≫
          ((Cat.Hom.toNatIso
            ((canonicalFiberPseudofunctor X.p).mapComp' l.op.toLoc A.hom.op.toLoc
              ((A.hom ≫ l).op.toLoc) (by rfl))).app
            (H.localObject L)).hom)
      hmid

set_option backward.isDefEq.respectTransparency false in
/-- Source stage 3.3: assuming the Hom presheaf is a sheaf and the local
sections `d_ijk` are compatible, glue them to the desired section over
`P_ik`.  Under `presheafHomObjHomEquiv.symm`, this is the component `c_ik`
of the composite morphism. -/
noncomputable def compositionGluedSectionOfCompatible
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (I : D.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ f ≫ g = l ≫ L.f)
    (hSheaf : Presheaf.IsSheaf (J.over W)
      ((canonicalFiberPseudofunctor X.p).presheafHom
        (D.restrictedLocalObject I i) (H.restrictedLocalObject L l)))
    (hmatch : compositionMiddleCoverSectionCompatible (J := J) α β I L i l h) :
    ((canonicalFiberPseudofunctor X.p).presheafHom
      (D.restrictedLocalObject I i) (H.restrictedLocalObject L l)).obj
        (op (Over.mk (𝟙 W))) :=
  let S := compositionMiddleCover (J := J)
    (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h
  (hSheaf.amalgamateOfArrows
    (f := fun Kp : S.Arrow =>
      (Over.homMk Kp.f : Over.mk Kp.f ⟶ Over.mk (𝟙 W)))
    (hf := compositionMiddleCover_overFamily_covering (J := J) I L i l h)
    (x := fun Kp (_ : PUnit) =>
      compositionMiddleCoverSection (J := J) α β I L i l h Kp)
    (hx := by
      intro A K₁ K₂ a b hab
      funext _
      exact hmatch a b hab)) PUnit.unit

set_option backward.isDefEq.respectTransparency false in
/-- The glued section restricts to the prescribed local section on every member of the middle
cover. -/
theorem compositionGluedSectionOfCompatible_map
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (I : D.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ f ≫ g = l ≫ L.f)
    (hSheaf : Presheaf.IsSheaf (J.over W)
      ((canonicalFiberPseudofunctor X.p).presheafHom
        (D.restrictedLocalObject I i) (H.restrictedLocalObject L l)))
    (hmatch : compositionMiddleCoverSectionCompatible (J := J) α β I L i l h)
    (Kp : (compositionMiddleCover (J := J)
      (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h).Arrow) :
    ((canonicalFiberPseudofunctor X.p).presheafHom
      (D.restrictedLocalObject I i) (H.restrictedLocalObject L l)).map
        (Over.homMk Kp.f : Over.mk Kp.f ⟶ Over.mk (𝟙 W)).op
        (compositionGluedSectionOfCompatible (J := J) α β I L i l h hSheaf hmatch) =
      compositionMiddleCoverSection (J := J) α β I L i l h Kp := by
  let S := compositionMiddleCover (J := J)
    (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h
  let P := (canonicalFiberPseudofunctor X.p).presheafHom
    (D.restrictedLocalObject I i) (H.restrictedLocalObject L l)
  let hx :
      ∀ ⦃A : Over W⦄ ⦃K₁ K₂ : S.Arrow⦄
        (a : A ⟶ Over.mk K₁.f) (b : A ⟶ Over.mk K₂.f),
          a ≫ (Over.homMk K₁.f : Over.mk K₁.f ⟶ Over.mk (𝟙 W)) =
            b ≫ (Over.homMk K₂.f : Over.mk K₂.f ⟶ Over.mk (𝟙 W)) →
            (fun _ : PUnit => compositionMiddleCoverSection (J := J) α β I L i l h K₁) ≫
                P.map a.op =
              (fun _ : PUnit => compositionMiddleCoverSection (J := J) α β I L i l h K₂) ≫
                P.map b.op := by
    intro A K₁ K₂ a b hab
    funext _
    exact hmatch a b hab
  have hmap :=
    hSheaf.amalgamateOfArrows_map
      (f := fun Kp : S.Arrow =>
        (Over.homMk Kp.f : Over.mk Kp.f ⟶ Over.mk (𝟙 W)))
      (hf := compositionMiddleCover_overFamily_covering (J := J) I L i l h)
      (x := fun Kp (_ : PUnit) =>
        compositionMiddleCoverSection (J := J) α β I L i l h Kp)
      (hx := hx) Kp
  change
    ((hSheaf.amalgamateOfArrows
      (f := fun Kp : S.Arrow =>
        (Over.homMk Kp.f : Over.mk Kp.f ⟶ Over.mk (𝟙 W)))
      (hf := compositionMiddleCover_overFamily_covering (J := J) I L i l h)
      (x := fun Kp (_ : PUnit) =>
        compositionMiddleCoverSection (J := J) α β I L i l h Kp)
      (hx := hx)) ≫ P.map
        (Over.homMk Kp.f : Over.mk Kp.f ⟶ Over.mk (𝟙 W)).op) PUnit.unit =
      compositionMiddleCoverSection (J := J) α β I L i l h Kp
  simpa using congrFun hmap PUnit.unit

set_option backward.isDefEq.respectTransparency false in
/-- Source stage 3.3: glue the local sections `d_ijk` under the explicit naturality laws for the
two input `HomOver` families. -/
noncomputable def compositionGluedSection
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (hαnat : familyNaturality' (J := J) α)
    (hβnat : familyNaturality' (J := J) β)
    (I : D.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ f ≫ g = l ≫ L.f)
    (hSheaf : Presheaf.IsSheaf (J.over W)
      ((canonicalFiberPseudofunctor X.p).presheafHom
        (D.restrictedLocalObject I i) (H.restrictedLocalObject L l))) :
    ((canonicalFiberPseudofunctor X.p).presheafHom
      (D.restrictedLocalObject I i) (H.restrictedLocalObject L l)).obj
        (op (Over.mk (𝟙 W))) :=
  compositionGluedSectionOfCompatible (J := J) α β I L i l h hSheaf
    (compositionMiddleCoverSectionCompatible_of_familyNaturality
      (J := J) α β hαnat hβnat I L i l h)

set_option backward.isDefEq.respectTransparency false in
/-- Source stage 3.3: the glued component `c_ik : x_i|_{P_ik} ⟶ z_k`, obtained from the glued
identity-slice Hom-presheaf section. -/
noncomputable def compositionGluedComponent
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (hαnat : familyNaturality' (J := J) α)
    (hβnat : familyNaturality' (J := J) β)
    (I : D.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ f ≫ g = l ≫ L.f)
    (hSheaf : Presheaf.IsSheaf (J.over W)
      ((canonicalFiberPseudofunctor X.p).presheafHom
        (D.restrictedLocalObject I i) (H.restrictedLocalObject L l))) :
    D.restrictedLocalObject I i ⟶ H.restrictedLocalObject L l :=
  ((canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv).symm
    (compositionGluedSection (J := J) α β hαnat hβnat I L i l h hSheaf)

set_option backward.isDefEq.respectTransparency false in
/-- The naturality-based glued section restricts to the prescribed local composite section. -/
theorem compositionGluedSection_map
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (hαnat : familyNaturality' (J := J) α)
    (hβnat : familyNaturality' (J := J) β)
    (I : D.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ f ≫ g = l ≫ L.f)
    (hSheaf : Presheaf.IsSheaf (J.over W)
      ((canonicalFiberPseudofunctor X.p).presheafHom
        (D.restrictedLocalObject I i) (H.restrictedLocalObject L l)))
    (Kp : (compositionMiddleCover (J := J)
      (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h).Arrow) :
    ((canonicalFiberPseudofunctor X.p).presheafHom
      (D.restrictedLocalObject I i) (H.restrictedLocalObject L l)).map
        (Over.homMk Kp.f : Over.mk Kp.f ⟶ Over.mk (𝟙 W)).op
        (compositionGluedSection (J := J) α β hαnat hβnat I L i l h hSheaf) =
      compositionMiddleCoverSection (J := J) α β I L i l h Kp :=
  compositionGluedSectionOfCompatible_map (J := J) α β I L i l h hSheaf
    (compositionMiddleCoverSectionCompatible_of_familyNaturality
      (J := J) α β hαnat hβnat I L i l h)
    Kp

set_option backward.isDefEq.respectTransparency false in
/-- The glued component `c_ik`, when restricted to a member of the middle cover, is the section
`d_ijk = b_jk ∘ a_ij` with the canonical source and target pseudofunctor comparisons. -/
theorem compositionGluedComponent_map
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (hαnat : familyNaturality' (J := J) α)
    (hβnat : familyNaturality' (J := J) β)
    (I : D.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ f ≫ g = l ≫ L.f)
    (hSheaf : Presheaf.IsSheaf (J.over W)
      ((canonicalFiberPseudofunctor X.p).presheafHom
        (D.restrictedLocalObject I i) (H.restrictedLocalObject L l)))
    (Kp : (compositionMiddleCover (J := J)
      (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h).Arrow) :
    ((canonicalFiberPseudofunctor X.p).map Kp.f.op.toLoc).toFunctor.map
        (compositionGluedComponent (J := J) α β hαnat hβnat I L i l h hSheaf) =
      compositionMiddleCoverSection (J := J) α β I L i l h Kp := by
  let P := (canonicalFiberPseudofunctor X.p).presheafHom
    (D.restrictedLocalObject I i) (H.restrictedLocalObject L l)
  let c := compositionGluedComponent (J := J) α β hαnat hβnat I L i l h hSheaf
  have hsection :
      (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv c =
        compositionGluedSection (J := J) α β hαnat hβnat I L i l h hSheaf := by
    dsimp [c, compositionGluedComponent]
    exact Equiv.apply_symm_apply _ _
  have hmap := compositionGluedSection_map
    (J := J) α β hαnat hβnat I L i l h hSheaf Kp
  rw [← hsection] at hmap
  rw [← hmap]
  symm
  simpa [P, c] using
    presheafHom_map_identitySlice_hom_overMk (p := X.p) Kp.f
      (D.restrictedLocalObject I i) (H.restrictedLocalObject L l) c

set_option backward.isDefEq.respectTransparency false in
/-- Pulling the glued component `c_ik` back to a middle-cover member gives exactly the ordinary
local composite `b_jk ∘ a_ij`. -/
theorem compositionGluedComponent_pullHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (hαnat : familyNaturality' (J := J) α)
    (hβnat : familyNaturality' (J := J) β)
    (I : D.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ f ≫ g = l ≫ L.f)
    (hSheaf : Presheaf.IsSheaf (J.over W)
      ((canonicalFiberPseudofunctor X.p).presheafHom
        (D.restrictedLocalObject I i) (H.restrictedLocalObject L l)))
    (Kp : (compositionMiddleCover (J := J)
      (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h).Arrow) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (compositionGluedComponent (J := J) α β hαnat hβnat I L i l h hSheaf)
        Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl =
      localComposite (J := J) α β I Kp.base L
        (Kp.f ≫ i) (𝟙 Kp.Y) (Kp.f ≫ l)
        (by simp [compositionMiddleCover, Category.assoc])
        (by
          simpa [compositionMiddleCover, Category.assoc] using
            congrArg (fun q => Kp.f ≫ q) h) := by
  dsimp [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  rw [compositionGluedComponent_map (J := J) α β hαnat hβnat I L i l h hSheaf Kp]
  change
    ((canonicalFiberPseudofunctor X.p).mapComp' i.op.toLoc Kp.f.op.toLoc
        ((Kp.f ≫ i).op.toLoc) (by rfl)).hom.toNatTrans.app (D.localObject I) ≫
      compositionMiddleCoverSection (J := J) α β I L i l h Kp ≫
        ((canonicalFiberPseudofunctor X.p).mapComp' l.op.toLoc Kp.f.op.toLoc
          ((Kp.f ≫ l).op.toLoc) (by rfl)).inv.toNatTrans.app (H.localObject L) =
      localComposite (J := J) α β I Kp.base L
        (Kp.f ≫ i) (𝟙 Kp.Y) (Kp.f ≫ l)
        (by simp [compositionMiddleCover, Category.assoc])
        (by
          simpa [compositionMiddleCover, Category.assoc] using
            congrArg (fun q => Kp.f ≫ q) h)
  simp only [compositionMiddleCoverSection, compositionMiddleCoverComposite,
    compositionMiddleCoverSourceIso, compositionMiddleCoverTargetIso, Cat.Hom.toNatIso,
    Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv,
    Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]
  rw [← Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Variant of `compositionGluedComponent_pullHom` where the two target restriction arrows are
supplied explicitly.  This is useful when source-faithful pullback notation produces
`(a ≫ b) ≫ c` on one side and `a ≫ (b ≫ c)` on the other. -/
theorem compositionGluedComponent_pullHom_of_fac
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (hαnat : familyNaturality' (J := J) α)
    (hβnat : familyNaturality' (J := J) β)
    (I : D.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ f ≫ g = l ≫ L.f)
    (hSheaf : Presheaf.IsSheaf (J.over W)
      ((canonicalFiberPseudofunctor X.p).presheafHom
        (D.restrictedLocalObject I i) (H.restrictedLocalObject L l)))
    (Kp : (compositionMiddleCover (J := J)
      (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h).Arrow)
    (ki : Kp.Y ⟶ I.Y) (kl : Kp.Y ⟶ L.Y)
    (hki : Kp.f ≫ i = ki) (hkl : Kp.f ≫ l = kl)
    (hα : ki ≫ I.f ≫ f = 𝟙 Kp.Y ≫ Kp.base.f)
    (hβ : 𝟙 Kp.Y ≫ Kp.base.f ≫ g = kl ≫ L.f) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (compositionGluedComponent (J := J) α β hαnat hβnat I L i l h hSheaf)
        Kp.f ki kl hki hkl =
      localComposite (J := J) α β I Kp.base L
        ki (𝟙 Kp.Y) kl hα hβ := by
  subst ki
  subst kl
  have h0 := compositionGluedComponent_pullHom (J := J)
    α β hαnat hβnat I L i l h hSheaf Kp
  simpa [localComposite, Category.assoc] using h0

/-- The Hom-presheaf sheaf condition needed for source stage 3.3 and later stage 3.4.  This is
the condition supplied by source stage 2 before descent-data objects are adjoined. -/
def homPresheavesAreSheaves
    (X : FibredCategoryOver.{u, v, uX, vX} C) : Prop :=
  ∀ (W : C) (x y : X.p.Fiber W),
    Presheaf.IsSheaf (J.over W)
      ((canonicalFiberPseudofunctor X.p).presheafHom x y)

set_option backward.isDefEq.respectTransparency false in
/-- Source stage 3.3 candidate for the composite morphism family:
`c_ik : x_i|_{P_ik} ⟶ z_k`, obtained by sheaf-gluing the local composites over the pulled-back
middle cover. -/
noncomputable def compositionFamily
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (hSheaf : homPresheavesAreSheaves (J := J) X)
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (hαnat : familyNaturality' (J := J) α)
    (hβnat : familyNaturality' (J := J) β)
    {W : C} (I : D.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ (f ≫ g) = l ≫ L.f) :
    D.restrictedLocalObject I i ⟶ H.restrictedLocalObject L l :=
  compositionGluedComponent (J := J) α β hαnat hβnat I L i l
    (by simpa [Category.assoc] using h)
    (hSheaf W (D.restrictedLocalObject I i) (H.restrictedLocalObject L l))

set_option backward.isDefEq.respectTransparency false in
/-- The candidate composite family restricts to the source-local composite on each member of the
middle cover. -/
theorem compositionFamily_map
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (hSheaf : homPresheavesAreSheaves (J := J) X)
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (hαnat : familyNaturality' (J := J) α)
    (hβnat : familyNaturality' (J := J) β)
    (I : D.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ (f ≫ g) = l ≫ L.f)
    (Kp : (compositionMiddleCover (J := J)
      (D := D) (E := E) (H := H) (f := f) (g := g) I L i l
        (by simpa [Category.assoc] using h)).Arrow) :
    ((canonicalFiberPseudofunctor X.p).map Kp.f.op.toLoc).toFunctor.map
        (compositionFamily (J := J) hSheaf α β hαnat hβnat I L i l h) =
      compositionMiddleCoverSection (J := J) α β I L i l
        (by simpa [Category.assoc] using h) Kp := by
  unfold compositionFamily
  exact
    compositionGluedComponent_map (J := J) α β hαnat hβnat I L i l
      (by simpa [Category.assoc] using h)
      (hSheaf W (D.restrictedLocalObject I i) (H.restrictedLocalObject L l)) Kp

/-- Source stage 3.4 global compatibility obligation for the glued composite family.  The source
proves this by restricting to the cover `Q_j`, using `localComposite_outer_compatible`, and then
using separatedness of Hom sheaves. -/
def compositionFamilyCompatible
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (hSheaf : homPresheavesAreSheaves (J := J) X)
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (hαnat : familyNaturality' (J := J) α)
    (hβnat : familyNaturality' (J := J) β) : Prop :=
  ∀ {W : C} (I₁ I₂ : D.cover.Arrow) (L₁ L₂ : H.cover.Arrow)
    (i₁ : W ⟶ I₁.Y) (i₂ : W ⟶ I₂.Y)
    (l₁ : W ⟶ L₁.Y) (l₂ : W ⟶ L₂.Y)
    (hD : i₁ ≫ I₁.f = i₂ ≫ I₂.f)
    (hH : l₁ ≫ L₁.f = l₂ ≫ L₂.f)
    (h₁ : i₁ ≫ I₁.f ≫ (f ≫ g) = l₁ ≫ L₁.f)
    (h₂ : i₂ ≫ I₂.f ≫ (f ≫ g) = l₂ ≫ L₂.f),
      (D.overlapIso i₁ i₂ hD).hom ≫
          compositionFamily (J := J) hSheaf α β hαnat hβnat I₂ L₂ i₂ l₂ h₂ =
        compositionFamily (J := J) hSheaf α β hαnat hβnat I₁ L₁ i₁ l₁ h₁ ≫
          (H.overlapIso l₁ l₂ hH).hom

set_option backward.isDefEq.respectTransparency false in
/-- Source stage 3.4: the composite family obtained by gluing the local composites satisfies the
descent-morphism compatibility condition.  The proof follows the source text: restrict the desired
equality to the middle cover `Q_j`, unfold both glued components there, and use
`localComposite_outer_compatible`. -/
theorem compositionFamilyCompatible_of_familyNaturality
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (hSheaf : homPresheavesAreSheaves (J := J) X)
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (hαnat : familyNaturality' (J := J) α)
    (hβnat : familyNaturality' (J := J) β) :
    compositionFamilyCompatible (J := J) hSheaf α β hαnat hβnat := by
  intro W I₁ I₂ L₁ L₂ i₁ i₂ l₁ l₂ hD hH h₁ h₂
  let h₁' : i₁ ≫ I₁.f ≫ f ≫ g = l₁ ≫ L₁.f := by
    simpa [Category.assoc] using h₁
  let h₂' : i₂ ≫ I₂.f ≫ f ≫ g = l₂ ≫ L₂.f := by
    simpa [Category.assoc] using h₂
  let S := compositionMiddleCover (J := J)
    (D := D) (E := E) (H := H) (f := f) (g := g) I₁ L₁ i₁ l₁ h₁'
  apply fiberHom_ext_of_cover (J := J) X.p S
    (D.restrictedLocalObject I₁ i₁) (H.restrictedLocalObject L₂ l₂)
    (hSheaf W (D.restrictedLocalObject I₁ i₁) (H.restrictedLocalObject L₂ l₂))
  intro Kp
  let K₁ :
      (compositionMiddleCover (J := J)
        (D := D) (E := E) (H := H) (f := f) (g := g) I₁ L₁ i₁ l₁ h₁').Arrow := Kp
  have hbase₂ : Kp.f ≫ i₁ ≫ I₁.f ≫ f = Kp.f ≫ i₂ ≫ I₂.f ≫ f := by
    simpa [Category.assoc] using congrArg (fun q => Kp.f ≫ q ≫ f) hD
  let K₂ :
      (compositionMiddleCover (J := J)
        (D := D) (E := E) (H := H) (f := f) (g := g) I₂ L₂ i₂ l₂ h₂').Arrow :=
    { Y := Kp.Y
      f := Kp.f
      hf := by
        have hf₁ :
            E.cover (Kp.f ≫ i₁ ≫ I₁.f ≫ f) := by
          simpa [S, compositionMiddleCover, Category.assoc] using Kp.hf
        simpa [compositionMiddleCover, Category.assoc, hbase₂] using hf₁ }
  have hmapD := overlapIso_map_eq (J := J) D I₁ I₂ i₁ i₂ hD Kp.f
  have hmapH := overlapIso_map_eq (J := J) H L₁ L₂ l₁ l₂ hH Kp.f
  have hmapC₁ := compositionFamily_map (J := J) hSheaf α β hαnat hβnat
    I₁ L₁ i₁ l₁ h₁ K₁
  have hmapC₂ := compositionFamily_map (J := J) hSheaf α β hαnat hβnat
    I₂ L₂ i₂ l₂ h₂ K₂
  have hlocal := localComposite_outer_compatible_of_middle (J := J) α β
    I₁ I₂ Kp.base K₂.base L₁ L₂
    (Kp.f ≫ i₁) (Kp.f ≫ i₂) (𝟙 Kp.Y) (𝟙 Kp.Y) (Kp.f ≫ l₁) (Kp.f ≫ l₂)
    (by simpa [Category.assoc] using congrArg (fun q => Kp.f ≫ q) hD)
    (by
      calc
        𝟙 Kp.Y ≫ Kp.base.f =
            Kp.f ≫ i₁ ≫ I₁.f ≫ f := by
              simp [S, compositionMiddleCover]
        _ = Kp.f ≫ i₂ ≫ I₂.f ≫ f := hbase₂
        _ = 𝟙 Kp.Y ≫ K₂.base.f := by
              simp [K₂, compositionMiddleCover])
    (by simpa [Category.assoc] using congrArg (fun q => Kp.f ≫ q) hH)
    (by simp [S, compositionMiddleCover, Category.assoc])
    (by simp [K₂, compositionMiddleCover, Category.assoc])
    (by
      simpa [Category.assoc] using congrArg (fun q => Kp.f ≫ q) h₁')
    (by
      calc
        𝟙 Kp.Y ≫ K₂.base.f ≫ g =
            Kp.f ≫ i₂ ≫ I₂.f ≫ f ≫ g := by
              simp [K₂, compositionMiddleCover, Category.assoc]
        _ = (Kp.f ≫ l₂) ≫ L₂.f := by
              simpa [Category.assoc] using congrArg (fun q => Kp.f ≫ q) h₂')
  rw [Functor.map_comp, Functor.map_comp]
  rw [hmapD, hmapC₂, hmapC₁, hmapH]
  simp only [compositionMiddleCoverSection, compositionMiddleCoverSourceIso,
    compositionMiddleCoverTargetIso, restrictedLocalObjectCompIso,
    Cat.Hom.toNatIso, Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv,
    Category.assoc]
  let A :=
    ((canonicalFiberPseudofunctor X.p).mapComp' i₁.op.toLoc Kp.f.op.toLoc
      ((Kp.f ≫ i₁).op.toLoc) (by rfl)).inv.toNatTrans.app (D.localObject I₁)
  let B :=
    ((canonicalFiberPseudofunctor X.p).mapComp' l₂.op.toLoc Kp.f.op.toLoc
      ((Kp.f ≫ l₂).op.toLoc) (by rfl)).hom.toNatTrans.app (H.localObject L₂)
  have hwrapped := congrArg (fun t => A ≫ t ≫ B) hlocal
  simpa [A, B, K₁, K₂, h₁', h₂', S, compositionMiddleCoverComposite, Category.assoc] using hwrapped

set_option backward.isDefEq.respectTransparency false in
/-- Conditional source stage 3.3-3.4 composite of two descent-completion morphism families.  The
only remaining mathematical input is the global compatibility proof isolated in
`compositionFamilyCompatible`. -/
noncomputable def composeOfCompatible
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (hSheaf : homPresheavesAreSheaves (J := J) X)
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (hαnat : familyNaturality' (J := J) α)
    (hβnat : familyNaturality' (J := J) β)
    (hcompat : compositionFamilyCompatible (J := J) hSheaf α β hαnat hβnat) :
    HomOver (J := J) D H (f ≫ g) where
  family I L i l h :=
    compositionFamily (J := J) hSheaf α β hαnat hβnat I L i l h
  compatible := hcompat

@[simp]
theorem composeOfCompatible_family
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (hSheaf : homPresheavesAreSheaves (J := J) X)
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (hαnat : familyNaturality' (J := J) α)
    (hβnat : familyNaturality' (J := J) β)
    (hcompat : compositionFamilyCompatible (J := J) hSheaf α β hαnat hβnat)
    (I : D.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ (f ≫ g) = l ≫ L.f) :
    (composeOfCompatible (J := J) hSheaf α β hαnat hβnat hcompat).family
        I L i l h =
      compositionFamily (J := J) hSheaf α β hαnat hβnat I L i l h :=
  rfl

/-- Source stages 3.3-3.4 combined: under the explicit restriction/naturality laws for the two
input families, the glued composite is a compatible `HomOver`.  This keeps the current owner-level
`familyNaturality'` hypothesis explicit rather than baking it into `HomOver` prematurely. -/
noncomputable def composeOfFamilyNaturality
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (hSheaf : homPresheavesAreSheaves (J := J) X)
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (hαnat : familyNaturality' (J := J) α)
    (hβnat : familyNaturality' (J := J) β) :
    HomOver (J := J) D H (f ≫ g) :=
  composeOfCompatible (J := J) hSheaf α β hαnat hβnat
    (compositionFamilyCompatible_of_familyNaturality (J := J) hSheaf α β hαnat hβnat)

@[simp]
theorem composeOfFamilyNaturality_family
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (hSheaf : homPresheavesAreSheaves (J := J) X)
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (hαnat : familyNaturality' (J := J) α)
    (hβnat : familyNaturality' (J := J) β)
    (I : D.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ (f ≫ g) = l ≫ L.f) :
    (composeOfFamilyNaturality (J := J) hSheaf α β hαnat hβnat).family
        I L i l h =
      compositionFamily (J := J) hSheaf α β hαnat hβnat I L i l h :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Source stage 3.4, owner-level restriction law: the glued composite components commute with
further restriction.  The proof follows the same source argument as compatibility: after restricting
to the pulled-back middle cover both sides become the same local composite `b_jk ∘ a_ij`, and the
Hom sheaf separates the two candidates. -/
theorem compositionFamily_familyNaturality
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (hSheaf : homPresheavesAreSheaves (J := J) X)
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (hαnat : familyNaturality' (J := J) α)
    (hβnat : familyNaturality' (J := J) β) :
    familyNaturality' (J := J)
      (composeOfFamilyNaturality (J := J) hSheaf α β hαnat hβnat) := by
  intro W W' I L i l h m mi ml hmi hml
  subst mi
  subst ml
  let hlarge : i ≫ I.f ≫ f ≫ g = l ≫ L.f := by
    simpa [Category.assoc] using h
  let hsmall : (m ≫ i) ≫ I.f ≫ f ≫ g = (m ≫ l) ≫ L.f := by
    simpa [Category.assoc] using congrArg (fun q => m ≫ q) hlarge
  let S := compositionMiddleCover (J := J)
    (D := D) (E := E) (H := H) (f := f) (g := g) I L (m ≫ i) (m ≫ l) hsmall
  apply fiberHom_ext_of_cover (J := J) X.p S
    (D.restrictedLocalObject I (m ≫ i)) (H.restrictedLocalObject L (m ≫ l))
    (hSheaf W' (D.restrictedLocalObject I (m ≫ i))
      (H.restrictedLocalObject L (m ≫ l)))
  intro Kp
  change
    ((canonicalFiberPseudofunctor X.p).map Kp.f.op.toLoc).toFunctor.map
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (compositionFamily (J := J) hSheaf α β hαnat hβnat I L i l h)
          m (m ≫ i) (m ≫ l) rfl rfl) =
      ((canonicalFiberPseudofunctor X.p).map Kp.f.op.toLoc).toFunctor.map
        (compositionFamily (J := J) hSheaf α β hαnat hβnat I L (m ≫ i) (m ≫ l)
          (by simpa [Category.assoc] using hsmall))
  let Kouter :
      (compositionMiddleCover (J := J)
        (D := D) (E := E) (H := H) (f := f) (g := g) I L i l hlarge).Arrow :=
    { Y := Kp.Y
      f := Kp.f ≫ m
      hf := by
        have hf' : E.cover (Kp.f ≫ (m ≫ i) ≫ I.f ≫ f) := by
          simpa [S, compositionMiddleCover, Category.assoc] using Kp.hf
        simpa [compositionMiddleCover, Category.assoc] using hf' }
  let hαK : ((Kp.f ≫ m) ≫ i) ≫ I.f ≫ f = 𝟙 Kp.Y ≫ Kp.base.f := by
    simp [S, compositionMiddleCover, Category.assoc]
  let hβK : 𝟙 Kp.Y ≫ Kp.base.f ≫ g = ((Kp.f ≫ m) ≫ l) ≫ L.f := by
    simpa [S, compositionMiddleCover, Category.assoc] using
      congrArg (fun q => Kp.f ≫ q) hsmall
  let localComp :=
    localComposite (J := J) α β I Kp.base L
      ((Kp.f ≫ m) ≫ i) (𝟙 Kp.Y) ((Kp.f ≫ m) ≫ l) hαK hβK
  have hleftPull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (F := canonicalFiberPseudofunctor X.p)
            (compositionFamily (J := J) hSheaf α β hαnat hβnat I L i l h)
            m (m ≫ i) (m ≫ l) rfl rfl)
          Kp.f ((Kp.f ≫ m) ≫ i) ((Kp.f ≫ m) ≫ l)
          (by simp [Category.assoc]) (by simp [Category.assoc]) =
        localComp := by
    rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_pullHom]
    let hαOuter :
        ((Kp.f ≫ m) ≫ i) ≫ I.f ≫ f = 𝟙 Kp.Y ≫ Kouter.base.f := by
      simp [Kouter, compositionMiddleCover, Category.assoc]
    let hβOuter :
        𝟙 Kp.Y ≫ Kouter.base.f ≫ g = ((Kp.f ≫ m) ≫ l) ≫ L.f := by
      simpa [Kouter, compositionMiddleCover, Category.assoc] using
        congrArg (fun q => Kp.f ≫ m ≫ q) hlarge
    let localOuter :=
      localComposite (J := J) α β I Kouter.base L
        ((Kp.f ≫ m) ≫ i) (𝟙 Kp.Y) ((Kp.f ≫ m) ≫ l) hαOuter hβOuter
    have houter := compositionGluedComponent_pullHom_of_fac (J := J)
      α β hαnat hβnat I L i l hlarge
      (hSheaf W (D.restrictedLocalObject I i) (H.restrictedLocalObject L l)) Kouter
      ((Kp.f ≫ m) ≫ i) ((Kp.f ≫ m) ≫ l) rfl rfl hαOuter hβOuter
    have houterPull :
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (compositionFamily (J := J) hSheaf α β hαnat hβnat I L i l h)
            (Kp.f ≫ m) ((Kp.f ≫ m) ≫ i) ((Kp.f ≫ m) ≫ l) rfl rfl =
          localOuter := by
      simpa [compositionFamily, localOuter, Kouter, Category.assoc] using
        houter
    have hK :
        (𝟙 Kp.Y : Kp.Y ⟶ Kouter.base.Y) ≫ Kouter.base.f =
          (𝟙 Kp.Y : Kp.Y ⟶ Kp.base.Y) ≫ Kp.base.f := by
      simp [Kouter, S, compositionMiddleCover, Category.assoc]
    have hmiddle :
        localOuter = localComp := by
      exact localComposite_middle_compatible (J := J) α β I Kouter.base Kp.base L
        ((Kp.f ≫ m) ≫ i) (𝟙 Kp.Y) (𝟙 Kp.Y) ((Kp.f ≫ m) ≫ l)
        hK hαOuter hαK hβOuter hβK
    exact houterPull.trans hmiddle
  have hrightPull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (compositionFamily (J := J) hSheaf α β hαnat hβnat I L (m ≫ i) (m ≫ l)
            (by
              simpa [Category.assoc] using hsmall))
          Kp.f ((Kp.f ≫ m) ≫ i) ((Kp.f ≫ m) ≫ l)
          (by simp [Category.assoc]) (by simp [Category.assoc]) =
        localComp := by
    have hinner := compositionGluedComponent_pullHom_of_fac (J := J)
      α β hαnat hβnat I L (m ≫ i) (m ≫ l) hsmall
      (hSheaf W' (D.restrictedLocalObject I (m ≫ i))
        (H.restrictedLocalObject L (m ≫ l))) Kp
      ((Kp.f ≫ m) ≫ i) ((Kp.f ≫ m) ≫ l)
      (by simp [Category.assoc]) (by simp [Category.assoc]) hαK hβK
    simpa [compositionFamily, localComp, Category.assoc] using hinner
  have hpull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (F := canonicalFiberPseudofunctor X.p)
            (compositionFamily (J := J) hSheaf α β hαnat hβnat I L i l h)
            m (m ≫ i) (m ≫ l) rfl rfl)
          Kp.f ((Kp.f ≫ m) ≫ i) ((Kp.f ≫ m) ≫ l)
          (by simp [Category.assoc]) (by simp [Category.assoc]) =
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (compositionFamily (J := J) hSheaf α β hαnat hβnat I L (m ≫ i) (m ≫ l)
            (by
              simpa [Category.assoc] using hsmall))
          Kp.f ((Kp.f ≫ m) ≫ i) ((Kp.f ≫ m) ≫ l)
          (by simp [Category.assoc]) (by simp [Category.assoc]) := by
    rw [hleftPull, hrightPull]
  have hmapLeft :=
    Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
      (F := canonicalFiberPseudofunctor X.p)
      (φ :=
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (compositionFamily (J := J) hSheaf α β hαnat hβnat I L i l h)
          m (m ≫ i) (m ≫ l) rfl rfl)
      Kp.f ((Kp.f ≫ m) ≫ i) ((Kp.f ≫ m) ≫ l)
      (by simp [Category.assoc]) (by simp [Category.assoc])
  have hmapRight :=
    Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
      (F := canonicalFiberPseudofunctor X.p)
      (φ :=
        compositionFamily (J := J) hSheaf α β hαnat hβnat I L (m ≫ i) (m ≫ l)
          (by
            simpa [Category.assoc] using hsmall))
      Kp.f ((Kp.f ≫ m) ≫ i) ((Kp.f ≫ m) ≫ l)
      (by simp [Category.assoc]) (by simp [Category.assoc])
  rw [hmapLeft, hmapRight, hpull]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Source stage 3.5, left bracketing on the fourfold refinement: after first restricting the
glued component for `(γ ∘ (β ∘ α))` to a member of the `H`-cover and then to a member of the
`E`-cover, it is the ordinary triple local composite
`a_ij ≫ b_jk ≫ c_kl`. -/
theorem compositionFamily_assoc_left_pullHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z T W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {KObj : DescentCompletionObjectOver (J := J) X T}
    {f : U ⟶ V} {g : V ⟶ Z} {r : Z ⟶ T}
    (hSheaf : homPresheavesAreSheaves (J := J) X)
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (γ : HomOver (J := J) H KObj r)
    (hαnat : familyNaturality' (J := J) α)
    (hβnat : familyNaturality' (J := J) β)
    (hγnat : familyNaturality' (J := J) γ)
    (I : D.cover.Arrow) (M : KObj.cover.Arrow)
    (i : W ⟶ I.Y) (m : W ⟶ M.Y)
    (h : i ≫ I.f ≫ ((f ≫ g) ≫ r) = m ≫ M.f)
    (L : (compositionMiddleCover (J := J)
      (D := D) (E := H) (H := KObj) (f := f ≫ g) (g := r)
      I M i m (by simpa [Category.assoc] using h)).Arrow)
    (K : (compositionMiddleCover (J := J)
      (D := D) (E := E) (H := H) (f := f) (g := g)
      I L.base (L.f ≫ i) (𝟙 L.Y)
      (by simp [compositionMiddleCover, Category.assoc])).Arrow) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (compositionFamily (J := J) hSheaf
            (composeOfFamilyNaturality (J := J) hSheaf α β hαnat hβnat) γ
            (compositionFamily_familyNaturality (J := J) hSheaf α β hαnat hβnat)
            hγnat I M i m h)
          L.f (L.f ≫ i) (L.f ≫ m) rfl rfl)
        K.f ((K.f ≫ L.f) ≫ i) ((K.f ≫ L.f) ≫ m)
        (by simp [Category.assoc]) (by simp [Category.assoc]) =
      (α.family I K.base ((K.f ≫ L.f) ≫ i) (𝟙 K.Y)
          (by simp [compositionMiddleCover, Category.assoc]) ≫
        β.family K.base L.base (𝟙 K.Y) K.f
          (by simp [compositionMiddleCover, Category.assoc])) ≫
        γ.family L.base M K.f ((K.f ≫ L.f) ≫ m)
          (by
            have hOuterBase : i ≫ I.f ≫ (f ≫ g) ≫ r = m ≫ M.f := by
              simpa [Category.assoc] using h
            calc
              K.f ≫ L.base.f ≫ r =
                  K.f ≫ L.f ≫ i ≫ I.f ≫ (f ≫ g) ≫ r := by
                    simp [compositionMiddleCover, Category.assoc]
              _ = ((K.f ≫ L.f) ≫ m) ≫ M.f := by
                    simpa [Category.assoc] using
                      congrArg (fun q => K.f ≫ L.f ≫ q) hOuterBase) := by
  let αβ : HomOver (J := J) D H (f ≫ g) :=
    composeOfFamilyNaturality (J := J) hSheaf α β hαnat hβnat
  let hαβnat : familyNaturality' (J := J) αβ :=
    compositionFamily_familyNaturality (J := J) hSheaf α β hαnat hβnat
  let hOuterBase : i ≫ I.f ≫ (f ≫ g) ≫ r = m ≫ M.f := by
    simpa [Category.assoc] using h
  let hOuterα : (L.f ≫ i) ≫ I.f ≫ (f ≫ g) = 𝟙 L.Y ≫ L.base.f := by
    simp [compositionMiddleCover, Category.assoc]
  let hOuterγ : 𝟙 L.Y ≫ L.base.f ≫ r = (L.f ≫ m) ≫ M.f := by
    simpa [compositionMiddleCover, Category.assoc] using
      congrArg (fun q => L.f ≫ q) hOuterBase
  have houter := compositionGluedComponent_pullHom_of_fac (J := J)
    αβ γ hαβnat hγnat I M i m hOuterBase
    (hSheaf W (D.restrictedLocalObject I i) (KObj.restrictedLocalObject M m)) L
    (L.f ≫ i) (L.f ≫ m) rfl rfl hOuterα hOuterγ
  have houter' :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (compositionFamily (J := J) hSheaf
            (composeOfFamilyNaturality (J := J) hSheaf α β hαnat hβnat) γ
            (compositionFamily_familyNaturality (J := J) hSheaf α β hαnat hβnat)
            hγnat I M i m h)
          L.f (L.f ≫ i) (L.f ≫ m) rfl rfl =
        localComposite (J := J) αβ γ I L.base M
          (L.f ≫ i) (𝟙 L.Y) (L.f ≫ m) hOuterα hOuterγ := by
    simpa [αβ, compositionFamily, Category.assoc] using houter
  rw [houter']
  let hαK : ((K.f ≫ L.f) ≫ i) ≫ I.f ≫ f = 𝟙 K.Y ≫ K.base.f := by
    simp [compositionMiddleCover, Category.assoc]
  let hβK : 𝟙 K.Y ≫ K.base.f ≫ g = K.f ≫ L.base.f := by
    simp [compositionMiddleCover, Category.assoc]
  let hγK : K.f ≫ L.base.f ≫ r = ((K.f ≫ L.f) ≫ m) ≫ M.f := by
    simpa [compositionMiddleCover, Category.assoc] using
      congrArg (fun q => K.f ≫ q) hOuterγ
  have hαβPull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (αβ.family I L.base (L.f ≫ i) (𝟙 L.Y) hOuterα)
          K.f ((K.f ≫ L.f) ≫ i) K.f
          (by simp [Category.assoc]) (by simp) =
        α.family I K.base ((K.f ≫ L.f) ≫ i) (𝟙 K.Y) hαK ≫
          β.family K.base L.base (𝟙 K.Y) K.f hβK := by
    have hglue := compositionGluedComponent_pullHom_of_fac (J := J)
      α β hαnat hβnat I L.base (L.f ≫ i) (𝟙 L.Y) hOuterα
      (hSheaf L.Y (D.restrictedLocalObject I (L.f ≫ i))
        (H.restrictedLocalObject L.base (𝟙 L.Y))) K
      ((K.f ≫ L.f) ≫ i) K.f
      (by simp [Category.assoc]) (by simp) hαK hβK
    simpa [αβ, composeOfFamilyNaturality, composeOfCompatible, compositionFamily,
      localComposite, Category.assoc] using hglue
  have hγPull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (γ.family L.base M (𝟙 L.Y) (L.f ≫ m) hOuterγ)
          K.f K.f ((K.f ≫ L.f) ≫ m)
          (by simp) (by simp [Category.assoc]) =
        γ.family L.base M K.f ((K.f ≫ L.f) ≫ m) hγK := by
    simpa [hγK] using
      hγnat L.base M (𝟙 L.Y) (L.f ≫ m) hOuterγ
        K.f K.f ((K.f ≫ L.f) ≫ m) (by simp) (by simp [Category.assoc])
  unfold localComposite
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp
    (F := canonicalFiberPseudofunctor X.p)
    (αβ.family I L.base (L.f ≫ i) (𝟙 L.Y) hOuterα)
    (γ.family L.base M (𝟙 L.Y) (L.f ≫ m) hOuterγ)
    K.f ((K.f ≫ L.f) ≫ i) K.f ((K.f ≫ L.f) ≫ m)
    (by simp [Category.assoc]) (by simp) (by simp [Category.assoc])]
  rw [hαβPull, hγPull]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Source stage 3.5, right bracketing on the fourfold refinement: after first restricting the
glued component for `((γ ∘ β) ∘ α)` to a member of the `E`-cover and then to a member of the
`H`-cover, it is the ordinary triple local composite
`a_ij ≫ b_jk ≫ c_kl`. -/
theorem compositionFamily_assoc_right_pullHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z T W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {KObj : DescentCompletionObjectOver (J := J) X T}
    {f : U ⟶ V} {g : V ⟶ Z} {r : Z ⟶ T}
    (hSheaf : homPresheavesAreSheaves (J := J) X)
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (γ : HomOver (J := J) H KObj r)
    (hαnat : familyNaturality' (J := J) α)
    (hβnat : familyNaturality' (J := J) β)
    (hγnat : familyNaturality' (J := J) γ)
    (I : D.cover.Arrow) (M : KObj.cover.Arrow)
    (i : W ⟶ I.Y) (m : W ⟶ M.Y)
    (h : i ≫ I.f ≫ (f ≫ (g ≫ r)) = m ≫ M.f)
    (K : (compositionMiddleCover (J := J)
      (D := D) (E := E) (H := KObj) (f := f) (g := g ≫ r)
      I M i m (by simpa [Category.assoc] using h)).Arrow)
    (L : (compositionMiddleCover (J := J)
      (D := E) (E := H) (H := KObj) (f := g) (g := r)
      K.base M (𝟙 K.Y) (K.f ≫ m)
      (by
        simpa [compositionMiddleCover, Category.assoc] using
          congrArg (fun q => K.f ≫ q) (by
            simpa [Category.assoc] using h))).Arrow) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (compositionFamily (J := J) hSheaf α
            (composeOfFamilyNaturality (J := J) hSheaf β γ hβnat hγnat)
            hαnat
            (compositionFamily_familyNaturality (J := J) hSheaf β γ hβnat hγnat)
            I M i m h)
          K.f (K.f ≫ i) (K.f ≫ m) rfl rfl)
        L.f ((L.f ≫ K.f) ≫ i) ((L.f ≫ K.f) ≫ m)
        (by simp [Category.assoc]) (by simp [Category.assoc]) =
      (α.family I K.base ((L.f ≫ K.f) ≫ i) L.f
          (by simp [compositionMiddleCover, Category.assoc]) ≫
        β.family K.base L.base L.f (𝟙 L.Y)
          (by simp [compositionMiddleCover, Category.assoc])) ≫
        γ.family L.base M (𝟙 L.Y) ((L.f ≫ K.f) ≫ m)
          (by
            have hOuterBase : i ≫ I.f ≫ f ≫ (g ≫ r) = m ≫ M.f := by
              simpa [Category.assoc] using h
            calc
              𝟙 L.Y ≫ L.base.f ≫ r =
                  L.f ≫ K.f ≫ i ≫ I.f ≫ f ≫ g ≫ r := by
                    simp [compositionMiddleCover, Category.assoc]
              _ = ((L.f ≫ K.f) ≫ m) ≫ M.f := by
                    simpa [Category.assoc] using
                      congrArg (fun q => L.f ≫ K.f ≫ q) hOuterBase) := by
  let βγ : HomOver (J := J) E KObj (g ≫ r) :=
    composeOfFamilyNaturality (J := J) hSheaf β γ hβnat hγnat
  let hβγnat : familyNaturality' (J := J) βγ :=
    compositionFamily_familyNaturality (J := J) hSheaf β γ hβnat hγnat
  let hOuterBase : i ≫ I.f ≫ f ≫ (g ≫ r) = m ≫ M.f := by
    simpa [Category.assoc] using h
  let hOuterα : (K.f ≫ i) ≫ I.f ≫ f = 𝟙 K.Y ≫ K.base.f := by
    simp [compositionMiddleCover, Category.assoc]
  let hOuterβγ : 𝟙 K.Y ≫ K.base.f ≫ (g ≫ r) = (K.f ≫ m) ≫ M.f := by
    simpa [compositionMiddleCover, Category.assoc] using
      congrArg (fun q => K.f ≫ q) hOuterBase
  have houter := compositionGluedComponent_pullHom_of_fac (J := J)
    α βγ hαnat hβγnat I M i m hOuterBase
    (hSheaf W (D.restrictedLocalObject I i) (KObj.restrictedLocalObject M m)) K
    (K.f ≫ i) (K.f ≫ m) rfl rfl hOuterα hOuterβγ
  have houter' :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (compositionFamily (J := J) hSheaf α
            (composeOfFamilyNaturality (J := J) hSheaf β γ hβnat hγnat)
            hαnat
            (compositionFamily_familyNaturality (J := J) hSheaf β γ hβnat hγnat)
            I M i m h)
          K.f (K.f ≫ i) (K.f ≫ m) rfl rfl =
        localComposite (J := J) α βγ I K.base M
          (K.f ≫ i) (𝟙 K.Y) (K.f ≫ m) hOuterα hOuterβγ := by
    simpa [βγ, compositionFamily, Category.assoc] using houter
  rw [houter']
  let hαL : ((L.f ≫ K.f) ≫ i) ≫ I.f ≫ f = L.f ≫ K.base.f := by
    simp [compositionMiddleCover, Category.assoc]
  let hβL : L.f ≫ K.base.f ≫ g = 𝟙 L.Y ≫ L.base.f := by
    simp [compositionMiddleCover, Category.assoc]
  let hγL : 𝟙 L.Y ≫ L.base.f ≫ r = ((L.f ≫ K.f) ≫ m) ≫ M.f := by
    simpa [compositionMiddleCover, Category.assoc] using
      congrArg (fun q => L.f ≫ q) hOuterβγ
  have hαPull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (α.family I K.base (K.f ≫ i) (𝟙 K.Y) hOuterα)
          L.f ((L.f ≫ K.f) ≫ i) L.f
          (by simp [Category.assoc]) (by simp) =
        α.family I K.base ((L.f ≫ K.f) ≫ i) L.f hαL := by
    simpa [hαL] using
      hαnat I K.base (K.f ≫ i) (𝟙 K.Y) hOuterα
        L.f ((L.f ≫ K.f) ≫ i) L.f
        (by simp [Category.assoc]) (by simp)
  have hβγPull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (βγ.family K.base M (𝟙 K.Y) (K.f ≫ m) hOuterβγ)
          L.f L.f ((L.f ≫ K.f) ≫ m)
          (by simp) (by simp [Category.assoc]) =
        β.family K.base L.base L.f (𝟙 L.Y) hβL ≫
          γ.family L.base M (𝟙 L.Y) ((L.f ≫ K.f) ≫ m) hγL := by
    have hglue := compositionGluedComponent_pullHom_of_fac (J := J)
      β γ hβnat hγnat K.base M (𝟙 K.Y) (K.f ≫ m) hOuterβγ
      (hSheaf K.Y (E.restrictedLocalObject K.base (𝟙 K.Y))
        (KObj.restrictedLocalObject M (K.f ≫ m))) L
      L.f ((L.f ≫ K.f) ≫ m)
      (by simp) (by simp [Category.assoc]) hβL hγL
    simpa [βγ, composeOfFamilyNaturality, composeOfCompatible, compositionFamily,
      localComposite, Category.assoc] using hglue
  unfold localComposite
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp
    (F := canonicalFiberPseudofunctor X.p)
    (α.family I K.base (K.f ≫ i) (𝟙 K.Y) hOuterα)
    (βγ.family K.base M (𝟙 K.Y) (K.f ≫ m) hOuterβγ)
    L.f ((L.f ≫ K.f) ≫ i) L.f ((L.f ≫ K.f) ≫ m)
    (by simp [Category.assoc]) (by simp) (by simp [Category.assoc])]
  rw [hαPull, hβγPull]
  simp [Category.assoc]

/-- Source stage 3.5 common refinement cover for the component associativity comparison.
It is the intersection of the `H`-middle cover used by the left bracketing and the `E`-middle
cover used by the right bracketing. -/
noncomputable def compositionFamilyAssocCommonCover
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z T W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {KObj : DescentCompletionObjectOver (J := J) X T}
    {f : U ⟶ V} {g : V ⟶ Z} {r : Z ⟶ T}
    (I : D.cover.Arrow) (M : KObj.cover.Arrow)
    (i : W ⟶ I.Y) (m : W ⟶ M.Y)
    (h : i ≫ I.f ≫ ((f ≫ g) ≫ r) = m ≫ M.f) :
    J.Cover W :=
  let hLeftBase : i ≫ I.f ≫ (f ≫ g) ≫ r = m ≫ M.f := by
    simpa [Category.assoc] using h
  let hRightBase : i ≫ I.f ≫ f ≫ (g ≫ r) = m ≫ M.f := by
    simpa [Category.assoc] using h
  let SH := compositionMiddleCover (J := J)
    (D := D) (E := H) (H := KObj) (f := f ≫ g) (g := r)
    I M i m hLeftBase
  let SE := compositionMiddleCover (J := J)
    (D := D) (E := E) (H := KObj) (f := f) (g := g ≫ r)
    I M i m hRightBase
  SH ⊓ SE

/-- The left-bracketing `H`-middle cover induced by `compositionFamilyAssocCommonCover`. -/
noncomputable def compositionFamilyAssocCommonCoverToLeft
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z T W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {KObj : DescentCompletionObjectOver (J := J) X T}
    {f : U ⟶ V} {g : V ⟶ Z} {r : Z ⟶ T}
    (I : D.cover.Arrow) (M : KObj.cover.Arrow)
    (i : W ⟶ I.Y) (m : W ⟶ M.Y)
    (h : i ≫ I.f ≫ ((f ≫ g) ≫ r) = m ≫ M.f)
    (Q : (compositionFamilyAssocCommonCover (J := J)
      (D := D) (E := E) (H := H) (KObj := KObj) (f := f) (g := g) (r := r)
      I M i m h).Arrow) :
    (compositionMiddleCover (J := J)
      (D := D) (E := H) (H := KObj) (f := f ≫ g) (g := r)
      I M i m (by simpa [Category.assoc] using h)).Arrow := by
  refine ⟨Q.Y, Q.f, ?_⟩
  exact Q.hf.1

/-- The right-bracketing `E`-middle cover induced by `compositionFamilyAssocCommonCover`. -/
noncomputable def compositionFamilyAssocCommonCoverToRight
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z T W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {KObj : DescentCompletionObjectOver (J := J) X T}
    {f : U ⟶ V} {g : V ⟶ Z} {r : Z ⟶ T}
    (I : D.cover.Arrow) (M : KObj.cover.Arrow)
    (i : W ⟶ I.Y) (m : W ⟶ M.Y)
    (h : i ≫ I.f ≫ ((f ≫ g) ≫ r) = m ≫ M.f)
    (Q : (compositionFamilyAssocCommonCover (J := J)
      (D := D) (E := E) (H := H) (KObj := KObj) (f := f) (g := g) (r := r)
      I M i m h).Arrow) :
    (compositionMiddleCover (J := J)
      (D := D) (E := E) (H := KObj) (f := f) (g := g ≫ r)
      I M i m (by simpa [Category.assoc] using h)).Arrow := by
  refine ⟨Q.Y, Q.f, ?_⟩
  exact Q.hf.2

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Source stage 3.5: associativity of the glued component family.  This is the global
separatedness upgrade of the local calculation on
`U_i ×_V V_j ×_Z Z_k ×_T T_l`: both bracketings restrict to the same triple composite. -/
theorem compositionFamily_assoc
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z T W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {KObj : DescentCompletionObjectOver (J := J) X T}
    {f : U ⟶ V} {g : V ⟶ Z} {r : Z ⟶ T}
    (hSheaf : homPresheavesAreSheaves (J := J) X)
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (γ : HomOver (J := J) H KObj r)
    (hαnat : familyNaturality' (J := J) α)
    (hβnat : familyNaturality' (J := J) β)
    (hγnat : familyNaturality' (J := J) γ)
    (I : D.cover.Arrow) (M : KObj.cover.Arrow)
    (i : W ⟶ I.Y) (m : W ⟶ M.Y)
    (h : i ≫ I.f ≫ ((f ≫ g) ≫ r) = m ≫ M.f) :
    compositionFamily (J := J) hSheaf
        (composeOfFamilyNaturality (J := J) hSheaf α β hαnat hβnat) γ
        (compositionFamily_familyNaturality (J := J) hSheaf α β hαnat hβnat)
        hγnat I M i m h =
      compositionFamily (J := J) hSheaf α
        (composeOfFamilyNaturality (J := J) hSheaf β γ hβnat hγnat)
        hαnat
        (compositionFamily_familyNaturality (J := J) hSheaf β γ hβnat hγnat)
        I M i m (by simpa [Category.assoc] using h) := by
  let αβ : HomOver (J := J) D H (f ≫ g) :=
    composeOfFamilyNaturality (J := J) hSheaf α β hαnat hβnat
  let βγ : HomOver (J := J) E KObj (g ≫ r) :=
    composeOfFamilyNaturality (J := J) hSheaf β γ hβnat hγnat
  let hαβnat : familyNaturality' (J := J) αβ :=
    compositionFamily_familyNaturality (J := J) hSheaf α β hαnat hβnat
  let hβγnat : familyNaturality' (J := J) βγ :=
    compositionFamily_familyNaturality (J := J) hSheaf β γ hβnat hγnat
  let leftComp :=
    compositionFamily (J := J) hSheaf αβ γ hαβnat hγnat I M i m h
  let rightComp :=
    compositionFamily (J := J) hSheaf α βγ hαnat hβγnat I M i m
      (by simpa [Category.assoc] using h)
  let S := compositionFamilyAssocCommonCover (J := J)
    (D := D) (E := E) (H := H) (KObj := KObj) (f := f) (g := g) (r := r)
    I M i m h
  apply fiberHom_ext_of_cover (J := J) X.p S
    (D.restrictedLocalObject I i) (KObj.restrictedLocalObject M m)
    (hSheaf W (D.restrictedLocalObject I i) (KObj.restrictedLocalObject M m))
  intro Q
  let Lh := compositionFamilyAssocCommonCoverToLeft (J := J)
    (D := D) (E := E) (H := H) (KObj := KObj) (f := f) (g := g) (r := r)
    I M i m h Q
  let Ke := compositionFamilyAssocCommonCoverToRight (J := J)
    (D := D) (E := E) (H := H) (KObj := KObj) (f := f) (g := g) (r := r)
    I M i m h Q
  let Kleft : (compositionMiddleCover (J := J)
      (D := D) (E := E) (H := H) (f := f) (g := g)
      I Lh.base (Lh.f ≫ i) (𝟙 Lh.Y)
      (by simp [Lh, compositionFamilyAssocCommonCoverToLeft, compositionMiddleCover,
        Category.assoc])).Arrow :=
    { Y := Q.Y
      f := 𝟙 Q.Y
      hf := by
        simpa [S, Lh, Ke, compositionFamilyAssocCommonCover,
          compositionFamilyAssocCommonCoverToLeft, compositionFamilyAssocCommonCoverToRight,
          compositionMiddleCover, Category.assoc] using Q.hf.2 }
  let Lright : (compositionMiddleCover (J := J)
      (D := E) (E := H) (H := KObj) (f := g) (g := r)
      Ke.base M (𝟙 Ke.Y) (Ke.f ≫ m)
      (by
        simpa [S, Ke, compositionFamilyAssocCommonCoverToRight, compositionMiddleCover,
          Category.assoc] using
          congrArg (fun q => Q.f ≫ q) (by simpa [Category.assoc] using h))).Arrow :=
    { Y := Q.Y
      f := 𝟙 Q.Y
      hf := by
        simpa [S, Lh, Ke, compositionFamilyAssocCommonCover,
          compositionFamilyAssocCommonCoverToLeft, compositionFamilyAssocCommonCoverToRight,
          compositionMiddleCover, Category.assoc] using Q.hf.1 }
  have hKbase : Kleft.base = Ke.base := by
    ext <;>
      simp [Kleft, Ke, S, Lh, compositionFamilyAssocCommonCover,
        compositionFamilyAssocCommonCoverToLeft, compositionFamilyAssocCommonCoverToRight,
        compositionMiddleCover, Category.assoc]
  have hLbase : Lh.base = Lright.base := by
    ext <;>
      simp [Lright, Ke, Lh, S, compositionFamilyAssocCommonCover,
        compositionFamilyAssocCommonCoverToLeft, compositionFamilyAssocCommonCoverToRight,
        compositionMiddleCover, Category.assoc]
  have hleftRaw := compositionFamily_assoc_left_pullHom (J := J) hSheaf
    α β γ hαnat hβnat hγnat I M i m h Lh Kleft
  have hrightRaw := compositionFamily_assoc_right_pullHom (J := J) hSheaf
    α β γ hαnat hβnat hγnat I M i m
      (by simpa [Category.assoc] using h) Ke Lright
  let qi : Q.Y ⟶ I.Y := (𝟙 Q.Y ≫ Q.f) ≫ i
  let qm : Q.Y ⟶ M.Y := (𝟙 Q.Y ≫ Q.f) ≫ m
  let hαL : qi ≫ I.f ≫ f = (𝟙 Q.Y : Q.Y ⟶ Kleft.base.Y) ≫ Kleft.base.f := by
    simp [qi, Kleft, Lh, compositionFamilyAssocCommonCoverToLeft,
      compositionMiddleCover, Category.assoc]
  let hαR : qi ≫ I.f ≫ f = (𝟙 Q.Y : Q.Y ⟶ Ke.base.Y) ≫ Ke.base.f := by
    simp [qi, Ke, compositionFamilyAssocCommonCoverToRight,
      compositionMiddleCover, Category.assoc]
  let hβL :
      (𝟙 Q.Y : Q.Y ⟶ Kleft.base.Y) ≫ Kleft.base.f ≫ g =
        (𝟙 Q.Y : Q.Y ⟶ Lh.base.Y) ≫ Lh.base.f := by
    simp [Kleft, Lh, compositionFamilyAssocCommonCoverToLeft,
      compositionMiddleCover, Category.assoc]
  let hβR :
      (𝟙 Q.Y : Q.Y ⟶ Ke.base.Y) ≫ Ke.base.f ≫ g =
        (𝟙 Q.Y : Q.Y ⟶ Lright.base.Y) ≫ Lright.base.f := by
    simp [Lright, Ke, compositionFamilyAssocCommonCoverToRight,
      compositionMiddleCover, Category.assoc]
  let hγL : (𝟙 Q.Y : Q.Y ⟶ Lh.base.Y) ≫ Lh.base.f ≫ r = qm ≫ M.f := by
    simpa [qm, Lh, compositionFamilyAssocCommonCoverToLeft,
      compositionMiddleCover, Category.assoc] using
      congrArg (fun q => Q.f ≫ q) (by simpa [Category.assoc] using h)
  let hγR : (𝟙 Q.Y : Q.Y ⟶ Lright.base.Y) ≫ Lright.base.f ≫ r = qm ≫ M.f := by
    simpa [qm, Lright, Ke, compositionFamilyAssocCommonCoverToRight,
      compositionMiddleCover, Category.assoc] using
      congrArg (fun q => Q.f ≫ q) (by simpa [Category.assoc] using h)
  let aL := α.family I Kleft.base qi (𝟙 Q.Y) hαL
  let aR := α.family I Ke.base qi (𝟙 Q.Y) hαR
  let bL := β.family Kleft.base Lh.base (𝟙 Q.Y) (𝟙 Q.Y) hβL
  let bR := β.family Ke.base Lright.base (𝟙 Q.Y) (𝟙 Q.Y) hβR
  let cL := γ.family Lh.base M (𝟙 Q.Y) qm hγL
  let cR := γ.family Lright.base M (𝟙 Q.Y) qm hγR
  have hleftPull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          leftComp Q.f qi qm (by simp [qi]) (by simp [qm]) =
        (aL ≫ bL) ≫ cL := by
    simpa [leftComp, αβ, hαβnat, qi, qm, hαL, hβL, hγL, aL, bL, cL, Kleft, Lh,
      compositionFamilyAssocCommonCoverToLeft, compositionFamilyAssocCommonCoverToRight,
      compositionMiddleCover, Category.assoc] using hleftRaw
  have hrightPull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          rightComp Q.f qi qm (by simp [qi]) (by simp [qm]) =
        aR ≫ (bR ≫ cR) := by
    simpa [rightComp, βγ, hβγnat, qi, qm, hαR, hβR, hγR, aR, bR, cR, Lright, Ke,
      compositionFamilyAssocCommonCoverToLeft, compositionFamilyAssocCommonCoverToRight,
      compositionMiddleCover, Category.assoc] using hrightRaw
  have hpull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          leftComp Q.f qi qm (by simp [qi]) (by simp [qm]) =
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          rightComp Q.f qi qm (by simp [qi]) (by simp [qm]) := by
    rw [hleftPull, hrightPull]
    let eK := (E.overlapIso (I₁ := Kleft.base) (I₂ := Ke.base) (𝟙 Q.Y) (𝟙 Q.Y)
      (by
        simp [Kleft, Ke, Lh, compositionFamilyAssocCommonCoverToLeft,
          compositionFamilyAssocCommonCoverToRight, compositionMiddleCover,
          Category.assoc])).hom
    let eL := (H.overlapIso (I₁ := Lh.base) (I₂ := Lright.base) (𝟙 Q.Y) (𝟙 Q.Y)
      (by
        simp [Lright, Ke, Lh, compositionFamilyAssocCommonCoverToLeft,
          compositionFamilyAssocCommonCoverToRight, compositionMiddleCover,
          Category.assoc])).hom
    have hαcompat : aR = aL ≫ eK := by
      have hcompat := α.compatible I I Kleft.base Ke.base qi qi
        (𝟙 Q.Y) (𝟙 Q.Y) rfl
        (by
          simp [Kleft, Ke, Lh, compositionFamilyAssocCommonCoverToLeft,
            compositionFamilyAssocCommonCoverToRight, compositionMiddleCover,
            Category.assoc])
        hαL hαR
      rw [overlapIso_self_hom (J := J) D I qi] at hcompat
      simpa [aL, aR, eK] using hcompat
    have hβcompat : eK ≫ bR = bL ≫ eL := by
      have hcompat := β.compatible Kleft.base Ke.base Lh.base Lright.base
        (𝟙 Q.Y) (𝟙 Q.Y) (𝟙 Q.Y) (𝟙 Q.Y)
        (by
          simp [Kleft, Ke, Lh, compositionFamilyAssocCommonCoverToLeft,
            compositionFamilyAssocCommonCoverToRight, compositionMiddleCover,
            Category.assoc])
        (by
          simp [Lright, Ke, Lh, compositionFamilyAssocCommonCoverToLeft,
            compositionFamilyAssocCommonCoverToRight, compositionMiddleCover,
            Category.assoc])
        hβL hβR
      simpa [bL, bR, eK, eL] using hcompat
    have hγcompat : eL ≫ cR = cL := by
      have hcompat := γ.compatible Lh.base Lright.base M M
        (𝟙 Q.Y) (𝟙 Q.Y) qm qm
        (by
          simp [Lright, Ke, Lh, compositionFamilyAssocCommonCoverToLeft,
            compositionFamilyAssocCommonCoverToRight, compositionMiddleCover,
            Category.assoc])
        rfl hγL hγR
      rw [overlapIso_self_hom (J := J) KObj M qm] at hcompat
      simpa [cL, cR, eL] using hcompat
    calc
      (aL ≫ bL) ≫ cL = (aL ≫ bL) ≫ (eL ≫ cR) := by
        rw [← hγcompat]
      _ = aL ≫ (bL ≫ eL) ≫ cR := by
        simp [Category.assoc]
      _ = aL ≫ (eK ≫ bR) ≫ cR := by
        rw [← hβcompat]
      _ = (aL ≫ eK) ≫ (bR ≫ cR) := by
        simp [Category.assoc]
      _ = aR ≫ (bR ≫ cR) := by
        rw [← hαcompat]
  exact
    Pseudofunctor.LocallyDiscreteOpToCat.map_eq_of_pullHom_eq
      (F := canonicalFiberPseudofunctor X.p)
      Q.f qi qm (by simp [qi]) (by simp [qm]) (by simp [qi]) (by simp [qm]) hpull

set_option backward.isDefEq.respectTransparency false in
/-- Source stage 3.6, right identity on glued components: composing a descent-completion morphism
with the identity morphism on the target glues back to the original component family. -/
theorem compositionFamily_right_id
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {f : U ⟶ V}
    (hSheaf : homPresheavesAreSheaves (J := J) X)
    (α : HomOver (J := J) D E f)
    (hαnat : familyNaturality' (J := J) α)
    {W : C} (I : D.cover.Arrow) (L : E.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ (f ≫ 𝟙 V) = l ≫ L.f) :
    compositionFamily (J := J) hSheaf α (idHomOver (J := J) E)
        hαnat (idHomOver_familyNaturality' (J := J) E) I L i l h =
      α.family I L i l (by simpa [Category.assoc] using h) := by
  let hbase : i ≫ I.f ≫ f = l ≫ L.f := by
    simpa [Category.assoc] using h
  let S := compositionMiddleCover (J := J)
    (D := D) (E := E) (H := E) (f := f) (g := 𝟙 V) I L i l
      (by simpa [Category.assoc] using hbase)
  apply fiberHom_ext_of_cover (J := J) X.p S
    (D.restrictedLocalObject I i) (E.restrictedLocalObject L l)
    (hSheaf W (D.restrictedLocalObject I i) (E.restrictedLocalObject L l))
  intro Kp
  let hsmall : (Kp.f ≫ i) ≫ I.f ≫ f = (Kp.f ≫ l) ≫ L.f := by
    simpa [Category.assoc] using congrArg (fun q => Kp.f ≫ q) hbase
  let hαK : (Kp.f ≫ i) ≫ I.f ≫ f = 𝟙 Kp.Y ≫ Kp.base.f := by
    simp [S, compositionMiddleCover, Category.assoc]
  let hβK : 𝟙 Kp.Y ≫ Kp.base.f ≫ 𝟙 V = (Kp.f ≫ l) ≫ L.f := by
    simpa [S, compositionMiddleCover, Category.assoc] using
      congrArg (fun q => Kp.f ≫ q) (by simpa [Category.assoc] using hbase)
  let localComp :=
    localComposite (J := J) α (idHomOver (J := J) E) I Kp.base L
      (Kp.f ≫ i) (𝟙 Kp.Y) (Kp.f ≫ l) hαK hβK
  have hleftPull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (compositionFamily (J := J) hSheaf α (idHomOver (J := J) E)
            hαnat (idHomOver_familyNaturality' (J := J) E) I L i l h)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl =
        localComp := by
    have hglue := compositionGluedComponent_pullHom_of_fac (J := J)
      α (idHomOver (J := J) E) hαnat (idHomOver_familyNaturality' (J := J) E)
      I L i l (by simpa [Category.assoc] using hbase)
      (hSheaf W (D.restrictedLocalObject I i) (E.restrictedLocalObject L l)) Kp
      (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl hαK hβK
    simpa [compositionFamily, localComp, Category.assoc] using hglue
  have hlocal :
      localComp =
        α.family I L (Kp.f ≫ i) (Kp.f ≫ l) hsmall := by
    have hE : (𝟙 Kp.Y : Kp.Y ⟶ Kp.base.Y) ≫ Kp.base.f =
        (Kp.f ≫ l) ≫ L.f := by
      simpa [S, compositionMiddleCover, Category.assoc] using
        congrArg (fun q => Kp.f ≫ q) hbase
    have hcompat := α.compatible I I Kp.base L
      (Kp.f ≫ i) (Kp.f ≫ i) (𝟙 Kp.Y) (Kp.f ≫ l)
      rfl hE hαK hsmall
    rw [overlapIso_self_hom (J := J) D I (Kp.f ≫ i)] at hcompat
    simp only [Category.id_comp] at hcompat
    simpa [localComp, localComposite, idHomOver_family] using hcompat.symm
  have hrightPull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (α.family I L i l hbase)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl =
        α.family I L (Kp.f ≫ i) (Kp.f ≫ l) hsmall := by
    simpa [hbase, hsmall] using
      hαnat I L i l hbase Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl
  have hpull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (compositionFamily (J := J) hSheaf α (idHomOver (J := J) E)
            hαnat (idHomOver_familyNaturality' (J := J) E) I L i l h)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl =
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (α.family I L i l hbase)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl := by
    rw [hleftPull, hrightPull, hlocal]
  have hmapLeft :=
    Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
      (F := canonicalFiberPseudofunctor X.p)
      (φ := compositionFamily (J := J) hSheaf α (idHomOver (J := J) E)
        hαnat (idHomOver_familyNaturality' (J := J) E) I L i l h)
      Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl
  have hmapRight :=
    Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
      (F := canonicalFiberPseudofunctor X.p)
      (φ := α.family I L i l hbase)
      Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl
  rw [hmapLeft, hmapRight, hpull]

set_option backward.isDefEq.respectTransparency false in
/-- Source stage 3.6, left identity on glued components: composing the identity morphism on the
source with a descent-completion morphism glues back to the original component family. -/
theorem compositionFamily_left_id
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {f : U ⟶ V}
    (hSheaf : homPresheavesAreSheaves (J := J) X)
    (α : HomOver (J := J) D E f)
    (hαnat : familyNaturality' (J := J) α)
    {W : C} (I : D.cover.Arrow) (L : E.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ (𝟙 U ≫ f) = l ≫ L.f) :
    compositionFamily (J := J) hSheaf (idHomOver (J := J) D) α
        (idHomOver_familyNaturality' (J := J) D) hαnat I L i l h =
      α.family I L i l (by simpa [Category.assoc] using h) := by
  let hbase : i ≫ I.f ≫ f = l ≫ L.f := by
    simpa [Category.assoc] using h
  let S := compositionMiddleCover (J := J)
    (D := D) (E := D) (H := E) (f := 𝟙 U) (g := f) I L i l
      (by simpa [Category.assoc] using hbase)
  apply fiberHom_ext_of_cover (J := J) X.p S
    (D.restrictedLocalObject I i) (E.restrictedLocalObject L l)
    (hSheaf W (D.restrictedLocalObject I i) (E.restrictedLocalObject L l))
  intro Kp
  let hsmall : (Kp.f ≫ i) ≫ I.f ≫ f = (Kp.f ≫ l) ≫ L.f := by
    simpa [Category.assoc] using congrArg (fun q => Kp.f ≫ q) hbase
  let hαK : (Kp.f ≫ i) ≫ I.f ≫ 𝟙 U = 𝟙 Kp.Y ≫ Kp.base.f := by
    simp [S, compositionMiddleCover, Category.assoc]
  let hβK : 𝟙 Kp.Y ≫ Kp.base.f ≫ f = (Kp.f ≫ l) ≫ L.f := by
    simpa [S, compositionMiddleCover, Category.assoc] using
      congrArg (fun q => Kp.f ≫ q) hbase
  let localComp :=
    localComposite (J := J) (idHomOver (J := J) D) α I Kp.base L
      (Kp.f ≫ i) (𝟙 Kp.Y) (Kp.f ≫ l) hαK hβK
  have hleftPull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (compositionFamily (J := J) hSheaf (idHomOver (J := J) D) α
            (idHomOver_familyNaturality' (J := J) D) hαnat I L i l h)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl =
        localComp := by
    have hglue := compositionGluedComponent_pullHom_of_fac (J := J)
      (idHomOver (J := J) D) α
      (idHomOver_familyNaturality' (J := J) D) hαnat
      I L i l (by simpa [Category.assoc] using hbase)
      (hSheaf W (D.restrictedLocalObject I i) (E.restrictedLocalObject L l)) Kp
      (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl hαK hβK
    simpa [compositionFamily, localComp, Category.assoc] using hglue
  have hlocal :
      localComp =
        α.family I L (Kp.f ≫ i) (Kp.f ≫ l) hsmall := by
    have hD : (Kp.f ≫ i) ≫ I.f =
        (𝟙 Kp.Y : Kp.Y ⟶ Kp.base.Y) ≫ Kp.base.f := by
      simp [S, compositionMiddleCover, Category.assoc]
    have hcompat := α.compatible I Kp.base L L
      (Kp.f ≫ i) (𝟙 Kp.Y) (Kp.f ≫ l) (Kp.f ≫ l)
      hD rfl hsmall hβK
    rw [overlapIso_self_hom (J := J) E L (Kp.f ≫ l)] at hcompat
    simp only [Category.comp_id] at hcompat
    simpa [localComp, localComposite, idHomOver_family] using hcompat
  have hrightPull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (α.family I L i l hbase)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl =
        α.family I L (Kp.f ≫ i) (Kp.f ≫ l) hsmall := by
    simpa [hbase, hsmall] using
      hαnat I L i l hbase Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl
  have hpull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (compositionFamily (J := J) hSheaf (idHomOver (J := J) D) α
            (idHomOver_familyNaturality' (J := J) D) hαnat I L i l h)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl =
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (α.family I L i l hbase)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl := by
    rw [hleftPull, hrightPull, hlocal]
  have hmapLeft :=
    Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
      (F := canonicalFiberPseudofunctor X.p)
      (φ := compositionFamily (J := J) hSheaf (idHomOver (J := J) D) α
        (idHomOver_familyNaturality' (J := J) D) hαnat I L i l h)
      Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl
  have hmapRight :=
    Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
      (F := canonicalFiberPseudofunctor X.p)
      (φ := α.family I L i l hbase)
      Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl
  rw [hmapLeft, hmapRight, hpull]

/-- Helper for Chap08 Lemma 8 8 1, source stage 3.3: the local composites
`d_ijk = b_jk ∘ a_ij` agree on overlaps of the pulled-back middle cover.  This
is the source proof's matching-family calculation before invoking the sheaf
condition to glue the desired `c_ik`. -/
theorem compositionMiddleCover_relation_compatible
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (α : HomOver (J := J) D E f) (β : HomOver (J := J) E H g)
    (I : D.cover.Arrow) (L : H.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ f ≫ g = l ≫ L.f)
    (R : (compositionMiddleCover (J := J)
      (D := D) (E := E) (H := H) (f := f) (g := g) I L i l h).Relation) :
    localComposite (J := J) α β I R.fst.base L
        (R.r.g₁ ≫ R.fst.f ≫ i) R.r.g₁ (R.r.g₁ ≫ R.fst.f ≫ l)
        (by simp [compositionMiddleCover, Category.assoc])
        (by
          simpa [compositionMiddleCover, Category.assoc] using
            congrArg (fun q => R.r.g₁ ≫ R.fst.f ≫ q) h) =
      localComposite (J := J) α β I R.snd.base L
        (R.r.g₁ ≫ R.fst.f ≫ i) R.r.g₂ (R.r.g₁ ≫ R.fst.f ≫ l)
        (by
          have hw : R.r.g₁ ≫ R.fst.f = R.r.g₂ ≫ R.snd.f := by
            simpa using R.r.w
          simpa [compositionMiddleCover, Category.assoc] using
            congrArg (fun q => q ≫ i ≫ I.f ≫ f) hw)
        (by
          have hw : R.r.g₁ ≫ R.fst.f = R.r.g₂ ≫ R.snd.f := by
            simpa using R.r.w
          calc
            R.r.g₂ ≫ R.snd.base.f ≫ g
                = R.r.g₁ ≫ R.fst.f ≫ i ≫ I.f ≫ f ≫ g := by
                  simpa [compositionMiddleCover, Category.assoc] using
                    congrArg (fun q => q ≫ i ≫ I.f ≫ f ≫ g) hw.symm
            _ = (R.r.g₁ ≫ R.fst.f ≫ l) ≫ L.f := by
                  simpa [Category.assoc] using
                    congrArg (fun q => R.r.g₁ ≫ R.fst.f ≫ q) h) := by
  apply localComposite_middle_compatible (J := J) α β I R.fst.base R.snd.base L
    (R.r.g₁ ≫ R.fst.f ≫ i) R.r.g₁ R.r.g₂ (R.r.g₁ ≫ R.fst.f ≫ l)
  · have hw : R.r.g₁ ≫ R.fst.f = R.r.g₂ ≫ R.snd.f := by
      simpa using R.r.w
    simpa [compositionMiddleCover, Category.assoc] using
      congrArg (fun q => q ≫ i ≫ I.f ≫ f) hw

end HomOver

/-- Owner-level morphisms between descent-completion objects over a fixed base arrow.  Besides the
source-text compatibility square, this bundles the restriction/naturality law needed for using the
double-indexed components as genuine Hom-presheaf sections. -/
structure NaturalHomOver
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V : C}
    (D : DescentCompletionObjectOver (J := J) X U)
    (E : DescentCompletionObjectOver (J := J) X V)
    (f : U ⟶ V) where
  /-- The source-text compatible family `(f, a_ij)`. -/
  toHomOver : HomOver (J := J) D E f
  /-- Restricting a component along a further map gives the corresponding smaller component. -/
  naturality : HomOver.familyNaturality' (J := J) toHomOver

namespace NaturalHomOver

@[simp]
theorem toHomOver_mk
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {f : U ⟶ V}
    (α : HomOver (J := J) D E f)
    (hα : HomOver.familyNaturality' (J := J) α) :
    (NaturalHomOver.mk α hα).toHomOver = α :=
  rfl

/-- Extensionality for natural owner-level morphisms over a fixed base arrow, reduced to the
source-text local component family. -/
theorem ext_family
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {f : U ⟶ V}
    (α β : NaturalHomOver (J := J) D E f)
    (hfamily :
      ∀ {W : C} (I : D.cover.Arrow) (K : E.cover.Arrow)
        (i : W ⟶ I.Y) (k : W ⟶ K.Y)
        (h : i ≫ I.f ≫ f = k ≫ K.f),
          α.toHomOver.family I K i k h = β.toHomOver.family I K i k h) :
    α = β := by
  cases α with
  | mk ahom anat =>
    cases β with
    | mk bhom bnat =>
      dsimp at hfamily
      have hhom : ahom = bhom := HomOver.ext_family (J := J) ahom bhom hfamily
      subst hhom
      congr

/-- Source stage 3.6 identity, now bundled with its restriction/naturality law. -/
noncomputable def id
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U : C}
    (D : DescentCompletionObjectOver (J := J) X U) :
    NaturalHomOver (J := J) D D (𝟙 U) where
  toHomOver := idHomOver (J := J) D
  naturality := HomOver.idHomOver_familyNaturality' (J := J) D

@[simp]
theorem id_toHomOver
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U : C}
    (D : DescentCompletionObjectOver (J := J) X U) :
    (id (J := J) D).toHomOver = idHomOver (J := J) D :=
  rfl

/-- The source stage 3.3-3.4 composite as a bare `HomOver`, obtained by gluing the local
composites.  Its remaining owner-level obligation is restriction/naturality of the glued family. -/
noncomputable def composeCandidate
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (hSheaf : HomOver.homPresheavesAreSheaves (J := J) X)
    (α : NaturalHomOver (J := J) D E f)
    (β : NaturalHomOver (J := J) E H g) :
    HomOver (J := J) D H (f ≫ g) :=
  HomOver.composeOfFamilyNaturality (J := J) hSheaf
    α.toHomOver β.toHomOver α.naturality β.naturality

/-- The exact remaining owner-level condition for turning the glued composite into a bundled
`NaturalHomOver`: gluing must commute with further restriction. -/
def composeNaturalityObligation
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (hSheaf : HomOver.homPresheavesAreSheaves (J := J) X)
    (α : NaturalHomOver (J := J) D E f)
    (β : NaturalHomOver (J := J) E H g) : Prop :=
  HomOver.familyNaturality' (J := J)
    (composeCandidate (J := J) hSheaf α β)

/-- Conditional bundled composite once the remaining restriction/naturality obligation for the
glued family is supplied.  This is the owner-clean target of the source stage 3.3-3.4 construction. -/
noncomputable def composeOfNaturality
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (hSheaf : HomOver.homPresheavesAreSheaves (J := J) X)
    (α : NaturalHomOver (J := J) D E f)
    (β : NaturalHomOver (J := J) E H g)
    (hnat : composeNaturalityObligation (J := J) hSheaf α β) :
    NaturalHomOver (J := J) D H (f ≫ g) where
  toHomOver := composeCandidate (J := J) hSheaf α β
  naturality := hnat

@[simp]
theorem composeOfNaturality_toHomOver
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (hSheaf : HomOver.homPresheavesAreSheaves (J := J) X)
    (α : NaturalHomOver (J := J) D E f)
    (β : NaturalHomOver (J := J) E H g)
    (hnat : composeNaturalityObligation (J := J) hSheaf α β) :
    (composeOfNaturality (J := J) hSheaf α β hnat).toHomOver =
      composeCandidate (J := J) hSheaf α β :=
  rfl

/-- The glued source-stage composite satisfies the owner-level restriction/naturality obligation. -/
theorem composeNaturality
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (hSheaf : HomOver.homPresheavesAreSheaves (J := J) X)
    (α : NaturalHomOver (J := J) D E f)
    (β : NaturalHomOver (J := J) E H g) :
    composeNaturalityObligation (J := J) hSheaf α β := by
  dsimp [composeNaturalityObligation, composeCandidate]
  exact HomOver.compositionFamily_familyNaturality (J := J) hSheaf
    α.toHomOver β.toHomOver α.naturality β.naturality

/-- Source stages 3.3-3.4 as an unconditional bundled composition of natural descent-completion
morphism families. -/
noncomputable def compose
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (hSheaf : HomOver.homPresheavesAreSheaves (J := J) X)
    (α : NaturalHomOver (J := J) D E f)
    (β : NaturalHomOver (J := J) E H g) :
    NaturalHomOver (J := J) D H (f ≫ g) :=
  composeOfNaturality (J := J) hSheaf α β
    (composeNaturality (J := J) hSheaf α β)

@[simp]
theorem compose_toHomOver
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {f : U ⟶ V} {g : V ⟶ Z}
    (hSheaf : HomOver.homPresheavesAreSheaves (J := J) X)
    (α : NaturalHomOver (J := J) D E f)
    (β : NaturalHomOver (J := J) E H g) :
    (compose (J := J) hSheaf α β).toHomOver =
      composeCandidate (J := J) hSheaf α β :=
  rfl

theorem compose_assoc_family
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z T W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {H : DescentCompletionObjectOver (J := J) X Z}
    {KObj : DescentCompletionObjectOver (J := J) X T}
    {f : U ⟶ V} {g : V ⟶ Z} {r : Z ⟶ T}
    (hSheaf : HomOver.homPresheavesAreSheaves (J := J) X)
    (α : NaturalHomOver (J := J) D E f)
    (β : NaturalHomOver (J := J) E H g)
    (γ : NaturalHomOver (J := J) H KObj r)
    (I : D.cover.Arrow) (M : KObj.cover.Arrow)
    (i : W ⟶ I.Y) (m : W ⟶ M.Y)
    (h : i ≫ I.f ≫ ((f ≫ g) ≫ r) = m ≫ M.f) :
    ((compose (J := J) hSheaf (compose (J := J) hSheaf α β) γ).toHomOver).family
        I M i m h =
      ((compose (J := J) hSheaf α (compose (J := J) hSheaf β γ)).toHomOver).family
        I M i m (by simpa [Category.assoc] using h) := by
  dsimp only [compose, composeOfNaturality, composeCandidate]
  rw [HomOver.composeOfFamilyNaturality_family,
    HomOver.composeOfFamilyNaturality_family]
  exact
    HomOver.compositionFamily_assoc (J := J) hSheaf
      α.toHomOver β.toHomOver γ.toHomOver
      α.naturality β.naturality γ.naturality I M i m h

theorem compose_right_id_family
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {f : U ⟶ V}
    (hSheaf : HomOver.homPresheavesAreSheaves (J := J) X)
    (α : NaturalHomOver (J := J) D E f)
    (I : D.cover.Arrow) (L : E.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ (f ≫ 𝟙 V) = l ≫ L.f) :
    ((compose (J := J) hSheaf α (id (J := J) E)).toHomOver).family I L i l h =
      α.toHomOver.family I L i l (by simpa [Category.assoc] using h) := by
  simpa [compose, composeOfNaturality, composeCandidate] using
    HomOver.compositionFamily_right_id (J := J) hSheaf
      α.toHomOver α.naturality I L i l h

theorem compose_left_id_family
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {f : U ⟶ V}
    (hSheaf : HomOver.homPresheavesAreSheaves (J := J) X)
    (α : NaturalHomOver (J := J) D E f)
    (I : D.cover.Arrow) (L : E.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ (𝟙 U ≫ f) = l ≫ L.f) :
    ((compose (J := J) hSheaf (id (J := J) D) α).toHomOver).family I L i l h =
      α.toHomOver.family I L i l (by simpa [Category.assoc] using h) := by
  simpa [compose, composeOfNaturality, composeCandidate] using
    HomOver.compositionFamily_left_id (J := J) hSheaf
      α.toHomOver α.naturality I L i l h

end NaturalHomOver

/-- The trivial descent-completion object associated to an existing fiber object, using the
maximal cover. -/
noncomputable def ofFiberObject
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U : C} (x : X.p.Fiber U) :
    DescentCompletionObjectOver (J := J) X U where
  cover := ⊤
  datum :=
    Pseudofunctor.DescentData.ofObj
      (F := canonicalFiberPseudofunctor X.p)
      (f := fun I : (⊤ : J.Cover U).Arrow => I.f) x

@[simp]
theorem ofFiberObject_cover
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U : C} (x : X.p.Fiber U) :
    (ofFiberObject (J := J) X x).cover = ⊤ :=
  rfl

@[simp]
theorem ofFiberObject_localObject
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U : C} (x : X.p.Fiber U)
    (I : (ofFiberObject (J := J) X x).cover.Arrow) :
    (ofFiberObject (J := J) X x).localObject I =
      ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.obj x :=
  rfl

/-- For the trivial descent datum attached to an old object, restricting first to a cover member
and then to a test object is canonically the same as directly pulling back along the composite
base arrow. -/
noncomputable def ofFiberObjectRestrictedIso
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U W : C} (x : X.p.Fiber U)
    (I : (ofFiberObject (J := J) X x).cover.Arrow) (i : W ⟶ I.Y) :
    (ofFiberObject (J := J) X x).restrictedLocalObject I i ≅
      ((canonicalFiberPseudofunctor X.p).map (i ≫ I.f).op.toLoc).toFunctor.obj x :=
  ((Cat.Hom.toNatIso
      ((canonicalFiberPseudofunctor X.p).mapComp' I.f.op.toLoc i.op.toLoc
        ((i ≫ I.f).op.toLoc) (by rfl))).app x).symm

/-- The canonical total-category arrow from an iterated restriction of a trivial descent datum
back to the original fiber object.  This is the owner-clean version of the source-text
identification `x|_W → x`. -/
noncomputable def ofFiberObjectRestrictedMap
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U W : C} (x : X.p.Fiber U)
    (I : (ofFiberObject (J := J) X x).cover.Arrow) (i : W ⟶ I.Y) :
    ((ofFiberObject (J := J) X x).restrictedLocalObject I i).1 ⟶ x.1 :=
  (ofFiberObjectRestrictedIso (J := J) X x I i).hom.1 ≫
    (canonicalPullbackChoice X.p).map (i ≫ I.f) x

@[reassoc]
theorem ofFiberObjectRestrictedIso_hom_fac
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U W : C} (x : X.p.Fiber U)
    (I : (ofFiberObject (J := J) X x).cover.Arrow) (i : W ⟶ I.Y) :
    (ofFiberObjectRestrictedIso (J := J) X x I i).hom.1 ≫
      (canonicalPullbackChoice X.p).map (i ≫ I.f) x =
        (canonicalPullbackChoice X.p).map i
            (((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.obj x) ≫
          (canonicalPullbackChoice X.p).map I.f x := by
  simpa [ofFiberObjectRestrictedIso, Category.assoc] using
    (FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_inv_app_fac
      X.p I.f i (i ≫ I.f) rfl x)

@[reassoc]
theorem ofFiberObjectRestrictedIso_inv_fac
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U W : C} (x : X.p.Fiber U)
    (I : (ofFiberObject (J := J) X x).cover.Arrow) (i : W ⟶ I.Y) :
    (ofFiberObjectRestrictedIso (J := J) X x I i).inv.1 ≫
        (canonicalPullbackChoice X.p).map i
          (((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.obj x) ≫
        (canonicalPullbackChoice X.p).map I.f x =
      (canonicalPullbackChoice X.p).map (i ≫ I.f) x := by
  simpa [ofFiberObjectRestrictedIso, Category.assoc] using
    (FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
      X.p I.f i (i ≫ I.f) rfl x)

theorem ofFiberObjectRestrictedMap_eq
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U W : C} (x : X.p.Fiber U)
    (I : (ofFiberObject (J := J) X x).cover.Arrow) (i : W ⟶ I.Y) :
    ofFiberObjectRestrictedMap (J := J) X x I i =
      (canonicalPullbackChoice X.p).map i
          (((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.obj x) ≫
        (canonicalPullbackChoice X.p).map I.f x := by
  exact ofFiberObjectRestrictedIso_hom_fac (J := J) X x I i

/-- The canonical map from a trivial restricted local object back to the original object is
strongly cartesian over the composite base arrow. -/
theorem ofFiberObjectRestrictedMap_isStronglyCartesian
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U W : C} (x : X.p.Fiber U)
    (I : (ofFiberObject (J := J) X x).cover.Arrow) (i : W ⟶ I.Y) :
    X.p.IsStronglyCartesian (i ≫ I.f)
      (ofFiberObjectRestrictedMap (J := J) X x I i) := by
  dsimp [ofFiberObjectRestrictedMap]
  let eIso := ofFiberObjectRestrictedIso (J := J) X x I i
  let eTotal : ((ofFiberObject (J := J) X x).restrictedLocalObject I i).1 ≅
      (((canonicalFiberPseudofunctor X.p).map (i ≫ I.f).op.toLoc).toFunctor.obj x).1 :=
    { hom := eIso.hom.1
      inv := eIso.inv.1
      hom_inv_id := by
        exact congrArg Subtype.val eIso.hom_inv_id
      inv_hom_id := by
        exact congrArg Subtype.val eIso.inv_hom_id }
  haveI : IsIso (ofFiberObjectRestrictedIso (J := J) X x I i).hom.1 := by
    simpa [eIso, eTotal] using eTotal.isIso_hom
  have hfirst :
      X.p.IsHomLift (𝟙 W)
        (ofFiberObjectRestrictedIso (J := J) X x I i).hom.1 :=
    (ofFiberObjectRestrictedIso (J := J) X x I i).hom.2
  letI : X.p.IsHomLift (𝟙 W)
        (ofFiberObjectRestrictedIso (J := J) X x I i).hom.1 := hfirst
  have hfirstCart :
      X.p.IsStronglyCartesian (𝟙 W)
        (ofFiberObjectRestrictedIso (J := J) X x I i).hom.1 := by
    exact Functor.IsStronglyCartesian.of_isIso X.p (𝟙 W)
      (ofFiberObjectRestrictedIso (J := J) X x I i).hom.1
  letI : X.p.IsStronglyCartesian (𝟙 W)
        (ofFiberObjectRestrictedIso (J := J) X x I i).hom.1 := hfirstCart
  let hc := canonicalPullbackChoice X.p
  let q : W ⟶ U := i ≫ I.f
  have hsecondCart : X.p.IsStronglyCartesian q (hc.map q x) :=
    hc.isStronglyCartesian q x
  haveI : X.p.IsStronglyCartesian q (hc.map q x) := hsecondCart
  have hcomp :
      X.p.IsStronglyCartesian ((𝟙 W) ≫ q)
        ((ofFiberObjectRestrictedIso (J := J) X x I i).hom.1 ≫
          hc.map q x) := by
    exact
      @Functor.IsStronglyCartesian.comp _ _ _ _ X.p W W U
        ((ofFiberObject (J := J) X x).restrictedLocalObject I i).1
        (((canonicalFiberPseudofunctor X.p).map q.op.toLoc).toFunctor.obj x).1
        x.1
        (𝟙 W) q
        (ofFiberObjectRestrictedIso (J := J) X x I i).hom.1
        (hc.map q x)
        hfirstCart hsecondCart
  simpa [q, Category.assoc] using hcomp

/-- The trivial descent transition preserves the canonical projection back to the original
object.  This is the source-faithful replacement for identifying two pullback owners by
definition. -/
@[reassoc]
theorem ofFiberObjectRestrictedMap_overlap
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U W : C} (x : X.p.Fiber U)
    {I₁ I₂ : (ofFiberObject (J := J) X x).cover.Arrow}
    (i₁ : W ⟶ I₁.Y) (i₂ : W ⟶ I₂.Y)
    (hD : i₁ ≫ I₁.f = i₂ ≫ I₂.f) :
    ((ofFiberObject (J := J) X x).overlapIso i₁ i₂ hD).hom.1 ≫
      ofFiberObjectRestrictedMap (J := J) X x I₂ i₂ =
        ofFiberObjectRestrictedMap (J := J) X x I₁ i₁ := by
  rw [ofFiberObjectRestrictedMap_eq (J := J) X x I₂ i₂,
    ofFiberObjectRestrictedMap_eq (J := J) X x I₁ i₁]
  dsimp [overlapIso, transitionIso, ofFiberObject, Pseudofunctor.DescentData.ofObj]
  let F := canonicalFiberPseudofunctor X.p
  let hc := canonicalPullbackChoice X.p
  let qloc := I₁.f.op.toLoc ≫ i₁.op.toLoc
  let α :=
    ((F.mapComp' I₁.f.op.toLoc i₁.op.toLoc qloc (by rfl)).inv.toNatTrans.app x)
  let β :=
    ((F.mapComp' I₂.f.op.toLoc i₂.op.toLoc qloc
      (by
        simpa [qloc, ← Quiver.Hom.comp_toLoc, ← op_comp] using
          congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op hD.symm))).hom.toNatTrans.app x)
  change (α.1 ≫ β.1) ≫ hc.map i₂
        (((canonicalFiberPseudofunctor X.p).map I₂.f.op.toLoc).toFunctor.obj x) ≫
      hc.map I₂.f x =
    hc.map i₁ (((canonicalFiberPseudofunctor X.p).map I₁.f.op.toLoc).toFunctor.obj x) ≫
      hc.map I₁.f x
  have hβ :
      β.1 ≫ hc.map i₂
          (((canonicalFiberPseudofunctor X.p).map I₂.f.op.toLoc).toFunctor.obj x) ≫
        hc.map I₂.f x =
      hc.map (i₁ ≫ I₁.f) x := by
    simpa [β, F, hc, qloc, Category.assoc, ← Quiver.Hom.comp_toLoc, ← op_comp] using
      (FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
        X.p I₂.f i₂ (i₁ ≫ I₁.f) hD.symm x)
  have hα :
      α.1 ≫ hc.map (i₁ ≫ I₁.f) x =
        hc.map i₁ (((canonicalFiberPseudofunctor X.p).map I₁.f.op.toLoc).toFunctor.obj x) ≫
          hc.map I₁.f x := by
    simpa [α, F, hc, qloc, Category.assoc, ← Quiver.Hom.comp_toLoc, ← op_comp] using
      (FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_inv_app_fac
        X.p I₁.f i₁ (i₁ ≫ I₁.f) rfl x)
  calc
    (α.1 ≫ β.1) ≫ hc.map i₂
          (((canonicalFiberPseudofunctor X.p).map I₂.f.op.toLoc).toFunctor.obj x) ≫
        hc.map I₂.f x
        = α.1 ≫
            (β.1 ≫ hc.map i₂
              (((canonicalFiberPseudofunctor X.p).map I₂.f.op.toLoc).toFunctor.obj x) ≫
              hc.map I₂.f x) := by
          simp [Category.assoc]
    _ = α.1 ≫ hc.map (i₁ ≫ I₁.f) x := by
          rw [hβ]
    _ = hc.map i₁ (((canonicalFiberPseudofunctor X.p).map I₁.f.op.toLoc).toFunctor.obj x) ≫
          hc.map I₁.f x := hα

/-- The singleton-cover component induced by an original total morphism `f : x ⟶ y`.
The outer `mapComp'` isomorphisms are the owner bridge between the source-text component on the
composite base arrow and the iterated pullback owner used by `HomOver.family`. -/
noncomputable def ofFiberHomComponent
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V W : C}
    (x : X.p.Fiber U) (y : X.p.Fiber V) {b : U ⟶ V}
    (f : x.1 ⟶ y.1) [X.p.IsHomLift b f]
    (I : (ofFiberObject (J := J) X x).cover.Arrow)
    (K : (ofFiberObject (J := J) X y).cover.Arrow)
    (i : W ⟶ I.Y) (k : W ⟶ K.Y)
    (h : i ≫ I.f ≫ b = k ≫ K.f) :
    (ofFiberObject (J := J) X x).restrictedLocalObject I i ⟶
      (ofFiberObject (J := J) X y).restrictedLocalObject K k :=
  (ofFiberObjectRestrictedIso (J := J) X x I i).hom ≫
    restrictedHomOfTotalHom x y f (i ≫ I.f) (k ≫ K.f)
      (by simpa [Category.assoc] using h) ≫
      (ofFiberObjectRestrictedIso (J := J) X y K k).inv

@[reassoc]
theorem ofFiberHomComponent_fac
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V W : C}
    (x : X.p.Fiber U) (y : X.p.Fiber V) {b : U ⟶ V}
    (f : x.1 ⟶ y.1) [X.p.IsHomLift b f]
    (I : (ofFiberObject (J := J) X x).cover.Arrow)
    (K : (ofFiberObject (J := J) X y).cover.Arrow)
    (i : W ⟶ I.Y) (k : W ⟶ K.Y)
    (h : i ≫ I.f ≫ b = k ≫ K.f) :
    (ofFiberHomComponent (J := J) x y f I K i k h).1 ≫
      ofFiberObjectRestrictedMap (J := J) X y K k =
        ofFiberObjectRestrictedMap (J := J) X x I i ≫ f := by
  dsimp [ofFiberHomComponent, ofFiberObjectRestrictedMap]
  let ex := ofFiberObjectRestrictedIso (J := J) X x I i
  let ey := ofFiberObjectRestrictedIso (J := J) X y K k
  let r :=
    restrictedHomOfTotalHom x y f (i ≫ I.f) (k ≫ K.f)
      (by simpa [Category.assoc] using h)
  let hc := canonicalPullbackChoice X.p
  change (ex.hom ≫ r ≫ ey.inv).1 ≫ ey.hom.1 ≫ hc.map (k ≫ K.f) y =
    (ex.hom.1 ≫ hc.map (i ≫ I.f) x) ≫ f
  have hcancel : ey.inv.1 ≫ ey.hom.1 = 𝟙 _ := by
    exact congrArg Subtype.val ey.inv_hom_id
  have hfac :
      r.1 ≫ hc.map (k ≫ K.f) y =
        hc.map (i ≫ I.f) x ≫ f := by
    simpa [r, hc] using
      (restrictedHomOfTotalHom_fac x y f (i ≫ I.f) (k ≫ K.f)
        (by simpa [Category.assoc] using h))
  calc
    (ex.hom ≫ r ≫ ey.inv).1 ≫ ey.hom.1 ≫ hc.map (k ≫ K.f) y
        = (ex.hom.1 ≫ r.1 ≫ ey.inv.1) ≫ ey.hom.1 ≫ hc.map (k ≫ K.f) y := by
          rfl
    _ = ex.hom.1 ≫ r.1 ≫ (ey.inv.1 ≫ ey.hom.1) ≫ hc.map (k ≫ K.f) y := by
          simp [Category.assoc]
    _ = ex.hom.1 ≫ r.1 ≫ hc.map (k ≫ K.f) y := by
          rw [hcancel]
          simp
    _ = ex.hom.1 ≫ (hc.map (i ≫ I.f) x ≫ f) := by
          simpa [Category.assoc] using congrArg (fun t => ex.hom.1 ≫ t) hfac
    _ = (ex.hom.1 ≫ hc.map (i ≫ I.f) x) ≫ f := by
          rw [Category.assoc]

@[reassoc]
theorem ofFiberHomComponent_pullHom_fac
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V W W' : C}
    (x : X.p.Fiber U) (y : X.p.Fiber V) {b : U ⟶ V}
    (f : x.1 ⟶ y.1) [X.p.IsHomLift b f]
    (I : (ofFiberObject (J := J) X x).cover.Arrow)
    (K : (ofFiberObject (J := J) X y).cover.Arrow)
    (i : W ⟶ I.Y) (k : W ⟶ K.Y)
    (h : i ≫ I.f ≫ b = k ≫ K.f)
    (m : W' ⟶ W) (mi : W' ⟶ I.Y) (mk : W' ⟶ K.Y)
    (hmi : m ≫ i = mi) (hmk : m ≫ k = mk) :
    (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := canonicalFiberPseudofunctor X.p)
      (ofFiberHomComponent (J := J) x y f I K i k h)
      m mi mk hmi hmk).1 ≫
      ofFiberObjectRestrictedMap (J := J) X y K mk =
        ofFiberObjectRestrictedMap (J := J) X x I mi ≫ f := by
  let F := canonicalFiberPseudofunctor X.p
  let hc := canonicalPullbackChoice X.p
  let ex := ofFiberObjectRestrictedIso (J := J) X x I i
  let ey := ofFiberObjectRestrictedIso (J := J) X y K k
  let r :=
    restrictedHomOfTotalHom x y f (i ≫ I.f) (k ≫ K.f)
      (by simpa [Category.assoc] using h)
  change (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := canonicalFiberPseudofunctor X.p) (ex.hom ≫ r ≫ ey.inv)
      m mi mk hmi hmk).1 ≫
      ofFiberObjectRestrictedMap (J := J) X y K mk =
        ofFiberObjectRestrictedMap (J := J) X x I mi ≫ f
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp₃
    (F := canonicalFiberPseudofunctor X.p)
    (φ := ex.hom) (ψ := r) (χ := ey.inv)
    (k := m) (kf₁ := mi) (kf₂ := mi ≫ I.f) (kf₃ := mk ≫ K.f) (kf₄ := mk)
    (hkf₁ := hmi)
    (hkf₂ := by simpa [Category.assoc] using congrArg (fun q => q ≫ I.f) hmi)
    (hkf₃ := by simpa [Category.assoc] using congrArg (fun q => q ≫ K.f) hmk)
    (hkf₄ := hmk)]
  let pex := Pseudofunctor.LocallyDiscreteOpToCat.pullHom
    (F := canonicalFiberPseudofunctor X.p) ex.hom m mi (mi ≫ I.f) hmi
      (by simpa [Category.assoc] using congrArg (fun q => q ≫ I.f) hmi)
  let pr := Pseudofunctor.LocallyDiscreteOpToCat.pullHom
    (F := canonicalFiberPseudofunctor X.p) r m (mi ≫ I.f) (mk ≫ K.f)
      (by simpa [Category.assoc] using congrArg (fun q => q ≫ I.f) hmi)
      (by simpa [Category.assoc] using congrArg (fun q => q ≫ K.f) hmk)
  let pey := Pseudofunctor.LocallyDiscreteOpToCat.pullHom
    (F := canonicalFiberPseudofunctor X.p) ey.inv m (mk ≫ K.f) mk
      (by simpa [Category.assoc] using congrArg (fun q => q ≫ K.f) hmk) hmk
  change (pex.1 ≫ pr.1 ≫ pey.1) ≫ ofFiberObjectRestrictedMap (J := J) X y K mk =
    ofFiberObjectRestrictedMap (J := J) X x I mi ≫ f
  have hpex : pex = (ofFiberObjectRestrictedIso (J := J) X x I mi).hom := by
    simpa [pex, ex, ofFiberObjectRestrictedIso, F] using
      (Pseudofunctor.LocallyDiscreteOpToCat.pullHom_mapComp'_inv_of_fac
        (F := F) I.f i m mi hmi x)
  have hpey : pey = (ofFiberObjectRestrictedIso (J := J) X y K mk).inv := by
    simpa [pey, ey, ofFiberObjectRestrictedIso, F] using
      (Pseudofunctor.LocallyDiscreteOpToCat.pullHom_mapComp'_hom_of_fac
        (F := F) K.f k m mk hmk y)
  have hpr : pr.1 ≫ hc.map (mk ≫ K.f) y = hc.map (mi ≫ I.f) x ≫ f := by
    simpa [pr, r, hc] using
      (restrictedHomOfTotalHom_pullHom_fac x y f
        (i ≫ I.f) (k ≫ K.f) (by simpa [Category.assoc] using h)
        m (mi ≫ I.f) (mk ≫ K.f)
        (by simpa [Category.assoc] using congrArg (fun q => q ≫ I.f) hmi)
        (by simpa [Category.assoc] using congrArg (fun q => q ≫ K.f) hmk))
  rw [hpex, hpey]
  let ex' := ofFiberObjectRestrictedIso (J := J) X x I mi
  let ey' := ofFiberObjectRestrictedIso (J := J) X y K mk
  change (ex'.hom.1 ≫ pr.1 ≫ ey'.inv.1) ≫ ey'.hom.1 ≫
      hc.map (mk ≫ K.f) y =
    (ex'.hom.1 ≫ hc.map (mi ≫ I.f) x) ≫ f
  have hcancel : ey'.inv.1 ≫ ey'.hom.1 = 𝟙 _ := by
    exact congrArg Subtype.val ey'.inv_hom_id
  calc
    (ex'.hom.1 ≫ pr.1 ≫ ey'.inv.1) ≫ ey'.hom.1 ≫ hc.map (mk ≫ K.f) y
        = ex'.hom.1 ≫ pr.1 ≫ (ey'.inv.1 ≫ ey'.hom.1) ≫
            hc.map (mk ≫ K.f) y := by
          simp [Category.assoc]
    _ = ex'.hom.1 ≫ pr.1 ≫ hc.map (mk ≫ K.f) y := by
          rw [hcancel]
          simp
    _ = ex'.hom.1 ≫ (hc.map (mi ≫ I.f) x ≫ f) := by
          simpa [Category.assoc] using congrArg (fun t => ex'.hom.1 ≫ t) hpr
    _ = (ex'.hom.1 ≫ hc.map (mi ≫ I.f) x) ≫ f := by
          rw [Category.assoc]

namespace HomOver

/-- The owner-level `HomOver` induced by an original total morphism.  This is the singleton-cover
part of the source construction of `G : S ⟶ S'`. -/
noncomputable def ofFiberHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V : C}
    (x : X.p.Fiber U) (y : X.p.Fiber V) {b : U ⟶ V}
    (f : x.1 ⟶ y.1) [X.p.IsHomLift b f] :
    HomOver (J := J) (ofFiberObject (J := J) X x) (ofFiberObject (J := J) X y) b where
  family I K i k h := ofFiberHomComponent (J := J) x y f I K i k h
  compatible := by
    intro W I₁ I₂ K₁ K₂ i₁ i₂ k₁ k₂ hD hE h₁ h₂
    let leftFiber :=
      ((ofFiberObject (J := J) X x).overlapIso i₁ i₂ hD).hom ≫
        ofFiberHomComponent (J := J) x y f I₂ K₂ i₂ k₂ h₂
    let rightFiber :=
      ofFiberHomComponent (J := J) x y f I₁ K₁ i₁ k₁ h₁ ≫
        ((ofFiberObject (J := J) X y).overlapIso k₁ k₂ hE).hom
    change leftFiber = rightFiber
    apply Functor.Fiber.hom_ext
    change leftFiber.1 = rightFiber.1
    let τ := ofFiberObjectRestrictedMap (J := J) X y K₂ k₂
    have hτ : X.p.IsStronglyCartesian (k₂ ≫ K₂.f) τ :=
      ofFiberObjectRestrictedMap_isStronglyCartesian (J := J) X y K₂ k₂
    letI : X.p.IsStronglyCartesian (k₂ ≫ K₂.f) τ := hτ
    haveI : X.p.IsHomLift (𝟙 W) leftFiber.1 := leftFiber.2
    haveI : X.p.IsHomLift (𝟙 W) rightFiber.1 := rightFiber.2
    apply Functor.IsStronglyCartesian.ext X.p (k₂ ≫ K₂.f) τ (𝟙 W)
    calc
      leftFiber.1 ≫ τ
          = (((ofFiberObject (J := J) X x).overlapIso i₁ i₂ hD).hom.1 ≫
              (ofFiberHomComponent (J := J) x y f I₂ K₂ i₂ k₂ h₂).1) ≫ τ := by
            rfl
      _ = ((ofFiberObject (J := J) X x).overlapIso i₁ i₂ hD).hom.1 ≫
            ((ofFiberHomComponent (J := J) x y f I₂ K₂ i₂ k₂ h₂).1 ≫ τ) := by
            rw [Category.assoc]
      _ = ((ofFiberObject (J := J) X x).overlapIso i₁ i₂ hD).hom.1 ≫
            (ofFiberObjectRestrictedMap (J := J) X x I₂ i₂ ≫ f) := by
            rw [ofFiberHomComponent_fac (J := J) x y f I₂ K₂ i₂ k₂ h₂]
      _ = (ofFiberObjectRestrictedMap (J := J) X x I₁ i₁) ≫ f := by
            rw [← Category.assoc,
              ofFiberObjectRestrictedMap_overlap (J := J) X x i₁ i₂ hD]
      _ = (ofFiberHomComponent (J := J) x y f I₁ K₁ i₁ k₁ h₁).1 ≫
            ofFiberObjectRestrictedMap (J := J) X y K₁ k₁ := by
            rw [ofFiberHomComponent_fac (J := J) x y f I₁ K₁ i₁ k₁ h₁]
      _ = (ofFiberHomComponent (J := J) x y f I₁ K₁ i₁ k₁ h₁).1 ≫
            ((ofFiberObject (J := J) X y).overlapIso k₁ k₂ hE).hom.1 ≫ τ := by
            rw [ofFiberObjectRestrictedMap_overlap (J := J) X y k₁ k₂ hE]
      _ = ((ofFiberHomComponent (J := J) x y f I₁ K₁ i₁ k₁ h₁).1 ≫
            ((ofFiberObject (J := J) X y).overlapIso k₁ k₂ hE).hom.1) ≫ τ := by
            rw [Category.assoc]
      _ = rightFiber.1 ≫ τ := by
            rfl

theorem ofFiberHom_familyNaturality'
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V : C}
    (x : X.p.Fiber U) (y : X.p.Fiber V) {b : U ⟶ V}
    (f : x.1 ⟶ y.1) [X.p.IsHomLift b f] :
    familyNaturality' (J := J) (ofFiberHom (J := J) x y (b := b) f) := by
  intro W W' I K i k h m mi mk hmi hmk
  let hsmall : mi ≫ I.f ≫ b = mk ≫ K.f := by
    calc
      mi ≫ I.f ≫ b = m ≫ i ≫ I.f ≫ b := by
        rw [← hmi]
        simp [Category.assoc]
      _ = m ≫ k ≫ K.f := by
        simpa [Category.assoc] using congrArg (fun q => m ≫ q) h
      _ = mk ≫ K.f := by
        simpa [Category.assoc] using congrArg (fun q => q ≫ K.f) hmk
  change
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (ofFiberHomComponent (J := J) x y f I K i k h) m mi mk hmi hmk =
      ofFiberHomComponent (J := J) x y f I K mi mk hsmall
  apply Functor.Fiber.hom_ext
  change
    (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (ofFiberHomComponent (J := J) x y f I K i k h) m mi mk hmi hmk).1 =
      (ofFiberHomComponent (J := J) x y f I K mi mk hsmall).1
  let τ := ofFiberObjectRestrictedMap (J := J) X y K mk
  have hτ : X.p.IsStronglyCartesian (mk ≫ K.f) τ :=
    ofFiberObjectRestrictedMap_isStronglyCartesian (J := J) X y K mk
  letI : X.p.IsStronglyCartesian (mk ≫ K.f) τ := hτ
  haveI : X.p.IsHomLift (𝟙 W')
      (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (ofFiberHomComponent (J := J) x y f I K i k h) m mi mk hmi hmk).1 :=
    (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := canonicalFiberPseudofunctor X.p)
      (ofFiberHomComponent (J := J) x y f I K i k h) m mi mk hmi hmk).2
  haveI : X.p.IsHomLift (𝟙 W')
      (ofFiberHomComponent (J := J) x y f I K mi mk hsmall).1 :=
    (ofFiberHomComponent (J := J) x y f I K mi mk hsmall).2
  apply Functor.IsStronglyCartesian.ext X.p (mk ≫ K.f) τ (𝟙 W')
  calc
    (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (ofFiberHomComponent (J := J) x y f I K i k h) m mi mk hmi hmk).1 ≫ τ
        = ofFiberObjectRestrictedMap (J := J) X x I mi ≫ f := by
          exact ofFiberHomComponent_pullHom_fac (J := J) x y f I K i k h m mi mk hmi hmk
    _ = (ofFiberHomComponent (J := J) x y f I K mi mk hsmall).1 ≫ τ := by
          exact (ofFiberHomComponent_fac (J := J) x y f I K mi mk hsmall).symm

theorem ofFiberHom_id
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U : C}
    (x : X.p.Fiber U) :
    letI : X.p.IsHomLift (𝟙 U) (𝟙 x.1) := CategoryTheory.IsHomLift.id x.2
    ofFiberHom (J := J) x x (b := 𝟙 U) (𝟙 x.1) =
      idHomOver (J := J) (ofFiberObject (J := J) X x) := by
  letI : X.p.IsHomLift (𝟙 U) (𝟙 x.1) := CategoryTheory.IsHomLift.id x.2
  apply ext_family
  intro W I K i k h
  apply Functor.Fiber.hom_ext
  change (ofFiberHomComponent (J := J) x x (𝟙 x.1) I K i k h).1 =
    ((ofFiberObject (J := J) X x).overlapIso i k
      (by simpa [Category.assoc] using h)).hom.1
  let τ := ofFiberObjectRestrictedMap (J := J) X x K k
  have hτ : X.p.IsStronglyCartesian (k ≫ K.f) τ :=
    ofFiberObjectRestrictedMap_isStronglyCartesian (J := J) X x K k
  letI : X.p.IsStronglyCartesian (k ≫ K.f) τ := hτ
  haveI : X.p.IsHomLift (𝟙 W)
      (ofFiberHomComponent (J := J) x x (𝟙 x.1) I K i k h).1 :=
    (ofFiberHomComponent (J := J) x x (𝟙 x.1) I K i k h).2
  haveI : X.p.IsHomLift (𝟙 W)
      ((ofFiberObject (J := J) X x).overlapIso i k
        (by simpa [Category.assoc] using h)).hom.1 :=
    ((ofFiberObject (J := J) X x).overlapIso i k
      (by simpa [Category.assoc] using h)).hom.2
  apply Functor.IsStronglyCartesian.ext X.p (k ≫ K.f) τ (𝟙 W)
  calc
    (ofFiberHomComponent (J := J) x x (𝟙 x.1) I K i k h).1 ≫ τ
        = ofFiberObjectRestrictedMap (J := J) X x I i ≫ 𝟙 x.1 := by
          exact ofFiberHomComponent_fac (J := J) x x (𝟙 x.1) I K i k h
    _ = ofFiberObjectRestrictedMap (J := J) X x I i := by simp
    _ = ((ofFiberObject (J := J) X x).overlapIso i k
          (by simpa [Category.assoc] using h)).hom.1 ≫ τ := by
          exact
            (ofFiberObjectRestrictedMap_overlap (J := J) X x i k
              (by simpa [Category.assoc] using h)).symm

end HomOver

namespace NaturalHomOver

/-- The singleton-cover morphism induced by an original total morphism, bundled with the
restriction/naturality law.  This is the morphism-level part of the source construction
`G : S ⟶ S'` on old objects. -/
noncomputable def ofFiberHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V : C}
    (x : X.p.Fiber U) (y : X.p.Fiber V) {b : U ⟶ V}
    (f : x.1 ⟶ y.1) [X.p.IsHomLift b f] :
    NaturalHomOver (J := J)
      (ofFiberObject (J := J) X x) (ofFiberObject (J := J) X y) b where
  toHomOver := HomOver.ofFiberHom (J := J) x y (b := b) f
  naturality := HomOver.ofFiberHom_familyNaturality' (J := J) x y (b := b) f

@[simp]
theorem ofFiberHom_toHomOver
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V : C}
    (x : X.p.Fiber U) (y : X.p.Fiber V) {b : U ⟶ V}
    (f : x.1 ⟶ y.1) [X.p.IsHomLift b f] :
    (ofFiberHom (J := J) x y (b := b) f).toHomOver =
      HomOver.ofFiberHom (J := J) x y (b := b) f :=
  rfl

theorem ofFiberHom_id
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U : C}
    (x : X.p.Fiber U) :
    letI : X.p.IsHomLift (𝟙 U) (𝟙 x.1) := CategoryTheory.IsHomLift.id x.2
    ofFiberHom (J := J) x x (b := 𝟙 U) (𝟙 x.1) =
      id (J := J) (ofFiberObject (J := J) X x) := by
  letI : X.p.IsHomLift (𝟙 U) (𝟙 x.1) := CategoryTheory.IsHomLift.id x.2
  apply ext_family
  intro W I K i k h
  change
    (HomOver.ofFiberHom (J := J) x x (b := 𝟙 U) (𝟙 x.1)).family I K i k h =
      (idHomOver (J := J) (ofFiberObject (J := J) X x)).family I K i k
        (by simpa using h)
  simpa using
    congrArg
      (fun α : HomOver (J := J)
          (ofFiberObject (J := J) X x) (ofFiberObject (J := J) X x) (𝟙 U) =>
        α.family I K i k h)
      (HomOver.ofFiberHom_id (J := J) x)

end NaturalHomOver

end DescentCompletionObjectOver

namespace DescentCompletionObject

/-- The projection of a descent-completion object to the base site. -/
@[simp]
def projection
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (x : DescentCompletionObject (J := J) X) : C :=
  x.base

/-- The total trivial object associated to an existing fiber object. -/
noncomputable def ofFiberObject
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U : C} (x : X.p.Fiber U) :
    DescentCompletionObject (J := J) X where
  base := U
  object := DescentCompletionObjectOver.ofFiberObject (J := J) X x

@[simp]
theorem ofFiberObject_base
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U : C} (x : X.p.Fiber U) :
    (ofFiberObject (J := J) X x).base = U :=
  rfl

/-- Helper for Chap08 Lemma 8 8 1, source stage 3.2: a total morphism of descent-completion
objects, consisting of the base arrow and the compatible double-indexed local morphisms over it.
This is the source's pair `(f, a_{ij})`. -/
structure Hom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D E : DescentCompletionObject (J := J) X) where
  /-- The projected base arrow. -/
  base : D.base ⟶ E.base
  /-- The compatible local components over `base`, bundled with their restriction/naturality law. -/
  components :
    DescentCompletionObjectOver.NaturalHomOver (J := J)
      D.object E.object base

/-- Extensionality for total descent-completion morphisms.  The base arrows may be propositionally
equal; after transporting along that equality, it is enough to compare the source-text local
component family. -/
theorem Hom.ext_base_family
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {D E : DescentCompletionObject (J := J) X}
    (α β : Hom (J := J) D E)
    (hbase : α.base = β.base)
    (hfamily :
      ∀ {W : C} (I : D.object.cover.Arrow) (K : E.object.cover.Arrow)
        (i : W ⟶ I.Y) (k : W ⟶ K.Y)
        (h : i ≫ I.f ≫ α.base = k ≫ K.f),
          α.components.toHomOver.family I K i k h =
            β.components.toHomOver.family I K i k (by simpa [hbase] using h)) :
    α = β := by
  cases α with
  | mk abase acomp =>
    cases β with
    | mk bbase bcomp =>
      dsimp at hbase hfamily
      subst bbase
      have hcomp : acomp = bcomp :=
        DescentCompletionObjectOver.NaturalHomOver.ext_family (J := J) acomp bcomp (by
          intro W I K i k h
          simpa using hfamily I K i k h)
      subst hcomp
      rfl

/-- Helper for Chap08 Lemma 8 8 1, source stage 3.6: the total identity morphism
`(id_U, φ_{ii'})`. -/
noncomputable def identity
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X) :
    Hom (J := J) D D where
  base := 𝟙 D.base
  components := DescentCompletionObjectOver.NaturalHomOver.id (J := J) D.object

@[simp]
theorem identity_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X) :
    (identity (J := J) D).base = 𝟙 D.base :=
  rfl

/-- The projection of a descent-completion morphism to the base site. -/
@[simp]
def Hom.projection
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {D E : DescentCompletionObject (J := J) X}
    (a : Hom (J := J) D E) :
    D.base ⟶ E.base :=
  a.base

namespace Hom

/-- The total descent-completion morphism induced by an original total morphism between old
fiber objects.  This is the source construction's morphism part of the embedding of old objects
into the descent-data completion. -/
noncomputable def ofFiberHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V : C}
    (x : X.p.Fiber U) (y : X.p.Fiber V) {b : U ⟶ V}
    (f : x.1 ⟶ y.1) [X.p.IsHomLift b f] :
    Hom (J := J)
      (ofFiberObject (J := J) X x) (ofFiberObject (J := J) X y) where
  base := b
  components := DescentCompletionObjectOver.NaturalHomOver.ofFiberHom
    (J := J) x y (b := b) f

@[simp]
theorem ofFiberHom_base
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V : C}
    (x : X.p.Fiber U) (y : X.p.Fiber V) {b : U ⟶ V}
    (f : x.1 ⟶ y.1) [X.p.IsHomLift b f] :
    (ofFiberHom (J := J) x y (b := b) f).base = b :=
  rfl

@[simp]
theorem ofFiberHom_components
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V : C}
    (x : X.p.Fiber U) (y : X.p.Fiber V) {b : U ⟶ V}
    (f : x.1 ⟶ y.1) [X.p.IsHomLift b f] :
    (ofFiberHom (J := J) x y (b := b) f).components =
      DescentCompletionObjectOver.NaturalHomOver.ofFiberHom (J := J) x y (b := b) f :=
  rfl

end Hom

/-- The remaining owner-level condition needed to compose two total descent-completion morphisms:
the glued component family must be natural under further restrictions. -/
def Hom.composeNaturalityObligation
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {D E H : DescentCompletionObject (J := J) X}
    (a : Hom (J := J) D E) (b : Hom (J := J) E H) : Prop :=
  DescentCompletionObjectOver.NaturalHomOver.composeNaturalityObligation
    (J := J) hSheaf a.components b.components

/-- Conditional total composition of descent-completion morphisms.  The base arrow is the ordinary
base composite, and the local components are the source-faithful glued composite from stages 3.3-3.4.
-/
noncomputable def Hom.composeOfNaturality
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {D E H : DescentCompletionObject (J := J) X}
    (a : Hom (J := J) D E) (b : Hom (J := J) E H)
    (hnat : Hom.composeNaturalityObligation (J := J) hSheaf a b) :
    Hom (J := J) D H where
  base := a.base ≫ b.base
  components :=
    DescentCompletionObjectOver.NaturalHomOver.composeOfNaturality
      (J := J) hSheaf a.components b.components hnat

@[simp]
theorem Hom.composeOfNaturality_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {D E H : DescentCompletionObject (J := J) X}
    (a : Hom (J := J) D E) (b : Hom (J := J) E H)
    (hnat : Hom.composeNaturalityObligation (J := J) hSheaf a b) :
    (Hom.composeOfNaturality (J := J) hSheaf a b hnat).base = a.base ≫ b.base :=
  rfl

/-- Total composition of descent-completion morphisms.  The base arrow is the ordinary base
composite, and the local components are the source-faithful glued composite from stages 3.3-3.4. -/
noncomputable def Hom.compose
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {D E H : DescentCompletionObject (J := J) X}
    (a : Hom (J := J) D E) (b : Hom (J := J) E H) :
    Hom (J := J) D H where
  base := a.base ≫ b.base
  components :=
    DescentCompletionObjectOver.NaturalHomOver.compose
      (J := J) hSheaf a.components b.components

@[simp]
theorem Hom.compose_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {D E H : DescentCompletionObject (J := J) X}
    (a : Hom (J := J) D E) (b : Hom (J := J) E H) :
    (Hom.compose (J := J) hSheaf a b).base = a.base ≫ b.base :=
  rfl

theorem Hom.compose_assoc_family
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {D E H K : DescentCompletionObject (J := J) X}
    (a : Hom (J := J) D E) (b : Hom (J := J) E H) (c : Hom (J := J) H K)
    {W : C} (I : D.object.cover.Arrow) (M : K.object.cover.Arrow)
    (i : W ⟶ I.Y) (m : W ⟶ M.Y)
    (h : i ≫ I.f ≫ ((a.base ≫ b.base) ≫ c.base) = m ≫ M.f) :
    (((Hom.compose (J := J) hSheaf (Hom.compose (J := J) hSheaf a b) c).components).toHomOver).family
        I M i m h =
      (((Hom.compose (J := J) hSheaf a (Hom.compose (J := J) hSheaf b c)).components).toHomOver).family
        I M i m (by simpa [Category.assoc] using h) := by
  dsimp only [Hom.compose]
  exact
    DescentCompletionObjectOver.NaturalHomOver.compose_assoc_family
      (J := J) hSheaf a.components b.components c.components I M i m h

theorem Hom.compose_right_id
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {D E : DescentCompletionObject (J := J) X}
    (a : Hom (J := J) D E) :
    Hom.compose (J := J) hSheaf a (identity (J := J) E) = a := by
  refine Hom.ext_base_family (Hom.compose (J := J) hSheaf a (identity (J := J) E)) a ?_ ?_
  · simp [Hom.compose, identity]
  · intro W I L i l h
    simpa [Hom.compose, identity] using
      DescentCompletionObjectOver.NaturalHomOver.compose_right_id_family
        (J := J) hSheaf a.components I L i l h

theorem Hom.compose_left_id
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {D E : DescentCompletionObject (J := J) X}
    (a : Hom (J := J) D E) :
    Hom.compose (J := J) hSheaf (identity (J := J) D) a = a := by
  refine Hom.ext_base_family (Hom.compose (J := J) hSheaf (identity (J := J) D) a) a ?_ ?_
  · simp [Hom.compose, identity]
  · intro W I L i l h
    simpa [Hom.compose, identity] using
      DescentCompletionObjectOver.NaturalHomOver.compose_left_id_family
        (J := J) hSheaf a.components I L i l h

theorem Hom.compose_assoc
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {D E H K : DescentCompletionObject (J := J) X}
    (a : Hom (J := J) D E) (b : Hom (J := J) E H) (c : Hom (J := J) H K) :
    Hom.compose (J := J) hSheaf (Hom.compose (J := J) hSheaf a b) c =
      Hom.compose (J := J) hSheaf a (Hom.compose (J := J) hSheaf b c) := by
  refine Hom.ext_base_family
    (Hom.compose (J := J) hSheaf (Hom.compose (J := J) hSheaf a b) c)
    (Hom.compose (J := J) hSheaf a (Hom.compose (J := J) hSheaf b c)) ?_ ?_
  · simp [Hom.compose, Category.assoc]
  · intro W I M i m h
    simpa [Hom.compose] using
      Hom.compose_assoc_family (J := J) hSheaf a b c I M i m h

/-- Source stages 3.2-3.6 as a category: objects are descent data on covers, morphisms are
compatible double-indexed local morphism families, identities are descent transitions, and
composition is the sheaf-glued source composite. -/
@[reducible]
noncomputable def category
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X) :
    Category (DescentCompletionObject (J := J) X) where
  Hom D E := Hom (J := J) D E
  id D := identity (J := J) D
  comp a b := Hom.compose (J := J) hSheaf a b
  id_comp := by
    intro D E a
    exact Hom.compose_left_id (J := J) hSheaf a
  comp_id := by
    intro D E a
    exact Hom.compose_right_id (J := J) hSheaf a
  assoc := by
    intro A B D E a b c
    exact Hom.compose_assoc (J := J) hSheaf a b c

/-- The projection functor from the source-stage descent-completion category to the base site. -/
noncomputable def projectionFunctor
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X) :
    letI := category (J := J) hSheaf
    DescentCompletionObject (J := J) X ⥤ C := by
  letI := category (J := J) hSheaf
  exact
    { obj := fun D => D.base
      map := fun a => a.base
      map_id := by
        intro D
        rfl
      map_comp := by
        intro D E H a b
        rfl }

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
