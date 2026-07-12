import Mathlib
import StacksProject_2024.Chap07.Lemma_7_12_4
import StacksProject_2024.Chap04.Example_4_3_4
import StacksProject_2024.Chap04.Definition_4_29_6
import StacksProject_2024.Chap04.Lemma_4_33_3
import StacksProject_2024.Chap04.Lemma_4_33_12
import StacksProject_2024.Chap04.Definition_4_42_3
import StacksProject_2024.Chap08.Lemma_8_4_2
import StacksProject_2024.Chap08.Definition_8_4_5
import StacksProject_2024.Chap08.Lemma_8_4_6.CanonicalPullbackComparison
import StacksProject_2024.Chap08.Lemma_8_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.BasedFunctor
open scoped Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂ u v vDesc

namespace CategoryTheory

open Bicategory
open scoped RepresentablePresheaf

variable {C : Type u} [Category.{v} C]

/-- Helper for Chap08 Lemma 8 13 2: two consecutive isomorphism tails cancel after any
incoming morphism. -/
private theorem twoIsoTailCancel
    {D : Type u₁} [Category.{v₁} D] {W X Y Z : D}
    (f : W ⟶ X) (i : X ≅ Y) (j : Y ≅ Z) :
    f ≫ i.hom ≫ j.hom ≫ j.inv ≫ i.inv = f := by
  -- Reassociate the tail so the two inverse pairs cancel from right to left.
  calc
    f ≫ i.hom ≫ j.hom ≫ j.inv ≫ i.inv =
        f ≫ i.hom ≫ (j.hom ≫ j.inv) ≫ i.inv := by
      simp
    _ = f ≫ i.hom ≫ 𝟙 Y ≫ i.inv := by
      rw [j.hom_inv_id]
    _ = f ≫ i.hom ≫ i.inv := by
      simp
    _ = f ≫ (i.hom ≫ i.inv) := by
      simp
    _ = f ≫ 𝟙 X := by
      rw [i.hom_inv_id]
    _ = f := by
      simp

/-- Helper for Chap08 Lemma 8 13 2: two consecutive inverse heads cancel before any outgoing
morphism. -/
private theorem twoIsoHeadCancel
    {D : Type u₁} [Category.{v₁} D] {W X Y Z : D}
    (j : W ≅ X) (i : X ≅ Y) (f : Y ⟶ Z) :
    i.inv ≫ j.inv ≫ j.hom ≫ i.hom ≫ f = f := by
  -- Reassociate the head so the inverse pairs cancel from left to right.
  calc
    i.inv ≫ j.inv ≫ j.hom ≫ i.hom ≫ f =
        i.inv ≫ (j.inv ≫ j.hom) ≫ i.hom ≫ f := by
      simp
    _ = i.inv ≫ 𝟙 X ≫ i.hom ≫ f := by
      rw [j.inv_hom_id]
    _ = i.inv ≫ i.hom ≫ f := by
      simp
    _ = (i.inv ≫ i.hom) ≫ f := by
      simp
    _ = 𝟙 Y ≫ f := by
      rw [i.inv_hom_id]
    _ = f := by
      simp

/-- Helper for Chap08 Lemma 8 13 2: an equality of fiber objects induced by equality of the
underlying total objects has the expected underlying `eqToHom`. -/
private theorem fiber_eqToIso_hom_val
    {D : Type u₁} {E : Type u₂} [Category.{v₁} D] [Category.{v₂} E]
    (p : E ⥤ D) {U : D} {x y : p.Fiber U} (h : x.1 = y.1) :
    ((eqToIso (C := p.Fiber U) (Subtype.ext h : x = y)).hom).1 = eqToHom h := by
  cases x with
  | mk xv xp =>
  cases y with
  | mk yv yp =>
  cases h
  rfl

/-- Helper for Chap08 Lemma 8 13 2: the underlying arrow of a fiber `eqToHom` is the
corresponding total-category `eqToHom`. -/
private theorem fiber_eqToHom_val
    {D : Type u₁} {E : Type u₂} [Category.{v₁} D] [Category.{v₂} E]
    (p : E ⥤ D) {U : D} {x y : p.Fiber U} (h : x.1 = y.1) :
    ((eqToHom (Subtype.ext h : x = y) : x ⟶ y).1) = eqToHom h := by
  cases x with
  | mk xv xp =>
  cases y with
  | mk yv yp =>
  cases h
  rfl

/-- Helper for Chap08 Lemma 8 13 2: pulling back along `k ≫ eqToHom h` is canonically the
same as first transporting the fiber endpoint across `h` and then pulling back along `k`. -/
private noncomputable def canonicalPullback_eqToHomCompIso
    {D : Type u₁} {E : Type u₂} [Category.{v₁} D] [Category.{v₂} E]
    (p : E ⥤ D) [p.IsFibered]
    {Y V' V : D} (h : V' = V) (k : Y ⟶ V') (a : p.Fiber V) :
    (((canonicalFiberPseudofunctor p).map (k ≫ eqToHom h).op.toLoc).toFunctor.obj a) ≅
      Functor.Fiber.mk (p := p)
        (a :=
          ((((canonicalFiberPseudofunctor p).map k.op.toLoc).toFunctor.obj
            (Functor.Fiber.mk (p := p) (by
              rw [h]
              exact a.2))).1))
        (by
          exact (((canonicalFiberPseudofunctor p).map k.op.toLoc).toFunctor.obj
            (Functor.Fiber.mk (p := p) (by
              rw [h]
              exact a.2))).2) := by
  let a' : p.Fiber V' := Functor.Fiber.mk (p := p) (by
    rw [h]
    exact a.2)
  let hc := canonicalPullbackChoice p
  let y₁ : p.Fiber Y := (hc.pullbackFunctor (k ≫ eqToHom h)).obj a
  let y₂ : p.Fiber Y := (hc.pullbackFunctor k).obj a'
  let φ₁ : y₁.1 ⟶ a.1 := hc.map (k ≫ eqToHom h) a
  let φ₂ : y₂.1 ⟶ a.1 := hc.map k a'
  have hφ₁ : p.IsStronglyCartesian (k ≫ eqToHom h) φ₁ := by
    simpa [φ₁, y₁, hc] using hc.isStronglyCartesian (k ≫ eqToHom h) a
  have hφ₂ : p.IsStronglyCartesian (k ≫ eqToHom h) φ₂ := by
    have hcart : p.IsStronglyCartesian k φ₂ := by
      simpa [φ₂, y₂, a', hc] using hc.isStronglyCartesian k a'
    letI : p.IsStronglyCartesian k φ₂ := hcart
    have hhom : p.IsHomLift (k ≫ eqToHom h) φ₂ := by
      refine IsHomLift.of_fac' p (k ≫ eqToHom h) φ₂
        (IsHomLift.domain_eq p k φ₂) a.2 ?_
      rw [IsHomLift.fac' p k φ₂]
      simpa [a', Category.assoc]
    letI : p.IsHomLift (k ≫ eqToHom h) φ₂ := hhom
    refine { universal_property' := ?_ }
    intro c g τ hτ
    have hτk : p.IsHomLift (g ≫ k) τ := by
      refine IsHomLift.of_fac' p (g ≫ k) τ
        (IsHomLift.domain_eq p (g ≫ (k ≫ eqToHom h)) τ) a'.2 ?_
      rw [IsHomLift.fac' p (g ≫ (k ≫ eqToHom h)) τ]
      simpa [a', Category.assoc]
    letI : p.IsHomLift (g ≫ k) τ := hτk
    rcases Functor.IsStronglyCartesian.universal_property p k φ₂ g (g ≫ k) rfl τ with
      ⟨χ, hχ, huniq⟩
    refine ⟨χ, hχ, ?_⟩
    intro χ' hχ'
    exact huniq χ' hχ'
  letI : p.IsStronglyCartesian (k ≫ eqToHom h) φ₁ := hφ₁
  letI : p.IsStronglyCartesian (k ≫ eqToHom h) φ₂ := hφ₂
  have hsame : (k ≫ eqToHom h) = (Iso.refl Y).hom ≫ (k ≫ eqToHom h) := by
    change k ≫ eqToHom h = 𝟙 Y ≫ (k ≫ eqToHom h)
    rw [Category.id_comp]
  let e := Functor.IsStronglyCartesian.domainIsoOfBaseIso
    (p := p) (g := Iso.refl Y) hsame φ₂ φ₁
  exact
    { hom := ⟨e.hom, by
        change p.IsHomLift (Iso.refl Y).hom e.hom
        infer_instance⟩
      inv := ⟨e.inv, by
        change p.IsHomLift (Iso.refl Y).inv e.inv
        infer_instance⟩
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact e.inv_hom_id }

/-- Helper for Chap08 Lemma 8 13 2: the endpoint-transport pullback comparison has the
expected factorization through the pullback chosen after transporting the endpoint. -/
private theorem canonicalPullback_eqToHomCompIso_hom_fac
    {D : Type u₁} {E : Type u₂} [Category.{v₁} D] [Category.{v₂} E]
    (p : E ⥤ D) [p.IsFibered]
    {Y V' V : D} (h : V' = V) (k : Y ⟶ V') (a : p.Fiber V) :
    (canonicalPullback_eqToHomCompIso p h k a).hom.1 ≫
        (canonicalPullbackChoice p).map k
          (Functor.Fiber.mk (p := p) (by
            rw [h]
            exact a.2)) =
      (canonicalPullbackChoice p).map (k ≫ eqToHom h) a := by
  let a' : p.Fiber V' := Functor.Fiber.mk (p := p) (by
    rw [h]
    exact a.2)
  let hc := canonicalPullbackChoice p
  let y₁ : p.Fiber Y := (hc.pullbackFunctor (k ≫ eqToHom h)).obj a
  let y₂ : p.Fiber Y := (hc.pullbackFunctor k).obj a'
  let φ₁ : y₁.1 ⟶ a.1 := hc.map (k ≫ eqToHom h) a
  let φ₂ : y₂.1 ⟶ a.1 := hc.map k a'
  have hφ₁ : p.IsStronglyCartesian (k ≫ eqToHom h) φ₁ := by
    simpa [φ₁, y₁, hc] using hc.isStronglyCartesian (k ≫ eqToHom h) a
  have hφ₂ : p.IsStronglyCartesian (k ≫ eqToHom h) φ₂ := by
    have hcart : p.IsStronglyCartesian k φ₂ := by
      simpa [φ₂, y₂, a', hc] using hc.isStronglyCartesian k a'
    letI : p.IsStronglyCartesian k φ₂ := hcart
    have hhom : p.IsHomLift (k ≫ eqToHom h) φ₂ := by
      refine IsHomLift.of_fac' p (k ≫ eqToHom h) φ₂
        (IsHomLift.domain_eq p k φ₂) a.2 ?_
      rw [IsHomLift.fac' p k φ₂]
      simpa [a', Category.assoc]
    letI : p.IsHomLift (k ≫ eqToHom h) φ₂ := hhom
    refine { universal_property' := ?_ }
    intro c g τ hτ
    have hτk : p.IsHomLift (g ≫ k) τ := by
      refine IsHomLift.of_fac' p (g ≫ k) τ
        (IsHomLift.domain_eq p (g ≫ (k ≫ eqToHom h)) τ) a'.2 ?_
      rw [IsHomLift.fac' p (g ≫ (k ≫ eqToHom h)) τ]
      simpa [a', Category.assoc]
    letI : p.IsHomLift (g ≫ k) τ := hτk
    rcases Functor.IsStronglyCartesian.universal_property p k φ₂ g (g ≫ k) rfl τ with
      ⟨χ, hχ, huniq⟩
    refine ⟨χ, hχ, ?_⟩
    intro χ' hχ'
    exact huniq χ' hχ'
  letI : p.IsStronglyCartesian (k ≫ eqToHom h) φ₁ := hφ₁
  letI : p.IsStronglyCartesian (k ≫ eqToHom h) φ₂ := hφ₂
  have hsame : (k ≫ eqToHom h) = (Iso.refl Y).hom ≫ (k ≫ eqToHom h) := by
    change k ≫ eqToHom h = 𝟙 Y ≫ (k ≫ eqToHom h)
    rw [Category.id_comp]
  dsimp [canonicalPullback_eqToHomCompIso]
  change (Functor.IsStronglyCartesian.domainIsoOfBaseIso
      (p := p) (g := Iso.refl Y) hsame φ₂ φ₁).hom ≫ φ₂ = φ₁
  rw [Functor.IsStronglyCartesian.domainIsoOfBaseIso_hom]
  exact Functor.IsStronglyCartesian.fac p (k ≫ eqToHom h) φ₂ hsame φ₁

/-- Helper for Chap08 Lemma 8 13 2: the inverse of the endpoint-transport pullback comparison
factors through the pullback chosen before transporting the endpoint. -/
private theorem canonicalPullback_eqToHomCompIso_inv_fac
    {D : Type u₁} {E : Type u₂} [Category.{v₁} D] [Category.{v₂} E]
    (p : E ⥤ D) [p.IsFibered]
    {Y V' V : D} (h : V' = V) (k : Y ⟶ V') (a : p.Fiber V) :
    (canonicalPullback_eqToHomCompIso p h k a).inv.1 ≫
        (canonicalPullbackChoice p).map (k ≫ eqToHom h) a =
      (canonicalPullbackChoice p).map k
        (Functor.Fiber.mk (p := p) (by
          rw [h]
          exact a.2)) := by
  rw [← canonicalPullback_eqToHomCompIso_hom_fac p h k a]
  let e := canonicalPullback_eqToHomCompIso p h k a
  change e.inv.1 ≫ e.hom.1 ≫
      (canonicalPullbackChoice p).map k
        (Functor.Fiber.mk (p := p) (by
          rw [h]
          exact a.2)) =
    (canonicalPullbackChoice p).map k
      (Functor.Fiber.mk (p := p) (by
        rw [h]
        exact a.2))
  have hcancel : e.inv.1 ≫ e.hom.1 = 𝟙 _ := by
    exact congrArg (fun m => m.1) e.inv_hom_id
  rw [← Category.assoc, hcancel, Category.id_comp]

private abbrev toFibredCategoryMor
    {J : GrothendieckTopology C} {X Y : StackOver J} (F : X ⟶ Y) :=
  InducedCategory.Hom.toFibredCategoryMor F

private abbrev toBasedFunctor
    {J : GrothendieckTopology C} {X Y : StackOver J} (F : X ⟶ Y) :=
  InducedCategory.Hom.toBasedFunctor F

private abbrev stackTwoHomToFibredCategoryMorTwoHom
    {J : GrothendieckTopology C} {X Y : StackOver J} {F G : X ⟶ Y}
    (η : F ⟶ G) :
    toFibredCategoryMor F ⟶ toFibredCategoryMor G :=
  η.hom.hom

private abbrev stackTwoHomToNatTrans
    {J : GrothendieckTopology C} {X Y : StackOver J} {F G : X ⟶ Y}
    (η : F ⟶ G) :
    (toBasedFunctor F).toFunctor ⟶ (toBasedFunctor G).toFunctor :=
  (stackTwoHomToFibredCategoryMorTwoHom η).hom.hom.toNatTrans

section

variable (J : GrothendieckTopology C)

variable (U : C)

/-- Helper for Chap08 Lemma 8 13 2: an object of a slice-projection fiber is determined by
its underlying arrow to the slice vertex. -/
private def over_fiber_to_hom (U V : C) :
    ((Over.forget U).Fiber V) → (V ⟶ U) :=
  fun a ↦ eqToHom a.2.symm ≫ a.1.hom

/-- Helper for Chap08 Lemma 8 13 2: the fiber of the slice projection over `V` is in bijection
with the hom-set `V ⟶ U`. -/
private theorem over_fiber_to_hom_bijective (U V : C) :
    Function.Bijective (over_fiber_to_hom U V) := by
  -- Unpack fiber objects and compare only the remembered arrows to `U`.
  constructor
  · intro a b h
    cases a with
    | mk a ha =>
        cases b with
        | mk b hb =>
            dsimp [over_fiber_to_hom] at h ⊢
            cases a with
            | mk la ra ha' =>
                cases b with
                | mk lb rb hb' =>
                    cases ha
                    cases hb
                    cases ra
                    cases rb
                    have h' : ha' = hb' := by
                      simpa [Over.forget_obj] using h
                    subst h'
                    rfl
  · intro f
    refine ⟨⟨Over.mk f, rfl⟩, ?_⟩
    simp [over_fiber_to_hom]

/-- Helper for Chap08 Lemma 8 13 2: equality of arrows to `U` identifies two objects in the
same fiber of the slice projection. -/
private theorem over_fiber_eq_of_hom_eq
    {U V : C} {a b : (Over.forget U).Fiber V}
    (h : over_fiber_to_hom U V a = over_fiber_to_hom U V b) :
    a = b :=
  (over_fiber_to_hom_bijective U V).1 h

/-- Helper for Chap08 Lemma 8 13 2: the fiber object built from an arrow has that arrow as its
underlying map to the slice vertex. -/
private theorem over_fiber_to_hom_fiber_mk_over_mk
    {U V : C} (f : V ⟶ U) :
    over_fiber_to_hom U V (Functor.Fiber.mk (a := Over.mk f) rfl) = f := by
  -- Normalize the equality transport in the freshly constructed fiber object.
  change eqToHom rfl.symm ≫ (Over.mk f).hom = f
  simp

/-- Helper for Chap08 Lemma 8 13 2: any morphism in a slice-projection fiber preserves the
underlying arrow to `U`. -/
private theorem over_fiber_to_hom_eq_of_hom
    {U V : C} {a b : (Over.forget U).Fiber V} (h : a ⟶ b) :
    over_fiber_to_hom U V a = over_fiber_to_hom U V b := by
  -- In a fiber over `V`, the base part of the morphism is the identity, so the slice triangle
  -- identifies the two arrows to `U`.
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  rcases a with ⟨la, ra, fa⟩
  rcases b with ⟨lb, rb, fb⟩
  dsimp at ha hb
  cases ha
  cases hb
  simp [over_fiber_to_hom]
  have hw : (Functor.Fiber.fiberInclusion.map h).left ≫ fb = fa := by
    simpa using Over.w (Functor.Fiber.fiberInclusion.map h)
  have hleft : (Functor.Fiber.fiberInclusion.map h).left = 𝟙 V := by
    simpa using
      (@IsHomLift.fac' _ _ _ _ (Over.forget U) V V _ _ (𝟙 V)
        (Functor.Fiber.fiberInclusion.map h) h.2)
  rw [hleft] at hw
  simpa using (show fa = 𝟙 V ≫ fb from hw.symm)

/-- Helper for Chap08 Lemma 8 13 2: every hom-set in a fiber of the slice projection is a
subsingleton. -/
private theorem over_fiber_hom_subsingleton
    {U V : C} (a b : (Over.forget U).Fiber V) :
    Subsingleton (a ⟶ b) := by
  -- Fiber morphisms have the same underlying identity map in `C`, hence the slice morphisms agree.
  refine ⟨fun φ ψ ↦ ?_⟩
  apply Functor.Fiber.hom_ext
  apply Over.OverMorphism.ext
  have hφ := @IsHomLift.fac' _ _ _ _ (Over.forget U) V V _ _ (𝟙 V)
    (Functor.Fiber.fiberInclusion.map φ) φ.2
  have hψ := @IsHomLift.fac' _ _ _ _ (Over.forget U) V V _ _ (𝟙 V)
    (Functor.Fiber.fiberInclusion.map ψ) ψ.2
  simpa using hφ.trans hψ.symm

/-- Helper for Chap08 Lemma 8 13 2: a hom-lift in the slice projection records precomposition
of the underlying arrow to `U`. -/
private theorem over_fiber_to_hom_eq_comp_of_isHomLift
    {U Y Z : C} {a : (Over.forget U).Fiber Y} {b : (Over.forget U).Fiber Z}
    {f : Y ⟶ Z} {h : a.1 ⟶ b.1} (hh : Functor.IsHomLift (Over.forget U) f h) :
    over_fiber_to_hom U Y a = f ≫ over_fiber_to_hom U Z b := by
  -- The hom-lift factorization identifies the base map of `h` with `f`; the slice triangle then
  -- gives the required composite formula.
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  rcases a with ⟨la, ra, fa⟩
  rcases b with ⟨lb, rb, fb⟩
  dsimp at ha hb
  cases ha
  cases hb
  have hfac : (Over.forget U).map h = f := by
    simpa using (@IsHomLift.fac' _ _ _ _ (Over.forget U) Y Z _ _ f h hh)
  have hw : h.left ≫ fb = fa := by
    simpa using Over.w h
  have hw' : fa = f ≫ fb := by
    rw [← hfac]
    simpa using hw.symm
  simpa [over_fiber_to_hom] using hw'

/-- Helper for Chap08 Lemma 8 13 2: an object of a composite fiber over `C` remembers the
underlying arrow from the base object to `U`. -/
private def compositeFiberArrowToU
    {S : Type*} [Category S] (q : S ⥤ Over U) {V : C}
    (a : (q ⋙ Over.forget U).Fiber V) : V ⟶ U :=
  eqToHom a.2.symm ≫ (q.obj a.1).hom

/-- Helper for Chap08 Lemma 8 13 2: a composite-fiber object is the explicit slice object
defined by its remembered arrow to `U`. -/
private theorem compositeFiberObj_eq_overMk_of_arrowToU_eq
    {S : Type*} [Category S] (q : S ⥤ Over U) {V : C}
    (a : (q ⋙ Over.forget U).Fiber V) {u : V ⟶ U}
    (hu : u = compositeFiberArrowToU (U := U) q a) :
    q.obj a.1 = Over.mk u := by
  -- Open the fiber equality so the left object is literally `V`, then compare slice objects by
  -- their arrows to `U`.
  rcases a with ⟨a, ha⟩
  dsimp [compositeFiberArrowToU] at hu ha ⊢
  cases ha
  exact CostructuredArrow.obj_ext (q.obj a) (Over.mk u) rfl (by simpa using hu)

/-- Helper for Chap08 Lemma 8 13 2: a composite-fiber object whose remembered arrow is `u`
can be regarded as a `q`-fiber object over `Over.mk u`. -/
private abbrev compositeFiberObjToQFiberObj
    {S : Type*} [Category S] (q : S ⥤ Over U) {V : C}
    (a : (q ⋙ Over.forget U).Fiber V) {u : V ⟶ U}
    (hu : u = compositeFiberArrowToU (U := U) q a) :
    q.Fiber (Over.mk u) :=
  Functor.Fiber.mk (a := a.1)
    (compositeFiberObj_eq_overMk_of_arrowToU_eq (U := U) q a hu)

/-- Helper for Chap08 Lemma 8 13 2: a `q`-fiber object over a slice arrow has the
corresponding base object after composing with the slice projection. -/
private theorem qFiberAsCompositeFiberObj_base_eq
    {S : Type*} [Category S] (q : S ⥤ Over U) {V : C} {u : V ⟶ U}
    (x : q.Fiber (Over.mk u)) :
    (q ⋙ Over.forget U).obj x.1 = V := by
  -- Project the fiber equality through `Over.forget U`; the target slice object is `V / U`.
  simpa [Functor.comp_obj] using congrArg (Over.forget U).obj x.2

/-- Helper for Chap08 Lemma 8 13 2: view a `q`-fiber object over a slice arrow as an object in
the fiber of the composite projection over the source of that arrow. -/
private abbrev qFiberAsCompositeFiberObj
    {S : Type*} [Category S] (q : S ⥤ Over U) {V : C} {u : V ⟶ U}
    (x : q.Fiber (Over.mk u)) :
    (q ⋙ Over.forget U).Fiber V :=
  Functor.Fiber.mk (a := x.1) (qFiberAsCompositeFiberObj_base_eq (U := U) q x)

/-- Helper for Chap08 Lemma 8 13 2: the composite-fiber object obtained from a `q`-fiber
object remembers the original slice arrow to `U`. -/
private theorem qFiberAsCompositeFiberObj_arrowToU
    {S : Type*} [Category S] (q : S ⥤ Over U) {V : C} {u : V ⟶ U}
    (x : q.Fiber (Over.mk u)) :
    compositeFiberArrowToU (U := U) q (qFiberAsCompositeFiberObj (U := U) q x) = u := by
  -- Once the fiber equality is opened, both remembered arrows are literally the same arrow.
  rcases x with ⟨x, hx⟩
  dsimp [qFiberAsCompositeFiberObj, qFiberAsCompositeFiberObj_base_eq,
    compositeFiberArrowToU] at hx ⊢
  have hw : (eqToHom hx).left ≫ u = (q.obj x).hom := by
    simpa using Over.w (eqToHom hx : q.obj x ⟶ Over.mk u)
  have hleft :
      (eqToHom hx).left =
        eqToHom (qFiberAsCompositeFiberObj_base_eq (U := U) q (Functor.Fiber.mk (p := q) hx)) := by
    have hproof :
        qFiberAsCompositeFiberObj_base_eq (U := U) q (Functor.Fiber.mk (p := q) hx) =
          congrArg (Over.forget U).obj hx := by
      apply Subsingleton.elim
    rw [hproof]
    exact CategoryTheory.eqToHom_map (Over.forget U) hx
  calc
    eqToHom (qFiberAsCompositeFiberObj_base_eq (U := U) q (Functor.Fiber.mk (p := q) hx)).symm ≫
        (q.obj x).hom =
      eqToHom (qFiberAsCompositeFiberObj_base_eq (U := U) q (Functor.Fiber.mk (p := q) hx)).symm ≫
        ((eqToHom hx).left ≫ u) := by
      rw [← hw]
      rfl
    _ =
      eqToHom (qFiberAsCompositeFiberObj_base_eq (U := U) q (Functor.Fiber.mk (p := q) hx)).symm ≫
        eqToHom (qFiberAsCompositeFiberObj_base_eq (U := U) q (Functor.Fiber.mk (p := q) hx)) ≫ u := by
      rw [hleft]
      rfl
    _ = u := by
      simp

/-- Helper for Chap08 Lemma 8 13 2: the composite-fiber view of a `q`-fiber object remembers
the arrow of its slice base object. -/
private theorem qFiberAsCompositeFiberObj_arrowToU_of_over
    {S : Type*} [Category S] (q : S ⥤ Over U) {A : Over U}
    (x : q.Fiber A) :
    compositeFiberArrowToU (U := U) q (qFiberAsCompositeFiberObj (U := U) q x) = A.hom := by
  -- `Over.mk A.hom` is the eta-expanded spelling of the same slice object.
  simpa using qFiberAsCompositeFiberObj_arrowToU (U := U) q x

/-- Helper for Chap08 Lemma 8 13 2: after viewing a local object of slice descent data as a
composite-fiber object, its remembered arrow to `U` is the projected cover arrow followed by the
target slice coordinate. -/
private theorem qDescentData_obj_compositeFiberArrowToU
    {S : Type*} [Category S] (q : S ⥤ Over U) [q.IsFibered]
    {A : Over U} (T : (J.over U).Cover A)
    (D : (canonicalFiberPseudofunctor q).DescentData (fun I : T.Arrow ↦ I.f))
    (I : T.Arrow) :
    compositeFiberArrowToU (U := U) q
        (qFiberAsCompositeFiberObj (U := U) q (D.obj I)) =
      I.f.left ≫ A.hom := by
  have hlocal :
      compositeFiberArrowToU (U := U) q
          (qFiberAsCompositeFiberObj (U := U) q (D.obj I)) =
        I.Y.hom :=
    qFiberAsCompositeFiberObj_arrowToU_of_over (U := U) q (D.obj I)
  simpa [hlocal] using (Over.w I.f).symm

/-- Helper for Chap08 Lemma 8 13 2: the arrows to `U` extracted from a slice descent datum,
after forgetting to the composite projection, are compatible over the projected base cover. -/
private theorem qDescentData_composite_arrowsToU_compatible
    {S : Type*} [Category S] (q : S ⥤ Over U) [q.IsFibered]
    {A : Over U} (T : (J.over U).Cover A)
    (D : (canonicalFiberPseudofunctor q).DescentData (fun I : T.Arrow ↦ I.f)) :
    Presieve.Arrows.Compatible (yoneda.obj U) (fun I : T.Arrow ↦ I.f.left)
      (fun I ↦
        compositeFiberArrowToU (U := U) q
          (qFiberAsCompositeFiberObj (U := U) q (D.obj I))) := by
  intro I₁ I₂ Y g₁ g₂ h
  change
    g₁ ≫ compositeFiberArrowToU (U := U) q
        (qFiberAsCompositeFiberObj (U := U) q (D.obj I₁)) =
      g₂ ≫ compositeFiberArrowToU (U := U) q
        (qFiberAsCompositeFiberObj (U := U) q (D.obj I₂))
  rw [qDescentData_obj_compositeFiberArrowToU (J := J) (U := U) q T D I₁,
    qDescentData_obj_compositeFiberArrowToU (J := J) (U := U) q T D I₂]
  simpa [Category.assoc] using congrArg (fun f ↦ f ≫ A.hom) h

/-- Helper for Chap08 Lemma 8 13 2: converting a composite-fiber object to the corresponding
`q`-fiber and then forgetting back to the composite fiber recovers the original object. -/
private theorem qFiberAsCompositeFiberObj_compositeFiberObjToQFiberObj
    {S : Type*} [Category S] (q : S ⥤ Over U) {V : C}
    (a : (q ⋙ Over.forget U).Fiber V) {u : V ⟶ U}
    (hu : u = compositeFiberArrowToU (U := U) q a) :
    qFiberAsCompositeFiberObj (U := U) q
      (compositeFiberObjToQFiberObj (U := U) q a hu) = a := by
  -- Both fiber objects have the same underlying total object.
  apply Subtype.ext
  rfl

/-- Helper for Chap08 Lemma 8 13 2: a fiber over a slice object maps to the corresponding
fiber of the composite projection over the source of that slice object. -/
private def qFiberToCompositeFiberFunctor
    {S : Type*} [Category S] (q : S ⥤ Over U) (A : Over U) :
    q.Fiber A ⥤ (q ⋙ Over.forget U).Fiber A.left where
  obj x := qFiberAsCompositeFiberObj (U := U) q x
  map {x y} φ := by
    refine ⟨φ.1, ?_⟩
    letI : q.IsHomLift (𝟙 A) φ.1 := φ.2
    refine IsHomLift.of_fac' (q ⋙ Over.forget U) (𝟙 A.left) φ.1 ?_ ?_ ?_
    · exact qFiberAsCompositeFiberObj_base_eq (U := U) q x
    · exact qFiberAsCompositeFiberObj_base_eq (U := U) q y
    · simpa [Functor.comp_map] using congrArg (Over.forget U).map
        (IsHomLift.fac' q (𝟙 A) φ.1)
  map_id x := by
    apply Functor.Fiber.hom_ext
    rfl
  map_comp {x y z} φ ψ := by
    apply Functor.Fiber.hom_ext
    rfl

/-- Helper for Chap08 Lemma 8 13 2: viewing a slice fiber inside the composite fiber is
faithful. -/
private theorem qFiberToCompositeFiberFunctor_faithful
    {S : Type*} [Category S] (q : S ⥤ Over U) (A : Over U) :
    (qFiberToCompositeFiberFunctor (U := U) q A).Faithful := by
  constructor
  intro X Y f g hfg
  apply Functor.Fiber.hom_ext
  exact congrArg (fun k => k.1) hfg

/-- Helper for Chap08 Lemma 8 13 2: the full subcategory of a composite fiber whose objects
remember the fixed slice arrow `A.hom`. -/
private abbrev compositeFiberFixedArrowProperty
    {S : Type*} [Category S] (q : S ⥤ Over U) (A : Over U) :
    ObjectProperty ((q ⋙ Over.forget U).Fiber A.left) :=
  fun x => compositeFiberArrowToU (U := U) q x = A.hom

/-- Helper for Chap08 Lemma 8 13 2: a `q`-fiber over `A` lands in the fixed-arrow part of the
corresponding composite fiber. -/
private noncomputable def qFiberToCompositeFixedFiberFunctor
    {S : Type*} [Category S] (q : S ⥤ Over U) (A : Over U) :
    q.Fiber A ⥤ (compositeFiberFixedArrowProperty (U := U) q A).FullSubcategory :=
  (compositeFiberFixedArrowProperty (U := U) q A).lift
    (qFiberToCompositeFiberFunctor (U := U) q A)
    (fun x => by
      simpa [compositeFiberFixedArrowProperty] using
        qFiberAsCompositeFiberObj_arrowToU_of_over (U := U) q x)

/-- Helper for Chap08 Lemma 8 13 2: a morphism in `Over U` whose left component is `f`
identifies the source arrow to `U` with `f` followed by the target arrow. -/
private theorem overMap_hom_eq_comp_of_left_eq
    {S : Type*} [Category S] (q : S ⥤ Over U) {a b : S}
    {f : (q.obj a).left ⟶ (q.obj b).left} {h : a ⟶ b}
    (hfac : (q.map h).left = f) :
    (q.obj a).hom = f ≫ (q.obj b).hom := by
  -- The defining triangle in the slice category gives the comparison, and `hfac` rewrites the
  -- left component to the chosen base arrow.
  have hw : (q.map h).left ≫ (q.obj b).hom = (q.obj a).hom := by
    simpa using Over.w (q.map h)
  rw [← hfac]
  simpa using hw.symm

/-- Helper for Chap08 Lemma 8 13 2: a hom-lift for a composite projection identifies the
remembered arrows to `U` by precomposition with the base arrow. -/
private theorem compositeFiberArrowToU_eq_comp_of_isHomLift
    {S : Type*} [Category S] (q : S ⥤ Over U)
    {Y Z : C} {a : (q ⋙ Over.forget U).Fiber Y} {b : (q ⋙ Over.forget U).Fiber Z}
    {f : Y ⟶ Z} {h : a.1 ⟶ b.1} (hh : Functor.IsHomLift (q ⋙ Over.forget U) f h) :
    compositeFiberArrowToU (U := U) q a = f ≫ compositeFiberArrowToU (U := U) q b := by
  -- Open the fiber endpoints so the hom-lift base arrow has the same endpoints as `q.map h`.
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  dsimp [compositeFiberArrowToU] at ha hb ⊢
  cases ha
  cases hb
  -- First extract the base-arrow equality from the hom-lift package, then use the ordinary
  -- slice-map normal form above.
  have hfac : (Over.forget U).map (q.map h) = f := by
    simpa using
      (@IsHomLift.fac' _ _ _ _ (q ⋙ Over.forget U) _ _ _ _ f h hh)
  have hleft : (q.map h).left = f := by
    simpa using hfac
  simpa using overMap_hom_eq_comp_of_left_eq (U := U) q hleft

/-- Helper for Chap08 Lemma 8 13 2: the canonical pullback in the slice projection represents
precomposition of arrows to `U`. -/
private theorem over_pseudofunctor_map_obj_hom_eq_comp
    {U Y Z : C} (f : Y ⟶ Z) (a : (Over.forget U).Fiber Z) :
    over_fiber_to_hom U Y
        (((canonicalFiberPseudofunctor (Over.forget U)).map f.op.toLoc).toFunctor.obj a) =
      f ≫ over_fiber_to_hom U Z a := by
  -- Read the canonical pullback choice as a strongly cartesian hom-lift and apply the previous
  -- normal-form lemma.
  let hc := canonicalPullbackChoice (Over.forget U)
  let φ := hc.map f a
  simpa using
    (over_fiber_to_hom_eq_comp_of_isHomLift
      (U := U) (a := ((hc.pullbackFunctor f).obj a)) (b := a) (f := f) (h := φ)
      ((hc.isStronglyCartesian f a).toIsHomLift))

/-- Helper for Chap08 Lemma 8 13 2: for a functor between discrete categories, being an
equivalence is the same as being bijective on objects. -/
private theorem isEquivalence_iff_bijective_obj_of_isDiscrete
    {A B : Type*} [Category A] [Category B] [IsDiscrete A] [IsDiscrete B]
    (G : A ⥤ B) :
    G.IsEquivalence ↔ Function.Bijective G.obj := by
  -- In discrete categories, fullness and faithfulness are automatic and essential surjectivity is
  -- exactly surjectivity on objects.
  constructor
  · intro h
    let _ : G.IsEquivalence := h
    refine ⟨?_, ?_⟩
    · intro X Y hXY
      exact obj_ext_of_isDiscrete (G.preimage (eqToHom hXY))
    · intro Y
      rcases Functor.EssSurj.mem_essImage (F := G) Y with ⟨X, ⟨e⟩⟩
      exact ⟨X, obj_ext_of_isDiscrete e.hom⟩
  · intro hG
    let faithfulG : G.Faithful := ⟨fun {_ _} _ _ _ ↦ Subsingleton.elim _ _⟩
    let fullG : G.Full := ⟨fun {X Y} f ↦
      ⟨eqToHom (hG.1 (obj_ext_of_isDiscrete f)), Subsingleton.elim _ _⟩⟩
    let essSurjG : G.EssSurj := Functor.essSurj_of_surj hG.2
    exact { faithful := faithfulG, full := fullG, essSurj := essSurjG }

/-- Helper for Chap08 Lemma 8 13 2: for a fixed cover, descent for the slice projection is
equivalent to the sheaf condition for the representable presheaf. -/
private theorem over_cover_toDescentData_isEquivalence_iff_isSheafFor
    (J : GrothendieckTopology C) (U V : C) (S : J.Cover V) :
    ((canonicalFiberPseudofunctor (Over.forget U)).toDescentData
      (fun I : S.Arrow ↦ I.f)).IsEquivalence ↔
      Presieve.IsSheafFor (yoneda.obj U) ((S : Sieve V).arrows) := by
  -- Convert descent data into compatible families of local arrows to `U`.
  let DD :=
    (canonicalFiberPseudofunctor (Over.forget U)).DescentData
      (fun I : S.Arrow ↦ I.f)
  let compat :=
    Subtype (Presieve.Arrows.Compatible (yoneda.obj U) (fun I : S.Arrow ↦ I.f))
  let compatOfDescent : DD → compat := fun D ↦
    ⟨fun I ↦ over_fiber_to_hom U I.Y (D.obj I), by
      intro I₁ I₂ Y g₁ g₂ h
      let q : Y ⟶ V := g₁ ≫ I₁.f
      have hg₁ : g₁ ≫ I₁.f = q := rfl
      have hg₂ : g₂ ≫ I₂.f = q := by
        simpa [q] using h.symm
      have hEq :
          over_fiber_to_hom U Y
              (((canonicalFiberPseudofunctor (Over.forget U)).map g₁.op.toLoc).toFunctor.obj
                (D.obj I₁)) =
            over_fiber_to_hom U Y
              (((canonicalFiberPseudofunctor (Over.forget U)).map g₂.op.toLoc).toFunctor.obj
                (D.obj I₂)) := by
        exact over_fiber_to_hom_eq_of_hom (D.hom q g₁ g₂ hg₁ hg₂)
      have hg₁' :
          (yoneda.obj U).map g₁.op (over_fiber_to_hom U I₁.Y (D.obj I₁)) =
            over_fiber_to_hom U Y
              (((canonicalFiberPseudofunctor (Over.forget U)).map g₁.op.toLoc).toFunctor.obj
                (D.obj I₁)) := by
        simpa using
          (over_pseudofunctor_map_obj_hom_eq_comp (U := U) (f := g₁) (a := D.obj I₁)).symm
      have hg₂' :
          over_fiber_to_hom U Y
              (((canonicalFiberPseudofunctor (Over.forget U)).map g₂.op.toLoc).toFunctor.obj
                (D.obj I₂)) =
            (yoneda.obj U).map g₂.op (over_fiber_to_hom U I₂.Y (D.obj I₂)) := by
        simpa using
          over_pseudofunctor_map_obj_hom_eq_comp (U := U) (f := g₂) (a := D.obj I₂)
      exact hg₁'.trans (hEq.trans hg₂')⟩
  have hHomSub :
      ∀ D₁ D₂ : DD, Subsingleton (D₁ ⟶ D₂) := by
    intro D₁ D₂
    refine ⟨fun φ ψ ↦ Pseudofunctor.DescentData.hom_ext (fun I ↦ ?_)⟩
    exact (over_fiber_hom_subsingleton (D₁.obj I) (D₂.obj I)).elim _ _
  have hCompatMap :
      ∀ {D₁ D₂ : DD} (φ : D₁ ⟶ D₂), compatOfDescent D₁ = compatOfDescent D₂ := by
    intro D₁ D₂ φ
    apply Subtype.ext
    funext I
    exact over_fiber_to_hom_eq_of_hom (φ.hom I)
  let G : DD ⥤ Discrete compat := by
    refine
      { obj := fun D ↦ Discrete.mk (compatOfDescent D)
        map := fun {D₁ D₂} φ ↦ ?_
        map_id := ?_
        map_comp := ?_ }
    · exact eqToHom (congrArg Discrete.mk (hCompatMap φ))
    · intro D
      exact Subsingleton.elim _ _
    · intro D₁ D₂ D₃ φ ψ
      exact Subsingleton.elim _ _
  -- Build descent data back from a compatible family by using the corresponding slice objects.
  let descentOfCompat : compat → DD := fun s ↦
    { obj := fun I ↦ Functor.Fiber.mk (a := Over.mk (s.1 I)) rfl
      hom := fun {Y} q {I₁ I₂} f₁ f₂ hf₁ hf₂ ↦ by
        have h₁ :
            over_fiber_to_hom U Y
                (((canonicalFiberPseudofunctor (Over.forget U)).map f₁.op.toLoc).toFunctor.obj
                  (Functor.Fiber.mk (a := Over.mk (s.1 I₁)) rfl)) =
              (yoneda.obj U).map f₁.op (s.1 I₁) := by
          simpa [over_fiber_to_hom_fiber_mk_over_mk] using
            over_pseudofunctor_map_obj_hom_eq_comp
              (U := U) (f := f₁) (a := Functor.Fiber.mk (a := Over.mk (s.1 I₁)) rfl)
        have h₂ :
            (yoneda.obj U).map f₁.op (s.1 I₁) =
              (yoneda.obj U).map f₂.op (s.1 I₂) := by
          simpa [hf₁, hf₂] using s.2 I₁ I₂ _ f₁ f₂ (by rw [hf₁, hf₂])
        have h₃ :
            (yoneda.obj U).map f₂.op (s.1 I₂) =
              over_fiber_to_hom U Y
                (((canonicalFiberPseudofunctor (Over.forget U)).map f₂.op.toLoc).toFunctor.obj
                  (Functor.Fiber.mk (a := Over.mk (s.1 I₂)) rfl)) := by
          simpa [over_fiber_to_hom_fiber_mk_over_mk] using
            (over_pseudofunctor_map_obj_hom_eq_comp
              (U := U) (f := f₂) (a := Functor.Fiber.mk (a := Over.mk (s.1 I₂)) rfl)).symm
        apply eqToHom
        apply over_fiber_eq_of_hom_eq (U := U)
        exact h₁.trans (h₂.trans h₃)
      pullHom_hom := by
        intro Y' Y g q q' hq I₁ I₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
        exact (over_fiber_hom_subsingleton _ _).elim _ _
      hom_self := by
        intro Y q I g hg
        exact (over_fiber_hom_subsingleton _ _).elim _ _
      hom_comp := by
        intro Y q I₁ I₂ I₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
        exact (over_fiber_hom_subsingleton _ _).elim _ _ }
  have hInverse : ∀ s : compat, compatOfDescent (descentOfCompat s) = s := by
    intro s
    apply Subtype.ext
    funext I
    simp [compatOfDescent, descentOfCompat, over_fiber_to_hom_fiber_mk_over_mk]
  have hObjEq :
      ∀ (D : DD) (I : S.Arrow),
        D.obj I = (descentOfCompat (compatOfDescent D)).obj I := by
    intro D I
    apply over_fiber_eq_of_hom_eq (U := U)
    simp [compatOfDescent, descentOfCompat, over_fiber_to_hom_fiber_mk_over_mk]
  let H : Discrete compat ⥤ DD := by
    refine
      { obj := fun s ↦ descentOfCompat s.as
        map := fun {s t} φ ↦
          eqToHom
            (congrArg (fun x : Discrete compat ↦ descentOfCompat x.as)
              (obj_ext_of_isDiscrete φ))
        map_id := ?_
        map_comp := ?_ }
    · intro s
      exact (hHomSub _ _).elim _ _
    · intro s t u φ ψ
      exact (hHomSub _ _).elim _ _
  let E : DD ≌ Discrete compat :=
    { functor := G
      inverse := H
      unitIso := by
        refine NatIso.ofComponents (fun D ↦ ?_) ?_
        · refine Pseudofunctor.DescentData.isoMk (fun I ↦ ?_) ?_
          · exact eqToIso (hObjEq D I)
          · intro Y q I₁ I₂ f₁ f₂ hf₁ hf₂
            exact (over_fiber_hom_subsingleton _ _).elim _ _
        · intro D₁ D₂ φ
          exact (hHomSub _ _).elim _ _
      counitIso := by
        refine Discrete.natIso ?_
        intro s
        apply eqToIso
        simp [G, H, hInverse] }
  let K : ((Over.forget U).Fiber V) ⥤ Discrete compat := by
    refine
      { obj := fun a ↦
          Discrete.mk (Presieve.Arrows.toCompatible (yoneda.obj U) (fun I : S.Arrow ↦ I.f)
            (over_fiber_to_hom U V a))
        map := fun {a b} φ ↦ ?_
        map_id := ?_
        map_comp := ?_ }
    · apply eqToHom
      apply congrArg Discrete.mk
      apply congrArg (Presieve.Arrows.toCompatible (yoneda.obj U) (fun I : S.Arrow ↦ I.f))
      exact over_fiber_to_hom_eq_of_hom φ
    · intro a
      exact Subsingleton.elim _ _
    · intro a b c φ ψ
      exact Subsingleton.elim _ _
  letI : IsDiscrete ((Over.forget U).Fiber V) :=
    { subsingleton := fun a b ↦ over_fiber_hom_subsingleton a b
      eq_of_hom := fun φ ↦ over_fiber_eq_of_hom_eq (over_fiber_to_hom_eq_of_hom φ) }
  have hIso :
      (((canonicalFiberPseudofunctor (Over.forget U)).toDescentData
          (fun I : S.Arrow ↦ I.f)) ⋙ G) ≅ K := by
    refine NatIso.ofComponents (fun a ↦ ?_) ?_
    · apply eqToIso
      apply congrArg Discrete.mk
      apply Subtype.ext
      funext I
      simpa [compatOfDescent] using
        over_pseudofunctor_map_obj_hom_eq_comp (U := U) (f := I.f) (a := a)
    · intro a b φ
      exact Subsingleton.elim _ _
  let Kobj' : ((Over.forget U).Fiber V) → compat := fun a ↦
    Presieve.Arrows.toCompatible (yoneda.obj U) (fun I : S.Arrow ↦ I.f) (over_fiber_to_hom U V a)
  have hDiscreteMk :
      Function.Bijective (fun s : compat ↦ (Discrete.mk s : Discrete compat)) := by
    constructor
    · intro s t hst
      cases hst
      rfl
    · intro s
      exact ⟨s.as, by cases s; rfl⟩
  have hObjBijDiscrete :
      Function.Bijective K.obj ↔ Function.Bijective Kobj' := by
    simpa [K, Kobj', Function.comp] using
      (Function.Bijective.of_comp_iff' hDiscreteMk Kobj')
  have hObjBijFiber :
      Function.Bijective Kobj' ↔
        Function.Bijective (Presieve.Arrows.toCompatible (yoneda.obj U) (fun I : S.Arrow ↦ I.f)) := by
    convert
      (Function.Bijective.of_comp_iff
        (f := Presieve.Arrows.toCompatible (yoneda.obj U) (fun I : S.Arrow ↦ I.f))
        (g := over_fiber_to_hom U V)
        (over_fiber_to_hom_bijective U V)) using 1
  have hObjBij :
      Function.Bijective K.obj ↔
        Function.Bijective (Presieve.Arrows.toCompatible (yoneda.obj U) (fun I : S.Arrow ↦ I.f)) :=
    hObjBijDiscrete.trans hObjBijFiber
  have hDiscrete :
      K.IsEquivalence ↔
        Function.Bijective (Presieve.Arrows.toCompatible (yoneda.obj U) (fun I : S.Arrow ↦ I.f)) := by
    rw [isEquivalence_iff_bijective_obj_of_isDiscrete (G := K), hObjBij]
  have hCompare :
      ((canonicalFiberPseudofunctor (Over.forget U)).toDescentData
          (fun I : S.Arrow ↦ I.f)).IsEquivalence ↔
        K.IsEquivalence := by
    constructor
    · intro hΦ
      let _ :
          ((canonicalFiberPseudofunctor (Over.forget U)).toDescentData
            (fun I : S.Arrow ↦ I.f)).IsEquivalence := hΦ
      let _ : G.IsEquivalence := E.isEquivalence_functor
      have hComp :
          ((((canonicalFiberPseudofunctor (Over.forget U)).toDescentData
              (fun I : S.Arrow ↦ I.f))) ⋙ G).IsEquivalence :=
        by infer_instance
      exact (Functor.isEquivalence_iff_of_iso hIso).1 hComp
    · intro hK
      let _ : K.IsEquivalence := hK
      have hComp :
          ((((canonicalFiberPseudofunctor (Over.forget U)).toDescentData
              (fun I : S.Arrow ↦ I.f))) ⋙ G).IsEquivalence :=
        (Functor.isEquivalence_iff_of_iso hIso).2 hK
      let _ : G.IsEquivalence := E.isEquivalence_functor
      exact Functor.isEquivalence_of_comp_right
        ((canonicalFiberPseudofunctor (Over.forget U)).toDescentData
          (fun I : S.Arrow ↦ I.f)) G
  -- The comparison reduces stack descent to the ordinary compatible-family bijection defining
  -- sheafness for this generated cover.
  rw [hCompare, hDiscrete]
  rw [← S.ofArrows_eq, ← Presieve.isSheafFor_iff_generate]
  exact
    (Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible
      (P := yoneda.obj U) (π := fun I : S.Arrow ↦ I.f)).symm

/-- Helper for Chap08 Lemma 8 13 2: the slice projection is a stack exactly when the
representable presheaf it represents is a sheaf. -/
private theorem over_forget_isStackOnSite_iff_representable_isSheaf
    (J : GrothendieckTopology C) (U : C) :
    IsStackOnSite J (Over.forget U) ↔ Presheaf.IsSheaf J (yoneda.obj U) := by
  -- Use the coverwise stack criterion and the fixed-cover comparison with compatible families of
  -- arrows to `U`.
  rw [isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence]
  constructor
  · intro h
    rw [isSheaf_iff_isSheaf_of_type]
    intro V R hR
    let S : J.Cover V := ⟨R, hR⟩
    exact
      (over_cover_toDescentData_isEquivalence_iff_isSheafFor
        (J := J) (U := U) (V := V) S).1 (h V S)
  · intro h V S
    have hS : Presieve.IsSheafFor (yoneda.obj U) ((S : Sieve V).arrows) := by
      exact h.isSheafFor (S : Sieve V) S.condition
    exact
      (over_cover_toDescentData_isEquivalence_iff_isSheafFor
        (J := J) (U := U) (V := V) S).2 hS

/- Domain-style sampling for Lemma 8.13.2:
- primary domain: stacks over a site, localization of a site at `U`, and the slice strict
  `2`-category over the representable stack `C/U`.
- inspected owner-level declarations:
  `StackOver`,
  `StackOver.ofProjection`,
  `SliceTwoCategory`,
  `FibredCategoryMor.ofBasedFunctor`,
  `StrictPseudofunctor.IsInverse`.
- best owner abstraction: the localized side should use the chapter owner `StackOver (J.over U)`
  directly, and the two source constructions should be packaged as strict pseudofunctors between
  `StackOver (J.over U)` and `SliceTwoCategory (sliceStackOver J U hU)`.
- primitive data: the projection functors produced by Constructions A and B together with the
  stack-on-site proofs for those projections.
- derived API: the bundled `StackOver` objects, their induced slice morphisms, and the inverse
  package `StrictPseudofunctor.IsInverse`.

Source/core/bridge triage:
- `source-facing`: `localizedStacksToSlice`, `sliceToLocalizedStacks`,
  `localizedStacks_equivalent_to_stacks_with_map_to_slice`.
- `core/canonical`: `StackOver`, `StackOver.ofProjection`, `SliceTwoCategory`,
  `FibredCategoryMor.ofBasedFunctor`, `StrictPseudofunctor.IsInverse`.
- `bridge/view`: the representable stack `sliceStackOver` and the private bundled object
  conversions used by Constructions A and B. -/

/-- If the representable presheaf `h_U` is a sheaf on `(C, J)`, then the slice fibred category
`C/U` defines the corresponding representable stack over `(C, J)`. -/
abbrev sliceStackOver
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) : StackOver J :=
  let p : Over U ⥤ C := Over.forget U
  letI : IsStackOnSite J p := by
    simpa [p] using (over_forget_isStackOnSite_iff_representable_isSheaf J U).2 hU
  ⟨FibredCategoryOver.ofFunctor p, by
    simpa [FibredCategoryOver.p, FibredCategoryOver.ofFunctor] using
      (inferInstance : IsStackOnSite J p)⟩

private abbrev sliceTwoHomToNatTrans
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : SliceTwoCategory (sliceStackOver J U hU)} {F G : X ⟶ Y}
    (η : F ⟶ G) :
    (toBasedFunctor F.hom).toFunctor ⟶ (toBasedFunctor G.hom).toFunctor :=
  stackTwoHomToNatTrans η.hom

/-- Helper for Chap08 Lemma 8 13 2: slice `2`-cells are determined by their ambient
`2`-cell component. -/
private theorem sliceTwoHom_eq_of_hom_eq
    {B : Type u₁} [Bicategory.{w₁, v₁} B] [Bicategory.Strict B]
    {X : B} {S T : SliceTwoCategory X} {F G : S ⟶ T}
    {η θ : F ⟶ G} (h : η.hom = θ.hom) : η = θ := by
  -- Strip the slice compatibility proof; the ambient component determines the `2`-cell.
  apply SliceTwoCategory.TwoHom.ext
  exact h

/-- Helper for Chap08 Lemma 8 13 2: stack `2`-cells are determined by their underlying
fibred-category `2`-cell. -/
private theorem stackTwoHom_eq_of_fibredCategoryMorTwoHom_eq
    {X Y : StackOver J} {F G : X ⟶ Y} {η θ : F ⟶ G}
    (h : stackTwoHomToFibredCategoryMorTwoHom η =
      stackTwoHomToFibredCategoryMorTwoHom θ) : η = θ := by
  -- Remove the wide-subcategory and full-subcategory proof wrappers around stack morphisms.
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  exact h

/-- Helper for Chap08 Lemma 8 13 2: stack `2`-cells are determined by their underlying
natural transformations. -/
private theorem stackTwoHom_eq_of_toNatTrans_eq
    {X Y : StackOver J} {F G : X ⟶ Y} {η θ : F ⟶ G}
    (h : stackTwoHomToNatTrans η = stackTwoHomToNatTrans θ) : η = θ := by
  -- First use the existing fibred-category extensionality bridge, then compare the based natural
  -- transformations by their ordinary natural-transformation fields.
  apply stackTwoHom_eq_of_fibredCategoryMorTwoHom_eq
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  exact BasedNatTrans.ext _ _ h

/-- Helper for Chap08 Lemma 8 13 2: slice `2`-cells are determined by their underlying
natural transformations. -/
private theorem sliceTwoHom_eq_of_toNatTrans_eq
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : SliceTwoCategory (sliceStackOver J U hU)} {F G : X ⟶ Y} {η θ : F ⟶ G}
    (h : sliceTwoHomToNatTrans J U hU η = sliceTwoHomToNatTrans J U hU θ) : η = θ := by
  -- The slice wrapper is determined by its ambient stack `2`-cell, and that ambient cell is
  -- determined by the same underlying natural transformation.
  apply sliceTwoHom_eq_of_hom_eq
  exact stackTwoHom_eq_of_toNatTrans_eq (J := J) h

/-- Helper for Chap08 Lemma 8 13 2: whiskering a `2`-cell by equality transports of the source
and target objects is heterogeneously the original `2`-cell. -/
private theorem twoHom_eqToHom_whisker_heq
    {B : Type u₁} [Bicategory.{w₁, v₁} B] [Bicategory.Strict B]
    {X X' Y Y' : B} (hx : X' = X) (hy : Y' = Y)
    {F G : X ⟶ Y} (η : F ⟶ G) :
    ((eqToHom hx ◁ η) ▷ eqToHom hy.symm) ≍ η := by
  subst hx
  subst hy
  simp [Bicategory.id_whiskerLeft, Bicategory.whiskerRight_id,
    Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso]

/-- Helper for Chap08 Lemma 8 13 2: equality transport between slice objects has the expected
ambient hom component. -/
private theorem sliceObject_eqToHom_hom
    {B : Type u₁} [Bicategory.{w₁, v₁} B] [Bicategory.Strict B]
    {X : B} {S T : SliceTwoCategory X} (h : S = T) :
    (eqToHom h : S ⟶ T).hom = eqToHom (congrArg SliceTwoCategory.obj h) := by
  -- Eliminate the slice-object equality; both equality transports are identities.
  subst h
  rfl

/-- Helper for Chap08 Lemma 8 13 2: composition in a slice hom category composes the
ambient hom components. -/
private theorem sliceHom_comp_hom
    {B : Type u₁} [Bicategory.{w₁, v₁} B] [Bicategory.Strict B]
    {X : B} {S T V : SliceTwoCategory X} (F : S ⟶ T) (G : T ⟶ V) :
    (F ≫ G).hom = F.hom ≫ G.hom := by
  -- This is the defining component of slice hom composition.
  rfl

/-- Helper for Chap08 Lemma 8 13 2: compatible local arrows to `U` over a `J`-cover glue
uniquely to a global arrow to `U`. -/
private theorem representableArrowUniqueAmalgamation
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {V : C} (S : J.Cover V)
    (a : ∀ I : S.Arrow, I.Y ⟶ U)
    (ha : Presieve.Arrows.Compatible (yoneda.obj U) (fun I : S.Arrow => I.f) a) :
    ∃! u : V ⟶ U, ∀ I, I.f ≫ u = a I := by
  -- Use the coverwise sheaf condition for the representable presheaf, then translate it to the
  -- explicit bijectivity statement for families indexed by the cover arrows.
  have hSheafFor : Presieve.IsSheafFor (yoneda.obj U)
      (Presieve.ofArrows (fun I : S.Arrow => I.Y) fun I => I.f) := by
    rw [Presieve.isSheafFor_iff_generate]
    simpa [S.ofArrows_eq] using hU.isSheafFor (S : Sieve V) S.condition
  have hbij :
      Function.Bijective
        (Presieve.Arrows.toCompatible (yoneda.obj U) (fun I : S.Arrow => I.f)) :=
    (Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible
      (P := yoneda.obj U) (π := fun I : S.Arrow => I.f)).1 hSheafFor
  -- Surjectivity gives the glued arrow, and injectivity gives the required uniqueness.
  rcases hbij.2 ⟨a, ha⟩ with ⟨u, hu⟩
  refine ⟨u, ?_, ?_⟩
  · intro I
    exact congr_fun (congrArg Subtype.val hu) I
  · intro u' hu'
    apply hbij.1
    ext I
    exact (hu' I).trans (congr_fun (congrArg Subtype.val hu) I).symm

/-- Helper for Chap08 Lemma 8 13 2: two arrows to `U` with the same compatible restrictions
over a cover are equal. -/
private theorem representableArrowAmalgamation_eq
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {V : C} (S : J.Cover V)
    {a : ∀ I : S.Arrow, I.Y ⟶ U}
    (ha : Presieve.Arrows.Compatible (yoneda.obj U) (fun I : S.Arrow => I.f) a)
    {u v : V ⟶ U}
    (hu : ∀ I, I.f ≫ u = a I)
    (hv : ∀ I, I.f ≫ v = a I) :
    u = v := by
  -- Apply the representable sheaf uniqueness statement and compare both arrows with the same
  -- glued amalgamation.
  rcases representableArrowUniqueAmalgamation (J := J) (U := U) hU S a ha with
    ⟨w, _hw, huniq⟩
  exact (huniq u hu).trans (huniq v hv).symm

/-- Helper for Chap08 Lemma 8 13 2: two arrows to `U` with the same compatible restrictions
along a covering family of arrows are equal. -/
private theorem representableArrowAmalgamation_eq_ofArrows
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {ι : Type*} {V : C} {Y : ι → C} {f : ∀ i, Y i ⟶ V}
    (hcover : Sieve.ofArrows Y f ∈ J V)
    {a : ∀ i, Y i ⟶ U}
    {u v : V ⟶ U}
    (hu : ∀ i, f i ≫ u = a i)
    (hv : ∀ i, f i ≫ v = a i) :
    u = v := by
  -- Use the same representable sheaf bijection as above, but keep the original family index.
  have hSheafFor : Presieve.IsSheafFor (yoneda.obj U) (Presieve.ofArrows Y f) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hU.isSheafFor (Sieve.ofArrows Y f) hcover
  have hbij :
      Function.Bijective (Presieve.Arrows.toCompatible (yoneda.obj U) f) :=
    (Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible
      (P := yoneda.obj U) (π := f)).1 hSheafFor
  apply hbij.1
  apply Subtype.ext
  funext i
  exact (hu i).trans (hv i).symm

/-- Helper for Chap08 Lemma 8 13 2: a cover of `V` induces a cover of `V/U`
in the slice topology. -/
private theorem overCoverOfBaseCover
    {V : C} (S : J.Cover V) (u : V ⟶ U) :
    Sieve.ofArrows (fun I : S.Arrow => Over.mk (I.f ≫ u))
      (fun I => Over.homMk I.f) ∈ (J.over U) (Over.mk u) := by
  -- Move the covering claim to the base category and identify the generated base sieve.
  rw [GrothendieckTopology.mem_over_iff]
  have hEq :
      Sieve.overEquiv (Over.mk u)
        (Sieve.ofArrows (fun I : S.Arrow => Over.mk (I.f ≫ u))
          (fun I => Over.homMk I.f)) =
        Sieve.ofArrows (fun I : S.Arrow => I.Y) (fun I => I.f) := by
    ext Z g
    rw [Sieve.overEquiv_iff, Sieve.mem_ofArrows_iff, Sieve.mem_ofArrows_iff]
    constructor
    · rintro ⟨I, h, hfac⟩
      refine ⟨I, h.left, ?_⟩
      exact congrArg (fun k => k.left) hfac
    · rintro ⟨I, h, hfac⟩
      refine ⟨I, Over.homMk h ?_, ?_⟩
      · simp [hfac, Category.assoc]
      · ext
        exact hfac
  rw [hEq]
  rw [S.ofArrows_eq]
  exact S.condition

/-- Helper for Chap08 Lemma 8 13 2: the standard slice cover induced by a base cover and
an arrow to `U`. -/
private abbrev standardSliceCover
    {V : C} (T : J.Cover V) (u : V ⟶ U) :
    (J.over U).Cover (Over.mk u) :=
  ⟨Sieve.ofArrows (fun I : T.Arrow => Over.mk (I.f ≫ u))
      (fun I => Over.homMk (U := Over.mk (I.f ≫ u)) (V := Over.mk u) I.f),
    overCoverOfBaseCover (J := J) (U := U) T u⟩

/-- Helper for Chap08 Lemma 8 13 2: the arrows of the standard slice cover generate the
standard slice sieve. -/
private theorem standardSliceCover_slice_sieve_eq
    {V : C} (T : J.Cover V) (u : V ⟶ U) :
    Sieve.ofArrows (fun I : T.Arrow => Over.mk (I.f ≫ u))
        (fun I => Over.homMk (U := Over.mk (I.f ≫ u)) (V := Over.mk u) I.f) =
      Sieve.ofArrows
        (fun K : (standardSliceCover (J := J) (U := U) T u).Arrow => K.Y)
        (fun K => K.f) := by
  rw [(standardSliceCover (J := J) (U := U) T u).ofArrows_eq]

/-- Helper for Chap08 Lemma 8 13 2: after forgetting the slice coordinate, the arrows of the
standard slice cover generate the original base cover. -/
private theorem standardSliceCover_left_sieve_eq
    {V : C} (T : J.Cover V) (u : V ⟶ U) :
    Sieve.ofArrows
        (fun K : (standardSliceCover (J := J) (U := U) T u).Arrow => K.Y.left)
        (fun K => K.f.left) =
      Sieve.ofArrows (fun I : T.Arrow => I.Y) (fun I => I.f) := by
  ext Z g
  rw [Sieve.mem_ofArrows_iff, Sieve.mem_ofArrows_iff]
  constructor
  · rintro ⟨K, h, hfac⟩
    have hK :
        (Sieve.ofArrows (fun I : T.Arrow => Over.mk (I.f ≫ u))
          (fun I => Over.homMk (U := Over.mk (I.f ≫ u)) (V := Over.mk u) I.f)).arrows
            K.f := by
      exact K.hf
    rw [Sieve.mem_ofArrows_iff] at hK
    rcases hK with ⟨I, k, hk⟩
    refine ⟨I, h ≫ k.left, ?_⟩
    have hkleft : K.f.left = k.left ≫ I.f := by
      exact congrArg (fun a => a.left) hk
    have hmiddle : h ≫ K.f.left = h ≫ (k.left ≫ I.f) := by
      exact congrArg (fun a => h ≫ a) hkleft
    have hassoc : h ≫ (k.left ≫ I.f) = (h ≫ k.left) ≫ I.f := by
      exact (Category.assoc h k.left I.f).symm
    exact hfac.trans (hmiddle.trans hassoc)
  · rintro ⟨I, h, hfac⟩
    let K : (standardSliceCover (J := J) (U := U) T u).Arrow :=
      ⟨Over.mk (I.f ≫ u),
        Over.homMk (U := Over.mk (I.f ≫ u)) (V := Over.mk u) I.f,
        by
          change
            (Sieve.ofArrows (fun I : T.Arrow => Over.mk (I.f ≫ u))
              (fun I => Over.homMk (U := Over.mk (I.f ≫ u)) (V := Over.mk u) I.f)).arrows
                (Over.homMk (U := Over.mk (I.f ≫ u)) (V := Over.mk u) I.f)
          rw [Sieve.mem_ofArrows_iff]
          refine ⟨I, 𝟙 _, ?_⟩
          rw [Category.id_comp]⟩
    refine ⟨K, h, ?_⟩
    exact hfac

/-- Helper for Chap08 Lemma 8 13 2: a base-cover arrow as an arrow of the standard
slice cover. -/
private abbrev standardSliceCoverArrowOfBaseArrow
    {V : C} (T : J.Cover V) (u : V ⟶ U) (I : T.Arrow) :
    (standardSliceCover (J := J) (U := U) T u).Arrow :=
  ⟨Over.mk (I.f ≫ u),
    Over.homMk (U := Over.mk (I.f ≫ u)) (V := Over.mk u) I.f,
    by
      change
        (Sieve.ofArrows (fun I : T.Arrow => Over.mk (I.f ≫ u))
          (fun I => Over.homMk (U := Over.mk (I.f ≫ u)) (V := Over.mk u) I.f)).arrows
            (Over.homMk (U := Over.mk (I.f ≫ u)) (V := Over.mk u) I.f)
      rw [Sieve.mem_ofArrows_iff]
      refine ⟨I, 𝟙 _, ?_⟩
      rw [Category.id_comp]⟩

private theorem standardSliceCoverArrowOfBaseArrow_left
    {V : C} (T : J.Cover V) (u : V ⟶ U) (I : T.Arrow) :
    (standardSliceCoverArrowOfBaseArrow (J := J) (U := U) T u I).f.left = I.f := by
  rfl

/-- Helper for Chap08 Lemma 8 13 2: every arrow of the standard slice cover factors, after
forgetting to `C`, through an arrow of the original base cover. -/
private theorem standardSliceCoverBaseFactor_exists
    {V : C} (T : J.Cover V) (u : V ⟶ U)
    (K : (standardSliceCover (J := J) (U := U) T u).Arrow) :
    ∃ (I : T.Arrow) (g : K.Y.left ⟶ I.Y), g ≫ I.f = K.f.left := by
  have hmem :
      Sieve.ofArrows (fun I : T.Arrow => I.Y) (fun I => I.f) K.f.left := by
    rw [← standardSliceCover_left_sieve_eq (J := J) (U := U) T u]
    rw [Sieve.mem_ofArrows_iff]
    refine ⟨K, 𝟙 _, ?_⟩
    rw [Category.id_comp]
  rw [Sieve.mem_ofArrows_iff] at hmem
  rcases hmem with ⟨I, g, hg⟩
  exact ⟨I, g, hg.symm⟩

private noncomputable def standardSliceCoverBaseFactorIndex
    {V : C} (T : J.Cover V) (u : V ⟶ U)
    (K : (standardSliceCover (J := J) (U := U) T u).Arrow) : T.Arrow :=
  Classical.choose (standardSliceCoverBaseFactor_exists (J := J) (U := U) T u K)

private noncomputable def standardSliceCoverBaseFactorHom
    {V : C} (T : J.Cover V) (u : V ⟶ U)
    (K : (standardSliceCover (J := J) (U := U) T u).Arrow) :
    K.Y.left ⟶ (standardSliceCoverBaseFactorIndex (J := J) (U := U) T u K).Y :=
  Classical.choose
    (Classical.choose_spec
      (standardSliceCoverBaseFactor_exists (J := J) (U := U) T u K))

private theorem standardSliceCoverBaseFactor_fac
    {V : C} (T : J.Cover V) (u : V ⟶ U)
    (K : (standardSliceCover (J := J) (U := U) T u).Arrow) :
    standardSliceCoverBaseFactorHom (J := J) (U := U) T u K ≫
        (standardSliceCoverBaseFactorIndex (J := J) (U := U) T u K).f =
      K.f.left :=
  Classical.choose_spec
    (Classical.choose_spec
      (standardSliceCoverBaseFactor_exists (J := J) (U := U) T u K))

/-- Helper for Chap08 Lemma 8 13 2: generating after `functorPushforward` agrees with
generating after the direct presieve image. -/
private theorem Sieve.generate_functorPushforward_eq_generate_map
    {D : Type*} [Category D] {F : C ⥤ D} {X : C} (R : Presieve X) :
    Sieve.generate (R.functorPushforward F) = Sieve.generate (R.map F) := by
  -- Compare the arrow predicates of the generated image sieve with the functor-pushforward
  -- predicate, then regenerate the sieve.
  rw [← Sieve.arrows_generate_map_eq_functorPushforward (F := F) (s := R),
    Sieve.generate_sieve]

/-- Helper for Chap08 Lemma 8 13 2: inherited covers for `Over.forget U` are covers in the
slice topology. -/
private theorem overForget_inheritedTopology_le_over
    (J : GrothendieckTopology C) (U : C) :
    (stronglyCartesianLiftPrecoverage J.toPrecoverage (Over.forget U)).toGrothendieck ≤
      J.over U := by
  -- Check the generators of the inherited topology; their images under `Sieve.overEquiv` are
  -- exactly the generated base presieves already known to cover for `J`.
  rw [Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
  intro Y R hR
  rw [GrothendieckTopology.mem_toPrecoverage_iff, GrothendieckTopology.mem_over_iff]
  obtain ⟨ι, A, f, hRdef, _hstrong, hbase⟩ := hR
  subst R
  rw [Sieve.overEquiv_generate]
  rw [GrothendieckTopology.mem_toPrecoverage_iff] at hbase
  have hrewrite :
      Sieve.generate (Presieve.functorPushforward (Over.forget U) (Presieve.ofArrows A f)) =
        Sieve.generate ((Presieve.ofArrows A f).map (Over.forget U)) :=
    Sieve.generate_functorPushforward_eq_generate_map
      (F := Over.forget U) (R := Presieve.ofArrows A f)
  change Sieve.generate (Presieve.functorPushforward (Over.forget U) (Presieve.ofArrows A f)) ∈
    J ((Over.forget U).obj Y)
  rw [hrewrite]
  simpa [Function.comp_def, Presieve.map_ofArrows] using hbase

/-- Helper for Chap08 Lemma 8 13 2: every slice cover is generated by strongly cartesian arrows
for `Over.forget U`. -/
private theorem over_le_overForget_inheritedTopology
    (J : GrothendieckTopology C) (U : C) :
    J.over U ≤
      (stronglyCartesianLiftPrecoverage J.toPrecoverage (Over.forget U)).toGrothendieck := by
  -- Represent the slice sieve by arrows. Since `Over.forget U` is fibred in groupoids, all these
  -- arrows are strongly cartesian, and their base image is the given `Sieve.overEquiv` cover.
  intro Y S hS
  rw [GrothendieckTopology.mem_over_iff] at hS
  obtain ⟨ι, A, f, hSdef⟩ := S.arrows.exists_eq_ofArrows
  have hpre : S.arrows ∈ stronglyCartesianLiftPrecoverage J.toPrecoverage (Over.forget U) Y := by
    rw [hSdef]
    refine (ofArrows_mem_stronglyCartesianLiftPrecoverage_iff
      (J := J.toPrecoverage) (p := Over.forget U) A f).2 ⟨?_, ?_⟩
    · intro i
      exact (inferInstance : IsFibredInGroupoids (Over.forget U)).isStronglyCartesian_map (f i)
    · rw [GrothendieckTopology.mem_toPrecoverage_iff]
      have hgen : Sieve.generate (Presieve.ofArrows A f) = S := by
        simp [← hSdef]
      have hbaseEq :
          Sieve.generate
              (Presieve.ofArrows ((Over.forget U).obj ∘ A)
                (fun i => (Over.forget U).map (f i))) =
            Sieve.overEquiv Y S := by
        calc
          Sieve.generate
              (Presieve.ofArrows ((Over.forget U).obj ∘ A)
                (fun i => (Over.forget U).map (f i))) =
              Sieve.generate ((Presieve.ofArrows A f).map (Over.forget U)) := by
            simp [Function.comp_def, Presieve.map_ofArrows]
          _ = Sieve.generate ((Presieve.ofArrows A f).functorPushforward (Over.forget U)) := by
            exact (Sieve.generate_functorPushforward_eq_generate_map
              (F := Over.forget U) (R := Presieve.ofArrows A f)).symm
          _ = Sieve.overEquiv Y (Sieve.generate (Presieve.ofArrows A f)) := by
            exact (Sieve.overEquiv_generate (Y := Y) (R := Presieve.ofArrows A f)).symm
          _ = Sieve.overEquiv Y S := by
            rw [hgen]
      rwa [hbaseEq]
  simpa [Sieve.generate_sieve] using
    (Precoverage.generate_mem_toGrothendieck
      (J := stronglyCartesianLiftPrecoverage J.toPrecoverage (Over.forget U)) hpre)

/-- Helper for Chap08 Lemma 8 13 2: the topology inherited by `Over.forget U` is the usual slice
topology. -/
private theorem overForget_inheritedTopology_eq_over
    (J : GrothendieckTopology C) (U : C) :
    (stronglyCartesianLiftPrecoverage J.toPrecoverage (Over.forget U)).toGrothendieck =
      J.over U := by
  -- Combine the two topology inclusions to get the exact transport lemma needed below.
  exact le_antisymm (overForget_inheritedTopology_le_over J U)
    (over_le_overForget_inheritedTopology J U)

/-- Helper for Chap08 Lemma 8 13 2: the inherited topology of the representable slice stack is
the usual slice topology. -/
private theorem sliceStackOver_inheritedTopology_eq_over
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    (stronglyCartesianLiftPrecoverage
        J.toPrecoverage (sliceStackOver J U hU).toFibredCategoryOver.p).toGrothendieck =
      J.over U := by
  -- Put the representable stack projection in the same spelling as the slice projection bridge.
  simpa [sliceStackOver, FibredCategoryOver.p, FibredCategoryOver.ofFunctor] using
    overForget_inheritedTopology_eq_over J U

/-- Helper for Chap08 Lemma 8 13 2: stackness over the slice topology is the same stackness
over the topology inherited from the slice projection. -/
private theorem overForgetInheritedTopology_isStackOnSite
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [IsStackOnSite (J.over U) q] :
    IsStackOnSite
      ((stronglyCartesianLiftPrecoverage J.toPrecoverage (Over.forget U)).toGrothendieck) q := by
  -- Transport the localized stack condition across the equality of the inherited and slice
  -- topologies.
  simpa [overForget_inheritedTopology_eq_over J U] using
    (inferInstance : IsStackOnSite (J.over U) q)

/-- Helper for Chap08 Lemma 8 13 2: localized stackness transports to the topology inherited by
the representable slice stack projection. -/
private theorem sliceStackOverInheritedTopology_isStackOnSite
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {S : Type*} [Category S] (q : S ⥤ (sliceStackOver J U hU).toFibredCategoryOver.S)
    [IsStackOnSite (J.over U) q] :
    IsStackOnSite
      ((stronglyCartesianLiftPrecoverage
        J.toPrecoverage (sliceStackOver J U hU).toFibredCategoryOver.p).toGrothendieck) q := by
  -- Rewrite the representable stack projection to the literal slice projection, then reuse the
  -- transport bridge for `Over.forget U`.
  simpa [sliceStackOver, FibredCategoryOver.p, FibredCategoryOver.ofFunctor] using
    overForgetInheritedTopology_isStackOnSite J U q

/-- Helper for Chap08 Lemma 8 13 2: a localized-stack projection remains fibred after
composing with the slice forgetful projection. -/
private theorem compOverForget_isFibered
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [IsStackOnSite (J.over U) q] :
    (q ⋙ Over.forget U).IsFibered := by
  -- The stack condition supplies fibredness of `q`; Lemma 4.33.12 composes it with the
  -- canonical fibred-in-groupoids structure on the slice projection.
  infer_instance

/-- Helper for Chap08 Lemma 8 13 2: a hom-lift for a composite projection gives a hom-lift
after projecting to the slice forgetful functor. -/
private theorem isHomLift_overForget_of_comp_isHomLift
    {S : Type*} [Category S] (q : S ⥤ Over U)
    {Y Z : C} {a b : S} {f : Y ⟶ Z} {h : a ⟶ b}
    (hh : Functor.IsHomLift (q ⋙ Over.forget U) f h) :
    Functor.IsHomLift (Over.forget U) f (q.map h) := by
  -- Reuse the endpoint equalities and factorization stored in the composite hom-lift.
  letI : (q ⋙ Over.forget U).IsHomLift f h := hh
  let ha := IsHomLift.domain_eq (q ⋙ Over.forget U) f h
  let hb := IsHomLift.codomain_eq (q ⋙ Over.forget U) f h
  refine IsHomLift.of_fac (Over.forget U) f (q.map h) ha hb ?_
  simpa [Functor.comp_map] using IsHomLift.fac (q ⋙ Over.forget U) f h

/-- Helper for Chap08 Lemma 8 13 2: a strongly cartesian morphism can be rebased to its
owner-level mapped arrow. -/
private theorem isStronglyCartesian_rebase_to_map
    {D : Type u₁} {E : Type u₂} [Category.{v₁} D] [Category.{v₂} E]
    (p : E ⥤ D) {R S : D} {a b : E} {f : R ⟶ S} (φ : a ⟶ b)
    [p.IsStronglyCartesian f φ] :
    p.IsStronglyCartesian (p.map φ) φ := by
  -- The strong-cartesian structure includes a hom-lift witness, so both endpoints and then the
  -- arrow itself can be normalized to `p.map φ`.
  have ha : p.obj a = R := IsHomLift.domain_eq p f φ
  have hb : p.obj b = S := IsHomLift.codomain_eq p f φ
  subst ha
  subst hb
  have hf : f = p.map φ := IsHomLift.eq_of_isHomLift p f φ
  subst hf
  infer_instance

/-- Helper for Chap08 Lemma 8 13 2: a strongly cartesian arrow rebased to its owner-level map
can be transported back to any hom-lift base for the same arrow. -/
private theorem isStronglyCartesian_rebase_of_isHomLift
    {D : Type u₁} {E : Type u₂} [Category.{v₁} D] [Category.{v₂} E]
    (p : E ⥤ D) {R S : D} {a b : E} {f : R ⟶ S} (φ : a ⟶ b)
    [p.IsStronglyCartesian (p.map φ) φ] (h : p.IsHomLift f φ) :
    p.IsStronglyCartesian f φ := by
  letI : p.IsHomLift f φ := h
  have ha : p.obj a = R := IsHomLift.domain_eq p f φ
  have hb : p.obj b = S := IsHomLift.codomain_eq p f φ
  subst ha
  subst hb
  have hf : f = p.map φ := IsHomLift.eq_of_isHomLift p f φ
  subst hf
  infer_instance

/-- Helper for Chap08 Lemma 8 13 2: composing a projection with another functor sends a hom-lift
to a hom-lift for the composite projection. -/
private theorem isHomLift_comp_of_isHomLift_for_boundary
    {D E S : Type*} [Category D] [Category E] [Category S]
    (p : S ⥤ D) (q : D ⥤ E)
    {a b : S} {R T : D} {f : R ⟶ T} {φ : a ⟶ b}
    (h : p.IsHomLift f φ) :
    (p ⋙ q).IsHomLift (q.map f) φ := by
  letI : p.IsHomLift f φ := h
  let ha := IsHomLift.domain_eq p f φ
  let hb := IsHomLift.codomain_eq p f φ
  refine IsHomLift.of_fac (p ⋙ q) (q.map f) φ (congrArg q.obj ha) (congrArg q.obj hb) ?_
  calc
    q.map f = q.map (eqToHom ha.symm ≫ p.map φ ≫ eqToHom hb) := by
      rw [IsHomLift.fac p f φ]
    _ = eqToHom (congrArg q.obj ha).symm ≫ (p ⋙ q).map φ ≫
        eqToHom (congrArg q.obj hb) := by
      simp [Functor.map_comp, CategoryTheory.eqToHom_map]

/-- Helper for Chap08 Lemma 8 13 2: a morphism in a composite fiber preserves the
remembered arrow to `U`. -/
private theorem compositeFiberArrowToU_eq_of_hom
    {S : Type*} [Category S] (q : S ⥤ Over U) {V : C}
    {a b : (q ⋙ Over.forget U).Fiber V} (h : a ⟶ b) :
    compositeFiberArrowToU (U := U) q a = compositeFiberArrowToU (U := U) q b := by
  -- A fiber morphism is a hom-lift over the identity; the composite-arrow normal form then
  -- reduces the right-hand side by the identity law.
  have hcomp :=
    compositeFiberArrowToU_eq_comp_of_isHomLift (U := U) q
      (a := a) (b := b) (f := 𝟙 V) (h := Functor.Fiber.fiberInclusion.map h) h.2
  simpa using hcomp

/-- Helper for Chap08 Lemma 8 13 2: reindexing a composite fiber object precomposes its
remembered arrow to `U`. -/
private theorem composite_pseudofunctor_map_obj_arrow_eq_comp
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {Y Z : C} (f : Y ⟶ Z) (a : (q ⋙ Over.forget U).Fiber Z) :
    compositeFiberArrowToU (U := U) q
        (((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).map f.op.toLoc).toFunctor.obj a) =
      f ≫ compositeFiberArrowToU (U := U) q a := by
  -- Read the canonical pullback choice as a strongly cartesian hom-lift and apply the
  -- composite-arrow formula.
  let hc := canonicalPullbackChoice (q ⋙ Over.forget U)
  let φ := hc.map f a
  simpa using
    (compositeFiberArrowToU_eq_comp_of_isHomLift
      (U := U) q (a := ((hc.pullbackFunctor f).obj a)) (b := a) (f := f) (h := φ)
      ((hc.isStronglyCartesian f a).toIsHomLift))

/-- Helper for Chap08 Lemma 8 13 2: every composite descent datum determines compatible
local arrows to `U` over the base cover. -/
private theorem compDescentData_arrowsToU_compatible
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {V : C} (T : J.Cover V)
    (D : (canonicalFiberPseudofunctor (q ⋙ Over.forget U)).DescentData
      (fun I : T.Arrow ↦ I.f)) :
    Presieve.Arrows.Compatible (yoneda.obj U) (fun I : T.Arrow ↦ I.f)
      (fun I ↦ compositeFiberArrowToU (U := U) q (D.obj I)) := by
  -- Compare the two pullbacks supplied by the descent datum, then translate both sides to arrows
  -- to `U` using the reindexing normal form.
  intro I₁ I₂ Y g₁ g₂ h
  let r : Y ⟶ V := g₁ ≫ I₁.f
  have hg₁ : g₁ ≫ I₁.f = r := rfl
  have hg₂ : g₂ ≫ I₂.f = r := by
    simpa [r] using h.symm
  have hEq :
      compositeFiberArrowToU (U := U) q
          (((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).map g₁.op.toLoc).toFunctor.obj
            (D.obj I₁)) =
        compositeFiberArrowToU (U := U) q
          (((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).map g₂.op.toLoc).toFunctor.obj
            (D.obj I₂)) := by
    exact compositeFiberArrowToU_eq_of_hom (U := U) q (D.hom r g₁ g₂ hg₁ hg₂)
  have hg₁' :
      (yoneda.obj U).map g₁.op (compositeFiberArrowToU (U := U) q (D.obj I₁)) =
        compositeFiberArrowToU (U := U) q
          (((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).map g₁.op.toLoc).toFunctor.obj
            (D.obj I₁)) := by
    simpa using
      (composite_pseudofunctor_map_obj_arrow_eq_comp (U := U) q (f := g₁) (a := D.obj I₁)).symm
  have hg₂' :
      compositeFiberArrowToU (U := U) q
          (((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).map g₂.op.toLoc).toFunctor.obj
            (D.obj I₂)) =
        (yoneda.obj U).map g₂.op (compositeFiberArrowToU (U := U) q (D.obj I₂)) := by
    simpa using
      composite_pseudofunctor_map_obj_arrow_eq_comp (U := U) q (f := g₂) (a := D.obj I₂)
  exact hg₁'.trans (hEq.trans hg₂')

/-- Helper for Chap08 Lemma 8 13 2: a descent-data morphism preserves the local arrows to
`U` extracted from composite-fiber objects. -/
private theorem compDescentData_arrowsToU_eq_of_hom
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {V : C} {T : J.Cover V}
    {D E : (canonicalFiberPseudofunctor (q ⋙ Over.forget U)).DescentData
      (fun I : T.Arrow ↦ I.f)}
    (φ : D ⟶ E) (I : T.Arrow) :
    compositeFiberArrowToU (U := U) q (D.obj I) =
      compositeFiberArrowToU (U := U) q (E.obj I) := by
  -- The component of a descent-data morphism is a morphism in the corresponding composite fiber,
  -- so the fiber-arrow normal form applies directly.
  exact compositeFiberArrowToU_eq_of_hom (U := U) q (φ.hom I)

/-- Helper for Chap08 Lemma 8 13 2: an isomorphism of descent data gives componentwise
isomorphisms on the local objects. -/
private noncomputable def descentDataComponentIso
    {D : Type*} [Category D]
    (F : Pseudofunctor (LocallyDiscrete Dᵒᵖ) Cat)
    {ι : Type*} {S₀ : D} {X : ι → D} {f : ∀ i, X i ⟶ S₀}
    {D₁ D₂ : F.DescentData f} (e : D₁ ≅ D₂) (i : ι) :
    D₁.obj i ≅ D₂.obj i where
  hom := e.hom.hom i
  inv := e.inv.hom i
  hom_inv_id := by
    rw [← Pseudofunctor.DescentData.comp_hom e.hom e.inv i, e.hom_inv_id]
    rfl
  inv_hom_id := by
    rw [← Pseudofunctor.DescentData.comp_hom e.inv e.hom i, e.inv_hom_id]
    rfl

/-- Helper for Chap08 Lemma 8 13 2: the compatible arrows to `U` extracted from a composite
descent datum glue uniquely. -/
private theorem compDescentData_gluedArrowToU
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {V : C} (T : J.Cover V)
    (D : (canonicalFiberPseudofunctor (q ⋙ Over.forget U)).DescentData
      (fun I : T.Arrow ↦ I.f)) :
    ∃! u : V ⟶ U, ∀ I : T.Arrow,
      I.f ≫ u = compositeFiberArrowToU (U := U) q (D.obj I) := by
  -- Feed the extracted compatible family into the representable sheaf gluing lemma.
  exact
    representableArrowUniqueAmalgamation (J := J) (U := U) hU T
      (fun I ↦ compositeFiberArrowToU (U := U) q (D.obj I))
      (compDescentData_arrowsToU_compatible (J := J) (U := U) q T D)

/-- Helper for Chap08 Lemma 8 13 2: a descent-data morphism forces equality of any two glued
over-coordinates for its source and target data. -/
private theorem compDescentData_gluedArrow_eq_of_hom
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {V : C} (T : J.Cover V)
    {D E : (canonicalFiberPseudofunctor (q ⋙ Over.forget U)).DescentData
      (fun I : T.Arrow ↦ I.f)}
    (φ : D ⟶ E)
    {uD uE : V ⟶ U}
    (huD : ∀ I : T.Arrow,
      I.f ≫ uD = compositeFiberArrowToU (U := U) q (D.obj I))
    (huE : ∀ I : T.Arrow,
      I.f ≫ uE = compositeFiberArrowToU (U := U) q (E.obj I)) :
    uD = uE := by
  -- Use the compatible family from the source datum as the common local family; the morphism
  -- rewrites the target datum's local arrows pointwise to that same family.
  refine representableArrowAmalgamation_eq (J := J) (U := U) hU T
    (compDescentData_arrowsToU_compatible (J := J) (U := U) q T D) huD ?_
  intro I
  exact (huE I).trans ((compDescentData_arrowsToU_eq_of_hom (J := J) (U := U) q φ I).symm)

/-- Helper for Chap08 Lemma 8 13 2: a descent morphism between two image descent data forces the
two original composite-fiber objects to have the same remembered arrow to `U`. -/
private theorem compCover_imageDescentHom_arrowToU_eq
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {V : C} (T : J.Cover V)
    {X Y : (q ⋙ Over.forget U).Fiber V}
    (φ :
      ((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).toDescentData
        (fun I : T.Arrow ↦ I.f)).obj X ⟶
      ((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).toDescentData
        (fun I : T.Arrow ↦ I.f)).obj Y) :
    compositeFiberArrowToU (U := U) q X =
      compositeFiberArrowToU (U := U) q Y := by
  -- Compare both global arrows with the local arrows of the image descent data, then use the
  -- representable sheaf uniqueness bridge for descent-data morphisms.
  let D :=
    ((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).toDescentData
      (fun I : T.Arrow ↦ I.f)).obj X
  let E :=
    ((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).toDescentData
      (fun I : T.Arrow ↦ I.f)).obj Y
  have hX : ∀ I : T.Arrow,
      I.f ≫ compositeFiberArrowToU (U := U) q X =
        compositeFiberArrowToU (U := U) q (D.obj I) := by
    intro I
    simpa [D] using
      (composite_pseudofunctor_map_obj_arrow_eq_comp (U := U) q (f := I.f) (a := X)).symm
  have hY : ∀ I : T.Arrow,
      I.f ≫ compositeFiberArrowToU (U := U) q Y =
        compositeFiberArrowToU (U := U) q (E.obj I) := by
    intro I
    simpa [E] using
      (composite_pseudofunctor_map_obj_arrow_eq_comp (U := U) q (f := I.f) (a := Y)).symm
  exact
    compDescentData_gluedArrow_eq_of_hom (J := J) (U := U) hU q T
      (D := D) (E := E) (φ := φ) hX hY

/-- Helper for Chap08 Lemma 8 13 2: the endpoint equality in a composite fiber cancels against
the remembered arrow to `U`. -/
private theorem eqToHom_comp_compositeFiberArrowToU
    {S : Type*} [Category S] (q : S ⥤ Over U) {V : C}
    (a : (q ⋙ Over.forget U).Fiber V) :
    eqToHom a.2 ≫ compositeFiberArrowToU (U := U) q a = (q.obj a.1).hom := by
  -- Keep the fiber object closed and cancel the two opposite equality transports propositionally.
  dsimp [compositeFiberArrowToU]
  rw [← Category.assoc, eqToHom_trans]
  simp

/-- Helper for Chap08 Lemma 8 13 2: the arrow induced by a glued over-coordinate satisfies the
slice triangle for the corresponding local object. -/
private theorem compDescentData_sliceArrow_fac
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {V : C} (T : J.Cover V)
    (D : (canonicalFiberPseudofunctor (q ⋙ Over.forget U)).DescentData
      (fun I : T.Arrow ↦ I.f))
    {u : V ⟶ U}
    (hu : ∀ I : T.Arrow,
      I.f ≫ u = compositeFiberArrowToU (U := U) q (D.obj I))
    (I : T.Arrow) :
    (eqToHom (D.obj I).2 ≫ I.f) ≫ u = (q.obj (D.obj I).1).hom := by
  -- Reassociate to expose the glued local arrow, then cancel the fiber endpoint transport by the
  -- normal-form lemma above.
  calc
    (eqToHom (D.obj I).2 ≫ I.f) ≫ u =
        eqToHom (D.obj I).2 ≫ (I.f ≫ u) := by
      simp only [Category.assoc]
    _ = eqToHom (D.obj I).2 ≫ compositeFiberArrowToU (U := U) q (D.obj I) := by
      rw [hu I]
    _ = (q.obj (D.obj I).1).hom := by
      exact eqToHom_comp_compositeFiberArrowToU (U := U) q (D.obj I)

/-- Helper for Chap08 Lemma 8 13 2: the generated slice arrow attached to a composite descent
datum and a glued arrow to `U`. -/
private abbrev compDescentData_sliceArrow
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {V : C} (T : J.Cover V)
    (D : (canonicalFiberPseudofunctor (q ⋙ Over.forget U)).DescentData
      (fun I : T.Arrow ↦ I.f))
    {u : V ⟶ U}
    (hu : ∀ I : T.Arrow,
      I.f ≫ u = compositeFiberArrowToU (U := U) q (D.obj I))
    (I : T.Arrow) :
    q.obj (D.obj I).1 ⟶ Over.mk u :=
  Over.homMk (U := q.obj (D.obj I).1) (V := Over.mk u)
    (eqToHom (D.obj I).2 ≫ I.f)
    (compDescentData_sliceArrow_fac (J := J) (U := U) q T D hu I)

/-- Helper for Chap08 Lemma 8 13 2: the generated slice arrow has the expected left component. -/
private theorem compDescentData_sliceArrow_left
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {V : C} (T : J.Cover V)
    (D : (canonicalFiberPseudofunctor (q ⋙ Over.forget U)).DescentData
      (fun I : T.Arrow ↦ I.f))
    {u : V ⟶ U}
    (hu : ∀ I : T.Arrow,
      I.f ≫ u = compositeFiberArrowToU (U := U) q (D.obj I))
    (I : T.Arrow) :
    (compDescentData_sliceArrow (J := J) (U := U) q T D hu I).left =
      eqToHom (D.obj I).2 ≫ I.f := by
  -- The adapter is just the canonical `Over.homMk` with the triangle proof factored out.
  rfl

/-- Helper for Chap08 Lemma 8 13 2: a local object of a composite descent datum becomes a
`q`-fiber object over the corresponding standard slice-cover object once the glued arrow to `U`
is fixed. -/
private abbrev compDescentData_standardLocalObj
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {V : C} (T : J.Cover V)
    (D : (canonicalFiberPseudofunctor (q ⋙ Over.forget U)).DescentData
      (fun I : T.Arrow ↦ I.f))
    {u : V ⟶ U}
    (hu : ∀ I : T.Arrow,
      I.f ≫ u = compositeFiberArrowToU (U := U) q (D.obj I))
    (I : T.Arrow) :
    q.Fiber (Over.mk (I.f ≫ u)) :=
  compositeFiberObjToQFiberObj (U := U) q (D.obj I) (hu I)

/-- Helper for Chap08 Lemma 8 13 2: the standard-slice local object associated to a composite
descent datum forgets back to the original composite-fiber local object. -/
private theorem compDescentData_standardLocalObj_forget
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {V : C} (T : J.Cover V)
    (D : (canonicalFiberPseudofunctor (q ⋙ Over.forget U)).DescentData
      (fun I : T.Arrow ↦ I.f))
    {u : V ⟶ U}
    (hu : ∀ I : T.Arrow,
      I.f ≫ u = compositeFiberArrowToU (U := U) q (D.obj I))
    (I : T.Arrow) :
    qFiberAsCompositeFiberObj (U := U) q
        (compDescentData_standardLocalObj (J := J) (U := U) q T D hu I) =
      D.obj I := by
  exact qFiberAsCompositeFiberObj_compositeFiberObjToQFiberObj
    (U := U) q (D.obj I) (hu I)

/-- Helper for Chap08 Lemma 8 13 2: a fixed-arrow composite-fiber object over the source of a
slice arrow is the same as an object of the corresponding `q`-fiber. -/
private abbrev compositeFixedLocalObjToQFiberObj
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {A : Over U} {I : Over U} (f : I ⟶ A)
    (x : (q ⋙ Over.forget U).Fiber I.left)
    (hx : compositeFiberArrowToU (U := U) q x = f.left ≫ A.hom) :
    q.Fiber I :=
  Functor.Fiber.mk (a := x.1) (by
    have hmk :
        q.obj x.1 = Over.mk (compositeFiberArrowToU (U := U) q x) := by
      exact compositeFiberObj_eq_overMk_of_arrowToU_eq (U := U) q x rfl
    have hIhom : I.hom = f.left ≫ A.hom := by
      exact (Over.w f).symm
    have hmkI : Over.mk (f.left ≫ A.hom) = I := by
      exact CostructuredArrow.obj_ext (Over.mk (f.left ≫ A.hom)) I rfl (by
        simpa [hIhom])
    exact hmk.trans ((congrArg (fun a : I.left ⟶ U => Over.mk a) hx).trans hmkI))

/-- Helper for Chap08 Lemma 8 13 2: forgetting the fixed-arrow local `q`-fiber object recovers the
original composite-fiber object. -/
private theorem compositeFixedLocalObjToQFiberObj_forget
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {A : Over U} {I : Over U} (f : I ⟶ A)
    (x : (q ⋙ Over.forget U).Fiber I.left)
    (hx : compositeFiberArrowToU (U := U) q x = f.left ≫ A.hom) :
    qFiberAsCompositeFiberObj (U := U) q
        (compositeFixedLocalObjToQFiberObj (U := U) q f x hx) =
      x := by
  apply Subtype.ext
  rfl

/-- Helper for Chap08 Lemma 8 13 2: arbitrary slice arrows form a slice cover when their
left components form a base cover. -/
private theorem overCoverOfArrowsOfBaseCover
    {ι : Type*} {A : Over U} (Y : ι → Over U) (g : ∀ i, Y i ⟶ A)
    (hbase : Sieve.ofArrows (fun i ↦ (Y i).left) (fun i ↦ (g i).left) ∈ J A.left) :
    Sieve.ofArrows Y g ∈ (J.over U) A := by
  -- Use the slice-cover criterion and identify `Sieve.overEquiv` of the generated slice sieve
  -- with the generated sieve of left components.
  rw [GrothendieckTopology.mem_over_iff]
  have hEq :
      Sieve.overEquiv A (Sieve.ofArrows Y g) =
        Sieve.ofArrows (fun i ↦ (Y i).left) (fun i ↦ (g i).left) := by
    ext Z f
    rw [Sieve.overEquiv_iff, Sieve.mem_ofArrows_iff, Sieve.mem_ofArrows_iff]
    constructor
    · rintro ⟨i, h, hfac⟩
      refine ⟨i, h.left, ?_⟩
      exact congrArg (fun k ↦ k.left) hfac
    · rintro ⟨i, h, hfac⟩
      refine ⟨i, Over.homMk h ?_, ?_⟩
      · simpa [hfac, Category.assoc] using
          congrArg (fun k ↦ h ≫ k) (Over.w (g i)).symm
      · ext
        exact hfac
  rwa [hEq]

/-- Helper for Chap08 Lemma 8 13 2: a cover in the slice topology projects to a cover of the
left component in the base topology. -/
private theorem overCover_baseCover
    {A : Over U} (T : (J.over U).Cover A) :
    Sieve.ofArrows (fun I : T.Arrow ↦ I.Y.left) (fun I ↦ I.f.left) ∈ J A.left := by
  -- Identify the generated sieve of left components with the image of the slice covering sieve
  -- under `Sieve.overEquiv`.
  have hEq :
      Sieve.overEquiv A (Sieve.ofArrows (fun I : T.Arrow ↦ I.Y) (fun I ↦ I.f)) =
        Sieve.ofArrows (fun I : T.Arrow ↦ I.Y.left) (fun I ↦ I.f.left) := by
    ext Z g
    rw [Sieve.overEquiv_iff, Sieve.mem_ofArrows_iff, Sieve.mem_ofArrows_iff]
    constructor
    · rintro ⟨I, h, hfac⟩
      exact ⟨I, h.left, congrArg (fun k ↦ k.left) hfac⟩
    · rintro ⟨I, h, hfac⟩
      refine ⟨I, Over.homMk h ?_, ?_⟩
      · simpa [hfac, Category.assoc] using congrArg (fun k ↦ h ≫ k) (Over.w I.f).symm
      · ext
        exact hfac
  have hT : Sieve.overEquiv A (T : Sieve A) ∈ J A.left :=
    (GrothendieckTopology.mem_over_iff J (T : Sieve A)).1 T.condition
  rw [← hEq]
  simpa [T.ofArrows_eq] using hT

/-- Helper for Chap08 Lemma 8 13 2: stackness of the composite projection gives effective
descent for the base family obtained by projecting a fixed slice cover. -/
private theorem overCover_composite_toDescentData_isEquivalence
    {S : Type*} [Category S] (p : S ⥤ Over U)
    [(p ⋙ Over.forget U).IsFibered]
    (hcomp : IsStackOnSite J (p ⋙ Over.forget U))
    {A : Over U} (T : (J.over U).Cover A) :
    ((canonicalFiberPseudofunctor (p ⋙ Over.forget U)).toDescentData
      (fun I : T.Arrow ↦ I.f.left)).IsEquivalence := by
  -- Keep the indexing family from the slice cover fixed; only the covering proof is transported
  -- through `overCover_baseCover`.
  letI : IsStackOnSite J (p ⋙ Over.forget U) := hcomp
  let F := canonicalFiberPseudofunctor (p ⋙ Over.forget U)
  have hStackFor :
      F.IsStackFor
        (Presieve.ofArrows (fun I : T.Arrow ↦ I.Y.left) (fun I ↦ I.f.left)) := by
    simpa [F, Sieve.ofArrows] using
      F.isStackFor'
        (Sieve.ofArrows (fun I : T.Arrow ↦ I.Y.left) (fun I ↦ I.f.left))
        (overCover_baseCover (J := J) (U := U) T)
  exact
    (F.isStackFor_ofArrows_iff (fun I : T.Arrow ↦ I.f.left)).1 hStackFor

/-- Helper for Chap08 Lemma 8 13 2: the full subcategory of composite descent data whose local
objects remember the fixed arrows `I.f.left ≫ A.hom`. -/
private abbrev compositeDescentFixedArrowProperty
    {S : Type*} [Category S] (p : S ⥤ Over U)
    [(p ⋙ Over.forget U).IsFibered]
    {A : Over U} (T : (J.over U).Cover A) :
    ObjectProperty
      ((canonicalFiberPseudofunctor (p ⋙ Over.forget U)).DescentData
        (fun I : T.Arrow ↦ I.f.left)) :=
  fun D => ∀ I : T.Arrow,
    compositeFiberArrowToU (U := U) p (D.obj I) = I.f.left ≫ A.hom

/-- Helper for Chap08 Lemma 8 13 2: composite descent of a fixed-arrow composite-fiber object
still has the fixed local arrows over the projected slice cover. -/
private noncomputable def compositeFixedFiberToFixedDescentFunctor
    {S : Type*} [Category S] (p : S ⥤ Over U)
    [(p ⋙ Over.forget U).IsFibered]
    {A : Over U} (T : (J.over U).Cover A) :
    (compositeFiberFixedArrowProperty (U := U) p A).FullSubcategory ⥤
      (compositeDescentFixedArrowProperty (J := J) (U := U) (p := p) T).FullSubcategory :=
  (compositeDescentFixedArrowProperty (J := J) (U := U) (p := p) T).lift
    ((compositeFiberFixedArrowProperty (U := U) p A).ι ⋙
      ((canonicalFiberPseudofunctor (p ⋙ Over.forget U)).toDescentData
        (fun I : T.Arrow ↦ I.f.left)))
    (fun X => by
      intro I
      change compositeFiberArrowToU (U := U) p
          (((canonicalFiberPseudofunctor (p ⋙ Over.forget U)).map I.f.left.op.toLoc).toFunctor.obj
            X.obj) =
        I.f.left ≫ A.hom
      rw [composite_pseudofunctor_map_obj_arrow_eq_comp (U := U) p
        (f := I.f.left) (a := X.obj)]
      rw [X.property]
      rfl)

/-- Helper for Chap08 Lemma 8 13 2: if the composite projection is a stack, then its projected
descent equivalence restricts to the fixed-arrow full subcategories attached to a slice cover. -/
private theorem compositeFixedFiberToFixedDescentFunctor_isEquivalence
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {S : Type*} [Category S] (p : S ⥤ Over U)
    [(p ⋙ Over.forget U).IsFibered]
    (hcomp : IsStackOnSite J (p ⋙ Over.forget U))
    {A : Over U} (T : (J.over U).Cover A) :
    (compositeFixedFiberToFixedDescentFunctor (J := J) (U := U) p T).IsEquivalence := by
  let Φc :=
    (canonicalFiberPseudofunctor (p ⋙ Over.forget U)).toDescentData
      (fun I : T.Arrow ↦ I.f.left)
  have hΦc : Φc.IsEquivalence :=
    overCover_composite_toDescentData_isEquivalence
      (J := J) (U := U) p hcomp T
  letI : Φc.IsEquivalence := hΦc
  let Ffix := compositeFixedFiberToFixedDescentFunctor (J := J) (U := U) p T
  have hFaithful :
      Ffix.Faithful := by
    constructor
    intro X Y f g hfg
    apply ObjectProperty.hom_ext
    apply Φc.map_injective
    simpa [Ffix, compositeFixedFiberToFixedDescentFunctor, Φc] using
      congrArg (fun k => k.hom) hfg
  have hFull :
      Ffix.Full := by
    constructor
    intro X Y φ
    refine ⟨ObjectProperty.homMk (Φc.preimage φ.hom), ?_⟩
    apply ObjectProperty.hom_ext
    simp [Ffix, compositeFixedFiberToFixedDescentFunctor, Φc]
  refine { faithful := hFaithful, full := hFull, essSurj := ?_ }
  refine
    { mem_essImage := fun D => ?_ }
  letI : Φc.EssSurj := hΦc.essSurj
  rcases Functor.EssSurj.mem_essImage (F := Φc) D.obj with ⟨X, ⟨e⟩⟩
  have hX :
      compositeFiberArrowToU (U := U) p X = A.hom := by
    refine
      representableArrowAmalgamation_eq_ofArrows (J := J) (U := U) hU
        (Y := fun I : T.Arrow ↦ I.Y.left)
        (f := fun I : T.Arrow ↦ I.f.left)
        (overCover_baseCover (J := J) (U := U) T)
        (a := fun I : T.Arrow ↦ I.f.left ≫ A.hom) ?_ ?_
    · intro I
      calc
        I.f.left ≫ compositeFiberArrowToU (U := U) p X =
            compositeFiberArrowToU (U := U) p (D.obj.obj I) := by
          rw [← composite_pseudofunctor_map_obj_arrow_eq_comp
            (U := U) p (f := I.f.left) (a := X)]
          exact compositeFiberArrowToU_eq_of_hom (U := U) p (e.hom.hom I)
        _ = I.f.left ≫ A.hom := D.property I
    · intro I
      rfl
  exact ⟨⟨X, hX⟩,
    ⟨ObjectProperty.isoMk
      (P := compositeDescentFixedArrowProperty (J := J) (U := U) (p := p) T) e⟩⟩

/-- Helper for Chap08 Lemma 8 13 2: the datum-dependent slice arrows obtained from a glued
over-coordinate form a cover in the slice topology. -/
private theorem compDescentData_sliceCover_mem
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {V : C} (T : J.Cover V)
    (D : (canonicalFiberPseudofunctor (q ⋙ Over.forget U)).DescentData
      (fun I : T.Arrow ↦ I.f))
    {u : V ⟶ U}
    (hu : ∀ I : T.Arrow,
      I.f ≫ u = compositeFiberArrowToU (U := U) q (D.obj I)) :
    Sieve.ofArrows
      (fun I : T.Arrow ↦ q.obj (D.obj I).1)
      (fun I ↦
        Over.homMk (U := q.obj (D.obj I).1) (V := Over.mk u)
          (eqToHom (D.obj I).2 ≫ I.f)
          (compDescentData_sliceArrow_fac (J := J) (U := U) q T D hu I)) ∈
      (J.over U) (Over.mk u) := by
  -- Reduce the slice-cover claim to the base cover; the original base arrows factor through the
  -- transported left components by the fiber endpoint isomorphisms.
  refine
    overCoverOfArrowsOfBaseCover (J := J) (U := U)
      (Y := fun I : T.Arrow ↦ q.obj (D.obj I).1)
      (g := fun I ↦
        Over.homMk (U := q.obj (D.obj I).1) (V := Over.mk u)
          (eqToHom (D.obj I).2 ≫ I.f)
          (compDescentData_sliceArrow_fac (J := J) (U := U) q T D hu I)) ?_
  have hbase :
      Sieve.ofArrows
          (fun I : T.Arrow ↦ (q.obj (D.obj I).1).left)
          (fun I ↦
            (Over.homMk (U := q.obj (D.obj I).1) (V := Over.mk u)
              (eqToHom (D.obj I).2 ≫ I.f)
              (compDescentData_sliceArrow_fac (J := J) (U := U) q T D hu I)).left) ∈
        J V := by
    -- The original cover sieve is contained in this base image sieve by precomposing with the
    -- inverse endpoint transport of each local fiber object.
    refine J.superset_covering
      (S := Sieve.ofArrows (fun I : T.Arrow ↦ I.Y) (fun I ↦ I.f))
      (R := Sieve.ofArrows
        (fun I : T.Arrow ↦ (q.obj (D.obj I).1).left)
        (fun I ↦
          (Over.homMk (U := q.obj (D.obj I).1) (V := Over.mk u)
            (eqToHom (D.obj I).2 ≫ I.f)
            (compDescentData_sliceArrow_fac (J := J) (U := U) q T D hu I)).left)) ?_ ?_
    · intro Y f hf
      rw [Sieve.mem_ofArrows_iff] at hf ⊢
      rcases hf with ⟨I, k, hk⟩
      refine ⟨I, k ≫ eqToHom (D.obj I).2.symm, ?_⟩
      simpa [Category.assoc] using hk
    · rw [T.ofArrows_eq]
      exact T.condition
  change
    Sieve.ofArrows
        (fun I : T.Arrow ↦ (q.obj (D.obj I).1).left)
        (fun I ↦
          (Over.homMk (U := q.obj (D.obj I).1) (V := Over.mk u)
            (eqToHom (D.obj I).2 ≫ I.f)
            (compDescentData_sliceArrow_fac (J := J) (U := U) q T D hu I)).left) ∈
      J V
  exact hbase

/-- Helper for Chap08 Lemma 8 13 2: stack descent for `q` applies to the generated slice
family attached to a composite descent datum. -/
private theorem compDescentData_sliceGenerator_toDescentData_isEquivalence
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [IsStackOnSite (J.over U) q]
    {V : C} (T : J.Cover V)
    (D : (canonicalFiberPseudofunctor (q ⋙ Over.forget U)).DescentData
      (fun I : T.Arrow ↦ I.f))
    {u : V ⟶ U}
    (hu : ∀ I : T.Arrow,
      I.f ≫ u = compositeFiberArrowToU (U := U) q (D.obj I)) :
    ((canonicalFiberPseudofunctor q).toDescentData
      (fun I : T.Arrow ↦
        compDescentData_sliceArrow (J := J) (U := U) q T D hu I)).IsEquivalence := by
  -- Use stackness of `q` on the generated slice sieve already proved to cover.
  let R : Sieve (Over.mk u) :=
    Sieve.ofArrows
      (fun I : T.Arrow ↦ q.obj (D.obj I).1)
      (fun I ↦ compDescentData_sliceArrow (J := J) (U := U) q T D hu I)
  have hR : R ∈ (J.over U) (Over.mk u) := by
    simpa [R, compDescentData_sliceArrow] using
      compDescentData_sliceCover_mem (J := J) (U := U) q T D hu
  let F := canonicalFiberPseudofunctor q
  have hStackR : F.IsStackFor R.arrows := by
    simpa [F] using F.isStackFor' R hR
  -- Replace the sieve's arrow presieve by the original generated-family presieve.
  have hgen :
      Sieve.generate R.arrows =
        Sieve.generate
          (Presieve.ofArrows
            (fun I : T.Arrow ↦ q.obj (D.obj I).1)
            (fun I ↦ compDescentData_sliceArrow (J := J) (U := U) q T D hu I)) := by
    rw [Sieve.generate_sieve]
  have hStackGenerated :
      F.IsStackFor
        (Presieve.ofArrows
          (fun I : T.Arrow ↦ q.obj (D.obj I).1)
          (fun I ↦ compDescentData_sliceArrow (J := J) (U := U) q T D hu I)) :=
    (F.isStackFor_iff_of_sieve_eq hgen).1 hStackR
  -- The `ofArrows` stack criterion is exactly the requested descent equivalence.
  exact
    (F.isStackFor_ofArrows_iff
      (fun I : T.Arrow ↦
        compDescentData_sliceArrow (J := J) (U := U) q T D hu I)).1 hStackGenerated

/-- Helper for Chap08 Lemma 8 13 2: stack descent for `q` applies to the standard
slice cover induced by a base cover and an arrow to `U`. -/
private theorem compStandardSliceCover_toDescentData_isEquivalence
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [IsStackOnSite (J.over U) q]
    {V : C} (T : J.Cover V) (u : V ⟶ U) :
    ((canonicalFiberPseudofunctor q).toDescentData
      (fun I : T.Arrow ↦
        Over.homMk (U := Over.mk (I.f ≫ u)) (V := Over.mk u) I.f)).IsEquivalence := by
  -- First register the standard family as a covering sieve in the slice topology.
  let R : Sieve (Over.mk u) :=
    Sieve.ofArrows
      (fun I : T.Arrow ↦ Over.mk (I.f ≫ u))
      (fun I ↦ Over.homMk (U := Over.mk (I.f ≫ u)) (V := Over.mk u) I.f)
  have hR : R ∈ (J.over U) (Over.mk u) := by
    simpa [R] using overCoverOfBaseCover (J := J) (U := U) T u
  -- Stackness for `q` over that sieve is then converted to the `ofArrows` descent functor.
  let F := canonicalFiberPseudofunctor q
  have hStackR : F.IsStackFor R.arrows := by
    simpa [F] using F.isStackFor' R hR
  have hgen :
      Sieve.generate R.arrows =
        Sieve.generate
          (Presieve.ofArrows
            (fun I : T.Arrow ↦ Over.mk (I.f ≫ u))
            (fun I ↦ Over.homMk (U := Over.mk (I.f ≫ u)) (V := Over.mk u) I.f)) := by
    rw [Sieve.generate_sieve]
  have hStackGenerated :
      F.IsStackFor
        (Presieve.ofArrows
          (fun I : T.Arrow ↦ Over.mk (I.f ≫ u))
          (fun I ↦ Over.homMk (U := Over.mk (I.f ≫ u)) (V := Over.mk u) I.f)) :=
    (F.isStackFor_iff_of_sieve_eq hgen).1 hStackR
  exact
    (F.isStackFor_ofArrows_iff
      (fun I : T.Arrow ↦
        Over.homMk (U := Over.mk (I.f ≫ u)) (V := Over.mk u) I.f)).1 hStackGenerated

/-- Helper for Chap08 Lemma 8 13 2: the standard slice-cover descent equivalence may be
indexed by the actual arrows of the generated cover. -/
private theorem standardSliceCover_arrow_toDescentData_isEquivalence
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [IsStackOnSite (J.over U) q]
    {V : C} (T : J.Cover V) (u : V ⟶ U) :
    ((canonicalFiberPseudofunctor q).toDescentData
      (fun K : (standardSliceCover (J := J) (U := U) T u).Arrow => K.f)).IsEquivalence := by
  let F := canonicalFiberPseudofunctor q
  have hStandard :
      (F.toDescentData
        (fun I : T.Arrow =>
          Over.homMk (U := Over.mk (I.f ≫ u)) (V := Over.mk u) I.f)).IsEquivalence :=
    compStandardSliceCover_toDescentData_isEquivalence (J := J) (U := U) q T u
  exact
    (Pseudofunctor.DescentData.isEquivalence_toDescentData_iff_of_sieve_eq
      (F := F)
      (f := fun I : T.Arrow =>
        Over.homMk (U := Over.mk (I.f ≫ u)) (V := Over.mk u) I.f)
      (f' := fun K : (standardSliceCover (J := J) (U := U) T u).Arrow => K.f)
      (standardSliceCover_slice_sieve_eq (J := J) (U := U) T u)).1 hStandard

/-- Helper for Chap08 Lemma 8 13 2: descent for the projected arrows of the standard slice
cover is equivalent to descent for the original base cover. -/
private theorem standardSliceCover_left_toDescentData_isEquivalence_iff
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {V : C} (T : J.Cover V) (u : V ⟶ U) :
    ((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).toDescentData
      (fun K : (standardSliceCover (J := J) (U := U) T u).Arrow => K.f.left)).IsEquivalence ↔
    ((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).toDescentData
      (fun I : T.Arrow => I.f)).IsEquivalence := by
  let F := canonicalFiberPseudofunctor (q ⋙ Over.forget U)
  exact
    Pseudofunctor.DescentData.isEquivalence_toDescentData_iff_of_sieve_eq
      (F := F)
      (f := fun K : (standardSliceCover (J := J) (U := U) T u).Arrow => K.f.left)
      (f' := fun I : T.Arrow => I.f)
      (standardSliceCover_left_sieve_eq (J := J) (U := U) T u)

/-- Helper for Chap08 Lemma 8 13 2: the composite canonical pullback maps to a hom-lift in the
slice projection and is strongly cartesian for `q`. -/
private theorem compCanonicalPullback_qCartesianNormalForm
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {Y Z : C} (f : Y ⟶ Z) (a : (q ⋙ Over.forget U).Fiber Z) :
    Functor.IsHomLift (Over.forget U) f
        (q.map ((canonicalPullbackChoice (q ⋙ Over.forget U)).map f a)) ∧
      q.IsStronglyCartesian
        (q.map ((canonicalPullbackChoice (q ⋙ Over.forget U)).map f a))
        ((canonicalPullbackChoice (q ⋙ Over.forget U)).map f a) := by
  let hc := canonicalPullbackChoice (q ⋙ Over.forget U)
  let φ := hc.map f a
  refine ⟨?_, ?_⟩
  · -- The composite hom-lift projects to a hom-lift in the slice projection.
    exact isHomLift_overForget_of_comp_isHomLift (U := U) q
      ((hc.isStronglyCartesian f a).toIsHomLift)
  · -- Rebase the composite strong-cartesian structure to the owner-level mapped arrow, then
    -- apply the slice-forgetful transport theorem.
    have hcompOwner :
        (q ⋙ Over.forget U).IsStronglyCartesian ((q ⋙ Over.forget U).map φ) φ := by
      letI : (q ⋙ Over.forget U).IsStronglyCartesian f φ := by
        simpa [φ] using hc.isStronglyCartesian f a
      exact isStronglyCartesian_rebase_to_map (p := q ⋙ Over.forget U) (f := f) φ
    letI : (q ⋙ Over.forget U).IsStronglyCartesian (q.map φ).left φ := by
      simpa [Functor.comp_map, Over.forget_map] using hcompOwner
    simpa [φ] using Functor.isStronglyCartesian_of_comp_over_forget q

/-- Helper for Chap08 Lemma 8 13 2: the composite canonical pullback along the left component
of a slice arrow has the expected slice object as its `q`-image. -/
private theorem compCanonicalPullback_obj_over
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {A B : Over U} (f : A ⟶ B) (x : q.Fiber B) :
    q.obj
        (((canonicalPullbackChoice (q ⋙ Over.forget U)).pullbackFunctor f.left).obj
          (qFiberAsCompositeFiberObj (U := U) q x)).1 = A := by
  rcases x with ⟨x, hx⟩
  cases hx
  let hc := canonicalPullbackChoice (q ⋙ Over.forget U)
  let y : (q ⋙ Over.forget U).Fiber A.left :=
    (hc.pullbackFunctor f.left).obj
      (qFiberAsCompositeFiberObj (U := U) q (Functor.Fiber.mk (p := q) rfl))
  let φ : y.1 ⟶ x :=
    hc.map f.left (qFiberAsCompositeFiberObj (U := U) q (Functor.Fiber.mk (p := q) rfl))
  have hφ :
      Functor.IsHomLift (Over.forget U) f.left (q.map φ) := by
    exact (compCanonicalPullback_qCartesianNormalForm (U := U) q f.left
      (qFiberAsCompositeFiberObj (U := U) q (Functor.Fiber.mk (p := q) rfl))).1
  apply CostructuredArrow.obj_ext (q.obj y.1) A y.2
  have hfac : (q.map φ).left = eqToHom y.2 ≫ f.left := by
    simpa [φ, y] using
      (@IsHomLift.fac' _ _ _ _ (Over.forget U) A.left (q.obj x).left _ _ f.left
        (q.map φ) hφ)
  rw [← Over.w f]
  simpa [Functor.id_map, Category.assoc, hfac] using Over.w (q.map φ)

/-- Helper for Chap08 Lemma 8 13 2: the composite canonical pullback and the slice canonical
pullback have canonically isomorphic domains in the `q`-fiber. -/
private noncomputable def compCanonicalPullback_qFiberIso
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [q.IsFibered] [(q ⋙ Over.forget U).IsFibered]
    {A B : Over U} (f : A ⟶ B) (x : q.Fiber B) :
    Functor.Fiber.mk (p := q)
        (compCanonicalPullback_obj_over (U := U) q f x) ≅
      ((canonicalPullbackChoice q).pullbackFunctor f).obj x := by
  rcases x with ⟨x, hx⟩
  cases hx
  let hcComp := canonicalPullbackChoice (q ⋙ Over.forget U)
  let hcQ := canonicalPullbackChoice q
  let xq : q.Fiber (q.obj x) := Functor.Fiber.mk (p := q) rfl
  let xc : (q ⋙ Over.forget U).Fiber (q.obj x).left :=
    qFiberAsCompositeFiberObj (U := U) q xq
  let yComp : S := ((hcComp.pullbackFunctor f.left).obj xc).1
  let φComp : yComp ⟶ x := hcComp.map f.left xc
  let yQ : q.Fiber A := (hcQ.pullbackFunctor f).obj xq
  let φQ : yQ.1 ⟶ x := hcQ.map f xq
  have hy : q.obj yComp = A := by
    simpa [yComp, xq, xc, hcComp] using
      compCanonicalPullback_obj_over (U := U) q f xq
  have hφCompStrongMap :
      q.IsStronglyCartesian (q.map φComp) φComp := by
    simpa [φComp, xc, hcComp] using
      (compCanonicalPullback_qCartesianNormalForm (U := U) q f.left xc).2
  have hφCompBase : q.map φComp = eqToHom hy ≫ f := by
    apply Over.OverMorphism.ext
    have hHom : Functor.IsHomLift (Over.forget U) f.left (q.map φComp) := by
      simpa [φComp, xc, hcComp] using
        (compCanonicalPullback_qCartesianNormalForm (U := U) q f.left xc).1
    have hleft : (q.map φComp).left = eqToHom (congrArg (Over.forget U).obj hy) ≫ f.left := by
      simpa [Functor.comp_obj, φComp, yComp, xc, hcComp] using
        (@IsHomLift.fac' _ _ _ _ (Over.forget U) A.left (q.obj x).left _ _
          f.left (q.map φComp) hHom)
    simpa [Over.comp_left, Category.assoc] using hleft
  have hφCompStrong :
      q.IsStronglyCartesian (eqToHom hy ≫ f) φComp := by
    simpa [hφCompBase] using hφCompStrongMap
  have hφQStrong : q.IsStronglyCartesian f φQ := by
    simpa [φQ, hcQ, xq] using hcQ.isStronglyCartesian f xq
  have hbase : (eqToHom hy ≫ f) = (eqToIso hy).hom ≫ f := by
    rfl
  let e : yComp ≅ yQ.1 :=
    @Functor.IsStronglyCartesian.domainIsoOfBaseIso _ _ _ _ q
      A (q.obj yComp) (q.obj x) yQ.1 yComp x
      f (eqToHom hy ≫ f) (eqToIso hy) hbase φQ φComp
      hφQStrong hφCompStrong
  refine
    { hom := ⟨e.hom, ?_⟩
      inv := ⟨e.inv, ?_⟩
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact e.inv_hom_id }
  · haveI : q.IsHomLift (eqToHom hy) e.hom := by
      simpa [e] using
        (inferInstance :
          q.IsHomLift (eqToIso hy).hom
            (@Functor.IsStronglyCartesian.domainIsoOfBaseIso _ _ _ _ q
              A (q.obj yComp) (q.obj x) yQ.1 yComp x
              f (eqToHom hy ≫ f) (eqToIso hy) hbase φQ φComp
              hφQStrong hφCompStrong).hom)
    simpa using
      (IsHomLift.of_fac' q (𝟙 A) e.hom hy yQ.2 (by
        simpa using (IsHomLift.fac' q (eqToHom hy) e.hom)))
  · haveI : q.IsHomLift (eqToIso hy).inv e.inv := by
      simpa [e] using
        (inferInstance :
          q.IsHomLift (eqToIso hy).inv
            (@Functor.IsStronglyCartesian.domainIsoOfBaseIso _ _ _ _ q
              A (q.obj yComp) (q.obj x) yQ.1 yComp x
              f (eqToHom hy ≫ f) (eqToIso hy) hbase φQ φComp
              hφQStrong hφCompStrong).inv)
    simpa using
      (IsHomLift.of_fac' q (𝟙 A) e.inv yQ.2 hy (by
        simpa using (IsHomLift.fac' q (eqToIso hy).inv e.inv)))

/-- Helper for Chap08 Lemma 8 13 2: the `q`-fiber comparison between the composite and slice
canonical pullbacks has the expected tail factorization. -/
private theorem compCanonicalPullback_qFiberIso_hom_fac
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [q.IsFibered] [(q ⋙ Over.forget U).IsFibered]
    {A B : Over U} (f : A ⟶ B) (x : q.Fiber B) :
    (compCanonicalPullback_qFiberIso (U := U) q f x).hom.1 ≫
      (canonicalPullbackChoice q).map f x =
    (canonicalPullbackChoice (q ⋙ Over.forget U)).map f.left
      (qFiberAsCompositeFiberObj (U := U) q x) := by
  rcases x with ⟨x, hx⟩
  cases hx
  let hcComp := canonicalPullbackChoice (q ⋙ Over.forget U)
  let hcQ := canonicalPullbackChoice q
  let xq : q.Fiber (q.obj x) := Functor.Fiber.mk (p := q) rfl
  let xc : (q ⋙ Over.forget U).Fiber (q.obj x).left :=
    qFiberAsCompositeFiberObj (U := U) q xq
  let yComp : S := ((hcComp.pullbackFunctor f.left).obj xc).1
  let φComp : yComp ⟶ x := hcComp.map f.left xc
  let yQ : q.Fiber A := (hcQ.pullbackFunctor f).obj xq
  let φQ : yQ.1 ⟶ x := hcQ.map f xq
  have hy : q.obj yComp = A := by
    simpa [yComp, xq, xc, hcComp] using
      compCanonicalPullback_obj_over (U := U) q f xq
  have hφCompStrongMap :
      q.IsStronglyCartesian (q.map φComp) φComp := by
    simpa [φComp, xc, hcComp] using
      (compCanonicalPullback_qCartesianNormalForm (U := U) q f.left xc).2
  have hφCompBase : q.map φComp = eqToHom hy ≫ f := by
    apply Over.OverMorphism.ext
    have hHom : Functor.IsHomLift (Over.forget U) f.left (q.map φComp) := by
      simpa [φComp, xc, hcComp] using
        (compCanonicalPullback_qCartesianNormalForm (U := U) q f.left xc).1
    have hleft : (q.map φComp).left = eqToHom (congrArg (Over.forget U).obj hy) ≫ f.left := by
      simpa [Functor.comp_obj, φComp, yComp, xc, hcComp] using
        (@IsHomLift.fac' _ _ _ _ (Over.forget U) A.left (q.obj x).left _ _
          f.left (q.map φComp) hHom)
    simpa [Over.comp_left, Category.assoc] using hleft
  have hφCompLift : q.IsHomLift (eqToHom hy ≫ f) φComp := by
    have hStrong : q.IsStronglyCartesian (eqToHom hy ≫ f) φComp := by
      simpa [hφCompBase] using hφCompStrongMap
    letI : q.IsStronglyCartesian (eqToHom hy ≫ f) φComp := hStrong
    infer_instance
  have hφQStrong : q.IsStronglyCartesian f φQ := by
    simpa [φQ, hcQ, xq] using hcQ.isStronglyCartesian f xq
  letI : q.IsStronglyCartesian f φQ := hφQStrong
  letI : q.IsHomLift (eqToHom hy ≫ f) φComp := hφCompLift
  have hfac :
      Functor.IsStronglyCartesian.map q f φQ
          (show eqToHom hy ≫ f = eqToHom hy ≫ f from rfl) φComp ≫ φQ =
        φComp := by
    exact Functor.IsStronglyCartesian.fac q f φQ
      (show eqToHom hy ≫ f = eqToHom hy ≫ f from rfl) φComp
  dsimp [compCanonicalPullback_qFiberIso, xq, xc, yComp, φComp, yQ, φQ, hcComp, hcQ]
  change Functor.IsStronglyCartesian.map q f φQ
      (show eqToHom hy ≫ f = eqToHom hy ≫ f from rfl) φComp ≫ φQ =
    φComp
  exact hfac

/-- Helper for Chap08 Lemma 8 13 2: a composite-fiber morphism whose endpoints have the same
slice object is vertical for the original slice projection. -/
private theorem qFiber_isHomLift_id_of_compositeFiberHom
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {A : Over U} {x y : (q ⋙ Over.forget U).Fiber A.left}
    (hx : q.obj x.1 = A) (hy : q.obj y.1 = A) (φ : x ⟶ y) :
    q.IsHomLift (𝟙 A) φ.1 := by
  refine IsHomLift.of_fac' q (𝟙 A) φ.1 hx hy ?_
  apply Over.OverMorphism.ext
  have hleft : (q.map φ.1).left = eqToHom (congrArg (Over.forget U).obj hx) ≫
      (𝟙 A.left) ≫ eqToHom (congrArg (Over.forget U).obj hy).symm := by
    simpa [Functor.comp_map] using
      (@IsHomLift.fac' _ _ _ _ (q ⋙ Over.forget U) A.left A.left _ _ (𝟙 A.left)
        φ.1 φ.2)
  simpa [Over.comp_left, Category.assoc] using hleft

/-- Helper for Chap08 Lemma 8 13 2: a composite-fiber morphism can be regarded as a morphism in
the original `q`-fiber once both endpoints have the same slice object. -/
private abbrev compositeFiberHomToQFiberHom
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {A : Over U} {x y : (q ⋙ Over.forget U).Fiber A.left}
    (hx : q.obj x.1 = A) (hy : q.obj y.1 = A) (φ : x ⟶ y) :
    Functor.Fiber.mk (p := q) hx ⟶ Functor.Fiber.mk (p := q) hy :=
  ⟨φ.1, qFiber_isHomLift_id_of_compositeFiberHom (U := U) q hx hy φ⟩

/-- Helper for Chap08 Lemma 8 13 2: viewing a slice fiber inside the composite fiber is full. -/
private theorem qFiberToCompositeFiberFunctor_full
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered] (A : Over U) :
    (qFiberToCompositeFiberFunctor (U := U) q A).Full := by
  constructor
  intro X Y φ
  let ψ : X ⟶ Y :=
    compositeFiberHomToQFiberHom (U := U) q X.2 Y.2 φ
  refine ⟨ψ, ?_⟩
  apply Functor.Fiber.hom_ext
  rfl

/-- Helper for Chap08 Lemma 8 13 2: a fixed-arrow composite-fiber object is the same thing as a
`q`-fiber object over the corresponding slice object. -/
private noncomputable def compositeFixedFiberToQFiberFunctor
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered] (A : Over U) :
    (compositeFiberFixedArrowProperty (U := U) q A).FullSubcategory ⥤ q.Fiber A where
  obj x := by
    refine compositeFiberObjToQFiberObj (U := U) q x.obj ?_
    exact x.property.symm
  map {x y} φ := by
    have hx : q.obj x.obj.1 = A := by
      simpa using
        compositeFiberObj_eq_overMk_of_arrowToU_eq (U := U) q x.obj x.property.symm
    have hy : q.obj y.obj.1 = A := by
      simpa using
        compositeFiberObj_eq_overMk_of_arrowToU_eq (U := U) q y.obj y.property.symm
    exact compositeFiberHomToQFiberHom (U := U) q hx hy φ.hom
  map_id x := by
    apply Functor.Fiber.hom_ext
    rfl
  map_comp {x y z} φ ψ := by
    apply Functor.Fiber.hom_ext
    rfl

/-- Helper for Chap08 Lemma 8 13 2: the fiber over a slice object is equivalent to the
fixed-arrow part of the corresponding composite fiber. -/
private theorem qFiberToCompositeFixedFiberFunctor_isEquivalence
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered] (A : Over U) :
    (qFiberToCompositeFixedFiberFunctor (U := U) q A).IsEquivalence := by
  let F := qFiberToCompositeFixedFiberFunctor (U := U) q A
  have hFaithful : F.Faithful := by
    constructor
    intro X Y f g hfg
    apply Functor.Fiber.hom_ext
    exact congrArg (fun k => k.hom.1) hfg
  have hFull : F.Full := by
    constructor
    intro X Y φ
    let ψ : X ⟶ Y :=
      compositeFiberHomToQFiberHom (U := U) q X.2 Y.2 φ.hom
    refine ⟨ψ, ?_⟩
    apply ObjectProperty.hom_ext
    apply Functor.Fiber.hom_ext
    rfl
  refine { faithful := hFaithful, full := hFull, essSurj := ?_ }
  refine { mem_essImage := fun X => ?_ }
  let Y := (compositeFixedFiberToQFiberFunctor (U := U) q A).obj X
  refine ⟨Y, ⟨?_⟩⟩
  apply ObjectProperty.isoMk
  apply eqToIso
  dsimp [F, Y, qFiberToCompositeFixedFiberFunctor,
    compositeFixedFiberToQFiberFunctor]
  exact qFiberAsCompositeFiberObj_compositeFiberObjToQFiberObj
    (U := U) q X.obj X.property.symm

/-- Helper for Chap08 Lemma 8 13 2: if a functor becomes an equivalence after composition
with a fully faithful functor, then it was already an equivalence. -/
private theorem isEquivalence_of_comp_right_full_faithful
    {A B D : Type*} [Category A] [Category B] [Category D]
    (F : A ⥤ B) (G : B ⥤ D)
    [G.Full] [G.Faithful] [(F ⋙ G).IsEquivalence] :
    F.IsEquivalence := by
  have hFaithful : F.Faithful := by
    constructor
    intro X Y f g hfg
    have hcomp : (F ⋙ G).map f = (F ⋙ G).map g := by
      exact congrArg G.map hfg
    exact (F ⋙ G).map_injective hcomp
  have hFull : F.Full := by
    constructor
    intro X Y φ
    let ψ : X ⟶ Y := (F ⋙ G).preimage (G.map φ)
    refine ⟨ψ, ?_⟩
    apply G.map_injective
    simpa [ψ] using (F ⋙ G).map_preimage (G.map φ)
  have hEss : F.EssSurj := by
    refine { mem_essImage := fun Y => ?_ }
    rcases Functor.EssSurj.mem_essImage (F := F ⋙ G) (G.obj Y) with ⟨X, ⟨e⟩⟩
    exact ⟨X, ⟨(Functor.FullyFaithful.ofFullyFaithful G).preimageIso e⟩⟩
  exact { faithful := hFaithful, full := hFull, essSurj := hEss }

/-- Helper for Chap08 Lemma 8 13 2: the canonical pullback for the composite projection is
identified with the canonical pullback in the original slice projection. -/
private noncomputable def compCanonicalPullback_asCompositeIso
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [q.IsFibered] [(q ⋙ Over.forget U).IsFibered]
    {A B : Over U} (f : A ⟶ B) (x : q.Fiber B) :
    Functor.Fiber.mk (p := q)
        (compCanonicalPullback_obj_over (U := U) q f x) ≅
      (((canonicalFiberPseudofunctor q).map f.op.toLoc).toFunctor.obj x) :=
  compCanonicalPullback_qFiberIso (U := U) q f x

/-- Helper for Chap08 Lemma 8 13 2: the composite canonical pullback of the composite-fiber
view of a `q`-fiber object is canonically the composite-fiber view of the `q`-pullback. -/
private noncomputable def compCanonicalPullback_asCompositeFiberIso
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [q.IsFibered] [(q ⋙ Over.forget U).IsFibered]
    {A B : Over U} (f : A ⟶ B) (x : q.Fiber B) :
    (((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).map f.left.op.toLoc).toFunctor.obj
      (qFiberAsCompositeFiberObj (U := U) q x)) ≅
    qFiberAsCompositeFiberObj (U := U) q
      (((canonicalFiberPseudofunctor q).map f.op.toLoc).toFunctor.obj x) := by
  -- First compare the underlying `q`-fiber pullbacks, then forget the comparison to the
  -- composite fiber and align the canonical source object.
  let eQ := compCanonicalPullback_asCompositeIso (U := U) q f x
  let sourceQ : q.Fiber A :=
    Functor.Fiber.mk (p := q) (compCanonicalPullback_obj_over (U := U) q f x)
  have hsource :
      qFiberAsCompositeFiberObj (U := U) q sourceQ =
        (((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).map f.left.op.toLoc).toFunctor.obj
          (qFiberAsCompositeFiberObj (U := U) q x)) := by
    apply Subtype.ext
    rfl
  exact (eqToIso hsource).symm ≪≫ (qFiberToCompositeFiberFunctor (U := U) q A).mapIso eQ

/-- Helper for Chap08 Lemma 8 13 2: the hom side of the composite/slice canonical-pullback
comparison factors through the chosen composite pullback arrow. -/
private theorem compCanonicalPullback_asCompositeFiberIso_hom_fac
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [q.IsFibered] [(q ⋙ Over.forget U).IsFibered]
    {A B : Over U} (f : A ⟶ B) (x : q.Fiber B) :
    (compCanonicalPullback_asCompositeFiberIso (U := U) q f x).hom.1 ≫
      (canonicalPullbackChoice q).map f x =
    (canonicalPullbackChoice (q ⋙ Over.forget U)).map f.left
      (qFiberAsCompositeFiberObj (U := U) q x) := by
  let eQ := compCanonicalPullback_asCompositeIso (U := U) q f x
  let sourceQ : q.Fiber A :=
    Functor.Fiber.mk (p := q) (compCanonicalPullback_obj_over (U := U) q f x)
  have hsource :
      qFiberAsCompositeFiberObj (U := U) q sourceQ =
        (((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).map f.left.op.toLoc).toFunctor.obj
          (qFiberAsCompositeFiberObj (U := U) q x)) := by
    apply Subtype.ext
    rfl
  have hEqToIso :
      ((eqToIso hsource).symm.hom).1 = 𝟙 _ := by
    cases hsource
    rfl
  dsimp [compCanonicalPullback_asCompositeFiberIso, eQ, sourceQ]
  change (((eqToIso hsource).symm.hom ≫
      (qFiberToCompositeFiberFunctor (U := U) q A).map
        (compCanonicalPullback_asCompositeIso (U := U) q f x).hom).1) ≫
        (canonicalPullbackChoice q).map f x =
    (canonicalPullbackChoice (q ⋙ Over.forget U)).map f.left
      (qFiberAsCompositeFiberObj (U := U) q x)
  change (((eqToIso hsource).symm.hom).1 ≫
      ((qFiberToCompositeFiberFunctor (U := U) q A).map
        (compCanonicalPullback_asCompositeIso (U := U) q f x).hom).1) ≫
        (canonicalPullbackChoice q).map f x =
    (canonicalPullbackChoice (q ⋙ Over.forget U)).map f.left
      (qFiberAsCompositeFiberObj (U := U) q x)
  rw [hEqToIso]
  change (𝟙 _ ≫ (compCanonicalPullback_qFiberIso (U := U) q f x).hom.1) ≫
      (canonicalPullbackChoice q).map f x =
    (canonicalPullbackChoice (q ⋙ Over.forget U)).map f.left
      (qFiberAsCompositeFiberObj (U := U) q x)
  rw [Category.id_comp]
  exact compCanonicalPullback_qFiberIso_hom_fac (U := U) q f x

/-- Helper for Chap08 Lemma 8 13 2: the inverse side of the composite/slice canonical-pullback
comparison factors through the chosen slice pullback arrow. -/
private theorem compCanonicalPullback_asCompositeFiberIso_inv_fac
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [q.IsFibered] [(q ⋙ Over.forget U).IsFibered]
    {A B : Over U} (f : A ⟶ B) (x : q.Fiber B) :
    (compCanonicalPullback_asCompositeFiberIso (U := U) q f x).inv.1 ≫
      (canonicalPullbackChoice (q ⋙ Over.forget U)).map f.left
        (qFiberAsCompositeFiberObj (U := U) q x) =
    (canonicalPullbackChoice q).map f x := by
  rw [← compCanonicalPullback_asCompositeFiberIso_hom_fac (U := U) q f x]
  let e := compCanonicalPullback_asCompositeFiberIso (U := U) q f x
  let z :=
    qFiberAsCompositeFiberObj (U := U) q
      (((canonicalFiberPseudofunctor q).map f.op.toLoc).toFunctor.obj x)
  have hcancel : e.inv.1 ≫ e.hom.1 = 𝟙 z.1 := by
    have hcancel' :
        e.inv.1 ≫ e.hom.1 =
          𝟙 (qFiberAsCompositeFiberObj (U := U) q
            (((canonicalFiberPseudofunctor q).map f.op.toLoc).toFunctor.obj x)).1 := by
      exact congrArg (fun k => k.1) e.inv_hom_id
    simpa [z] using hcancel'
  change e.inv.1 ≫ e.hom.1 ≫ (canonicalPullbackChoice q).map f x =
    (canonicalPullbackChoice q).map f x
  rw [← Category.assoc, hcancel, Category.id_comp]

/-- Helper for Chap08 Lemma 8 13 2: the inverse composite/slice pullback comparison is natural on
vertical morphisms after viewing slice-fiber morphisms in the composite fiber. -/
private theorem compCanonicalPullback_asCompositeFiberIso_inv_naturality
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [q.IsFibered] [(q ⋙ Over.forget U).IsFibered]
    {A B : Over U} (f : A ⟶ B) {x y : q.Fiber B} (φ : x ⟶ y) :
    (compCanonicalPullback_asCompositeFiberIso (U := U) q f x).inv ≫
      ((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).map f.left.op.toLoc).toFunctor.map
        ((qFiberToCompositeFiberFunctor (U := U) q B).map φ) =
    (qFiberToCompositeFiberFunctor (U := U) q A).map
        (((canonicalFiberPseudofunctor q).map f.op.toLoc).toFunctor.map φ) ≫
      (compCanonicalPullback_asCompositeFiberIso (U := U) q f y).inv := by
  let pc := q ⋙ Over.forget U
  let Fcomp := canonicalFiberPseudofunctor pc
  let Fq := canonicalFiberPseudofunctor q
  let ex := compCanonicalPullback_asCompositeFiberIso (U := U) q f x
  let ey := compCanonicalPullback_asCompositeFiberIso (U := U) q f y
  let φc := (qFiberToCompositeFiberFunctor (U := U) q B).map φ
  let φq := ((Fq.map f.op.toLoc).toFunctor.map φ)
  let L := ex.inv ≫ (Fcomp.map f.left.op.toLoc).toFunctor.map φc
  let R := (qFiberToCompositeFiberFunctor (U := U) q A).map φq ≫ ey.inv
  change L = R
  apply Functor.Fiber.hom_ext
  change L.1 = R.1
  let tailY := (canonicalPullbackChoice pc).map f.left (qFiberAsCompositeFiberObj (U := U) q y)
  have htailY : pc.IsCartesian f.left tailY := by
    letI : pc.IsStronglyCartesian f.left tailY := by
      simpa [pc, tailY] using
        (canonicalPullbackChoice pc).isStronglyCartesian f.left
          (qFiberAsCompositeFiberObj (U := U) q y)
    infer_instance
  have hL : pc.IsHomLift (𝟙 A.left) L.1 := by
    simpa [L] using L.2
  have hR : pc.IsHomLift (𝟙 A.left) R.1 := by
    simpa [R] using R.2
  apply @Functor.IsCartesian.ext C S _ _ pc _ _ _ _
    f.left tailY htailY _ L.1 R.1 hL hR
  let tailX := (canonicalPullbackChoice pc).map f.left (qFiberAsCompositeFiberObj (U := U) q x)
  let tailQY := (canonicalPullbackChoice q).map f y
  let tailQX := (canonicalPullbackChoice q).map f x
  have hmapComp :
      (((Fcomp.map f.left.op.toLoc).toFunctor.map φc).1) ≫ tailY =
        tailX ≫ φc.1 := by
    simpa [Fcomp, pc, φc, tailX, tailY] using
      canonical_pullbackFunctor_map_fac
        (p := pc) (f := f.left) (φ := φc)
  have hmapQ :
      φq.1 ≫ tailQY = tailQX ≫ φc.1 := by
    simpa [Fq, φq, φc, tailQX, tailQY, qFiberToCompositeFiberFunctor] using
      canonical_pullbackFunctor_map_fac
        (p := q) (f := f) (φ := φ)
  have hx :
      (ex.inv.1 ≫ tailX) ≫ φc.1 = tailQX ≫ φc.1 := by
    exact congrArg (fun k => k ≫ φc.1)
      (compCanonicalPullback_asCompositeFiberIso_inv_fac (U := U) q f x)
  have hL_expand :
      L.1 ≫ tailY = (ex.inv.1 ≫ tailX) ≫ φc.1 := by
    calc
      L.1 ≫ tailY =
          (ex.inv.1 ≫ ((Fcomp.map f.left.op.toLoc).toFunctor.map φc).1) ≫ tailY := by
        rfl
      _ = ex.inv.1 ≫ (((Fcomp.map f.left.op.toLoc).toFunctor.map φc).1 ≫ tailY) := by
        rw [Category.assoc]
      _ = ex.inv.1 ≫ (tailX ≫ φc.1) := by
        exact congrArg (fun k => ex.inv.1 ≫ k) hmapComp
      _ = (ex.inv.1 ≫ tailX) ≫ φc.1 := by
        rw [Category.assoc]
  have hL_to_q :
      (ex.inv.1 ≫ tailX) ≫ φc.1 = φq.1 ≫ tailQY :=
    hx.trans hmapQ.symm
  have hR_expand :
      φq.1 ≫ tailQY = R.1 ≫ tailY := by
    let θ := (qFiberToCompositeFiberFunctor (U := U) q A).map φq
    have hθ_start :
        φq.1 ≫ tailQY = θ.1 ≫ tailQY := by
      rfl
    have hθ_tail :
        θ.1 ≫ tailQY = θ.1 ≫ (ey.inv.1 ≫ tailY) := by
      exact congrArg (fun k => θ.1 ≫ k)
        (compCanonicalPullback_asCompositeFiberIso_inv_fac (U := U) q f y).symm
    have hR_def :
        R.1 ≫ tailY = (θ.1 ≫ ey.inv.1) ≫ tailY := by
      rfl
    have hθ_assoc :
        θ.1 ≫ (ey.inv.1 ≫ tailY) = R.1 ≫ tailY := by
      rw [hR_def]
      rw [Category.assoc]
    exact hθ_start.trans (hθ_tail.trans hθ_assoc)
  exact (hL_expand.trans hL_to_q).trans hR_expand

/-- Helper for Chap08 Lemma 8 13 2: the hom side of the composite/slice pullback comparison is
natural on vertical morphisms after viewing slice-fiber morphisms in the composite fiber. -/
private theorem compCanonicalPullback_asCompositeFiberIso_hom_naturality
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [q.IsFibered] [(q ⋙ Over.forget U).IsFibered]
    {A B : Over U} (f : A ⟶ B) {x y : q.Fiber B} (φ : x ⟶ y) :
    ((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).map f.left.op.toLoc).toFunctor.map
        ((qFiberToCompositeFiberFunctor (U := U) q B).map φ) ≫
      (compCanonicalPullback_asCompositeFiberIso (U := U) q f y).hom =
    (compCanonicalPullback_asCompositeFiberIso (U := U) q f x).hom ≫
      (qFiberToCompositeFiberFunctor (U := U) q A).map
        (((canonicalFiberPseudofunctor q).map f.op.toLoc).toFunctor.map φ) := by
  let ex := compCanonicalPullback_asCompositeFiberIso (U := U) q f x
  let ey := compCanonicalPullback_asCompositeFiberIso (U := U) q f y
  let α :=
    ((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).map f.left.op.toLoc).toFunctor.map
      ((qFiberToCompositeFiberFunctor (U := U) q B).map φ)
  let β :=
    (qFiberToCompositeFiberFunctor (U := U) q A).map
      (((canonicalFiberPseudofunctor q).map f.op.toLoc).toFunctor.map φ)
  have hinv : ex.inv ≫ α = β ≫ ey.inv := by
    simpa [ex, ey, α, β] using
      compCanonicalPullback_asCompositeFiberIso_inv_naturality (U := U) q f φ
  dsimp [qFiberToCompositeFiberFunctor] at α β
  change α ≫ ey.hom = ex.hom ≫ β
  rw [← cancel_epi ex.inv]
  have hL :
      ex.inv ≫ (α ≫ ey.hom) = β := by
    calc
      ex.inv ≫ (α ≫ ey.hom) =
        (ex.inv ≫ α) ≫ ey.hom := by
            rw [Category.assoc]
      _ = (β ≫ ey.inv) ≫ ey.hom := by
            exact congrArg (fun k => k ≫ ey.hom) hinv
      _ = β ≫ (ey.inv ≫ ey.hom) := by
            rw [Category.assoc]
      _ = β := by
            exact (congrArg (fun k => β ≫ k) ey.inv_hom_id).trans
              (Category.comp_id β)
  have hR :
      ex.inv ≫ (ex.hom ≫ β) = β := by
    rw [← Category.assoc, ex.inv_hom_id, Category.id_comp]
  exact hL.trans hR.symm

/-- Helper for Chap08 Lemma 8 13 2: a base arrow to the target of a slice cover determines
the corresponding object of the slice category over `U`. -/
private abbrev sliceDescentBaseObj
    {A : Over U} {Y : C} (q : Y ⟶ A.left) : Over U :=
  Over.mk (q ≫ A.hom)

/-- Helper for Chap08 Lemma 8 13 2: the slice object associated to a base arrow maps to the
target slice object. -/
private abbrev sliceDescentBaseHom
    {A : Over U} {Y : C} (q : Y ⟶ A.left) :
    sliceDescentBaseObj (U := U) q ⟶ A :=
  Over.homMk q (by rfl)

/-- Helper for Chap08 Lemma 8 13 2: a compatible base change arrow lifts to the corresponding
map between the auxiliary slice objects used in descent comparisons. -/
private abbrev sliceDescentBaseMap
    {A : Over U} {Y' Y : C} (g : Y' ⟶ Y)
    {q : Y ⟶ A.left} {q' : Y' ⟶ A.left} (hq : g ≫ q = q') :
    sliceDescentBaseObj (U := U) q' ⟶ sliceDescentBaseObj (U := U) q :=
  Over.homMk g (by
    change g ≫ q ≫ A.hom = q' ≫ A.hom
    rw [← Category.assoc, hq])

/-- Helper for Chap08 Lemma 8 13 2: the lifted base-change arrow composes with the auxiliary
map to the slice-cover target as expected. -/
private theorem sliceDescentBaseMap_comp_baseHom
    {A : Over U} {Y' Y : C} (g : Y' ⟶ Y)
    {q : Y ⟶ A.left} {q' : Y' ⟶ A.left} (hq : g ≫ q = q') :
    sliceDescentBaseMap (U := U) g hq ≫ sliceDescentBaseHom (U := U) q =
      sliceDescentBaseHom (U := U) q' := by
  ext
  exact hq

/-- Helper for Chap08 Lemma 8 13 2: a factorization through a member of a slice cover lifts to
the corresponding slice arrow. -/
private abbrev sliceDescentLift
    {A : Over U} (T : (J.over U).Cover A) {Y : C} (q : Y ⟶ A.left)
    {I : T.Arrow} (f : Y ⟶ I.Y.left)
    (hf : f ≫ I.f.left = q) :
    sliceDescentBaseObj (U := U) q ⟶ I.Y :=
  Over.homMk f (by
    change f ≫ I.Y.hom = q ≫ A.hom
    rw [← hf, Category.assoc]
    exact congrArg (fun k => f ≫ k) (Over.w I.f).symm)

/-- Helper for Chap08 Lemma 8 13 2: the lifted slice factorization composes back to the
canonical map to the slice-cover target. -/
private theorem sliceDescentLift_comp
    {A : Over U} (T : (J.over U).Cover A) {Y : C} (q : Y ⟶ A.left)
    {I : T.Arrow} (f : Y ⟶ I.Y.left)
    (hf : f ≫ I.f.left = q) :
    sliceDescentLift (J := J) (U := U) T q f hf ≫ I.f =
      sliceDescentBaseHom (U := U) q := by
  ext
  exact hf

/-- Helper for Chap08 Lemma 8 13 2: base change of a lifted slice factorization agrees with
the lifted factorization after base change. -/
private theorem sliceDescentBaseMap_comp_lift
    {A : Over U} (T : (J.over U).Cover A) {Y' Y : C} (g : Y' ⟶ Y)
    {q : Y ⟶ A.left} {q' : Y' ⟶ A.left} (hq : g ≫ q = q')
    {I : T.Arrow} (f : Y ⟶ I.Y.left) (gf : Y' ⟶ I.Y.left)
    (hf : f ≫ I.f.left = q) (hgf : g ≫ f = gf) :
    sliceDescentBaseMap (U := U) g hq ≫
        sliceDescentLift (J := J) (U := U) T q f hf =
      sliceDescentLift (J := J) (U := U) T q' gf
        (by rw [← hq, ← hgf, Category.assoc, hf]) := by
  ext
  exact hgf

/-- Helper for Chap08 Lemma 8 13 2: the overlap morphism of slice descent data, viewed in the
composite projection, is the corresponding slice overlap conjugated by the canonical pullback
comparison. -/
private noncomputable def sliceDescentToCompositeHom
    {S : Type*} [Category S] (p : S ⥤ Over U)
    [p.IsFibered] [(p ⋙ Over.forget U).IsFibered]
    {A : Over U} (T : (J.over U).Cover A)
    (D : (canonicalFiberPseudofunctor p).DescentData (fun I : T.Arrow => I.f))
    {Y : C} (q : Y ⟶ A.left) {I₁ I₂ : T.Arrow}
    (f₁ : Y ⟶ I₁.Y.left) (f₂ : Y ⟶ I₂.Y.left)
    (hf₁ : f₁ ≫ I₁.f.left = q) (hf₂ : f₂ ≫ I₂.f.left = q) :
    (((canonicalFiberPseudofunctor (p ⋙ Over.forget U)).map f₁.op.toLoc).toFunctor.obj
      (qFiberAsCompositeFiberObj (U := U) p (D.obj I₁))) ⟶
    (((canonicalFiberPseudofunctor (p ⋙ Over.forget U)).map f₂.op.toLoc).toFunctor.obj
      (qFiberAsCompositeFiberObj (U := U) p (D.obj I₂))) := by
  let Y₀ : Over U := sliceDescentBaseObj (U := U) q
  let q₀ : Y₀ ⟶ A := sliceDescentBaseHom (U := U) q
  let f₁₀ : Y₀ ⟶ I₁.Y := sliceDescentLift (J := J) (U := U) T q f₁ hf₁
  let f₂₀ : Y₀ ⟶ I₂.Y := sliceDescentLift (J := J) (U := U) T q f₂ hf₂
  have hf₁₀ : f₁₀ ≫ I₁.f = q₀ := by
    simpa [f₁₀, q₀] using sliceDescentLift_comp (J := J) (U := U) T q f₁ hf₁
  have hf₂₀ : f₂₀ ≫ I₂.f = q₀ := by
    simpa [f₂₀, q₀] using sliceDescentLift_comp (J := J) (U := U) T q f₂ hf₂
  let e₁ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₁₀ (D.obj I₁)
  let e₂ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₂₀ (D.obj I₂)
  simpa [Y₀, f₁₀, f₂₀] using
    (e₁.hom ≫
      (qFiberToCompositeFiberFunctor (U := U) p Y₀).map
        (D.hom q₀ f₁₀ f₂₀ hf₁₀ hf₂₀) ≫
      e₂.inv)

/-- Helper for Chap08 Lemma 8 13 2: the composite view of a slice-descent self-overlap is the
identity. -/
private theorem sliceDescentToCompositeHom_self
    {S : Type*} [Category S] (p : S ⥤ Over U)
    [p.IsFibered] [(p ⋙ Over.forget U).IsFibered]
    {A : Over U} (T : (J.over U).Cover A)
    (D : (canonicalFiberPseudofunctor p).DescentData (fun I : T.Arrow => I.f))
    {Y : C} (q : Y ⟶ A.left) {I : T.Arrow}
    (g : Y ⟶ I.Y.left) (hg : g ≫ I.f.left = q) :
    sliceDescentToCompositeHom (J := J) (U := U) p T D q g g hg hg = 𝟙 _ := by
  dsimp [sliceDescentToCompositeHom]
  rw [D.hom_self (sliceDescentBaseHom (U := U) q)
    (sliceDescentLift (J := J) (U := U) T q g hg)
    (sliceDescentLift_comp (J := J) (U := U) T q g hg)]
  have hmid :
      (qFiberToCompositeFiberFunctor (U := U) p
        (sliceDescentBaseObj (U := U) q)).map
          (𝟙 (((canonicalFiberPseudofunctor p).map
            (sliceDescentLift (J := J) (U := U) T q g hg).op.toLoc).toFunctor.obj
              (D.obj I))) = 𝟙 _ := by
    apply Functor.Fiber.hom_ext
    rfl
  rw [hmid]
  calc
    (compCanonicalPullback_asCompositeFiberIso (U := U) p
          (sliceDescentLift (J := J) (U := U) T q g hg) (D.obj I)).hom ≫
        𝟙 _ ≫
          (compCanonicalPullback_asCompositeFiberIso (U := U) p
            (sliceDescentLift (J := J) (U := U) T q g hg) (D.obj I)).inv =
      (compCanonicalPullback_asCompositeFiberIso (U := U) p
          (sliceDescentLift (J := J) (U := U) T q g hg) (D.obj I)).hom ≫
        (compCanonicalPullback_asCompositeFiberIso (U := U) p
          (sliceDescentLift (J := J) (U := U) T q g hg) (D.obj I)).inv := by
        exact congrArg
          (fun k => (compCanonicalPullback_asCompositeFiberIso (U := U) p
            (sliceDescentLift (J := J) (U := U) T q g hg) (D.obj I)).hom ≫ k)
          (Category.id_comp
            (compCanonicalPullback_asCompositeFiberIso (U := U) p
              (sliceDescentLift (J := J) (U := U) T q g hg) (D.obj I)).inv)
    _ = 𝟙 _ :=
      (compCanonicalPullback_asCompositeFiberIso (U := U) p
        (sliceDescentLift (J := J) (U := U) T q g hg) (D.obj I)).hom_inv_id

/-- Helper for Chap08 Lemma 8 13 2: the composite view of slice-descent overlaps preserves the
descent cocycle composition. -/
private theorem sliceDescentToCompositeHom_comp
    {S : Type*} [Category S] (p : S ⥤ Over U)
    [p.IsFibered] [(p ⋙ Over.forget U).IsFibered]
    {A : Over U} (T : (J.over U).Cover A)
    (D : (canonicalFiberPseudofunctor p).DescentData (fun I : T.Arrow => I.f))
    {Y : C} (q : Y ⟶ A.left) {I₁ I₂ I₃ : T.Arrow}
    (f₁ : Y ⟶ I₁.Y.left) (f₂ : Y ⟶ I₂.Y.left) (f₃ : Y ⟶ I₃.Y.left)
    (hf₁ : f₁ ≫ I₁.f.left = q) (hf₂ : f₂ ≫ I₂.f.left = q)
    (hf₃ : f₃ ≫ I₃.f.left = q) :
    sliceDescentToCompositeHom (J := J) (U := U) p T D q f₁ f₂ hf₁ hf₂ ≫
      sliceDescentToCompositeHom (J := J) (U := U) p T D q f₂ f₃ hf₂ hf₃ =
    sliceDescentToCompositeHom (J := J) (U := U) p T D q f₁ f₃ hf₁ hf₃ := by
  let Y₀ : Over U := sliceDescentBaseObj (U := U) q
  let q₀ : Y₀ ⟶ A := sliceDescentBaseHom (U := U) q
  let f₁₀ : Y₀ ⟶ I₁.Y := sliceDescentLift (J := J) (U := U) T q f₁ hf₁
  let f₂₀ : Y₀ ⟶ I₂.Y := sliceDescentLift (J := J) (U := U) T q f₂ hf₂
  let f₃₀ : Y₀ ⟶ I₃.Y := sliceDescentLift (J := J) (U := U) T q f₃ hf₃
  have hf₁₀ : f₁₀ ≫ I₁.f = q₀ := by
    simpa [f₁₀, q₀] using sliceDescentLift_comp (J := J) (U := U) T q f₁ hf₁
  have hf₂₀ : f₂₀ ≫ I₂.f = q₀ := by
    simpa [f₂₀, q₀] using sliceDescentLift_comp (J := J) (U := U) T q f₂ hf₂
  have hf₃₀ : f₃₀ ≫ I₃.f = q₀ := by
    simpa [f₃₀, q₀] using sliceDescentLift_comp (J := J) (U := U) T q f₃ hf₃
  let F := qFiberToCompositeFiberFunctor (U := U) p Y₀
  let e₁ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₁₀ (D.obj I₁)
  let e₂ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₂₀ (D.obj I₂)
  let e₃ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₃₀ (D.obj I₃)
  let d₁₂ := D.hom q₀ f₁₀ f₂₀ hf₁₀ hf₂₀
  let d₂₃ := D.hom q₀ f₂₀ f₃₀ hf₂₀ hf₃₀
  let d₁₃ := D.hom q₀ f₁₀ f₃₀ hf₁₀ hf₃₀
  change (e₁.hom ≫ F.map d₁₂ ≫ e₂.inv) ≫
      e₂.hom ≫ F.map d₂₃ ≫ e₃.inv =
    e₁.hom ≫ F.map d₁₃ ≫ e₃.inv
  have hd : d₁₂ ≫ d₂₃ = d₁₃ := by
    exact D.hom_comp q₀ f₁₀ f₂₀ f₃₀ hf₁₀ hf₂₀ hf₃₀
  have hcancel :
      e₁.hom ≫ F.map d₁₂ ≫ (e₂.inv ≫ e₂.hom) ≫ F.map d₂₃ ≫ e₃.inv =
        e₁.hom ≫ F.map d₁₂ ≫ F.map d₂₃ ≫ e₃.inv := by
    calc
      e₁.hom ≫ F.map d₁₂ ≫ (e₂.inv ≫ e₂.hom) ≫ F.map d₂₃ ≫ e₃.inv =
          e₁.hom ≫ F.map d₁₂ ≫ 𝟙 _ ≫ F.map d₂₃ ≫ e₃.inv := by
        exact congrArg
          (fun k => e₁.hom ≫ F.map d₁₂ ≫ k ≫ F.map d₂₃ ≫ e₃.inv)
          e₂.inv_hom_id
      _ = e₁.hom ≫ F.map d₁₂ ≫ F.map d₂₃ ≫ e₃.inv := by
        simp only [Category.id_comp]
  calc
    (e₁.hom ≫ F.map d₁₂ ≫ e₂.inv) ≫ e₂.hom ≫ F.map d₂₃ ≫ e₃.inv =
        e₁.hom ≫ F.map d₁₂ ≫ (e₂.inv ≫ e₂.hom) ≫ F.map d₂₃ ≫ e₃.inv := by
      simp only [Category.assoc]
    _ = e₁.hom ≫ F.map d₁₂ ≫ F.map d₂₃ ≫ e₃.inv := hcancel
    _ = e₁.hom ≫ (F.map d₁₂ ≫ F.map d₂₃) ≫ e₃.inv := by
      simp only [Category.assoc]
    _ = e₁.hom ≫ F.map (d₁₂ ≫ d₂₃) ≫ e₃.inv := by
      exact congrArg (fun k => e₁.hom ≫ k ≫ e₃.inv) (F.map_comp d₁₂ d₂₃).symm
    _ = e₁.hom ≫ F.map d₁₃ ≫ e₃.inv := by
      exact congrArg (fun k => e₁.hom ≫ F.map k ≫ e₃.inv) hd

/-- Helper for Chap08 Lemma 8 13 2: the left `pullHom` boundary for the composite/slice
canonical-pullback comparison normalizes to the strict composite-leg shell. -/
private theorem compCanonicalPullback_asCompositeFiberIso_pullHom_left_boundary
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [q.IsFibered] [(q ⋙ Over.forget U).IsFibered]
    {A B D : Over U} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) (x : q.Fiber D) :
    (((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).mapComp'
          f.left.op.toLoc g.left.op.toLoc gf.left.op.toLoc
          (comp_toLoc_eq f.left g.left gf.left
            (by simpa using congrArg (fun k => k.left) hgf))).hom.toNatTrans.app
        (qFiberAsCompositeFiberObj (U := U) q x)) ≫
      (((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).map g.left.op.toLoc).toFunctor.map
        (compCanonicalPullback_asCompositeFiberIso (U := U) q f x).hom) =
    (compCanonicalPullback_asCompositeFiberIso (U := U) q gf x).hom ≫
      (qFiberToCompositeFiberFunctor (U := U) q A).map
        (((canonicalFiberPseudofunctor q).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
      (compCanonicalPullback_asCompositeFiberIso (U := U) q g
        (((canonicalFiberPseudofunctor q).map f.op.toLoc).toFunctor.obj x)).inv := by
  let pc := q ⋙ Over.forget U
  let Fcomp := canonicalFiberPseudofunctor pc
  let Fq := canonicalFiberPseudofunctor q
  have hgf_left : g.left ≫ f.left = gf.left := by
    simpa using congrArg (fun k => k.left) hgf
  let leftTarget :=
    ((Fcomp.mapComp'
        f.left.op.toLoc g.left.op.toLoc gf.left.op.toLoc
        (comp_toLoc_eq f.left g.left gf.left hgf_left)).hom.toNatTrans.app
      (qFiberAsCompositeFiberObj (U := U) q x))
  let leftSource :=
    ((Fq.mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x)
  let ef := compCanonicalPullback_asCompositeFiberIso (U := U) q f x
  let egf := compCanonicalPullback_asCompositeFiberIso (U := U) q gf x
  let cg := compCanonicalPullback_asCompositeFiberIso (U := U) q g
    ((Fq.map f.op.toLoc).toFunctor.obj x)
  let raw := leftTarget ≫ (Fcomp.map g.left.op.toLoc).toFunctor.map ef.hom
  let strict :=
    egf.hom ≫ (qFiberToCompositeFiberFunctor (U := U) q A).map leftSource ≫ cg.inv
  change raw = strict
  apply Functor.Fiber.hom_ext
  change raw.1 = strict.1
  let tailgTarget :=
    (canonicalPullbackChoice pc).map g.left
      (qFiberAsCompositeFiberObj (U := U) q ((Fq.map f.op.toLoc).toFunctor.obj x))
  let tailfQ := (canonicalPullbackChoice q).map f x
  let tail := tailgTarget ≫ tailfQ
  have htailgTarget : pc.IsStronglyCartesian g.left tailgTarget := by
    exact (canonicalPullbackChoice pc).isStronglyCartesian g.left
      (qFiberAsCompositeFiberObj (U := U) q ((Fq.map f.op.toLoc).toFunctor.obj x))
  have htailfQq : q.IsStronglyCartesian f tailfQ := by
    exact (canonicalPullbackChoice q).isStronglyCartesian f x
  have htailfQpcMap : pc.IsStronglyCartesian (pc.map tailfQ) tailfQ := by
    have htailfQqMap : q.IsStronglyCartesian (q.map tailfQ) tailfQ := by
      letI : q.IsStronglyCartesian f tailfQ := htailfQq
      exact isStronglyCartesian_rebase_to_map (p := q) (f := f) tailfQ
    letI : q.IsStronglyCartesian (q.map tailfQ) tailfQ := htailfQqMap
    letI : (Over.forget U).IsStronglyCartesian
        ((Over.forget U).map (q.map tailfQ)) (q.map tailfQ) :=
      (inferInstance : IsFibredInGroupoids (Over.forget U)).isStronglyCartesian_map
        (q.map tailfQ)
    change pc.IsStronglyCartesian (pc.map tailfQ) tailfQ
    simpa [pc] using
      Functor.isStronglyCartesian_map_comp q (Over.forget U) tailfQ
  have htailfQpc_lift : pc.IsHomLift f.left tailfQ := by
    exact isHomLift_comp_of_isHomLift_for_boundary q (Over.forget U) htailfQq.toIsHomLift
  have htailfQpc : pc.IsStronglyCartesian f.left tailfQ := by
    letI : pc.IsStronglyCartesian (pc.map tailfQ) tailfQ := htailfQpcMap
    exact isStronglyCartesian_rebase_of_isHomLift (p := pc)
      (f := f.left) tailfQ htailfQpc_lift
  have htail : pc.IsStronglyCartesian (g.left ≫ f.left) tail := by
    letI : pc.IsStronglyCartesian g.left tailgTarget := htailgTarget
    letI : pc.IsStronglyCartesian f.left tailfQ := htailfQpc
    change pc.IsStronglyCartesian (g.left ≫ f.left) (tailgTarget ≫ tailfQ)
    exact
      @Functor.IsStronglyCartesian.comp C S _ _ pc
        A.left B.left D.left _ _ _ g.left f.left tailgTarget tailfQ
        htailgTarget htailfQpc
  let tailgSource :=
    (canonicalPullbackChoice pc).map g.left
      (((Fcomp.map f.left.op.toLoc).toFunctor.obj
        (qFiberAsCompositeFiberObj (U := U) q x)))
  let tailfComp :=
    (canonicalPullbackChoice pc).map f.left (qFiberAsCompositeFiberObj (U := U) q x)
  let tailgfComp :=
    (canonicalPullbackChoice pc).map gf.left (qFiberAsCompositeFiberObj (U := U) q x)
  let tailgQ :=
    (canonicalPullbackChoice q).map g ((Fq.map f.op.toLoc).toFunctor.obj x)
  let tailgfQ := (canonicalPullbackChoice q).map gf x
  have hmapEf :
      (((Fcomp.map g.left.op.toLoc).toFunctor.map ef.hom).1) ≫ tailgTarget =
        tailgSource ≫ ef.hom.1 := by
    simpa [Fcomp, pc, ef, tailgSource, tailgTarget] using
      canonical_pullbackFunctor_map_fac
        (p := pc) (f := g.left) (φ := ef.hom)
  have hleftTarget_fac :
      leftTarget.1 ≫ tailgSource ≫ tailfComp = tailgfComp := by
    simpa [Fcomp, pc, leftTarget, tailgSource, tailfComp, tailgfComp] using
      canonicalFiberPseudofunctor_mapComp'_hom_app_fac
        (p := pc) (f := f.left) (g := g.left) (gf := gf.left)
        (hgf := hgf_left) (x := qFiberAsCompositeFiberObj (U := U) q x)
  have hraw_post :
      raw.1 ≫ tail = tailgfComp := by
    have hraw_pre :
        raw.1 ≫ tail = leftTarget.1 ≫ tailgSource ≫ tailfComp := by
      calc
        raw.1 ≫ tail =
            (leftTarget.1 ≫ (((Fcomp.map g.left.op.toLoc).toFunctor.map ef.hom).1)) ≫
              tailgTarget ≫ tailfQ := by
          rfl
        _ = leftTarget.1 ≫
              ((((Fcomp.map g.left.op.toLoc).toFunctor.map ef.hom).1) ≫ tailgTarget) ≫
              tailfQ := by
          simp only [Category.assoc]
        _ = leftTarget.1 ≫ (tailgSource ≫ ef.hom.1) ≫ tailfQ := by
          exact congrArg (fun k => leftTarget.1 ≫ k ≫ tailfQ) hmapEf
        _ = leftTarget.1 ≫ tailgSource ≫ (ef.hom.1 ≫ tailfQ) := by
          simp only [Category.assoc]
        _ = leftTarget.1 ≫ tailgSource ≫ tailfComp := by
          exact congrArg (fun k => leftTarget.1 ≫ tailgSource ≫ k)
            (compCanonicalPullback_asCompositeFiberIso_hom_fac (U := U) q f x)
    exact hraw_pre.trans hleftTarget_fac
  have hcg_inv :
      cg.inv.1 ≫ tailgTarget = tailgQ := by
    exact compCanonicalPullback_asCompositeFiberIso_inv_fac (U := U) q g
      ((Fq.map f.op.toLoc).toFunctor.obj x)
  have hleftSource_fac :
      leftSource.1 ≫ tailgQ ≫ tailfQ = tailgfQ := by
    simpa [Fq, leftSource, tailgQ, tailfQ, tailgfQ] using
      canonicalFiberPseudofunctor_mapComp'_hom_app_fac
        (p := q) (f := f) (g := g) (gf := gf) (hgf := hgf) (x := x)
  have hstrict_post :
      strict.1 ≫ tail = tailgfComp := by
    calc
      strict.1 ≫ tail =
          (egf.hom.1 ≫ ((qFiberToCompositeFiberFunctor (U := U) q A).map leftSource).1 ≫
            cg.inv.1) ≫ tailgTarget ≫ tailfQ := by
        rfl
      _ = egf.hom.1 ≫ ((qFiberToCompositeFiberFunctor (U := U) q A).map leftSource).1 ≫
            cg.inv.1 ≫ tailgTarget ≫ tailfQ := by
        simp only [Category.assoc]
      _ = egf.hom.1 ≫ ((qFiberToCompositeFiberFunctor (U := U) q A).map leftSource).1 ≫
            (cg.inv.1 ≫ tailgTarget) ≫ tailfQ := by
        simp only [Category.assoc]
      _ = egf.hom.1 ≫ leftSource.1 ≫ tailgQ ≫ tailfQ := by
        exact congrArg
          (fun k => egf.hom.1 ≫
            ((qFiberToCompositeFiberFunctor (U := U) q A).map leftSource).1 ≫ k ≫ tailfQ)
          hcg_inv
      _ = egf.hom.1 ≫ (leftSource.1 ≫ tailgQ ≫ tailfQ) := by
        simp only [Category.assoc]
      _ = egf.hom.1 ≫ tailgfQ := by
        exact congrArg (fun k => egf.hom.1 ≫ k) hleftSource_fac
      _ = tailgfComp := by
        exact compCanonicalPullback_asCompositeFiberIso_hom_fac (U := U) q gf x
  have hrawtail : pc.IsHomLift (g.left ≫ f.left) (raw.1 ≫ tail) := by
    exact @IsHomLift.comp_lift_id_left' C S _ _ pc _ _ _
      A.left raw.1 raw.2 _ _ (g.left ≫ f.left) tail htail.toIsHomLift
  have hstricttail : pc.IsHomLift (g.left ≫ f.left) (strict.1 ≫ tail) := by
    exact @IsHomLift.comp_lift_id_left' C S _ _ pc _ _ _
      A.left strict.1 strict.2 _ _ (g.left ≫ f.left) tail htail.toIsHomLift
  exact
    @Functor.IsStronglyCartesian.ext C S _ _ pc _ _ _ _
      (g.left ≫ f.left) tail htail _ _ (𝟙 A.left)
      raw.1 strict.1 raw.2 strict.2 (hraw_post.trans hstrict_post.symm)

/-- Helper for Chap08 Lemma 8 13 2: the right `pullHom` boundary for the composite/slice
canonical-pullback comparison is the inverse shell of the left boundary. -/
private theorem compCanonicalPullback_asCompositeFiberIso_pullHom_right_boundary
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [q.IsFibered] [(q ⋙ Over.forget U).IsFibered]
    {A B D : Over U} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) (x : q.Fiber D) :
    (compCanonicalPullback_asCompositeFiberIso (U := U) q g
        (((canonicalFiberPseudofunctor q).map f.op.toLoc).toFunctor.obj x)).inv ≫
      (((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).map g.left.op.toLoc).toFunctor.map
        (compCanonicalPullback_asCompositeFiberIso (U := U) q f x).inv) ≫
      (((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).mapComp'
          f.left.op.toLoc g.left.op.toLoc gf.left.op.toLoc
          (comp_toLoc_eq f.left g.left gf.left
            (by simpa using congrArg (fun k => k.left) hgf))).inv.toNatTrans.app
        (qFiberAsCompositeFiberObj (U := U) q x)) =
    (qFiberToCompositeFiberFunctor (U := U) q A).map
        (((canonicalFiberPseudofunctor q).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app x) ≫
      (compCanonicalPullback_asCompositeFiberIso (U := U) q gf x).inv := by
  let pc := q ⋙ Over.forget U
  let Fcomp := canonicalFiberPseudofunctor pc
  let Fq := canonicalFiberPseudofunctor q
  have hgf_left : g.left ≫ f.left = gf.left := by
    simpa using congrArg (fun k => k.left) hgf
  let targetComp :=
    Fcomp.mapComp'
      f.left.op.toLoc g.left.op.toLoc gf.left.op.toLoc
      (comp_toLoc_eq f.left g.left gf.left hgf_left)
  let targetIso :
      ((Fcomp.map gf.left.op.toLoc).toFunctor.obj (qFiberAsCompositeFiberObj (U := U) q x)) ≅
        ((Fcomp.map g.left.op.toLoc).toFunctor.obj
          ((Fcomp.map f.left.op.toLoc).toFunctor.obj
            (qFiberAsCompositeFiberObj (U := U) q x))) :=
    { hom := (targetComp.hom).toNatTrans.app _
      inv := (targetComp.inv).toNatTrans.app _
      hom_inv_id := by
        exact Cat.Hom.hom_inv_id_toNatTrans_app targetComp
          (qFiberAsCompositeFiberObj (U := U) q x)
      inv_hom_id := by
        exact Cat.Hom.inv_hom_id_toNatTrans_app targetComp
          (qFiberAsCompositeFiberObj (U := U) q x) }
  let sourceComp :=
    Fq.mapComp'
      f.op.toLoc g.op.toLoc gf.op.toLoc
      (comp_toLoc_eq f g gf hgf)
  let sourceIso :
      ((Fq.map gf.op.toLoc).toFunctor.obj x) ≅
        ((Fq.map g.op.toLoc).toFunctor.obj
          ((Fq.map f.op.toLoc).toFunctor.obj x)) :=
    { hom := (sourceComp.hom).toNatTrans.app x
      inv := (sourceComp.inv).toNatTrans.app x
      hom_inv_id := by
        exact Cat.Hom.hom_inv_id_toNatTrans_app sourceComp x
      inv_hom_id := by
        exact Cat.Hom.inv_hom_id_toNatTrans_app sourceComp x }
  let ef := compCanonicalPullback_asCompositeFiberIso (U := U) q f x
  let egf := compCanonicalPullback_asCompositeFiberIso (U := U) q gf x
  let cg := compCanonicalPullback_asCompositeFiberIso (U := U) q g
    ((Fq.map f.op.toLoc).toFunctor.obj x)
  let L :=
    targetIso ≪≫ ((Fcomp.map g.left.op.toLoc).toFunctor.mapIso ef)
  let R :=
    egf ≪≫ (qFiberToCompositeFiberFunctor (U := U) q A).mapIso sourceIso ≪≫ cg.symm
  have hhom : L.hom = R.hom := by
    change
      targetIso.hom ≫ ((Fcomp.map g.left.op.toLoc).toFunctor.map ef.hom) =
        egf.hom ≫
          (qFiberToCompositeFiberFunctor (U := U) q A).map sourceIso.hom ≫
          cg.inv
    simpa [targetIso, sourceIso, ef, egf, cg, Fcomp, Fq, pc] using
      compCanonicalPullback_asCompositeFiberIso_pullHom_left_boundary
        (U := U) q f g gf hgf x
  have hIso : L = R := by
    apply Iso.ext
    exact hhom
  have hinv : L.inv = R.inv := by
    exact congrArg (fun e => e.inv) hIso
  change
    cg.inv ≫ ((Fcomp.map g.left.op.toLoc).toFunctor.map ef.inv) ≫ targetIso.inv =
      (qFiberToCompositeFiberFunctor (U := U) q A).map sourceIso.inv ≫ egf.inv
  have hinv_expanded :
      ((Fcomp.map g.left.op.toLoc).toFunctor.map ef.inv) ≫ targetIso.inv =
        cg.hom ≫
          (qFiberToCompositeFiberFunctor (U := U) q A).map sourceIso.inv ≫ egf.inv := by
    simpa [L, R, targetIso, sourceIso, ef, egf, cg, Iso.trans_inv,
      Functor.mapIso_inv] using hinv
  calc
    cg.inv ≫ ((Fcomp.map g.left.op.toLoc).toFunctor.map ef.inv) ≫ targetIso.inv =
        cg.inv ≫ (((Fcomp.map g.left.op.toLoc).toFunctor.map ef.inv) ≫ targetIso.inv) := by
      simp only [Category.assoc]
    _ = cg.inv ≫ (cg.hom ≫
          (qFiberToCompositeFiberFunctor (U := U) q A).map sourceIso.inv ≫ egf.inv) := by
      exact congrArg (fun k => cg.inv ≫ k) hinv_expanded
    _ = (qFiberToCompositeFiberFunctor (U := U) q A).map sourceIso.inv ≫ egf.inv := by
      rw [← Category.assoc, cg.inv_hom_id, Category.id_comp]
      rfl

/-- Helper for Chap08 Lemma 8 13 2: the composite view of a slice-descent overlap is compatible
with further pullback. -/
private theorem sliceDescentToCompositeHom_pullHom_hom
    {S : Type*} [Category S] (p : S ⥤ Over U)
    [p.IsFibered] [(p ⋙ Over.forget U).IsFibered]
    {A : Over U} (T : (J.over U).Cover A)
    (D : (canonicalFiberPseudofunctor p).DescentData (fun I : T.Arrow => I.f))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ A.left) (q' : Y' ⟶ A.left)
    (hq : g ≫ q = q')
    {I₁ I₂ : T.Arrow} (f₁ : Y ⟶ I₁.Y.left) (f₂ : Y ⟶ I₂.Y.left)
    (hf₁ : f₁ ≫ I₁.f.left = q) (hf₂ : f₂ ≫ I₂.f.left = q)
    (gf₁ : Y' ⟶ I₁.Y.left) (gf₂ : Y' ⟶ I₂.Y.left)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (sliceDescentToCompositeHom (J := J) (U := U) p T D q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      sliceDescentToCompositeHom (J := J) (U := U) p T D q' gf₁ gf₂
        (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
        (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) := by
  let Y₀ : Over U := sliceDescentBaseObj (U := U) q
  let Y₀' : Over U := sliceDescentBaseObj (U := U) q'
  let g₀ : Y₀' ⟶ Y₀ := sliceDescentBaseMap (U := U) g hq
  let q₀ : Y₀ ⟶ A := sliceDescentBaseHom (U := U) q
  let q₀' : Y₀' ⟶ A := sliceDescentBaseHom (U := U) q'
  have hgq₀ : g₀ ≫ q₀ = q₀' := by
    simpa [g₀, q₀, q₀'] using sliceDescentBaseMap_comp_baseHom (U := U) g hq
  let f₁₀ : Y₀ ⟶ I₁.Y := sliceDescentLift (J := J) (U := U) T q f₁ hf₁
  let f₂₀ : Y₀ ⟶ I₂.Y := sliceDescentLift (J := J) (U := U) T q f₂ hf₂
  have hgf₁_fac : gf₁ ≫ I₁.f.left = q' := by
    rw [← hq, ← hgf₁, Category.assoc, hf₁]
  have hgf₂_fac : gf₂ ≫ I₂.f.left = q' := by
    rw [← hq, ← hgf₂, Category.assoc, hf₂]
  let gf₁₀ : Y₀' ⟶ I₁.Y := sliceDescentLift (J := J) (U := U) T q' gf₁ hgf₁_fac
  let gf₂₀ : Y₀' ⟶ I₂.Y := sliceDescentLift (J := J) (U := U) T q' gf₂ hgf₂_fac
  have hf₁₀ : f₁₀ ≫ I₁.f = q₀ := by
    simpa [f₁₀, q₀] using sliceDescentLift_comp (J := J) (U := U) T q f₁ hf₁
  have hf₂₀ : f₂₀ ≫ I₂.f = q₀ := by
    simpa [f₂₀, q₀] using sliceDescentLift_comp (J := J) (U := U) T q f₂ hf₂
  have hgf₁₀_fac : gf₁₀ ≫ I₁.f = q₀' := by
    simpa [gf₁₀, q₀'] using
      sliceDescentLift_comp (J := J) (U := U) T q' gf₁ hgf₁_fac
  have hgf₂₀_fac : gf₂₀ ≫ I₂.f = q₀' := by
    simpa [gf₂₀, q₀'] using
      sliceDescentLift_comp (J := J) (U := U) T q' gf₂ hgf₂_fac
  have hgf₁₀ : g₀ ≫ f₁₀ = gf₁₀ := by
    simpa [g₀, f₁₀, gf₁₀] using
      sliceDescentBaseMap_comp_lift (J := J) (U := U) T g hq f₁ gf₁ hf₁ hgf₁
  have hgf₂₀ : g₀ ≫ f₂₀ = gf₂₀ := by
    simpa [g₀, f₂₀, gf₂₀] using
      sliceDescentBaseMap_comp_lift (J := J) (U := U) T g hq f₂ gf₂ hf₂ hgf₂
  let Fcomp := canonicalFiberPseudofunctor (p ⋙ Over.forget U)
  let Fq := canonicalFiberPseudofunctor p
  let FYg := (Fcomp.map g.op.toLoc).toFunctor
  let FXg := (Fq.map g₀.op.toLoc).toFunctor
  let FY₀ := qFiberToCompositeFiberFunctor (U := U) p Y₀
  let FY₀' := qFiberToCompositeFiberFunctor (U := U) p Y₀'
  let d := D.hom q₀ f₁₀ f₂₀ hf₁₀ hf₂₀
  let e₁ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₁₀ (D.obj I₁)
  let e₂ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₂₀ (D.obj I₂)
  let eg₁ := compCanonicalPullback_asCompositeFiberIso (U := U) p gf₁₀ (D.obj I₁)
  let eg₂ := compCanonicalPullback_asCompositeFiberIso (U := U) p gf₂₀ (D.obj I₂)
  let cg₁ := compCanonicalPullback_asCompositeFiberIso (U := U) p g₀
    ((Fq.map f₁₀.op.toLoc).toFunctor.obj (D.obj I₁))
  let cg₂ := compCanonicalPullback_asCompositeFiberIso (U := U) p g₀
    ((Fq.map f₂₀.op.toLoc).toFunctor.obj (D.obj I₂))
  let leftTarget :=
    ((Fcomp.mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
      (qFiberAsCompositeFiberObj (U := U) p (D.obj I₁)))
  let rightTarget :=
    ((Fcomp.mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
      (qFiberAsCompositeFiberObj (U := U) p (D.obj I₂)))
  let leftSource :=
    ((Fq.mapComp'
        f₁₀.op.toLoc g₀.op.toLoc gf₁₀.op.toLoc
        (comp_toLoc_eq f₁₀ g₀ gf₁₀ hgf₁₀)).hom.toNatTrans.app (D.obj I₁))
  let rightSource :=
    ((Fq.mapComp'
        f₂₀.op.toLoc g₀.op.toLoc gf₂₀.op.toLoc
        (comp_toLoc_eq f₂₀ g₀ gf₂₀ hgf₂₀)).inv.toNatTrans.app (D.obj I₂))
  have hunfolded :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (sliceDescentToCompositeHom (J := J) (U := U) p T D q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ =
        leftTarget ≫ FYg.map (e₁.hom ≫ FY₀.map d ≫ e₂.inv) ≫ rightTarget := by
    rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
    dsimp [sliceDescentToCompositeHom]
    rfl
  have hmap' :
      leftTarget ≫ FYg.map (e₁.hom ≫ FY₀.map d ≫ e₂.inv) ≫ rightTarget =
        leftTarget ≫ FYg.map e₁.hom ≫ FYg.map (FY₀.map d) ≫
          FYg.map e₂.inv ≫ rightTarget := by
    calc
      leftTarget ≫ FYg.map (e₁.hom ≫ FY₀.map d ≫ e₂.inv) ≫ rightTarget =
          leftTarget ≫ (FYg.map e₁.hom ≫ FYg.map (FY₀.map d) ≫ FYg.map e₂.inv) ≫
            rightTarget := by
        exact congrArg (fun k => leftTarget ≫ k ≫ rightTarget)
          (functor_map_threefold_comp FYg e₁.hom (FY₀.map d) e₂.inv)
      _ = leftTarget ≫ FYg.map e₁.hom ≫ FYg.map (FY₀.map d) ≫
          FYg.map e₂.inv ≫ rightTarget := by
        simp only [Category.assoc]
  have hleftBoundary :
      leftTarget ≫ FYg.map e₁.hom =
        eg₁.hom ≫ FY₀'.map leftSource ≫ cg₁.inv := by
    simpa [Fcomp, Fq, FYg, FY₀', leftTarget, leftSource, e₁, eg₁, cg₁,
      f₁₀, g₀, gf₁₀] using
      compCanonicalPullback_asCompositeFiberIso_pullHom_left_boundary
        (U := U) p f₁₀ g₀ gf₁₀ hgf₁₀ (D.obj I₁)
  have hleft' :
      leftTarget ≫ FYg.map e₁.hom ≫ FYg.map (FY₀.map d) ≫
          FYg.map e₂.inv ≫ rightTarget =
        eg₁.hom ≫ FY₀'.map leftSource ≫ cg₁.inv ≫
          FYg.map (FY₀.map d) ≫ FYg.map e₂.inv ≫ rightTarget := by
    calc
      leftTarget ≫ FYg.map e₁.hom ≫ FYg.map (FY₀.map d) ≫
          FYg.map e₂.inv ≫ rightTarget =
        (leftTarget ≫ FYg.map e₁.hom) ≫ FYg.map (FY₀.map d) ≫
          FYg.map e₂.inv ≫ rightTarget := by
          simp only [Category.assoc]
      _ =
        (eg₁.hom ≫ FY₀'.map leftSource ≫ cg₁.inv) ≫ FYg.map (FY₀.map d) ≫
          FYg.map e₂.inv ≫ rightTarget := by
          exact congrArg
            (fun k => k ≫ FYg.map (FY₀.map d) ≫ FYg.map e₂.inv ≫ rightTarget)
            hleftBoundary
      _ =
        eg₁.hom ≫ FY₀'.map leftSource ≫ cg₁.inv ≫
          FYg.map (FY₀.map d) ≫ FYg.map e₂.inv ≫ rightTarget := by
          simp only [Category.assoc]
  have hmidBoundary :
      cg₁.inv ≫ FYg.map (FY₀.map d) =
        FY₀'.map (FXg.map d) ≫ cg₂.inv := by
    simpa [Fcomp, Fq, FYg, FXg, FY₀, FY₀', d, cg₁, cg₂, g₀] using
      compCanonicalPullback_asCompositeFiberIso_inv_naturality
        (U := U) p g₀ (φ := d)
  have hmid' :
      eg₁.hom ≫ FY₀'.map leftSource ≫ cg₁.inv ≫
          FYg.map (FY₀.map d) ≫ FYg.map e₂.inv ≫ rightTarget =
        eg₁.hom ≫ FY₀'.map leftSource ≫ FY₀'.map (FXg.map d) ≫
          cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget := by
    calc
      eg₁.hom ≫ FY₀'.map leftSource ≫ cg₁.inv ≫
          FYg.map (FY₀.map d) ≫ FYg.map e₂.inv ≫ rightTarget =
        eg₁.hom ≫ FY₀'.map leftSource ≫
          (cg₁.inv ≫ FYg.map (FY₀.map d)) ≫ FYg.map e₂.inv ≫ rightTarget := by
          simp only [Category.assoc]
      _ =
        eg₁.hom ≫ FY₀'.map leftSource ≫
          (FY₀'.map (FXg.map d) ≫ cg₂.inv) ≫ FYg.map e₂.inv ≫ rightTarget := by
          exact congrArg
            (fun k => eg₁.hom ≫ FY₀'.map leftSource ≫ k ≫
              FYg.map e₂.inv ≫ rightTarget)
            hmidBoundary
      _ =
        eg₁.hom ≫ FY₀'.map leftSource ≫ FY₀'.map (FXg.map d) ≫
          cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget := by
          simp only [Category.assoc]
  have hrightBoundary :
      cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget =
        FY₀'.map rightSource ≫ eg₂.inv := by
    simpa [Fcomp, Fq, FYg, FY₀', rightTarget, rightSource, e₂, eg₂, cg₂,
      f₂₀, g₀, gf₂₀] using
      compCanonicalPullback_asCompositeFiberIso_pullHom_right_boundary
        (U := U) p f₂₀ g₀ gf₂₀ hgf₂₀ (D.obj I₂)
  have hright' :
      eg₁.hom ≫ FY₀'.map leftSource ≫ FY₀'.map (FXg.map d) ≫
          cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget =
        eg₁.hom ≫ FY₀'.map leftSource ≫ FY₀'.map (FXg.map d) ≫
          FY₀'.map rightSource ≫ eg₂.inv := by
    calc
      eg₁.hom ≫ FY₀'.map leftSource ≫ FY₀'.map (FXg.map d) ≫
          cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget =
        eg₁.hom ≫ FY₀'.map leftSource ≫ FY₀'.map (FXg.map d) ≫
          (cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget) := by
          simp only [Category.assoc]
      _ =
        eg₁.hom ≫ FY₀'.map leftSource ≫ FY₀'.map (FXg.map d) ≫
          (FY₀'.map rightSource ≫ eg₂.inv) := by
          exact congrArg
            (fun k => eg₁.hom ≫ FY₀'.map leftSource ≫ FY₀'.map (FXg.map d) ≫ k)
            hrightBoundary
      _ =
        eg₁.hom ≫ FY₀'.map leftSource ≫ FY₀'.map (FXg.map d) ≫
          FY₀'.map rightSource ≫ eg₂.inv := by
          simp only [Category.assoc]
  have hfold :
      FY₀'.map leftSource ≫ FY₀'.map (FXg.map d) ≫ FY₀'.map rightSource =
        FY₀'.map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            d g₀ gf₁₀ gf₂₀ hgf₁₀ hgf₂₀) := by
    change
      FY₀'.map leftSource ≫ FY₀'.map (FXg.map d) ≫ FY₀'.map rightSource =
        FY₀'.map (leftSource ≫ FXg.map d ≫ rightSource)
    rw [functor_map_threefold_comp]
  have hsourcePull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          d g₀ gf₁₀ gf₂₀ hgf₁₀ hgf₂₀ =
        D.hom q₀' gf₁₀ gf₂₀ hgf₁₀_fac hgf₂₀_fac := by
    exact D.pullHom_hom g₀ q₀ q₀' hgq₀ f₁₀ f₂₀ hf₁₀ hf₂₀ gf₁₀ gf₂₀ hgf₁₀ hgf₂₀
  have hsource' :
      eg₁.hom ≫ FY₀'.map leftSource ≫ FY₀'.map (FXg.map d) ≫
          FY₀'.map rightSource ≫ eg₂.inv =
        eg₁.hom ≫ FY₀'.map (D.hom q₀' gf₁₀ gf₂₀ hgf₁₀_fac hgf₂₀_fac) ≫
          eg₂.inv := by
    calc
      eg₁.hom ≫ FY₀'.map leftSource ≫ FY₀'.map (FXg.map d) ≫
          FY₀'.map rightSource ≫ eg₂.inv =
        eg₁.hom ≫
          (FY₀'.map leftSource ≫ FY₀'.map (FXg.map d) ≫ FY₀'.map rightSource) ≫
          eg₂.inv := by
          simp only [Category.assoc]
      _ =
        eg₁.hom ≫
          FY₀'.map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              d g₀ gf₁₀ gf₂₀ hgf₁₀ hgf₂₀) ≫
          eg₂.inv := by
          exact congrArg (fun k => eg₁.hom ≫ k ≫ eg₂.inv) hfold
      _ =
        eg₁.hom ≫ FY₀'.map (D.hom q₀' gf₁₀ gf₂₀ hgf₁₀_fac hgf₂₀_fac) ≫
          eg₂.inv := by
          rw [hsourcePull]
  have hfinal :
      eg₁.hom ≫ FY₀'.map (D.hom q₀' gf₁₀ gf₂₀ hgf₁₀_fac hgf₂₀_fac) ≫
          eg₂.inv =
        sliceDescentToCompositeHom (J := J) (U := U) p T D q' gf₁ gf₂
          hgf₁_fac hgf₂_fac := by
    dsimp [sliceDescentToCompositeHom]
    rfl
  exact
    hunfolded.trans
      (hmap'.trans
        (hleft'.trans
          (hmid'.trans
            (hright'.trans
              (hsource'.trans hfinal)))))

/-- Helper for Chap08 Lemma 8 13 2: componentwise morphisms of slice descent data remain
compatible after viewing the data in the composite projection. -/
private theorem sliceDescentToCompositeHom_comm
    {S : Type*} [Category S] (p : S ⥤ Over U)
    [p.IsFibered] [(p ⋙ Over.forget U).IsFibered]
    {A : Over U} (T : (J.over U).Cover A)
    {D₁ D₂ : (canonicalFiberPseudofunctor p).DescentData (fun I : T.Arrow => I.f)}
    (φ : D₁ ⟶ D₂)
    {Y : C} (q : Y ⟶ A.left) {I₁ I₂ : T.Arrow}
    (f₁ : Y ⟶ I₁.Y.left) (f₂ : Y ⟶ I₂.Y.left)
    (hf₁ : f₁ ≫ I₁.f.left = q) (hf₂ : f₂ ≫ I₂.f.left = q) :
    ((canonicalFiberPseudofunctor (p ⋙ Over.forget U)).map f₁.op.toLoc).toFunctor.map
        ((qFiberToCompositeFiberFunctor (U := U) p I₁.Y).map (φ.hom I₁)) ≫
      sliceDescentToCompositeHom (J := J) (U := U) p T D₂ q f₁ f₂ hf₁ hf₂ =
    sliceDescentToCompositeHom (J := J) (U := U) p T D₁ q f₁ f₂ hf₁ hf₂ ≫
      ((canonicalFiberPseudofunctor (p ⋙ Over.forget U)).map f₂.op.toLoc).toFunctor.map
        ((qFiberToCompositeFiberFunctor (U := U) p I₂.Y).map (φ.hom I₂)) := by
  let Y₀ : Over U := sliceDescentBaseObj (U := U) q
  let q₀ : Y₀ ⟶ A := sliceDescentBaseHom (U := U) q
  let f₁₀ : Y₀ ⟶ I₁.Y := sliceDescentLift (J := J) (U := U) T q f₁ hf₁
  let f₂₀ : Y₀ ⟶ I₂.Y := sliceDescentLift (J := J) (U := U) T q f₂ hf₂
  have hf₁₀ : f₁₀ ≫ I₁.f = q₀ := by
    simpa [f₁₀, q₀] using sliceDescentLift_comp (J := J) (U := U) T q f₁ hf₁
  have hf₂₀ : f₂₀ ≫ I₂.f = q₀ := by
    simpa [f₂₀, q₀] using sliceDescentLift_comp (J := J) (U := U) T q f₂ hf₂
  let Fcomp := canonicalFiberPseudofunctor (p ⋙ Over.forget U)
  let Fq := canonicalFiberPseudofunctor p
  let FY₀ := qFiberToCompositeFiberFunctor (U := U) p Y₀
  let α₁ :=
    ((Fcomp.map f₁.op.toLoc).toFunctor.map
      ((qFiberToCompositeFiberFunctor (U := U) p I₁.Y).map (φ.hom I₁)))
  let α₂ :=
    ((Fcomp.map f₂.op.toLoc).toFunctor.map
      ((qFiberToCompositeFiberFunctor (U := U) p I₂.Y).map (φ.hom I₂)))
  let β₁ := FY₀.map ((Fq.map f₁₀.op.toLoc).toFunctor.map (φ.hom I₁))
  let β₂ := FY₀.map ((Fq.map f₂₀.op.toLoc).toFunctor.map (φ.hom I₂))
  let e₁₁ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₁₀ (D₁.obj I₁)
  let e₁₂ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₁₀ (D₂.obj I₁)
  let e₂₁ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₂₀ (D₁.obj I₂)
  let e₂₂ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₂₀ (D₂.obj I₂)
  let d₁ := D₁.hom q₀ f₁₀ f₂₀ hf₁₀ hf₂₀
  let d₂ := D₂.hom q₀ f₁₀ f₂₀ hf₁₀ hf₂₀
  have hleft :
      α₁ ≫ e₁₂.hom = e₁₁.hom ≫ β₁ := by
    simpa [Fcomp, Fq, FY₀, α₁, β₁, e₁₁, e₁₂, f₁₀] using
      compCanonicalPullback_asCompositeFiberIso_hom_naturality
        (U := U) p f₁₀ (φ.hom I₁)
  have hmid :
      β₁ ≫ FY₀.map d₂ = FY₀.map d₁ ≫ β₂ := by
    calc
      β₁ ≫ FY₀.map d₂ =
          FY₀.map (((Fq.map f₁₀.op.toLoc).toFunctor.map (φ.hom I₁)) ≫ d₂) := by
        dsimp [β₁, d₂]
        rw [← FY₀.map_comp]
      _ =
          FY₀.map (d₁ ≫ ((Fq.map f₂₀.op.toLoc).toFunctor.map (φ.hom I₂))) := by
        exact congrArg FY₀.map (φ.comm q₀ f₁₀ f₂₀ hf₁₀ hf₂₀)
      _ = FY₀.map d₁ ≫ β₂ := by
        dsimp [β₂, d₁]
        rw [FY₀.map_comp]
  have hright :
      β₂ ≫ e₂₂.inv = e₂₁.inv ≫ α₂ := by
    simpa [Fcomp, Fq, FY₀, α₂, β₂, e₂₁, e₂₂, f₂₀] using
      (compCanonicalPullback_asCompositeFiberIso_inv_naturality
        (U := U) p f₂₀ (φ.hom I₂)).symm
  dsimp [sliceDescentToCompositeHom]
  change
    α₁ ≫ (e₁₂.hom ≫ FY₀.map d₂ ≫ e₂₂.inv) =
      (e₁₁.hom ≫ FY₀.map d₁ ≫ e₂₁.inv) ≫ α₂
  have h₀ :
      α₁ ≫ (e₁₂.hom ≫ FY₀.map d₂ ≫ e₂₂.inv) =
        (α₁ ≫ e₁₂.hom) ≫ FY₀.map d₂ ≫ e₂₂.inv := by
      simp only [Category.assoc]
  have h₁ :
      (α₁ ≫ e₁₂.hom) ≫ FY₀.map d₂ ≫ e₂₂.inv =
        (e₁₁.hom ≫ β₁) ≫ FY₀.map d₂ ≫ e₂₂.inv := by
      exact congrArg (fun k => k ≫ FY₀.map d₂ ≫ e₂₂.inv) hleft
  have h₂ :
      (e₁₁.hom ≫ β₁) ≫ FY₀.map d₂ ≫ e₂₂.inv =
        e₁₁.hom ≫ (β₁ ≫ FY₀.map d₂) ≫ e₂₂.inv := by
      simp only [Category.assoc]
  have h₃ :
      e₁₁.hom ≫ (β₁ ≫ FY₀.map d₂) ≫ e₂₂.inv =
        e₁₁.hom ≫ (FY₀.map d₁ ≫ β₂) ≫ e₂₂.inv := by
      exact congrArg (fun k => e₁₁.hom ≫ k ≫ e₂₂.inv) hmid
  have h₄ :
      e₁₁.hom ≫ (FY₀.map d₁ ≫ β₂) ≫ e₂₂.inv =
        (e₁₁.hom ≫ FY₀.map d₁ ≫ e₂₁.inv) ≫ α₂ := by
    simpa only [Category.assoc] using
      congrArg (fun k => e₁₁.hom ≫ FY₀.map d₁ ≫ k) hright
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans h₄)))

/-- Helper for Chap08 Lemma 8 13 2: a slice descent datum has a fixed-arrow composite
descent datum after forgetting the slice coordinate. -/
private noncomputable def sliceDescentToCompositeFixedDescentFunctor
    {S : Type*} [Category S] (p : S ⥤ Over U)
    [p.IsFibered] [(p ⋙ Over.forget U).IsFibered]
    {A : Over U} (T : (J.over U).Cover A) :
    (canonicalFiberPseudofunctor p).DescentData (fun I : T.Arrow => I.f) ⥤
      (compositeDescentFixedArrowProperty (J := J) (U := U) (p := p) T).FullSubcategory where
  obj D :=
    ⟨
      { obj := fun I => qFiberAsCompositeFiberObj (U := U) p (D.obj I)
        hom := fun {Y} q {I₁ I₂} f₁ f₂ hf₁ hf₂ =>
          sliceDescentToCompositeHom (J := J) (U := U) p T D q f₁ f₂ hf₁ hf₂
        pullHom_hom := by
          intro Y' Y g q q' hq I₁ I₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
          exact
            sliceDescentToCompositeHom_pullHom_hom
              (J := J) (U := U) p T D g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
        hom_self := by
          intro Y q I g hg
          exact sliceDescentToCompositeHom_self (J := J) (U := U) p T D q g hg
        hom_comp := by
          intro Y q I₁ I₂ I₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
          exact
            sliceDescentToCompositeHom_comp
              (J := J) (U := U) p T D q f₁ f₂ f₃ hf₁ hf₂ hf₃ },
      by
        intro I
        exact qDescentData_obj_compositeFiberArrowToU (J := J) (U := U) p T D I⟩
  map {D₁ D₂} φ :=
    ObjectProperty.homMk
      { hom := fun I => (qFiberToCompositeFiberFunctor (U := U) p I.Y).map (φ.hom I)
        comm := by
          intro Y q I₁ I₂ f₁ f₂ hf₁ hf₂
          exact sliceDescentToCompositeHom_comm
            (J := J) (U := U) p T φ q f₁ f₂ hf₁ hf₂ }
  map_id D := by
    apply ObjectProperty.hom_ext
    apply Pseudofunctor.DescentData.hom_ext
    intro I
    exact (qFiberToCompositeFiberFunctor (U := U) p I.Y).map_id (D.obj I)
  map_comp {D₁ D₂ D₃} φ ψ := by
    apply ObjectProperty.hom_ext
    apply Pseudofunctor.DescentData.hom_ext
    intro I
    exact (qFiberToCompositeFiberFunctor (U := U) p I.Y).map_comp (φ.hom I) (ψ.hom I)

/-- Helper for Chap08 Lemma 8 13 2: the descent-data comparison from slice data to fixed
composite data is faithful. -/
private theorem sliceDescentToCompositeFixedDescentFunctor_faithful
    {S : Type*} [Category S] (p : S ⥤ Over U)
    [p.IsFibered] [(p ⋙ Over.forget U).IsFibered]
    {A : Over U} (T : (J.over U).Cover A) :
    (sliceDescentToCompositeFixedDescentFunctor (J := J) (U := U) p T).Faithful := by
  let Cfun := sliceDescentToCompositeFixedDescentFunctor (J := J) (U := U) p T
  constructor
  intro D₁ D₂ φ ψ hφψ
  apply Pseudofunctor.DescentData.hom_ext
  intro I
  let FI := qFiberToCompositeFiberFunctor (U := U) p I.Y
  haveI : FI.Faithful := qFiberToCompositeFiberFunctor_faithful (U := U) p I.Y
  apply FI.map_injective
  have hI : (Cfun.map φ).hom.hom I = (Cfun.map ψ).hom.hom I := by
    exact congrArg (fun k => k.hom.hom I) hφψ
  simpa [Cfun, sliceDescentToCompositeFixedDescentFunctor, FI] using hI

/-- Helper for Chap08 Lemma 8 13 2: the descent-data comparison from slice data to fixed
composite data is full. -/
private theorem sliceDescentToCompositeFixedDescentFunctor_full
    {S : Type*} [Category S] (p : S ⥤ Over U)
    [p.IsFibered] [(p ⋙ Over.forget U).IsFibered]
    {A : Over U} (T : (J.over U).Cover A) :
    (sliceDescentToCompositeFixedDescentFunctor (J := J) (U := U) p T).Full := by
  let Cfun := sliceDescentToCompositeFixedDescentFunctor (J := J) (U := U) p T
  constructor
  intro D₁ D₂ θ
  let preHom : ∀ I : T.Arrow, D₁.obj I ⟶ D₂.obj I := fun I => by
    let FI := qFiberToCompositeFiberFunctor (U := U) p I.Y
    haveI : FI.Full := qFiberToCompositeFiberFunctor_full (U := U) p I.Y
    exact FI.preimage (θ.hom.hom I)
  let φ : D₁ ⟶ D₂ :=
    { hom := preHom
      comm := by
        intro Y q I₁ I₂ f₁ f₂ hf₁ hf₂
        generalize hYb : Y.left = Yb
        generalize hqb : eqToHom hYb.symm ≫ q.left = qb
        have hY : Y = sliceDescentBaseObj (U := U) (A := A) qb := by
          refine CostructuredArrow.obj_ext Y (sliceDescentBaseObj (U := U) (A := A) qb) hYb ?_
          dsimp [sliceDescentBaseObj]
          rw [← hqb]
          calc
            eqToHom hYb ≫ ((eqToHom hYb.symm ≫ q.left) ≫ A.hom) =
                (eqToHom hYb ≫ eqToHom hYb.symm) ≫ q.left ≫ A.hom := by
              simp only [Category.assoc]
            _ = q.left ≫ A.hom := by
              rw [eqToHom_trans]
              simp
            _ = Y.hom := Over.w q
        cases hY
        have hq : q = sliceDescentBaseHom (U := U) (A := A) qb := by
          ext
          simpa using hqb
        cases hq
        let f₁b : (sliceDescentBaseObj (U := U) qb).left ⟶ I₁.Y.left := f₁.left
        have hf₁b : f₁b ≫ I₁.f.left = qb := by
          dsimp [f₁b]
          exact congrArg (fun k => k.left) hf₁
        have hf₁eq : f₁ = sliceDescentLift (J := J) (U := U) T qb f₁b hf₁b := by
          ext
          rfl
        cases hf₁eq
        let f₂b : (sliceDescentBaseObj (U := U) qb).left ⟶ I₂.Y.left := f₂.left
        have hf₂b : f₂b ≫ I₂.f.left = qb := by
          dsimp [f₂b]
          exact congrArg (fun k => k.left) hf₂
        have hf₂eq : f₂ = sliceDescentLift (J := J) (U := U) T qb f₂b hf₂b := by
          ext
          rfl
        cases hf₂eq
        let Fq := canonicalFiberPseudofunctor p
        let Fcomp := canonicalFiberPseudofunctor (p ⋙ Over.forget U)
        let Y₀ : Over U := sliceDescentBaseObj (U := U) qb
        let q₀ : Y₀ ⟶ A := sliceDescentBaseHom (U := U) qb
        let f₁₀ : Y₀ ⟶ I₁.Y := sliceDescentLift (J := J) (U := U) T qb f₁b hf₁b
        let f₂₀ : Y₀ ⟶ I₂.Y := sliceDescentLift (J := J) (U := U) T qb f₂b hf₂b
        have hf₁₀ : f₁₀ ≫ I₁.f = q₀ := by
          simpa [f₁₀, q₀] using sliceDescentLift_comp (J := J) (U := U) T qb f₁b hf₁b
        have hf₂₀ : f₂₀ ≫ I₂.f = q₀ := by
          simpa [f₂₀, q₀] using sliceDescentLift_comp (J := J) (U := U) T qb f₂b hf₂b
        let FY := qFiberToCompositeFiberFunctor (U := U) p Y₀
        haveI : FY.Faithful := qFiberToCompositeFiberFunctor_faithful (U := U) p Y₀
        let ψ₁ : D₁.obj I₁ ⟶ D₂.obj I₁ := preHom I₁
        let ψ₂ : D₁.obj I₂ ⟶ D₂.obj I₂ := preHom I₂
        let d₁ := D₁.hom q₀ f₁₀ f₂₀ hf₁₀ hf₂₀
        let d₂ := D₂.hom q₀ f₁₀ f₂₀ hf₁₀ hf₂₀
        let e₁₁ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₁₀ (D₁.obj I₁)
        let e₁₂ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₁₀ (D₂.obj I₁)
        let e₂₁ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₂₀ (D₁.obj I₂)
        let e₂₂ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₂₀ (D₂.obj I₂)
        let α₁ := ((Fcomp.map f₁b.op.toLoc).toFunctor.map (θ.hom.hom I₁))
        let α₂ := ((Fcomp.map f₂b.op.toLoc).toFunctor.map (θ.hom.hom I₂))
        let β₁ := FY.map ((Fq.map f₁₀.op.toLoc).toFunctor.map ψ₁)
        let β₂ := FY.map ((Fq.map f₂₀.op.toLoc).toFunctor.map ψ₂)
        have hpre₁ :
            (qFiberToCompositeFiberFunctor (U := U) p I₁.Y).map ψ₁ = θ.hom.hom I₁ := by
          dsimp [ψ₁, preHom]
          let FI := qFiberToCompositeFiberFunctor (U := U) p I₁.Y
          haveI : FI.Full := qFiberToCompositeFiberFunctor_full (U := U) p I₁.Y
          simpa [FI] using FI.map_preimage (θ.hom.hom I₁)
        have hpre₂ :
            (qFiberToCompositeFiberFunctor (U := U) p I₂.Y).map ψ₂ = θ.hom.hom I₂ := by
          dsimp [ψ₂, preHom]
          let FI := qFiberToCompositeFiberFunctor (U := U) p I₂.Y
          haveI : FI.Full := qFiberToCompositeFiberFunctor_full (U := U) p I₂.Y
          simpa [FI] using FI.map_preimage (θ.hom.hom I₂)
        have hleft :
            α₁ ≫ e₁₂.hom = e₁₁.hom ≫ β₁ := by
          have hnat :=
            compCanonicalPullback_asCompositeFiberIso_hom_naturality
              (U := U) p f₁₀ ψ₁
          rw [hpre₁] at hnat
          simpa [Fq, Fcomp, FY, f₁₀, e₁₁, e₁₂, α₁, β₁] using hnat
        have hright :
            e₂₁.inv ≫ α₂ = β₂ ≫ e₂₂.inv := by
          have hnat :=
            compCanonicalPullback_asCompositeFiberIso_inv_naturality
              (U := U) p f₂₀ ψ₂
          rw [hpre₂] at hnat
          simpa [Fq, Fcomp, FY, f₂₀, e₂₁, e₂₂, α₂, β₂] using hnat
        have hH₁ :
            e₁₁.hom ≫ FY.map d₁ ≫ e₂₁.inv =
              sliceDescentToCompositeHom (J := J) (U := U) p T D₁ qb f₁b f₂b hf₁b hf₂b := by
          dsimp [sliceDescentToCompositeHom]
          rfl
        have hH₂ :
            e₁₂.hom ≫ FY.map d₂ ≫ e₂₂.inv =
              sliceDescentToCompositeHom (J := J) (U := U) p T D₂ qb f₁b f₂b hf₁b hf₂b := by
          dsimp [sliceDescentToCompositeHom]
          rfl
        have hθ :
            α₁ ≫ (e₁₂.hom ≫ FY.map d₂ ≫ e₂₂.inv) =
              (e₁₁.hom ≫ FY.map d₁ ≫ e₂₁.inv) ≫ α₂ := by
          have hθbase :
              α₁ ≫
                  sliceDescentToCompositeHom
                    (J := J) (U := U) p T D₂ qb f₁b f₂b hf₁b hf₂b =
                sliceDescentToCompositeHom
                    (J := J) (U := U) p T D₁ qb f₁b f₂b hf₁b hf₂b ≫
                  α₂ := by
            simpa [Cfun, sliceDescentToCompositeFixedDescentFunctor, Fcomp, α₁, α₂] using
              θ.hom.comm qb f₁b f₂b hf₁b hf₂b
          have hleftθ :
              α₁ ≫ e₁₂.hom ≫ FY.map d₂ ≫ e₂₂.inv =
                α₁ ≫
                  sliceDescentToCompositeHom
                    (J := J) (U := U) p T D₂ qb f₁b f₂b hf₁b hf₂b := by
            simpa only [Category.assoc] using
              congrArg (fun k => α₁ ≫ k) hH₂
          have hrightθ :
              sliceDescentToCompositeHom
                    (J := J) (U := U) p T D₁ qb f₁b f₂b hf₁b hf₂b ≫
                  α₂ =
                (e₁₁.hom ≫ FY.map d₁ ≫ e₂₁.inv) ≫ α₂ := by
            exact congrArg (fun k => k ≫ α₂) hH₁.symm
          exact hleftθ.trans (hθbase.trans hrightθ)
        have hmain : β₁ ≫ FY.map d₂ = FY.map d₁ ≫ β₂ := by
          have hleftCancel :
              (e₁₁.hom ≫ β₁) ≫ FY.map d₂ ≫ e₂₂.inv =
                (α₁ ≫ e₁₂.hom) ≫ FY.map d₂ ≫ e₂₂.inv :=
            congrArg (fun k => k ≫ FY.map d₂ ≫ e₂₂.inv) hleft.symm
          have hrightCancel :
              e₁₁.hom ≫ FY.map d₁ ≫ e₂₁.inv ≫ α₂ =
                e₁₁.hom ≫ FY.map d₁ ≫ (β₂ ≫ e₂₂.inv) :=
            congrArg (fun k => e₁₁.hom ≫ FY.map d₁ ≫ k) hright
          have hθassoc :
              (α₁ ≫ e₁₂.hom) ≫ FY.map d₂ ≫ e₂₂.inv =
                e₁₁.hom ≫ FY.map d₁ ≫ e₂₁.inv ≫ α₂ := by
            simpa only [Category.assoc] using hθ
          have hcancelledAssoc :
              (e₁₁.hom ≫ β₁) ≫ FY.map d₂ ≫ e₂₂.inv =
                e₁₁.hom ≫ FY.map d₁ ≫ (β₂ ≫ e₂₂.inv) :=
            hleftCancel.trans (hθassoc.trans hrightCancel)
          have hcancelled :
              (e₁₁.hom ≫ (β₁ ≫ FY.map d₂)) ≫ e₂₂.inv =
                (e₁₁.hom ≫ (FY.map d₁ ≫ β₂)) ≫ e₂₂.inv := by
            simpa only [Category.assoc] using hcancelledAssoc
          have hafterMono :
              e₁₁.hom ≫ (β₁ ≫ FY.map d₂) =
                e₁₁.hom ≫ (FY.map d₁ ≫ β₂) :=
            (cancel_mono e₂₂.inv).1 hcancelled
          exact (cancel_epi e₁₁.hom).1 hafterMono
        change
          ((Fq.map f₁₀.op.toLoc).toFunctor.map ψ₁) ≫ d₂ =
            d₁ ≫ ((Fq.map f₂₀.op.toLoc).toFunctor.map ψ₂)
        apply FY.map_injective
        have hleftMap :
            FY.map (((Fq.map f₁₀.op.toLoc).toFunctor.map ψ₁) ≫ d₂) =
              β₁ ≫ FY.map d₂ := by
          dsimp [β₁]
          exact FY.map_comp ((Fq.map f₁₀.op.toLoc).toFunctor.map ψ₁) d₂
        have hrightMap :
            FY.map (d₁ ≫ ((Fq.map f₂₀.op.toLoc).toFunctor.map ψ₂)) =
              FY.map d₁ ≫ β₂ := by
          dsimp [β₂]
          exact FY.map_comp d₁ ((Fq.map f₂₀.op.toLoc).toFunctor.map ψ₂)
        exact hleftMap.trans (hmain.trans hrightMap.symm) }
  refine ⟨φ, ?_⟩
  apply ObjectProperty.hom_ext
  apply Pseudofunctor.DescentData.hom_ext
  intro I
  let FI := qFiberToCompositeFiberFunctor (U := U) p I.Y
  haveI : FI.Full := qFiberToCompositeFiberFunctor_full (U := U) p I.Y
  simpa [Cfun, sliceDescentToCompositeFixedDescentFunctor, φ, preHom, FI] using
    FI.map_preimage (θ.hom.hom I)

/-- Helper for Chap08 Lemma 8 13 2: the inverse overlap morphism from a fixed-arrow composite
descent datum to the corresponding slice descent datum. -/
private noncomputable def compositeFixedDescentToSliceHom
    {S : Type*} [Category S] (p : S ⥤ Over U)
    [p.IsFibered] [(p ⋙ Over.forget U).IsFibered]
    {A : Over U} (T : (J.over U).Cover A)
    (D : (compositeDescentFixedArrowProperty (J := J) (U := U) (p := p) T).FullSubcategory)
    {Y : Over U} (q : Y ⟶ A) {I₁ I₂ : T.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q) :
    (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.obj
      (compositeFixedLocalObjToQFiberObj (U := U) p I₁.f (D.obj.obj I₁)
        (D.property I₁))) ⟶
    (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.obj
      (compositeFixedLocalObjToQFiberObj (U := U) p I₂.f (D.obj.obj I₂)
        (D.property I₂))) := by
  let X₁ :=
    compositeFixedLocalObjToQFiberObj (U := U) p I₁.f (D.obj.obj I₁) (D.property I₁)
  let X₂ :=
    compositeFixedLocalObjToQFiberObj (U := U) p I₂.f (D.obj.obj I₂) (D.property I₂)
  let Fcomp := canonicalFiberPseudofunctor (p ⋙ Over.forget U)
  let Fq := canonicalFiberPseudofunctor p
  let FY := qFiberToCompositeFiberFunctor (U := U) p Y
  haveI : FY.Full := qFiberToCompositeFiberFunctor_full (U := U) p Y
  let e₁ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₁ X₁
  let e₂ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₂ X₂
  have hX₁ :
      qFiberAsCompositeFiberObj (U := U) p X₁ = D.obj.obj I₁ := by
    exact compositeFixedLocalObjToQFiberObj_forget (U := U) p I₁.f (D.obj.obj I₁)
      (D.property I₁)
  have hX₂ :
      qFiberAsCompositeFiberObj (U := U) p X₂ = D.obj.obj I₂ := by
    exact compositeFixedLocalObjToQFiberObj_forget (U := U) p I₂.f (D.obj.obj I₂)
      (D.property I₂)
  have hf₁left : f₁.left ≫ I₁.f.left = q.left := by
    exact congrArg (fun k => k.left) hf₁
  have hf₂left : f₂.left ≫ I₂.f.left = q.left := by
    exact congrArg (fun k => k.left) hf₂
  let dComp :
      ((Fcomp.map f₁.left.op.toLoc).toFunctor.obj
          (qFiberAsCompositeFiberObj (U := U) p X₁)) ⟶
        ((Fcomp.map f₂.left.op.toLoc).toFunctor.obj
          (qFiberAsCompositeFiberObj (U := U) p X₂)) := by
    simpa [Fcomp, hX₁, hX₂] using
      (D.obj.hom q.left f₁.left f₂.left hf₁left hf₂left)
  exact FY.preimage (e₁.inv ≫ dComp ≫ e₂.hom)

/-- Helper for Chap08 Lemma 8 13 2: after forgetting to the composite fiber, the inverse overlap
morphism is the conjugated composite overlap morphism by definition. -/
private theorem compositeFixedDescentToSliceHom_forget
    {S : Type*} [Category S] (p : S ⥤ Over U)
    [p.IsFibered] [(p ⋙ Over.forget U).IsFibered]
    {A : Over U} (T : (J.over U).Cover A)
    (D : (compositeDescentFixedArrowProperty (J := J) (U := U) (p := p) T).FullSubcategory)
    {Y : Over U} (q : Y ⟶ A) {I₁ I₂ : T.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q) :
    let X₁ :=
      compositeFixedLocalObjToQFiberObj (U := U) p I₁.f (D.obj.obj I₁) (D.property I₁)
    let X₂ :=
      compositeFixedLocalObjToQFiberObj (U := U) p I₂.f (D.obj.obj I₂) (D.property I₂)
    let Fcomp := canonicalFiberPseudofunctor (p ⋙ Over.forget U)
    let FY := qFiberToCompositeFiberFunctor (U := U) p Y
    let e₁ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₁ X₁
    let e₂ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₂ X₂
    let dComp :
        ((Fcomp.map f₁.left.op.toLoc).toFunctor.obj
            (qFiberAsCompositeFiberObj (U := U) p X₁)) ⟶
          ((Fcomp.map f₂.left.op.toLoc).toFunctor.obj
            (qFiberAsCompositeFiberObj (U := U) p X₂)) := by
      have hX₁ :
          qFiberAsCompositeFiberObj (U := U) p X₁ = D.obj.obj I₁ := by
        exact compositeFixedLocalObjToQFiberObj_forget (U := U) p I₁.f (D.obj.obj I₁)
          (D.property I₁)
      have hX₂ :
          qFiberAsCompositeFiberObj (U := U) p X₂ = D.obj.obj I₂ := by
        exact compositeFixedLocalObjToQFiberObj_forget (U := U) p I₂.f (D.obj.obj I₂)
          (D.property I₂)
      have hf₁left : f₁.left ≫ I₁.f.left = q.left := congrArg (fun k => k.left) hf₁
      have hf₂left : f₂.left ≫ I₂.f.left = q.left := congrArg (fun k => k.left) hf₂
      simpa [Fcomp, hX₁, hX₂] using
        (D.obj.hom q.left f₁.left f₂.left hf₁left hf₂left)
    FY.map (compositeFixedDescentToSliceHom (J := J) (U := U) p T D q f₁ f₂ hf₁ hf₂) =
      e₁.inv ≫ dComp ≫ e₂.hom := by
  intro X₁ X₂ Fcomp FY e₁ e₂ dComp
  haveI : FY.Full := qFiberToCompositeFiberFunctor_full (U := U) p Y
  exact FY.map_preimage (e₁.inv ≫ dComp ≫ e₂.hom)

/-- Helper for Chap08 Lemma 8 13 2: the inverse comparison overlap is the identity on a
self-overlap. -/
private theorem compositeFixedDescentToSliceHom_self
    {S : Type*} [Category S] (p : S ⥤ Over U)
    [p.IsFibered] [(p ⋙ Over.forget U).IsFibered]
    {A : Over U} (T : (J.over U).Cover A)
    (D : (compositeDescentFixedArrowProperty (J := J) (U := U) (p := p) T).FullSubcategory)
    {Y : Over U} (q : Y ⟶ A) {I : T.Arrow}
    (f : Y ⟶ I.Y) (hf : f ≫ I.f = q) :
    compositeFixedDescentToSliceHom (J := J) (U := U) p T D q f f hf hf = 𝟙 _ := by
  let X :=
    compositeFixedLocalObjToQFiberObj (U := U) p I.f (D.obj.obj I) (D.property I)
  let Fcomp := canonicalFiberPseudofunctor (p ⋙ Over.forget U)
  let FY := qFiberToCompositeFiberFunctor (U := U) p Y
  haveI : FY.Faithful := qFiberToCompositeFiberFunctor_faithful (U := U) p Y
  let e := compCanonicalPullback_asCompositeFiberIso (U := U) p f X
  have hX :
      qFiberAsCompositeFiberObj (U := U) p X = D.obj.obj I := by
    exact compositeFixedLocalObjToQFiberObj_forget (U := U) p I.f (D.obj.obj I)
      (D.property I)
  have hfleft : f.left ≫ I.f.left = q.left := by
    exact congrArg (fun k => k.left) hf
  cases hX
  let dComp :
      ((Fcomp.map f.left.op.toLoc).toFunctor.obj
          (qFiberAsCompositeFiberObj (U := U) p X)) ⟶
        ((Fcomp.map f.left.op.toLoc).toFunctor.obj
          (qFiberAsCompositeFiberObj (U := U) p X)) := by
    exact D.obj.hom q.left f.left f.left hfleft hfleft
  have hforget :
      FY.map (compositeFixedDescentToSliceHom (J := J) (U := U) p T D q f f hf hf) =
        e.inv ≫ dComp ≫ e.hom := by
    simpa [X, Fcomp, FY, e, dComp] using
      compositeFixedDescentToSliceHom_forget (J := J) (U := U) p T D q f f hf hf
  have hd : dComp = 𝟙 _ := by
    dsimp [dComp]
    exact D.obj.hom_self q.left f.left hfleft
  apply FY.map_injective
  have hmain :
      FY.map (compositeFixedDescentToSliceHom (J := J) (U := U) p T D q f f hf hf) =
        𝟙 (qFiberAsCompositeFiberObj (U := U) p
          (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj X)) := by
    calc
      FY.map (compositeFixedDescentToSliceHom (J := J) (U := U) p T D q f f hf hf) =
          e.inv ≫ dComp ≫ e.hom := hforget
      _ = e.inv ≫ 𝟙 _ ≫ e.hom := by
          exact congrArg (fun k => e.inv ≫ k ≫ e.hom) hd
      _ = 𝟙 _ := by
          rw [Category.id_comp, e.inv_hom_id]
  exact hmain.trans (FY.map_id _).symm

/-- Helper for Chap08 Lemma 8 13 2: the inverse comparison overlaps satisfy the descent
cocycle law. -/
private theorem compositeFixedDescentToSliceHom_comp
    {S : Type*} [Category S] (p : S ⥤ Over U)
    [p.IsFibered] [(p ⋙ Over.forget U).IsFibered]
    {A : Over U} (T : (J.over U).Cover A)
    (D : (compositeDescentFixedArrowProperty (J := J) (U := U) (p := p) T).FullSubcategory)
    {Y : Over U} (q : Y ⟶ A) {I₁ I₂ I₃ : T.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q) (hf₃ : f₃ ≫ I₃.f = q) :
    compositeFixedDescentToSliceHom (J := J) (U := U) p T D q f₁ f₂ hf₁ hf₂ ≫
      compositeFixedDescentToSliceHom (J := J) (U := U) p T D q f₂ f₃ hf₂ hf₃ =
    compositeFixedDescentToSliceHom (J := J) (U := U) p T D q f₁ f₃ hf₁ hf₃ := by
  let X₁ :=
    compositeFixedLocalObjToQFiberObj (U := U) p I₁.f (D.obj.obj I₁) (D.property I₁)
  let X₂ :=
    compositeFixedLocalObjToQFiberObj (U := U) p I₂.f (D.obj.obj I₂) (D.property I₂)
  let X₃ :=
    compositeFixedLocalObjToQFiberObj (U := U) p I₃.f (D.obj.obj I₃) (D.property I₃)
  let Fcomp := canonicalFiberPseudofunctor (p ⋙ Over.forget U)
  let FY := qFiberToCompositeFiberFunctor (U := U) p Y
  haveI : FY.Faithful := qFiberToCompositeFiberFunctor_faithful (U := U) p Y
  let e₁ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₁ X₁
  let e₂ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₂ X₂
  let e₃ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₃ X₃
  have hX₁ :
      qFiberAsCompositeFiberObj (U := U) p X₁ = D.obj.obj I₁ := by
    exact compositeFixedLocalObjToQFiberObj_forget (U := U) p I₁.f (D.obj.obj I₁)
      (D.property I₁)
  have hX₂ :
      qFiberAsCompositeFiberObj (U := U) p X₂ = D.obj.obj I₂ := by
    exact compositeFixedLocalObjToQFiberObj_forget (U := U) p I₂.f (D.obj.obj I₂)
      (D.property I₂)
  have hX₃ :
      qFiberAsCompositeFiberObj (U := U) p X₃ = D.obj.obj I₃ := by
    exact compositeFixedLocalObjToQFiberObj_forget (U := U) p I₃.f (D.obj.obj I₃)
      (D.property I₃)
  cases hX₁
  cases hX₂
  cases hX₃
  have hf₁left : f₁.left ≫ I₁.f.left = q.left := congrArg (fun k => k.left) hf₁
  have hf₂left : f₂.left ≫ I₂.f.left = q.left := congrArg (fun k => k.left) hf₂
  have hf₃left : f₃.left ≫ I₃.f.left = q.left := congrArg (fun k => k.left) hf₃
  let d₁₂ :
      ((Fcomp.map f₁.left.op.toLoc).toFunctor.obj
          (qFiberAsCompositeFiberObj (U := U) p X₁)) ⟶
        ((Fcomp.map f₂.left.op.toLoc).toFunctor.obj
          (qFiberAsCompositeFiberObj (U := U) p X₂)) := by
    exact D.obj.hom q.left f₁.left f₂.left hf₁left hf₂left
  let d₂₃ :
      ((Fcomp.map f₂.left.op.toLoc).toFunctor.obj
          (qFiberAsCompositeFiberObj (U := U) p X₂)) ⟶
        ((Fcomp.map f₃.left.op.toLoc).toFunctor.obj
          (qFiberAsCompositeFiberObj (U := U) p X₃)) := by
    exact D.obj.hom q.left f₂.left f₃.left hf₂left hf₃left
  let d₁₃ :
      ((Fcomp.map f₁.left.op.toLoc).toFunctor.obj
          (qFiberAsCompositeFiberObj (U := U) p X₁)) ⟶
        ((Fcomp.map f₃.left.op.toLoc).toFunctor.obj
          (qFiberAsCompositeFiberObj (U := U) p X₃)) := by
    exact D.obj.hom q.left f₁.left f₃.left hf₁left hf₃left
  have h₁₂ :
      FY.map (compositeFixedDescentToSliceHom (J := J) (U := U) p T D q f₁ f₂
          hf₁ hf₂) =
        e₁.inv ≫ d₁₂ ≫ e₂.hom := by
    simpa [X₁, X₂, Fcomp, FY, e₁, e₂, d₁₂] using
      compositeFixedDescentToSliceHom_forget (J := J) (U := U) p T D q f₁ f₂ hf₁ hf₂
  have h₂₃ :
      FY.map (compositeFixedDescentToSliceHom (J := J) (U := U) p T D q f₂ f₃
          hf₂ hf₃) =
        e₂.inv ≫ d₂₃ ≫ e₃.hom := by
    simpa [X₂, X₃, Fcomp, FY, e₂, e₃, d₂₃] using
      compositeFixedDescentToSliceHom_forget (J := J) (U := U) p T D q f₂ f₃ hf₂ hf₃
  have h₁₃ :
      FY.map (compositeFixedDescentToSliceHom (J := J) (U := U) p T D q f₁ f₃
          hf₁ hf₃) =
        e₁.inv ≫ d₁₃ ≫ e₃.hom := by
    simpa [X₁, X₃, Fcomp, FY, e₁, e₃, d₁₃] using
      compositeFixedDescentToSliceHom_forget (J := J) (U := U) p T D q f₁ f₃ hf₁ hf₃
  have hd : d₁₂ ≫ d₂₃ = d₁₃ := by
    dsimp [d₁₂, d₂₃, d₁₃]
    exact D.obj.hom_comp q.left f₁.left f₂.left f₃.left hf₁left hf₂left hf₃left
  apply FY.map_injective
  have hcancel :
      (e₁.inv ≫ d₁₂ ≫ e₂.hom) ≫ (e₂.inv ≫ d₂₃ ≫ e₃.hom) =
        e₁.inv ≫ d₁₃ ≫ e₃.hom := by
    calc
      (e₁.inv ≫ d₁₂ ≫ e₂.hom) ≫ (e₂.inv ≫ d₂₃ ≫ e₃.hom) =
          e₁.inv ≫ d₁₂ ≫ (e₂.hom ≫ e₂.inv) ≫ d₂₃ ≫ e₃.hom := by
        simp only [Category.assoc]
      _ = e₁.inv ≫ d₁₂ ≫ 𝟙 _ ≫ d₂₃ ≫ e₃.hom := by
        exact congrArg (fun k => e₁.inv ≫ d₁₂ ≫ k ≫ d₂₃ ≫ e₃.hom) e₂.hom_inv_id
      _ = e₁.inv ≫ (d₁₂ ≫ d₂₃) ≫ e₃.hom := by
        simp only [Category.id_comp, Category.assoc]
      _ = e₁.inv ≫ d₁₃ ≫ e₃.hom := by
        exact congrArg (fun k => e₁.inv ≫ k ≫ e₃.hom) hd
  have hmain :
      FY.map
          (compositeFixedDescentToSliceHom (J := J) (U := U) p T D q f₁ f₂ hf₁ hf₂ ≫
            compositeFixedDescentToSliceHom (J := J) (U := U) p T D q f₂ f₃ hf₂ hf₃) =
        e₁.inv ≫ d₁₃ ≫ e₃.hom := by
    calc
      FY.map
          (compositeFixedDescentToSliceHom (J := J) (U := U) p T D q f₁ f₂ hf₁ hf₂ ≫
            compositeFixedDescentToSliceHom (J := J) (U := U) p T D q f₂ f₃ hf₂ hf₃) =
          FY.map (compositeFixedDescentToSliceHom (J := J) (U := U) p T D q f₁ f₂ hf₁ hf₂) ≫
            FY.map (compositeFixedDescentToSliceHom (J := J) (U := U) p T D q f₂ f₃ hf₂ hf₃) := by
          rw [FY.map_comp]
      _ = (e₁.inv ≫ d₁₂ ≫ e₂.hom) ≫ (e₂.inv ≫ d₂₃ ≫ e₃.hom) := by
          exact congrArg₂ (fun a b => a ≫ b) h₁₂ h₂₃
      _ = e₁.inv ≫ d₁₃ ≫ e₃.hom := hcancel
  exact hmain.trans h₁₃.symm

/-- Helper for Chap08 Lemma 8 13 2: the inverse comparison overlap is compatible with
pullback. -/
private theorem compositeFixedDescentToSliceHom_pullHom_hom
    {S : Type*} [Category S] (p : S ⥤ Over U)
    [p.IsFibered] [(p ⋙ Over.forget U).IsFibered]
    {A : Over U} (T : (J.over U).Cover A)
    (D : (compositeDescentFixedArrowProperty (J := J) (U := U) (p := p) T).FullSubcategory)
    {Y' Y : Over U} (g : Y' ⟶ Y) (q : Y ⟶ A) (q' : Y' ⟶ A)
    (hq : g ≫ q = q')
    {I₁ I₂ : T.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (compositeFixedDescentToSliceHom (J := J) (U := U) p T D q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      compositeFixedDescentToSliceHom (J := J) (U := U) p T D q' gf₁ gf₂
        (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
        (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) := by
  let X₁ :=
    compositeFixedLocalObjToQFiberObj (U := U) p I₁.f (D.obj.obj I₁) (D.property I₁)
  let X₂ :=
    compositeFixedLocalObjToQFiberObj (U := U) p I₂.f (D.obj.obj I₂) (D.property I₂)
  let Fcomp := canonicalFiberPseudofunctor (p ⋙ Over.forget U)
  let Fq := canonicalFiberPseudofunctor p
  let FY := qFiberToCompositeFiberFunctor (U := U) p Y
  let FY' := qFiberToCompositeFiberFunctor (U := U) p Y'
  haveI : FY'.Faithful := qFiberToCompositeFiberFunctor_faithful (U := U) p Y'
  let FYg := (Fcomp.map g.left.op.toLoc).toFunctor
  let FXg := (Fq.map g.op.toLoc).toFunctor
  let e₁ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₁ X₁
  let e₂ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₂ X₂
  let eg₁ := compCanonicalPullback_asCompositeFiberIso (U := U) p gf₁ X₁
  let eg₂ := compCanonicalPullback_asCompositeFiberIso (U := U) p gf₂ X₂
  let cg₁ := compCanonicalPullback_asCompositeFiberIso (U := U) p g
    (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.obj X₁)
  let cg₂ := compCanonicalPullback_asCompositeFiberIso (U := U) p g
    (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.obj X₂)
  have hX₁ :
      qFiberAsCompositeFiberObj (U := U) p X₁ = D.obj.obj I₁ := by
    exact compositeFixedLocalObjToQFiberObj_forget (U := U) p I₁.f (D.obj.obj I₁)
      (D.property I₁)
  have hX₂ :
      qFiberAsCompositeFiberObj (U := U) p X₂ = D.obj.obj I₂ := by
    exact compositeFixedLocalObjToQFiberObj_forget (U := U) p I₂.f (D.obj.obj I₂)
      (D.property I₂)
  cases hX₁
  cases hX₂
  have hqleft : g.left ≫ q.left = q'.left := congrArg (fun k => k.left) hq
  have hf₁left : f₁.left ≫ I₁.f.left = q.left := congrArg (fun k => k.left) hf₁
  have hf₂left : f₂.left ≫ I₂.f.left = q.left := congrArg (fun k => k.left) hf₂
  have hgf₁left : g.left ≫ f₁.left = gf₁.left := congrArg (fun k => k.left) hgf₁
  have hgf₂left : g.left ≫ f₂.left = gf₂.left := congrArg (fun k => k.left) hgf₂
  have hgf₁fac : gf₁.left ≫ I₁.f.left = q'.left := by
    rw [← hqleft, ← hgf₁left, Category.assoc, hf₁left]
  have hgf₂fac : gf₂.left ≫ I₂.f.left = q'.left := by
    rw [← hqleft, ← hgf₂left, Category.assoc, hf₂left]
  let d :
      ((Fcomp.map f₁.left.op.toLoc).toFunctor.obj
          (qFiberAsCompositeFiberObj (U := U) p X₁)) ⟶
        ((Fcomp.map f₂.left.op.toLoc).toFunctor.obj
          (qFiberAsCompositeFiberObj (U := U) p X₂)) :=
    D.obj.hom q.left f₁.left f₂.left hf₁left hf₂left
  let d' :
      ((Fcomp.map gf₁.left.op.toLoc).toFunctor.obj
          (qFiberAsCompositeFiberObj (U := U) p X₁)) ⟶
        ((Fcomp.map gf₂.left.op.toLoc).toFunctor.obj
          (qFiberAsCompositeFiberObj (U := U) p X₂)) :=
    D.obj.hom q'.left gf₁.left gf₂.left hgf₁fac hgf₂fac
  let φ :=
    compositeFixedDescentToSliceHom (J := J) (U := U) p T D q f₁ f₂ hf₁ hf₂
  let φ' :=
    compositeFixedDescentToSliceHom (J := J) (U := U) p T D q' gf₁ gf₂
      (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
      (by rw [← hq, ← hgf₂, Category.assoc, hf₂])
  let leftSource :=
    ((Fq.mapComp'
      f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
      (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app X₁)
  let rightSource :=
    ((Fq.mapComp'
      f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
      (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app X₂)
  let leftTarget :=
    ((Fcomp.mapComp'
      f₁.left.op.toLoc g.left.op.toLoc gf₁.left.op.toLoc
      (comp_toLoc_eq f₁.left g.left gf₁.left hgf₁left)).hom.toNatTrans.app
        (qFiberAsCompositeFiberObj (U := U) p X₁))
  let rightTarget :=
    ((Fcomp.mapComp'
      f₂.left.op.toLoc g.left.op.toLoc gf₂.left.op.toLoc
      (comp_toLoc_eq f₂.left g.left gf₂.left hgf₂left)).inv.toNatTrans.app
        (qFiberAsCompositeFiberObj (U := U) p X₂))
  have hφ :
      FY.map φ = e₁.inv ≫ d ≫ e₂.hom := by
    simpa [φ, X₁, X₂, Fcomp, FY, e₁, e₂, d] using
      compositeFixedDescentToSliceHom_forget (J := J) (U := U) p T D q f₁ f₂ hf₁ hf₂
  have hφ' :
      FY'.map φ' = eg₁.inv ≫ d' ≫ eg₂.hom := by
    simpa [φ', X₁, X₂, Fcomp, FY', eg₁, eg₂, d'] using
      compositeFixedDescentToSliceHom_forget (J := J) (U := U) p T D q' gf₁ gf₂
        (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
        (by rw [← hq, ← hgf₂, Category.assoc, hf₂])
  have hleftBoundary :
      leftTarget ≫ FYg.map e₁.hom =
        eg₁.hom ≫ FY'.map leftSource ≫ cg₁.inv := by
    simpa [Fcomp, Fq, FYg, FY', leftTarget, leftSource, e₁, eg₁, cg₁] using
      compCanonicalPullback_asCompositeFiberIso_pullHom_left_boundary
        (U := U) p f₁ g gf₁ hgf₁ X₁
  have hrightBoundary :
      cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget =
        FY'.map rightSource ≫ eg₂.inv := by
    simpa [Fcomp, Fq, FYg, FY', rightTarget, rightSource, e₂, eg₂, cg₂] using
      compCanonicalPullback_asCompositeFiberIso_pullHom_right_boundary
        (U := U) p f₂ g gf₂ hgf₂ X₂
  have hnat :
      FYg.map (FY.map φ) ≫ cg₂.hom =
        cg₁.hom ≫ FY'.map (FXg.map φ) := by
    simpa [Fcomp, Fq, FYg, FXg, FY, FY', cg₁, cg₂, φ] using
      compCanonicalPullback_asCompositeFiberIso_hom_naturality
        (U := U) p g φ
  have hleft :
      FY'.map leftSource =
        eg₁.inv ≫ leftTarget ≫ FYg.map e₁.hom ≫ cg₁.hom := by
    have h := congrArg (fun k => eg₁.inv ≫ k ≫ cg₁.hom) hleftBoundary.symm
    have h' :
        FY'.map leftSource ≫ cg₁.inv ≫ cg₁.hom =
          eg₁.inv ≫ leftTarget ≫ FYg.map e₁.hom ≫ cg₁.hom := by
      simpa only [Category.assoc, Iso.inv_hom_id_assoc, Category.id_comp] using h
    have htail :
        FY'.map leftSource ≫ cg₁.inv ≫ cg₁.hom = FY'.map leftSource := by
      calc
        FY'.map leftSource ≫ cg₁.inv ≫ cg₁.hom =
            FY'.map leftSource ≫ 𝟙 _ := by
          exact congrArg (fun k => FY'.map leftSource ≫ k) cg₁.inv_hom_id
        _ = FY'.map leftSource := by
          rw [Category.comp_id]
    exact htail.symm.trans h'
  have hmiddle :
      FY'.map (FXg.map φ) =
        cg₁.inv ≫ FYg.map (FY.map φ) ≫ cg₂.hom := by
    have h := congrArg (fun k => cg₁.inv ≫ k) hnat.symm
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Category.id_comp] using h
  have hright :
      FY'.map rightSource =
        cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget ≫ eg₂.hom := by
    have h := congrArg (fun k => k ≫ eg₂.hom) hrightBoundary.symm
    have h' :
        (FY'.map rightSource ≫ eg₂.inv) ≫ eg₂.hom =
          (cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget) ≫ eg₂.hom := by
      exact h
    have htail :
        (FY'.map rightSource ≫ eg₂.inv) ≫ eg₂.hom =
          FY'.map rightSource := by
      calc
        (FY'.map rightSource ≫ eg₂.inv) ≫ eg₂.hom =
            FY'.map rightSource ≫ eg₂.inv ≫ eg₂.hom := by
          rw [Category.assoc]
        _ = FY'.map rightSource ≫ 𝟙 _ := by
          exact congrArg (fun k => FY'.map rightSource ≫ k) eg₂.inv_hom_id
        _ = FY'.map rightSource := by
          rw [Category.comp_id]
    simpa only [Category.assoc] using htail.symm.trans h'
  have hDpull :
      leftTarget ≫ FYg.map d ≫ rightTarget = d' := by
    have hbase :=
      D.obj.pullHom_hom g.left q.left q'.left hqleft
        f₁.left f₂.left hf₁left hf₂left gf₁.left gf₂.left hgf₁left hgf₂left
    simpa [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Fcomp, FYg, leftTarget,
      rightTarget, d, d'] using hbase
  apply FY'.map_injective
  have hmapPull :
      FY'.map (Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ g gf₁ gf₂ hgf₁ hgf₂) =
        eg₁.inv ≫ d' ≫ eg₂.hom := by
    have hmap₀ :
        FY'.map (Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ g gf₁ gf₂ hgf₁ hgf₂) =
          FY'.map leftSource ≫ FY'.map (FXg.map φ) ≫ FY'.map rightSource := by
      rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
      change FY'.map (leftSource ≫ FXg.map φ ≫ rightSource) =
        FY'.map leftSource ≫ FY'.map (FXg.map φ) ≫ FY'.map rightSource
      exact functor_map_threefold_comp FY' leftSource (FXg.map φ) rightSource
    calc
      FY'.map (Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ g gf₁ gf₂ hgf₁ hgf₂) =
          FY'.map leftSource ≫ FY'.map (FXg.map φ) ≫ FY'.map rightSource := hmap₀
      _ =
          (eg₁.inv ≫ leftTarget ≫ FYg.map e₁.hom ≫ cg₁.hom) ≫
            (cg₁.inv ≫ FYg.map (FY.map φ) ≫ cg₂.hom) ≫
            (cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget ≫ eg₂.hom) := by
        have h₁ :
            FY'.map leftSource ≫ FY'.map (FXg.map φ) =
              (eg₁.inv ≫ leftTarget ≫ FYg.map e₁.hom ≫ cg₁.hom) ≫
                (cg₁.inv ≫ FYg.map (FY.map φ) ≫ cg₂.hom) :=
          congrArg₂ (fun a b => a ≫ b) hleft hmiddle
        have h₂ :
            (FY'.map leftSource ≫ FY'.map (FXg.map φ)) ≫ FY'.map rightSource =
              ((eg₁.inv ≫ leftTarget ≫ FYg.map e₁.hom ≫ cg₁.hom) ≫
                (cg₁.inv ≫ FYg.map (FY.map φ) ≫ cg₂.hom)) ≫
                FY'.map rightSource :=
          congrArg (fun k => k ≫ FY'.map rightSource) h₁
        have h₃ :
            ((eg₁.inv ≫ leftTarget ≫ FYg.map e₁.hom ≫ cg₁.hom) ≫
                (cg₁.inv ≫ FYg.map (FY.map φ) ≫ cg₂.hom)) ≫
                FY'.map rightSource =
              ((eg₁.inv ≫ leftTarget ≫ FYg.map e₁.hom ≫ cg₁.hom) ≫
                (cg₁.inv ≫ FYg.map (FY.map φ) ≫ cg₂.hom)) ≫
                (cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget ≫ eg₂.hom) :=
          congrArg
            (fun k => ((eg₁.inv ≫ leftTarget ≫ FYg.map e₁.hom ≫ cg₁.hom) ≫
              (cg₁.inv ≫ FYg.map (FY.map φ) ≫ cg₂.hom)) ≫ k)
            hright
        simpa only [Category.assoc] using h₂.trans h₃
      _ =
          eg₁.inv ≫ leftTarget ≫ FYg.map e₁.hom ≫
            FYg.map (FY.map φ) ≫ FYg.map e₂.inv ≫ rightTarget ≫ eg₂.hom := by
        calc
          (eg₁.inv ≫ leftTarget ≫ FYg.map e₁.hom ≫ cg₁.hom) ≫
              (cg₁.inv ≫ FYg.map (FY.map φ) ≫ cg₂.hom) ≫
              (cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget ≫ eg₂.hom) =
            eg₁.inv ≫ leftTarget ≫ FYg.map e₁.hom ≫
              (cg₁.hom ≫ cg₁.inv) ≫ FYg.map (FY.map φ) ≫
              (cg₂.hom ≫ cg₂.inv) ≫ FYg.map e₂.inv ≫ rightTarget ≫ eg₂.hom := by
              simp only [Category.assoc]
          _ =
            eg₁.inv ≫ leftTarget ≫ FYg.map e₁.hom ≫
              𝟙 _ ≫ FYg.map (FY.map φ) ≫
              𝟙 _ ≫ FYg.map e₂.inv ≫ rightTarget ≫ eg₂.hom := by
              exact congrArg₂
                (fun a b => eg₁.inv ≫ leftTarget ≫ FYg.map e₁.hom ≫
                  a ≫ FYg.map (FY.map φ) ≫ b ≫ FYg.map e₂.inv ≫
                  rightTarget ≫ eg₂.hom)
                cg₁.hom_inv_id cg₂.hom_inv_id
          _ =
            eg₁.inv ≫ leftTarget ≫ FYg.map e₁.hom ≫
              FYg.map (FY.map φ) ≫ FYg.map e₂.inv ≫ rightTarget ≫ eg₂.hom := by
              simp only [Category.id_comp, Category.assoc]
      _ =
          eg₁.inv ≫ leftTarget ≫ FYg.map e₁.hom ≫
            FYg.map (e₁.inv ≫ d ≫ e₂.hom) ≫ FYg.map e₂.inv ≫
            rightTarget ≫ eg₂.hom := by
        exact congrArg
          (fun k => eg₁.inv ≫ leftTarget ≫ FYg.map e₁.hom ≫
            FYg.map k ≫ FYg.map e₂.inv ≫ rightTarget ≫ eg₂.hom) hφ
      _ =
          eg₁.inv ≫ leftTarget ≫ FYg.map e₁.hom ≫
            (FYg.map e₁.inv ≫ FYg.map d ≫ FYg.map e₂.hom) ≫
            FYg.map e₂.inv ≫ rightTarget ≫ eg₂.hom := by
        exact congrArg
          (fun k => eg₁.inv ≫ leftTarget ≫ FYg.map e₁.hom ≫ k ≫
            FYg.map e₂.inv ≫ rightTarget ≫ eg₂.hom)
          (functor_map_threefold_comp FYg e₁.inv d e₂.hom)
      _ = eg₁.inv ≫ leftTarget ≫ FYg.map d ≫ rightTarget ≫ eg₂.hom := by
        calc
          eg₁.inv ≫ leftTarget ≫ FYg.map e₁.hom ≫
              (FYg.map e₁.inv ≫ FYg.map d ≫ FYg.map e₂.hom) ≫
              FYg.map e₂.inv ≫ rightTarget ≫ eg₂.hom =
            eg₁.inv ≫ leftTarget ≫
              (FYg.map e₁.hom ≫ FYg.map e₁.inv) ≫
              FYg.map d ≫ (FYg.map e₂.hom ≫ FYg.map e₂.inv) ≫
              rightTarget ≫ eg₂.hom := by
              simp only [Category.assoc]
          _ =
            eg₁.inv ≫ leftTarget ≫
              FYg.map (e₁.hom ≫ e₁.inv) ≫
              FYg.map d ≫ FYg.map (e₂.hom ≫ e₂.inv) ≫
              rightTarget ≫ eg₂.hom := by
              rw [FYg.map_comp, FYg.map_comp]
              rfl
          _ =
            eg₁.inv ≫ leftTarget ≫
              FYg.map (𝟙 _) ≫ FYg.map d ≫ FYg.map (e₂.hom ≫ e₂.inv) ≫
              rightTarget ≫ eg₂.hom := by
              exact congrArg
                (fun k => eg₁.inv ≫ leftTarget ≫ FYg.map k ≫ FYg.map d ≫
                  FYg.map (e₂.hom ≫ e₂.inv) ≫ rightTarget ≫ eg₂.hom)
                e₁.hom_inv_id
          _ =
            eg₁.inv ≫ leftTarget ≫
              FYg.map (𝟙 _) ≫ FYg.map d ≫ FYg.map (𝟙 _) ≫
              rightTarget ≫ eg₂.hom := by
              exact congrArg
                (fun k => eg₁.inv ≫ leftTarget ≫ FYg.map (𝟙 _) ≫ FYg.map d ≫
                  FYg.map k ≫ rightTarget ≫ eg₂.hom)
                e₂.hom_inv_id
          _ = eg₁.inv ≫ leftTarget ≫ FYg.map d ≫ rightTarget ≫ eg₂.hom := by
              rw [FYg.map_id, FYg.map_id]
              have hid :
                  𝟙 _ ≫ FYg.map d ≫ 𝟙 _ ≫ rightTarget ≫ eg₂.hom =
                    FYg.map d ≫ rightTarget ≫ eg₂.hom := by
                simp only [Category.id_comp]
              exact congrArg (fun k => eg₁.inv ≫ leftTarget ≫ k) hid
      _ = eg₁.inv ≫ d' ≫ eg₂.hom := by
        calc
          eg₁.inv ≫ leftTarget ≫ FYg.map d ≫ rightTarget ≫ eg₂.hom =
              eg₁.inv ≫ (leftTarget ≫ FYg.map d ≫ rightTarget) ≫ eg₂.hom := by
            simp only [Category.assoc]
          _ = eg₁.inv ≫ d' ≫ eg₂.hom := by
            exact congrArg (fun k => eg₁.inv ≫ k ≫ eg₂.hom) hDpull
  exact hmapPull.trans hφ'.symm

/-- Helper for Chap08 Lemma 8 13 2: a fixed-arrow composite descent datum over a slice cover
can be regarded as genuine slice descent data. -/
private noncomputable def compositeFixedDescentToSliceDescentData
    {S : Type*} [Category S] (p : S ⥤ Over U)
    [p.IsFibered] [(p ⋙ Over.forget U).IsFibered]
    {A : Over U} (T : (J.over U).Cover A)
    (D : (compositeDescentFixedArrowProperty (J := J) (U := U) (p := p) T).FullSubcategory) :
    (canonicalFiberPseudofunctor p).DescentData (fun I : T.Arrow => I.f) where
  obj I :=
    compositeFixedLocalObjToQFiberObj (U := U) p I.f (D.obj.obj I) (D.property I)
  hom {Y} q {I₁ I₂} f₁ f₂ hf₁ hf₂ :=
    compositeFixedDescentToSliceHom (J := J) (U := U) p T D q f₁ f₂ hf₁ hf₂
  pullHom_hom {Y' Y} g q q' hq {I₁ I₂} f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
    compositeFixedDescentToSliceHom_pullHom_hom
      (J := J) (U := U) p T D g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  hom_self {Y} q {I} f hf :=
    compositeFixedDescentToSliceHom_self (J := J) (U := U) p T D q f hf
  hom_comp {Y} q {I₁ I₂ I₃} f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
    compositeFixedDescentToSliceHom_comp
      (J := J) (U := U) p T D q f₁ f₂ f₃ hf₁ hf₂ hf₃

/-- Helper for Chap08 Lemma 8 13 2: the slice-to-composite fixed descent comparison is
essentially surjective. -/
private theorem sliceDescentToCompositeFixedDescentFunctor_essSurj
    {S : Type*} [Category S] (p : S ⥤ Over U)
    [p.IsFibered] [(p ⋙ Over.forget U).IsFibered]
    {A : Over U} (T : (J.over U).Cover A) :
    (sliceDescentToCompositeFixedDescentFunctor (J := J) (U := U) p T).EssSurj := by
  let Cfun := sliceDescentToCompositeFixedDescentFunctor (J := J) (U := U) p T
  refine { mem_essImage := fun D => ?_ }
  let E := compositeFixedDescentToSliceDescentData (J := J) (U := U) p T D
  refine ⟨E, ⟨?_⟩⟩
  apply ObjectProperty.isoMk
  let hObj : ∀ I : T.Arrow,
      qFiberAsCompositeFiberObj (U := U) p
          (compositeFixedLocalObjToQFiberObj (U := U) p I.f (D.obj.obj I) (D.property I)) =
        D.obj.obj I := fun I =>
    compositeFixedLocalObjToQFiberObj_forget (U := U) p I.f (D.obj.obj I) (D.property I)
  refine Pseudofunctor.DescentData.isoMk (fun I => ?_) ?_
  · exact eqToIso (hObj I)
  · intro Y q I₁ I₂ f₁ f₂ hf₁ hf₂
    let X₁ :=
      compositeFixedLocalObjToQFiberObj (U := U) p I₁.f (D.obj.obj I₁) (D.property I₁)
    let X₂ :=
      compositeFixedLocalObjToQFiberObj (U := U) p I₂.f (D.obj.obj I₂) (D.property I₂)
    let Y₀ : Over U := sliceDescentBaseObj (U := U) q
    let q₀ : Y₀ ⟶ A := sliceDescentBaseHom (U := U) q
    let f₁₀ : Y₀ ⟶ I₁.Y := sliceDescentLift (J := J) (U := U) T q f₁ hf₁
    let f₂₀ : Y₀ ⟶ I₂.Y := sliceDescentLift (J := J) (U := U) T q f₂ hf₂
    have hf₁₀ : f₁₀ ≫ I₁.f = q₀ := by
      simpa [f₁₀, q₀] using sliceDescentLift_comp (J := J) (U := U) T q f₁ hf₁
    have hf₂₀ : f₂₀ ≫ I₂.f = q₀ := by
      simpa [f₂₀, q₀] using sliceDescentLift_comp (J := J) (U := U) T q f₂ hf₂
    let Fcomp := canonicalFiberPseudofunctor (p ⋙ Over.forget U)
    let FY := qFiberToCompositeFiberFunctor (U := U) p Y₀
    let e₁ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₁₀ X₁
    let e₂ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₂₀ X₂
    have hX₁ :
        qFiberAsCompositeFiberObj (U := U) p X₁ = D.obj.obj I₁ := by
      exact hObj I₁
    have hX₂ :
        qFiberAsCompositeFiberObj (U := U) p X₂ = D.obj.obj I₂ := by
      exact hObj I₂
    let dComp :
        ((Fcomp.map f₁.op.toLoc).toFunctor.obj
            (qFiberAsCompositeFiberObj (U := U) p X₁)) ⟶
          ((Fcomp.map f₂.op.toLoc).toFunctor.obj
            (qFiberAsCompositeFiberObj (U := U) p X₂)) := by
      simpa [Fcomp, hX₁, hX₂] using
        (D.obj.hom q f₁ f₂ hf₁ hf₂)
    have hforget :
        FY.map
            (compositeFixedDescentToSliceHom (J := J) (U := U) p T D q₀ f₁₀ f₂₀
              hf₁₀ hf₂₀) =
          e₁.inv ≫ dComp ≫ e₂.hom := by
      simpa [X₁, X₂, Y₀, q₀, f₁₀, f₂₀, Fcomp, FY, e₁, e₂, dComp] using
        compositeFixedDescentToSliceHom_forget (J := J) (U := U) p T D q₀ f₁₀ f₂₀
          hf₁₀ hf₂₀
    have hslice :
        sliceDescentToCompositeHom (J := J) (U := U) p T E q f₁ f₂ hf₁ hf₂ =
          e₁.hom ≫
            FY.map
              (compositeFixedDescentToSliceHom (J := J) (U := U) p T D q₀ f₁₀ f₂₀
                hf₁₀ hf₂₀) ≫
            e₂.inv := by
      dsimp [sliceDescentToCompositeHom, E, compositeFixedDescentToSliceDescentData,
        X₁, X₂, Y₀, q₀, f₁₀, f₂₀, e₁, e₂, FY]
    have hcore :
        sliceDescentToCompositeHom (J := J) (U := U) p T E q f₁ f₂ hf₁ hf₂ =
          dComp := by
      have hmiddle :
          e₁.hom ≫
              FY.map
                (compositeFixedDescentToSliceHom (J := J) (U := U) p T D q₀ f₁₀ f₂₀
                  hf₁₀ hf₂₀) ≫
              e₂.inv =
            e₁.hom ≫ (e₁.inv ≫ dComp ≫ e₂.hom) ≫ e₂.inv :=
        congrArg (fun k => e₁.hom ≫ k ≫ e₂.inv) hforget
      have hcancel :
          e₁.hom ≫ (e₁.inv ≫ dComp ≫ e₂.hom) ≫ e₂.inv = dComp := by
        rw [Category.assoc]
        rw [e₁.hom_inv_id_assoc]
        change (dComp ≫ e₂.hom) ≫ e₂.inv = dComp
        calc
          (dComp ≫ e₂.hom) ≫ e₂.inv = dComp ≫ (e₂.hom ≫ e₂.inv) :=
            Category.assoc dComp e₂.hom e₂.inv
          _ = dComp ≫ 𝟙 _ := by
            exact congrArg (fun k => dComp ≫ k) e₂.hom_inv_id
          _ = dComp := by
            rw [Category.comp_id]
      exact hslice.trans (hmiddle.trans hcancel)
    dsimp [Cfun, sliceDescentToCompositeFixedDescentFunctor, E,
      compositeFixedDescentToSliceDescentData]
    cases hObj I₁
    cases hObj I₂
    cases hX₁
    cases hX₂
    change _ =
      sliceDescentToCompositeHom (J := J) (U := U) p T E q f₁ f₂ hf₁ hf₂ ≫ _
    rw [hcore]
    rw [eqToHom_map, eqToHom_map]
    rw [← heq_eq_eq]
    exact
      (eqToHom_comp_heq (D.obj.hom q f₁ f₂ hf₁ hf₂) _).trans
        ((by simp [dComp] : D.obj.hom q f₁ f₂ hf₁ hf₂ ≍ dComp).trans
          (comp_eqToHom_heq dComp _).symm)

/-- Helper for Chap08 Lemma 8 13 2: the slice-to-composite fixed descent comparison is an
equivalence. -/
private theorem sliceDescentToCompositeFixedDescentFunctor_isEquivalence
    {S : Type*} [Category S] (p : S ⥤ Over U)
    [p.IsFibered] [(p ⋙ Over.forget U).IsFibered]
    {A : Over U} (T : (J.over U).Cover A) :
    (sliceDescentToCompositeFixedDescentFunctor (J := J) (U := U) p T).IsEquivalence :=
  { faithful := sliceDescentToCompositeFixedDescentFunctor_faithful (J := J) (U := U) p T
    full := sliceDescentToCompositeFixedDescentFunctor_full (J := J) (U := U) p T
    essSurj := sliceDescentToCompositeFixedDescentFunctor_essSurj (J := J) (U := U) p T }

/-- Helper for Chap08 Lemma 8 13 2: the canonical comparison between composite pullbacks and
slice pullbacks identifies the two canonical descent data attached to one fiber object. -/
private theorem sliceCanonicalToComposite_component_comm
    {S : Type*} [Category S] (p : S ⥤ Over U)
    [p.IsFibered] [(p ⋙ Over.forget U).IsFibered]
    {A : Over U} (T : (J.over U).Cover A) (x : p.Fiber A)
    {Y : C} (q : Y ⟶ A.left) {I₁ I₂ : T.Arrow}
    (f₁ : Y ⟶ I₁.Y.left) (f₂ : Y ⟶ I₂.Y.left)
    (hf₁ : f₁ ≫ I₁.f.left = q) (hf₂ : f₂ ≫ I₂.f.left = q) :
    (((canonicalFiberPseudofunctor (p ⋙ Over.forget U)).map f₁.op.toLoc).toFunctor.map
        (compCanonicalPullback_asCompositeFiberIso (U := U) p I₁.f x).hom) ≫
      sliceDescentToCompositeHom (J := J) (U := U) p T
        (((canonicalFiberPseudofunctor p).toDescentData
          (fun I : T.Arrow => I.f)).obj x) q f₁ f₂ hf₁ hf₂ =
    ((((canonicalFiberPseudofunctor (p ⋙ Over.forget U)).toDescentData
        (fun I : T.Arrow => I.f.left)).obj
          (qFiberAsCompositeFiberObj (U := U) p x)).hom q f₁ f₂ hf₁ hf₂) ≫
      (((canonicalFiberPseudofunctor (p ⋙ Over.forget U)).map f₂.op.toLoc).toFunctor.map
        (compCanonicalPullback_asCompositeFiberIso (U := U) p I₂.f x).hom) := by
  let Fcomp := canonicalFiberPseudofunctor (p ⋙ Over.forget U)
  let Fp := canonicalFiberPseudofunctor p
  let Y₀ : Over U := sliceDescentBaseObj (U := U) q
  let q₀ : Y₀ ⟶ A := sliceDescentBaseHom (U := U) q
  let f₁₀ : Y₀ ⟶ I₁.Y := sliceDescentLift (J := J) (U := U) T q f₁ hf₁
  let f₂₀ : Y₀ ⟶ I₂.Y := sliceDescentLift (J := J) (U := U) T q f₂ hf₂
  have hf₁₀ : f₁₀ ≫ I₁.f = q₀ := by
    simpa [f₁₀, q₀] using sliceDescentLift_comp (J := J) (U := U) T q f₁ hf₁
  have hf₂₀ : f₂₀ ≫ I₂.f = q₀ := by
    simpa [f₂₀, q₀] using sliceDescentLift_comp (J := J) (U := U) T q f₂ hf₂
  let FY := qFiberToCompositeFiberFunctor (U := U) p Y₀
  let E₁ := compCanonicalPullback_asCompositeFiberIso (U := U) p I₁.f x
  let E₂ := compCanonicalPullback_asCompositeFiberIso (U := U) p I₂.f x
  let e₀ := compCanonicalPullback_asCompositeFiberIso (U := U) p q₀ x
  let e₁ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₁₀
    ((Fp.map I₁.f.op.toLoc).toFunctor.obj x)
  let e₂ := compCanonicalPullback_asCompositeFiberIso (U := U) p f₂₀
    ((Fp.map I₂.f.op.toLoc).toFunctor.obj x)
  let tc₁ :=
    Fcomp.mapComp' I₁.f.left.op.toLoc f₁.op.toLoc q.op.toLoc
      (comp_toLoc_eq I₁.f.left f₁ q hf₁)
  let tc₂ :=
    Fcomp.mapComp' I₂.f.left.op.toLoc f₂.op.toLoc q.op.toLoc
      (comp_toLoc_eq I₂.f.left f₂ q hf₂)
  let sc₁ :=
    Fp.mapComp' I₁.f.op.toLoc f₁₀.op.toLoc q₀.op.toLoc
      (comp_toLoc_eq I₁.f f₁₀ q₀ hf₁₀)
  let sc₂ :=
    Fp.mapComp' I₂.f.op.toLoc f₂₀.op.toLoc q₀.op.toLoc
      (comp_toLoc_eq I₂.f f₂₀ q₀ hf₂₀)
  let t₁ :
      ((Fcomp.map q.op.toLoc).toFunctor.obj (qFiberAsCompositeFiberObj (U := U) p x)) ≅
        ((Fcomp.map f₁.op.toLoc).toFunctor.obj
          ((Fcomp.map I₁.f.left.op.toLoc).toFunctor.obj
            (qFiberAsCompositeFiberObj (U := U) p x))) :=
    { hom := tc₁.hom.toNatTrans.app (qFiberAsCompositeFiberObj (U := U) p x)
      inv := tc₁.inv.toNatTrans.app (qFiberAsCompositeFiberObj (U := U) p x)
      hom_inv_id := by
        exact Cat.Hom.hom_inv_id_toNatTrans_app tc₁ (qFiberAsCompositeFiberObj (U := U) p x)
      inv_hom_id := by
        exact Cat.Hom.inv_hom_id_toNatTrans_app tc₁ (qFiberAsCompositeFiberObj (U := U) p x) }
  let t₂ :
      ((Fcomp.map q.op.toLoc).toFunctor.obj (qFiberAsCompositeFiberObj (U := U) p x)) ≅
        ((Fcomp.map f₂.op.toLoc).toFunctor.obj
          ((Fcomp.map I₂.f.left.op.toLoc).toFunctor.obj
            (qFiberAsCompositeFiberObj (U := U) p x))) :=
    { hom := tc₂.hom.toNatTrans.app (qFiberAsCompositeFiberObj (U := U) p x)
      inv := tc₂.inv.toNatTrans.app (qFiberAsCompositeFiberObj (U := U) p x)
      hom_inv_id := by
        exact Cat.Hom.hom_inv_id_toNatTrans_app tc₂ (qFiberAsCompositeFiberObj (U := U) p x)
      inv_hom_id := by
        exact Cat.Hom.inv_hom_id_toNatTrans_app tc₂ (qFiberAsCompositeFiberObj (U := U) p x) }
  let s₁ :
      ((Fp.map q₀.op.toLoc).toFunctor.obj x) ≅
        ((Fp.map f₁₀.op.toLoc).toFunctor.obj
          ((Fp.map I₁.f.op.toLoc).toFunctor.obj x)) :=
    { hom := sc₁.hom.toNatTrans.app x
      inv := sc₁.inv.toNatTrans.app x
      hom_inv_id := by
        exact Cat.Hom.hom_inv_id_toNatTrans_app sc₁ x
      inv_hom_id := by
        exact Cat.Hom.inv_hom_id_toNatTrans_app sc₁ x }
  let s₂ :
      ((Fp.map q₀.op.toLoc).toFunctor.obj x) ≅
        ((Fp.map f₂₀.op.toLoc).toFunctor.obj
          ((Fp.map I₂.f.op.toLoc).toFunctor.obj x)) :=
    { hom := sc₂.hom.toNatTrans.app x
      inv := sc₂.inv.toNatTrans.app x
      hom_inv_id := by
        exact Cat.Hom.hom_inv_id_toNatTrans_app sc₂ x
      inv_hom_id := by
        exact Cat.Hom.inv_hom_id_toNatTrans_app sc₂ x }
  have hleftBoundary :
      t₁.hom ≫ ((Fcomp.map f₁.op.toLoc).toFunctor.map E₁.hom) =
        e₀.hom ≫ FY.map s₁.hom ≫ e₁.inv := by
    simpa [Fcomp, Fp, FY, Y₀, q₀, f₁₀, E₁, e₀, e₁, tc₁, sc₁, t₁, s₁] using
      compCanonicalPullback_asCompositeFiberIso_pullHom_left_boundary
        (U := U) p I₁.f f₁₀ q₀ hf₁₀ x
  have hrightBoundary :
      t₂.hom ≫ ((Fcomp.map f₂.op.toLoc).toFunctor.map E₂.hom) =
        e₀.hom ≫ FY.map s₂.hom ≫ e₂.inv := by
    simpa [Fcomp, Fp, FY, Y₀, q₀, f₂₀, E₂, e₀, e₂, tc₂, sc₂, t₂, s₂] using
      compCanonicalPullback_asCompositeFiberIso_pullHom_left_boundary
        (U := U) p I₂.f f₂₀ q₀ hf₂₀ x
  have hleft :
      ((Fcomp.map f₁.op.toLoc).toFunctor.map E₁.hom) ≫ e₁.hom =
        t₁.inv ≫ e₀.hom ≫ FY.map s₁.hom := by
    calc
      ((Fcomp.map f₁.op.toLoc).toFunctor.map E₁.hom) ≫ e₁.hom =
          (t₁.inv ≫ t₁.hom) ≫
            ((Fcomp.map f₁.op.toLoc).toFunctor.map E₁.hom) ≫ e₁.hom := by
        rw [t₁.inv_hom_id]
        simp only [Category.id_comp]
      _ = t₁.inv ≫
            (t₁.hom ≫ ((Fcomp.map f₁.op.toLoc).toFunctor.map E₁.hom)) ≫
          e₁.hom := by
        simp only [Category.assoc]
      _ = t₁.inv ≫ (e₀.hom ≫ FY.map s₁.hom ≫ e₁.inv) ≫ e₁.hom := by
        exact congrArg (fun k => t₁.inv ≫ k ≫ e₁.hom) hleftBoundary
      _ = t₁.inv ≫ e₀.hom ≫ FY.map s₁.hom := by
        calc
          t₁.inv ≫ (e₀.hom ≫ FY.map s₁.hom ≫ e₁.inv) ≫ e₁.hom =
              t₁.inv ≫ e₀.hom ≫ FY.map s₁.hom ≫ (e₁.inv ≫ e₁.hom) := by
            simp only [Category.assoc]
          _ = t₁.inv ≫ e₀.hom ≫ FY.map s₁.hom ≫ 𝟙 _ := by
            exact congrArg (fun k => t₁.inv ≫ e₀.hom ≫ FY.map s₁.hom ≫ k)
              e₁.inv_hom_id
          _ = t₁.inv ≫ e₀.hom ≫ FY.map s₁.hom := by
            rw [Category.comp_id]
  have hmiddle :
      FY.map s₁.hom ≫ FY.map (s₁.inv ≫ s₂.hom) = FY.map s₂.hom := by
    calc
      FY.map s₁.hom ≫ FY.map (s₁.inv ≫ s₂.hom) =
          FY.map (s₁.hom ≫ (s₁.inv ≫ s₂.hom)) := by
        rw [← FY.map_comp]
      _ = FY.map ((s₁.hom ≫ s₁.inv) ≫ s₂.hom) := by
        simp only [Category.assoc]
      _ = FY.map (𝟙 _ ≫ s₂.hom) := by
        exact congrArg (fun k => FY.map (k ≫ s₂.hom)) s₁.hom_inv_id
      _ = FY.map s₂.hom := by
        rw [Category.id_comp]
  have hcore :
      ((Fcomp.map f₁.op.toLoc).toFunctor.map E₁.hom) ≫
          e₁.hom ≫ FY.map (s₁.inv ≫ s₂.hom) ≫ e₂.inv =
        t₁.inv ≫ e₀.hom ≫ FY.map s₂.hom ≫ e₂.inv := by
    have hleftTail :
        ((((Fcomp.map f₁.op.toLoc).toFunctor.map E₁.hom) ≫ e₁.hom) ≫
              FY.map (s₁.inv ≫ s₂.hom)) ≫ e₂.inv =
          (((t₁.inv ≫ e₀.hom ≫ FY.map s₁.hom) ≫
              FY.map (s₁.inv ≫ s₂.hom)) ≫ e₂.inv) := by
      exact congrArg (fun k => (k ≫ FY.map (s₁.inv ≫ s₂.hom)) ≫ e₂.inv) hleft
    calc
      ((Fcomp.map f₁.op.toLoc).toFunctor.map E₁.hom) ≫
          e₁.hom ≫ FY.map (s₁.inv ≫ s₂.hom) ≫ e₂.inv =
          ((((Fcomp.map f₁.op.toLoc).toFunctor.map E₁.hom) ≫ e₁.hom) ≫
              FY.map (s₁.inv ≫ s₂.hom)) ≫ e₂.inv := by
        simp only [Category.assoc]
      _ =
          ((t₁.inv ≫ e₀.hom ≫ FY.map s₁.hom) ≫
            FY.map (s₁.inv ≫ s₂.hom)) ≫ e₂.inv := hleftTail
      _ = t₁.inv ≫ e₀.hom ≫
            (FY.map s₁.hom ≫ FY.map (s₁.inv ≫ s₂.hom)) ≫ e₂.inv := by
        simp only [Category.assoc]
      _ = t₁.inv ≫ e₀.hom ≫ FY.map s₂.hom ≫ e₂.inv := by
        exact congrArg (fun k => t₁.inv ≫ e₀.hom ≫ k ≫ e₂.inv) hmiddle
  have hright :
      t₁.inv ≫ t₂.hom ≫ ((Fcomp.map f₂.op.toLoc).toFunctor.map E₂.hom) =
        t₁.inv ≫ e₀.hom ≫ FY.map s₂.hom ≫ e₂.inv := by
    calc
      t₁.inv ≫ t₂.hom ≫ ((Fcomp.map f₂.op.toLoc).toFunctor.map E₂.hom) =
          t₁.inv ≫
            (t₂.hom ≫ ((Fcomp.map f₂.op.toLoc).toFunctor.map E₂.hom)) := by
        rfl
      _ = t₁.inv ≫ (e₀.hom ≫ FY.map s₂.hom ≫ e₂.inv) := by
        exact congrArg (fun k => t₁.inv ≫ k) hrightBoundary
      _ = t₁.inv ≫ e₀.hom ≫ FY.map s₂.hom ≫ e₂.inv := by
        simp only [Category.assoc]
  have hfinal :
      ((Fcomp.map f₁.op.toLoc).toFunctor.map E₁.hom) ≫
          e₁.hom ≫ FY.map (s₁.inv ≫ s₂.hom) ≫ e₂.inv =
        (t₁.inv ≫ t₂.hom) ≫ ((Fcomp.map f₂.op.toLoc).toFunctor.map E₂.hom) :=
    hcore.trans (by
      simpa only [Category.assoc] using hright.symm)
  simpa [Fcomp, Fp, FY, Y₀, q₀, f₁₀, f₂₀, E₁, E₂, e₁, e₂, t₁, t₂, s₁, s₂,
    tc₁, tc₂, sc₁, sc₂, sliceDescentToCompositeHom] using hfinal

/-- Helper for Chap08 Lemma 8 13 2: on a fixed slice cover, first taking canonical slice
descent and then forgetting to the composite fixed-arrow descent data agrees with first passing
to the fixed composite fiber and then taking canonical composite descent. -/
private noncomputable def sliceCanonicalToComposite_fixedDescentIso
    {S : Type*} [Category S] (p : S ⥤ Over U)
    [p.IsFibered] [(p ⋙ Over.forget U).IsFibered]
    {A : Over U} (T : (J.over U).Cover A) :
    (qFiberToCompositeFixedFiberFunctor (U := U) p A ⋙
        compositeFixedFiberToFixedDescentFunctor (J := J) (U := U) p T) ≅
      ((canonicalFiberPseudofunctor p).toDescentData (fun I : T.Arrow => I.f) ⋙
        sliceDescentToCompositeFixedDescentFunctor (J := J) (U := U) p T) := by
  let Ffib := qFiberToCompositeFixedFiberFunctor (U := U) p A
  let Ffix := compositeFixedFiberToFixedDescentFunctor (J := J) (U := U) p T
  let Φ := (canonicalFiberPseudofunctor p).toDescentData (fun I : T.Arrow => I.f)
  let Cfun := sliceDescentToCompositeFixedDescentFunctor (J := J) (U := U) p T
  refine NatIso.ofComponents (fun x => ?_) ?_
  · apply ObjectProperty.isoMk
    refine Pseudofunctor.DescentData.isoMk (fun I => ?_) ?_
    · change
        (((canonicalFiberPseudofunctor (p ⋙ Over.forget U)).map I.f.left.op.toLoc).toFunctor.obj
            (qFiberAsCompositeFiberObj (U := U) p x)) ≅
          qFiberAsCompositeFiberObj (U := U) p
            (((canonicalFiberPseudofunctor p).map I.f.op.toLoc).toFunctor.obj x)
      exact compCanonicalPullback_asCompositeFiberIso (U := U) p I.f x
    · intro Y q I₁ I₂ f₁ f₂ hf₁ hf₂
      change
        (((canonicalFiberPseudofunctor (p ⋙ Over.forget U)).map f₁.op.toLoc).toFunctor.map
            (compCanonicalPullback_asCompositeFiberIso (U := U) p I₁.f x).hom) ≫
          sliceDescentToCompositeHom (J := J) (U := U) p T
            (((canonicalFiberPseudofunctor p).toDescentData
              (fun I : T.Arrow => I.f)).obj x) q f₁ f₂ hf₁ hf₂ =
        ((((canonicalFiberPseudofunctor (p ⋙ Over.forget U)).toDescentData
            (fun I : T.Arrow => I.f.left)).obj
              (qFiberAsCompositeFiberObj (U := U) p x)).hom q f₁ f₂ hf₁ hf₂) ≫
          (((canonicalFiberPseudofunctor (p ⋙ Over.forget U)).map f₂.op.toLoc).toFunctor.map
            (compCanonicalPullback_asCompositeFiberIso (U := U) p I₂.f x).hom)
      exact
        sliceCanonicalToComposite_component_comm
          (J := J) (U := U) p T x (q := q)
          (I₁ := I₁) (I₂ := I₂) f₁ f₂ hf₁ hf₂
  · intro x y φ
    apply ObjectProperty.hom_ext
    apply Pseudofunctor.DescentData.hom_ext
    intro I
    change
      ((canonicalFiberPseudofunctor (p ⋙ Over.forget U)).map I.f.left.op.toLoc).toFunctor.map
          ((qFiberToCompositeFiberFunctor (U := U) p A).map φ) ≫
        (compCanonicalPullback_asCompositeFiberIso (U := U) p I.f y).hom =
      (compCanonicalPullback_asCompositeFiberIso (U := U) p I.f x).hom ≫
        (qFiberToCompositeFiberFunctor (U := U) p I.Y).map
          (((canonicalFiberPseudofunctor p).map I.f.op.toLoc).toFunctor.map φ)
    exact
      compCanonicalPullback_asCompositeFiberIso_hom_naturality
        (U := U) p I.f φ

/-- Helper for Chap08 Lemma 8 13 2: if the composite projection is a stack over the base site,
then the fixed-cover slice descent functor is an equivalence. -/
private theorem sliceCover_toDescentData_isEquivalence_of_comp
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {S : Type*} [Category S] (p : S ⥤ Over U)
    [p.IsFibered] [(p ⋙ Over.forget U).IsFibered]
    (hcomp : IsStackOnSite J (p ⋙ Over.forget U))
    {A : Over U} (T : (J.over U).Cover A) :
    ((canonicalFiberPseudofunctor p).toDescentData
      (fun I : T.Arrow => I.f)).IsEquivalence := by
  let Φ := (canonicalFiberPseudofunctor p).toDescentData (fun I : T.Arrow => I.f)
  let Cfun := sliceDescentToCompositeFixedDescentFunctor (J := J) (U := U) p T
  let Ffib := qFiberToCompositeFixedFiberFunctor (U := U) p A
  let Ffix := compositeFixedFiberToFixedDescentFunctor (J := J) (U := U) p T
  have hFfib : Ffib.IsEquivalence :=
    qFiberToCompositeFixedFiberFunctor_isEquivalence (U := U) p A
  have hFfix : Ffix.IsEquivalence :=
    compositeFixedFiberToFixedDescentFunctor_isEquivalence (J := J) (U := U) hU p hcomp T
  letI : Ffib.IsEquivalence := hFfib
  letI : Ffix.IsEquivalence := hFfix
  have hright : (Ffib ⋙ Ffix).IsEquivalence :=
    Functor.isEquivalence_trans Ffib Ffix
  have hIso :
      Ffib ⋙ Ffix ≅ Φ ⋙ Cfun :=
    sliceCanonicalToComposite_fixedDescentIso (J := J) (U := U) p T
  have hleft : (Φ ⋙ Cfun).IsEquivalence :=
    (Functor.isEquivalence_iff_of_iso hIso).1 hright
  letI : Cfun.Full := sliceDescentToCompositeFixedDescentFunctor_full (J := J) (U := U) p T
  letI : Cfun.Faithful :=
    sliceDescentToCompositeFixedDescentFunctor_faithful (J := J) (U := U) p T
  letI : (Φ ⋙ Cfun).IsEquivalence := hleft
  exact isEquivalence_of_comp_right_full_faithful Φ Cfun

/-- Helper for Chap08 Lemma 8 13 2: for a fixed base cover, prestackness of the composite
fiber pseudofunctor reduces stack descent to essential surjectivity. -/
private theorem compCover_isEquivalence_of_prestack_essSurj
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    [Pseudofunctor.IsPrestack (canonicalFiberPseudofunctor (q ⋙ Over.forget U)) J]
    {V : C} (T : J.Cover V)
    (hEss :
      ((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).toDescentData
        (fun I : T.Arrow ↦ I.f)).EssSurj) :
    ((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).toDescentData
      (fun I : T.Arrow ↦ I.f)).IsEquivalence := by
  -- The arrows listed by the cover generate exactly the cover's sieve.
  have hCover :
      Sieve.ofArrows (fun I : T.Arrow ↦ I.Y) (fun I ↦ I.f) ∈ J V := by
    rw [T.ofArrows_eq]
    exact T.condition
  -- Prestackness supplies full faithfulness; the caller supplies object effectiveness.
  exact
    { faithful :=
        ((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).fullyFaithfulToDescentData
          (fun I : T.Arrow ↦ I.f) hCover).faithful
      full :=
        ((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).fullyFaithfulToDescentData
          (fun I : T.Arrow ↦ I.f) hCover).full
      essSurj := hEss }

/-- Helper for Chap08 Lemma 8 13 2: the full subcategory of base-cover composite descent
data whose local objects remember one fixed glued arrow `u : V ⟶ U`. -/
private abbrev compositeBaseDescentFixedArrowProperty
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {V : C} (T : J.Cover V) (u : V ⟶ U) :
    ObjectProperty
      ((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).DescentData
        (fun I : T.Arrow ↦ I.f)) :=
  fun D => ∀ I : T.Arrow,
    compositeFiberArrowToU (U := U) q (D.obj I) = I.f ≫ u

/-- Helper for Chap08 Lemma 8 13 2: pulling a fixed-arrow composite descent datum along a
refinement preserves the fixed-arrow condition. -/
private theorem compositeFixed_pullFunctor_preserves
    {ι ι' : Type*} {V : C}
    {X : ι → C} {f : ∀ i, X i ⟶ V}
    {X' : ι' → C} {f' : ∀ j, X' j ⟶ V}
    {α : ι' → ι} {p' : ∀ j, X' j ⟶ X (α j)}
    (w : ∀ j, p' j ≫ f (α j) = f' j)
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered] (u : V ⟶ U)
    (D : (canonicalFiberPseudofunctor (q ⋙ Over.forget U)).DescentData f)
    (hD : ∀ i, compositeFiberArrowToU (U := U) q (D.obj i) = f i ≫ u) :
    ∀ j,
      compositeFiberArrowToU (U := U) q
        (((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).map
          (p' j).op.toLoc).toFunctor.obj (D.obj (α j))) =
      f' j ≫ u := by
  intro j
  rw [composite_pseudofunctor_map_obj_arrow_eq_comp (U := U) q
    (f := p' j) (a := D.obj (α j))]
  rw [hD (α j)]
  calc
    p' j ≫ (f (α j) ≫ u) = (p' j ≫ f (α j)) ≫ u := by
      exact (Category.assoc (p' j) (f (α j)) u).symm
    _ = f' j ≫ u := by
      rw [w j]

private theorem standardSliceToBase_w
    {V : C} (T : J.Cover V) (u : V ⟶ U) (I : T.Arrow) :
    (𝟙 I.Y) ≫
        (standardSliceCoverArrowOfBaseArrow (J := J) (U := U) T u I).f.left =
      I.f ≫ 𝟙 V := by
  rw [Category.id_comp]
  rw [standardSliceCoverArrowOfBaseArrow_left (J := J) (U := U) T u I]
  rw [Category.comp_id]

private theorem standardSliceToBase_w_noId
    {V : C} (T : J.Cover V) (u : V ⟶ U) (I : T.Arrow) :
    (𝟙 I.Y) ≫
        (standardSliceCoverArrowOfBaseArrow (J := J) (U := U) T u I).f.left =
      I.f := by
  rw [Category.id_comp]
  rw [standardSliceCoverArrowOfBaseArrow_left (J := J) (U := U) T u I]

private theorem baseToStandardSlice_w
    {V : C} (T : J.Cover V) (u : V ⟶ U)
    (K : (standardSliceCover (J := J) (U := U) T u).Arrow) :
    standardSliceCoverBaseFactorHom (J := J) (U := U) T u K ≫
        (standardSliceCoverBaseFactorIndex (J := J) (U := U) T u K).f =
      K.f.left ≫ 𝟙 V := by
  rw [standardSliceCoverBaseFactor_fac (J := J) (U := U) T u K]
  exact (Category.comp_id K.f.left).symm

private theorem baseToStandardSlice_w_noId
    {V : C} (T : J.Cover V) (u : V ⟶ U)
    (K : (standardSliceCover (J := J) (U := U) T u).Arrow) :
    standardSliceCoverBaseFactorHom (J := J) (U := U) T u K ≫
        (standardSliceCoverBaseFactorIndex (J := J) (U := U) T u K).f =
      K.f.left :=
  standardSliceCoverBaseFactor_fac (J := J) (U := U) T u K

/-- Helper for Chap08 Lemma 8 13 2: pull descent data from the projected standard slice cover
to the original base cover using the tautological base-cover arrows. -/
private noncomputable def standardSliceToBaseDescentPullFunctor
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {V : C} (T : J.Cover V) (u : V ⟶ U) :
    (canonicalFiberPseudofunctor (q ⋙ Over.forget U)).DescentData
        (fun K : (standardSliceCover (J := J) (U := U) T u).Arrow => K.f.left) ⥤
      (canonicalFiberPseudofunctor (q ⋙ Over.forget U)).DescentData
        (fun I : T.Arrow => I.f) :=
  let F := canonicalFiberPseudofunctor (q ⋙ Over.forget U)
  Pseudofunctor.DescentData.pullFunctor
    (F := F)
    (f := fun K : (standardSliceCover (J := J) (U := U) T u).Arrow => K.f.left)
    (f' := fun I : T.Arrow => I.f)
    (p := 𝟙 V)
    (α := fun I : T.Arrow => standardSliceCoverArrowOfBaseArrow (J := J) (U := U) T u I)
    (p' := fun I : T.Arrow => 𝟙 I.Y)
    (standardSliceToBase_w (J := J) (U := U) T u)

/-- Helper for Chap08 Lemma 8 13 2: pull descent data from the base cover to the projected
standard slice cover by the chosen factorization of each standard slice arrow. -/
private noncomputable def baseToStandardSliceDescentPullFunctor
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {V : C} (T : J.Cover V) (u : V ⟶ U) :
    (canonicalFiberPseudofunctor (q ⋙ Over.forget U)).DescentData
        (fun I : T.Arrow => I.f) ⥤
      (canonicalFiberPseudofunctor (q ⋙ Over.forget U)).DescentData
        (fun K : (standardSliceCover (J := J) (U := U) T u).Arrow => K.f.left) :=
  let F := canonicalFiberPseudofunctor (q ⋙ Over.forget U)
  Pseudofunctor.DescentData.pullFunctor
    (F := F)
    (f := fun I : T.Arrow => I.f)
    (f' := fun K : (standardSliceCover (J := J) (U := U) T u).Arrow => K.f.left)
    (p := 𝟙 V)
    (α := fun K : (standardSliceCover (J := J) (U := U) T u).Arrow =>
      standardSliceCoverBaseFactorIndex (J := J) (U := U) T u K)
    (p' := fun K : (standardSliceCover (J := J) (U := U) T u).Arrow =>
      standardSliceCoverBaseFactorHom (J := J) (U := U) T u K)
    (baseToStandardSlice_w (J := J) (U := U) T u)

/-- Helper for Chap08 Lemma 8 13 2: the projected standard slice cover and the base cover have
equivalent fixed-arrow composite descent full subcategories. -/
private noncomputable def standardSliceFixedDescentToBaseFixedDescentFunctor
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {V : C} (T : J.Cover V) (u : V ⟶ U) :
    (compositeDescentFixedArrowProperty (J := J) (U := U) (p := q)
        (standardSliceCover (J := J) (U := U) T u)).FullSubcategory ⥤
      (compositeBaseDescentFixedArrowProperty (J := J) (U := U) q T u).FullSubcategory :=
  (compositeBaseDescentFixedArrowProperty (J := J) (U := U) q T u).lift
    ((compositeDescentFixedArrowProperty (J := J) (U := U) (p := q)
        (standardSliceCover (J := J) (U := U) T u)).ι ⋙
      standardSliceToBaseDescentPullFunctor (J := J) (U := U) q T u)
    (fun D => by
      intro I
      exact
        compositeFixed_pullFunctor_preserves (U := U)
          (X := fun K : (standardSliceCover (J := J) (U := U) T u).Arrow => K.Y.left)
          (f := fun K : (standardSliceCover (J := J) (U := U) T u).Arrow => K.f.left)
          (X' := fun I : T.Arrow => I.Y)
          (f' := fun I : T.Arrow => I.f)
          (α := fun I : T.Arrow =>
            standardSliceCoverArrowOfBaseArrow (J := J) (U := U) T u I)
          (p' := fun I : T.Arrow => 𝟙 I.Y)
          (w := fun I : T.Arrow => standardSliceToBase_w_noId (J := J) (U := U) T u I)
          q u D.obj D.property I)

/-- Helper for Chap08 Lemma 8 13 2: the inverse fixed-arrow descent comparison from the base
cover to the projected standard slice cover. -/
private noncomputable def baseFixedDescentToStandardSliceFixedDescentFunctor
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {V : C} (T : J.Cover V) (u : V ⟶ U) :
    (compositeBaseDescentFixedArrowProperty (J := J) (U := U) q T u).FullSubcategory ⥤
      (compositeDescentFixedArrowProperty (J := J) (U := U) (p := q)
        (standardSliceCover (J := J) (U := U) T u)).FullSubcategory :=
  (compositeDescentFixedArrowProperty (J := J) (U := U) (p := q)
      (standardSliceCover (J := J) (U := U) T u)).lift
    ((compositeBaseDescentFixedArrowProperty (J := J) (U := U) q T u).ι ⋙
      baseToStandardSliceDescentPullFunctor (J := J) (U := U) q T u)
    (fun D => by
      intro K
      exact
        compositeFixed_pullFunctor_preserves (U := U)
          (X := fun I : T.Arrow => I.Y)
          (f := fun I : T.Arrow => I.f)
          (X' := fun K : (standardSliceCover (J := J) (U := U) T u).Arrow => K.Y.left)
          (f' := fun K : (standardSliceCover (J := J) (U := U) T u).Arrow => K.f.left)
          (α := fun K : (standardSliceCover (J := J) (U := U) T u).Arrow =>
            standardSliceCoverBaseFactorIndex (J := J) (U := U) T u K)
          (p' := fun K : (standardSliceCover (J := J) (U := U) T u).Arrow =>
            standardSliceCoverBaseFactorHom (J := J) (U := U) T u K)
          (w := fun K : (standardSliceCover (J := J) (U := U) T u).Arrow =>
            baseToStandardSlice_w_noId (J := J) (U := U) T u K)
          q u D.obj D.property K)

/-- Helper for Chap08 Lemma 8 13 2: the fixed-arrow full subcategory comparison induced by the
two projected covering families is an equivalence. -/
private noncomputable def standardSliceFixedDescentBaseFixedEquivalence
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {V : C} (T : J.Cover V) (u : V ⟶ U) :
    (compositeDescentFixedArrowProperty (J := J) (U := U) (p := q)
        (standardSliceCover (J := J) (U := U) T u)).FullSubcategory ≌
      (compositeBaseDescentFixedArrowProperty (J := J) (U := U) q T u).FullSubcategory := by
  let F := canonicalFiberPseudofunctor (q ⋙ Over.forget U)
  let E :
      F.DescentData
          (fun K : (standardSliceCover (J := J) (U := U) T u).Arrow => K.f.left) ≌
        F.DescentData (fun I : T.Arrow => I.f) :=
    Pseudofunctor.DescentData.pullFunctorEquivalence
      (F := F)
      (f := fun K : (standardSliceCover (J := J) (U := U) T u).Arrow => K.f.left)
      (f' := fun I : T.Arrow => I.f)
      (e := Iso.refl V)
      (α := fun I : T.Arrow => standardSliceCoverArrowOfBaseArrow (J := J) (U := U) T u I)
      (p' := fun I : T.Arrow => 𝟙 I.Y)
      (β := fun K : (standardSliceCover (J := J) (U := U) T u).Arrow =>
        standardSliceCoverBaseFactorIndex (J := J) (U := U) T u K)
      (q' := fun K : (standardSliceCover (J := J) (U := U) T u).Arrow =>
        standardSliceCoverBaseFactorHom (J := J) (U := U) T u K)
      (standardSliceToBase_w (J := J) (U := U) T u)
      (baseToStandardSlice_w (J := J) (U := U) T u)
  exact
    { functor := standardSliceFixedDescentToBaseFixedDescentFunctor (J := J) (U := U) q T u
      inverse := baseFixedDescentToStandardSliceFixedDescentFunctor (J := J) (U := U) q T u
      unitIso := NatIso.ofComponents
        (fun D =>
          ObjectProperty.isoMk
            (P := compositeDescentFixedArrowProperty (J := J) (U := U) (p := q)
              (standardSliceCover (J := J) (U := U) T u))
            (E.unitIso.app D.obj))
        (fun φ => by
          apply ObjectProperty.hom_ext
          change
            φ.hom ≫ E.unitIso.hom.app _ =
              E.unitIso.hom.app _ ≫ (E.functor ⋙ E.inverse).map φ.hom
          exact E.unitIso.hom.naturality φ.hom)
      counitIso := NatIso.ofComponents
        (fun D =>
          ObjectProperty.isoMk
            (P := compositeBaseDescentFixedArrowProperty (J := J) (U := U) q T u)
            (E.counitIso.app D.obj))
        (fun φ => by
          apply ObjectProperty.hom_ext
          change
            (E.inverse ⋙ E.functor).map φ.hom ≫ E.counitIso.hom.app _ =
              E.counitIso.hom.app _ ≫ φ.hom
          exact E.counitIso.hom.naturality φ.hom)
      functor_unitIso_comp := fun D => by
        apply ObjectProperty.hom_ext
        change
          E.functor.map (E.unitIso.hom.app D.obj) ≫
              E.counitIso.hom.app (E.functor.obj D.obj) =
            𝟙 (E.functor.obj D.obj)
        exact E.functor_unitIso_comp D.obj }

private theorem standardSliceFixedDescentToBaseFixedDescentFunctor_isEquivalence
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {V : C} (T : J.Cover V) (u : V ⟶ U) :
    (standardSliceFixedDescentToBaseFixedDescentFunctor (J := J) (U := U) q T u).IsEquivalence :=
by
  simpa [standardSliceFixedDescentBaseFixedEquivalence] using
    (standardSliceFixedDescentBaseFixedEquivalence (J := J) (U := U) q T u).isEquivalence_functor

/-- Helper for Chap08 Lemma 8 13 2: a composite-fiber object with fixed arrow `u` has
base-cover descent data whose local arrows are fixed by `u`. -/
private noncomputable def compositeFixedFiberToBaseFixedDescentFunctor
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {V : C} (T : J.Cover V) (u : V ⟶ U) :
    (compositeFiberFixedArrowProperty (U := U) q (Over.mk u)).FullSubcategory ⥤
      (compositeBaseDescentFixedArrowProperty (J := J) (U := U) q T u).FullSubcategory :=
  (compositeBaseDescentFixedArrowProperty (J := J) (U := U) q T u).lift
    ((compositeFiberFixedArrowProperty (U := U) q (Over.mk u)).ι ⋙
      ((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).toDescentData
        (fun I : T.Arrow ↦ I.f)))
    (fun X => by
      intro I
      change compositeFiberArrowToU (U := U) q
          (((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).map I.f.op.toLoc).toFunctor.obj
            X.obj) =
        I.f ≫ u
      rw [composite_pseudofunctor_map_obj_arrow_eq_comp (U := U) q
        (f := I.f) (a := X.obj)]
      change I.f ≫ compositeFiberArrowToU (U := U) q X.obj = I.f ≫ (Over.mk u).hom
      exact congrArg (fun a => I.f ≫ a) X.property)

/-- Helper for Chap08 Lemma 8 13 2: canonical descent from a fixed composite fiber over the
standard slice cover, followed by the fixed descent comparison to the base cover, is the canonical
base-cover descent functor. -/
private noncomputable def compositeFixedFiber_standardSlice_to_baseFixedDescentIso
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {V : C} (T : J.Cover V) (u : V ⟶ U) :
    (compositeFixedFiberToFixedDescentFunctor (J := J) (U := U) q
        (standardSliceCover (J := J) (U := U) T u) ⋙
      standardSliceFixedDescentToBaseFixedDescentFunctor (J := J) (U := U) q T u) ≅
      compositeFixedFiberToBaseFixedDescentFunctor (J := J) (U := U) q T u := by
  let F := canonicalFiberPseudofunctor (q ⋙ Over.forget U)
  let Ts := standardSliceCover (J := J) (U := U) T u
  let Φs := F.toDescentData (fun K : Ts.Arrow => K.f.left)
  let Φb := F.toDescentData (fun I : T.Arrow => I.f)
  let Pull := standardSliceToBaseDescentPullFunctor (J := J) (U := U) q T u
  let isoDesc : Φs ⋙ Pull ≅ Φb :=
    Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
        (F := F)
        (f := fun K : Ts.Arrow => K.f.left)
        (f' := fun I : T.Arrow => I.f)
        (p := 𝟙 V)
        (α := fun I : T.Arrow =>
          standardSliceCoverArrowOfBaseArrow (J := J) (U := U) T u I)
        (p' := fun I : T.Arrow => 𝟙 I.Y)
        (w := standardSliceToBase_w (J := J) (U := U) T u) ≪≫
      Functor.isoWhiskerRight (Cat.Hom.toNatIso (F.mapId _)) Φb ≪≫
      Functor.leftUnitor Φb
  refine NatIso.ofComponents (fun X => ?_) ?_
  · exact
      ObjectProperty.isoMk
        (P := compositeBaseDescentFixedArrowProperty (J := J) (U := U) q T u)
        (isoDesc.app X.obj)
  · intro X Y φ
    apply ObjectProperty.hom_ext
    change
      (Φs ⋙ Pull).map φ.hom ≫ isoDesc.hom.app Y.obj =
        isoDesc.hom.app X.obj ≫ Φb.map φ.hom
    exact isoDesc.hom.naturality φ.hom

/-- Helper for Chap08 Lemma 8 13 2: fixed composite descent over the standard slice cover is
effective, using stackness of `q` over the slice site and the slice-to-composite comparison. -/
private theorem compositeFixedFiberToFixedDescentFunctor_standardSlice_isEquivalence
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [IsStackOnSite (J.over U) q]
    [(q ⋙ Over.forget U).IsFibered]
    {V : C} (T : J.Cover V) (u : V ⟶ U) :
    (compositeFixedFiberToFixedDescentFunctor (J := J) (U := U) q
      (standardSliceCover (J := J) (U := U) T u)).IsEquivalence := by
  let A : Over U := Over.mk u
  let Ts := standardSliceCover (J := J) (U := U) T u
  let Ffib := qFiberToCompositeFixedFiberFunctor (U := U) q A
  let Ffix := compositeFixedFiberToFixedDescentFunctor (J := J) (U := U) q Ts
  let Φ := (canonicalFiberPseudofunctor q).toDescentData (fun K : Ts.Arrow => K.f)
  let Cfun := sliceDescentToCompositeFixedDescentFunctor (J := J) (U := U) q Ts
  have hFfib : Ffib.IsEquivalence :=
    qFiberToCompositeFixedFiberFunctor_isEquivalence (U := U) q A
  have hΦ : Φ.IsEquivalence :=
    standardSliceCover_arrow_toDescentData_isEquivalence (J := J) (U := U) q T u
  have hCfun : Cfun.IsEquivalence :=
    sliceDescentToCompositeFixedDescentFunctor_isEquivalence (J := J) (U := U) q Ts
  letI : Φ.IsEquivalence := hΦ
  letI : Cfun.IsEquivalence := hCfun
  have hright : (Φ ⋙ Cfun).IsEquivalence :=
    Functor.isEquivalence_trans Φ Cfun
  have hIso :
      Ffib ⋙ Ffix ≅ Φ ⋙ Cfun := by
    simpa [A, Ts, Ffib, Ffix, Φ, Cfun] using
      sliceCanonicalToComposite_fixedDescentIso (J := J) (U := U) q Ts
  have hleft : (Ffib ⋙ Ffix).IsEquivalence :=
    (Functor.isEquivalence_iff_of_iso hIso).2 hright
  letI : Ffib.IsEquivalence := hFfib
  letI : (Ffib ⋙ Ffix).IsEquivalence := hleft
  exact Functor.isEquivalence_of_comp_left Ffib Ffix

/-- Helper for Chap08 Lemma 8 13 2: the fixed glued-arrow component of a base-cover composite
descent functor is an equivalence. -/
private theorem compositeFixedFiberToBaseFixedDescentFunctor_isEquivalence
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [IsStackOnSite (J.over U) q]
    [(q ⋙ Over.forget U).IsFibered]
    {V : C} (T : J.Cover V) (u : V ⟶ U) :
    (compositeFixedFiberToBaseFixedDescentFunctor (J := J) (U := U) q T u).IsEquivalence := by
  let Ts := standardSliceCover (J := J) (U := U) T u
  let Fslice := compositeFixedFiberToFixedDescentFunctor (J := J) (U := U) q Ts
  let G := standardSliceFixedDescentToBaseFixedDescentFunctor (J := J) (U := U) q T u
  let Fbase := compositeFixedFiberToBaseFixedDescentFunctor (J := J) (U := U) q T u
  have hFslice : Fslice.IsEquivalence :=
    compositeFixedFiberToFixedDescentFunctor_standardSlice_isEquivalence (J := J) (U := U) q T u
  have hG : G.IsEquivalence :=
    standardSliceFixedDescentToBaseFixedDescentFunctor_isEquivalence (J := J) (U := U) q T u
  letI : Fslice.IsEquivalence := hFslice
  letI : G.IsEquivalence := hG
  have hcomp : (Fslice ⋙ G).IsEquivalence :=
    Functor.isEquivalence_trans Fslice G
  have hIso : Fslice ⋙ G ≅ Fbase := by
    simpa [Ts, Fslice, G, Fbase] using
      compositeFixedFiber_standardSlice_to_baseFixedDescentIso (J := J) (U := U) q T u
  exact (Functor.isEquivalence_iff_of_iso hIso).1 hcomp

/-- Helper for Chap08 Lemma 8 13 2: if every glued-arrow component of a base-cover descent
functor is an equivalence, then the whole base-cover descent functor is an equivalence. -/
private theorem compCover_toDescentData_isEquivalence_of_fixedComponents
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [(q ⋙ Over.forget U).IsFibered]
    {V : C} (T : J.Cover V)
    (hfixed : ∀ u : V ⟶ U,
      (compositeFixedFiberToBaseFixedDescentFunctor (J := J) (U := U) q T u).IsEquivalence) :
    ((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).toDescentData
      (fun I : T.Arrow ↦ I.f)).IsEquivalence := by
  let Φ :=
    (canonicalFiberPseudofunctor (q ⋙ Over.forget U)).toDescentData
      (fun I : T.Arrow ↦ I.f)
  have hFaithful : Φ.Faithful := by
    constructor
    intro X Y f g hfg
    let u : V ⟶ U := compositeFiberArrowToU (U := U) q X
    have huY : compositeFiberArrowToU (U := U) q Y = u := by
      exact (compositeFiberArrowToU_eq_of_hom (U := U) q f).symm
    let Xf : (compositeFiberFixedArrowProperty (U := U) q (Over.mk u)).FullSubcategory :=
      ⟨X, rfl⟩
    let Yf : (compositeFiberFixedArrowProperty (U := U) q (Over.mk u)).FullSubcategory :=
      ⟨Y, huY⟩
    let Ffix := compositeFixedFiberToBaseFixedDescentFunctor (J := J) (U := U) q T u
    let ff : Xf ⟶ Yf := ObjectProperty.homMk f
    let gg : Xf ⟶ Yf := ObjectProperty.homMk g
    have hfgFixed : Ffix.map ff = Ffix.map gg := by
      apply ObjectProperty.hom_ext
      exact hfg
    letI : Ffix.Faithful := (hfixed u).faithful
    have hfixedEq : ff = gg := Ffix.map_injective hfgFixed
    exact congrArg (fun k => k.hom) hfixedEq
  have hFull : Φ.Full := by
    constructor
    intro X Y φ
    let u : V ⟶ U := compositeFiberArrowToU (U := U) q X
    have huY : compositeFiberArrowToU (U := U) q Y = u := by
      exact (compCover_imageDescentHom_arrowToU_eq (J := J) (U := U) hU q T φ).symm
    let Xf : (compositeFiberFixedArrowProperty (U := U) q (Over.mk u)).FullSubcategory :=
      ⟨X, rfl⟩
    let Yf : (compositeFiberFixedArrowProperty (U := U) q (Over.mk u)).FullSubcategory :=
      ⟨Y, huY⟩
    let Ffix := compositeFixedFiberToBaseFixedDescentFunctor (J := J) (U := U) q T u
    let φf : Ffix.obj Xf ⟶ Ffix.obj Yf := ObjectProperty.homMk φ
    letI : Ffix.Full := (hfixed u).full
    refine ⟨(Ffix.preimage φf).hom, ?_⟩
    have hpre : Ffix.map (Ffix.preimage φf) = φf := Ffix.map_preimage φf
    exact congrArg (fun k => k.hom) hpre
  have hEss : Φ.EssSurj := by
    refine { mem_essImage := fun D => ?_ }
    rcases compDescentData_gluedArrowToU (J := J) (U := U) hU q T D with
      ⟨u, hu, _⟩
    let Df :
        (compositeBaseDescentFixedArrowProperty (J := J) (U := U) q T u).FullSubcategory :=
      ⟨D, fun I => (hu I).symm⟩
    let Ffix := compositeFixedFiberToBaseFixedDescentFunctor (J := J) (U := U) q T u
    letI : Ffix.EssSurj := (hfixed u).essSurj
    rcases Functor.EssSurj.mem_essImage (F := Ffix) Df with ⟨Xf, ⟨e⟩⟩
    let eUnder :=
      (compositeBaseDescentFixedArrowProperty (J := J) (U := U) q T u).ι.mapIso e
    refine ⟨Xf.obj, ⟨?_⟩⟩
    change (Ffix.obj Xf).obj ≅ Df.obj
    exact eUnder
  exact { faithful := hFaithful, full := hFull, essSurj := hEss }

/-- Helper for Chap08 Lemma 8 13 2: for a fixed base cover, descent for the composite
projection to `C` is effective. -/
private theorem compOverForget_cover_toDescentData_isEquivalence
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [IsStackOnSite (J.over U) q]
    [(q ⋙ Over.forget U).IsFibered]
    {V : C} (T : J.Cover V) :
    ((canonicalFiberPseudofunctor (q ⋙ Over.forget U)).toDescentData
      (fun I : T.Arrow ↦ I.f)).IsEquivalence := by
  exact
    compCover_toDescentData_isEquivalence_of_fixedComponents
      (J := J) (U := U) hU q T
      (fun u =>
        compositeFixedFiberToBaseFixedDescentFunctor_isEquivalence
          (J := J) (U := U) q T u)

/-- Helper for Chap08 Lemma 8 13 2: a localized stack remains a stack after composing its
projection with `Over.forget U`. -/
private theorem compOverForgetIsStackOnSite
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {S : Type*} [Category S] (q : S ⥤ Over U)
    [IsStackOnSite (J.over U) q] :
    IsStackOnSite J (q ⋙ Over.forget U) := by
  -- It remains to prove object-effectivity coverwise; the fixed-cover lemma isolates the
  -- inherited-topology transitivity frontier.
  rw [isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence]
  intro V T
  letI : (q ⋙ Over.forget U).IsFibered := compOverForget_isFibered (J := J) (U := U) q
  exact compOverForget_cover_toDescentData_isEquivalence (J := J) (U := U) hU q T

/-- Construction A on objects: a stack over the localized site `(C/U, J.over U)` defines a stack
over `(C, J)` by composing its projection with `Over.forget U`. -/
private abbrev localizedStackAsStackOver
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : StackOver (J.over U)) : StackOver J :=
  let p : X.S ⥤ C := X.p ⋙ Over.forget U
  letI : IsStackOnSite J p := by
    change IsStackOnSite J (X.p ⋙ Over.forget U)
    -- Compose localized stackness with the slice projection using the inherited-precoverage bridge.
    exact compOverForgetIsStackOnSite J U hU X.p
  ⟨FibredCategoryOver.ofFunctor p, by
    simpa [FibredCategoryOver.p, FibredCategoryOver.ofFunctor] using
      (inferInstance : IsStackOnSite J p)⟩

/-- Helper for Chap08 Lemma 8 13 2: Construction A has the composite projection
`X.p ⋙ Over.forget U`. -/
private theorem localizedStackAsStackOver_projection
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : StackOver (J.over U)) :
    (localizedStackAsStackOver J U hU X).p = X.p ⋙ Over.forget U := by
  -- Unfold just the object constructor; the projection field is the named composite functor.
  rfl

/-- The based functor over `C` underlying Construction A on the map to `C/U`. -/
private abbrev localizedStackToSliceBasedFunctor
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : StackOver (J.over U)) :
    (localizedStackAsStackOver J U hU X).toFibredCategoryOver.toBasedCategory ⥤ᵇ
      (sliceStackOver J U hU).toFibredCategoryOver.toBasedCategory where
  toFunctor := show X.S ⥤ Over U from X.p
  w := by
    rfl

private theorem localizedStackToSlice_preservesStronglyCartesian
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : StackOver (J.over U)) :
    BasedFunctor.PreservesStronglyCartesian
      (localizedStackToSliceBasedFunctor J U hU X) := by
  intro a b φ hφ
  simpa [localizedStackToSliceBasedFunctor, sliceStackOver, FibredCategoryOver.p,
      FibredCategoryOver.ofFunctor] using
    (inferInstance : IsFibredInGroupoids (Over.forget U)).isStronglyCartesian_map
      (X.p.map φ)

/-- Construction A on objects: the canonical morphism from the induced stack over `(C, J)` to the
representable stack `C/U`. -/
private abbrev localizedStackToSliceMorphism
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : StackOver (J.over U)) :
    FibredCategoryMor
      (localizedStackAsStackOver J U hU X).toFibredCategoryOver
      (sliceStackOver J U hU).toFibredCategoryOver :=
  FibredCategoryMor.ofBasedFunctor
    (localizedStackToSliceBasedFunctor J U hU X)
    (localizedStackToSlice_preservesStronglyCartesian J U hU X)

/-- Construction A on `1`-morphisms, forgetting that the source and target lie over `Over U` and
viewing the same functor as a morphism over `C`. -/
private abbrev localizedStackMapAsStackBasedFunctor
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : StackOver (J.over U)} (F : X ⟶ Y) :
    (localizedStackAsStackOver J U hU X).toFibredCategoryOver.toBasedCategory ⥤ᵇ
      (localizedStackAsStackOver J U hU Y).toFibredCategoryOver.toBasedCategory where
  toFunctor := show X.S ⥤ Y.S from (toBasedFunctor F).toFunctor
  w := by
    -- Compose the original equality over `Over U` with the slice forgetful functor.
    simpa [localizedStackAsStackOver, FibredCategoryOver.p, FibredCategoryOver.ofFunctor,
      Functor.assoc] using
      congrArg (fun q : X.S ⥤ Over U => q ⋙ Over.forget U) (toBasedFunctor F).w

private theorem localizedStackMapAsStack_preservesStronglyCartesian
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : StackOver (J.over U)} (F : X ⟶ Y) :
  BasedFunctor.PreservesStronglyCartesian
      (localizedStackMapAsStackBasedFunctor J U hU F) := by
  intro a b φ hφ
  -- First recover cartesianness over `Over U` from cartesianness after forgetting to `C`.
  have hφOver : X.p.IsStronglyCartesian (X.p.map φ) φ := by
    haveI : (X.p ⋙ Over.forget U).IsStronglyCartesian (X.p.map φ).left φ := by
      simpa [localizedStackAsStackOver, FibredCategoryOver.p, FibredCategoryOver.ofFunctor] using hφ
    exact Functor.isStronglyCartesian_of_comp_over_forget X.p
  -- The original morphism of localized stacks preserves cartesian arrows over `Over U`.
  have hF :
      Y.p.IsStronglyCartesian (Y.p.map ((toBasedFunctor F).map φ))
        ((toBasedFunctor F).map φ) := by
    exact FibredCategoryMor.map_stronglyCartesian (toFibredCategoryMor F) φ hφOver
  -- Compose that cartesian arrow with the cartesian slice projection.
  letI :
      Y.p.IsStronglyCartesian (Y.p.map ((toBasedFunctor F).map φ))
        ((toBasedFunctor F).map φ) := hF
  letI :
      (Over.forget U).IsStronglyCartesian
        ((Over.forget U).map (Y.p.map ((toBasedFunctor F).map φ)))
        (Y.p.map ((toBasedFunctor F).map φ)) :=
    (inferInstance : IsFibredInGroupoids (Over.forget U)).isStronglyCartesian_map
      (Y.p.map ((toBasedFunctor F).map φ))
  change (Y.p ⋙ Over.forget U).IsStronglyCartesian
    ((Y.p ⋙ Over.forget U).map ((toBasedFunctor F).map φ))
    ((toBasedFunctor F).map φ)
  exact Functor.isStronglyCartesian_map_comp Y.p (Over.forget U) ((toBasedFunctor F).map φ)

/-- Helper for Chap08 Lemma 8 13 2: composing a projection with another functor sends a hom-lift
to a hom-lift for the composite projection. -/
private theorem isHomLift_comp_of_isHomLift
    {D E S : Type*} [Category D] [Category E] [Category S]
    (p : S ⥤ D) (q : D ⥤ E)
    {a b : S} {R T : D} {f : R ⟶ T} {φ : a ⟶ b}
    (h : p.IsHomLift f φ) :
    (p ⋙ q).IsHomLift (q.map f) φ := by
  -- Normalize the two endpoint equalities carried by the source hom-lift and map its factorization
  -- through `q`.
  letI : p.IsHomLift f φ := h
  let ha := IsHomLift.domain_eq p f φ
  let hb := IsHomLift.codomain_eq p f φ
  refine IsHomLift.of_fac (p ⋙ q) (q.map f) φ (congrArg q.obj ha) (congrArg q.obj hb) ?_
  calc
    q.map f = q.map (eqToHom ha.symm ≫ p.map φ ≫ eqToHom hb) := by
      rw [IsHomLift.fac p f φ]
    _ = eqToHom (congrArg q.obj ha).symm ≫ (p ⋙ q).map φ ≫
        eqToHom (congrArg q.obj hb) := by
      simp [Functor.map_comp, CategoryTheory.eqToHom_map]

/-- Helper for Chap08 Lemma 8 13 2: the slice forgetful functor sends an identity arrow
in `Over U` to the corresponding identity arrow in the base category. -/
private theorem overForget_map_id (X : Over U) :
    (Over.forget U).map (𝟙 X) = 𝟙 X.left := by
  -- Record the base normal form used when transporting verticality through the slice projection.
  rfl

/-- Helper for Chap08 Lemma 8 13 2: forgetting a left-whiskered fibred-category `2`-cell gives
left whiskering of the underlying based natural transformation. -/
private theorem fibredCategoryMorTwoHom_whiskerLeft_hom_hom
    {X Y Z : FibredCategoryOver C} (F : X ⟶ Y) {G H : Y ⟶ Z}
    (η : G ⟶ H) :
    (F ◁ η).hom.hom =
      CategoryTheory.BasedCategory.whiskerLeft (FibredCategoryMor.toBasedFunctor F) η.hom.hom := by
  -- This is the defining normal form of left whiskering in the induced fibred-category owner.
  rfl

/-- Helper for Chap08 Lemma 8 13 2: forgetting a right-whiskered fibred-category `2`-cell gives
right whiskering of the underlying based natural transformation. -/
private theorem fibredCategoryMorTwoHom_whiskerRight_hom_hom
    {X Y Z : FibredCategoryOver C} {F G : X ⟶ Y} (η : F ⟶ G) (H : Y ⟶ Z) :
    (η ▷ H).hom.hom =
      CategoryTheory.BasedCategory.whiskerRight η.hom.hom (FibredCategoryMor.toBasedFunctor H) := by
  -- This is the defining normal form of right whiskering in the induced fibred-category owner.
  rfl

/-- Helper for Chap08 Lemma 8 13 2: based functors are equal when their underlying functors are
equal. -/
private theorem basedFunctor_eq_of_toFunctor_eq
    {X : BasedCategory C} {Y : BasedCategory C}
    {F G : X ⥤ᵇ Y} (h : F.toFunctor = G.toFunctor) : F = G := by
  -- The base-commutativity fields are propositions, so the structure equality reduces to the
  -- underlying functor equality.
  cases F
  cases G
  simpa [BasedFunctor.mk.injEq] using h

/-- Helper for Chap08 Lemma 8 13 2: the underlying functor of a composite stack morphism is the
composite of the underlying functors. -/
private theorem stackHom_comp_toFunctor
    {X Y Z : StackOver J} (F : X ⟶ Y) (G : Y ⟶ Z) :
    (toBasedFunctor (F ≫ G)).toFunctor =
      (toBasedFunctor F).toFunctor ⋙ (toBasedFunctor G).toFunctor := by
  rfl

/-- Helper for Chap08 Lemma 8 13 2: two based categories with the same carrier and category
instance are equal when their projection functors agree. -/
private theorem basedCategory_eq_of_p_eq {S' : Type*} [Category S']
    (A B : BasedCategory S')
    (hobj : A.obj = B.obj)
    (hcat : HEq A.category B.category)
    (hp : HEq A.p B.p) : A = B := by
  -- Destructure both based categories; once the carrier and category fields are identified, the
  -- projection-field equality determines the whole structure.
  cases A
  cases B
  cases hobj
  cases hcat
  cases hp
  rfl

/-- Helper for Chap08 Lemma 8 13 2: cancel a right-hand equality transport in a morphism
equation. -/
private theorem eq_of_comp_eqToHom
    {A B D : C} (f : A ⟶ B) (g : A ⟶ D) (h : B = D)
    (e : f ≫ eqToHom h = g) :
    f = g ≫ eqToHom h.symm := by
  -- Eliminate the endpoint identification, where the statement is just right identity.
  subst h
  simpa using e

/-- Helper for Chap08 Lemma 8 13 2: the underlying natural transformation of a vertical
composite of stack `2`-cells is the vertical composite of the underlying natural
transformations. -/
private theorem stackTwoHomToNatTrans_comp_app
    {X Y : StackOver J} {F G H : X ⟶ Y} (η : F ⟶ G) (θ : G ⟶ H) (a : X.S) :
    (stackTwoHomToNatTrans (η ≫ θ)).app a =
      (stackTwoHomToNatTrans η).app a ≫ (stackTwoHomToNatTrans θ).app a := by
  -- The stack hom-category is induced from the ambient fibred-category hom-category.
  rfl

/-- Helper for Chap08 Lemma 8 13 2: right whiskering a stack `2`-cell maps its underlying
natural transformation by the whiskering stack morphism. -/
private theorem stackTwoHomToNatTrans_whiskerRight_app
    {W X Y : StackOver J} {F G : W ⟶ X} (η : F ⟶ G) (H : X ⟶ Y) (a : W.S) :
    (stackTwoHomToNatTrans (η ▷ H)).app a =
      (toBasedFunctor H).toFunctor.map ((stackTwoHomToNatTrans η).app a) := by
  -- The induced strict `2`-category uses the ambient right whiskering componentwise.
  rfl

/-- Helper for Chap08 Lemma 8 13 2: left whiskering a stack `2`-cell evaluates the underlying
natural transformation at the image of the whiskering stack morphism. -/
private theorem stackTwoHomToNatTrans_whiskerLeft_app
    {W X Y : StackOver J} (H : W ⟶ X) {F G : X ⟶ Y} (η : F ⟶ G) (a : W.S) :
    (stackTwoHomToNatTrans (H ◁ η)).app a =
      (stackTwoHomToNatTrans η).app ((toBasedFunctor H).toFunctor.obj a) := by
  -- The induced strict `2`-category uses the ambient left whiskering componentwise.
  rfl

/-- Helper for Chap08 Lemma 8 13 2: left whiskering a slice `2`-cell evaluates the underlying
natural transformation at the image of the whiskering slice morphism. -/
private theorem sliceTwoHomToNatTrans_whiskerLeft_app
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y Z : SliceTwoCategory (sliceStackOver J U hU)}
    (F : X ⟶ Y) {G H : Y ⟶ Z} (η : G ⟶ H) (a : X.obj.S) :
    (sliceTwoHomToNatTrans J U hU (F ◁ η)).app a =
      (sliceTwoHomToNatTrans J U hU η).app ((toBasedFunctor F.hom).toFunctor.obj a) := by
  -- Strip the slice wrapper; the stack-level left-whiskering normal form is definitional.
  rfl

/-- Helper for Chap08 Lemma 8 13 2: right whiskering a slice `2`-cell maps the underlying
natural transformation by the whiskering slice morphism. -/
private theorem sliceTwoHomToNatTrans_whiskerRight_app
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y Z : SliceTwoCategory (sliceStackOver J U hU)}
    {F G : X ⟶ Y} (η : F ⟶ G) (H : Y ⟶ Z) (a : X.obj.S) :
    (sliceTwoHomToNatTrans J U hU (η ▷ H)).app a =
      (toBasedFunctor H.hom).toFunctor.map ((sliceTwoHomToNatTrans J U hU η).app a) := by
  -- Strip the slice wrapper; the stack-level right-whiskering normal form is definitional.
  rfl

/-- Helper for Chap08 Lemma 8 13 2: vertical composition of slice `2`-cells evaluates to
vertical composition of the underlying natural transformations. -/
private theorem sliceTwoHomToNatTrans_comp_app
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : SliceTwoCategory (sliceStackOver J U hU)} {F G H : X ⟶ Y}
    (η : F ⟶ G) (θ : G ⟶ H) (a : X.obj.S) :
    (sliceTwoHomToNatTrans J U hU (η ≫ θ)).app a =
      (sliceTwoHomToNatTrans J U hU η).app a ≫
        (sliceTwoHomToNatTrans J U hU θ).app a := by
  -- Slice vertical composition is inherited from the ambient stack hom-category.
  rfl

/-- Helper for Chap08 Lemma 8 13 2: an equality transport of slice morphisms evaluates to the
corresponding object equality transport on underlying natural transformations. -/
private theorem sliceTwoHomToNatTrans_eqToHom_app
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : SliceTwoCategory (sliceStackOver J U hU)} {F G : X ⟶ Y}
    (h : F = G) (a : X.obj.S) :
    (sliceTwoHomToNatTrans J U hU (eqToHom h : F ⟶ G)).app a =
      eqToHom
        (congrArg (fun H : X ⟶ Y => (toBasedFunctor H.hom).toFunctor.obj a) h) := by
  -- After identifying the two slice morphisms, the equality transport is the identity component.
  subst h
  rfl

/-- Helper for Chap08 Lemma 8 13 2: an equality transport of stack morphisms evaluates to the
corresponding object equality transport on underlying natural transformations. -/
private theorem stackTwoHomToNatTrans_eqToHom_app
    {X Y : StackOver J} {F G : X ⟶ Y} (h : F = G) (a : X.S) :
    (stackTwoHomToNatTrans (eqToHom h : F ⟶ G)).app a =
      eqToHom (congrArg (fun H : X ⟶ Y => (toBasedFunctor H).toFunctor.obj a) h) := by
  -- After identifying the two stack morphisms, the equality transport is the identity component.
  subst h
  rfl

/-- Helper for Chap08 Lemma 8 13 2: the underlying natural transformation of a slice `2`-cell is
vertical for the target map to the slice base. -/
private theorem sliceTwoHomToNatTrans_isHomLift_id
    {Z : StackOver J} {X Y : SliceTwoCategory Z} {F G : X ⟶ Y}
    (η : F ⟶ G) (a : X.obj.S) :
    (toBasedFunctor Y.hom).toFunctor.IsHomLift
      (𝟙 ((toBasedFunctor X.hom).toFunctor.obj a))
      ((stackTwoHomToNatTrans η.hom).app a) := by
  -- Use the slice `2`-cell equation, then cancel the target-side equality transport.
  refine IsHomLift.of_fac' (toBasedFunctor Y.hom).toFunctor _ _
    (congrArg (fun H : X.obj ⟶ Z => (toBasedFunctor H).toFunctor.obj a) F.comm)
    (congrArg (fun H : X.obj ⟶ Z => (toBasedFunctor H).toFunctor.obj a) G.comm) ?_
  have hη := congrArg
    (fun θ : (F.hom ≫ Y.hom) ⟶ X.hom => (stackTwoHomToNatTrans θ).app a) η.comm
  dsimp only at hη
  rw [stackTwoHomToNatTrans_comp_app, stackTwoHomToNatTrans_whiskerRight_app,
    stackTwoHomToNatTrans_eqToHom_app, stackTwoHomToNatTrans_eqToHom_app] at hη
  rw [Category.id_comp]
  exact
    eq_of_comp_eqToHom
      ((toBasedFunctor Y.hom).toFunctor.map ((stackTwoHomToNatTrans η.hom).app a))
      (eqToHom (congrArg (fun H : X.obj ⟶ Z => (toBasedFunctor H).toFunctor.obj a) F.comm))
      (congrArg (fun H : X.obj ⟶ Z => (toBasedFunctor H).toFunctor.obj a) G.comm)
      hη

private abbrev localizedStackMapAsStackMorphism
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : StackOver (J.over U)} (F : X ⟶ Y) :
    FibredCategoryMor
      (localizedStackAsStackOver J U hU X).toFibredCategoryOver
      (localizedStackAsStackOver J U hU Y).toFibredCategoryOver :=
  FibredCategoryMor.ofBasedFunctor
    (localizedStackMapAsStackBasedFunctor J U hU F)
    (localizedStackMapAsStack_preservesStronglyCartesian J U hU F)

private abbrev localizedStackMapAsStackTwoHom
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : StackOver (J.over U)} {F G : X ⟶ Y} (η : F ⟶ G) :
    localizedStackMapAsStackMorphism J U hU F ⟶
      localizedStackMapAsStackMorphism J U hU G :=
  let τ := stackTwoHomToNatTrans η
  ⟨ObjectProperty.homMk <|
      { toNatTrans := τ
        isHomLift' := by
          intro a
          -- The ambient `2`-cell is already vertical; unfold only the object wrapper so the
          -- verticality statement is expressed over the composite projection to `C`.
          have hOver :
              Y.p.IsHomLift (𝟙 (X.p.obj a)) (τ.app a) := by
            change Y.toFibredCategoryOver.p.IsHomLift (𝟙 (X.toFibredCategoryOver.p.obj a))
              ((stackTwoHomToFibredCategoryMorTwoHom η).hom.hom.app a)
            exact fibredCategoryMor_hom_isHomLift_id (stackTwoHomToFibredCategoryMorTwoHom η) a
          have hComp :
              (Y.p ⋙ Over.forget U).IsHomLift
                ((Over.forget U).map (𝟙 (X.p.obj a))) (τ.app a) :=
            isHomLift_comp_of_isHomLift Y.p (Over.forget U) hOver
          change (Y.p ⋙ Over.forget U).IsHomLift
            (𝟙 ((Over.forget U).obj (X.p.obj a))) (τ.app a)
          simpa only [overForget_map_id] using hComp },
    trivial⟩

/-- Helper for Chap08 Lemma 8 13 2: Construction A does not change the underlying natural
transformation of a stack `2`-cell. -/
private theorem localizedStackMapAsStackTwoHom_toNatTrans
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : StackOver (J.over U)} {F G : X ⟶ Y} (η : F ⟶ G) :
    ((localizedStackMapAsStackTwoHom J U hU η).hom.hom).toNatTrans =
      stackTwoHomToNatTrans η := by
  -- The wrapper only changes the base category spelling; its natural-transformation field is
  -- the original stack `2`-cell.
  rfl

/-- Helper for Chap08 Lemma 8 13 2: Construction A's wrapped stack `2`-cell has the same
component as the original localized-stack `2`-cell. -/
private theorem localizedStackMapAsStackTwoHom_toNatTrans_app
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : StackOver (J.over U)} {F G : X ⟶ Y} (η : F ⟶ G) (a : X.S) :
    ((localizedStackMapAsStackTwoHom J U hU η).hom.hom).toNatTrans.app a =
      (stackTwoHomToNatTrans η).app a := by
  -- Evaluate the stored natural-transformation equality at the chosen object.
  exact congrArg (fun τ ↦ τ.app a) (localizedStackMapAsStackTwoHom_toNatTrans J U hU η)

/-- Helper for Chap08 Lemma 8 13 2: after turning Construction A's wrapped `2`-cell into an
induced stack `2`-cell, its natural-transformation component is still the original localized
stack component. -/
private theorem localizedStackMapAsStack_homMk_toNatTrans_app
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : StackOver (J.over U)} {F G : X ⟶ Y} (η : F ⟶ G) (a : X.S) :
    (stackTwoHomToNatTrans
        (InducedCategory.Hom.homMk (localizedStackMapAsStackTwoHom J U hU η) :
          InducedCategory.Hom.ofFibredCategoryMor
              (localizedStackMapAsStackMorphism J U hU F) ⟶
            InducedCategory.Hom.ofFibredCategoryMor
              (localizedStackMapAsStackMorphism J U hU G))).app a =
      (stackTwoHomToNatTrans η).app a := by
  -- The induced-category wrapper stores the same fibred-category `2`-cell, so the previous
  -- component normal form applies directly.
  exact localizedStackMapAsStackTwoHom_toNatTrans_app J U hU η a

/-- Helper for Chap08 Lemma 8 13 2: Construction A's induced stack morphism has the original
underlying functor on total categories. -/
private theorem localizedStackMapAsStack_homMk_toFunctor
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : StackOver (J.over U)} (F : X ⟶ Y) :
    (toBasedFunctor
        (InducedCategory.Hom.ofFibredCategoryMor
          (localizedStackMapAsStackMorphism J U hU F))).toFunctor =
      (toBasedFunctor F).toFunctor := by
  -- The induced stack morphism only changes the ambient base spelling.
  rfl

/-- Helper for Chap08 Lemma 8 13 2: Construction A's wrapped left whisker has the expected
underlying natural-transformation component. -/
private theorem localizedStackMapAsStack_homMk_whiskerLeft_toNatTrans_app
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y Z : StackOver (J.over U)} (F : X ⟶ Y) {G H : Y ⟶ Z}
    (η : G ⟶ H) (a : X.S) :
    (stackTwoHomToNatTrans
        (InducedCategory.Hom.homMk (localizedStackMapAsStackTwoHom J U hU (F ◁ η)) :
          InducedCategory.Hom.ofFibredCategoryMor
              (localizedStackMapAsStackMorphism J U hU (F ≫ G)) ⟶
            InducedCategory.Hom.ofFibredCategoryMor
              (localizedStackMapAsStackMorphism J U hU (F ≫ H)))).app a =
      (stackTwoHomToNatTrans η).app ((toBasedFunctor F).toFunctor.obj a) := by
  -- Normalize the Construction A wrapper, then use the ambient stack left-whiskering formula.
  rw [localizedStackMapAsStack_homMk_toNatTrans_app,
    stackTwoHomToNatTrans_whiskerLeft_app]

/-- Helper for Chap08 Lemma 8 13 2: Construction A's wrapped right whisker has the expected
underlying natural-transformation component. -/
private theorem localizedStackMapAsStack_homMk_whiskerRight_toNatTrans_app
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y Z : StackOver (J.over U)} {F G : X ⟶ Y} (η : F ⟶ G)
    (H : Y ⟶ Z) (a : X.S) :
    (stackTwoHomToNatTrans
        (InducedCategory.Hom.homMk (localizedStackMapAsStackTwoHom J U hU (η ▷ H)) :
          InducedCategory.Hom.ofFibredCategoryMor
              (localizedStackMapAsStackMorphism J U hU (F ≫ H)) ⟶
            InducedCategory.Hom.ofFibredCategoryMor
              (localizedStackMapAsStackMorphism J U hU (G ≫ H)))).app a =
      (toBasedFunctor H).toFunctor.map ((stackTwoHomToNatTrans η).app a) := by
  -- Normalize the Construction A wrapper, then use the ambient stack right-whiskering formula.
  rw [localizedStackMapAsStack_homMk_toNatTrans_app,
    stackTwoHomToNatTrans_whiskerRight_app]

private abbrev localizedStackToSliceHom
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : StackOver (J.over U)) :
    localizedStackAsStackOver J U hU X ⟶
      sliceStackOver J U hU :=
  InducedCategory.Hom.ofFibredCategoryMor (localizedStackToSliceMorphism J U hU X)

/-- Helper for Chap08 Lemma 8 13 2: the map from Construction A to the representable slice
stack has underlying functor equal to the original localized-stack projection. -/
private theorem localizedStackToSliceHom_toFunctor
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : StackOver (J.over U)) :
    (toBasedFunctor (localizedStackToSliceHom J U hU X)).toFunctor = X.p := by
  -- Construction A stores `X.p` as the underlying functor of the based morphism to `C/U`.
  rfl

private theorem localizedStackToSlice_map_comm
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : StackOver (J.over U)} (F : X ⟶ Y) :
    InducedCategory.Hom.ofFibredCategoryMor (localizedStackMapAsStackMorphism J U hU F) ≫
      localizedStackToSliceHom J U hU Y =
      localizedStackToSliceHom J U hU X := by
  -- Peel off the stack and fibred-category wrappers until only the based-functor triangle remains.
  apply WideSubcategory.ext
  apply ObjectProperty.FullSubcategory.ext
  change localizedStackMapAsStackMorphism J U hU F ≫ localizedStackToSliceMorphism J U hU Y =
    localizedStackToSliceMorphism J U hU X
  apply WideSubcategory.ext
  apply ObjectProperty.FullSubcategory.ext
  change (localizedStackMapAsStackBasedFunctor J U hU F) ⋙
      (localizedStackToSliceBasedFunctor J U hU Y) =
    localizedStackToSliceBasedFunctor J U hU X
  -- The remaining equality is exactly the original morphism's base equation over `Over U`.
  refine basedFunctor_eq_of_toFunctor_eq ?_
  simpa [BasedFunctor.comp_toFunctor, localizedStackMapAsStackBasedFunctor,
    localizedStackToSliceBasedFunctor] using (toBasedFunctor F).w

/-- Helper for Chap08 Lemma 8 13 2: Construction A sends a localized stack `2`-cell to a
slice `2`-cell over the representable stack. -/
private theorem localizedStacksToSlice_map₂_comm
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : StackOver (J.over U)} {F G : X ⟶ Y} (η : F ⟶ G) :
  (InducedCategory.Hom.homMk (localizedStackMapAsStackTwoHom J U hU η) ▷
        localizedStackToSliceHom J U hU Y) ≫
      eqToHom (localizedStackToSlice_map_comm J U hU G) =
    eqToHom (localizedStackToSlice_map_comm J U hU F) := by
  -- Reduce the slice compatibility equality to the stored natural transformations; the remaining
  -- pointwise statement is the original verticality of `η` over `Over U`.
  apply stackTwoHom_eq_of_toNatTrans_eq
  apply NatTrans.ext
  funext a
  -- Expand the vertical composite, right whiskering, and equality transports to the component
  -- equality supplied by the original localized-stack two-cell.
  rw [stackTwoHomToNatTrans_comp_app, stackTwoHomToNatTrans_whiskerRight_app,
    stackTwoHomToNatTrans_eqToHom_app, stackTwoHomToNatTrans_eqToHom_app]
  -- TODO: bridge the wrapper component above to the original localized-stack component. A direct
  -- `rfl` comparison hits a universe/transport mismatch between `localizedStackAsStackOver` and
  -- the owner `StackOver (J.over U)` object type.
  rw [localizedStackMapAsStack_homMk_toNatTrans_app]
  -- Use the original verticality of `η` over `Y.p`, then identify the stored Construction A
  -- endpoints with the localized-stack endpoints.
  have hη : Y.p.IsHomLift (𝟙 (X.p.obj a)) ((stackTwoHomToNatTrans η).app a) := by
    change Y.toFibredCategoryOver.p.IsHomLift (𝟙 (X.toFibredCategoryOver.p.obj a))
      ((stackTwoHomToFibredCategoryMorTwoHom η).hom.hom.toNatTrans.app a)
    exact fibredCategoryMor_hom_isHomLift_id (stackTwoHomToFibredCategoryMorTwoHom η) a
  letI : Y.p.IsHomLift (𝟙 (X.p.obj a)) ((stackTwoHomToNatTrans η).app a) := hη
  change Y.p.map ((stackTwoHomToNatTrans η).app a) ≫ eqToHom _ = eqToHom _
  rw [IsHomLift.fac' Y.p (𝟙 (X.p.obj a)) ((stackTwoHomToNatTrans η).app a)]
  simp only [Category.id_comp, eqToHom_trans]

/-- Construction A of Lemma 8.13.2: a localized stack defines a stack over `(C, J)` equipped with
its canonical map to the representable stack `C/U`. -/
private def localizedStacksToSlicePreCore
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    StrictPseudofunctorPreCore
      (StackOver (J.over U))
      (SliceTwoCategory (sliceStackOver J U hU)) :=
  {
    obj := fun X ↦
      { obj := localizedStackAsStackOver J U hU X
        hom := localizedStackToSliceHom J U hU X }
    map := fun F ↦
      { hom := InducedCategory.Hom.ofFibredCategoryMor (localizedStackMapAsStackMorphism J U hU F)
        comm := localizedStackToSlice_map_comm J U hU F }
    map₂ := fun η ↦
      { hom := InducedCategory.Hom.homMk (localizedStackMapAsStackTwoHom J U hU η)
        comm := localizedStacksToSlice_map₂_comm J U hU η
      }
    map_id := by
      intro X
      -- The object and morphism wrappers are definitionally the identity construction here.
      rfl
    map_comp := by
      intro X Y Z F G
      -- Composition is inherited unchanged from the underlying morphisms of localized stacks.
      rfl
    map₂_id := by
      intro X Y F
      -- The induced two-cell is the identity natural transformation after unfolding the wrappers.
      rfl
    map₂_comp := by
      intro X Y F G H η θ
      -- Vertical composition is preserved definitionally by the induced two-cell wrapper.
      rfl
    map₂_whisker_left := by
      intro X Y Z F G H η
      -- Work directly with slice-level natural transformations so composition transports reduce
      -- through the slice comparison lemmas before touching the Construction A wrapper.
      apply sliceTwoHom_eq_of_toNatTrans_eq
      apply NatTrans.ext
      funext a
      rw [localizedStackMapAsStack_homMk_whiskerLeft_toNatTrans_app]
      rw [sliceTwoHomToNatTrans_comp_app, sliceTwoHomToNatTrans_comp_app,
        sliceTwoHomToNatTrans_whiskerLeft_app, sliceTwoHomToNatTrans_eqToHom_app,
        sliceTwoHomToNatTrans_eqToHom_app]
      rw [localizedStackMapAsStack_homMk_toNatTrans_app]
      change (stackTwoHomToNatTrans η).app ((toBasedFunctor F).obj a) =
        eqToHom _ ≫ (stackTwoHomToNatTrans η).app ((toBasedFunctor F).obj a) ≫ eqToHom _
      simp only [Category.id_comp, Category.comp_id, eqToHom_refl]
    map₂_whisker_right := by
      intro X Y Z F G H η
      -- Work directly with slice-level natural transformations so the strict-composition
      -- endpoint transports can be rewritten by the slice transport API.
      apply sliceTwoHom_eq_of_toNatTrans_eq
      apply NatTrans.ext
      funext a
      rw [localizedStackMapAsStack_homMk_whiskerRight_toNatTrans_app]
      -- Normalize the transported right-whisker component to the same underlying stack component.
      rw [sliceTwoHomToNatTrans_comp_app, sliceTwoHomToNatTrans_comp_app,
        sliceTwoHomToNatTrans_whiskerRight_app, sliceTwoHomToNatTrans_eqToHom_app,
        sliceTwoHomToNatTrans_eqToHom_app]
      rw [localizedStackMapAsStack_homMk_toNatTrans_app]
      change (toBasedFunctor η).map ((stackTwoHomToNatTrans H).app a) =
        eqToHom _ ≫ (toBasedFunctor η).map ((stackTwoHomToNatTrans H).app a) ≫ eqToHom _
      simp only [Category.id_comp, Category.comp_id, eqToHom_refl]
  }

/-- Construction A of Lemma 8.13.2: a localized stack defines a stack over `(C, J)` equipped with
its canonical map to the representable stack `C/U`. -/
noncomputable def localizedStacksToSlice
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    StrictPseudofunctor
      (StackOver (J.over U))
      (SliceTwoCategory (sliceStackOver J U hU)) :=
  StrictPseudofunctor.mk'' (localizedStacksToSlicePreCore J U hU)

/-- Helper for Chap08 Lemma 8 13 2: the projection of a slice object, after forgetting the
slice coordinate, is the ambient stack projection. -/
private theorem sliceProjectionForObject_comp_overForget
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : SliceTwoCategory (sliceStackOver J U hU)) :
    (toBasedFunctor X.hom).toFunctor ⋙ Over.forget U = X.obj.p := by
  -- Read the equality from the based-functor triangle defining the map to the representable
  -- slice stack, then unfold only the target projection of that representable stack.
  simpa [sliceStackOver, FibredCategoryOver.p, FibredCategoryOver.ofFunctor] using
    (toBasedFunctor X.hom).w

/-- Helper for Chap08 Lemma 8 13 2: stackness transports across equality of projection
functors. -/
private theorem isStackOnSite_of_projection_eq
    {D : Type*} [Category D] {p q : D ⥤ C}
    (h : p = q) [IsStackOnSite J p] :
    IsStackOnSite J q := by
  -- After identifying the two projection functors, the requested instance is the original one.
  cases h
  infer_instance

/-- Helper for Chap08 Lemma 8 13 2: the projection of a slice object is a stack after
forgetting the slice coordinate. -/
private theorem sliceObjectProjection_comp_overForget_isStackOnSite
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : SliceTwoCategory (sliceStackOver J U hU)) :
    IsStackOnSite J ((toBasedFunctor X.hom).toFunctor ⋙ Over.forget U) := by
  -- Transport the ambient stack structure of `X.obj.p` across the triangle defining `X.hom`.
  exact
    isStackOnSite_of_projection_eq (J := J)
      (h := (sliceProjectionForObject_comp_overForget J U hU X).symm)

/-- Helper for Chap08 Lemma 8 13 2: the projection determined by a slice object is a stack over
the localized slice site. -/
private theorem sliceObjectProjection_isStackOnSite
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : SliceTwoCategory (sliceStackOver J U hU)) :
    IsStackOnSite (J.over U) (toBasedFunctor X.hom).toFunctor := by
  -- The slice triangle first gives stackness of the composite projection over `C`.
  have hcomp :
      IsStackOnSite J ((toBasedFunctor X.hom).toFunctor ⋙ Over.forget U) :=
    sliceObjectProjection_comp_overForget_isStackOnSite J U hU X
  let p : X.obj.S ⥤ Over U := (toBasedFunctor X.hom).toFunctor
  change IsStackOnSite (J.over U) p
  have hcomp' : IsStackOnSite J (p ⋙ Over.forget U) := by
    simpa [p] using hcomp
  letI : IsStackOnSite J (p ⋙ Over.forget U) := hcomp'
  letI : (p ⋙ Over.forget U).IsFibered := hcomp'.toIsFibered
  letI : p.IsFibered := Functor.isFibered_of_comp_over_forget p
  rw [isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence]
  intro A T
  exact sliceCover_toDescentData_isEquivalence_of_comp (J := J) (U := U) hU p hcomp' T

/-- Construction B on objects: a stack over `(C, J)` with a map to `C/U` is viewed as a stack
over the localized site `(C/U, J.over U)` via that map. -/
private abbrev sliceObjectAsLocalizedStack
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : SliceTwoCategory (sliceStackOver J U hU)) :
    StackOver (J.over U) :=
  let p : X.obj.S ⥤ Over U := (toBasedFunctor X.hom).toFunctor
  letI : IsStackOnSite (J.over U) p := sliceObjectProjection_isStackOnSite J U hU X
  ⟨FibredCategoryOver.ofFunctor p, by
    simpa [FibredCategoryOver.p, FibredCategoryOver.ofFunctor] using
      (inferInstance : IsStackOnSite (J.over U) p)⟩

private abbrev sliceHomToLocalizedStackBasedFunctor
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : SliceTwoCategory (sliceStackOver J U hU)}
    (F : X ⟶ Y) :
    (sliceObjectAsLocalizedStack J U hU X).toFibredCategoryOver.toBasedCategory ⥤ᵇ
      (sliceObjectAsLocalizedStack J U hU Y).toFibredCategoryOver.toBasedCategory where
  toFunctor := show X.obj.S ⥤ Y.obj.S from (toBasedFunctor F.hom).toFunctor
  w := by
    -- The triangle relation in the slice category is exactly the base equality over `Over U`.
    exact congrArg (fun H => (toBasedFunctor H).toFunctor) F.comm

/-- Helper for Chap08 Lemma 8 13 2: the projection of a slice object, after forgetting the
slice coordinate, is the ambient stack projection. -/
private theorem sliceProjection_comp_overForget
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : SliceTwoCategory (sliceStackOver J U hU)) :
    (toBasedFunctor X.hom).toFunctor ⋙ Over.forget U = X.obj.p := by
  -- Reuse the forward projection normal form established before Construction B is packaged.
  exact sliceProjectionForObject_comp_overForget J U hU X

/-- Helper for Chap08 Lemma 8 13 2: Construction B remembers a projection whose composite with
`Over.forget U` is the ambient stack projection. -/
private theorem sliceObjectAsLocalizedStack_projection_comp_overForget
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : SliceTwoCategory (sliceStackOver J U hU)) :
    (sliceObjectAsLocalizedStack J U hU X).p ⋙ Over.forget U = X.obj.p := by
  -- Expose the projection field of Construction B and reuse the slice triangle for `X.hom`.
  change (toBasedFunctor X.hom).toFunctor ⋙ Over.forget U = X.obj.p
  exact sliceProjection_comp_overForget J U hU X

private theorem sliceHomToLocalizedStack_preservesStronglyCartesian
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : SliceTwoCategory (sliceStackOver J U hU)}
    (F : X ⟶ Y) :
  BasedFunctor.PreservesStronglyCartesian
      (sliceHomToLocalizedStackBasedFunctor J U hU F) := by
  intro a b φ hφ
  -- Name the two slice projections so the proof stays in a single normal form.
  let pX : X.obj.S ⥤ Over U := (toBasedFunctor X.hom).toFunctor
  let pY : Y.obj.S ⥤ Over U := (toBasedFunctor Y.hom).toFunctor
  have hbaseX : pX ⋙ Over.forget U = X.obj.p := by
    simpa [pX] using sliceProjection_comp_overForget J U hU X
  have hbaseY : pY ⋙ Over.forget U = Y.obj.p := by
    simpa [pY] using sliceProjection_comp_overForget J U hU Y
  -- First view the source cartesian arrow over `Over U`, then compose it with `Over.forget U`.
  have hφOver : pX.IsStronglyCartesian (pX.map φ) φ := by
    change pX.IsStronglyCartesian (pX.map φ) φ
    exact hφ
  have hφComp : (pX ⋙ Over.forget U).IsStronglyCartesian ((pX ⋙ Over.forget U).map φ) φ := by
    letI : pX.IsStronglyCartesian (pX.map φ) φ := hφOver
    letI : (Over.forget U).IsStronglyCartesian ((Over.forget U).map (pX.map φ))
        (pX.map φ) :=
      (inferInstance : IsFibredInGroupoids (Over.forget U)).isStronglyCartesian_map (pX.map φ)
    exact Functor.isStronglyCartesian_map_comp pX (Over.forget U) φ
  have hφAmbient : X.obj.p.IsStronglyCartesian (X.obj.p.map φ) φ := by
    rw [← hbaseX]
    exact hφComp
  -- The ambient stack morphism preserves cartesian arrows over `C`.
  have hMap : Y.obj.p.IsStronglyCartesian
      (Y.obj.p.map ((toBasedFunctor F.hom).toFunctor.map φ))
      ((toBasedFunctor F.hom).toFunctor.map φ) :=
    FibredCategoryMor.map_stronglyCartesian (toFibredCategoryMor F.hom) φ hφAmbient
  -- Rewrite the result back along the target slice triangle and recover cartesianness over
  -- `Over U`.
  have hTargetComp : (pY ⋙ Over.forget U).IsStronglyCartesian
      ((pY ⋙ Over.forget U).map ((toBasedFunctor F.hom).toFunctor.map φ))
      ((toBasedFunctor F.hom).toFunctor.map φ) := by
    rw [hbaseY]
    exact hMap
  letI : (pY ⋙ Over.forget U).IsStronglyCartesian
      (pY.map ((toBasedFunctor F.hom).toFunctor.map φ)).left
      ((toBasedFunctor F.hom).toFunctor.map φ) := by
    simpa only [Functor.comp_map, Over.forget_map] using hTargetComp
  change pY.IsStronglyCartesian (pY.map ((toBasedFunctor F.hom).toFunctor.map φ))
    ((toBasedFunctor F.hom).toFunctor.map φ)
  exact Functor.isStronglyCartesian_of_comp_over_forget pY

/-- Construction B on `1`-morphisms: a triangle over `C/U` induces a morphism over the localized
site `(C/U, J.over U)`. -/
private abbrev sliceHomToLocalizedStackMorphism
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : SliceTwoCategory (sliceStackOver J U hU)}
    (F : X ⟶ Y) :
    FibredCategoryMor
      (sliceObjectAsLocalizedStack J U hU X).toFibredCategoryOver
      (sliceObjectAsLocalizedStack J U hU Y).toFibredCategoryOver :=
  FibredCategoryMor.ofBasedFunctor
    (sliceHomToLocalizedStackBasedFunctor J U hU F)
    (sliceHomToLocalizedStack_preservesStronglyCartesian J U hU F)

private abbrev sliceHomToLocalizedStackTwoHom
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : SliceTwoCategory (sliceStackOver J U hU)}
    {F G : X ⟶ Y} (η : F ⟶ G) :
    sliceHomToLocalizedStackMorphism J U hU F ⟶
      sliceHomToLocalizedStackMorphism J U hU G :=
  let τ := sliceTwoHomToNatTrans J U hU η
  ⟨ObjectProperty.homMk <|
      { toNatTrans := τ
        isHomLift' := by
          intro a
          -- The slice `2`-cell equation makes the component vertical for the induced projection.
          exact sliceTwoHomToNatTrans_isHomLift_id J η a },
    trivial⟩

/-- Helper for Chap08 Lemma 8 13 2: Construction B does not change the underlying natural
transformation of a slice `2`-cell. -/
private theorem sliceHomToLocalizedStackTwoHom_toNatTrans
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : SliceTwoCategory (sliceStackOver J U hU)}
    {F G : X ⟶ Y} (η : F ⟶ G) :
    ((sliceHomToLocalizedStackTwoHom J U hU η).hom.hom).toNatTrans =
      sliceTwoHomToNatTrans J U hU η := by
  -- The localized wrapper stores exactly the slice `2`-cell's underlying natural
  -- transformation.
  rfl

/-- Helper for Chap08 Lemma 8 13 2: Construction B's wrapped slice `2`-cell has the same
component as the original slice `2`-cell. -/
private theorem sliceHomToLocalizedStackTwoHom_toNatTrans_app
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : SliceTwoCategory (sliceStackOver J U hU)}
    {F G : X ⟶ Y} (η : F ⟶ G) (a : X.obj.S) :
    ((sliceHomToLocalizedStackTwoHom J U hU η).hom.hom).toNatTrans.app a =
      (sliceTwoHomToNatTrans J U hU η).app a := by
  -- Evaluate the wrapper's stored natural-transformation equality componentwise.
  exact congrArg (fun τ ↦ τ.app a) (sliceHomToLocalizedStackTwoHom_toNatTrans J U hU η)

/-- Helper for Chap08 Lemma 8 13 2: after turning Construction B's wrapped `2`-cell into an
induced stack `2`-cell, its natural-transformation component is still the original slice
component. -/
private theorem sliceHomToLocalizedStack_homMk_toNatTrans_app
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : SliceTwoCategory (sliceStackOver J U hU)}
    {F G : X ⟶ Y} (η : F ⟶ G) (a : X.obj.S) :
    (stackTwoHomToNatTrans
        (InducedCategory.Hom.homMk (sliceHomToLocalizedStackTwoHom J U hU η) :
          InducedCategory.Hom.ofFibredCategoryMor
              (sliceHomToLocalizedStackMorphism J U hU F) ⟶
            InducedCategory.Hom.ofFibredCategoryMor
              (sliceHomToLocalizedStackMorphism J U hU G))).app a =
      (sliceTwoHomToNatTrans J U hU η).app a := by
  -- The induced-category wrapper stores the same fibred-category `2`-cell, so the previous
  -- component normal form applies directly.
  exact sliceHomToLocalizedStackTwoHom_toNatTrans_app J U hU η a

/-- Helper for Chap08 Lemma 8 13 2: Construction B's induced stack morphism has the original
underlying functor on total categories. -/
private theorem sliceHomToLocalizedStack_homMk_toFunctor
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : SliceTwoCategory (sliceStackOver J U hU)} (F : X ⟶ Y) :
    (toBasedFunctor
        (InducedCategory.Hom.ofFibredCategoryMor
          (sliceHomToLocalizedStackMorphism J U hU F))).toFunctor =
      (toBasedFunctor F.hom).toFunctor := by
  -- The induced stack morphism only changes the ambient site spelling.
  rfl

/-- Helper for Chap08 Lemma 8 13 2: Construction B's wrapped left whisker has the expected
underlying natural-transformation component. -/
private theorem sliceHomToLocalizedStack_homMk_whiskerLeft_toNatTrans_app
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y Z : SliceTwoCategory (sliceStackOver J U hU)}
    (F : X ⟶ Y) {G H : Y ⟶ Z} (η : G ⟶ H) (a : X.obj.S) :
    (stackTwoHomToNatTrans
        (InducedCategory.Hom.homMk (sliceHomToLocalizedStackTwoHom J U hU (F ◁ η)) :
          InducedCategory.Hom.ofFibredCategoryMor
              (sliceHomToLocalizedStackMorphism J U hU (F ≫ G)) ⟶
            InducedCategory.Hom.ofFibredCategoryMor
              (sliceHomToLocalizedStackMorphism J U hU (F ≫ H)))).app a =
      (sliceTwoHomToNatTrans J U hU η).app
        ((toBasedFunctor F.hom).toFunctor.obj a) := by
  -- Normalize the Construction B wrapper, then use the slice left-whiskering formula.
  rw [sliceHomToLocalizedStack_homMk_toNatTrans_app,
    sliceTwoHomToNatTrans_whiskerLeft_app]

/-- Helper for Chap08 Lemma 8 13 2: Construction B's wrapped right whisker has the expected
underlying natural-transformation component. -/
private theorem sliceHomToLocalizedStack_homMk_whiskerRight_toNatTrans_app
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y Z : SliceTwoCategory (sliceStackOver J U hU)}
    {F G : X ⟶ Y} (η : F ⟶ G) (H : Y ⟶ Z) (a : X.obj.S) :
    (stackTwoHomToNatTrans
        (InducedCategory.Hom.homMk (sliceHomToLocalizedStackTwoHom J U hU (η ▷ H)) :
          InducedCategory.Hom.ofFibredCategoryMor
              (sliceHomToLocalizedStackMorphism J U hU (F ≫ H)) ⟶
            InducedCategory.Hom.ofFibredCategoryMor
              (sliceHomToLocalizedStackMorphism J U hU (G ≫ H)))).app a =
      (toBasedFunctor H.hom).toFunctor.map
        ((sliceTwoHomToNatTrans J U hU η).app a) := by
  -- Normalize the Construction B wrapper, then use the slice right-whiskering formula.
  rw [sliceHomToLocalizedStack_homMk_toNatTrans_app,
    sliceTwoHomToNatTrans_whiskerRight_app]

/-- Construction B of Lemma 8.13.2: a stack over `(C, J)` equipped with a map to `C/U` defines a
stack over the localized site `(C/U, J.over U)`. -/
private def sliceToLocalizedStacksPreCore
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    StrictPseudofunctorPreCore
      (SliceTwoCategory (sliceStackOver J U hU))
      (StackOver (J.over U)) :=
  {
    obj := fun X ↦ sliceObjectAsLocalizedStack J U hU X
    map := fun F ↦
      InducedCategory.Hom.ofFibredCategoryMor (sliceHomToLocalizedStackMorphism J U hU F)
    map₂ := fun η ↦
      InducedCategory.Hom.homMk (sliceHomToLocalizedStackTwoHom J U hU η)
    map_id := by
      intro X
      -- The localized morphism wrapper does not change the identity morphism data.
      rfl
    map_comp := by
      intro X Y Z F G
      -- The localized construction keeps the underlying slice morphism composition unchanged.
      rfl
    map₂_id := by
      intro X Y F
      -- The two-cell wrapper preserves identity two-cells definitionally.
      rfl
    map₂_comp := by
      intro X Y F G H η θ
      -- Vertical composition is inherited from the original slice two-cell wrapper.
      rfl
    map₂_whisker_left := by
      intro X Y Z F G H η
      -- Compare stack `2`-cells by their underlying natural transformations; the wrapper lemma
      -- removes the Construction B packaging from the left-whiskered side.
      apply stackTwoHom_eq_of_toNatTrans_eq
      apply NatTrans.ext
      funext a
      rw [sliceHomToLocalizedStack_homMk_whiskerLeft_toNatTrans_app]
      -- Normalize the transported left-whisker component to the same slice natural transformation.
      rw [stackTwoHomToNatTrans_comp_app, stackTwoHomToNatTrans_comp_app,
        stackTwoHomToNatTrans_whiskerLeft_app, stackTwoHomToNatTrans_eqToHom_app,
        stackTwoHomToNatTrans_eqToHom_app]
      rw [sliceHomToLocalizedStack_homMk_toNatTrans_app]
      change (sliceTwoHomToNatTrans J U hU η).app ((toBasedFunctor F.hom).obj a) =
        eqToHom _ ≫ (sliceTwoHomToNatTrans J U hU η).app ((toBasedFunctor F.hom).obj a) ≫
          eqToHom _
      simp only [Category.id_comp, Category.comp_id, eqToHom_refl]
    map₂_whisker_right := by
      intro X Y Z F G H η
      -- Compare stack `2`-cells by their underlying natural transformations; the wrapper lemma
      -- removes the Construction B packaging from the right-whiskered side.
      apply stackTwoHom_eq_of_toNatTrans_eq
      apply NatTrans.ext
      funext a
      rw [sliceHomToLocalizedStack_homMk_whiskerRight_toNatTrans_app]
      -- Normalize the transported right-whisker component to the same mapped slice component.
      rw [stackTwoHomToNatTrans_comp_app, stackTwoHomToNatTrans_comp_app,
        stackTwoHomToNatTrans_whiskerRight_app, stackTwoHomToNatTrans_eqToHom_app,
        stackTwoHomToNatTrans_eqToHom_app]
      rw [sliceHomToLocalizedStack_homMk_toNatTrans_app]
      change (toBasedFunctor η.hom).map ((sliceTwoHomToNatTrans J U hU H).app a) =
        eqToHom _ ≫ (toBasedFunctor η.hom).map ((sliceTwoHomToNatTrans J U hU H).app a) ≫
          eqToHom _
      simp only [Category.id_comp, Category.comp_id, eqToHom_refl]
  }

/-- Construction B of Lemma 8.13.2: a stack over `(C, J)` equipped with a map to `C/U` defines a
stack over the localized site `(C/U, J.over U)`. -/
noncomputable def sliceToLocalizedStacks
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    StrictPseudofunctor
      (SliceTwoCategory (sliceStackOver J U hU))
      (StackOver (J.over U)) :=
  StrictPseudofunctor.mk'' (sliceToLocalizedStacksPreCore J U hU)

/-- Construction A followed by Construction B is the identity on the strict `2`-category of
stacks over the localized site `(C/U, J.over U)` on objects. -/
@[simp] private theorem sliceToLocalizedStacks_obj_localizedStacksToSlice_obj
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    ∀ X : StackOver (J.over U),
      (sliceToLocalizedStacks J U hU).obj ((localizedStacksToSlice J U hU).obj X) = X := by
  intro X
  -- Construction A then B returns the original localized projection definitionally.
  rfl

/-- Construction A followed by Construction B is the identity on the strict `2`-category of
stacks over the localized site `(C/U, J.over U)` on `1`-morphisms. -/
@[simp] private theorem sliceToLocalizedStacks_map_localizedStacksToSlice_map
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    ∀ ⦃X Y : StackOver (J.over U)⦄ (F : X ⟶ Y),
      HEq ((sliceToLocalizedStacks J U hU).map ((localizedStacksToSlice J U hU).map F)) F := by
  intro X Y F
  -- Construction A changes only the ambient base spelling, and Construction B recovers the same
  -- localized morphism data.
  rfl

/-- Construction A followed by Construction B is the identity on the strict `2`-category of
stacks over the localized site `(C/U, J.over U)` on `2`-morphisms. -/
@[simp] private theorem sliceToLocalizedStacks_map₂_localizedStacksToSlice_map₂
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    ∀ ⦃X Y : StackOver (J.over U)⦄ {F G : X ⟶ Y} (η : F ⟶ G),
      HEq ((sliceToLocalizedStacks J U hU).map₂ ((localizedStacksToSlice J U hU).map₂ η)) η := by
  intro X Y F G η
  -- Strip the stack and fibred-category wrappers before using the definitional equality of the
  -- underlying based natural transformation.
  apply heq_of_eq
  apply stackTwoHom_eq_of_fibredCategoryMorTwoHom_eq
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  rfl

/-- Helper for Chap08 Lemma 8 13 2: the object component of Construction B followed by
Construction A is the original ambient stack object. -/
private theorem localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_obj
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : SliceTwoCategory (sliceStackOver J U hU)) :
    ((localizedStacksToSlice J U hU).obj ((sliceToLocalizedStacks J U hU).obj X)).obj =
      X.obj := by
  -- Unfold the strict-functor object wrappers only far enough to expose the based category
  -- determined by Construction B's projection, then use the slice triangle.
  apply ObjectProperty.FullSubcategory.ext
  apply ObjectProperty.FullSubcategory.ext
  dsimp [localizedStacksToSlice, sliceToLocalizedStacks, localizedStacksToSlicePreCore,
    sliceToLocalizedStacksPreCore]
  refine basedCategory_eq_of_p_eq _ _ rfl (HEq.refl _) ?_
  exact heq_of_eq (sliceObjectAsLocalizedStack_projection_comp_overForget J U hU X)

/-- Helper for Chap08 Lemma 8 13 2: equality transport between stack objects acts on total
category objects by the corresponding type cast. -/
private theorem stackOver_eqToHom_toFunctor_obj
    {X Y : StackOver J} (h : X = Y) (a : X.S) :
    (toBasedFunctor (eqToHom h : X ⟶ Y)).toFunctor.obj a =
      cast (congrArg ObjectProperty.FullSubcategory.S h) a := by
  cases h
  rfl

/-- Helper for Chap08 Lemma 8 13 2: equality transport between stack objects acts as the
identity on total-category morphisms, up to the endpoint transports. -/
private theorem stackOver_eqToHom_toFunctor_map_heq
    {X Y : StackOver J} (h : X = Y) {a b : X.S} (f : a ⟶ b) :
    (toBasedFunctor (eqToHom h : X ⟶ Y)).toFunctor.map f ≍ f := by
  cases h
  rfl

/-- Helper for Chap08 Lemma 8 13 2: the object transport used in the Construction B/A object
roundtrip is identity on the underlying total-category objects. -/
private theorem localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_eqToHom_obj
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : SliceTwoCategory (sliceStackOver J U hU))
    (a : ((localizedStacksToSlice J U hU).obj
      ((sliceToLocalizedStacks J U hU).obj X)).obj.S) :
    (toBasedFunctor
      (eqToHom (localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_obj J U hU X) :
        ((localizedStacksToSlice J U hU).obj
          ((sliceToLocalizedStacks J U hU).obj X)).obj ⟶ X.obj)).toFunctor.obj a = a := by
  rw [stackOver_eqToHom_toFunctor_obj]
  rfl

/-- Helper for Chap08 Lemma 8 13 2: the object transport used in the Construction B/A object
roundtrip is the identity functor on the underlying total category. -/
private theorem localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_eqToHom_toFunctor
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : SliceTwoCategory (sliceStackOver J U hU)) :
    (toBasedFunctor
      (eqToHom (localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_obj J U hU X) :
        ((localizedStacksToSlice J U hU).obj
          ((sliceToLocalizedStacks J U hU).obj X)).obj ⟶ X.obj)).toFunctor =
      𝟭 (((localizedStacksToSlice J U hU).obj
        ((sliceToLocalizedStacks J U hU).obj X)).obj.S) := by
  apply Functor.hext
  · intro a
    rw [localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_eqToHom_obj]
    rfl
  · intro a b f
    exact stackOver_eqToHom_toFunctor_map_heq
      (J := J) (localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_obj J U hU X) f

/-- Helper for Chap08 Lemma 8 13 2: the inverse object transport used in the Construction B/A
object roundtrip is the identity functor on the original total category. -/
private theorem localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_eqToHom_symm_toFunctor
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : SliceTwoCategory (sliceStackOver J U hU)) :
    (toBasedFunctor
      (eqToHom (localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_obj J U hU X).symm :
        X.obj ⟶
          ((localizedStacksToSlice J U hU).obj
            ((sliceToLocalizedStacks J U hU).obj X)).obj)).toFunctor =
      𝟭 X.obj.S := by
  apply Functor.hext
  · intro a
    rw [stackOver_eqToHom_toFunctor_obj]
    rfl
  · intro a b f
    exact stackOver_eqToHom_toFunctor_map_heq
      (J := J) (localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_obj J U hU X).symm f

/-- Construction B followed by Construction A is the identity on the slice strict `2`-category of
stacks over `(C, J)` above the representable stack `C/U` on objects. -/
@[simp] private theorem localizedStacksToSlice_obj_sliceToLocalizedStacks_obj
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
  ∀ X : SliceTwoCategory (sliceStackOver J U hU),
      (localizedStacksToSlice J U hU).obj ((sliceToLocalizedStacks J U hU).obj X) = X := by
  intro X
  -- The object field is the original ambient stack: after unfolding the strict functor wrappers,
  -- the only remaining data is the projection identity of Construction B.
  apply SliceTwoCategory.ext
  · exact localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_obj J U hU X
  · -- Converting the heterogeneous hom-field goal to an ordinary equality gives the precise
    -- conjugation normal form needed for the remaining transport proof.
    let hobj := localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_obj J U hU X
    rw [← conj_eqToHom_iff_heq' _ _ hobj rfl]
    -- Peel off the slice and stack wrappers; Construction A stores exactly the original
    -- slice-coordinate based functor after the ambient object transport.
    apply WideSubcategory.ext
    apply ObjectProperty.FullSubcategory.ext
    change localizedStackToSliceMorphism J U hU (sliceObjectAsLocalizedStack J U hU X) =
      toFibredCategoryMor (eqToHom hobj ≫ X.hom)
    apply WideSubcategory.ext
    apply ObjectProperty.FullSubcategory.ext
    refine basedFunctor_eq_of_toFunctor_eq ?_
    change (toBasedFunctor X.hom).toFunctor =
      (toBasedFunctor
        (eqToHom hobj :
          ((localizedStacksToSlice J U hU).obj
            ((sliceToLocalizedStacks J U hU).obj X)).obj ⟶ X.obj)).toFunctor ⋙
        (toBasedFunctor X.hom).toFunctor
    rw [localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_eqToHom_toFunctor]
    rfl

/-- Helper for Chap08 Lemma 8 13 2: the hom type after Construction B followed by
Construction A is identified by the object roundtrip. -/
private theorem localizedStacksToSlice_roundtrip_hom_type_eq
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X Y : SliceTwoCategory (sliceStackOver J U hU)) :
    (((localizedStacksToSlice J U hU).obj ((sliceToLocalizedStacks J U hU).obj X)) ⟶
      ((localizedStacksToSlice J U hU).obj ((sliceToLocalizedStacks J U hU).obj Y))) =
      (X ⟶ Y) := by
  -- Rewrite both endpoints through the object roundtrip so dependent hom transport has a named
  -- normal form for the later map roundtrip proof.
  rw [localizedStacksToSlice_obj_sliceToLocalizedStacks_obj J U hU X,
    localizedStacksToSlice_obj_sliceToLocalizedStacks_obj J U hU Y]

/-- Helper for Chap08 Lemma 8 13 2: the object component of the slice roundtrip equality is the
separately named object equality. -/
private theorem localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_congr_obj
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : SliceTwoCategory (sliceStackOver J U hU)) :
    congrArg SliceTwoCategory.obj
        (localizedStacksToSlice_obj_sliceToLocalizedStacks_obj J U hU X) =
      localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_obj J U hU X := by
  apply Subsingleton.elim

/-- Helper for Chap08 Lemma 8 13 2: the inverse object component of the slice roundtrip equality
is the inverse of the separately named object equality. -/
private theorem localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_congr_obj_symm
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : SliceTwoCategory (sliceStackOver J U hU)) :
    congrArg SliceTwoCategory.obj
        (localizedStacksToSlice_obj_sliceToLocalizedStacks_obj J U hU X).symm =
      (localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_obj J U hU X).symm := by
  apply Subsingleton.elim

/-- Helper for Chap08 Lemma 8 13 2: the slice-object equality transport from the Construction
B/A object roundtrip has identity underlying functor on total categories. -/
private theorem localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_slice_eqToHom_hom_toFunctor
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : SliceTwoCategory (sliceStackOver J U hU)) :
    (toBasedFunctor
      (eqToHom (localizedStacksToSlice_obj_sliceToLocalizedStacks_obj J U hU X) :
        (localizedStacksToSlice J U hU).obj
          ((sliceToLocalizedStacks J U hU).obj X) ⟶ X).hom).toFunctor =
      𝟭 (((localizedStacksToSlice J U hU).obj
        ((sliceToLocalizedStacks J U hU).obj X)).obj.S) := by
  rw [sliceObject_eqToHom_hom]
  rw [localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_congr_obj]
  exact localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_eqToHom_toFunctor J U hU X

/-- Helper for Chap08 Lemma 8 13 2: the inverse slice-object equality transport from the
Construction B/A object roundtrip has identity underlying functor on total categories. -/
private theorem localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_slice_eqToHom_symm_hom_toFunctor
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : SliceTwoCategory (sliceStackOver J U hU)) :
    (toBasedFunctor
      (eqToHom (localizedStacksToSlice_obj_sliceToLocalizedStacks_obj J U hU X).symm :
        X ⟶
          (localizedStacksToSlice J U hU).obj
            ((sliceToLocalizedStacks J U hU).obj X)).hom).toFunctor =
      𝟭 X.obj.S := by
  rw [sliceObject_eqToHom_hom]
  rw [localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_congr_obj_symm]
  exact localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_eqToHom_symm_toFunctor J U hU X

/-- Helper for Chap08 Lemma 8 13 2: Construction B followed by Construction A sends a
`1`-morphism to its conjugate by the object roundtrip transports. -/
private theorem localizedStacksToSlice_map_sliceToLocalizedStacks_map_conj
    (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : SliceTwoCategory (sliceStackOver J U hU)} (F : X ⟶ Y) :
    let hx := localizedStacksToSlice_obj_sliceToLocalizedStacks_obj J U hU X
    let hy := localizedStacksToSlice_obj_sliceToLocalizedStacks_obj J U hU Y
    (localizedStacksToSlice J U hU).map ((sliceToLocalizedStacks J U hU).map F) =
      eqToHom hx ≫ F ≫ eqToHom hy.symm := by
  intro hx hy
  apply SliceTwoCategory.Hom.ext
  rw [sliceHom_comp_hom, sliceHom_comp_hom, sliceObject_eqToHom_hom hx,
    sliceObject_eqToHom_hom hy.symm]
  rw [localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_congr_obj J U hU X,
    localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_congr_obj_symm J U hU Y]
  apply WideSubcategory.ext
  apply ObjectProperty.FullSubcategory.ext
  apply WideSubcategory.ext
  apply ObjectProperty.FullSubcategory.ext
  refine basedFunctor_eq_of_toFunctor_eq ?_
  change (toBasedFunctor
      (InducedCategory.Hom.ofFibredCategoryMor
        (localizedStackMapAsStackMorphism J U hU
          ((sliceToLocalizedStacks J U hU).map F)))).toFunctor =
    (toBasedFunctor
      (eqToHom (localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_obj J U hU X) ≫
        F.hom ≫
        eqToHom (localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_obj J U hU Y).symm)).toFunctor
  rw [localizedStackMapAsStack_homMk_toFunctor]
  change (toBasedFunctor
      (InducedCategory.Hom.ofFibredCategoryMor
        (sliceHomToLocalizedStackMorphism J U hU F))).toFunctor =
    (toBasedFunctor
      (eqToHom (localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_obj J U hU X) ≫
        F.hom ≫
        eqToHom (localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_obj J U hU Y).symm)).toFunctor
  rw [sliceHomToLocalizedStack_homMk_toFunctor]
  rw [stackHom_comp_toFunctor, stackHom_comp_toFunctor]
  rw [localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_eqToHom_toFunctor]
  rw [localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_eqToHom_symm_toFunctor]
  rfl

/-- Construction B followed by Construction A is the identity on the slice strict `2`-category of
stacks over `(C, J)` above the representable stack `C/U` on `1`-morphisms, up to transport along
the object equalities from `localizedStacksToSlice_obj_sliceToLocalizedStacks_obj`. -/
private theorem localizedStacksToSlice_map_sliceToLocalizedStacks_map
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
  ∀ ⦃X Y : SliceTwoCategory (sliceStackOver J U hU)⦄ (F : X ⟶ Y),
      HEq ((localizedStacksToSlice J U hU).map ((sliceToLocalizedStacks J U hU).map F)) F := by
  intro X Y F
  let hx := localizedStacksToSlice_obj_sliceToLocalizedStacks_obj J U hU X
  let hy := localizedStacksToSlice_obj_sliceToLocalizedStacks_obj J U hU Y
  exact
    (conj_eqToHom_iff_heq
      ((localizedStacksToSlice J U hU).map ((sliceToLocalizedStacks J U hU).map F))
      F hx hy).1
      (localizedStacksToSlice_map_sliceToLocalizedStacks_map_conj J U hU F)

/-- Construction B followed by Construction A is the identity on the slice strict `2`-category of
stacks over `(C, J)` above the representable stack `C/U` on `2`-morphisms, up to transport along
the object equalities from `localizedStacksToSlice_obj_sliceToLocalizedStacks_obj`. -/
private theorem localizedStacksToSlice_map₂_sliceToLocalizedStacks_map₂
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    ∀ ⦃X Y : SliceTwoCategory (sliceStackOver J U hU)⦄
      {F G : X ⟶ Y} (η : F ⟶ G),
      HEq ((localizedStacksToSlice J U hU).map₂ ((sliceToLocalizedStacks J U hU).map₂ η)) η := by
  intro X Y F G η
  let hx := localizedStacksToSlice_obj_sliceToLocalizedStacks_obj J U hU X
  let hy := localizedStacksToSlice_obj_sliceToLocalizedStacks_obj J U hU Y
  let F' := (localizedStacksToSlice J U hU).map ((sliceToLocalizedStacks J U hU).map F)
  let G' := (localizedStacksToSlice J U hU).map ((sliceToLocalizedStacks J U hU).map G)
  let η' : F' ⟶ G' :=
    (localizedStacksToSlice J U hU).map₂ ((sliceToLocalizedStacks J U hU).map₂ η)
  change η' ≍ η
  let θ : (eqToHom hx ≫ F ≫ eqToHom hy.symm) ⟶
      (eqToHom hx ≫ G ≫ eqToHom hy.symm) :=
    (eqToHom hx ◁ η) ▷ eqToHom hy.symm
  have hF : F' = eqToHom hx ≫ F ≫ eqToHom hy.symm :=
    localizedStacksToSlice_map_sliceToLocalizedStacks_map_conj J U hU F
  have hG : G' = eqToHom hx ≫ G ≫ eqToHom hy.symm :=
    localizedStacksToSlice_map_sliceToLocalizedStacks_map_conj J U hU G
  have hηconj : η' = eqToHom hF ≫ θ ≫ eqToHom hG.symm := by
    apply sliceTwoHom_eq_of_toNatTrans_eq
    apply NatTrans.ext
    funext a
    have hleft :
        (sliceTwoHomToNatTrans J U hU η').app a =
          (sliceTwoHomToNatTrans J U hU η).app a := by
      rfl
    rw [hleft]
    rw [sliceTwoHomToNatTrans_comp_app, sliceTwoHomToNatTrans_comp_app,
      sliceTwoHomToNatTrans_eqToHom_app, sliceTwoHomToNatTrans_eqToHom_app]
    rw [sliceTwoHomToNatTrans_whiskerRight_app,
      sliceTwoHomToNatTrans_whiskerLeft_app]
    apply eq_of_heq
    let m :=
      (toBasedFunctor (eqToHom hy.symm).hom).map
        ((sliceTwoHomToNatTrans J U hU η).app ((toBasedFunctor (eqToHom hx).hom).obj a))
    change (sliceTwoHomToNatTrans J U hU η).app a ≍ eqToHom _ ≫ m ≫ eqToHom _
    rw [← Category.assoc]
    apply (heq_comp_eqToHom_iff (eqToHom _ ≫ m) ((sliceTwoHomToNatTrans J U hU η).app a) _).2
    apply (heq_eqToHom_comp_iff m ((sliceTwoHomToNatTrans J U hU η).app a) _).2
    change (sliceTwoHomToNatTrans J U hU η).app a ≍
      (toBasedFunctor (eqToHom hy.symm).hom).map
        ((sliceTwoHomToNatTrans J U hU η).app ((toBasedFunctor (eqToHom hx).hom).obj a))
    have hL :
        (toBasedFunctor (eqToHom hx).hom).toFunctor =
          𝟭 (((localizedStacksToSlice J U hU).obj
            ((sliceToLocalizedStacks J U hU).obj X)).obj.S) := by
      dsimp only [hx]
      exact localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_slice_eqToHom_hom_toFunctor
        J U hU X
    have ha : (toBasedFunctor (eqToHom hx).hom).obj a = a := by
      change (toBasedFunctor (eqToHom hx).hom).toFunctor.obj a = a
      rw [hL]
      rfl
    have hτ :
        (sliceTwoHomToNatTrans J U hU η).app
            ((toBasedFunctor (eqToHom hx).hom).obj a) ≍
          (sliceTwoHomToNatTrans J U hU η).app a := by
      rw [ha]
    have hK :
        (toBasedFunctor (eqToHom hy.symm).hom).toFunctor =
          𝟭 Y.obj.S := by
      dsimp only [hy]
      exact localizedStacksToSlice_obj_sliceToLocalizedStacks_obj_slice_eqToHom_symm_hom_toFunctor
        J U hU Y
    have hmap :
        (toBasedFunctor (eqToHom hy.symm).hom).map
            ((sliceTwoHomToNatTrans J U hU η).app
              ((toBasedFunctor (eqToHom hx).hom).obj a)) ≍
          (sliceTwoHomToNatTrans J U hU η).app
            ((toBasedFunctor (eqToHom hx).hom).obj a) := by
      change (toBasedFunctor (eqToHom hy.symm).hom).toFunctor.map
          ((sliceTwoHomToNatTrans J U hU η).app
            ((toBasedFunctor (eqToHom hx).hom).obj a)) ≍
        (sliceTwoHomToNatTrans J U hU η).app
          ((toBasedFunctor (eqToHom hx).hom).obj a)
      simpa only [Functor.id_map] using
        (Functor.hcongr_hom hK
          ((sliceTwoHomToNatTrans J U hU η).app
            ((toBasedFunctor (eqToHom hx).hom).obj a)))
    exact hτ.symm.trans hmap.symm
  exact
    ((conj_eqToHom_iff_heq η' θ hF hG).1 hηconj).trans
      (twoHom_eqToHom_whisker_heq hx hy η)

/-- Lemma 8.13.2: if the representable presheaf `yoneda.obj U` is a sheaf on `(C, J)`, then Construction A
`localizedStacksToSlice` and Construction B `sliceToLocalizedStacks` are inverse strict
`2`-functors between stacks over the localized site `(C/U, J.over U)` and stacks over `(C, J)`
above the representable stack `C/U`. This packages the source statement in the canonical Lean
form `StrictPseudofunctor.IsInverse`. -/
@[stacks 04WV]
theorem localizedStacks_equivalent_to_stacks_with_map_to_slice
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    StrictPseudofunctor.IsInverse
      (localizedStacksToSlice J U hU)
      (sliceToLocalizedStacks J U hU) := by
  refine
    { left_obj := sliceToLocalizedStacks_obj_localizedStacksToSlice_obj J U hU
      left_map := sliceToLocalizedStacks_map_localizedStacksToSlice_map J U hU
      left_map₂ := sliceToLocalizedStacks_map₂_localizedStacksToSlice_map₂ J U hU
      right_obj := localizedStacksToSlice_obj_sliceToLocalizedStacks_obj J U hU
      right_map := localizedStacksToSlice_map_sliceToLocalizedStacks_map J U hU
      right_map₂ := localizedStacksToSlice_map₂_sliceToLocalizedStacks_map₂ J U hU }

end

end CategoryTheory
