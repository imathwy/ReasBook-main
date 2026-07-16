import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.CategoryTheory.Comma.LocallySmall
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic.StacksAttribute
import stacks_proof.stacks_project.Chap10.Lemma_10_127_7.Index

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open Algebra.TensorProduct
open scoped TensorProduct

universe u v w

noncomputable section

section

-- Semantic recall note: `lean_leansearch` was unavailable (HTTP 502), so the owner/API choice
-- below follows the source tag `05N8` in `source/stacks-project/algebra.tex`.

variable {A : Type u} [CommRing A]
variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ CommAlgCat.{u} A) [HasColimit F]

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

local instance tensorDomainRightAlgebraGeneric
    {R : Type u} [CommRing R] [Algebra A R] :
    Algebra R (C ⊗[A] R) :=
  Algebra.TensorProduct.rightAlgebra (R := A) (A := C) (B := R)

local instance tensorCodomainRightAlgebraGeneric
    {R : Type u} [CommRing R] [Algebra A R] :
    Algebra R (B ⊗[A] R) :=
  Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := R)

local instance colimitTensorDomainRightAlgebra :
    Algebra ↑(colimit F) (C ⊗[A] ↑(colimit F)) :=
  Algebra.TensorProduct.rightAlgebra (R := A) (A := C) (B := ↑(colimit F))

local instance colimitTensorCodomainRightAlgebra :
    Algebra ↑(colimit F) (B ⊗[A] ↑(colimit F)) :=
  Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := ↑(colimit F))

local instance stageTensorDomainRightAlgebra (j : J) :
    Algebra ↑(F.obj j) (C ⊗[A] ↑(F.obj j)) :=
  Algebra.TensorProduct.rightAlgebra (R := A) (A := C) (B := ↑(F.obj j))

local instance stageTensorCodomainRightAlgebra (j : J) :
    Algebra ↑(F.obj j) (B ⊗[A] ↑(F.obj j)) :=
  Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := ↑(F.obj j))

omit [IsFiltered J] in
/-- Helper for Chap10 Lemma 10 127 7: the stage-to-colimit tensor map after a transition agrees
with the direct tensor map from the source stage. -/
lemma tensorStageMapToColimit_comp
    {S : Type u} [CommRing S] [Algebra A S]
    {j j' : J} (f : j ⟶ j') :
    (Algebra.TensorProduct.map (AlgHom.id A S) (colimit.ι F j').hom).comp
        (Algebra.TensorProduct.map (AlgHom.id A S) (F.map f).hom) =
      Algebra.TensorProduct.map (AlgHom.id A S) (colimit.ι F j).hom := by
  -- Proof comment: this should be a direct re-expression of
  -- `tensor_base_change_cocone_naturality`.
  apply tensor_base_change_algHom_ext
  · -- Proof comment: tensoring with the identity on the left preserves the left inclusion.
    ext s
    simp
  · -- Proof comment: on the right tensor generators, the claim is just the cocone naturality of
    -- `colimit.ι F`.
    ext r
    change (1 : S) ⊗ₜ[A] (colimit.ι F j').hom ((F.map f).hom r) =
      (1 : S) ⊗ₜ[A] (colimit.ι F j).hom r
    simpa using
      congrArg (fun φ : F.obj j ⟶ colimit F ↦ φ.hom r) ((colimit.cocone F).w f)

/-- Helper for Chap10 Lemma 10 127 7: the scalar map
`A → B ⊗[A] R'` is the composite of `A → B` with the left tensor inclusion. -/
lemma tensorIncludeLeft_comp_algebraMap
    {S R' : Type u} [CommRing S] [CommRing R'] [Algebra A S] [Algebra A R'] :
    ((Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] R').comp
        (algebraMap A S)) =
      algebraMap A (S ⊗[A] R') := by
  -- Proof comment: both algebra maps send `a : A` to the pure tensor `a ⊗ 1`.
  ext a
  simp

/-- Helper for Chap10 Lemma 10 127 7: changing the left tensor factor by `u` commutes with
changing the right tensor factor by `g`, after restricting scalars back to `A`. -/
lemma tensorMapExchangeRestrictScalars
    (u : B →ₐ[A] C)
    {R' R'' : Type u} [CommRing R'] [CommRing R''] [Algebra A R'] [Algebra A R'']
    (g : R' →ₐ[A] R'') :
    (AlgHom.restrictScalars A (Algebra.TensorProduct.map u (AlgHom.id A R''))).comp
        (Algebra.TensorProduct.map (AlgHom.id A B) g) =
      (Algebra.TensorProduct.map (AlgHom.id A C) g).comp
        (AlgHom.restrictScalars A (Algebra.TensorProduct.map u (AlgHom.id A R'))) := by
  apply tensor_base_change_algHom_ext
  · ext s
    simp
  · ext r
    simp

/-- Helper for Chap10 Lemma 10 127 7: `productMap vLeft includeRight` recovers `vLeft` on the
left tensor-factor generators. -/
lemma tensorProductProductMap_comp_includeLeft
    {R : Type u} [CommRing R] [Algebra A R]
    (vLeft : C →ₐ[A] B ⊗[A] R) :
    (Algebra.TensorProduct.productMap vLeft
      (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R)).comp
        (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R) =
      vLeft := by
  -- Proof comment: the universal tensor map is characterized by extending `vLeft` on the left
  -- tensor generator and `includeRight` on the right tensor generator.
  ext c
  simp

/-- Helper for Chap10 Lemma 10 127 7: `productMap vLeft includeRight` fixes the right tensor
factor elementwise, so it upgrades to an algebra map over the stage ring. -/
lemma tensorProductProductMap_commutesStageScalars_apply
    {R : Type u} [CommRing R] [Algebra A R]
    (vLeft : C →ₐ[A] B ⊗[A] R)
    (r : R) :
    (Algebra.TensorProduct.productMap vLeft
      (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R))
        ((Algebra.TensorProduct.includeRight : R →ₐ[A] C ⊗[A] R) r) =
      (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R) r := by
  -- Proof comment: the universal tensor map was defined to restrict to `includeRight` on the
  -- right tensor factor, which is exactly the stage scalar map.
  simpa using
    Algebra.TensorProduct.productMap_right_apply vLeft
      (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R) r

/-- Helper for Chap10 Lemma 10 127 7: the tensor base-change map `u ⊗ 1`
commutes with the right tensor-factor algebra structure. -/
lemma tensorBaseChangeMapOverRightBase_commutes
    {R : Type u} [CommRing R] [Algebra A R]
    (u : B →ₐ[A] C)
    (r : R) :
    (Algebra.TensorProduct.map u (AlgHom.id A R))
        ((algebraMap R (B ⊗[A] R)) r) =
      (algebraMap R (C ⊗[A] R)) r := by
  -- Proof comment: `u ⊗ 1` fixes the right tensor generators, which are exactly the
  -- `R`-algebra structure maps on the tensor products.
  have hmap :
      (Algebra.TensorProduct.map u (AlgHom.id A R)).comp
          (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R) =
        (Algebra.TensorProduct.includeRight : R →ₐ[A] C ⊗[A] R) := by
    simpa using Algebra.TensorProduct.map_comp_includeRight u (AlgHom.id A R)
  exact congrArg (fun φ : R →ₐ[A] C ⊗[A] R ↦ φ r) hmap

/-- Helper for Chap10 Lemma 10 127 7: view `u ⊗ 1` as an algebra map over the right tensor
factor ring. -/
abbrev tensorBaseChangeMapOverRightBase
    {R : Type u} [CommRing R] [Algebra A R]
    (u : B →ₐ[A] C) :
    B ⊗[A] R →ₐ[R] C ⊗[A] R :=
  { toRingHom := (Algebra.TensorProduct.map u (AlgHom.id A R)).toRingHom
    commutes' := tensorBaseChangeMapOverRightBase_commutes u }

/-- Helper for Chap10 Lemma 10 127 7: finitely many arrows from one source object can be pushed
to a common target with a common composite in a filtered category. -/
lemma filteredCommonTargetOfFiniteMapsFrom
    {i : J} {α : Type u}
    (s : Finset α)
    (j : α → J)
    (f : ∀ a : α, ∀ ha : a ∈ s, i ⟶ j a) :
    ∃ k : J, ∃ g : i ⟶ k, ∀ a (ha : a ∈ s), ∃ h : j a ⟶ k, f a ha ≫ h = g := by
  classical
  -- Proof comment: recurse on the finite family; when inserting one more map, first push the old
  -- target and the new target to a common object, then coequalize the two resulting maps from `i`.
  revert j f
  refine s.induction_on ?_ ?_
  · intro j f
    refine ⟨i, 𝟙 i, ?_⟩
    intro a ha
    cases ha
  · intro a s ha ih j f
    let fTail : ∀ b : α, ∀ hb : b ∈ s, i ⟶ j b := fun b hb ↦ f b (Finset.mem_insert_of_mem hb)
    obtain ⟨k₀, g₀, hg₀⟩ := ih j fTail
    let l := IsFiltered.max (j a) k₀
    let αa : j a ⟶ l := IsFiltered.leftToMax (j a) k₀
    let β₀ : k₀ ⟶ l := IsFiltered.rightToMax (j a) k₀
    let p : i ⟶ l := f a (Finset.mem_insert_self a s) ≫ αa
    let q : i ⟶ l := g₀ ≫ β₀
    let k : J := IsFiltered.coeq p q
    let t : l ⟶ k := IsFiltered.coeqHom p q
    refine ⟨k, p ≫ t, ?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb'
    · refine ⟨αa ≫ t, ?_⟩
      simp [p, Category.assoc]
    · rcases hg₀ b hb' with ⟨h_b, hh_b⟩
      have hh_b' : f b hb ≫ h_b = g₀ := by
        simpa [fTail] using hh_b
      refine ⟨h_b ≫ β₀ ≫ t, ?_⟩
      calc
        f b hb ≫ (h_b ≫ β₀ ≫ t) = (f b hb ≫ h_b) ≫ β₀ ≫ t := by simp [Category.assoc]
        _ = g₀ ≫ β₀ ≫ t := by rw [hh_b']
        _ = q ≫ t := by simp [q, Category.assoc]
        _ = p ≫ t := by simpa [p, q] using (IsFiltered.coeq_condition p q).symm

/-- Helper for Chap10 Lemma 10 127 7: every element of the underlying ring of a filtered colimit
comes from some stage map. -/
lemma commRing_filteredColimit_forget_jointly_surjective
    {I : Type v} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ CommRingCat.{u}} {c : Cocone D} (hc : IsColimit c) :
    ∀ x : ((forget CommRingCat).mapCocone c).pt,
      ∃ i y, x = ((forget CommRingCat).mapCocone c).ι.app i y := by
  let G : Set c.pt := {z | ∃ i y, z = c.ι.app i y}
  let S : Subring c.pt := Subring.closure G
  let P : c.pt → Prop := fun z ↦ ∃ i y, z = c.ι.app i y
  have hclosure : ∀ z : c.pt, z ∈ S → ∃ i y, z = c.ι.app i y := by
    intro z hz
    refine Subring.closure_induction ?_ ?_ ?_ ?_ ?_ ?_ hz
    · intro z hzG
      exact hzG
    · obtain ⟨i⟩ := (IsFiltered.nonempty : Nonempty I)
      exact ⟨i, 0, ((c.ι.app i).hom.map_zero).symm⟩
    · obtain ⟨i⟩ := (IsFiltered.nonempty : Nonempty I)
      exact ⟨i, 1, ((c.ι.app i).hom.map_one).symm⟩
    · intro x y _ _ hx hy
      obtain ⟨i, xi, hxi⟩ := hx
      obtain ⟨j, yj, hyj⟩ := hy
      let k := IsFiltered.max i j
      let fi : i ⟶ k := IsFiltered.leftToMax i j
      let fj : j ⟶ k := IsFiltered.rightToMax i j
      refine ⟨k, (D.map fi).hom xi + (D.map fj).hom yj, ?_⟩
      have hleft : (c.ι.app i).hom xi = (c.ι.app k).hom ((D.map fi).hom xi) := by
        exact (congrArg (fun f : D.obj i ⟶ c.pt ↦ f xi) (c.w fi)).symm
      have hright : (c.ι.app j).hom yj = (c.ι.app k).hom ((D.map fj).hom yj) := by
        exact (congrArg (fun f : D.obj j ⟶ c.pt ↦ f yj) (c.w fj)).symm
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
      let fi : i ⟶ k := IsFiltered.leftToMax i j
      let fj : j ⟶ k := IsFiltered.rightToMax i j
      refine ⟨k, (D.map fi).hom xi * (D.map fj).hom yj, ?_⟩
      have hleft : (c.ι.app i).hom xi = (c.ι.app k).hom ((D.map fi).hom xi) := by
        exact (congrArg (fun f : D.obj i ⟶ c.pt ↦ f xi) (c.w fi)).symm
      have hright : (c.ι.app j).hom yj = (c.ι.app k).hom ((D.map fj).hom yj) := by
        exact (congrArg (fun f : D.obj j ⟶ c.pt ↦ f yj) (c.w fj)).symm
      rw [hxi, hyj, hleft, hright]
      exact ((c.ι.app k).hom.map_mul _ _).symm
  have hmem (i : I) (y : D.obj i) : c.ι.app i y ∈ S :=
    Subring.subset_closure ⟨i, y, rfl⟩
  let app (i : I) : D.obj i ⟶ CommRingCat.of S :=
    CommRingCat.ofHom ((c.ι.app i).hom.codRestrict S (hmem i))
  have app_naturality : ∀ {i j : I} (f : i ⟶ j), D.map f ≫ app j = app i := by
    intro i j f
    ext y
    exact congrArg (fun g : D.obj i ⟶ c.pt ↦ g y) (c.w f)
  let d : Cocone D :=
    { pt := CommRingCat.of S
      ι :=
        { app := app
          naturality := fun _ _ f ↦ app_naturality f } }
  let liftToS : c.pt ⟶ CommRingCat.of S := hc.desc d
  let incl : CommRingCat.of S ⟶ c.pt := CommRingCat.ofHom S.subtype
  have hincl : liftToS ≫ incl = 𝟙 c.pt := by
    -- Proof comment: both endomorphisms of the colimit point agree after precomposing with every
    -- stage leg, so colimit extensionality identifies them.
    apply hc.hom_ext
    intro i
    calc
      c.ι.app i ≫ liftToS ≫ incl = d.ι.app i ≫ incl := by
        simpa [Category.assoc, liftToS] using congrArg (fun f ↦ f ≫ incl) (hc.fac d i)
      _ = c.ι.app i ≫ 𝟙 c.pt := by
        ext y
        rfl
  intro x
  -- Proof comment: the splitting through the representative subring shows that `x` already lies
  -- in the closure of stage images, where the closure induction produced a stage representative.
  have hx : x = incl (liftToS x) := by
    exact (congrArg (fun f : c.pt ⟶ c.pt ↦ f x) hincl).symm
  obtain ⟨i, y, hy⟩ := hclosure (incl (liftToS x)) (liftToS x).property
  exact ⟨i, y, hx.trans hy⟩

/-- Helper for Chap10 Lemma 10 127 7: an equality in the underlying `Type`-colimit of a filtered
diagram of commutative rings descends once the forgetful functor is known to preserve the chosen
colimit. -/
lemma commRing_filteredColimit_forget_eq_descends_of_preserves
    {I : Type v} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ CommRingCat.{w}} {c : Cocone D} (hc : IsColimit c)
    [PreservesColimit D (forget CommRingCat)]
    {i : I} (x y : D.obj i)
    (hxy : ((forget CommRingCat).mapCocone c).ι.app i x =
      ((forget CommRingCat).mapCocone c).ι.app i y) :
    ∃ (j : I) (f : i ⟶ j), (D.map f).hom x = (D.map f).hom y := by
  have htype :
      IsColimit ((forget CommRingCat).mapCocone c) :=
    isColimitOfPreserves (forget CommRingCat) hc
  -- Proof comment: once the chosen cocone is also a colimit in `Type`, the standard filtered
  -- colimit equality criterion gives the required eventual equality at a later stage.
  exact (Types.FilteredColimit.isColimit_eq_iff' htype x y).1 hxy

/-- Helper for Chap10 Lemma 10 127 7: the local `CommRingCat` carrier-`ULift` functor sends
identity morphisms to identity morphisms. -/
lemma commRingUliftFunctor_map_id (R : CommRingCat.{w}) :
    CommRingCat.ofHom
        (RingHom.ulift (RingHom.id R) : ULift.{v} R →+* ULift.{v} R) =
      𝟙 (CommRingCat.of (ULift.{v} R)) := by
  -- Proof comment: on elements, the lifted identity map is definitionally the identity function.
  ext x
  simp [RingHom.ulift_apply]

/-- Helper for Chap10 Lemma 10 127 7: the local `CommRingCat` carrier-`ULift` functor sends
composites to composites. -/
lemma commRingUliftFunctor_map_comp
    {R S T : CommRingCat.{w}} (f : R ⟶ S) (g : S ⟶ T) :
    CommRingCat.ofHom
        (RingHom.ulift (g.hom.comp f.hom) : ULift.{v} R →+* ULift.{v} T) =
      CommRingCat.ofHom
          (RingHom.ulift f.hom : ULift.{v} R →+* ULift.{v} S) ≫
        CommRingCat.ofHom
          (RingHom.ulift g.hom : ULift.{v} S →+* ULift.{v} T) := by
  -- Proof comment: both sides evaluate to `ULift.up (g (f x.down))`.
  ext x
  simp [RingHom.ulift_apply]

/-- Helper for Chap10 Lemma 10 127 7: the local carrier-`ULift` functor on `CommRingCat`
raises ring carriers to a universe large enough for the filtered index category. -/
abbrev commRingUliftFunctor : CommRingCat.{w} ⥤ CommRingCat.{max v w} where
  obj R := CommRingCat.of (ULift.{v} R)
  map f := CommRingCat.ofHom (RingHom.ulift f.hom)
  map_id := commRingUliftFunctor_map_id
  map_comp := commRingUliftFunctor_map_comp

/-- Helper for Chap10 Lemma 10 127 7: any cocone of commutative rings lifts along the local
carrier-`ULift` functor. -/
abbrev commRingUliftCocone
    {I : Type v} [SmallCategory I] {D : I ⥤ CommRingCat.{w}} (c : Cocone D) :
    Cocone (D ⋙ commRingUliftFunctor) where
  pt := CommRingCat.of (ULift.{v} c.pt)
  ι :=
    { app := fun i ↦ CommRingCat.ofHom (RingHom.ulift (c.ι.app i).hom)
      naturality := by
        intro i j f
        -- Proof comment: the cocone naturality equation is preserved by `RingHom.ulift`.
        apply CommRingCat.hom_ext
        ext x
        change ULift.up ((c.ι.app j).hom ((D.map f).hom x.down)) =
          ULift.up ((c.ι.app i).hom x.down)
        exact congrArg ULift.up (DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (c.w f)) x.down) }

/-- Helper for Chap10 Lemma 10 127 7: after forgetting commutative-ring structure, the local
carrier-`ULift` functor is literally the ordinary type-level `uliftFunctor`. -/
def commRingUliftFunctorForgetIso :
    commRingUliftFunctor.{v, w} ⋙ forget CommRingCat.{max v w} ≅
      forget CommRingCat.{w} ⋙ CategoryTheory.uliftFunctor.{v, w} :=
  NatIso.ofComponents
    (fun R ↦ Iso.refl (CategoryTheory.uliftFunctor.obj R))
    (by
      intro X Y f
      rfl)

/-- Helper for Chap10 Lemma 10 127 7: if two elements from one stage agree in the canonical
filtered colimit of commutative rings, then they agree after one later transition. -/
lemma commRingForgetMapCoconeUliftEq
    {I : Type v} [SmallCategory I]
    {D : I ⥤ CommRingCat.{w}} {c : Cocone D}
    {i : I} (x y : D.obj i)
    (hxy : ((forget CommRingCat).mapCocone c).ι.app i x =
      ((forget CommRingCat).mapCocone c).ι.app i y) :
    ((CategoryTheory.uliftFunctor.{v}.mapCocone ((forget CommRingCat).mapCocone c)).ι.app i
        (ULift.up.{v} x)) =
      ((CategoryTheory.uliftFunctor.{v}.mapCocone ((forget CommRingCat).mapCocone c)).ι.app i
        (ULift.up.{v} y)) := by
  -- Proof comment: applying `ULift.up` to an equality in the forgotten cocone is exactly the
  -- same as evaluating the lifted cocone in `Type (max v w)`.
  simpa using congrArg ULift.up.{v} hxy

/-- Helper for Chap10 Lemma 10 127 7: if two elements from one stage agree in the canonical
filtered colimit of commutative rings, then they agree after one later transition. -/
lemma commRingUliftStageMap_naturality
    {I : Type v} [SmallCategory I]
    {D : I ⥤ CommRingCat.{w}} {i j : I} (f : i ⟶ j) :
    (ULift.ringEquiv.symm.toRingHom : D.obj j →+* ULift.{v} (D.obj j)).comp (D.map f).hom =
      (RingHom.ulift (D.map f).hom).comp
        (ULift.ringEquiv.symm.toRingHom : D.obj i →+* ULift.{v} (D.obj i)) := by
  -- Proof comment: both composites send an element `x` to the same lifted image
  -- `ULift.up ((D.map f).hom x)` in the larger-universe stage ring.
  ext x
  rfl

/-- Helper for Chap10 Lemma 10 127 7: equality of lifted stage images descends back to equality
in the original stage ring after applying `ULift.down`. -/
lemma commRingUliftStageEq_down
    {I : Type v} [SmallCategory I]
    {D : I ⥤ CommRingCat.{w}} {i j : I} (f : i ⟶ j)
    {x y : D.obj i}
    (h :
      (RingHom.ulift (D.map f).hom) (ULift.up.{v} x) =
        (RingHom.ulift (D.map f).hom) (ULift.up.{v} y)) :
    (D.map f).hom x = (D.map f).hom y := by
  -- Proof comment: `RingHom.ulift` sends an element to the lifted image of the original map, so
  -- applying `ULift.down` to both sides recovers equality in the source universe.
  simpa [RingHom.ulift_apply] using congrArg ULift.down h

/-- Helper for Chap10 Lemma 10 127 7: a morphism out of the one-generator polynomial ring
`(ULift ℤ)[X]` is determined by the image of `X`. -/
lemma oneVarUliftInt_hom_ext
    {R : Type w} [CommRing R]
    {f g : CommRingCat.of (MvPolynomial PUnit.{w + 1} (ULift.{w} ℤ)) ⟶ CommRingCat.of R}
    (h : f (.X PUnit.unit) = g (.X PUnit.unit)) :
    f = g := by
  -- Proof comment: first transport the coefficient ring from `ULift ℤ` back to `ℤ`,
  -- where `RingHom.ext_int` handles the coefficient part automatically.
  suffices hf :
      f.hom.comp (MvPolynomial.mapEquiv _ ULift.ringEquiv.symm).toRingHom =
        g.hom.comp (MvPolynomial.mapEquiv _ ULift.ringEquiv.symm).toRingHom by
    -- Proof comment: after this normalization, equality on coefficients and on the single
    -- generator recovers equality of the original commutative-ring morphisms.
    ext x
    · obtain ⟨x⟩ := x
      simpa [-map_intCast, -eq_intCast] using DFunLike.congr_fun hf (MvPolynomial.C x)
    · simpa [-map_intCast, -eq_intCast] using DFunLike.congr_fun hf (MvPolynomial.X x)
  ext1
  · -- Proof comment: the normalized maps agree on the integer coefficients.
    exact RingHom.ext_int _ _
  · -- Proof comment: there is only one variable, so the hypothesis fixes the generator image.
    simpa using h

/-- Helper for Chap10 Lemma 10 127 7: a morphism in the under category from the one-generator
classifier is determined by the image of the polynomial generator. -/
lemma oneVarUliftIntUnderHomExt
    {Z : Under (CommRingCat.of (ULift.{w} ℤ))}
    {f g :
      CommRingCat.mkUnder (CommRingCat.of (ULift.{w} ℤ))
        (MvPolynomial PUnit.{w + 1} (ULift.{w} ℤ)) ⟶ Z}
    (h : f.right (.X PUnit.unit) = g.right (.X PUnit.unit)) :
    f = g := by
  -- Proof comment: equality in `Under` is equality of the underlying ring maps, and the source
  -- ring map is already determined by the image of the single polynomial generator.
  apply Under.UnderMorphism.ext
  exact oneVarUliftInt_hom_ext h

/-- Helper for Chap10 Lemma 10 127 7: the one-generator classifier under `ULift ℤ` is finitely
presentable in the corresponding under category. -/
lemma oneVarUliftIntUnderIsFinitelyPresentable :
    IsFinitelyPresentable.{w}
      (CommRingCat.mkUnder (CommRingCat.of (ULift.{w} ℤ))
        (MvPolynomial PUnit.{w + 1} (ULift.{w} ℤ))) := by
  let R0 : CommRingCat.{w} := CommRingCat.of (ULift.{w} ℤ)
  let PUnder : Under R0 :=
    CommRingCat.mkUnder R0 (MvPolynomial PUnit.{w + 1} (ULift.{w} ℤ))
  have hfp :
      (algebraMap (ULift.{w} ℤ) (MvPolynomial PUnit.{w + 1} (ULift.{w} ℤ))).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr inferInstance
  -- Proof comment: mathlib already identifies finite presentation of the structure map with
  -- finite presentability of the corresponding object in `Under`.
  simpa [R0, PUnder] using
    (CommRingCat.isFinitelyPresentable_under (R := R0) PUnder hfp)

/-- Helper for Chap10 Lemma 10 127 7: if two elements from one stage agree in the canonical
filtered colimit of commutative rings, then they agree after one later transition. -/
lemma commRing_largeFilteredColimit_forget_eq_descends
    {I : Type v} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ CommRingCat.{w}} {c : Cocone D} (hc : IsColimit c)
    {i : I} (x y : D.obj i)
    (hxy : ((forget CommRingCat).mapCocone c).ι.app i x =
      ((forget CommRingCat).mapCocone c).ι.app i y) :
    ∃ (j : I) (f : i ⟶ j), (D.map f).hom x = (D.map f).hom y := by
  let R0 : CommRingCat.{w} := CommRingCat.of (ULift.{w} ℤ)
  let baseHom : ∀ X : CommRingCat.{w}, R0 ⟶ X := fun X ↦
    CommRingCat.ofHom ((Int.castRingHom X).comp ULift.ringEquiv.toRingHom)
  let s : (Functor.const I).obj R0 ⟶ D :=
    { app := fun j ↦ baseHom (D.obj j)
      naturality := by
        intro j k f
        -- Proof comment: every transition map preserves integer coefficients, so the chosen
        -- base map into the stages is natural.
        apply CommRingCat.hom_ext
        ext n
        obtain ⟨n⟩ := n
        change (n : D.obj k) = (D.map f).hom (n : D.obj j)
        simp }
  let p : R0 ⟶ c.pt := baseHom c.pt
  have hp : ∀ j, s.app j ≫ c.ι.app j = p := by
    intro j
    -- Proof comment: the cocone legs are also ring maps, so they commute with the canonical
    -- map from `ULift ℤ` into each stage.
    apply CommRingCat.hom_ext
    ext n
    obtain ⟨n⟩ := n
    change (c.ι.app j).hom (n : D.obj j) = (n : c.pt)
    simpa using (map_intCast (c.ι.app j).hom n)
  let cUnder : Cocone (Under.lift D s) := Under.liftCocone D s c p hp
  letI : Nonempty I := IsFiltered.nonempty
  have hcUnder : IsColimit cUnder := by
    -- Proof comment: once the original cocone is colimiting, the lifted cocone in `Under R0`
    -- is also colimiting because the filtered index category is nonempty.
    exact Under.isColimitLiftCocone D s c p hp hc
  let PUnder : Under R0 :=
    CommRingCat.mkUnder R0 (MvPolynomial PUnit.{w + 1} (ULift.{w} ℤ))
  haveI : IsFinitelyPresentable.{w} PUnder := by
    -- Proof comment: the classifier source is the finitely presented one-variable polynomial
    -- algebra over `ULift ℤ`.
    simpa [PUnder, R0] using
      (oneVarUliftIntUnderIsFinitelyPresentable : IsFinitelyPresentable.{w}
        (CommRingCat.mkUnder (CommRingCat.of (ULift.{w} ℤ))
          (MvPolynomial PUnit.{w + 1} (ULift.{w} ℤ))))
  let a : PUnder ⟶ (Under.lift D s).obj i :=
    Under.homMk
      (CommRingCat.ofHom (MvPolynomial.eval₂Hom (s.app i).hom (fun _ ↦ x)))
      (by
        -- Proof comment: the classifier sends coefficients through the chosen structure map and
        -- the single variable to `x`, so it is automatically a morphism in `Under R0`.
        ext z
        obtain ⟨z⟩ := z
        simpa [s, baseHom] using
          (MvPolynomial.eval₂Hom_C (s.app i).hom (fun _ ↦ x) (ULift.up z)))
  let b : PUnder ⟶ (Under.lift D s).obj i :=
    Under.homMk
      (CommRingCat.ofHom (MvPolynomial.eval₂Hom (s.app i).hom (fun _ ↦ y)))
      (by
        -- Proof comment: the second classifier is identical except that the generator maps to
        -- `y`.
        ext z
        obtain ⟨z⟩ := z
        simpa [s, baseHom] using
          (MvPolynomial.eval₂Hom_C (s.app i).hom (fun _ ↦ y) (ULift.up z)))
  have hab_colim : a ≫ cUnder.ι.app i = b ≫ cUnder.ι.app i := by
    -- Route correction: instead of trying to prove `forget CommRingCat` preserves this colimit,
    -- classify the chosen elements by morphisms from a finitely presentable under-object and
    -- descend equality in the corresponding `coyoneda` filtered colimit.
    apply oneVarUliftIntUnderHomExt
    -- Proof comment: evaluating the two classifier maps on the generator `X` recovers the given
    -- equality of the original elements in the colimit ring.
    change
      (c.ι.app i).hom (MvPolynomial.eval₂Hom (s.app i).hom (fun _ ↦ x) (.X PUnit.unit)) =
        (c.ι.app i).hom (MvPolynomial.eval₂Hom (s.app i).hom (fun _ ↦ y) (.X PUnit.unit))
    rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
    simpa using hxy
  haveI : Fact Cardinal.aleph0.{max v w}.IsRegular := Cardinal.fact_isRegular_aleph0
  haveI : EssentiallySmall.{max v w} I := essentiallySmallSelf I
  haveI : IsCardinalFiltered I Cardinal.aleph0.{max v w} :=
    (isCardinalFiltered_aleph0_iff.{max v w} I).2 inferInstance
  haveI : IsFinitelyPresentable.{max v w} PUnder := by
    -- TODO: upgrade the existing `IsFinitelyPresentable.{w}` classifier instance to
    -- `IsFinitelyPresentable.{max v w}`. The presentability theorem currently available for
    -- `Under` objects is universe-fixed at `w`, but `exists_eq_of_isColimit'` over `I : Type v`
    -- needs the larger presentability universe.
    sorry
  obtain ⟨j, f, hstage⟩ :=
    IsCardinalPresentable.exists_eq_of_isColimit'
      (X := PUnder) (κ := Cardinal.aleph0.{max v w}) hcUnder a b hab_colim
  refine ⟨j, f, ?_⟩
  -- Proof comment: evaluating the stabilized classifier equality on the unique generator gives
  -- the desired equality after one later transition in the original ring diagram.
  have hX := congrArg (fun g ↦ g.right (.X PUnit.unit)) hstage
  change
    (D.map f).hom (MvPolynomial.eval₂Hom (s.app i).hom (fun _ ↦ x) (.X PUnit.unit)) =
      (D.map f).hom (MvPolynomial.eval₂Hom (s.app i).hom (fun _ ↦ y) (.X PUnit.unit)) at hX
  rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X'] at hX
  simpa using hX

/-- Helper for Chap10 Lemma 10 127 7: after transporting a backend tensor-base-change morphism
through the canonical comparison isomorphisms, its action on elements is exactly the literal tensor
map `Algebra.TensorProduct.map (AlgHom.id A S) g.hom`. -/
lemma tensorBaseChangeBackendForgetMap_apply_eq_literal
    {S : Type u} [CommRing S] [Algebra A S]
    {T T' : CommAlgCat.{u} A} (g : T ⟶ T')
    (z : S ⊗[A] (T : Type u)) :
    let backendMap :=
      ((Under.forget (CommRingCat.of S)).map
        ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).map
          (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g)))
    (tensor_base_change_backend_forget_obj_iso S T').hom
        (backendMap.hom ((tensor_base_change_backend_forget_obj_iso S T).inv z)) =
      (Algebra.TensorProduct.map (AlgHom.id A S) g.hom) z := by
  -- Proof comment: evaluate the backend/literal comparison isomorphism on the chosen tensor
  -- element, so the abstract conjugation identity becomes an explicit formula on elements.
  have hcmp :=
    tensor_base_change_backend_forget_hom_conj_eq_literal S g
  simpa [Category.assoc] using
    congrArg
      (fun k :
        CommRingCat.of (S ⊗[A] (T : Type u)) ⟶
          CommRingCat.of (S ⊗[A] (T' : Type u)) ↦
          k.hom z)
      hcmp

/-- Helper for Chap10 Lemma 10 127 7: one equality at the colimit stage already stabilizes after
passing to a later stage. -/
lemma tensorStageEqDescends
    {S : Type u} [CommRing S] [Algebra A S]
    {j₀ : J}
    (x y : S ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u))
    (h :
      (Algebra.TensorProduct.map (AlgHom.id A S) (colimit.ι F j₀).hom) x =
        (Algebra.TensorProduct.map (AlgHom.id A S) (colimit.ι F j₀).hom) y) :
    ∃ (j : J) (f : j₀ ⟶ j),
        (Algebra.TensorProduct.map (AlgHom.id A S) (F.map f).hom) x =
        (Algebra.TensorProduct.map (AlgHom.id A S) (F.map f).hom) y := by
  let D' := tensor_base_change_diagram F S
  let c' : Cocone D' := tensor_base_change_cocone F S
  have hc : IsColimit c' := tensor_base_change_cocone_isColimit F S
  -- Proof comment: the literal tensor cocone is already a filtered colimit in `CommRingCat`,
  -- so equality at the colimit point descends directly to equality after one later transition.
  obtain ⟨j, f, hf⟩ :=
    commRing_largeFilteredColimit_forget_eq_descends hc x y (by
        -- Proof comment: rewrite the tensor equality as equality after applying the corresponding
        -- cocone leg in the forgotten ring diagram.
        simpa [c', D', tensor_base_change_cocone, tensor_base_change_diagram] using h)
  refine ⟨j, f, ?_⟩
  -- Proof comment: after unfolding the tensor-stage diagram map, the descended equality is
  -- exactly the desired literal tensor equality.
  simpa [D', tensor_base_change_diagram] using hf

omit [IsFiltered J] [HasColimit F] in
/-- Helper for Chap10 Lemma 10 127 7: once two tensor-stage elements agree after one transition,
they still agree after any further transition. -/
lemma tensorStageEqMap_comp
    {S : Type u} [CommRing S] [Algebra A S]
    {i j k : J} (f : i ⟶ j) (g : j ⟶ k)
    {x y : S ⊗[A] ((F.obj i : CommAlgCat A) : Type u)}
    (hxy :
      (Algebra.TensorProduct.map (AlgHom.id A S) (F.map f).hom) x =
        (Algebra.TensorProduct.map (AlgHom.id A S) (F.map f).hom) y) :
    (Algebra.TensorProduct.map (AlgHom.id A S) (F.map (f ≫ g)).hom) x =
      (Algebra.TensorProduct.map (AlgHom.id A S) (F.map (f ≫ g)).hom) y := by
  -- Proof comment: apply the later transition map to both sides of the known equality.
  have hpush :=
    congrArg (Algebra.TensorProduct.map (AlgHom.id A S) (F.map g).hom) hxy
  have hcomp :
      Algebra.TensorProduct.map (AlgHom.id A S) (F.map (f ≫ g)).hom =
        (Algebra.TensorProduct.map (AlgHom.id A S) (F.map g).hom).comp
          (Algebra.TensorProduct.map (AlgHom.id A S) (F.map f).hom) := by
    ext z <;> simp [Functor.map_comp, Algebra.TensorProduct.map_comp]
  calc
    (Algebra.TensorProduct.map (AlgHom.id A S) (F.map (f ≫ g)).hom) x =
      (Algebra.TensorProduct.map (AlgHom.id A S) (F.map g).hom)
        ((Algebra.TensorProduct.map (AlgHom.id A S) (F.map f).hom) x) := by
          simpa [AlgHom.comp_apply] using
            congrArg
              (fun φ :
                S ⊗[A] ((F.obj i : CommAlgCat A) : Type u) →ₐ[A]
                  S ⊗[A] ((F.obj k : CommAlgCat A) : Type u) ↦ φ x)
              hcomp
    _ =
      (Algebra.TensorProduct.map (AlgHom.id A S) (F.map g).hom)
        ((Algebra.TensorProduct.map (AlgHom.id A S) (F.map f).hom) y) := hpush
    _ = (Algebra.TensorProduct.map (AlgHom.id A S) (F.map (f ≫ g)).hom) y := by
          simpa [AlgHom.comp_apply] using
            congrArg
              (fun φ :
                S ⊗[A] ((F.obj i : CommAlgCat A) : Type u) →ₐ[A]
                  S ⊗[A] ((F.obj k : CommAlgCat A) : Type u) ↦ φ y)
              hcomp.symm

/-- Helper for Chap10 Lemma 10 127 7: finitely many colimit equalities at one source stage
stabilize after passing to a common later stage. -/
lemma tensorStageEqDescendsFiniteFamily
    {S : Type u} [CommRing S] [Algebra A S]
    {α : Type u}
    {j₀ : J}
    (s : Finset α)
    (x y : α → S ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u))
    (h :
      ∀ a ∈ s,
        (Algebra.TensorProduct.map (AlgHom.id A S) (colimit.ι F j₀).hom) (x a) =
          (Algebra.TensorProduct.map (AlgHom.id A S) (colimit.ι F j₀).hom) (y a)) :
    ∃ (j : J) (f : j₀ ⟶ j),
      ∀ a ∈ s,
        (Algebra.TensorProduct.map (AlgHom.id A S) (F.map f).hom) (x a) =
        (Algebra.TensorProduct.map (AlgHom.id A S) (F.map f).hom) (y a) := by
  classical
  -- Proof comment: first descend each equality separately, then push the resulting stage maps to
  -- one common target and transport the equalities along the common transition maps.
  let t : Finset {a // a ∈ s} := s.attach
  have hdesc :
      ∀ a : {a // a ∈ s}, ∃ (j : J) (f : j₀ ⟶ j),
        (Algebra.TensorProduct.map (AlgHom.id A S) (F.map f).hom) (x a) =
          (Algebra.TensorProduct.map (AlgHom.id A S) (F.map f).hom) (y a) := by
    intro a
    exact tensorStageEqDescends F (x a) (y a) (h a a.2)
  choose j fj hfj using hdesc
  obtain ⟨k, g, hg⟩ :=
    filteredCommonTargetOfFiniteMapsFrom t j fun a _ ↦ fj a
  refine ⟨k, g, ?_⟩
  intro a ha
  rcases hg ⟨a, ha⟩ (by simp [t]) with ⟨k_a, hk_a⟩
  have hpush :=
    congrArg (Algebra.TensorProduct.map (AlgHom.id A S) (F.map k_a).hom) (hfj ⟨a, ha⟩)
  have hk_map :
      (Algebra.TensorProduct.map (AlgHom.id A S) (F.map k_a).hom).comp
          (Algebra.TensorProduct.map (AlgHom.id A S) (F.map (fj ⟨a, ha⟩)).hom) =
        Algebra.TensorProduct.map (AlgHom.id A S) (F.map g).hom := by
    apply tensor_base_change_algHom_ext
    · ext s
      simp [AlgHom.comp_apply, Algebra.TensorProduct.map_comp_includeLeft]
    · ext r
      have hmap :
          F.map (fj ⟨a, ha⟩ ≫ k_a) = F.map g := by
        simpa [hk_a]
      have hmap_apply :
          (F.map k_a).hom ((F.map (fj ⟨a, ha⟩)).hom r) =
            (F.map g).hom r := by
        simpa [Functor.map_comp] using
          congrArg (fun φ : F.obj j₀ ⟶ F.obj k ↦ φ.hom r) hmap
      simpa using congrArg (fun z : (F.obj k : CommAlgCat A) ↦ (1 : S) ⊗ₜ[A] z) hmap_apply
  calc
    (Algebra.TensorProduct.map (AlgHom.id A S) (F.map g).hom) (x a) =
      (Algebra.TensorProduct.map (AlgHom.id A S) (F.map k_a).hom)
        ((Algebra.TensorProduct.map (AlgHom.id A S) (F.map (fj ⟨a, ha⟩)).hom) (x a)) := by
          simpa [AlgHom.comp_apply] using
            congrArg
              (fun φ :
                S ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u) →ₐ[A]
                    S ⊗[A] ((F.obj k : CommAlgCat A) : Type u) ↦
                  φ (x a))
              hk_map.symm
    _ =
      (Algebra.TensorProduct.map (AlgHom.id A S) (F.map k_a).hom)
        ((Algebra.TensorProduct.map (AlgHom.id A S) (F.map (fj ⟨a, ha⟩)).hom) (y a)) := hpush
    _ = (Algebra.TensorProduct.map (AlgHom.id A S) (F.map g).hom) (y a) := by
          simpa [AlgHom.comp_apply] using
            congrArg
              (fun φ :
                S ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u) →ₐ[A]
                    S ⊗[A] ((F.obj k : CommAlgCat A) : Type u) ↦
                  φ (y a))
              hk_map

/-- Helper for Chap10 Lemma 10 127 7: equality of two finitely generated `S`-algebra maps into one
tensor stage already stabilizes after passing to a later stage of the filtered diagram. -/
lemma tensorStageMapEqualityDescends
    {S P : Type u} [CommRing S] [CommRing P] [Algebra A S] [Algebra S P]
    [Algebra.FiniteType S P]
    {j₀ : J}
    (a b : P →ₐ[S] S ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u))
    (h :
      CommRingCat.ofHom a.toRingHom ≫
          (tensor_base_change_cocone F S).ι.app j₀ =
        CommRingCat.ofHom b.toRingHom ≫
          (tensor_base_change_cocone F S).ι.app j₀) :
    ∃ (j : J) (f : j₀ ⟶ j),
      CommRingCat.ofHom a.toRingHom ≫
          (tensor_base_change_diagram F S).map f =
      CommRingCat.ofHom b.toRingHom ≫
          (tensor_base_change_diagram F S).map f := by
  classical
  obtain ⟨s, hs⟩ :=
    (Algebra.FiniteType.out : ∃ s : Finset P, Algebra.adjoin S (s : Set P) = ⊤)
  have hgen :
      ∀ p ∈ s,
        (Algebra.TensorProduct.map (AlgHom.id A S) (colimit.ι F j₀).hom) (a p) =
          (Algebra.TensorProduct.map (AlgHom.id A S) (colimit.ι F j₀).hom) (b p) := by
    intro p hp
    -- Proof comment: evaluate the colimit-stage equality on the chosen `S`-algebra generators.
    exact congrArg
      (fun k : CommRingCat.of P ⟶ CommRingCat.of
          (S ⊗[A] ((colimit F : CommAlgCat A) : Type u)) ↦ k.hom p)
      h
  obtain ⟨j, f, hf⟩ :=
    tensorStageEqDescendsFiniteFamily F s (fun p ↦ a p) (fun p ↦ b p) hgen
  let φ : P →ₐ[S] S ⊗[A] ((F.obj j : CommAlgCat A) : Type u) :=
    { toRingHom :=
        (CommRingCat.ofHom a.toRingHom ≫
          (tensor_base_change_diagram F S).map f).hom
      commutes' := by
        intro s
        simp [tensor_base_change_diagram] }
  let ψ : P →ₐ[S] S ⊗[A] ((F.obj j : CommAlgCat A) : Type u) :=
    { toRingHom :=
        (CommRingCat.ofHom b.toRingHom ≫
          (tensor_base_change_diagram F S).map f).hom
      commutes' := by
        intro s
        simp [tensor_base_change_diagram] }
  have hφψ : φ = ψ := by
    -- Proof comment: equality on the chosen finite generating set determines the whole
    -- `S`-algebra map.
    apply AlgHom.ext_of_adjoin_eq_top hs
    intro p hp
    exact hf p hp
  refine ⟨j, f, ?_⟩
  apply CommRingCat.hom_ext
  simpa [φ, ψ] using congrArg AlgHom.toRingHom hφψ

/-- Helper for Chap10 Lemma 10 127 7: finitely many elements of
`S ⊗[A] colimit F` can be represented at a common stage. -/
lemma tensorStageLiftFiniteFamily
    {S : Type u} [CommRing S] [Algebra A S]
    {α : Type u}
    (s : Finset α)
    (z : α → S ⊗[A] ((colimit F : CommAlgCat A) : Type u)) :
    ∃ (j : J) (zj : α → S ⊗[A] ((F.obj j : CommAlgCat A) : Type u)),
      ∀ a ∈ s,
        (Algebra.TensorProduct.map (AlgHom.id A S) (colimit.ι F j).hom) (zj a) = z a := by
  classical
  let c := tensor_base_change_cocone F S
  have hc : IsColimit c := tensor_base_change_cocone_isColimit F S
  let t : Finset {a // a ∈ s} := s.attach
  have hrepr :
      ∀ a : {a // a ∈ s},
        ∃ (j : J) (zj : S ⊗[A] ((F.obj j : CommAlgCat A) : Type u)),
          (Algebra.TensorProduct.map (AlgHom.id A S) (colimit.ι F j).hom) zj = z a := by
    intro a
    obtain ⟨j, xj, hxj⟩ :=
      commRing_filteredColimit_forget_jointly_surjective hc (z a)
    refine ⟨j, xj, ?_⟩
    simpa [c, tensor_base_change_diagram] using hxj.symm
  choose j zj hz using hrepr
  obtain ⟨k, hk⟩ : ∃ k : J, ∀ a : {a // a ∈ s}, Nonempty (j a ⟶ k) := by
    obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (t.image j)
    refine ⟨k, ?_⟩
    intro a
    exact hk (by simpa using Finset.mem_image.mpr ⟨a, by simp [t], rfl⟩)
  let toK : ∀ a : {a // a ∈ s}, j a ⟶ k := fun a ↦ Classical.choice (hk a)
  refine ⟨k, fun a ↦ if ha : a ∈ s then
      (Algebra.TensorProduct.map (AlgHom.id A S) (F.map (toK ⟨a, ha⟩)).hom) (zj ⟨a, ha⟩)
    else 0, ?_⟩
  intro a ha
  have hcomp :
      (Algebra.TensorProduct.map (AlgHom.id A S) (colimit.ι F k).hom).comp
          (Algebra.TensorProduct.map (AlgHom.id A S) (F.map (toK ⟨a, ha⟩)).hom) =
        Algebra.TensorProduct.map (AlgHom.id A S) (colimit.ι F (j ⟨a, ha⟩)).hom :=
    tensorStageMapToColimit_comp F (toK ⟨a, ha⟩)
  calc
    (Algebra.TensorProduct.map (AlgHom.id A S) (colimit.ι F k).hom)
        ((if ha' : a ∈ s then
            (Algebra.TensorProduct.map (AlgHom.id A S) (F.map (toK ⟨a, ha'⟩)).hom) (zj ⟨a, ha'⟩)
          else 0)) =
      (Algebra.TensorProduct.map (AlgHom.id A S) (colimit.ι F k).hom)
        ((Algebra.TensorProduct.map (AlgHom.id A S) (F.map (toK ⟨a, ha⟩)).hom) (zj ⟨a, ha⟩)) := by
          simp [ha]
    _ =
      (Algebra.TensorProduct.map (AlgHom.id A S) (colimit.ι F (j ⟨a, ha⟩)).hom) (zj ⟨a, ha⟩) := by
        simpa [AlgHom.comp_apply] using
          congrArg
            (fun φ :
              S ⊗[A] ((F.obj (j ⟨a, ha⟩) : CommAlgCat A) : Type u) →ₐ[A]
                S ⊗[A] ((colimit F : CommAlgCat A) : Type u) ↦
              φ (zj ⟨a, ha⟩))
            hcomp
    _ = z a := hz ⟨a, ha⟩

/-- Helper for Chap10 Lemma 10 127 7: the tensor-stage diagram with left factor `S` can also be
viewed as a diagram in `Under (CommRingCat.of A)` via its scalar maps. -/
abbrev tensor_base_change_scalar_under_diagram
    (S : Type u) [CommRing S] [Algebra A S] :
    J ⥤ Under (CommRingCat.of A) :=
  Under.lift
    (tensor_base_change_diagram F S)
    (tensor_base_change_scalar_natTrans F S)

/-- Helper for Chap10 Lemma 10 127 7: the colimit tensor cocone respects the scalar maps from
`A`, so it lifts to `Under (CommRingCat.of A)`. -/
lemma tensor_base_change_scalar_under_cocone_factor
    (S : Type u) [CommRing S] [Algebra A S] (j : J) :
    (tensor_base_change_scalar_natTrans F S).app j ≫
        (tensor_base_change_cocone F S).ι.app j =
      CommRingCat.ofHom (algebraMap A (S ⊗[A] ((colimit F : CommAlgCat A) : Type u))) := by
  -- Proof comment: first rewrite the source scalar map as the usual algebra map into the stage
  -- tensor product, then use that the colimit tensor map is an `A`-algebra morphism.
  apply CommRingCat.hom_ext
  ext a
  change
    (Algebra.TensorProduct.map (AlgHom.id A S) (colimit.ι F j).hom)
        (((Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] ↑(F.obj j)).comp
          (algebraMap A S)) a) =
      algebraMap A (S ⊗[A] ((colimit F : CommAlgCat A) : Type u)) a
  rw [tensorIncludeLeft_comp_algebraMap]
  exact (Algebra.TensorProduct.map (AlgHom.id A S) (colimit.ι F j).hom).commutes a

/-- Helper for Chap10 Lemma 10 127 7: the scalar leg of
`tensor_base_change_diagram F S` is the canonical algebra map
`A → S ⊗[A] F.obj j`. -/
lemma tensorBaseChangeScalarNatTrans_app_hom
    (S : Type u) [CommRing S] [Algebra A S] (j : J) :
    ((tensor_base_change_scalar_natTrans F S).app j).hom =
      algebraMap A (S ⊗[A] ((F.obj j : CommAlgCat A) : Type u)) := by
  -- Proof comment: the scalar leg is defined as `algebraMap A S` followed by the left tensor
  -- inclusion, and that composite is the canonical tensor algebra map.
  apply RingHom.ext
  intro a
  change
    (((Algebra.TensorProduct.includeLeftRingHom :
        S →+* S ⊗[A] ((F.obj j : CommAlgCat A) : Type u)).comp
          (algebraMap A S)) a) =
      algebraMap A (S ⊗[A] ((F.obj j : CommAlgCat A) : Type u)) a
  exact congrArg
    (fun φ : A →+* S ⊗[A] ((F.obj j : CommAlgCat A) : Type u) ↦ φ a)
    tensorIncludeLeft_comp_algebraMap

/-- Helper for Chap10 Lemma 10 127 7: the tensor colimit cocone lifts to a cocone in
`Under (CommRingCat.of A)` using the scalar maps from `A`. -/
abbrev tensor_base_change_scalar_under_cocone
    (S : Type u) [CommRing S] [Algebra A S] :
    Cocone (tensor_base_change_scalar_under_diagram F S) :=
  Under.liftCocone
    (tensor_base_change_diagram F S)
    (tensor_base_change_scalar_natTrans F S)
    (tensor_base_change_cocone F S)
    (CommRingCat.ofHom (algebraMap A (S ⊗[A] ((colimit F : CommAlgCat A) : Type u))))
    (tensor_base_change_scalar_under_cocone_factor F S)

/-- Helper for Chap10 Lemma 10 127 7: the scalar-lifted tensor cocone is still colimiting in the
under category over `A`. -/
noncomputable abbrev tensor_base_change_scalar_under_cocone_isColimit
    (S : Type u) [CommRing S] [Algebra A S] :
    IsColimit (tensor_base_change_scalar_under_cocone F S) := by
  -- Proof comment: filtered categories are nonempty, so `Under.isColimitLiftCocone` upgrades the
  -- already-proved ring-level tensor colimit to the under category over `A`.
  letI : Nonempty J := tensor_base_change_index_nonempty
  exact Under.isColimitLiftCocone
    (tensor_base_change_diagram F S)
    (tensor_base_change_scalar_natTrans F S)
    (tensor_base_change_cocone F S)
    (CommRingCat.ofHom (algebraMap A (S ⊗[A] ((colimit F : CommAlgCat A) : Type u))))
    (tensor_base_change_scalar_under_cocone_factor F S)
    (tensor_base_change_cocone_isColimit F S)

/-- Helper for Chap10 Lemma 10 127 7: if `C` is finitely presented over `A`, then the under object
`Under.mk (CommRingCat.ofHom (algebraMap A C))` is finitely presentable in
`Under (CommRingCat.of A)`.
-/
lemma underMkIsFinitelyPresentableNativeOfFinitePresentation
    [Algebra.FinitePresentation A C] :
    IsFinitelyPresentable.{u}
      (Under.mk (CommRingCat.ofHom (algebraMap A C) :
        CommRingCat.of A ⟶ CommRingCat.of C)) := by
  have hfp : (algebraMap A C).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr inferInstance
  let S : Under (CommRingCat.of A) :=
    Under.mk (CommRingCat.ofHom (algebraMap A C) :
      CommRingCat.of A ⟶ CommRingCat.of C)
  -- Proof comment: mathlib's owner theorem already packages finite presentation of `algebraMap A C`
  -- as finite presentability of the corresponding under-object in the native universe.
  simpa [S] using CommRingCat.isFinitelyPresentable_under (CommRingCat.of A) S hfp

/-- Helper for Chap10 Lemma 10 127 7: after forgetting commutative-ring structure, the
tensor-base-change cocone is still a colimit cocone in `Type`.
-/
noncomputable def tensorBaseChangeForgetCoconeIsColimit
    (S : Type u) [CommRing S] [Algebra A S] :
    IsColimit ((forget CommRingCat).mapCocone (tensor_base_change_cocone F S)) := by
  let c := tensor_base_change_cocone F S
  have hc : IsColimit c := tensor_base_change_cocone_isColimit F S
  -- Route correction: instead of rebuilding a global forgetful-preservation instance, certify
  -- this specific forgotten cocone directly from stagewise surjectivity and equality descent.
  refine Types.FilteredColimit.isColimitOf'
    (F := tensor_base_change_diagram F S ⋙ forget CommRingCat) ((forget CommRingCat).mapCocone c)
    ?_ ?_
  · intro z
    -- Proof comment: every tensor element over the colimit already comes from some stage.
    exact commRing_filteredColimit_forget_jointly_surjective hc z
  · intro j x y hxy
    -- Proof comment: equality of two elements from one tensor stage descends to equality after
    -- one later transition, which is exactly the injectivity criterion for filtered colimits.
    obtain ⟨k, f, hf⟩ := tensorStageEqDescends (F := F) (S := S) x y (by
      simpa [c, tensor_base_change_cocone, tensor_base_change_diagram] using hxy)
    exact ⟨k, f, by simpa [c, tensor_base_change_diagram] using hf⟩

/-- Helper for Chap10 Lemma 10 127 7: the forgetful functor preserves the specific tensor
base-change colimit cocone needed for the finite-presentation descent argument.
-/
lemma tensorBaseChangeDiagramForgetPreservesColimit
    (S : Type u) [CommRing S] [Algebra A S] :
    PreservesColimit (tensor_base_change_diagram F S) (forget CommRingCat) := by
  -- Proof comment: once the chosen tensor cocone is a colimit after forgetting to `Type`,
  -- preservation for this specific diagram follows by cocone uniqueness.
  exact preservesColimit_of_preserves_colimit_cocone
    (tensor_base_change_cocone_isColimit F S)
    (tensorBaseChangeForgetCoconeIsColimit F S)

omit [IsFiltered J] in
/-- Helper for Chap10 Lemma 10 127 7: the stage-to-colimit tensor map sends `0` to `0`. -/
lemma tensorStageMapToColimit_zero
    {S : Type u} [CommRing S] [Algebra A S] {j : J} :
    (Algebra.TensorProduct.map (AlgHom.id A S) (colimit.ι F j).hom) 0 = 0 := by
  -- Proof comment: every algebra morphism preserves zero.
  simp

/-- Chap10 Lemma 10 127 7 (1): if `B` is of finite type over `A` and two `A`-algebra maps
`u, u' : B → C` induce the same base-changed map
`B ⊗[A] colimit F → C ⊗[A] colimit F`, then they already induce the same base-changed map
at some stage `j`. -/
@[stacks 05N8]
theorem finite_type_map_equality_descends
    [Algebra.FiniteType A B]
    (u u' : B →ₐ[A] C)
    (h :
      Algebra.TensorProduct.map u
          (AlgHom.id A (((colimit F : CommAlgCat A) : Type u))) =
        Algebra.TensorProduct.map u'
          (AlgHom.id A (((colimit F : CommAlgCat A) : Type u)))) :
  ∃ j : J,
      Algebra.TensorProduct.map u
          (AlgHom.id A (((F.obj j : CommAlgCat A) : Type u))) =
        Algebra.TensorProduct.map u'
          (AlgHom.id A (((F.obj j : CommAlgCat A) : Type u))) := by
  classical
  letI : Nonempty J := tensor_base_change_index_nonempty
  let j₀ : J := Classical.choice ‹Nonempty J›
  obtain ⟨s, hs⟩ :=
    (Algebra.FiniteType.out : ∃ s : Finset B, Algebra.adjoin A (s : Set B) = ⊤)
  have hgen :
      ∀ b ∈ s,
        (Algebra.TensorProduct.map (AlgHom.id A C) (colimit.ι F j₀).hom)
            ((Algebra.TensorProduct.includeLeft : C →ₐ[A]
              C ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u)) (u b)) =
          (Algebra.TensorProduct.map (AlgHom.id A C) (colimit.ι F j₀).hom)
            ((Algebra.TensorProduct.includeLeft : C →ₐ[A]
              C ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u)) (u' b)) := by
    intro b hb
    -- Proof comment: evaluate the colimit-level equality on the left tensor generators.
    have hb' := congrArg
      (fun φ :
        B ⊗[A] ((colimit F : CommAlgCat A) : Type u) →ₐ[A]
          C ⊗[A] ((colimit F : CommAlgCat A) : Type u) ↦
          φ ((Algebra.TensorProduct.includeLeft :
            B →ₐ[A] B ⊗[A] ((colimit F : CommAlgCat A) : Type u)) b)) h
    simpa [Algebra.TensorProduct.map_comp_includeLeft] using hb'
  obtain ⟨j, f, hf⟩ :=
    tensorStageEqDescendsFiniteFamily F s
      (fun b ↦ (Algebra.TensorProduct.includeLeft :
        C →ₐ[A] C ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u)) (u b))
      (fun b ↦ (Algebra.TensorProduct.includeLeft :
        C →ₐ[A] C ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u)) (u' b))
      hgen
  refine ⟨j, ?_⟩
  -- Proof comment: equality on a finite generating set forces equality of the whole tensor maps.
  apply tensor_base_change_algHom_ext
  · have hleft :
        (Algebra.TensorProduct.includeLeft :
            C →ₐ[A] C ⊗[A] ((F.obj j : CommAlgCat A) : Type u)).comp u =
          (Algebra.TensorProduct.includeLeft :
            C →ₐ[A] C ⊗[A] ((F.obj j : CommAlgCat A) : Type u)).comp u' := by
      apply AlgHom.ext_of_adjoin_eq_top hs
      intro b hb
      have hbEq := hf b hb
      simpa [Functor.map_comp, Algebra.TensorProduct.map_comp,
        Algebra.TensorProduct.map_comp_includeLeft] using hbEq
    simpa [Algebra.TensorProduct.map_comp_includeLeft] using hleft
  · ext r
    simp

/-- Chap10 Lemma 10 127 7 (2): if `C` is of finite type over `A` and the base change of
`u : B → C` to the filtered colimit algebra `colimit F` is surjective, then the base change of
`u` to some stage `F.obj j` is already surjective. -/
@[stacks 05N8]
theorem finite_type_surjectivity_descends
    [Algebra.FiniteType A C]
    (u : B →ₐ[A] C)
    (h :
      Function.Surjective
        (Algebra.TensorProduct.map u
          (AlgHom.id A (((colimit F : CommAlgCat A) : Type u))))) :
    ∃ j : J,
      Function.Surjective
        (Algebra.TensorProduct.map u
          (AlgHom.id A (((F.obj j : CommAlgCat A) : Type u)))) := by
  classical
  letI : Algebra B C := u.toRingHom.toAlgebra
  letI : Algebra.FiniteType B C :=
    Algebra.FiniteType.of_restrictScalars_finiteType A B C
  obtain ⟨s, hs⟩ :=
    (Algebra.FiniteType.out : ∃ s : Finset C, Algebra.adjoin B (s : Set C) = ⊤)
  let preim :
      C → B ⊗[A] ((colimit F : CommAlgCat A) : Type u) := fun c ↦
    if hc : c ∈ s then
      Classical.choose (h ((Algebra.TensorProduct.includeLeft :
        C →ₐ[A] C ⊗[A] ((colimit F : CommAlgCat A) : Type u)) c))
    else 0
  have hpreim :
      ∀ c ∈ s,
        (Algebra.TensorProduct.map u
          (AlgHom.id A (((colimit F : CommAlgCat A) : Type u)))) (preim c) =
            (Algebra.TensorProduct.includeLeft :
              C →ₐ[A] C ⊗[A] ((colimit F : CommAlgCat A) : Type u)) c := by
    intro c hc
    simpa [preim, hc] using Classical.choose_spec
      (h ((Algebra.TensorProduct.includeLeft :
        C →ₐ[A] C ⊗[A] ((colimit F : CommAlgCat A) : Type u)) c))
  obtain ⟨j₀, zj₀, hzj₀⟩ :=
    tensorStageLiftFiniteFamily F s preim
  have hdef :
      ∀ c ∈ s,
        (Algebra.TensorProduct.map (AlgHom.id A C) (colimit.ι F j₀).hom)
            ((Algebra.TensorProduct.map u
              (AlgHom.id A (((F.obj j₀ : CommAlgCat A) : Type u)))) (zj₀ c)) =
          (Algebra.TensorProduct.map (AlgHom.id A C) (colimit.ι F j₀).hom)
            ((Algebra.TensorProduct.includeLeft :
              C →ₐ[A] C ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u)) c) := by
    intro c hc
    -- Proof comment: the lifted stage representative maps to the chosen colimit preimage of
    -- `c ⊗ 1`, hence the stage defect vanishes after passage to the colimit.
    have htransport :
        (Algebra.TensorProduct.map (AlgHom.id A C) (colimit.ι F j₀).hom).comp
            (Algebra.TensorProduct.map u
              (AlgHom.id A (((F.obj j₀ : CommAlgCat A) : Type u)))) =
          (Algebra.TensorProduct.map u
            (AlgHom.id A (((colimit F : CommAlgCat A) : Type u)))).comp
              (Algebra.TensorProduct.map (AlgHom.id A B) (colimit.ι F j₀).hom) := by
      simpa using tensor_map_exchange u (colimit.ι F j₀).hom
    calc
      (Algebra.TensorProduct.map (AlgHom.id A C) (colimit.ι F j₀).hom)
          ((Algebra.TensorProduct.map u
            (AlgHom.id A (((F.obj j₀ : CommAlgCat A) : Type u)))) (zj₀ c)) =
        (Algebra.TensorProduct.map u
          (AlgHom.id A (((colimit F : CommAlgCat A) : Type u)))) ((Algebra.TensorProduct.map
            (AlgHom.id A B) (colimit.ι F j₀).hom) (zj₀ c)) := by
              simpa using congrArg
                (fun φ :
                  B ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u) →ₐ[A]
                    C ⊗[A] ((colimit F : CommAlgCat A) : Type u) ↦
                      φ (zj₀ c)) htransport
      _ = (Algebra.TensorProduct.map u
            (AlgHom.id A (((colimit F : CommAlgCat A) : Type u)))) (preim c) := by
              rw [hzj₀ c hc]
      _ = (Algebra.TensorProduct.includeLeft :
            C →ₐ[A] C ⊗[A] ((colimit F : CommAlgCat A) : Type u)) c := hpreim c hc
      _ =
        (Algebra.TensorProduct.map (AlgHom.id A C) (colimit.ι F j₀).hom)
          ((Algebra.TensorProduct.includeLeft :
            C →ₐ[A] C ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u)) c) := by
              simp
  obtain ⟨j, f, hf⟩ :=
    tensorStageEqDescendsFiniteFamily F s
      (fun c ↦
        (Algebra.TensorProduct.map u
          (AlgHom.id A (((F.obj j₀ : CommAlgCat A) : Type u)))) (zj₀ c))
      (fun c ↦
        (Algebra.TensorProduct.includeLeft :
          C →ₐ[A] C ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u)) c)
      hdef
  refine ⟨j, ?_⟩
  -- Proof comment: after transporting the lifted preimages to the common stage `j`, each chosen
  -- `B`-generator of `C` already has a stagewise tensor preimage.
  apply tensor_map_surjective_of_generator_preimages u s hs
  intro c hc
  refine ⟨(Algebra.TensorProduct.map (AlgHom.id A B) (F.map f).hom) (zj₀ c), ?_⟩
  have hcEq := hf c hc
  have htransport :
      (Algebra.TensorProduct.map u
        (AlgHom.id A (((F.obj j : CommAlgCat A) : Type u)))).comp
          (Algebra.TensorProduct.map (AlgHom.id A B) (F.map f).hom) =
        (Algebra.TensorProduct.map (AlgHom.id A C) (F.map f).hom).comp
          (Algebra.TensorProduct.map u
            (AlgHom.id A (((F.obj j₀ : CommAlgCat A) : Type u)))) := by
    simpa using (tensor_map_exchange u (F.map f).hom).symm
  calc
    (Algebra.TensorProduct.map u (AlgHom.id A (((F.obj j : CommAlgCat A) : Type u))))
        ((Algebra.TensorProduct.map (AlgHom.id A B) (F.map f).hom) (zj₀ c)) =
      (Algebra.TensorProduct.map (AlgHom.id A C) (F.map f).hom)
        ((Algebra.TensorProduct.map u (AlgHom.id A (((F.obj j₀ : CommAlgCat A) : Type u))))
          (zj₀ c)) := by
            simpa using congrArg
              (fun φ :
                B ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u) →ₐ[A]
                  C ⊗[A] ((F.obj j : CommAlgCat A) : Type u) ↦
                    φ (zj₀ c)) htransport
    _ =
      (Algebra.TensorProduct.map (AlgHom.id A C) (F.map f).hom)
        ((Algebra.TensorProduct.includeLeft :
          C →ₐ[A] C ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u)) c) := hcEq
    _ = (Algebra.TensorProduct.includeLeft :
          C →ₐ[A] C ⊗[A] ((F.obj j : CommAlgCat A) : Type u)) c := by
          simp

/-- Chap10 Lemma 10 127 7 (3): if `C` is finitely presented over `A`, then every
`colimit F`-algebra map `v : C ⊗[A] colimit F → B ⊗[A] colimit F` descends to some stage
`F.obj j`. -/
@[stacks 05N8]
theorem finite_presentation_hom_descends
    [Algebra.FinitePresentation A C]
    (v :
      C ⊗[A] ((colimit F : CommAlgCat A) : Type u) →ₐ[((colimit F : CommAlgCat A) : Type u)]
        B ⊗[A] ((colimit F : CommAlgCat A) : Type u)) :
    ∃ (j : J)
        (v_j :
          C ⊗[A] ((F.obj j : CommAlgCat A) : Type u) →ₐ[((F.obj j : CommAlgCat A) : Type u)]
            B ⊗[A] ((F.obj j : CommAlgCat A) : Type u)),
        (Algebra.TensorProduct.map (AlgHom.id A B) (colimit.ι F j).hom).comp
          (v_j.restrictScalars A) =
        (v.restrictScalars A).comp
        (Algebra.TensorProduct.map (AlgHom.id A C) (colimit.ι F j).hom) := by
  let vLeftColim : C →ₐ[A] B ⊗[A] ((colimit F : CommAlgCat A) : Type u) :=
    (v.restrictScalars A).comp (Algebra.TensorProduct.includeLeft :
      C →ₐ[A] C ⊗[A] ((colimit F : CommAlgCat A) : Type u))
  let g : CommRingCat.of C ⟶ CommRingCat.of (B ⊗[A] ((colimit F : CommAlgCat A) : Type u)) :=
    CommRingCat.ofHom vLeftColim.toRingHom
  have hgA :
      ∀ i : J,
        (CommRingCat.ofHom (algebraMap A C) :
          CommRingCat.of A ⟶ CommRingCat.of C) ≫ g =
          (tensor_base_change_scalar_natTrans F B).app i ≫
            (tensor_base_change_cocone F B).ι.app i := by
    intro i
    -- Proof comment: both composites are the canonical scalar map
    -- `A → B ⊗[A] colimit F`, once we use that `vLeftColim` is an `A`-algebra morphism.
    calc
      (CommRingCat.ofHom (algebraMap A C) :
          CommRingCat.of A ⟶ CommRingCat.of C) ≫ g =
        CommRingCat.ofHom (algebraMap A (B ⊗[A] ((colimit F : CommAlgCat A) : Type u))) := by
          apply CommRingCat.hom_ext
          ext a
          exact vLeftColim.commutes a
      _ =
        (tensor_base_change_scalar_natTrans F B).app i ≫
          (tensor_base_change_cocone F B).ι.app i := by
            symm
            exact tensor_base_change_scalar_under_cocone_factor F B i
  have hfp : (algebraMap A C).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr inferInstance
  letI :
      PreservesColimit (tensor_base_change_diagram F B) (forget CommRingCat) :=
    tensorBaseChangeDiagramForgetPreservesColimit F B
  obtain ⟨j, g', hgA', hg⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
      (R := CommRingCat.of A)
      (F := tensor_base_change_diagram F B)
      (α := tensor_base_change_scalar_natTrans F B)
      (f := (CommRingCat.ofHom (algebraMap A C) :
        CommRingCat.of A ⟶ CommRingCat.of C))
      (c := tensor_base_change_cocone F B)
      (hc := tensor_base_change_cocone_isColimit F B)
      hfp g hgA
  let vLeftj : C →ₐ[A] B ⊗[A] ((F.obj j : CommAlgCat A) : Type u) :=
    { __ := g'.hom
      commutes' := by
        -- Proof comment: the descended ring hom lies over `A`, so its composite with
        -- `algebraMap A C` is the canonical stage scalar map.
        intro a
        have hw := CommRingCat.hom_ext_iff.mp hgA'
        change (g'.hom.comp (algebraMap A C)) a =
          (algebraMap A (B ⊗[A] ((F.obj j : CommAlgCat A) : Type u))) a
        simpa [tensorBaseChangeScalarNatTrans_app_hom,
          CommRingCat.hom_comp] using DFunLike.congr_fun hw a }
  have hvLeftj :
      (Algebra.TensorProduct.map (AlgHom.id A B) (colimit.ι F j).hom).comp vLeftj =
        vLeftColim := by
    -- Proof comment: the factorization through stage `j` is exactly the equality produced by the
    -- colimit factorization of the ring map `g`, rewritten on elements of `C`.
    apply AlgHom.ext
    intro c
    have hw := CommRingCat.hom_ext_iff.mp hg
    simpa [vLeftj, vLeftColim, CommRingCat.hom_comp, tensor_base_change_cocone,
      tensor_base_change_diagram, AlgHom.comp_apply] using
      (DFunLike.congr_fun hw c).symm
  let v_j :
      C ⊗[A] ((F.obj j : CommAlgCat A) : Type u) →ₐ[((F.obj j : CommAlgCat A) : Type u)]
        B ⊗[A] ((F.obj j : CommAlgCat A) : Type u) :=
    { __ := Algebra.TensorProduct.productMap vLeftj
        (Algebra.TensorProduct.includeRight :
          ((F.obj j : CommAlgCat A) : Type u) →ₐ[A]
            B ⊗[A] ((F.obj j : CommAlgCat A) : Type u))
      commutes' := by
        -- Proof comment: `productMap` fixes the right tensor factor, so it is already linear over
        -- the stage ring.
        intro r
        change
          (Algebra.TensorProduct.productMap vLeftj
            (Algebra.TensorProduct.includeRight :
              ((F.obj j : CommAlgCat A) : Type u) →ₐ[A]
                B ⊗[A] ((F.obj j : CommAlgCat A) : Type u)))
            ((Algebra.TensorProduct.includeRight :
              ((F.obj j : CommAlgCat A) : Type u) →ₐ[A]
                C ⊗[A] ((F.obj j : CommAlgCat A) : Type u)) r) =
            (Algebra.TensorProduct.includeRight :
              ((F.obj j : CommAlgCat A) : Type u) →ₐ[A]
                B ⊗[A] ((F.obj j : CommAlgCat A) : Type u)) r
        simpa using tensorProductProductMap_commutesStageScalars_apply vLeftj r }
  have hvj_left :
      (v_j.restrictScalars A).comp (Algebra.TensorProduct.includeLeft :
        C →ₐ[A] C ⊗[A] ((F.obj j : CommAlgCat A) : Type u)) =
        vLeftj := by
    ext c
    change
      (Algebra.TensorProduct.productMap vLeftj
        (Algebra.TensorProduct.includeRight :
          ((F.obj j : CommAlgCat A) : Type u) →ₐ[A]
            B ⊗[A] ((F.obj j : CommAlgCat A) : Type u)))
        ((Algebra.TensorProduct.includeLeft :
          C →ₐ[A] C ⊗[A] ((F.obj j : CommAlgCat A) : Type u)) c) =
        vLeftj c
    simpa using
      (Algebra.TensorProduct.productMap_left_apply
        vLeftj
        (Algebra.TensorProduct.includeRight :
          ((F.obj j : CommAlgCat A) : Type u) →ₐ[A]
            B ⊗[A] ((F.obj j : CommAlgCat A) : Type u))
        c)
  have hvj_right :
      (v_j.restrictScalars A).comp (Algebra.TensorProduct.includeRight :
        ((F.obj j : CommAlgCat A) : Type u) →ₐ[A]
          C ⊗[A] ((F.obj j : CommAlgCat A) : Type u)) =
        (Algebra.TensorProduct.includeRight :
          ((F.obj j : CommAlgCat A) : Type u) →ₐ[A]
            B ⊗[A] ((F.obj j : CommAlgCat A) : Type u)) := by
    ext r
    change
      (Algebra.TensorProduct.productMap vLeftj
        (Algebra.TensorProduct.includeRight :
          ((F.obj j : CommAlgCat A) : Type u) →ₐ[A]
            B ⊗[A] ((F.obj j : CommAlgCat A) : Type u)))
        ((Algebra.TensorProduct.includeRight :
          ((F.obj j : CommAlgCat A) : Type u) →ₐ[A]
            C ⊗[A] ((F.obj j : CommAlgCat A) : Type u)) r) =
        (Algebra.TensorProduct.includeRight :
          ((F.obj j : CommAlgCat A) : Type u) →ₐ[A]
            B ⊗[A] ((F.obj j : CommAlgCat A) : Type u)) r
    simpa using
      (Algebra.TensorProduct.productMap_right_apply
        vLeftj
        (Algebra.TensorProduct.includeRight :
          ((F.obj j : CommAlgCat A) : Type u) →ₐ[A]
            B ⊗[A] ((F.obj j : CommAlgCat A) : Type u))
        r)
  refine ⟨j, v_j, ?_⟩
  -- Proof comment: the descended tensor map agrees with the colimit tensor map on both tensor
  -- generators, so tensor extensionality identifies the two algebra morphisms.
  apply tensor_base_change_algHom_ext
  · calc
      ((Algebra.TensorProduct.map (AlgHom.id A B) (colimit.ι F j).hom).comp
          (v_j.restrictScalars A)).comp
          (Algebra.TensorProduct.includeLeft :
            C →ₐ[A] C ⊗[A] ((F.obj j : CommAlgCat A) : Type u)) =
        (Algebra.TensorProduct.map (AlgHom.id A B) (colimit.ι F j).hom).comp vLeftj := by
          rw [AlgHom.comp_assoc, hvj_left]
      _ = vLeftColim := hvLeftj
      _ =
        ((v.restrictScalars A).comp
          (Algebra.TensorProduct.map (AlgHom.id A C) (colimit.ι F j).hom)).comp
            (Algebra.TensorProduct.includeLeft :
              C →ₐ[A] C ⊗[A] ((F.obj j : CommAlgCat A) : Type u)) := by
              rw [AlgHom.comp_assoc, Algebra.TensorProduct.map_comp_includeLeft]
              rfl
  · ext r
    calc
      (((Algebra.TensorProduct.map (AlgHom.id A B) (colimit.ι F j).hom).comp
            (v_j.restrictScalars A)).comp
          (Algebra.TensorProduct.includeRight :
            ((F.obj j : CommAlgCat A) : Type u) →ₐ[A]
              C ⊗[A] ((F.obj j : CommAlgCat A) : Type u))) r =
        ((Algebra.TensorProduct.includeRight :
          ((colimit F : CommAlgCat A) : Type u) →ₐ[A]
            B ⊗[A] ((colimit F : CommAlgCat A) : Type u)) ((colimit.ι F j).hom r)) := by
          rw [AlgHom.comp_assoc, hvj_right]
          simp [Algebra.TensorProduct.map_comp_includeRight]
      _ = v ((Algebra.TensorProduct.includeRight :
          ((colimit F : CommAlgCat A) : Type u) →ₐ[A]
            C ⊗[A] ((colimit F : CommAlgCat A) : Type u)) ((colimit.ι F j).hom r)) := by
          symm
          simpa [Algebra.TensorProduct.algebraMap_eq_includeRight] using
            v.commutes ((colimit.ι F j).hom r)
      _ =
        (((v.restrictScalars A).comp
              (Algebra.TensorProduct.map (AlgHom.id A C) (colimit.ι F j).hom)).comp
            (Algebra.TensorProduct.includeRight :
              ((F.obj j : CommAlgCat A) : Type u) →ₐ[A]
                C ⊗[A] ((F.obj j : CommAlgCat A) : Type u))) r := by
          simp [AlgHom.comp_apply]

/-- Helper for Chap10 Lemma 10 127 7: the descended left tensor-factor map becomes a left inverse
to `u` once it fixes a finite set of algebra generators after transport. -/
lemma tensorLeftFactorInverseOfGeneratorTransport
    {R₀ R : Type u} [CommRing R₀] [CommRing R] [Algebra A R₀] [Algebra A R]
    (u : B →ₐ[A] C)
    (vj0 : C ⊗[A] R₀ →ₐ[A] B ⊗[A] R₀)
    (uj0 : B ⊗[A] R₀ →ₐ[A] C ⊗[A] R₀)
    (mapBk : B ⊗[A] R₀ →ₐ[A] B ⊗[A] R)
    (huj0_left :
      uj0.comp (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R₀) =
        (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R₀).comp u)
    (hmapBk_left :
      mapBk.comp (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R₀) =
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R))
    (sB : Finset B) (hsB : Algebra.adjoin A (sB : Set B) = ⊤)
    (hBstage :
      ∀ b ∈ sB,
        mapBk ((vj0.comp uj0)
          ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R₀) b)) =
        mapBk ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R₀) b)) :
    let vLeftj0 : C →ₐ[A] B ⊗[A] R₀ :=
      vj0.comp (Algebra.TensorProduct.includeLeft :
        C →ₐ[A] C ⊗[A] R₀)
    let vLeftk : C →ₐ[A] B ⊗[A] R := mapBk.comp vLeftj0
    vLeftk.comp u =
      (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R) := by
  apply AlgHom.ext_of_adjoin_eq_top hsB
  intro b hb
  have huj0_left_apply :
      uj0 ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R₀) b) =
        (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R₀) (u b) := by
    simpa [AlgHom.comp_apply] using
      congrArg (fun φ : B →ₐ[A] C ⊗[A] R₀ ↦ φ b) huj0_left
  have hmapBk_left_apply :
      mapBk ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R₀) b) =
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R) b := by
    simpa [AlgHom.comp_apply] using
      congrArg (fun φ : B →ₐ[A] B ⊗[A] R ↦ φ b) hmapBk_left
  calc
    ((mapBk.comp (vj0.comp (Algebra.TensorProduct.includeLeft :
        C →ₐ[A] C ⊗[A] R₀))).comp u) b =
      mapBk (vj0 ((Algebra.TensorProduct.includeLeft :
        C →ₐ[A] C ⊗[A] R₀) (u b))) := by
        simp [AlgHom.comp_apply]
    _ =
      mapBk ((vj0.comp uj0)
        ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R₀) b)) := by
          simpa [AlgHom.comp_apply] using
            congrArg (fun z : C ⊗[A] R₀ ↦ mapBk (vj0 z)) huj0_left_apply.symm
    _ = mapBk ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R₀) b) := hBstage b hb
    _ = (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R) b := hmapBk_left_apply

/-- Helper for Chap10 Lemma 10 127 7: the descended left tensor-factor map becomes a right inverse
to `u` once it fixes a finite set of algebra generators after transport. -/
lemma tensorRightFactorInverseOfGeneratorTransport
    {R₀ R : Type u} [CommRing R₀] [CommRing R] [Algebra A R₀] [Algebra A R]
    (vj0A : C ⊗[A] R₀ →ₐ[A] B ⊗[A] R₀)
    (uj0 : B ⊗[A] R₀ →ₐ[A] C ⊗[A] R₀)
    (mapBk : B ⊗[A] R₀ →ₐ[A] B ⊗[A] R)
    (mapCk : C ⊗[A] R₀ →ₐ[A] C ⊗[A] R)
    (uk : B ⊗[A] R →ₐ[A] C ⊗[A] R)
    (htransport : uk.comp mapBk = mapCk.comp uj0)
    (hmapCk_left :
      mapCk.comp (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R₀) =
        (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R))
    (sC : Finset C) (hsC : Algebra.adjoin A (sC : Set C) = ⊤)
    (hCstage :
      ∀ c ∈ sC,
        mapCk ((uj0.comp vj0A)
          ((Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R₀) c)) =
        mapCk ((Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R₀) c)) :
    uk.comp
        (mapBk.comp (vj0A.comp (Algebra.TensorProduct.includeLeft :
          C →ₐ[A] C ⊗[A] R₀))) =
      (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R) := by
  apply AlgHom.ext_of_adjoin_eq_top hsC
  intro c hc
  have hmapCk_left_apply :
      mapCk ((Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R₀) c) =
        (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R) c := by
    simpa [AlgHom.comp_apply] using
      congrArg (fun φ : C →ₐ[A] C ⊗[A] R ↦ φ c) hmapCk_left
  calc
    (uk.comp (mapBk.comp (vj0A.comp (Algebra.TensorProduct.includeLeft :
        C →ₐ[A] C ⊗[A] R₀)))) c =
      uk (mapBk (vj0A
        ((Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R₀) c))) := by
        simp [AlgHom.comp_apply]
    _ =
      mapCk ((uj0.comp vj0A)
        ((Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R₀) c)) := by
        simpa [AlgHom.comp_apply] using
          congrArg
            (fun φ : B ⊗[A] R₀ →ₐ[A] C ⊗[A] R ↦
              φ (vj0A
                ((Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R₀) c)))
            htransport
    _ = mapCk ((Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R₀) c) := hCstage c hc
    _ = (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R) c := hmapCk_left_apply

/-- Helper for Chap10 Lemma 10 127 7: transporting a colimit left inverse back to one stage makes
`vj0A.comp uj0` fix the left tensor generators of `B` after mapping to the colimit stage. -/
lemma tensorLeftGeneratorTransportEqOfColimitLeftInverse
    {R₀ R : Type u} [CommRing R₀] [CommRing R] [Algebra A R₀] [Algebra A R]
    (vj0A : C ⊗[A] R₀ →ₐ[A] B ⊗[A] R₀)
    (uj0 : B ⊗[A] R₀ →ₐ[A] C ⊗[A] R₀)
    (mapB : B ⊗[A] R₀ →ₐ[A] B ⊗[A] R)
    (mapC : C ⊗[A] R₀ →ₐ[A] C ⊗[A] R)
    (uR : B ⊗[A] R →ₐ[A] C ⊗[A] R)
    (vR : C ⊗[A] R →ₐ[A] B ⊗[A] R)
    (hv : mapB.comp vj0A = vR.comp mapC)
    (hu : mapC.comp uj0 = uR.comp mapB)
    (hleft : vR.comp uR = AlgHom.id A _)
    (b : B) :
    mapB ((vj0A.comp uj0)
      ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R₀) b)) =
      mapB ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R₀) b) := by
  have hv_apply :
      mapB (vj0A (uj0 ((Algebra.TensorProduct.includeLeft :
          B →ₐ[A] B ⊗[A] R₀) b))) =
        vR (mapC (uj0 ((Algebra.TensorProduct.includeLeft :
          B →ₐ[A] B ⊗[A] R₀) b))) := by
    simpa [AlgHom.comp_apply] using
      congrArg
        (fun φ :
          C ⊗[A] R₀ →ₐ[A] B ⊗[A] R ↦
            φ (uj0
              ((Algebra.TensorProduct.includeLeft :
                B →ₐ[A] B ⊗[A] R₀) b)))
        hv
  have hu_apply :
      mapC (uj0 ((Algebra.TensorProduct.includeLeft :
          B →ₐ[A] B ⊗[A] R₀) b)) =
        uR (mapB ((Algebra.TensorProduct.includeLeft :
          B →ₐ[A] B ⊗[A] R₀) b)) := by
    simpa [AlgHom.comp_apply] using
      congrArg
        (fun φ :
          B ⊗[A] R₀ →ₐ[A] C ⊗[A] R ↦
            φ ((Algebra.TensorProduct.includeLeft :
              B →ₐ[A] B ⊗[A] R₀) b))
        hu
  have hleft_apply :
      vR (uR (mapB ((Algebra.TensorProduct.includeLeft :
          B →ₐ[A] B ⊗[A] R₀) b))) =
        mapB ((Algebra.TensorProduct.includeLeft :
          B →ₐ[A] B ⊗[A] R₀) b) := by
    simpa [AlgHom.comp_apply] using
      congrArg
        (fun φ :
          B ⊗[A] R →ₐ[A] B ⊗[A] R ↦
            φ (mapB ((Algebra.TensorProduct.includeLeft :
              B →ₐ[A] B ⊗[A] R₀) b)))
        hleft
  calc
    mapB ((vj0A.comp uj0)
        ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R₀) b)) =
      mapB (vj0A (uj0 ((Algebra.TensorProduct.includeLeft :
        B →ₐ[A] B ⊗[A] R₀) b))) := by
          simp [AlgHom.comp_apply]
    _ = vR (mapC (uj0 ((Algebra.TensorProduct.includeLeft :
          B →ₐ[A] B ⊗[A] R₀) b))) := hv_apply
    _ = vR (uR (mapB ((Algebra.TensorProduct.includeLeft :
          B →ₐ[A] B ⊗[A] R₀) b))) := by rw [hu_apply]
    _ = mapB ((Algebra.TensorProduct.includeLeft :
          B →ₐ[A] B ⊗[A] R₀) b) := hleft_apply

/-- Helper for Chap10 Lemma 10 127 7: transporting a colimit right inverse back to one stage makes
`uj0.comp vj0A` fix the left tensor generators of `C` after mapping to the colimit stage. -/
lemma tensorRightGeneratorTransportEqOfColimitRightInverse
    {R₀ R : Type u} [CommRing R₀] [CommRing R] [Algebra A R₀] [Algebra A R]
    (vj0A : C ⊗[A] R₀ →ₐ[A] B ⊗[A] R₀)
    (uj0 : B ⊗[A] R₀ →ₐ[A] C ⊗[A] R₀)
    (mapB : B ⊗[A] R₀ →ₐ[A] B ⊗[A] R)
    (mapC : C ⊗[A] R₀ →ₐ[A] C ⊗[A] R)
    (uR : B ⊗[A] R →ₐ[A] C ⊗[A] R)
    (vR : C ⊗[A] R →ₐ[A] B ⊗[A] R)
    (hv : mapB.comp vj0A = vR.comp mapC)
    (hu : mapC.comp uj0 = uR.comp mapB)
    (hright : uR.comp vR = AlgHom.id A _)
    (c : C) :
    mapC ((uj0.comp vj0A)
      ((Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R₀) c)) =
      mapC ((Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R₀) c) := by
  have hv_apply :
      mapB (vj0A ((Algebra.TensorProduct.includeLeft :
          C →ₐ[A] C ⊗[A] R₀) c)) =
        vR (mapC ((Algebra.TensorProduct.includeLeft :
          C →ₐ[A] C ⊗[A] R₀) c)) := by
    simpa [AlgHom.comp_apply] using
      congrArg
        (fun φ :
          C ⊗[A] R₀ →ₐ[A] B ⊗[A] R ↦
            φ ((Algebra.TensorProduct.includeLeft :
              C →ₐ[A] C ⊗[A] R₀) c))
        hv
  have hu_apply :
      mapC (uj0 (vj0A ((Algebra.TensorProduct.includeLeft :
          C →ₐ[A] C ⊗[A] R₀) c))) =
        uR (mapB (vj0A ((Algebra.TensorProduct.includeLeft :
          C →ₐ[A] C ⊗[A] R₀) c))) := by
    simpa [AlgHom.comp_apply] using
      congrArg
        (fun φ :
          B ⊗[A] R₀ →ₐ[A] C ⊗[A] R ↦
            φ (vj0A
              ((Algebra.TensorProduct.includeLeft :
                C →ₐ[A] C ⊗[A] R₀) c)))
        hu
  have hright_apply :
      uR (vR (mapC ((Algebra.TensorProduct.includeLeft :
          C →ₐ[A] C ⊗[A] R₀) c))) =
        mapC ((Algebra.TensorProduct.includeLeft :
          C →ₐ[A] C ⊗[A] R₀) c) := by
    simpa [AlgHom.comp_apply] using
      congrArg
        (fun φ :
          C ⊗[A] R →ₐ[A] C ⊗[A] R ↦
            φ (mapC ((Algebra.TensorProduct.includeLeft :
              C →ₐ[A] C ⊗[A] R₀) c)))
        hright
  calc
    mapC ((uj0.comp vj0A)
        ((Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R₀) c)) =
      mapC (uj0 (vj0A ((Algebra.TensorProduct.includeLeft :
        C →ₐ[A] C ⊗[A] R₀) c))) := by
          simp [AlgHom.comp_apply]
    _ = uR (mapB (vj0A ((Algebra.TensorProduct.includeLeft :
          C →ₐ[A] C ⊗[A] R₀) c))) := hu_apply
    _ = uR (vR (mapC ((Algebra.TensorProduct.includeLeft :
          C →ₐ[A] C ⊗[A] R₀) c))) := by rw [hv_apply]
    _ = mapC ((Algebra.TensorProduct.includeLeft :
          C →ₐ[A] C ⊗[A] R₀) c) := hright_apply

/-- Helper for Chap10 Lemma 10 127 7: a transported left-factor inverse on finite generators
 yields a two-sided tensor inverse at the target stage. -/
lemma tensorMapLeftInverseOfStagewiseGeneratorInverses
    {R₀ R : Type u} [CommRing R₀] [CommRing R] [Algebra A R₀] [Algebra A R]
    (u : B →ₐ[A] C)
    (vj0A : C ⊗[A] R₀ →ₐ[A] B ⊗[A] R₀)
    (uj0 : B ⊗[A] R₀ →ₐ[A] C ⊗[A] R₀)
    (mapBk : B ⊗[A] R₀ →ₐ[A] B ⊗[A] R)
    (mapCk : C ⊗[A] R₀ →ₐ[A] C ⊗[A] R)
    (uk : B ⊗[A] R →ₐ[A] C ⊗[A] R)
    (htransport : uk.comp mapBk = mapCk.comp uj0)
    (huk_left :
      uk.comp (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R) =
        (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R).comp u)
    (huk_right :
      uk.comp (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R) =
        (Algebra.TensorProduct.includeRight : R →ₐ[A] C ⊗[A] R))
    (huj0_left :
      uj0.comp (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R₀) =
        (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R₀).comp u)
    (hmapBk_left :
      mapBk.comp (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R₀) =
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R))
    (hmapCk_left :
      mapCk.comp (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R₀) =
        (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R))
    (sB : Finset B) (hsB : Algebra.adjoin A (sB : Set B) = ⊤)
    (hBstage :
      ∀ b ∈ sB,
        mapBk ((vj0A.comp uj0)
          ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R₀) b)) =
        mapBk ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R₀) b))
    (sC : Finset C) (hsC : Algebra.adjoin A (sC : Set C) = ⊤)
    (hCstage :
      ∀ c ∈ sC,
        mapCk ((uj0.comp vj0A)
          ((Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R₀) c)) =
        mapCk ((Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R₀) c)) :
    let vLeftj0 : C →ₐ[A] B ⊗[A] R₀ :=
      vj0A.comp (Algebra.TensorProduct.includeLeft :
        C →ₐ[A] C ⊗[A] R₀)
    let vLeftk : C →ₐ[A] B ⊗[A] R := mapBk.comp vLeftj0
    let vk : C ⊗[A] R →ₐ[A] B ⊗[A] R :=
      Algebra.TensorProduct.productMap vLeftk
        (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R)
    vk.comp uk = AlgHom.id A _ := by
  let vLeftj0 : C →ₐ[A] B ⊗[A] R₀ :=
    vj0A.comp (Algebra.TensorProduct.includeLeft :
      C →ₐ[A] C ⊗[A] R₀)
  let vLeftk : C →ₐ[A] B ⊗[A] R := mapBk.comp vLeftj0
  let vk : C ⊗[A] R →ₐ[A] B ⊗[A] R :=
    Algebra.TensorProduct.productMap vLeftk
      (Algebra.TensorProduct.includeRight :
        R →ₐ[A] B ⊗[A] R)
  have hvLeft :
      vLeftk.comp u =
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R) :=
    tensorLeftFactorInverseOfGeneratorTransport u vj0A uj0 mapBk
      huj0_left hmapBk_left sB hsB hBstage
  -- Proof comment: the candidate inverse agrees with the identity on both tensor generators of
  -- `B ⊗[A] R`, so tensor extensionality identifies the maps.
  apply tensor_base_change_algHom_ext
  · calc
      (vk.comp uk).comp (Algebra.TensorProduct.includeLeft :
          B →ₐ[A] B ⊗[A] R) =
        vk.comp (uk.comp (Algebra.TensorProduct.includeLeft :
          B →ₐ[A] B ⊗[A] R)) := rfl
      _ = vk.comp ((Algebra.TensorProduct.includeLeft :
          C →ₐ[A] C ⊗[A] R).comp u) := by rw [huk_left]
      _ = (vk.comp (Algebra.TensorProduct.includeLeft :
          C →ₐ[A] C ⊗[A] R)).comp u := rfl
      _ = vLeftk.comp u := by simp [vk]
      _ = (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R) := hvLeft
      _ = (AlgHom.id A _).comp (Algebra.TensorProduct.includeLeft :
          B →ₐ[A] B ⊗[A] R) := by simp
  · calc
      (vk.comp uk).comp (Algebra.TensorProduct.includeRight :
          R →ₐ[A] B ⊗[A] R) =
        vk.comp (uk.comp (Algebra.TensorProduct.includeRight :
          R →ₐ[A] B ⊗[A] R)) := rfl
      _ = vk.comp (Algebra.TensorProduct.includeRight :
          R →ₐ[A] C ⊗[A] R) := by rw [huk_right]
      _ = (Algebra.TensorProduct.includeRight :
          R →ₐ[A] B ⊗[A] R) := by simp [vk]
      _ = (AlgHom.id A _).comp (Algebra.TensorProduct.includeRight :
          R →ₐ[A] B ⊗[A] R) := by simp

/-- Helper for Chap10 Lemma 10 127 7: the same transported inverse data also yields a right
inverse for the descended tensor map at the target stage. -/
lemma tensorMapRightInverseOfStagewiseGeneratorInverses
    {R₀ R : Type u} [CommRing R₀] [CommRing R] [Algebra A R₀] [Algebra A R]
    (u : B →ₐ[A] C)
    (vj0A : C ⊗[A] R₀ →ₐ[A] B ⊗[A] R₀)
    (uj0 : B ⊗[A] R₀ →ₐ[A] C ⊗[A] R₀)
    (mapBk : B ⊗[A] R₀ →ₐ[A] B ⊗[A] R)
    (mapCk : C ⊗[A] R₀ →ₐ[A] C ⊗[A] R)
    (uk : B ⊗[A] R →ₐ[A] C ⊗[A] R)
    (htransport : uk.comp mapBk = mapCk.comp uj0)
    (huk_left :
      uk.comp (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R) =
        (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R).comp u)
    (huk_right :
      uk.comp (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R) =
        (Algebra.TensorProduct.includeRight : R →ₐ[A] C ⊗[A] R))
    (huj0_left :
      uj0.comp (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R₀) =
        (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R₀).comp u)
    (hmapBk_left :
      mapBk.comp (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R₀) =
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R))
    (hmapCk_left :
      mapCk.comp (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R₀) =
        (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R))
    (sB : Finset B) (hsB : Algebra.adjoin A (sB : Set B) = ⊤)
    (hBstage :
      ∀ b ∈ sB,
        mapBk ((vj0A.comp uj0)
          ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R₀) b)) =
        mapBk ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R₀) b))
    (sC : Finset C) (hsC : Algebra.adjoin A (sC : Set C) = ⊤)
    (hCstage :
      ∀ c ∈ sC,
        mapCk ((uj0.comp vj0A)
          ((Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R₀) c)) =
        mapCk ((Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R₀) c)) :
    let vLeftj0 : C →ₐ[A] B ⊗[A] R₀ :=
      vj0A.comp (Algebra.TensorProduct.includeLeft :
        C →ₐ[A] C ⊗[A] R₀)
    let vLeftk : C →ₐ[A] B ⊗[A] R := mapBk.comp vLeftj0
    let vk : C ⊗[A] R →ₐ[A] B ⊗[A] R :=
      Algebra.TensorProduct.productMap vLeftk
        (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R)
    uk.comp vk = AlgHom.id A _ := by
  let vLeftj0 : C →ₐ[A] B ⊗[A] R₀ :=
    vj0A.comp (Algebra.TensorProduct.includeLeft :
      C →ₐ[A] C ⊗[A] R₀)
  let vLeftk : C →ₐ[A] B ⊗[A] R := mapBk.comp vLeftj0
  let vk : C ⊗[A] R →ₐ[A] B ⊗[A] R :=
    Algebra.TensorProduct.productMap vLeftk
      (Algebra.TensorProduct.includeRight :
        R →ₐ[A] B ⊗[A] R)
  have huvLeft :
      uk.comp vLeftk =
        (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R) :=
    tensorRightFactorInverseOfGeneratorTransport vj0A uj0 mapBk mapCk uk
      htransport hmapCk_left sC hsC hCstage
  -- Proof comment: the same tensor-ext argument shows that `vk` is also a right inverse.
  apply tensor_base_change_algHom_ext
  · calc
      (uk.comp vk).comp (Algebra.TensorProduct.includeLeft :
          C →ₐ[A] C ⊗[A] R) =
        uk.comp (vk.comp (Algebra.TensorProduct.includeLeft :
          C →ₐ[A] C ⊗[A] R)) := rfl
      _ = uk.comp vLeftk := by simp [vk]
      _ = (Algebra.TensorProduct.includeLeft :
          C →ₐ[A] C ⊗[A] R) := huvLeft
      _ = (AlgHom.id A _).comp (Algebra.TensorProduct.includeLeft :
          C →ₐ[A] C ⊗[A] R) := by simp
  · calc
      (uk.comp vk).comp (Algebra.TensorProduct.includeRight :
          R →ₐ[A] C ⊗[A] R) =
        uk.comp (vk.comp (Algebra.TensorProduct.includeRight :
          R →ₐ[A] C ⊗[A] R)) := rfl
      _ = uk.comp (Algebra.TensorProduct.includeRight :
          R →ₐ[A] B ⊗[A] R) := by simp [vk]
      _ = (Algebra.TensorProduct.includeRight :
          R →ₐ[A] C ⊗[A] R) := huk_right
      _ = (AlgHom.id A _).comp (Algebra.TensorProduct.includeRight :
          R →ₐ[A] C ⊗[A] R) := by simp

lemma tensorMapBijectiveOfStagewiseGeneratorInverses
    {R₀ R : Type u} [CommRing R₀] [CommRing R] [Algebra A R₀] [Algebra A R]
    (u : B →ₐ[A] C)
    (vj0A : C ⊗[A] R₀ →ₐ[A] B ⊗[A] R₀)
    (uj0 : B ⊗[A] R₀ →ₐ[A] C ⊗[A] R₀)
    (mapBk : B ⊗[A] R₀ →ₐ[A] B ⊗[A] R)
    (mapCk : C ⊗[A] R₀ →ₐ[A] C ⊗[A] R)
    (uk : B ⊗[A] R →ₐ[A] C ⊗[A] R)
    (htransport : uk.comp mapBk = mapCk.comp uj0)
    (huk_left :
      uk.comp (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R) =
        (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R).comp u)
    (huk_right :
      uk.comp (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R) =
        (Algebra.TensorProduct.includeRight : R →ₐ[A] C ⊗[A] R))
    (huj0_left :
      uj0.comp (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R₀) =
        (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R₀).comp u)
    (hmapBk_left :
      mapBk.comp (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R₀) =
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R))
    (hmapCk_left :
      mapCk.comp (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R₀) =
        (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R))
    (sB : Finset B) (hsB : Algebra.adjoin A (sB : Set B) = ⊤)
    (hBstage :
      ∀ b ∈ sB,
        mapBk ((vj0A.comp uj0)
          ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R₀) b)) =
        mapBk ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R₀) b))
    (sC : Finset C) (hsC : Algebra.adjoin A (sC : Set C) = ⊤)
    (hCstage :
      ∀ c ∈ sC,
        mapCk ((uj0.comp vj0A)
          ((Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R₀) c)) =
        mapCk ((Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R₀) c)) :
    Function.Bijective uk := by
  let vLeftj0 : C →ₐ[A] B ⊗[A] R₀ :=
    vj0A.comp (Algebra.TensorProduct.includeLeft :
      C →ₐ[A] C ⊗[A] R₀)
  let vLeftk : C →ₐ[A] B ⊗[A] R := mapBk.comp vLeftj0
  let vk : C ⊗[A] R →ₐ[A] B ⊗[A] R :=
    Algebra.TensorProduct.productMap vLeftk
      (Algebra.TensorProduct.includeRight :
        R →ₐ[A] B ⊗[A] R)
  have hleft_inv : vk.comp uk = AlgHom.id A _ :=
    tensorMapLeftInverseOfStagewiseGeneratorInverses
      u vj0A uj0 mapBk mapCk uk
      htransport huk_left huk_right huj0_left hmapBk_left hmapCk_left
      sB hsB hBstage sC hsC hCstage
  have hright_inv : uk.comp vk = AlgHom.id A _ :=
    tensorMapRightInverseOfStagewiseGeneratorInverses
      u vj0A uj0 mapBk mapCk uk
      htransport huk_left huk_right huj0_left hmapBk_left hmapCk_left
      sB hsB hBstage sC hsC hCstage
  refine ⟨?_, ?_⟩
  · intro x₁ x₂ hEq
    have hx₁ := congrArg (fun φ : B ⊗[A] R →ₐ[A] B ⊗[A] R ↦ φ x₁) hleft_inv
    have hx₂ := congrArg (fun φ : B ⊗[A] R →ₐ[A] B ⊗[A] R ↦ φ x₂) hleft_inv
    calc
      x₁ = vk (uk x₁) := by simpa [AlgHom.comp_apply] using hx₁.symm
      _ = vk (uk x₂) := by rw [hEq]
      _ = x₂ := by simpa [AlgHom.comp_apply] using hx₂
  · intro y
    refine ⟨vk y, ?_⟩
    exact congrArg (fun φ : C ⊗[A] R →ₐ[A] C ⊗[A] R ↦ φ y) hright_inv

/-- Chap10 Lemma 10 127 7 (4): if `B` is of finite type over `A`, `C` is finitely presented over
`A`, and the base change of `u : B → C` to the filtered colimit algebra `colimit F` is
bijective, then the base change of `u` to some stage `F.obj j` is already bijective. -/
@[stacks 05N8]
theorem finite_type_finite_presentation_bijective_descends
    [Algebra.FiniteType A B] [Algebra.FinitePresentation A C]
    (u : B →ₐ[A] C)
    (h :
      Function.Bijective
        (Algebra.TensorProduct.map u
          (AlgHom.id A (((colimit F : CommAlgCat A) : Type u))))) :
    ∃ j : J,
      Function.Bijective
        (Algebra.TensorProduct.map u
          (AlgHom.id A (((F.obj j : CommAlgCat A) : Type u)))) := by
  classical
  let uColim :
      B ⊗[A] ((colimit F : CommAlgCat A) : Type u) →ₐ[((colimit F : CommAlgCat A) : Type u)]
        C ⊗[A] ((colimit F : CommAlgCat A) : Type u) :=
    tensorBaseChangeMapOverRightBase u
  have huColim : Function.Bijective uColim := by
    simpa [uColim, tensorBaseChangeMapOverRightBase] using h
  let eColim :
      B ⊗[A] ((colimit F : CommAlgCat A) : Type u) ≃ₐ[((colimit F : CommAlgCat A) : Type u)]
        C ⊗[A] ((colimit F : CommAlgCat A) : Type u) :=
    AlgEquiv.ofBijective uColim huColim
  let vColim :
      C ⊗[A] ((colimit F : CommAlgCat A) : Type u) →ₐ[((colimit F : CommAlgCat A) : Type u)]
        B ⊗[A] ((colimit F : CommAlgCat A) : Type u) :=
    eColim.symm.toAlgHom
  obtain ⟨j₀, vj₀, hvj₀⟩ :=
    finite_presentation_hom_descends F vColim
  let vj₀A :
      C ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u) →ₐ[A]
        B ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u) :=
    vj₀.restrictScalars A
  let uj₀ :
      B ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u) →ₐ[A]
        C ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u) :=
    Algebra.TensorProduct.map u (AlgHom.id A (((F.obj j₀ : CommAlgCat A) : Type u)))
  let uColimA :
      B ⊗[A] ((colimit F : CommAlgCat A) : Type u) →ₐ[A]
        C ⊗[A] ((colimit F : CommAlgCat A) : Type u) :=
    uColim.restrictScalars A
  let vColimA :
      C ⊗[A] ((colimit F : CommAlgCat A) : Type u) →ₐ[A]
        B ⊗[A] ((colimit F : CommAlgCat A) : Type u) :=
    vColim.restrictScalars A
  let mapBj₀ :
      B ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u) →ₐ[A]
        B ⊗[A] ((colimit F : CommAlgCat A) : Type u) :=
    Algebra.TensorProduct.map (AlgHom.id A B) (colimit.ι F j₀).hom
  let mapCj₀ :
      C ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u) →ₐ[A]
        C ⊗[A] ((colimit F : CommAlgCat A) : Type u) :=
    Algebra.TensorProduct.map (AlgHom.id A C) (colimit.ι F j₀).hom
  have hvj₀A : mapBj₀.comp vj₀A = vColimA.comp mapCj₀ := by
    simpa [mapBj₀, mapCj₀, vj₀A, vColimA] using hvj₀
  have huj₀ :
      mapCj₀.comp uj₀ = uColimA.comp mapBj₀ := by
    simpa [mapBj₀, mapCj₀, uj₀, uColimA] using
      (tensorMapExchangeRestrictScalars u (colimit.ι F j₀).hom).symm
  have hleftColim : vColimA.comp uColimA = AlgHom.id A _ := by
    apply AlgHom.ext
    intro x
    simpa [uColim, eColim, vColim, uColimA, vColimA] using
      AlgEquiv.ofBijective_symm_apply_apply uColim huColim x
  have hrightColim : uColimA.comp vColimA = AlgHom.id A _ := by
    apply AlgHom.ext
    intro x
    simpa [uColim, eColim, vColim, uColimA, vColimA] using
      AlgEquiv.ofBijective_apply_symm_apply uColim huColim x
  obtain ⟨sB, hsB⟩ :=
    (Algebra.FiniteType.out : ∃ s : Finset B, Algebra.adjoin A (s : Set B) = ⊤)
  obtain ⟨sC, hsC⟩ :=
    (Algebra.FiniteType.out : ∃ s : Finset C, Algebra.adjoin A (s : Set C) = ⊤)
  let xB : B → B ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u) := fun b ↦
    (vj₀A.comp uj₀)
      ((Algebra.TensorProduct.includeLeft :
        B →ₐ[A] B ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u)) b)
  let yB : B → B ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u) := fun b ↦
    (Algebra.TensorProduct.includeLeft :
      B →ₐ[A] B ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u)) b
  let xC : C → C ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u) := fun c ↦
    (uj₀.comp vj₀A)
      ((Algebra.TensorProduct.includeLeft :
        C →ₐ[A] C ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u)) c)
  let yC : C → C ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u) := fun c ↦
    (Algebra.TensorProduct.includeLeft :
      C →ₐ[A] C ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u)) c
  have hBdef : ∀ b ∈ sB, mapBj₀ (xB b) = mapBj₀ (yB b) := by
    intro b hb
    simpa [xB, yB, AlgHom.comp_apply] using
      tensorLeftGeneratorTransportEqOfColimitLeftInverse
        vj₀A uj₀ mapBj₀ mapCj₀ uColimA vColimA hvj₀A huj₀ hleftColim b
  have hCdef : ∀ c ∈ sC, mapCj₀ (xC c) = mapCj₀ (yC c) := by
    intro c hc
    simpa [xC, yC, AlgHom.comp_apply] using
      tensorRightGeneratorTransportEqOfColimitRightInverse
        vj₀A uj₀ mapBj₀ mapCj₀ uColimA vColimA hvj₀A huj₀ hrightColim c
  obtain ⟨kB, fB, hfB⟩ :=
    tensorStageEqDescendsFiniteFamily F sB xB yB hBdef
  obtain ⟨kC, fC, hfC⟩ :=
    tensorStageEqDescendsFiniteFamily F sC xC yC hCdef
  let jBool : Bool → J := fun t ↦ Bool.rec kB kC t
  let fBool : ∀ t : Bool, t ∈ (Finset.univ : Finset Bool) → (j₀ ⟶ jBool t) :=
    fun t _ ↦ Bool.rec fB fC t
  obtain ⟨k, gk, hgk⟩ :=
    filteredCommonTargetOfFiniteMapsFrom (Finset.univ : Finset Bool)
      jBool
      fBool
  rcases hgk false (by simp) with ⟨hB, hBfac_raw⟩
  rcases hgk true (by simp) with ⟨hC, hCfac_raw⟩
  have hBfac : fB ≫ hB = gk := by
    simpa using hBfac_raw
  have hCfac : fC ≫ hC = gk := by
    simpa using hCfac_raw
  let mapBk :
      B ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u) →ₐ[A]
        B ⊗[A] ((F.obj k : CommAlgCat A) : Type u) :=
    Algebra.TensorProduct.map (AlgHom.id A B) (F.map gk).hom
  let mapCk :
      C ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u) →ₐ[A]
        C ⊗[A] ((F.obj k : CommAlgCat A) : Type u) :=
    Algebra.TensorProduct.map (AlgHom.id A C) (F.map gk).hom
  let uk :
      B ⊗[A] ((F.obj k : CommAlgCat A) : Type u) →ₐ[A]
        C ⊗[A] ((F.obj k : CommAlgCat A) : Type u) :=
    Algebra.TensorProduct.map u (AlgHom.id A (((F.obj k : CommAlgCat A) : Type u)))
  have hBstage :
      ∀ b ∈ sB, mapBk (xB b) = mapBk (yB b) := by
    intro b hb
    have hpush :=
      tensorStageEqMap_comp F fB hB (hfB b hb)
    simpa [mapBk, hBfac] using hpush
  have hCstage :
      ∀ c ∈ sC, mapCk (xC c) = mapCk (yC c) := by
    intro c hc
    have hpush :=
      tensorStageEqMap_comp F fC hC (hfC c hc)
    simpa [mapCk, hCfac] using hpush
  have htransport : uk.comp mapBk = mapCk.comp uj₀ := by
    simpa [uk, mapBk, mapCk, uj₀] using
      tensorMapExchangeRestrictScalars u (F.map gk).hom
  have huk_left :
      uk.comp (Algebra.TensorProduct.includeLeft :
        B →ₐ[A] B ⊗[A] ((F.obj k : CommAlgCat A) : Type u)) =
      (Algebra.TensorProduct.includeLeft :
        C →ₐ[A] C ⊗[A] ((F.obj k : CommAlgCat A) : Type u)).comp u := by
    simpa [uk] using
      (Algebra.TensorProduct.map_comp_includeLeft
        u (AlgHom.id A (((F.obj k : CommAlgCat A) : Type u))))
  have huk_right :
      uk.comp (Algebra.TensorProduct.includeRight :
        ((F.obj k : CommAlgCat A) : Type u) →ₐ[A] B ⊗[A] ((F.obj k : CommAlgCat A) : Type u)) =
      (Algebra.TensorProduct.includeRight :
        ((F.obj k : CommAlgCat A) : Type u) →ₐ[A] C ⊗[A] ((F.obj k : CommAlgCat A) : Type u)) := by
    simpa [uk] using
      (Algebra.TensorProduct.map_comp_includeRight
        u (AlgHom.id A (((F.obj k : CommAlgCat A) : Type u))))
  have huj₀_left :
      uj₀.comp (Algebra.TensorProduct.includeLeft :
        B →ₐ[A] B ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u)) =
      (Algebra.TensorProduct.includeLeft :
        C →ₐ[A] C ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u)).comp u := by
    simpa [uj₀] using
      (Algebra.TensorProduct.map_comp_includeLeft
        u (AlgHom.id A (((F.obj j₀ : CommAlgCat A) : Type u))))
  have hmapBk_left :
      mapBk.comp (Algebra.TensorProduct.includeLeft :
        B →ₐ[A] B ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u)) =
      (Algebra.TensorProduct.includeLeft :
        B →ₐ[A] B ⊗[A] ((F.obj k : CommAlgCat A) : Type u)) := by
    simpa [mapBk] using
      (Algebra.TensorProduct.map_comp_includeLeft
        (AlgHom.id A B) (F.map gk).hom)
  have hmapCk_left :
      mapCk.comp (Algebra.TensorProduct.includeLeft :
        C →ₐ[A] C ⊗[A] ((F.obj j₀ : CommAlgCat A) : Type u)) =
      (Algebra.TensorProduct.includeLeft :
        C →ₐ[A] C ⊗[A] ((F.obj k : CommAlgCat A) : Type u)) := by
    simpa [mapCk] using
      (Algebra.TensorProduct.map_comp_includeLeft
        (AlgHom.id A C) (F.map gk).hom)
  refine ⟨k, ?_⟩
  exact tensorMapBijectiveOfStagewiseGeneratorInverses
    u vj₀A uj₀ mapBk mapCk uk htransport
    huk_left huk_right huj₀_left hmapBk_left hmapCk_left
    sB hsB hBstage sC hsC hCstage

end
