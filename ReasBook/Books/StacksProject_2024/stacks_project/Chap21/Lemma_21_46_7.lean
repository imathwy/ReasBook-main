import StacksProject_2024.stacks_project.Chap15.Lemma_15_58_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_59_7
import StacksProject_2024.stacks_project.Chap18.Lemma_18_28_12
import StacksProject_2024.stacks_project.Chap21.Definition_21_17_2
import StacksProject_2024.stacks_project.Chap21.Definition_21_17_13_Core
import StacksProject_2024.stacks_project.Chap21.Definition_21_46_1_Core
import StacksProject_2024.stacks_project.Chap21.Lemma_21_46_3

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open RingedSite.Hom (ModuleCat ModuleDerived)
open scoped RingedSiteDerivedTensor

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

/- Domain-style sampling for Lemma 21.46.7:
- primary domain: tor-amplitude in `D(\mathcal O_X)` under the derived tensor product on a ringed
  site;
- sampled owner declarations:
  `SheafOfModules.RingedSite.HasTorAmplitudeIn`,
  `SheafOfModules.RingedSite.derivedTensorProduct`,
  `RingedSite.Hom.ModuleCat`,
  `RingedSite.Hom.ModuleDerived`,
  `RingedSiteDerivedTensor`;
- best owner abstraction: the ambient owners are the tor-amplitude
  predicate `HasTorAmplitudeIn` on the bundled ringed site
  `X := RingedSite.ofCommRingSheaf J 𝒪`, and the Chapter 21 derived tensor owner
  `derivedTensorProduct`; on this theorem surface the source-facing notation `K ⊗^L L` should
  come from the existing scoped bridge `RingedSiteDerivedTensor`, so this file should not
  introduce a second local tensor wrapper;
- the Chapter 20 ringed-space theorem is a specialization along the opens-ringed-site bridge, not
  the owner of this bundled ringed-site interface, so the public theorem here should remain the
  Chapter 21 owner-level statement rather than a second wrapper around a specialization;
- primitive data: the derived objects `K`, `L` and their tor-amplitude bounds;
- derived API: the induced tor-amplitude bound for `K ⊗^L L`.

Source/core/bridge triage:
- `source-facing`: the tor-amplitude bound for the derived tensor product `K ⊗^L L` on a ringed
  site;
- `core/canonical`: `HasTorAmplitudeIn` together with `derivedTensorProduct`;
- `bridge/view`: the existing scoped notation `K ⊗^L L` from `RingedSiteDerivedTensor`.

The Chapter 20 ringed-space theorem is a specialization of this commutative ringed-site statement,
not its owner. The theorem therefore lives over the Chapter 21 presentation
`X := RingedSite.ofCommRingSheaf J 𝒪` so that `K ⊗^L L` is the actual derived-tensor owner, and
it stays in the owner namespace `HasTorAmplitudeIn` rather than introducing a parallel
tensor-closure wrapper.
-/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
 
local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "DMod" => ModuleDerived (RingedSite.ofCommRingSheaf J 𝒪)

variable [Abelian Mod]
variable [CategoryWithHomology Mod]
variable [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [HasColimits (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ M : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj M).Additive]
variable [∀ (K L : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (ringedSiteModuleCategory J 𝒪))]
variable [∀ G₁ G₂ : GradedObject ℤ (ringedSiteModuleCategory J 𝒪), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (ringedSiteModuleCategory J 𝒪),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (ringedSiteModuleCategory J 𝒪),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (ringedSiteModuleCategory J 𝒪),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [∀ M : ringedSiteModuleCategory J 𝒪,
  PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory J 𝒪))
    ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj M)]
variable [∀ M : ringedSiteModuleCategory J 𝒪,
  PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory J 𝒪))
    ((curriedTensor (ringedSiteModuleCategory J 𝒪)).flip.obj M)]
variable [MonoidalCategory (DerivedCategory (ringedSiteModuleCategory J 𝒪))]

variable {a b c d : ℤ}

local notation "Complexes" => CochainComplex Mod ℤ
local notation "KMod" => HomotopyCategory Mod (ComplexShape.up ℤ)
local notation "Q" => (HomotopyCategory.quotient Mod (ComplexShape.up ℤ) : Complexes ⥤ KMod)
local notation "Qh" => (DerivedCategory.Qh : KMod ⥤ DMod)
local notation "Qis" => HomotopyCategory.quasiIso Mod (ComplexShape.up ℤ)

local instance : MonoidalCategory KMod := inferInstance

local instance : (Q : Complexes ⥤ KMod).Monoidal := inferInstance

variable [Functor.Monoidal
  (DerivedCategory.Qh :
    HomotopyCategory (ringedSiteModuleCategory J 𝒪) (up ℤ) ⥤
      DerivedCategory (ringedSiteModuleCategory J 𝒪))]

/-- Helper for Lemma 21.46.7: the composite quotient functor
`DerivedCategory.Q : Complexes ⥤ D(𝒪)` carries the ambient monoidal structure. -/
private noncomputable instance quotientFunctorMonoidal :
    (DerivedCategory.Q : Complexes ⥤ DMod).Monoidal := by
  change (((Q : Complexes ⥤ KMod) ⋙ (Qh : KMod ⥤ DMod))).Monoidal
  infer_instance

/-- Helper for Lemma 21.46.7: tensoring two strictly bounded-below cochain complexes adds their
lower cutoffs. -/
private theorem tensorObjIsStrictlyGE_add
    {E F : Complexes}
    (hE : E.IsStrictlyGE a) (hF : F.IsStrictlyGE c) :
    CochainComplex.IsStrictlyGE (HomologicalComplex.tensorObj E F) (a + c) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
  change 𝟙 ((CategoryTheory.GradedObject.Monoidal.tensorObj E.X F.X) n) = 0
  -- Proof comment: below degree `a + c`, each tensor summand has one factor below its lower
  -- support bound, so the corresponding inclusion is already zero.
  apply CategoryTheory.GradedObject.Monoidal.tensorObj_ext
  intro p q h
  have hpq : p < a ∨ q < c := by
    omega
  cases hpq with
  | inl hp =>
      let T : Mod ⥤ Mod :=
        (CategoryTheory.MonoidalCategory.curriedTensor Mod).flip.obj (F.X q)
      have hzero : IsZero (E.X p) := E.isZero_of_isStrictlyGE a p hp
      have hsrc : IsZero (T.obj (E.X p)) := CategoryTheory.Functor.map_isZero T hzero
      simpa [T, Category.assoc] using
        hsrc.eq_of_src (CategoryTheory.GradedObject.Monoidal.ιTensorObj E.X F.X p q n h) 0
  | inr hq =>
      let T : Mod ⥤ Mod :=
        (CategoryTheory.MonoidalCategory.curriedTensor Mod).obj (E.X p)
      have hzero : IsZero (F.X q) := F.isZero_of_isStrictlyGE c q hq
      have hsrc : IsZero (T.obj (F.X q)) := CategoryTheory.Functor.map_isZero T hzero
      simpa [T, Category.assoc] using
        hsrc.eq_of_src (CategoryTheory.GradedObject.Monoidal.ιTensorObj E.X F.X p q n h) 0

/-- Helper for Lemma 21.46.7: tensoring two strictly bounded-above cochain complexes adds their
upper cutoffs. -/
private theorem tensorObjIsStrictlyLE_add
    {E F : Complexes}
    (hE : E.IsStrictlyLE b) (hF : F.IsStrictlyLE d) :
    CochainComplex.IsStrictlyLE (HomologicalComplex.tensorObj E F) (b + d) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
  change 𝟙 ((CategoryTheory.GradedObject.Monoidal.tensorObj E.X F.X) n) = 0
  -- Proof comment: above degree `b + d`, every `(p,q)` summand lies beyond one of the two
  -- support bounds, so that tensor summand already vanishes.
  apply CategoryTheory.GradedObject.Monoidal.tensorObj_ext
  intro p q h
  have hpq : b < p ∨ d < q := by
    omega
  cases hpq with
  | inl hp =>
      let T : Mod ⥤ Mod :=
        (CategoryTheory.MonoidalCategory.curriedTensor Mod).flip.obj (F.X q)
      have hzero : IsZero (E.X p) := E.isZero_of_isStrictlyLE b p hp
      have hsrc : IsZero (T.obj (E.X p)) := CategoryTheory.Functor.map_isZero T hzero
      simpa [T, Category.assoc] using
        hsrc.eq_of_src (CategoryTheory.GradedObject.Monoidal.ιTensorObj E.X F.X p q n h) 0
  | inr hq =>
      let T : Mod ⥤ Mod :=
        (CategoryTheory.MonoidalCategory.curriedTensor Mod).obj (E.X p)
      have hzero : IsZero (F.X q) := F.isZero_of_isStrictlyLE d q hq
      have hsrc : IsZero (T.obj (F.X q)) := CategoryTheory.Functor.map_isZero T hzero
      simpa [T, Category.assoc] using
        hsrc.eq_of_src (CategoryTheory.GradedObject.Monoidal.ιTensorObj E.X F.X p q n h) 0

/-- Helper for Lemma 21.46.7: the strict tensor product of two termwise-flat complexes is still
termwise flat. -/
private theorem tensorObjIsTermwiseFlatOfIsTermwiseFlat
    {E F : Complexes}
    (hE : CochainComplex.IsTermwiseFlat E) (hF : CochainComplex.IsTermwiseFlat F) :
    CochainComplex.IsTermwiseFlat (HomologicalComplex.tensorObj E F) := by
  -- Proof comment: degreewise identify `(E ⊗ F).X n` with the coproduct of the tensor summands
  -- indexed by `p + q = n`, apply `isFlat_tensor` on each summand, and close with
  -- `isFlat_coproduct`.
  rw [CochainComplex.isTermwiseFlat_iff] at hE hF ⊢
  intro n
  -- Proof comment: every summand in total degree `n` is a tensor product of flat terms, so the
  -- coproduct description of the graded tensor object is flat termwise.
  let S : {pq : ℤ × ℤ // pq.1 + pq.2 = n} → Mod :=
    fun pq ↦ ((curriedTensor Mod).obj (E.X pq.1.1)).obj (F.X pq.1.2)
  have hS : ∀ pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n}, IsFlat 𝒪 (S pq) := by
    intro pq
    rcases pq with ⟨⟨p, q⟩, hpq⟩
    dsimp [S]
    let _ : IsFlat 𝒪 (E.X p) := hE p
    let _ : IsFlat 𝒪 (F.X q) := hF q
    simpa using (SheafOfModules.RingedSite.isFlat_tensor (J := J) (𝒪 := 𝒪) (E.X p) (F.X q))
  change IsFlat 𝒪 ((CategoryTheory.GradedObject.Monoidal.tensorObj E.X F.X) n)
  simpa [CategoryTheory.GradedObject.Monoidal.tensorObj, S] using
    (SheafOfModules.RingedSite.isFlat_coproduct (J := J) (𝒪 := 𝒪) S hS)

/-- Helper for Lemma 21.46.7: tor-amplitude in a fixed interval is invariant under
isomorphism in `D(𝒪)`. -/
private theorem hasTorAmplitudeIn_of_iso
    {K L : DMod} {a b : ℤ}
    (e : K ≅ L) :
    HasTorAmplitudeIn (X := RingedSite.ofCommRingSheaf J 𝒪) K a b ↔
      HasTorAmplitudeIn (X := RingedSite.ofCommRingSheaf J 𝒪) L a b := by
  -- Proof comment: transport the test homology objects along the functorial tensor isomorphism
  -- induced by `e` and its inverse.
  constructor
  · intro h M i hi
    -- Proof comment: apply the bound before whiskering by the tensor image of `e.symm`.
    exact
      (h M i hi).of_iso
        ((DerivedCategory.homologyFunctor Mod i).mapIso
          ((derivedTensorProduct ((DerivedCategory.singleFunctor Mod (0 : ℤ)).obj M)).mapIso
            e.symm))
  · intro h M i hi
    -- Proof comment: the converse direction uses the same transport with `e`.
    exact
      (h M i hi).of_iso
        ((DerivedCategory.homologyFunctor Mod i).mapIso
          ((derivedTensorProduct ((DerivedCategory.singleFunctor Mod (0 : ℤ)).obj M)).mapIso e))

/-- Helper for Lemma 21.46.7: the quotient functor identifies the strict tensor complex with the
ambient tensor of the two quotient objects. -/
omit [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [CategoryWithHomology Mod]
  [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)] in
private noncomputable def qObjTensorObjIsoAmbientTensor
    (E F : Complexes) :
    (DerivedCategory.Q.obj (HomologicalComplex.tensorObj E F) : DMod) ≅
      ((DerivedCategory.Q.obj E : DMod) ⊗ (DerivedCategory.Q.obj F)) :=
  Functor.Monoidal.μIso (DerivedCategory.Q : Complexes ⥤ DMod) E F

/-- Helper for Lemma 21.46.7: the fixed-right representative in `KMod` chosen from a derived
right tensor factor. -/
omit [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [CategoryWithHomology Mod]
  [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)] in
private noncomputable abbrev tensorRightRepresentative
    (L : DMod) :
    KMod :=
  (Q : Complexes ⥤ KMod).obj ((DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L)

/-- Helper for Lemma 21.46.7: passing the chosen right representative through `Qh` recovers the
original derived object. -/
omit [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [CategoryWithHomology Mod]
  [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)] in
private noncomputable def tensorRightRepresentativeIso
    (L : DMod) :
    (((Qh : KMod ⥤ DMod)).obj (tensorRightRepresentative L)) ≅ L :=
  (DerivedCategory.quotientCompQhIso Mod).app
      ((DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L) ≪≫
    (DerivedCategory.Q : Complexes ⥤ DMod).objObjPreimageIso L

/-- Helper for Lemma 21.46.7: a monoidal functor commutes with right tensoring by a fixed
object. -/
omit [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [CategoryWithHomology Mod]
  [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)] in
private noncomputable def tensorRightCommIso
    {A : Type*} [Category A] [MonoidalCategory A]
    {B : Type*} [Category B] [MonoidalCategory B]
    (F : A ⥤ B) [Functor.Monoidal F] (X : A) :
    F ⋙ (tensoringRight B).obj (F.obj X) ≅ (tensoringRight A).obj X ⋙ F :=
  Functor.Monoidal.commTensorRight (F := F) X

/-- Helper for Lemma 21.46.7: before applying `Qh`, the source tensor functor is computed in
`KMod` by tensoring with a chosen representative of the right factor. -/
omit [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [CategoryWithHomology Mod]
  [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)] in
private noncomputable abbrev derivedTensorSourceLiftFunctor
    (L : DMod) :
    KMod ⥤ KMod :=
  let L' := (DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L
  CategoryTheory.Quotient.lift
      (homotopic Mod (up ℤ))
      ((((curriedTensor Mod).map₂CochainComplex).flip.obj L') ⋙ Q)
      (fun _ _ _ _ ⟨h⟩ ↦
        HomotopyCategory.eq_of_homotopy _ _
          (HomologicalComplex.mapBifunctorMapHomotopy₁ h
            (𝟙 L')
            (curriedTensor Mod)
            (up ℤ)))

/-- Helper for Lemma 21.46.7: on represented morphisms, the quotient lift computes the source
tensor map by tensoring with the chosen right representative in complexes. -/
omit [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [CategoryWithHomology Mod]
  [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)] in
private theorem derivedTensorSourceLiftFunctor_map_quotientMap
    (L : DMod) {A B : Complexes} (f : A ⟶ B) :
    (derivedTensorSourceLiftFunctor L).map ((Q : Complexes ⥤ KMod).map f) =
      ((((curriedTensor Mod).map₂CochainComplex).flip.obj
        ((DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L)) ⋙ Q).map f := by
  let L' := (DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L
  -- Proof comment: this is the defining map formula for the quotient lift before composing with
  -- `Qh`.
  rfl

/-- Helper for Lemma 21.46.7: in `KMod`, right tensoring by the chosen representative agrees
with the quotient-side source tensor lift. -/
omit [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [CategoryWithHomology Mod]
  [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)] in
private theorem tensoringRightRepresentativeIsoDerivedTensorSourceLiftFunctor_hom_naturality_repr
    (L : DMod) {A B : Complexes} (f : A ⟶ B) :
    ((tensoringRight KMod).obj (tensorRightRepresentative L)).map ((Q : Complexes ⥤ KMod).map f) ≫
        (Functor.Monoidal.μIso Q ((Q : Complexes ⥤ KMod).obj B)
          ((DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L)).hom =
      (Functor.Monoidal.μIso Q ((Q : Complexes ⥤ KMod).obj A)
        ((DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L)).hom ≫
          (derivedTensorSourceLiftFunctor L).map ((Q : Complexes ⥤ KMod).map f) := by
  let L' := (DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L
  -- Proof comment: rewrite the target map using the quotient-lift computation rule, then this is
  -- exactly the right-factor naturality of the monoidal structure map for `Q`.
  have hnat :
      ((tensoringRight KMod).obj (tensorRightRepresentative L)).map ((Q : Complexes ⥤ KMod).map f) ≫
          (Functor.Monoidal.μIso Q ((Q : Complexes ⥤ KMod).obj B) L').hom =
        (Functor.Monoidal.μIso Q ((Q : Complexes ⥤ KMod).obj A) L').hom ≫
          ((((curriedTensor Mod).map₂CochainComplex).flip.obj L') ⋙ Q).map f := by
    simpa [L', tensorRightRepresentative] using
      (tensorRightCommIso (F := Q) L').hom.naturality f
  have hmap :
      (Functor.Monoidal.μIso Q ((Q : Complexes ⥤ KMod).obj A) L').hom ≫
          ((((curriedTensor Mod).map₂CochainComplex).flip.obj L') ⋙ Q).map f =
        (Functor.Monoidal.μIso Q ((Q : Complexes ⥤ KMod).obj A) L').hom ≫
          (derivedTensorSourceLiftFunctor L).map ((Q : Complexes ⥤ KMod).map f) := by
    exact congrArg
      (fun k ↦ (Functor.Monoidal.μIso Q ((Q : Complexes ⥤ KMod).obj A) L').hom ≫ k)
      (derivedTensorSourceLiftFunctor_map_quotientMap (L := L) f).symm
  exact hnat.trans hmap

/-- Helper for Lemma 21.46.7: the represented comparison in `KMod` descends to a natural
isomorphism. -/
omit [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [CategoryWithHomology Mod]
  [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)] in
private noncomputable def tensoringRightRepresentativeIsoDerivedTensorSourceLiftFunctor
    (L : DMod) :
    (tensoringRight KMod).obj (tensorRightRepresentative L) ≅ derivedTensorSourceLiftFunctor L := by
  let L' := (DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L
  refine NatIso.ofComponents
    (fun A ↦ ?_)
    (fun {A B} f ↦ ?_)
  · -- Proof comment: on represented objects, the comparison is just the monoidal tensorator of
    -- `Q`.
    simpa [L', derivedTensorSourceLiftFunctor, tensorRightRepresentative] using
      (Functor.Monoidal.μIso Q A.as L')
  · -- Proof comment: quotient induction reduces arbitrary morphisms in `KMod` to represented
    -- chain maps.
    rw [← HomotopyCategory.quotient_map_out (V := Mod) (c := up ℤ) f]
    simpa using
      tensoringRightRepresentativeIsoDerivedTensorSourceLiftFunctor_hom_naturality_repr
        (L := L) f.out

/-- Helper for Lemma 21.46.7: after whiskering by `Qh`, the quotient-side comparison reaches the
actual source tensor functor. -/
omit [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [CategoryWithHomology Mod]
  [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)] in
private noncomputable def tensoringRightRepresentativeIsoDerivedTensorSourceFunctor
    (L : DMod) :
    (tensoringRight KMod).obj (tensorRightRepresentative L) ⋙ Qh ≅ derivedTensorSourceFunctor L := by
  -- Proof comment: whiskering transfers the cheaper `KMod` comparison to the DMod-valued source
  -- tensor functor.
  simpa [derivedTensorSourceFunctor, derivedTensorSourceLiftFunctor] using
    (Functor.isoWhiskerRight
      (tensoringRightRepresentativeIsoDerivedTensorSourceLiftFunctor L)
      (Qh : KMod ⥤ DMod))

/-- Helper for Lemma 21.46.7: ambient right tensoring on `D(𝒪)` identifies with the source
tensor functor before left deriving. -/
private noncomputable def tensoringRightObjIsoDerivedTensorSourceFunctor
    (L : DMod) :
    Qh ⋙ (tensoringRight DMod).obj L ≅ derivedTensorSourceFunctor L :=
  -- Proof comment: first transport the fixed right representative back to `L`, then commute `Qh`
  -- past right tensoring, and finally apply the quotient-side source comparison.
  Functor.isoWhiskerLeft Qh (((tensoringRight DMod).mapIso (tensorRightRepresentativeIso L)).symm) ≪≫
    tensorRightCommIso Qh (tensorRightRepresentative L) ≪≫
      tensoringRightRepresentativeIsoDerivedTensorSourceFunctor L

/-- Helper for Lemma 21.46.7: the ambient right-tensor functor is already a left derived functor
of the source tensor functor. -/
private noncomputable instance tensoringRightObj_isLeftDerivedFunctor
    (L : DMod) :
    ((tensoringRight DMod).obj L).IsLeftDerivedFunctor
      (tensoringRightObjIsoDerivedTensorSourceFunctor L).hom
      Qis :=
  Functor.isLeftDerivedFunctor_of_inverts
    Qis
    ((tensoringRight DMod).obj L)
    (tensoringRightObjIsoDerivedTensorSourceFunctor L)

/-- Helper for Lemma 21.46.7: uniqueness of left derived functors identifies ambient right
tensoring with the source-facing derived tensor functor. -/
private noncomputable def tensoringRightObjIsoDerivedTensorProduct
    (L : DMod) :
    (tensoringRight DMod).obj L ≅ derivedTensorProduct L :=
  let F : KMod ⥤ DMod := derivedTensorSourceFunctor L
  -- Proof comment: both functors are left derived functors of the same source functor, so
  -- `Functor.leftDerivedNatIso` gives the comparison directly.
  (show (tensoringRight DMod).obj L ≅ derivedTensorProduct L from
    Functor.leftDerivedNatIso
      ((tensoringRight DMod).obj L)
      (derivedTensorProduct L)
      (tensoringRightObjIsoDerivedTensorSourceFunctor L).hom
      (derivedTensorProductCounit L)
      Qis
      (Iso.refl F))

/-- Helper for Lemma 21.46.7: for a represented left factor `Q.obj E`, the ambient tensor
`Q.obj E ⊗ L` agrees with the source-facing derived tensor object
`(derivedTensorProduct L).obj (Q.obj E)`. -/
private noncomputable def qObjAmbientTensorIsoDerivedTensorProduct
    (E : Complexes) (L : DMod) :
    (((DerivedCategory.Q.obj E : DMod) ⊗ L)) ≅
      ((derivedTensorProduct L).obj (DerivedCategory.Q.obj E)) :=
  (tensoringRightObjIsoDerivedTensorProduct L).app (DerivedCategory.Q.obj E)

/-- Helper for Lemma 21.46.7: the ambient tor-amplitude bound for `Q.obj E ⊗ L` transports to
the corresponding source-facing derived tensor object. -/
private theorem hasTorAmplitudeIn_qObjDerivedTensorProduct
    {E : Complexes} {L : DMod} {a b : ℤ}
    (h :
      HasTorAmplitudeIn (X := RingedSite.ofCommRingSheaf J 𝒪)
        (((DerivedCategory.Q.obj E : DMod) ⊗ L))
        a b) :
    HasTorAmplitudeIn (X := RingedSite.ofCommRingSheaf J 𝒪)
      ((derivedTensorProduct L).obj (DerivedCategory.Q.obj E))
      a b := by
  -- Proof comment: this is just transport across the objectwise comparison between ambient and
  -- source-facing tensor products on a represented left factor.
  exact
    (hasTorAmplitudeIn_of_iso
      (J := J) (𝒪 := 𝒪)
      (a := a) (b := b)
      (qObjAmbientTensorIsoDerivedTensorProduct (J := J) (𝒪 := 𝒪) E L)).1
      h

-- Proof sketch: test the tor-amplitude conditions for `K` and `L` against an arbitrary
-- degree-zero module, reassociate the iterated derived tensor product, and combine the intervals
-- `[a, b]` and `[c, d]` via the Tor spectral sequence.
namespace HasTorAmplitudeIn

theorem tensor
    {K L : DMod}
    (hK : HasTorAmplitudeIn (X := RingedSite.ofCommRingSheaf J 𝒪) K a b)
    (hL : HasTorAmplitudeIn (X := RingedSite.ofCommRingSheaf J 𝒪) L c d) :
    HasTorAmplitudeIn (X := RingedSite.ofCommRingSheaf J 𝒪)
      ((SheafOfModules.RingedSite.derivedTensorProduct L).obj K)
      (a + c) (b + d) := by
  -- Route correction: the proof stays on the representative route, but the first stable step is
  -- now explicit: extract bounded flat models for both factors and close the two interval-support
  -- lemmas for their strict tensor complex before rebuilding the derived comparison.
  obtain ⟨E, eE, hEGE, hELE, hEFlat⟩ :=
    exists_flat_representative (E := K) (a := a) (b := b) hK
  obtain ⟨F, eF, hFGE, hFLE, hFFlat⟩ :=
    exists_flat_representative (E := L) (a := c) (b := d) hL
  have hTensorGE :
      CochainComplex.IsStrictlyGE (HomologicalComplex.tensorObj E F) (a + c) :=
    tensorObjIsStrictlyGE_add (a := a) (c := c) hEGE hFGE
  have hTensorLE :
      CochainComplex.IsStrictlyLE (HomologicalComplex.tensorObj E F) (b + d) :=
    tensorObjIsStrictlyLE_add (b := b) (d := d) hELE hFLE
  have hTensorFlat :
      CochainComplex.IsTermwiseFlat (HomologicalComplex.tensorObj E F) :=
    tensorObjIsTermwiseFlatOfIsTermwiseFlat (J := J) (𝒪 := 𝒪) hEFlat hFFlat
  have hTensorModel :
      HasTorAmplitudeIn (X := RingedSite.ofCommRingSheaf J 𝒪)
        (DerivedCategory.Q.obj (HomologicalComplex.tensorObj E F))
        (a + c) (b + d) := by
    -- Proof comment: the strict tensor complex is a flat representative supported in the sum
    -- interval, so the representative criterion applies directly.
    exact
      hasTorAmplitudeIn_of_exists_flat_representative
        (E := DerivedCategory.Q.obj (HomologicalComplex.tensorObj E F))
        (a := a + c)
        (b := b + d)
        ⟨HomologicalComplex.tensorObj E F, Iso.refl _, hTensorGE, hTensorLE, hTensorFlat⟩
  have hAmbientQQ :
      HasTorAmplitudeIn (X := RingedSite.ofCommRingSheaf J 𝒪)
        (((DerivedCategory.Q.obj E : DMod) ⊗ (DerivedCategory.Q.obj F)))
        (a + c) (b + d) := by
    -- Proof comment: replace the strict tensor representative by its ambient tensor image under
    -- the monoidal quotient functor.
    exact
      (hasTorAmplitudeIn_of_iso
        (J := J) (𝒪 := 𝒪)
        (a := a + c) (b := b + d)
        (qObjTensorObjIsoAmbientTensor E F)).1
        hTensorModel
  have hAmbientQL :
      HasTorAmplitudeIn (X := RingedSite.ofCommRingSheaf J 𝒪)
        (((DerivedCategory.Q.obj E : DMod) ⊗ L))
        (a + c) (b + d) := by
    -- Proof comment: transport only the right ambient tensor factor from the representative
    -- `Q.obj F` back to the original object `L`.
    exact
      (hasTorAmplitudeIn_of_iso
        (J := J) (𝒪 := 𝒪)
        (a := a + c) (b := b + d)
        (((tensoringRight DMod).mapIso eF.symm).app (DerivedCategory.Q.obj E))).1
        hAmbientQQ
  have hDerivedRepresentative :
      HasTorAmplitudeIn (X := RingedSite.ofCommRingSheaf J 𝒪)
        ((derivedTensorProduct L).obj (DerivedCategory.Q.obj E))
        (a + c) (b + d) := by
    -- Proof comment: the generic comparison between ambient right tensoring and the derived tensor
    -- functor turns the ambient bound into the desired derived one on the chosen representative.
    exact
      hasTorAmplitudeIn_qObjDerivedTensorProduct
        (J := J) (𝒪 := 𝒪)
        (a := a + c) (b := b + d)
        hAmbientQL
  -- Proof comment: transport the derived-tensor bound from the flat representative `Q.obj E`
  -- back to the original object `K`.
  exact
    (hasTorAmplitudeIn_of_iso
      (J := J) (𝒪 := 𝒪)
      (a := a + c) (b := b + d)
      ((derivedTensorProduct L).mapIso eE.symm)).1
      hDerivedRepresentative

end HasTorAmplitudeIn

end

end SheafOfModules.RingedSite
