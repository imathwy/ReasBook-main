import StacksProject_2024.Chap20.Definition_20_46_1
import StacksProject_2024.Chap06.RingedSpaceModuleCore
import StacksProject_2024.Chap17.SheafOfModulesTensorUnit

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open MonoidalCategory

noncomputable section

universe u

set_option checkBinderAnnotations false

namespace AlgebraicGeometry.RingedSpace

namespace CochainComplex

/-
Domain-style sampling for Lemma 20.46.3:
- primary domain: total tensor products of strictly perfect cochain complexes of module sheaves;
- sampled owner declarations:
  `CochainComplex.IsStrictlyPerfect`,
  `HomologicalComplex.tensorObj`,
  `CochainComplex.tensorObj_isKFlat_of_isKFlat`,
  `AlgebraicGeometry.RingedSpace.CochainComplex.tensorObj_isStrictlyPerfect_of_isStrictlyPerfect`;
- best owner abstraction: the source-facing notion remains `CochainComplex.IsStrictlyPerfect`, but
  the reusable owner theorem should be stated for complexes of modules over an arbitrary sheaf of
  rings on a topological space, with the tensor product complex given by the canonical total tensor
  object `HomologicalComplex.tensorObj K L`;
- primitive data: the two strict-perfectness hypotheses and the canonical tensor datum
  `[HomologicalComplex.HasTensor K L]`;
- derived API: none; specializing `R` to the structure sheaf of a ringed space is ordinary
  ambient specialization, so no parallel wrapper theorem is needed.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma for the total tensor product of strictly perfect complexes of
  `𝒪_X`-modules on a ringed space;
- `core/canonical`: the generalized theorem
  `CochainComplex.tensorObj_isStrictlyPerfect_of_isStrictlyPerfect` for modules over an arbitrary
  sheaf of rings on a topological space;
- `bridge/view`: none; the numbered item is represented directly by the generalized owner theorem,
  and the ringed-space case is obtained by specializing `R = X.presheafedSpace.presheaf`.
-/

variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}

local notation "Mod" => SheafOfModules R
local notation "Cpx" => CochainComplex Mod ℤ

variable {K L : Cpx}
variable [MonoidalCategory (SheafOfModules R)]
variable [MonoidalPreadditive (SheafOfModules R)]
variable [(curriedTensor (SheafOfModules R)).Additive]
variable [∀ M : SheafOfModules R, ((curriedTensor (SheafOfModules R)).obj M).Additive]
variable [HomologicalComplex.HasTensor K L]

/-- Helper for Lemma 20.46.3: if two cochain complexes are strictly bounded below, then their
total tensor complex is strictly bounded below by the sum of the two lower cutoffs. -/
private lemma tensorObjIsStrictlyGE_add
    {E F : Cpx} {a c : ℤ}
    [HomologicalComplex.HasTensor E F]
    (hE : E.IsStrictlyGE a) (hF : F.IsStrictlyGE c) :
    CochainComplex.IsStrictlyGE (HomologicalComplex.tensorObj E F) (a + c) := by
  -- Proof comment: below `a + c`, every antidiagonal summand has either the left term below `a`
  -- or the right term below `c`, so that tensor summand is already zero.
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have hpq' : p + q = n := by
    simpa [ComplexShape.up] using h
  have hpq : p < a ∨ q < c := by
    omega
  cases hpq with
  | inl hp =>
      let T : Mod ⥤ Mod :=
        (CategoryTheory.MonoidalCategory.curriedTensor Mod).flip.obj (F.X q)
      have hzero : IsZero (E.X p) := E.isZero_of_isStrictlyGE a p hp
      have hsrc : IsZero (T.obj (E.X p)) := CategoryTheory.Functor.map_isZero T hzero
      simpa [Category.comp_id, T] using
        hsrc.eq_of_src (HomologicalComplex.ιTensorObj E F p q n h) 0
  | inr hq =>
      let T : Mod ⥤ Mod :=
        (CategoryTheory.MonoidalCategory.curriedTensor Mod).obj (E.X p)
      have hzero : IsZero (F.X q) := F.isZero_of_isStrictlyGE c q hq
      have hsrc : IsZero (T.obj (F.X q)) := CategoryTheory.Functor.map_isZero T hzero
      simpa [Category.comp_id, T] using
        hsrc.eq_of_src (HomologicalComplex.ιTensorObj E F p q n h) 0

/-- Helper for Lemma 20.46.3: if two cochain complexes are strictly bounded above, then their
total tensor complex is strictly bounded above by the sum of the two upper cutoffs. -/
private lemma tensorObjIsStrictlyLE_add
    {E F : Cpx} {b d : ℤ}
    [HomologicalComplex.HasTensor E F]
    (hE : E.IsStrictlyLE b) (hF : F.IsStrictlyLE d) :
    CochainComplex.IsStrictlyLE (HomologicalComplex.tensorObj E F) (b + d) := by
  -- Proof comment: above `b + d`, every antidiagonal summand has either the left term above `b`
  -- or the right term above `d`, so that tensor summand vanishes.
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have hpq' : p + q = n := by
    simpa [ComplexShape.up] using h
  have hpq : b < p ∨ d < q := by
    omega
  cases hpq with
  | inl hp =>
      let T : Mod ⥤ Mod :=
        (CategoryTheory.MonoidalCategory.curriedTensor Mod).flip.obj (F.X q)
      have hzero : IsZero (E.X p) := E.isZero_of_isStrictlyLE b p hp
      have hsrc : IsZero (T.obj (E.X p)) := CategoryTheory.Functor.map_isZero T hzero
      simpa [Category.comp_id, T] using
        hsrc.eq_of_src (HomologicalComplex.ιTensorObj E F p q n h) 0
  | inr hq =>
      let T : Mod ⥤ Mod :=
        (CategoryTheory.MonoidalCategory.curriedTensor Mod).obj (E.X p)
      have hzero : IsZero (F.X q) := F.isZero_of_isStrictlyLE d q hq
      have hsrc : IsZero (T.obj (F.X q)) := CategoryTheory.Functor.map_isZero T hzero
      simpa [Category.comp_id, T] using
        hsrc.eq_of_src (HomologicalComplex.ιTensorObj E F p q n h) 0

/-- Helper for Lemma 20.46.3: the finite interval of left degrees that can contribute to the
tensor totalization once `K` is supported in `[a,b]`. -/
private abbrev tensorDegreeInterval (a b : ℤ) :=
  Set.Icc a b

/-- Helper for Lemma 20.46.3: the degree-`n` tensor summands indexed by the finite interval
`a ≤ p ≤ b`. -/
private noncomputable def tensorDegreeIntervalDiagram
    {K L : Cpx} (n a b : ℤ) :
    Discrete (tensorDegreeInterval a b) ⥤ Mod :=
  Discrete.functor fun s ↦
    ((CategoryTheory.MonoidalCategory.curriedTensor Mod).obj (K.X s.1)).obj (L.X (n - s.1))

/-- Helper for Lemma 20.46.3: the canonical antidiagonal pair `(p, n - p)` satisfies the tensor
index relation for degree `n`. -/
private lemma tensorDegree_rightIndex_condition (p n : ℤ) :
    (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, n - p) = n := by
  -- Proof comment: this is exactly the defining antidiagonal equation `p + (n - p) = n`.
  change p + (n - p) = n
  omega

/-- Helper for Lemma 20.46.3: the tautological cocone from the interval-indexed tensor summands to
the actual degree-`n` tensor term. -/
private noncomputable def tensorDegreeIntervalCocone
    {K L : Cpx} [HomologicalComplex.HasTensor K L] (n a b : ℤ) :
    Cocone (tensorDegreeIntervalDiagram (K := K) (L := L) n a b) where
  pt := (HomologicalComplex.tensorObj K L).X n
  ι := Discrete.natTrans fun s ↦
    HomologicalComplex.ιTensorObj K L s.as.1 (n - s.as.1) n
      (tensorDegree_rightIndex_condition s.as.1 n)

/-- Helper for Lemma 20.46.3: a tensor summand indexed by `p + q = n` can be rewritten using the
canonical expression `q = n - p`. -/
private lemma tensorDegree_rightIndex_eq
    {p q n : ℤ}
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    q = n - p := by
  have hpq : p + q = n := by
    simpa [ComplexShape.up] using h
  omega

/-- Helper for Lemma 20.46.3: if the left tensor index lies outside `[a,b]`, then the
corresponding tensor summand map already vanishes after any postcomposition. -/
private theorem tensorObjLeg_eq_zero_of_leftOutsideBounds
    {K L : Cpx} {n a b p q : ℤ}
    [HomologicalComplex.HasTensor K L]
    (hKge : K.IsStrictlyGE a) (hKle : K.IsStrictlyLE b)
    (hp : p < a ∨ b < p)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n)
    {A : Mod}
    (u : (HomologicalComplex.tensorObj K L).X n ⟶ A) :
    HomologicalComplex.ιTensorObj K L p q n h ≫ u = 0 := by
  -- Proof comment: once `p` lies outside the retained interval, the left tensor factor `K.X p`
  -- is zero, so the entire tensor summand dies before reaching the total tensor degree.
  cases hp with
  | inl hp =>
      let T : Mod ⥤ Mod :=
        (CategoryTheory.MonoidalCategory.curriedTensor Mod).flip.obj (L.X q)
      have hzero : IsZero (K.X p) := K.isZero_of_isStrictlyGE a p hp
      have hsrc : IsZero (T.obj (K.X p)) := CategoryTheory.Functor.map_isZero T hzero
      simpa [T, Category.assoc, HomologicalComplex.ιTensorObj] using
        hsrc.eq_of_src (HomologicalComplex.ιTensorObj K L p q n h ≫ u) 0
  | inr hp =>
      let T : Mod ⥤ Mod :=
        (CategoryTheory.MonoidalCategory.curriedTensor Mod).flip.obj (L.X q)
      have hzero : IsZero (K.X p) := K.isZero_of_isStrictlyLE b p hp
      have hsrc : IsZero (T.obj (K.X p)) := CategoryTheory.Functor.map_isZero T hzero
      simpa [T, Category.assoc, HomologicalComplex.ιTensorObj] using
        hsrc.eq_of_src (HomologicalComplex.ιTensorObj K L p q n h ≫ u) 0

/-- Helper for Lemma 20.46.3: on the retained interval, the universal tensor summand map lands in
the corresponding cocone leg. -/
private theorem tensorDegreeIntervalDescLeg
    {K L : Cpx} {n a b : ℤ}
    [HomologicalComplex.HasTensor K L]
    (s : Cocone (tensorDegreeIntervalDiagram (K := K) (L := L) n a b))
    (p q : ℤ) (hp : p ∈ tensorDegreeInterval a b)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    ((CategoryTheory.MonoidalCategory.curriedTensor Mod).obj (K.X p)).obj (L.X q) ⟶ s.pt := by
  -- Proof comment: the tensor totalization relation determines `q` as `n - p`, so the source is
  -- exactly the interval summand indexed by `p`.
  have hq : q = n - p := tensorDegree_rightIndex_eq h
  subst hq
  exact s.ι.app ⟨⟨p, hp⟩⟩

/-- Helper for Lemma 20.46.3: after restricting to the finite interval `[a,b]`, the resulting
interval-indexed cocone still presents the degree-`n` tensor term. -/
private theorem tensorDegreeIntervalCoconeIsColimit
    {K L : Cpx} (n a b : ℤ)
    [HomologicalComplex.HasTensor K L]
    (hKge : K.IsStrictlyGE a) (hKle : K.IsStrictlyLE b) :
    IsColimit (tensorDegreeIntervalCocone (K := K) (L := L) n a b) := by
  let lift
      (s : Cocone (tensorDegreeIntervalDiagram (K := K) (L := L) n a b))
      (p q : ℤ)
      (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
      ((CategoryTheory.MonoidalCategory.curriedTensor Mod).obj (K.X p)).obj (L.X q) ⟶ s.pt :=
    if hp : p ∈ tensorDegreeInterval a b then
      tensorDegreeIntervalDescLeg (K := K) (L := L) (n := n) (a := a) (b := b) s p q hp h
    else
      0
  let desc
      (s : Cocone (tensorDegreeIntervalDiagram (K := K) (L := L) n a b)) :
      (tensorDegreeIntervalCocone (K := K) (L := L) n a b).pt ⟶ s.pt := by
    simpa [tensorDegreeIntervalCocone, HomologicalComplex.tensorObj] using
      (HomologicalComplex.mapBifunctorDesc
        (K₁ := K) (K₂ := L) (F := curriedTensor Mod)
        (c := ComplexShape.up ℤ) (A := s.pt) (j := n)
        (lift s))
  refine IsColimit.mk ?_ ?_ ?_
  · intro s
    -- Proof comment: descend an arbitrary interval cocone through `mapBifunctorDesc`, keeping the
    -- retained interval legs and sending every discarded left index to `0`.
    exact desc s
  · intro s t
    -- Proof comment: on an interval summand, the descended map evaluates to the prescribed cocone
    -- leg because the `if`-branch is positive there.
    simpa [desc, lift, tensorDegreeIntervalCocone, tensorDegreeIntervalDescLeg, dif_pos t.as.2,
      HomologicalComplex.tensorObj] using
      (HomologicalComplex.ι_mapBifunctorDesc
        (K₁ := K) (K₂ := L) (F := curriedTensor Mod)
        (c := ComplexShape.up ℤ) (A := s.pt) (j := n)
        (f := lift s)
        t.as.1 (n - t.as.1) (tensorDegree_rightIndex_condition t.as.1 n))
  · intro s m hm
    -- Proof comment: two maps out of the tensor degree agree once they agree on every tensor
    -- summand; the retained summands use `hm`, and the discarded ones are already zero.
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    by_cases hp : p ∈ tensorDegreeInterval a b
    · have hq : q = n - p := tensorDegree_rightIndex_eq h
      subst hq
      let t : Discrete (tensorDegreeInterval a b) := ⟨⟨p, hp⟩⟩
      have hleg :
          HomologicalComplex.ιTensorObj K L p (n - p) n (tensorDegree_rightIndex_condition p n) ≫
              m =
            s.ι.app t := by
        simpa [t, tensorDegreeIntervalCocone] using hm t
      have hdesc :
          HomologicalComplex.ιTensorObj K L p (n - p) n (tensorDegree_rightIndex_condition p n) ≫
              desc s =
            s.ι.app t := by
        simpa [desc, lift, t, tensorDegreeIntervalDescLeg, dif_pos hp,
          HomologicalComplex.tensorObj] using
          (HomologicalComplex.ι_mapBifunctorDesc
            (K₁ := K) (K₂ := L) (F := curriedTensor Mod)
            (c := ComplexShape.up ℤ) (A := s.pt) (j := n)
            (f := lift s)
            p (n - p) (tensorDegree_rightIndex_condition p n))
      exact hleg.trans hdesc.symm
    · have hp' : p < a ∨ b < p := by
        rw [tensorDegreeInterval, Set.mem_Icc] at hp
        omega
      have hzero_m :
          HomologicalComplex.ιTensorObj K L p q n h ≫ m = 0 :=
        tensorObjLeg_eq_zero_of_leftOutsideBounds
          (K := K) (L := L) (n := n) (a := a) (b := b)
          hKge hKle hp' h m
      have hzero_desc :
          HomologicalComplex.ιTensorObj K L p q n h ≫ desc s = 0 :=
        tensorObjLeg_eq_zero_of_leftOutsideBounds
          (K := K) (L := L) (n := n) (a := a) (b := b)
          hKge hKle hp' h
          (desc s)
      exact hzero_m.trans hzero_desc.symm

/-- Helper for Lemma 20.46.3: the zero module sheaf is a finite-free retract. -/
private theorem finiteFreeRetractModuleProperty_zero :
    SheafOfModules.finiteFreeRetractModuleProperty R (⊥_ Mod) := by
  -- Proof comment: the zero module is isomorphic to the free sheaf on the empty index set, so it
  -- lies in the retract closure of finite free sheaves.
  let _ : HasInitial Mod := SheafOfModules.sheafOfModules_hasInitial_of_free_empty (𝒪 := R)
  let X : Mod := (SheafOfModules.free.{u} (ULift.{u, 0} PEmpty) : Mod)
  have hX : Limits.IsInitial X := by
    refine Limits.IsInitial.ofUniqueHom (fun Y ↦ ?_) (fun Y f ↦ ?_)
    · exact Y.freeHomEquiv.symm (fun i : ULift.{u, 0} PEmpty ↦ PEmpty.elim i.down)
    · apply Y.freeHomEquiv.injective
      funext i
      exact PEmpty.elim i.down
  have hFree : SheafOfModules.finiteFreeRetractModuleProperty R X := by
    exact SheafOfModules.finiteFreeRetractModuleProperty_of_retract_free
      (𝒪 := R) (M := X) (L := ULift.{u, 0} PEmpty) (Retract.refl _)
  let e : (⊥_ Mod) ≅ X := (Limits.initialIsInitial.isZero).iso hX.isZero
  exact (SheafOfModules.finiteFreeRetractModuleProperty R).prop_of_iso e.symm hFree

/-- Helper for Lemma 20.46.3: binary biproducts of finite-free-retract module sheaves are again
finite-free-retract module sheaves. -/
private theorem finiteFreeRetractModuleProperty_biprod
    {M N : Mod}
    [Limits.HasBinaryBiproduct M N]
    (hM : SheafOfModules.finiteFreeRetractModuleProperty R M)
    (hN : SheafOfModules.finiteFreeRetractModuleProperty R N) :
    SheafOfModules.finiteFreeRetractModuleProperty R (M ⊞ N) := by
  -- Proof comment: choose retracts of `M` and `N` onto finite free models, take their coproduct,
  -- and identify the coproduct free model with a single free sheaf on the sum-type index set.
  obtain ⟨I, hI, ⟨rM⟩⟩ :=
    (SheafOfModules.finiteFreeRetractModuleProperty_iff M).1 hM
  obtain ⟨J, hJ, ⟨rN⟩⟩ :=
    (SheafOfModules.finiteFreeRetractModuleProperty_iff N).1 hN
  let FK : Mod := (SheafOfModules.free.{u} I : Mod)
  let FL : Mod := (SheafOfModules.free.{u} J : Mod)
  let rCoprod : Retract (M ⨿ N) (Limits.coprod FK FL) := {
    i := Limits.coprod.map rM.i rN.i
    r := Limits.coprod.map rM.r rN.r
    retract := by
      -- Proof comment: the coproduct retract is determined componentwise by the two given
      -- retract presentations.
      apply Limits.coprod.hom_ext
      · simp
      · simp
  }
  let _ : Finite I := hI
  let _ : Finite J := hJ
  let _ : Fintype I := Fintype.ofFinite I
  let _ : Fintype J := Fintype.ofFinite J
  let _ : Finite (I ⊕ J) := Finite.of_fintype (I ⊕ J)
  let FSum : Mod := (SheafOfModules.free.{u} (I ⊕ J) : Mod)
  let cSum : Limits.BinaryCofan I J := Limits.BinaryCofan.mk Sum.inl Sum.inr
  have hcSum : Limits.IsColimit cSum := by
    refine Limits.BinaryCofan.IsColimit.mk cSum (fun {T} f g ↦ Sum.elim f g) ?_ ?_ ?_
    · intro T f g
      ext x
      rfl
    · intro T f g
      ext x
      rfl
    · intro T f g m hm₁ hm₂
      ext x
      cases x with
      | inl x =>
          simpa using congrFun hm₁ x
      | inr x =>
          simpa using congrFun hm₂ x
  let pairFreeIso :
      CategoryTheory.Limits.pair FK FL ≅
        (CategoryTheory.Limits.pair I J ⋙ SheafOfModules.freeFunctor (R := R)) :=
    (show
      (CategoryTheory.Limits.pair I J ⋙ SheafOfModules.freeFunctor (R := R)) ≅
        CategoryTheory.Limits.pair FK FL from
        CategoryTheory.Limits.mapPairIso (Iso.refl FK) (Iso.refl FL)).symm
  let cMapped := (SheafOfModules.freeFunctor (R := R)).mapCocone cSum
  have hcMapped : Limits.IsColimit cMapped := by
    -- Proof comment: `freeFunctor` preserves the sum-type coproduct, so the free sheaf on
    -- `I ⊕ J` identifies with the coproduct of the two free models.
    simpa [cSum, cMapped, FK, FL, FSum] using
      (CategoryTheory.Limits.isColimitOfPreserves
        (F := SheafOfModules.freeFunctor (R := R)) hcSum)
  let cFree : Limits.Cocone (CategoryTheory.Limits.pair FK FL) :=
    (CategoryTheory.Limits.Cocone.precompose pairFreeIso.hom).obj cMapped
  have hcFree : Limits.IsColimit cFree :=
    (CategoryTheory.Limits.IsColimit.precomposeHomEquiv pairFreeIso cMapped).2 hcMapped
  let cCoprod : Limits.Cocone (CategoryTheory.Limits.pair FK FL) :=
    Limits.BinaryCofan.mk Limits.coprod.inl Limits.coprod.inr
  have hcCoprod : Limits.IsColimit cCoprod := by
    simpa [cCoprod] using (Limits.coprodIsCoprod FK FL)
  let eFree : FSum ≅ Limits.coprod FK FL := by
    simpa [cMapped, cFree, cCoprod, pairFreeIso, FSum] using
      hcFree.coconePointUniqueUpToIso hcCoprod
  have hFreeCoprod : SheafOfModules.finiteFreeRetractModuleProperty R (Limits.coprod FK FL) := by
    -- Proof comment: the coproduct free model is canonically a single finite free sheaf indexed
    -- by the sum type.
    exact SheafOfModules.finiteFreeRetractModuleProperty_of_retract_free
      (𝒪 := R) (M := Limits.coprod FK FL) (L := I ⊕ J) (Retract.ofIso eFree.symm)
  have hCoprod : SheafOfModules.finiteFreeRetractModuleProperty R (M ⨿ N) := by
    -- Proof comment: coproducts of retracts remain retracts of the coproduct free model.
    exact (SheafOfModules.finiteFreeRetractModuleProperty R).prop_of_retract rCoprod hFreeCoprod
  -- Proof comment: binary biproducts agree with coproducts in this abelian category, so transport
  -- the coproduct retract presentation across the canonical comparison.
  exact (SheafOfModules.finiteFreeRetractModuleProperty R).prop_of_iso
    (Limits.biprod.isoCoprod M N).symm hCoprod

/-- Helper for Lemma 20.46.3: finite-free-retract module sheaves contain a zero object. -/
private instance finiteFreeRetractModuleProperty_containsZero :
    (SheafOfModules.finiteFreeRetractModuleProperty R).ContainsZero where
  exists_zero := by
    let _ : HasInitial Mod := SheafOfModules.sheafOfModules_hasInitial_of_free_empty (𝒪 := R)
    exact ⟨⊥_ Mod, Limits.initialIsInitial.isZero, finiteFreeRetractModuleProperty_zero (R := R)⟩

/-- Helper for Lemma 20.46.3: finite-free-retract module sheaves are closed under binary
coproducts. -/
private instance finiteFreeRetractModuleProperty_isClosedUnderBinaryCoproducts :
    (SheafOfModules.finiteFreeRetractModuleProperty R).IsClosedUnderBinaryCoproducts where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    let X₁ := p.diag.obj (.mk .left)
    let X₂ := p.diag.obj (.mk .right)
    let B : BinaryCofan X₁ X₂ := BinaryCofan.mk (p.ι.app (.mk .left)) (p.ι.app (.mk .right))
    have hB : IsColimit B := by
      let hp :=
        ((IsColimit.precomposeHomEquiv (diagramIsoPair p.diag).symm p.cocone).2 p.isColimit)
      simpa [B, BinaryCofan.inl, BinaryCofan.inr] using
        (IsColimit.ofIsoColimit hp (isoBinaryCofanMk _))
    have e : X ≅ X₁ ⨿ X₂ := by
      simpa [B] using hB.coconePointUniqueUpToIso (coprodIsCoprod X₁ X₂)
    -- Proof comment: every binary coproduct presentation is canonically isomorphic to the
    -- standard coproduct, so the explicit coproduct closure lemma applies.
    exact (SheafOfModules.finiteFreeRetractModuleProperty R).prop_of_iso
      ((Limits.biprod.isoCoprod X₁ X₂) ≪≫ e.symm)
      (finiteFreeRetractModuleProperty_biprod (R := R)
        (p.prop_diag_obj (.mk .left)) (p.prop_diag_obj (.mk .right)))

/-- Helper for Lemma 20.46.3: tensoring a finite free sheaf `free I` with `free J` is a finite
coproduct of copies of `free I`, hence lies in `finiteFreeRetractModuleProperty R`. -/
private theorem tensorFree_finiteFreeRetract
    (I J : Type u) [Finite I] [Finite J] :
    SheafOfModules.finiteFreeRetractModuleProperty R
      (((CategoryTheory.MonoidalCategory.curriedTensor Mod).obj
          (SheafOfModules.free.{u} I : Mod)).obj
        (SheafOfModules.free.{u} J : Mod)) := by
  let P : ObjectProperty Mod := SheafOfModules.finiteFreeRetractModuleProperty R
  let _ : P.ContainsZero := finiteFreeRetractModuleProperty_containsZero (R := R)
  let _ : P.IsClosedUnderBinaryCoproducts :=
    finiteFreeRetractModuleProperty_isClosedUnderBinaryCoproducts (R := R)
  let _ : P.IsClosedUnderFiniteCoproducts :=
    CategoryTheory.ObjectProperty.IsClosedUnderFiniteCoproducts.mk'
  let _ : P.IsClosedUnderColimitsOfShape (Discrete J) := by
    infer_instance
  let FK : Mod := (SheafOfModules.free.{u} I : Mod)
  let F : Discrete J ⥤ Mod := Discrete.functor fun _ ↦ SheafOfModules.unit R
  let eTensorRight :
      ((CategoryTheory.MonoidalCategory.curriedTensor Mod).flip.obj
          (SheafOfModules.unit R : Mod)) ≅ 𝟭 Mod :=
    (tensoringRight Mod).mapIso (SheafOfModules.unitIsoTensorUnit (R := R)) ≪≫
      MonoidalCategory.rightUnitorNatIso Mod
  let cTensor :=
    ((CategoryTheory.MonoidalCategory.curriedTensor Mod).obj FK).mapCocone
      (SheafOfModules.freeCofan (R := R) J)
  have hcTensor : IsColimit cTensor := by
    exact CategoryTheory.Limits.isColimitOfPreserves
      ((CategoryTheory.MonoidalCategory.curriedTensor Mod).obj FK)
      (SheafOfModules.isColimitFreeCofan (R := R) J)
  have hSummand :
      ∀ j : Discrete J,
        P ((F ⋙ (CategoryTheory.MonoidalCategory.curriedTensor Mod).obj FK).obj j) := by
    intro j
    have hFK : P FK := by
      exact SheafOfModules.finiteFreeRetractModuleProperty_of_retract_free
        (𝒪 := R) (M := FK) (L := I) (Retract.refl _)
    simpa [F, FK] using
      (P.prop_of_iso (eTensorRight.app FK).symm hFK)
  -- Proof comment: `free J` is the finite coproduct of `J` copies of the unit sheaf, and left
  -- tensoring by `free I` preserves those finite coproducts.
  simpa [F, FK] using
    CategoryTheory.ObjectProperty.prop_of_isColimit
      (P := P) (J := Discrete J)
      (F := F ⋙ (CategoryTheory.MonoidalCategory.curriedTensor Mod).obj FK)
      (c := cTensor) hcTensor hSummand

/-- Helper for Lemma 20.46.3: tensoring two finite-free-retract module sheaves again yields a
finite-free-retract module sheaf. -/
private lemma tensorSummand_finiteFreeRetract
    {M N : Mod}
    (hM : SheafOfModules.finiteFreeRetractModuleProperty R M)
    (hN : SheafOfModules.finiteFreeRetractModuleProperty R N) :
    SheafOfModules.finiteFreeRetractModuleProperty R
      (((CategoryTheory.MonoidalCategory.curriedTensor Mod).obj M).obj N) := by
  -- Proof comment: choose retract presentations of the two factors by finite free sheaves, tensor
  -- those retracts through the left and right tensor functors, and finish from the finite-coproduct
  -- model for the tensor of the two free factors.
  obtain ⟨I, hI, ⟨rM⟩⟩ :=
    (SheafOfModules.finiteFreeRetractModuleProperty_iff M).1 hM
  obtain ⟨J, hJ, ⟨rN⟩⟩ :=
    (SheafOfModules.finiteFreeRetractModuleProperty_iff N).1 hN
  let FK : Mod := (SheafOfModules.free.{u} I : Mod)
  let FL : Mod := (SheafOfModules.free.{u} J : Mod)
  let _ : Finite I := hI
  let _ : Finite J := hJ
  let rLeft :
      Retract (((CategoryTheory.MonoidalCategory.curriedTensor Mod).obj M).obj N)
        (((CategoryTheory.MonoidalCategory.curriedTensor Mod).obj FK).obj N) :=
    rM.map ((CategoryTheory.MonoidalCategory.curriedTensor Mod).flip.obj N)
  let rRight :
      Retract (((CategoryTheory.MonoidalCategory.curriedTensor Mod).obj FK).obj N)
        (((CategoryTheory.MonoidalCategory.curriedTensor Mod).obj FK).obj FL) :=
    rN.map ((CategoryTheory.MonoidalCategory.curriedTensor Mod).obj FK)
  let rTensor :
      Retract (((CategoryTheory.MonoidalCategory.curriedTensor Mod).obj M).obj N)
        (((CategoryTheory.MonoidalCategory.curriedTensor Mod).obj FK).obj FL) :=
    rLeft.trans rRight
  have hTensor :
      SheafOfModules.finiteFreeRetractModuleProperty R
        (((CategoryTheory.MonoidalCategory.curriedTensor Mod).obj FK).obj FL) := by
    simpa [FK, FL] using tensorFree_finiteFreeRetract (R := R) I J
  exact (SheafOfModules.finiteFreeRetractModuleProperty R).prop_of_retract rTensor hTensor

/-- Helper for Lemma 20.46.3: once the two complexes are bounded and termwise finite-free
retracts, each tensor degree retracts onto the finite coproduct of its active antidiagonal
summands and hence lies in `finiteFreeRetractModuleProperty R`. -/
private lemma tensorDegree_finiteFreeRetract
    {K L : Cpx} (n a b c d : ℤ)
    (hKge : K.IsStrictlyGE a) (hKle : K.IsStrictlyLE b)
    (hLge : L.IsStrictlyGE c) (hLle : L.IsStrictlyLE d)
    (hKterm : ∀ i : ℤ, SheafOfModules.finiteFreeRetractModuleProperty R (K.X i))
    (hLterm : ∀ i : ℤ, SheafOfModules.finiteFreeRetractModuleProperty R (L.X i)) :
    SheafOfModules.finiteFreeRetractModuleProperty R ((HomologicalComplex.tensorObj K L).X n) := by
  -- Route correction: instead of packaging a bespoke retract onto the active antidiagonal, use the
  -- finite interval of left indices `p ∈ [a,b]` and the owner colimit `mapBifunctorDesc`; all
  -- omitted summands are already zero because `K` vanishes outside that interval.
  let P : ObjectProperty Mod := SheafOfModules.finiteFreeRetractModuleProperty R
  let _ : Finite (tensorDegreeInterval a b) := (Set.finite_Icc a b).to_subtype
  let _ : Fintype (tensorDegreeInterval a b) := Fintype.ofFinite (tensorDegreeInterval a b)
  let _ : P.IsClosedUnderFiniteCoproducts :=
    CategoryTheory.ObjectProperty.IsClosedUnderFiniteCoproducts.mk'
  let _ : P.IsClosedUnderColimitsOfShape (Discrete (tensorDegreeInterval a b)) := by
    infer_instance
  let F := tensorDegreeIntervalDiagram (K := K) (L := L) n a b
  have hSummand :
      ∀ j : Discrete (tensorDegreeInterval a b), P (F.obj j) := by
    intro j
    -- Proof comment: every retained interval summand is the tensor of two termwise
    -- finite-free-retract module sheaves.
    simpa [P, F, tensorDegreeIntervalDiagram] using
      tensorSummand_finiteFreeRetract
        (R := R) (M := K.X j.as.1) (N := L.X (n - j.as.1))
        (hKterm j.as.1) (hLterm (n - j.as.1))
  -- Proof comment: the interval diagram is finite, so finite-coproduct closure promotes the
  -- summandwise property to the colimit, which is the actual tensor degree by the preceding
  -- interval-cocone comparison.
  exact CategoryTheory.ObjectProperty.prop_of_isColimit
    (P := P) (J := Discrete (tensorDegreeInterval a b)) (F := F)
    (c := tensorDegreeIntervalCocone (K := K) (L := L) n a b)
    (tensorDegreeIntervalCoconeIsColimit (K := K) (L := L) n a b hKge hKle)
    hSummand

-- Proof sketch: boundedness of the total tensor complex follows from boundedness of the two
-- strictly perfect inputs. In each degree, the total tensor term is a finite direct sum of tensor
-- products of retracts of finite free module sheaves, hence again a retract of a finite free
-- module sheaf.
/-- Lemma 20.46.3: the canonical total tensor product of two strictly perfect complexes of modules
over a sheaf of rings is strictly perfect. Specializing to the structure sheaf of a ringed space
recovers the Stacks statement for `𝒪_X`-modules. -/
@[stacks 09J2]
theorem tensorObj_isStrictlyPerfect_of_isStrictlyPerfect
    (K L : Cpx) [HomologicalComplex.HasTensor K L]
    (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L) :
    IsStrictlyPerfect (HomologicalComplex.tensorObj K L) := by
  -- Proof comment: unpack strict perfectness into support bounds and termwise finite-free-retract
  -- data, then rebuild the tensor complex from the additive bounds and the finite active
  -- antidiagonal in each degree.
  obtain ⟨a, b, hKge, hKle⟩ := hK.bounded
  obtain ⟨c, d, hLge, hLle⟩ := hL.bounded
  refine ⟨?_, ?_⟩
  · -- Proof comment: the tensor support is bounded by the sum of the lower and upper bounds.
    exact ⟨a + c, b + d,
      tensorObjIsStrictlyGE_add hKge hLge,
      tensorObjIsStrictlyLE_add hKle hLle⟩
  · -- Proof comment: in each degree, discard the zero off-box summands and keep the finite active
    -- coproduct of tensor summands.
    intro n
    exact tensorDegree_finiteFreeRetract
      (K := K) (L := L) n a b c d hKge hKle hLge hLle
      (fun i ↦ hK.term_retractClosure i)
      (fun i ↦ hL.term_retractClosure i)

end CochainComplex

end AlgebraicGeometry.RingedSpace
