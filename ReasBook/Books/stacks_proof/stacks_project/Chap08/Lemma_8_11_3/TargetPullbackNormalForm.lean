import StacksProject_2024.Chap08.Lemma_8_11_3.FactorizationEssentialImage

open CategoryTheory
open BasedFunctor
open Functor
open Functor.Fiber
open Functor.IsStronglyCartesian
open FibredCategoryOver

universe w v₁ u₁ v₂ u₂

namespace CategoryTheory

namespace StackInGroupoidsOver.Hom

section

variable {C : Type u₁} [Category.{v₁} C]
variable {J : GrothendieckTopology C}
variable {Xₛ Yₛ : StackInGroupoidsOver.{u₁, v₁, max u₁ v₁, v₁} J}

/-- Helper for Lemma 8.11.3: the comparison arrow stored in a canonical factorization object is
an isomorphism in the target total category. -/
theorem canonicalFactorizationComparison_isIso
    (F : Xₛ ⟶ Yₛ)
    (P : (fibredInGroupoidsFactorization (toBasedFunctor F)).obj) :
    IsIso P.comparison := by
  -- Forget the fiberwise isomorphism carried by `P` to the total category of `Yₛ`.
  let e : (toBasedFunctor F).obj P.obj.fst.1 ≅ P.obj.snd.1 :=
    { hom := P.comparison
      inv := P.obj.iso.inv.1
      hom_inv_id := by
        exact congrArg Subtype.val P.obj.iso.hom_inv_id
      inv_hom_id := by
        exact congrArg Subtype.val P.obj.iso.inv_hom_id }
  exact ⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩

/-- Helper for Lemma 8.11.3: a strongly cartesian arrow can be reindexed from its owner base
map to any externally specified base map that the same arrow lifts. -/
theorem isStronglyCartesian_of_externalHomLift_forGerbeCriterion
    {𝒮 : Type u₁} {𝒳 : Type (max u₁ v₁)} [Category.{v₁} 𝒮] [Category.{v₁} 𝒳]
    (p : 𝒳 ⥤ 𝒮)
    {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} (φ : a ⟶ b)
    [p.IsStronglyCartesian (p.map φ) φ] [p.IsHomLift f φ] :
    p.IsStronglyCartesian f φ := by
  -- Normalize the external source and target to the actual source and target of `φ`.
  have ha : p.obj a = R := IsHomLift.domain_eq p f φ
  have hb : p.obj b = S := IsHomLift.codomain_eq p f φ
  subst ha
  subst hb
  -- Once the lifted base arrow is identified with `p.map φ`, the original instance applies.
  have hf : f = p.map φ := IsHomLift.eq_of_isHomLift p f φ
  subst hf
  infer_instance

/-- Helper for Lemma 8.11.3: the explicit pullback object of the target factorization along a
single target arrow. -/
noncomputable def factorizationTargetPullbackObject
    (F : Xₛ ⟶ Yₛ)
    (P : (fibredInGroupoidsFactorization (toBasedFunctor F)).obj)
    {y' : Yₛ.S}
    (b : y' ⟶ (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj P) :
    (fibredInGroupoidsFactorization (toBasedFunctor F)).obj :=
  { U := Yₛ.p.obj y'
    obj :=
      { fst := fibredInGroupoidsFactorizationToTarget_left_pullback (toBasedFunctor F) P b
        snd := Functor.Fiber.mk rfl
        iso :=
          fibredInGroupoidsFactorizationToTarget_pulledback_comparison_iso
            (toBasedFunctor F) P b } }

/-- Helper for Lemma 8.11.3: the source component of the explicit target pullback projection
lifts the transported base arrow. -/
theorem factorizationTargetPullback_left_map_isHomLift
    (F : Xₛ ⟶ Yₛ)
    (P : (fibredInGroupoidsFactorization (toBasedFunctor F)).obj)
    {y' : Yₛ.S}
    (b : y' ⟶ (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj P) :
    Xₛ.p.IsHomLift (fibredInGroupoidsFactorizationToTarget_pullbackBase (toBasedFunctor F) b)
      (fibredInGroupoidsFactorizationToTarget_left_pullback_map (toBasedFunctor F) P b) := by
  -- The chosen left pullback map is strongly cartesian, hence in particular a lift.
  exact
    (fibredInGroupoidsFactorizationToTarget_left_pullback_map_isStronglyCartesian
      (toBasedFunctor F) P b).toIsHomLift

/-- Helper for Lemma 8.11.3: the explicit target pullback projection satisfies the defining
two-fibre-product square. -/
theorem factorizationTargetPullback_comm
    (F : Xₛ ⟶ Yₛ)
    (P : (fibredInGroupoidsFactorization (toBasedFunctor F)).obj)
    {y' : Yₛ.S}
    (b : y' ⟶ (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj P) :
    CommSq
      ((toBasedFunctor F).map
        (fibredInGroupoidsFactorizationToTarget_left_pullback_map (toBasedFunctor F) P b))
      (factorizationTargetPullbackObject F P b).comparison
      P.comparison
      b := by
  let F' := toBasedFunctor F
  let f := fibredInGroupoidsFactorizationToTarget_pullbackBase F' b
  let a := fibredInGroupoidsFactorizationToTarget_left_pullback_map F' P b
  have ha : Xₛ.p.IsStronglyCartesian f a := by
    simpa [F', f, a] using
      fibredInGroupoidsFactorizationToTarget_left_pullback_map_isStronglyCartesian F' P b
  letI : Xₛ.p.IsStronglyCartesian f a := ha
  have hFa : Yₛ.p.IsStronglyCartesian f (F'.map a) := by
    -- Transport the owner-level strong-cartesian instance for `F'.map a` to the base arrow `f`.
    have hmap : Yₛ.p.IsStronglyCartesian (Yₛ.p.map (F'.map a)) (F'.map a) :=
      inferInstance
    letI : Yₛ.p.IsStronglyCartesian (Yₛ.p.map (F'.map a)) (F'.map a) := hmap
    letI : Yₛ.p.IsHomLift f (F'.map a) := by
      infer_instance
    exact isStronglyCartesian_of_externalHomLift_forGerbeCriterion
      (p := Yₛ.p) (f := f) (F'.map a)
  have hb : Yₛ.p.IsStronglyCartesian f b := by
    -- The target arrow `b` also lifts the transported base arrow by construction.
    letI : Yₛ.p.IsHomLift f b :=
      fibredInGroupoidsFactorizationToTarget_pullbackBase_isHomLift F' b
    exact isStronglyCartesian_of_externalHomLift_forGerbeCriterion
      (p := Yₛ.p) (f := f) b
  letI : IsIso P.comparison := fibredInGroupoidsFactorization_comparison_isIso F' P
  have hleftOver : Yₛ.p.IsHomLift f (F'.map a ≫ P.comparison) := by
    -- Compose the lifted source map with the vertical comparison stored in `P`.
    have hFaOver : Yₛ.p.IsHomLift f (F'.map a) := by
      infer_instance
    letI : Yₛ.p.IsHomLift f (F'.map a) := hFaOver
    letI : Yₛ.p.IsHomLift (𝟙 P.U) P.comparison := P.comparison_over
    exact IsHomLift.comp_lift_id_right' (p := Yₛ.p) f (F'.map a) P.U P.comparison
  have hleft : Yₛ.p.IsStronglyCartesian f (F'.map a ≫ P.comparison) := by
    -- The composite of the cartesian image of `a` with the vertical isomorphism is cartesian.
    letI : Yₛ.p.IsStronglyCartesian f (F'.map a) := hFa
    letI : Yₛ.p.IsHomLift (𝟙 P.U) P.comparison := P.comparison_over
    have hcomparison : Yₛ.p.IsStronglyCartesian (𝟙 P.U) P.comparison :=
      Functor.IsStronglyCartesian.of_isIso Yₛ.p (𝟙 P.U) P.comparison
    letI : Yₛ.p.IsStronglyCartesian (𝟙 P.U) P.comparison := hcomparison
    simpa using
      (show Yₛ.p.IsStronglyCartesian (f ≫ 𝟙 P.U) (F'.map a ≫ P.comparison) from
        inferInstance)
  have hbaseId : f = (Iso.refl (Yₛ.p.obj y')).hom ≫ f := (Category.id_comp f).symm
  let e : F'.obj ((fibredInGroupoidsFactorizationToTarget_left_pullback F' P b).1) ≅ y' :=
    @Functor.IsStronglyCartesian.domainIsoOfBaseIso _ _ _ _ Yₛ.p
      _ _ _ _ _ _ _ _ _ hbaseId b (F'.map a ≫ P.comparison) hb hleft
  have hfac : e.hom ≫ b = F'.map a ≫ P.comparison := by
    -- The comparison isomorphism was chosen by the same strong-cartesian uniqueness equation.
    simpa [e] using
      (@Functor.IsStronglyCartesian.fac _ _ _ _ Yₛ.p
        _ _ _ _ f b hb
        _ _ (Iso.refl (Yₛ.p.obj y')).hom f hbaseId
        (F'.map a ≫ P.comparison) hleftOver)
  refine ⟨?_⟩
  simpa [factorizationTargetPullbackObject, fibredInGroupoidsFactorizationToTarget_left_pullback_map]
    using hfac.symm

/-- Helper for Lemma 8.11.3: the explicit target pullback object maps to the original
factorization object over the given target arrow. -/
noncomputable def factorizationTargetPullbackProjection
    (F : Xₛ ⟶ Yₛ)
    (P : (fibredInGroupoidsFactorization (toBasedFunctor F)).obj)
    {y' : Yₛ.S}
    (b : y' ⟶ (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj P) :
    factorizationTargetPullbackObject F P b ⟶ P :=
  { base := fibredInGroupoidsFactorizationToTarget_pullbackBase (toBasedFunctor F) b
    a := fibredInGroupoidsFactorizationToTarget_left_pullback_map (toBasedFunctor F) P b
    a_over := factorizationTargetPullback_left_map_isHomLift F P b
    b := b
    b_over := fibredInGroupoidsFactorizationToTarget_pullbackBase_isHomLift (toBasedFunctor F) b
    comm := factorizationTargetPullback_comm F P b }

/-- Helper for Lemma 8.11.3: the explicit target pullback projection is strongly cartesian for
the target projection. -/
theorem factorizationTargetPullbackProjection_isStronglyCartesian
    (F : Xₛ ⟶ Yₛ)
    (P : (fibredInGroupoidsFactorization (toBasedFunctor F)).obj)
    {y' : Yₛ.S}
    (b : y' ⟶ (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj P) :
    (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.IsStronglyCartesian b
      (factorizationTargetPullbackProjection F P b) := by
  -- The Chapter 4 strong-cartesian criterion reduces the proof to the left component.
  simpa [factorizationTargetPullbackProjection] using
    fibredInGroupoidsFactorizationToTarget_hom_isStronglyCartesian_of_left
      (toBasedFunctor F)
      (factorizationTargetPullbackProjection F P b)
      (fibredInGroupoidsFactorizationToTarget_left_pullback_map_isStronglyCartesian
        (toBasedFunctor F) P b)

/-- Helper for Lemma 8.11.3: the explicit target pullback object is isomorphic to the canonical
pullback chosen for the target factorization. -/
theorem factorizationTargetPullback_iso_canonical
    (F : Xₛ ⟶ Yₛ)
    (P : (fibredInGroupoidsFactorization (toBasedFunctor F)).obj)
    {y' : Yₛ.S}
    (b : y' ⟶ (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj P)
    [IsFibredInGroupoids (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor] :
    Nonempty
      ((Functor.Fiber.mk (p := (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor)
          (show (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj
              (factorizationTargetPullbackObject F P b) = y' from rfl)) ≅
        ((canonicalPullbackChoice
            (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor).pullbackFunctor b).obj
          (Functor.Fiber.mk
            (p := (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor)
            (show (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj P =
                (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj P from
              rfl))) := by
  let Ftarget := fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)
  have hη :
      Ftarget.toFunctor.IsStronglyCartesian b
        (factorizationTargetPullbackProjection F P b) :=
    factorizationTargetPullbackProjection_isStronglyCartesian F P b
  letI :
      Ftarget.toFunctor.IsStronglyCartesian
        (Ftarget.toFunctor.map (factorizationTargetPullbackProjection F P b))
        (factorizationTargetPullbackProjection F P b) := by
    simpa [Ftarget, factorizationTargetPullbackProjection] using hη
  -- Compare this explicit cartesian lift with the canonical one for the same target arrow.
  simpa [Ftarget, factorizationTargetPullbackProjection] using
    stronglyCartesianDomain_iso_canonicalPullback_nonempty
      (p := Ftarget.toFunctor) (factorizationTargetPullbackProjection F P b)

/-- Helper for Lemma 8.11.3: the source component of the explicit target pullback is the
canonical pullback of the source component over the transported target base arrow. -/
theorem factorizationTargetPullbackSourceIsoCanonical
    (F : Xₛ ⟶ Yₛ)
    (P : (fibredInGroupoidsFactorization (toBasedFunctor F)).obj)
    {y' : Yₛ.S}
    (b : y' ⟶ (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj P) :
    Nonempty
      ((factorizationTargetPullbackObject F P b).obj.fst ≅
        ((canonicalPullbackChoice Xₛ.p).pullbackFunctor
            (fibredInGroupoidsFactorizationToTarget_pullbackBase (toBasedFunctor F) b)).obj
          P.obj.fst) := by
  let F' := toBasedFunctor F
  let f := fibredInGroupoidsFactorizationToTarget_pullbackBase F' b
  let a := fibredInGroupoidsFactorizationToTarget_left_pullback_map F' P b
  let hcX := canonicalPullbackChoice Xₛ.p
  let k := hcX.map f P.obj.fst
  have ha : Xₛ.p.IsStronglyCartesian f a := by
    -- The explicit source component was built by the same source-side cartesian pullback.
    simpa [F', f, a] using
      fibredInGroupoidsFactorizationToTarget_left_pullback_map_isStronglyCartesian F' P b
  have hk : Xₛ.p.IsStronglyCartesian f k := by
    -- The canonical pullback arrow is strongly cartesian over the identical external base map.
    simpa [hcX, k] using hcX.isStronglyCartesian f P.obj.fst
  letI : Xₛ.p.IsStronglyCartesian f k := hk
  letI : Xₛ.p.IsStronglyCartesian f a := ha
  let e :
      (factorizationTargetPullbackObject F P b).obj.fst.1 ≅
        ((hcX.pullbackFunctor f).obj P.obj.fst).1 :=
    @Functor.IsStronglyCartesian.domainIsoOfBaseIso _ _ _ _ Xₛ.p
      _ _ _ _ _ _ f f (Iso.refl (Yₛ.p.obj y'))
      (show f = (Iso.refl (Yₛ.p.obj y')).hom ≫ f by simp)
      k a hk ha
  have hhom : Xₛ.p.IsHomLift (𝟙 (Yₛ.p.obj y')) e.hom := by
    -- The uniqueness comparison is vertical over the pullback domain.
    simpa [e] using
      (@Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift _ _ _ _ Xₛ.p
        _ _ _ _ _ _ f f (Iso.refl (Yₛ.p.obj y'))
        (show f = (Iso.refl (Yₛ.p.obj y')).hom ≫ f by simp)
        k a hk ha)
  have hinv : Xₛ.p.IsHomLift (𝟙 (Yₛ.p.obj y')) e.inv := by
    -- The inverse comparison is vertical for the same base-isomorphism reason.
    simpa [e] using
      (@Functor.IsStronglyCartesian.domainUniqueUpToIso_hom_isHomLift _ _ _ _ Xₛ.p
        _ _ _ _ _ _ f f (Iso.refl (Yₛ.p.obj y'))
        (show f = (Iso.refl (Yₛ.p.obj y')).hom ≫ f by simp)
        k a hk ha)
  refine ⟨?_⟩
  exact
    { hom := Functor.Fiber.homMk Xₛ.p (Yₛ.p.obj y') e.hom
      inv := Functor.Fiber.homMk Xₛ.p (Yₛ.p.obj y') e.inv
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact e.inv_hom_id }

/-- Helper for Lemma 8.11.3: the source comparison with the canonical pullback also records its
factorization through the canonical source pullback arrow. -/
theorem factorizationTargetPullbackSourceIsoCanonical_hom_fac
    (F : Xₛ ⟶ Yₛ)
    (P : (fibredInGroupoidsFactorization (toBasedFunctor F)).obj)
    {y' : Yₛ.S}
    (b : y' ⟶ (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj P) :
    ∃ e :
      (factorizationTargetPullbackObject F P b).obj.fst ≅
        ((canonicalPullbackChoice Xₛ.p).pullbackFunctor
            (fibredInGroupoidsFactorizationToTarget_pullbackBase (toBasedFunctor F) b)).obj
          P.obj.fst,
      e.hom.1 ≫
          (canonicalPullbackChoice Xₛ.p).map
            (fibredInGroupoidsFactorizationToTarget_pullbackBase (toBasedFunctor F) b)
            P.obj.fst =
        fibredInGroupoidsFactorizationToTarget_left_pullback_map (toBasedFunctor F) P b := by
  let F' := toBasedFunctor F
  let f := fibredInGroupoidsFactorizationToTarget_pullbackBase F' b
  let a := fibredInGroupoidsFactorizationToTarget_left_pullback_map F' P b
  let hcX := canonicalPullbackChoice Xₛ.p
  let k := hcX.map f P.obj.fst
  have ha : Xₛ.p.IsStronglyCartesian f a := by
    -- The explicit source component was built as the source cartesian lift.
    simpa [F', f, a] using
      fibredInGroupoidsFactorizationToTarget_left_pullback_map_isStronglyCartesian F' P b
  have hk : Xₛ.p.IsStronglyCartesian f k := by
    -- The target of the comparison is the canonical cartesian lift over the same base arrow.
    simpa [hcX, k] using hcX.isStronglyCartesian f P.obj.fst
  letI : Xₛ.p.IsStronglyCartesian f k := hk
  letI : Xₛ.p.IsStronglyCartesian f a := ha
  let e :
      (factorizationTargetPullbackObject F P b).obj.fst.1 ≅
        ((hcX.pullbackFunctor f).obj P.obj.fst).1 :=
    @Functor.IsStronglyCartesian.domainIsoOfBaseIso _ _ _ _ Xₛ.p
      _ _ _ _ _ _ f f (Iso.refl (Yₛ.p.obj y'))
      (show f = (Iso.refl (Yₛ.p.obj y')).hom ≫ f by simp)
      k a hk ha
  have hhom : Xₛ.p.IsHomLift (𝟙 (Yₛ.p.obj y')) e.hom := by
    -- The source comparison is vertical over the pullback base.
    simpa [e] using
      (@Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift _ _ _ _ Xₛ.p
        _ _ _ _ _ _ f f (Iso.refl (Yₛ.p.obj y'))
        (show f = (Iso.refl (Yₛ.p.obj y')).hom ≫ f by simp)
        k a hk ha)
  have hinv : Xₛ.p.IsHomLift (𝟙 (Yₛ.p.obj y')) e.inv := by
    -- The inverse comparison is vertical for the same reason.
    simpa [e] using
      (@Functor.IsStronglyCartesian.domainUniqueUpToIso_hom_isHomLift _ _ _ _ Xₛ.p
        _ _ _ _ _ _ f f (Iso.refl (Yₛ.p.obj y'))
        (show f = (Iso.refl (Yₛ.p.obj y')).hom ≫ f by simp)
        k a hk ha)
  let eFiber :
      (factorizationTargetPullbackObject F P b).obj.fst ≅
        ((hcX.pullbackFunctor f).obj P.obj.fst) :=
    { hom := Functor.Fiber.homMk Xₛ.p (Yₛ.p.obj y') e.hom
      inv := Functor.Fiber.homMk Xₛ.p (Yₛ.p.obj y') e.inv
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact e.inv_hom_id }
  refine ⟨eFiber, ?_⟩
  -- Read the comparison factorization from strong-cartesian uniqueness.
  change e.hom ≫ k = a
  rw [Functor.IsStronglyCartesian.domainIsoOfBaseIso_hom]
  exact Functor.IsStronglyCartesian.fac Xₛ.p f k
    (show f = (Iso.refl (Yₛ.p.obj y')).hom ≫ f by simp) a

/-- Helper for Lemma 8.11.3: the source pullback arrow has transported base map equal to the
external target-pullback base arrow. -/
theorem factorizationTargetPullbackSourceBase_fac
    (F : Xₛ ⟶ Yₛ)
    (P : (fibredInGroupoidsFactorization (toBasedFunctor F)).obj)
    {y' : Yₛ.S}
    (b : y' ⟶ (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj P) :
    eqToHom (factorizationTargetPullbackObject F P b).obj.fst.2.symm ≫
        Xₛ.p.map
          (fibredInGroupoidsFactorizationToTarget_left_pullback_map
            (toBasedFunctor F) P b) ≫
        eqToHom P.obj.fst.2 =
      fibredInGroupoidsFactorizationToTarget_pullbackBase (toBasedFunctor F) b := by
  letI :
      Xₛ.p.IsHomLift (fibredInGroupoidsFactorizationToTarget_pullbackBase (toBasedFunctor F) b)
        (fibredInGroupoidsFactorizationToTarget_left_pullback_map (toBasedFunctor F) P b) :=
    factorizationTargetPullback_left_map_isHomLift F P b
  -- Read the external base arrow from the lift property of the chosen source pullback map.
  simpa [factorizationTargetPullbackObject, Category.assoc] using
    (IsHomLift.fac Xₛ.p
      (fibredInGroupoidsFactorizationToTarget_pullbackBase (toBasedFunctor F) b)
      (fibredInGroupoidsFactorizationToTarget_left_pullback_map (toBasedFunctor F) P b)).symm

/-- Helper for Lemma 8.11.3: after casting the explicit source object to an external domain
fiber, it is the canonical source pullback along the external base arrow. -/
theorem sourcePullbackCastIsoOfTargetPullbackBaseEq
    (F : Xₛ ⟶ Yₛ)
    (P : (fibredInGroupoidsFactorization (toBasedFunctor F)).obj)
    {y' : Yₛ.S}
    (i : y' ⟶ (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj P)
    {V : C} (hdom : Yₛ.p.obj y' = V) (f : V ⟶ P.U)
    (hbase :
      fibredInGroupoidsFactorizationToTarget_pullbackBase (toBasedFunctor F) i =
        eqToHom hdom ≫ f) :
    Nonempty
      ((hdom ▸ (factorizationTargetPullbackObject F P i).obj.fst) ≅
        ((canonicalPullbackChoice Xₛ.p).pullbackFunctor f).obj P.obj.fst) := by
  -- Move to the external fiber first; then the remaining comparison is just equality of base
  -- arrows for the canonical source pullback functor.
  cases hdom
  obtain ⟨e⟩ := factorizationTargetPullbackSourceIsoCanonical F P i
  refine ⟨e ≪≫ ?_⟩
  exact
    eqToIso
      (congrArg
        (fun r ↦ ((canonicalPullbackChoice Xₛ.p).pullbackFunctor r).obj P.obj.fst)
        (by simpa using hbase))

/-- Helper for Lemma 8.11.3: after normalizing the target-pullback base arrow, the source
comparison still carries the source pullback factorization equation. -/
theorem sourcePullbackIsoOfTargetPullbackBaseEq_hom_fac
    (F : Xₛ ⟶ Yₛ)
    (P : (fibredInGroupoidsFactorization (toBasedFunctor F)).obj)
    {y' : Yₛ.S}
    (i : y' ⟶ (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj P)
    (f : Yₛ.p.obj y' ⟶ P.U)
    (hbase :
      fibredInGroupoidsFactorizationToTarget_pullbackBase (toBasedFunctor F) i = f) :
    ∃ e :
      (factorizationTargetPullbackObject F P i).obj.fst ≅
        ((canonicalPullbackChoice Xₛ.p).pullbackFunctor f).obj P.obj.fst,
      e.hom.1 ≫ (canonicalPullbackChoice Xₛ.p).map f P.obj.fst =
        fibredInGroupoidsFactorizationToTarget_left_pullback_map (toBasedFunctor F) P i := by
  -- Equality induction reduces this to the canonical comparison with its recorded factorization.
  cases hbase
  simpa using factorizationTargetPullbackSourceIsoCanonical_hom_fac (J := J) F P i

/-- Helper for Lemma 8.11.3: the target component of an explicit target pullback compares with
the canonical target pullback and records the factorization through the original arrow. -/
theorem factorizationTargetPullbackTargetIsoCanonical_hom_fac
    (F : Xₛ ⟶ Yₛ)
    (P : (fibredInGroupoidsFactorization (toBasedFunctor F)).obj)
    {y' : Yₛ.S}
    (i : y' ⟶ (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj P) :
    ∃ e :
      (Functor.Fiber.mk (p := Yₛ.p) (show Yₛ.p.obj y' = Yₛ.p.obj y' from rfl)) ≅
        ((canonicalPullbackChoice Yₛ.p).pullbackFunctor
            (fibredInGroupoidsFactorizationToTarget_pullbackBase (toBasedFunctor F) i)).obj
          P.obj.snd,
      e.hom.1 ≫
          (canonicalPullbackChoice Yₛ.p).map
            (fibredInGroupoidsFactorizationToTarget_pullbackBase (toBasedFunctor F) i)
            P.obj.snd =
        i := by
  let F' := toBasedFunctor F
  let f := fibredInGroupoidsFactorizationToTarget_pullbackBase F' i
  let hcY := canonicalPullbackChoice Yₛ.p
  let k := hcY.map f P.obj.snd
  have hiLift : Yₛ.p.IsHomLift f i :=
    fibredInGroupoidsFactorizationToTarget_pullbackBase_isHomLift F' i
  have hi : Yₛ.p.IsStronglyCartesian f i := by
    -- Any arrow in a fibred groupoid is strongly cartesian over its external lifted base.
    letI : Yₛ.p.IsHomLift f i := hiLift
    exact isStronglyCartesian_of_externalHomLift_forGerbeCriterion (p := Yₛ.p) (f := f) i
  have hk : Yₛ.p.IsStronglyCartesian f k := by
    -- The canonical pullback arrow is strongly cartesian over the same base map.
    simpa [hcY, k] using hcY.isStronglyCartesian f P.obj.snd
  letI : Yₛ.p.IsStronglyCartesian f k := hk
  letI : Yₛ.p.IsStronglyCartesian f i := hi
  let e : y' ≅ ((hcY.pullbackFunctor f).obj P.obj.snd).1 :=
    @Functor.IsStronglyCartesian.domainIsoOfBaseIso _ _ _ _ Yₛ.p
      _ _ _ _ _ _ f f (Iso.refl (Yₛ.p.obj y'))
      (show f = (Iso.refl (Yₛ.p.obj y')).hom ≫ f by simp)
      k i hk hi
  have hhom : Yₛ.p.IsHomLift (𝟙 (Yₛ.p.obj y')) e.hom := by
    -- The target comparison is vertical over the pullback domain.
    simpa [e] using
      (@Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift _ _ _ _ Yₛ.p
        _ _ _ _ _ _ f f (Iso.refl (Yₛ.p.obj y'))
        (show f = (Iso.refl (Yₛ.p.obj y')).hom ≫ f by simp)
        k i hk hi)
  have hinv : Yₛ.p.IsHomLift (𝟙 (Yₛ.p.obj y')) e.inv := by
    -- The inverse comparison is vertical for the same base-isomorphism reason.
    simpa [e] using
      (@Functor.IsStronglyCartesian.domainUniqueUpToIso_hom_isHomLift _ _ _ _ Yₛ.p
        _ _ _ _ _ _ f f (Iso.refl (Yₛ.p.obj y'))
        (show f = (Iso.refl (Yₛ.p.obj y')).hom ≫ f by simp)
        k i hk hi)
  let eFiber :
      (Functor.Fiber.mk (p := Yₛ.p) (show Yₛ.p.obj y' = Yₛ.p.obj y' from rfl)) ≅
        ((hcY.pullbackFunctor f).obj P.obj.snd) :=
    { hom := Functor.Fiber.homMk Yₛ.p (Yₛ.p.obj y') e.hom
      inv := Functor.Fiber.homMk Yₛ.p (Yₛ.p.obj y') e.inv
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact e.inv_hom_id }
  refine ⟨eFiber, ?_⟩
  -- Read the target factorization from the same strong-cartesian uniqueness comparison.
  change e.hom ≫ k = i
  rw [Functor.IsStronglyCartesian.domainIsoOfBaseIso_hom]
  exact Functor.IsStronglyCartesian.fac Yₛ.p f k
    (show f = (Iso.refl (Yₛ.p.obj y')).hom ≫ f by simp) i

/-- Helper for Lemma 8.11.3: after normalizing the target-pullback base arrow, the target
comparison still records its factorization through the original target arrow. -/
theorem targetPullbackIsoOfTargetPullbackBaseEq_hom_fac
    (F : Xₛ ⟶ Yₛ)
    (P : (fibredInGroupoidsFactorization (toBasedFunctor F)).obj)
    {y' : Yₛ.S}
    (i : y' ⟶ (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj P)
    (f : Yₛ.p.obj y' ⟶ P.U)
    (hbase :
      fibredInGroupoidsFactorizationToTarget_pullbackBase (toBasedFunctor F) i = f) :
    ∃ e :
      (Functor.Fiber.mk (p := Yₛ.p) (show Yₛ.p.obj y' = Yₛ.p.obj y' from rfl)) ≅
        ((canonicalPullbackChoice Yₛ.p).pullbackFunctor f).obj P.obj.snd,
      e.hom.1 ≫ (canonicalPullbackChoice Yₛ.p).map f P.obj.snd = i := by
  -- Equality induction reduces the normalized statement to the canonical target comparison.
  cases hbase
  simpa using factorizationTargetPullbackTargetIsoCanonical_hom_fac (J := J) F P i

/-- Helper for Lemma 8.11.3: a morphism in the strict target-factorization fiber has identity
target component on the pulled target object. -/
theorem targetPullbackFiberHom_targetComponent_eq_id
    (F : Xₛ ⟶ Yₛ)
    (P Q : (fibredInGroupoidsFactorization (toBasedFunctor F)).obj)
    {y' : Yₛ.S}
    (iP : y' ⟶ (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj P)
    (iQ : y' ⟶ (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj Q)
    (φ :
      Functor.Fiber.mk
          (p := (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor)
          (show (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj
              (factorizationTargetPullbackObject F P iP) = y' from rfl) ⟶
        Functor.Fiber.mk
          (p := (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor)
          (show (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj
              (factorizationTargetPullbackObject F Q iQ) = y' from rfl)) :
    φ.1.b = 𝟙 y' := by
  let Ftarget := fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)
  have hφ : Ftarget.toFunctor.IsHomLift (𝟙 y') φ.1 := φ.2
  -- The fiber condition says the underlying target projection of `φ` is the identity.
  have hbase : 𝟙 y' = Ftarget.toFunctor.map φ.1 :=
    @IsHomLift.eq_of_isHomLift _ _ _ _ Ftarget.toFunctor _ _ (𝟙 y') φ.1 hφ
  change 𝟙 y' = φ.1.b at hbase
  exact hbase.symm

/-- Helper for Lemma 8.11.3: if an explicit target-pullback morphism is vertical on the target
component, then its source component is vertical over the pulled target base. -/
theorem targetPullbackHom_sourceComponent_isHomLift_id
    (F : Xₛ ⟶ Yₛ)
    (P Q : (fibredInGroupoidsFactorization (toBasedFunctor F)).obj)
    {y' : Yₛ.S}
    (iP : y' ⟶ (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj P)
    (iQ : y' ⟶ (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj Q)
    (φ : factorizationTargetPullbackObject F P iP ⟶ factorizationTargetPullbackObject F Q iQ)
    (hb : φ.b = 𝟙 y') :
    Xₛ.p.IsHomLift (𝟙 (Yₛ.p.obj y')) φ.a := by
  have hbOver : Yₛ.p.IsHomLift φ.base φ.b := φ.b_over
  have hbase : φ.base = 𝟙 (Yₛ.p.obj y') := by
    have hbase' : φ.base = Yₛ.p.map φ.b :=
      @IsHomLift.eq_of_isHomLift _ _ _ _ Yₛ.p _ _ φ.base φ.b hbOver
    rw [hb] at hbase'
    exact hbase'.trans (Yₛ.p.map_id y')
  have haOver : Xₛ.p.IsHomLift φ.base φ.a := φ.a_over
  -- Rewrite the common base of the explicit hom to the identity and reuse its source lift field.
  simpa [hbase] using haOver

/- Helper for Lemma 8.11.3: a vertical explicit target-pullback morphism gives a source
component after transporting both explicit source objects to an external fiber.
theorem targetPullbackHom_sourceComponent_cast
    (F : Xₛ ⟶ Yₛ)
    (P Q : (fibredInGroupoidsFactorization (toBasedFunctor F)).obj)
    {y' : Yₛ.S}
    (iP : y' ⟶ (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj P)
    (iQ : y' ⟶ (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj Q)
    {V : C} (hdom : Yₛ.p.obj y' = V)
    (φ : factorizationTargetPullbackObject F P iP ⟶ factorizationTargetPullbackObject F Q iQ)
    (hb : φ.b = 𝟙 y') :
    Nonempty
      ((hdom ▸ (factorizationTargetPullbackObject F P iP).obj.fst) ⟶
        (hdom ▸ (factorizationTargetPullbackObject F Q iQ).obj.fst)) := by
  -- Equality induction exposes the fiber base, and the verticality helper supplies the lift proof.
  cases hdom
  exact
    ⟨⟨φ.a, by
      simpa using targetPullbackHom_sourceComponent_isHomLift_id F P Q iP iQ φ hb⟩⟩
-/

/-- Helper for Lemma 8.11.3: the hom side of the chosen pullback-composition isomorphism is
natural in the object of the source fiber. -/
theorem pullbackCompComponentIso_hom_naturality_forGerbeCriterion
    {S : Type u₂} [Category.{v₂} S] {p : S ⥤ C} (hc : PullbackChoice p)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    {X Y : p.Fiber U} (θ : X ⟶ Y) :
    (hc.pullbackFunctor (g ≫ f)).map θ ≫
        (hc.pullbackCompComponentIso f g Y).hom =
      (hc.pullbackCompComponentIso f g X).hom ≫
        (hc.pullbackFunctor g).map ((hc.pullbackFunctor f).map θ) := by
  -- Repackage naturality of the composite-pullback comparison in the orientation needed by the
  -- remaining source-lift bridge.
  simpa [PullbackChoice.pullbackCompIso] using (hc.pullbackCompIso f g).hom.naturality θ

/-- Helper for Lemma 8.11.3: pulling back along `eqToHom h ≫ f` is, after transporting the
base fiber along `h`, the same as pulling back along `f`. -/
theorem pullback_eqToHom_comp_baseCast_iso
    {S : Type u₂} [Category.{v₂} S] {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    {U V V' : C} (h : V' = V) (f : V ⟶ U) (x : p.Fiber U) :
    Nonempty
      ((h ▸ ((hc.pullbackFunctor (eqToHom h ≫ f)).obj x)) ≅
        (hc.pullbackFunctor f).obj x) := by
  -- Equality induction reduces the base transport to the identity pullback of the same arrow.
  cases h
  refine ⟨?_⟩
  simpa using (show ((hc.pullbackFunctor f).obj x) ≅ (hc.pullbackFunctor f).obj x from Iso.refl _)

/-- Helper for Lemma 8.11.3: changing a pullback base arrow by equality is natural in the
pulled-back fiber morphism. -/
theorem pullbackFunctor_eqToIso_naturality_forGerbeCriterion
    {S : Type u₂} [Category.{v₂} S] {p : S ⥤ C} (hc : PullbackChoice p)
    {U V : C} {f g : V ⟶ U} (h : f = g)
    {X Y : p.Fiber U} (η : X ⟶ Y) :
    (hc.pullbackFunctor f).map η ≫
        (eqToIso (congrArg (fun r ↦ (hc.pullbackFunctor r).obj Y) h)).hom =
      (eqToIso (congrArg (fun r ↦ (hc.pullbackFunctor r).obj X) h)).hom ≫
        (hc.pullbackFunctor g).map η := by
  -- Equality induction turns both comparison isomorphisms into identities.
  cases h
  have hY :
      congrArg (fun r ↦ (hc.pullbackFunctor r).obj Y) (rfl : f = f) = rfl :=
    Subsingleton.elim _ _
  have hX :
      congrArg (fun r ↦ (hc.pullbackFunctor r).obj X) (rfl : f = f) = rfl :=
    Subsingleton.elim _ _
  rw [hY, hX]
  simp

/-- Helper for Lemma 8.11.3: the factorization object attached to a fiber morphism
`F x ⟶ F x'`. -/
noncomputable def factorizationObjectOfFiberHom
    (F : Xₛ ⟶ Yₛ) {U : C} (x x' : Xₛ.p.Fiber U)
    (b : (F.fiberFunctor U).obj x ⟶ (F.fiberFunctor U).obj x') [IsIso b] :
    (fibredInGroupoidsFactorization (toBasedFunctor F)).obj :=
  { U := U
    obj := { fst := x, snd := (F.fiberFunctor U).obj x', iso := asIso b } }

/-- Helper for Lemma 8.11.3: the factorization object attached to the identity on `F x`. -/
noncomputable def factorizationObjectOfFiberIdentity
    (F : Xₛ ⟶ Yₛ) {U : C} (x : Xₛ.p.Fiber U) :
    (fibredInGroupoidsFactorization (toBasedFunctor F)).obj :=
  { U := U
    obj := { fst := x, snd := (F.fiberFunctor U).obj x, iso := Iso.refl _ } }

end

end StackInGroupoidsOver.Hom

end CategoryTheory
