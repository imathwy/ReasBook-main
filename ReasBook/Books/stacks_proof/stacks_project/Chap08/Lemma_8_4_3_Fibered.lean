import StacksProject_2024.Chap08.Lemma_8_4_3_FiberedBase

open CategoryTheory
open CategoryTheory Functor
open Functor.IsPreFibered
open Functor.Fiber

universe u₁ u₂ v₁ v₂

section

variable {C : Type u₁} {X : Type u₂} [Category.{v₁} C] [Category.{v₂} X]
variable (p : X ⥤ C)
variable (P : ObjectProperty X)
variable [p.IsFibered]

section RestrictedFibered

variable [(P.ι ⋙ p).IsFibered]

/-- Helper for Lemma 8.4.3: once the pullback-closure hypothesis provides an ambient strongly
cartesian model over the same base arrow, a strongly cartesian morphism in the restricted
projection is already strongly cartesian in the ambient category. -/
lemma fullSubcategory_hom_isStronglyCartesian_to_ambient
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {R S : C} {a b : P.FullSubcategory} (f : R ⟶ S) (φ : a ⟶ b)
    [hφ : (P.ι ⋙ p).IsStronglyCartesian f φ] :
    p.IsStronglyCartesian f φ.hom := by
  have hφLiftRestricted : (P.ι ⋙ p).IsHomLift f φ := hφ.toIsHomLift
  have hφOwnerRestricted : (P.ι ⋙ p).IsStronglyCartesian ((P.ι ⋙ p).map φ) φ := by
    -- Normalize the restricted base arrow to the owner map of `φ` before comparing lifts.
    letI : (P.ι ⋙ p).IsStronglyCartesian f φ := hφ
    letI : (P.ι ⋙ p).IsHomLift f φ := hφLiftRestricted
    have hφDom : (P.ι ⋙ p).obj a = R := IsHomLift.domain_eq (P.ι ⋙ p) f φ
    have hφCod : (P.ι ⋙ p).obj b = S := IsHomLift.codomain_eq (P.ι ⋙ p) f φ
    subst hφDom
    subst hφCod
    have hbase : f = (P.ι ⋙ p).map φ := IsHomLift.eq_of_isHomLift (P.ι ⋙ p) f φ
    subst hbase
    infer_instance
  obtain ⟨y, ψ, hψAmbient⟩ :=
    fullSubcategory_exists_ambient_stronglyCartesian_lift
      (p := p) (P := P) (hpullback := hpullback)
      (x := b) ((P.ι ⋙ p).map φ)
  have hψRestricted : (P.ι ⋙ p).IsStronglyCartesian ((P.ι ⋙ p).map φ) ψ :=
    fullSubcategory_hom_isStronglyCartesian_of_ambient
      (p := p) (P := P) (f := (P.ι ⋙ p).map φ) (φ := ψ) (hpφ := hψAmbient)
  let e : y ≅ a :=
    Functor.IsCartesian.domainUniqueUpToIso (P.ι ⋙ p) ((P.ι ⋙ p).map φ) φ ψ
  have hcomp : e.hom ≫ φ = ψ := by
    -- The domain-uniqueness comparison isomorphism is characterized by the Cartesian
    -- factorization through `φ`.
    exact Functor.IsCartesian.fac (P.ι ⋙ p) ((P.ι ⋙ p).map φ) φ ψ
  have hφ_eq : φ = e.inv ≫ ψ := by
    -- Rewrite `φ` as the ambient pullback lift preceded by the vertical comparison isomorphism.
    calc
      φ = (𝟙 a) ≫ φ := by simp
      _ = (e.inv ≫ e.hom) ≫ φ := by rw [e.inv_hom_id]
      _ = e.inv ≫ (e.hom ≫ φ) := by simp
      _ = e.inv ≫ ψ := by rw [hcomp]
  have hφ_eq_hom : φ.hom = e.inv.hom ≫ ψ.hom := by
    exact congrArg (fun k ↦ k.hom) hφ_eq
  have heInvLiftRestricted :
      (P.ι ⋙ p).IsHomLift (𝟙 ((P.ι ⋙ p).obj a)) e.inv := by
    exact Functor.IsCartesian.domainUniqueUpToIso_hom_isHomLift
      (P.ι ⋙ p) ((P.ι ⋙ p).map φ) φ ψ
  have heInvLiftAmbient :
      p.IsHomLift (𝟙 ((P.ι ⋙ p).obj a)) e.inv.hom :=
    (fullSubcategory_homLift_iff_ambient (p := p) (P := P)
      (f := 𝟙 ((P.ι ⋙ p).obj a)) (φ := e.inv)).1 heInvLiftRestricted
  have hφOwnerAmbient : p.IsStronglyCartesian ((P.ι ⋙ p).map φ) φ.hom := by
    -- Compose the vertical ambient isomorphism with the chosen ambient strongly cartesian lift.
    letI : p.IsHomLift (𝟙 ((P.ι ⋙ p).obj a)) e.inv.hom := heInvLiftAmbient
    let eAmbient : a.obj ≅ y.obj := P.ι.mapIso e.symm
    letI : p.IsHomLift (𝟙 ((P.ι ⋙ p).obj a)) eAmbient.hom := by
      simpa [eAmbient] using heInvLiftAmbient
    letI : p.IsStronglyCartesian (𝟙 ((P.ι ⋙ p).obj a)) e.inv.hom :=
      IsStronglyCartesian.of_iso (p := p) (f := 𝟙 ((P.ι ⋙ p).obj a)) eAmbient
    have hcompAmbient :
        p.IsStronglyCartesian
          ((𝟙 ((P.ι ⋙ p).obj a)) ≫ ((P.ι ⋙ p).map φ))
          (e.inv.hom ≫ ψ.hom) := by
      infer_instance
    simpa [Functor.comp_map, hφ_eq_hom] using hcompAmbient
  have hφLiftAmbient : p.IsHomLift f φ.hom :=
    (fullSubcategory_homLift_iff_ambient (p := p) (P := P) (f := f) (φ := φ)).1
      hφLiftRestricted
  -- Rebase the owner-level ambient result back to the original external arrow `f`.
  letI : p.IsStronglyCartesian ((P.ι ⋙ p).map φ) φ.hom := hφOwnerAmbient
  letI : p.IsHomLift f φ.hom := hφLiftAmbient
  have ha : p.obj a.obj = R := IsHomLift.domain_eq p f φ.hom
  have hb : p.obj b.obj = S := IsHomLift.codomain_eq p f φ.hom
  subst ha
  subst hb
  have hbase : f = p.map φ.hom := IsHomLift.eq_of_isHomLift p f φ.hom
  subst hbase
  exact hφOwnerAmbient

/-- Helper for Lemma 8.4.3: forgetting the property inside the restricted fiber lands in the
ambient fiber over the same base object. -/
theorem fullSubcategory_restrictedFiber_forget_comp_eq_const (U : C) :
    ((((fiberInclusion : (P.ι ⋙ p).Fiber U ⥤ P.FullSubcategory) ⋙ P.ι) ⋙ p)) =
      (const ((P.ι ⋙ p).Fiber U)).obj U := by
  -- Reassociate the fiber-inclusion identity for `P.ι ⋙ p` to the ambient projection `p`.
  simpa [Functor.assoc] using
    (fiberInclusion_comp_eq_const (p := P.ι ⋙ p) (S := U))

/-- Helper for Lemma 8.4.3: the forgetful functor from the restricted fiber to the ambient fiber
remembers the same underlying ambient object. -/
noncomputable def fullSubcategory_fiber_forget (U : C) :
    (P.ι ⋙ p).Fiber U ⥤ p.Fiber U :=
  inducedFunctor
    (p := p) (S := U)
    (F := ((fiberInclusion : (P.ι ⋙ p).Fiber U ⥤ P.FullSubcategory) ⋙ P.ι))
    (fullSubcategory_restrictedFiber_forget_comp_eq_const (p := p) (P := P) U)

/-- Helper for Lemma 8.4.3: every object of the restricted fiber still satisfies `P` after
forgetting to the ambient fiber. -/
theorem fullSubcategory_fiber_forget_property (U : C) (x : (P.ι ⋙ p).Fiber U) :
    (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X))
      ((fullSubcategory_fiber_forget (p := p) (P := P) U).obj x) := by
  -- The induced ambient-fiber object is definitionally the same underlying object.
  simpa [fullSubcategory_fiber_forget, ObjectProperty.inverseImage] using x.1.2

/-- Helper for Lemma 8.4.3: an object of the inverse-image full subcategory of the ambient fiber
determines an object of `P.FullSubcategory` over the same base. -/
noncomputable def inverseImage_fiber_to_fullSubcategory (U : C) :
    (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory ⥤ P.FullSubcategory :=
  P.lift
    (((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).ι) ⋙
      (fiberInclusion : p.Fiber U ⥤ X))
    (fun x ↦ x.2)

/-- Helper for Lemma 8.4.3: the inverse-image full subcategory over the ambient fiber projects to
the constant functor at `U` through `P.ι ⋙ p`. -/
theorem inverseImage_fiber_to_fullSubcategory_comp_eq_const (U : C) :
    ((inverseImage_fiber_to_fullSubcategory (p := p) (P := P) U) ⋙ (P.ι ⋙ p)) =
      (const ((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory)).obj U := by
  -- After forgetting the `P`-proof, this is the standard fiber-inclusion identity for `p.Fiber U`.
  simpa [inverseImage_fiber_to_fullSubcategory, Functor.assoc] using
    congrArg
      (fun F ↦ ((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).ι) ⋙ F)
      (fiberInclusion_comp_eq_const (p := p) (S := U))

/-- Helper for Lemma 8.4.3: the inverse-image full subcategory of the ambient fiber maps back to
the restricted fiber over `U`. -/
noncomputable def inverseImage_fiber_to_restrictedFiber (U : C) :
    (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory ⥤ (P.ι ⋙ p).Fiber U :=
  inducedFunctor
    (p := P.ι ⋙ p) (S := U)
    (F := inverseImage_fiber_to_fullSubcategory (p := p) (P := P) U)
    (inverseImage_fiber_to_fullSubcategory_comp_eq_const (p := p) (P := P) U)

/-- Helper for Lemma 8.4.3: the restricted fiber maps to the full subcategory of the ambient
fiber cut out by `P`. -/
noncomputable def restrictedFiber_to_inverseImage_fiber (U : C) :
    (P.ι ⋙ p).Fiber U ⥤
      (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory :=
  (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).lift
    (fullSubcategory_fiber_forget (p := p) (P := P) U)
    (fullSubcategory_fiber_forget_property (p := p) (P := P) U)

/-- Helper for Lemma 8.4.3: after forgetting a transport morphism in the restricted fiber all the
way to `X`, only the ambient `eqToHom` remains. -/
lemma restricted_fiber_eqToHom_hom_eq_id (U : C)
    {x y : (P.ι ⋙ p).Fiber U} (h : x = y) :
    (((fiberInclusion : (P.ι ⋙ p).Fiber U ⥤ P.FullSubcategory) ⋙ P.ι).map (eqToHom h)) =
      eqToHom (by subst h; rfl) := by
  -- Substituting the equality removes the nested fiber and full-subcategory transport data.
  subst h
  rfl

/-- Helper for Lemma 8.4.3: after forgetting a transport morphism in the inverse-image full
subcategory all the way to `X`, only the ambient `eqToHom` remains. -/
lemma inverse_image_fullSubcategory_eqToHom_hom_eq_id (U : C)
    {x y : (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory} (h : x = y) :
    ((((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).ι) ⋙
        (fiberInclusion : p.Fiber U ⥤ X)).map (eqToHom h)) =
      eqToHom (by subst h; rfl) := by
  -- The dual nested transport again contracts after substituting the object equality.
  subst h
  rfl

/-- Helper for Lemma 8.4.3: the forward bridge from the restricted fiber to the ambient inverse-
image full subcategory is strictly inverse to the ambient-to-restricted bridge on the restricted
fiber side. -/
theorem restrictedFiber_to_inverseImage_fiber_comp_eq_id (U : C) :
    restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U ⋙
        inverseImage_fiber_to_restrictedFiber (p := p) (P := P) U =
      𝟭 ((P.ι ⋙ p).Fiber U) := by
  -- Route correction: package the roundtrip as a strict functor equality, so the later
  -- equivalence uses `eqToIso` instead of dependent `NatIso.ofComponents`.
  refine CategoryTheory.Functor.hext (h_obj := ?_) (h_map := ?_)
  · intro x
    -- On objects, both bridges return the same nested record once the fiber witness is unfolded.
    cases x
    rfl
  · intro x y φ
    -- Once the object equalities are treated heterogeneously, the map equality is definitional.
    cases x
    cases y
    rfl

/-- Helper for Lemma 8.4.3: the ambient-to-restricted bridge is strictly inverse to the forward
bridge on the inverse-image full-subcategory side. -/
theorem inverseImage_fiber_to_restrictedFiber_comp_eq_id (U : C) :
    inverseImage_fiber_to_restrictedFiber (p := p) (P := P) U ⋙
        restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U =
      𝟭 ((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory) := by
  -- The dual roundtrip again becomes a strict functor equality once both bridges are explicit.
  refine CategoryTheory.Functor.hext (h_obj := ?_) (h_map := ?_)
  · intro x
    -- The object-level dual roundtrip also unfolds to the original full-subcategory record.
    cases x
    rfl
  · intro x y φ
    -- The dual heterogeneous map equality again collapses after unfolding the nested records.
    cases x
    cases y
    rfl

/-- Helper for Lemma 8.4.3: the restricted fiber is equivalent to the full subcategory of the
ambient fiber cut out by `P`. -/
noncomputable def fullSubcategory_fiber_equiv_inverseImage (U : C) :
    (P.ι ⋙ p).Fiber U ≌
      (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory :=
  CategoryTheory.Equivalence.mk
    (restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U)
    (inverseImage_fiber_to_restrictedFiber (p := p) (P := P) U)
    (eqToIso (restrictedFiber_to_inverseImage_fiber_comp_eq_id (p := p) (P := P) U).symm)
    (eqToIso (inverseImage_fiber_to_restrictedFiber_comp_eq_id (p := p) (P := P) U))

/-- Helper for Lemma 8.4.3: applying the fiber equivalence and then its inverse returns the
original restricted-fiber object. -/
@[simp] theorem fullSubcategory_fiber_equiv_inverseImage_inverse_functor_obj
    (U : C) (x : (P.ι ⋙ p).Fiber U) :
    (inverseImage_fiber_to_restrictedFiber (p := p) (P := P) U).obj
      ((fullSubcategory_fiber_equiv_inverseImage (p := p) (P := P) U).functor.obj x) = x := by
  -- The object-level roundtrip is exactly the component of the strict composite equality.
  simpa [fullSubcategory_fiber_equiv_inverseImage] using
    Functor.congr_obj
      (restrictedFiber_to_inverseImage_fiber_comp_eq_id (p := p) (P := P) U) x

/-- Helper for Lemma 8.4.3: applying the inverse of the fiber equivalence and then the forward
functor returns the original inverse-image fiber object. -/
@[simp] theorem fullSubcategory_fiber_equiv_inverseImage_functor_inverse_obj
    (U : C)
    (x : (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory) :
    (fullSubcategory_fiber_equiv_inverseImage (p := p) (P := P) U).functor.obj
      ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) U).obj x) = x := by
  -- The dual object-level roundtrip is the component of the other strict composite equality.
  simpa [fullSubcategory_fiber_equiv_inverseImage] using
    Functor.congr_obj
      (inverseImage_fiber_to_restrictedFiber_comp_eq_id (p := p) (P := P) U) x

/-- Helper for Lemma 8.4.3: the restricted-to-inverse-image bridge cancels the inverse bridge on
morphisms exactly, not only on objects. -/
@[simp] theorem fullSubcategory_fiber_equiv_inverseImage_inverse_functor_map
    (U : C)
    {x y : (P.ι ⋙ p).Fiber U} (φ : x ⟶ y) :
    (inverseImage_fiber_to_restrictedFiber (p := p) (P := P) U).map
        ((fullSubcategory_fiber_equiv_inverseImage (p := p) (P := P) U).functor.map φ) =
      φ := by
  -- Forget to `X`, where the roundtrip functor equality produces only `eqToHom` transports, and
  -- the dedicated transport lemma collapses them to identities.
  change (inverseImage_fiber_to_restrictedFiber (p := p) (P := P) U).map
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).map φ) = φ
  apply Functor.Fiber.hom_ext
  apply ObjectProperty.hom_ext
  cases x
  cases y
  rfl

/-- Helper for Lemma 8.4.3: the inverse-image-to-restricted bridge cancels the forward bridge on
morphisms exactly, mirroring the object-level roundtrip lemma above. -/
@[simp] theorem fullSubcategory_fiber_equiv_inverseImage_functor_inverse_map
    (U : C)
    {x y : (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory} (φ : x ⟶ y) :
    (fullSubcategory_fiber_equiv_inverseImage (p := p) (P := P) U).functor.map
        ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) U).map φ) =
      φ := by
  -- Forget to the ambient fiber and then to `X`, so the strict composite equality reduces to the
  -- corresponding ambient `eqToHom` transports.
  change (restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).map
      ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) U).map φ) = φ
  apply ObjectProperty.hom_ext
  apply Functor.Fiber.hom_ext
  cases x
  cases y
  rfl

end RestrictedFibered


end
