import Mathlib
import stacks_proof.stacks_project.Chap04.Lemma_4_34_1
import stacks_proof.stacks_project.Chap04.«4_34_2_3»
import stacks_proof.stacks_project.Chap08.Lemma_8_8_1
import stacks_proof.stacks_project.Chap08.Lemma_8_8_4

universe u v

namespace CategoryTheory

open CategoryOver FibredCategoryMor

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] uliftCategory

namespace FibredCategoryOver

/-- Helper for Chap08 Lemma 8 8 5: the raw absolute-inertia projection is fibred, so it can be
repackaged as a fibred category over the base. -/
private instance relativeInertiaProjectionSelf_isFibered (X : FibredCategoryOver C) :
    (relativeInertiaProjection X.p X.p).IsFibered :=
  CategoryOver.relativeInertiaProjection_self_isFibered (p := X.p)

/-- Helper for Chap08 Lemma 8 8 5: absolute inertia is the fibred category associated to raw
self-inertia. -/
abbrev absoluteInertiaOver (X : FibredCategoryOver.{u, v, max u v, v} C) :
    FibredCategoryOver C :=
  FibredCategoryOver.ofFunctor (relativeInertiaProjection X.p X.p)

end FibredCategoryOver

/- Domain-style sampling for Lemma 8.8.5:
- primary domain: absolute inertia of fibred categories over a site and stackification morphisms.
- inspected owner-level declarations:
  `FibredCategoryOver.absoluteInertiaOver`,
  `CategoryOver.absoluteInertiaOverMap`,
  `absoluteInertiaStack`,
  `FibredCategoryMor.IsStackification`.
- best owner abstraction: the Chapter 4 fibred-category owner
  `FibredCategoryOver.absoluteInertiaOver`; the Chapter 4 based-category map
  `CategoryOver.absoluteInertiaOverMap` is only bridge/view data, and the Chapter 8 bundled stack
  target is `absoluteInertiaStack X'`.
- primitive data: a morphism `F : X ⟶ Y` of fibred categories and the canonical absolute inertia
  owner map induced by its underlying based functor over `C`.
- derived API: the strongly-cartesian preservation theorem below, the rebundled owner morphism
  `absoluteInertiaMap`, and the source-facing stackification theorem.

Source/core/bridge triage:
- `source-facing`: `absoluteInertia_of_stackification_isStackification`.
- `core/canonical`: `FibredCategoryOver.absoluteInertiaOver`, `absoluteInertiaStack`, and
  `FibredCategoryMor.IsStackification`.
- `bridge/view`: the Chapter 4 based-category map `CategoryOver.absoluteInertiaOverMap`, the
  preservation theorem below, and the rebundled induced morphism `absoluteInertiaMap`. -/

-- Proof sketch: view the absolute inertia as the relative inertia of the structure functor and
-- transport the preservation of strongly cartesian arrows along the explicit iterated `2`-fibre
-- product model of Lemma `4.34.1`.
/-- Helper for Lemma 8.8.5: a lift condition in the absolute inertia is equivalent to the same
lift condition on the underlying arrow in the ambient fibred category. -/
private theorem absolute_inertia_is_hom_lift_iff_underlying
    {Z : FibredCategoryOver C}
    {A B : (CategoryOver.absoluteInertiaOver Z.toBasedCategory).obj}
    {R S : C}
    {f : R ⟶ S}
    {φ : A ⟶ B} :
    (CategoryOver.absoluteInertiaOver Z.toBasedCategory).p.IsHomLift f φ ↔
      Z.p.IsHomLift f φ.φ := by
  -- Unfolding the packaged absolute inertia exposes the same base projection on the underlying
  -- arrow in `Z`.
  constructor
  · intro h
    let _ : (CategoryOver.absoluteInertiaOver Z.toBasedCategory).p.IsHomLift f φ := h
    refine IsHomLift.of_fac' Z.p f φ.φ
      (IsHomLift.domain_eq (CategoryOver.absoluteInertiaOver Z.toBasedCategory).p f φ)
      (IsHomLift.codomain_eq (CategoryOver.absoluteInertiaOver Z.toBasedCategory).p f φ) ?_
    simpa [CategoryOver.absoluteInertiaOver, CategoryOver.relativeInertiaOver,
      FibredCategoryOver.absoluteInertiaOver, FibredCategoryOver.relativeInertiaOver,
      relativeInertiaProjection] using
      (IsHomLift.fac' (CategoryOver.absoluteInertiaOver Z.toBasedCategory).p f φ)
  · intro h
    let _ : Z.p.IsHomLift f φ.φ := h
    refine IsHomLift.of_fac' (CategoryOver.absoluteInertiaOver Z.toBasedCategory).p f φ
      (IsHomLift.domain_eq Z.p f φ.φ)
      (IsHomLift.codomain_eq Z.p f φ.φ) ?_
    simpa [CategoryOver.absoluteInertiaOver, CategoryOver.relativeInertiaOver,
      FibredCategoryOver.absoluteInertiaOver, FibredCategoryOver.relativeInertiaOver,
      relativeInertiaProjection] using
      (IsHomLift.fac' Z.p f φ.φ)

/-- Helper for Chap08 Lemma 8 8 5: the automorphism stored in an absolute-inertia object is
vertical for the ambient fibred-category projection. -/
private theorem absoluteInertiaObject_map_hom_eq_id
    {Z : FibredCategoryOver C}
    (A : (CategoryOver.absoluteInertiaOver Z.toBasedCategory).obj) :
    Z.p.map A.α.hom = 𝟙 (Z.p.obj A.x) := by
  -- The object field is stated using the `Cat/C` base functor; unfold that functor once to
  -- reuse it as a statement about `Z.p`.
  simpa [CategoryOver.absoluteInertiaOver, CategoryOver.relativeInertiaOver,
    BasedCategory.toBase] using A.map_hom_eq_id

/-- Helper for Chap08 Lemma 8 8 5: the inverse of the stored absolute-inertia automorphism is
also vertical for the ambient fibred-category projection. -/
private theorem absoluteInertiaObject_map_inv_eq_id
    {Z : FibredCategoryOver C}
    (A : (CategoryOver.absoluteInertiaOver Z.toBasedCategory).obj) :
    Z.p.map A.α.inv = 𝟙 (Z.p.obj A.x) := by
  -- Use functoriality of the inverse and the already-normalized verticality of the hom part.
  calc
    Z.p.map A.α.inv = 𝟙 (Z.p.obj A.x) ≫ Z.p.map A.α.inv := by simp
    _ = Z.p.map A.α.hom ≫ Z.p.map A.α.inv := by
      rw [absoluteInertiaObject_map_hom_eq_id A]
    _ = Z.p.map (A.α.hom ≫ A.α.inv) := by simp
    _ = 𝟙 (Z.p.obj A.x) := by simp

/-- Helper for Chap08 Lemma 8 8 5: an underlying strongly cartesian morphism is strongly
cartesian in the absolute-inertia projection. -/
private theorem absolute_inertia_isStronglyCartesian_of_underlying
    {Z : FibredCategoryOver C}
    {A B : (CategoryOver.absoluteInertiaOver Z.toBasedCategory).obj}
    {φ : A ⟶ B}
    (hφ : Z.p.IsStronglyCartesian (Z.p.map φ.φ) φ.φ) :
    (CategoryOver.absoluteInertiaOver Z.toBasedCategory).p.IsStronglyCartesian
      ((CategoryOver.absoluteInertiaOver Z.toBasedCategory).p.map φ) φ := by
  -- The lift condition is the same after forgetting the inertia automorphism data.
  letI : Z.p.IsStronglyCartesian (Z.p.map φ.φ) φ.φ := hφ
  refine { toIsHomLift := ?_, universal_property' := ?_ }
  · apply absolute_inertia_is_hom_lift_iff_underlying.mpr
    exact hφ.toIsHomLift
  · intro A' g ψ hψ
    -- Project the competing inertia lift to the underlying fibred category.
    have hψUnderlying : Z.p.IsHomLift (g ≫ Z.p.map φ.φ) ψ.φ := by
      have hψ' : (CategoryOver.absoluteInertiaOver Z.toBasedCategory).p.IsHomLift
          (g ≫ (CategoryOver.absoluteInertiaOver Z.toBasedCategory).p.map φ) ψ := hψ
      have hψu := absolute_inertia_is_hom_lift_iff_underlying.mp hψ'
      simpa [CategoryOver.absoluteInertiaOver, CategoryOver.relativeInertiaOver,
        FibredCategoryOver.absoluteInertiaOver, FibredCategoryOver.relativeInertiaOver,
        relativeInertiaProjection] using hψu
    letI : Z.p.IsHomLift (g ≫ Z.p.map φ.φ) ψ.φ := hψUnderlying
    obtain ⟨χ0, hχ0, hχ0uniq⟩ :=
      Functor.IsStronglyCartesian.universal_property Z.p (Z.p.map φ.φ) φ.φ
        g (g ≫ Z.p.map φ.φ) rfl ψ.φ
    have hχ0fac : χ0 ≫ φ.φ = ψ.φ := hχ0.2
    letI : Z.p.IsHomLift g χ0 := hχ0.1
    have hχ0comm : A'.α.hom ≫ χ0 = χ0 ≫ A.α.hom := by
      -- Both candidates are lifts over `g`; after postcomposition with `φ.φ`, the inertia
      -- commutation relations identify them, so strong-cartesian uniqueness applies.
      have hA'Lift : Z.p.IsHomLift (𝟙 (Z.p.obj A'.x)) A'.α.hom := by
        simpa [absoluteInertiaObject_map_hom_eq_id A'] using
          (inferInstance : Z.p.IsHomLift (Z.p.map A'.α.hom) A'.α.hom)
      have hALift : Z.p.IsHomLift (𝟙 (Z.p.obj A.x)) A.α.hom := by
        simpa [absoluteInertiaObject_map_hom_eq_id A] using
          (inferInstance : Z.p.IsHomLift (Z.p.map A.α.hom) A.α.hom)
      letI : Z.p.IsHomLift (𝟙 (Z.p.obj A'.x)) A'.α.hom := hA'Lift
      letI : Z.p.IsHomLift (𝟙 (Z.p.obj A.x)) A.α.hom := hALift
      have hleftLift : Z.p.IsHomLift g (A'.α.hom ≫ χ0) :=
        IsHomLift.comp_lift_id_left' (p := Z.p) (Z.p.obj A'.x) A'.α.hom g χ0
      have hrightLift : Z.p.IsHomLift g (χ0 ≫ A.α.hom) :=
        IsHomLift.comp_lift_id_right' (p := Z.p) g χ0 (Z.p.obj A.x) A.α.hom
      letI : Z.p.IsHomLift g (A'.α.hom ≫ χ0) := hleftLift
      letI : Z.p.IsHomLift g (χ0 ≫ A.α.hom) := hrightLift
      exact @Functor.IsStronglyCartesian.ext _ _ _ _ Z.p _ _ _ _
        (Z.p.map φ.φ) φ.φ hφ _ _ g
        (A'.α.hom ≫ χ0) (χ0 ≫ A.α.hom) hleftLift hrightLift <| by
        calc
          (A'.α.hom ≫ χ0) ≫ φ.φ = A'.α.hom ≫ (χ0 ≫ φ.φ) := by
            simp
          _ = A'.α.hom ≫ ψ.φ := by rw [hχ0fac]
          _ = ψ.φ ≫ B.α.hom := by simpa using ψ.comm
          _ = (χ0 ≫ φ.φ) ≫ B.α.hom := by rw [hχ0fac]
          _ = χ0 ≫ (φ.φ ≫ B.α.hom) := by simp [Category.assoc]
          _ = χ0 ≫ (A.α.hom ≫ φ.φ) := by rw [← φ.comm]
          _ = (χ0 ≫ A.α.hom) ≫ φ.φ := by simp [Category.assoc]
    let χ : A' ⟶ A := { φ := χ0, comm := hχ0comm }
    refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
    · -- The chosen factor is a lift in absolute inertia because its underlying arrow is.
      apply absolute_inertia_is_hom_lift_iff_underlying.mpr
      exact hχ0.1
    · -- The factorization equality is detected on underlying inertia morphisms.
      apply RelativeInertiaHom.ext
      exact hχ0fac
    · intro π hπ
      -- Uniqueness likewise reduces to uniqueness for the underlying strongly cartesian arrow.
      apply RelativeInertiaHom.ext
      have hπUnderlying : Z.p.IsHomLift g π.φ :=
        absolute_inertia_is_hom_lift_iff_underlying.mp hπ.1
      have hπfac : π.φ ≫ φ.φ = ψ.φ := by
        simpa using congrArg RelativeInertiaHom.φ hπ.2
      exact hχ0uniq π.φ ⟨hπUnderlying, hπfac⟩

/-- Helper for Chap08 Lemma 8 8 5: a vertical lift of an automorphism over an identified base
object maps to the identity in the base category. -/
private theorem absolute_inertia_lift_iso_map_hom_eq_id
    {Z : FibredCategoryOver C} {R : C} {y : Z.S} {e : y ≅ y}
    (he : Z.p.IsHomLift (𝟙 R) e.hom) (hy : Z.p.obj y = R) :
    Z.p.map e.hom = 𝟙 (Z.p.obj y) := by
  -- The hom-lift equation identifies the base image with the identity after transporting the
  -- chosen source object to the external base object.
  letI : Z.p.IsHomLift (𝟙 R) e.hom := he
  subst hy
  simpa using (IsHomLift.eq_of_isHomLift Z.p (𝟙 (Z.p.obj y)) e.hom).symm

/-- Helper for Chap08 Lemma 8 8 5: a vertical automorphism of an absolute-inertia object pulls
back along a strongly cartesian lift of its underlying object. -/
private theorem absolute_inertia_pullback_automorphism_iso
    {Z : FibredCategoryOver C} {B : (CategoryOver.absoluteInertiaOver Z.toBasedCategory).obj}
    {R : C} {y : Z.S} {f : R ⟶ Z.p.obj B.x}
    (a : y ⟶ B.x) (ha : Z.p.IsStronglyCartesian f a) :
    ∃ e : y ≅ y, Z.p.IsHomLift (𝟙 R) e.hom ∧ e.hom ≫ a = a ≫ B.α.hom := by
  -- Pull back first the automorphism and then its inverse; the two pulled-back endomorphisms are
  -- inverse by strong-cartesian uniqueness after postcomposing with `a`.
  letI : Z.p.IsStronglyCartesian f a := ha
  have hBhom : Z.p.IsHomLift (𝟙 (Z.p.obj B.x)) B.α.hom := by
    simpa [absoluteInertiaObject_map_hom_eq_id B] using
      (inferInstance : Z.p.IsHomLift (Z.p.map B.α.hom) B.α.hom)
  have hpull (β : B.x ⟶ B.x) (hβlift : Z.p.IsHomLift (𝟙 (Z.p.obj B.x)) β) :
      ∃ βy : y ⟶ y, Z.p.IsHomLift (𝟙 R) βy ∧ βy ≫ a = a ≫ β := by
    letI : Z.p.IsHomLift (𝟙 (Z.p.obj B.x)) β := hβlift
    have haβ : Z.p.IsHomLift f (a ≫ β) := by
      simpa using
        (inferInstance : Z.p.IsHomLift (f ≫ 𝟙 (Z.p.obj B.x)) (a ≫ β))
    letI : Z.p.IsHomLift f (a ≫ β) := haβ
    obtain ⟨βy, hβy, -⟩ :=
      Functor.IsStronglyCartesian.universal_property Z.p f a (𝟙 R) f
        (Category.id_comp f).symm (a ≫ β)
    exact ⟨βy, hβy.1, hβy.2⟩
  obtain ⟨αh, hαh_lift, hαh_eq⟩ := hpull B.α.hom hBhom
  have hBinv : Z.p.IsHomLift (𝟙 (Z.p.obj B.x)) B.α.inv := by
    simpa [absoluteInertiaObject_map_inv_eq_id B] using
      (inferInstance : Z.p.IsHomLift (Z.p.map B.α.inv) B.α.inv)
  obtain ⟨αi, hαi_lift, hαi_eq⟩ := hpull B.α.inv hBinv
  have hαhαi : αh ≫ αi = 𝟙 y := by
    letI : Z.p.IsHomLift (𝟙 R) αh := hαh_lift
    letI : Z.p.IsHomLift (𝟙 R) αi := hαi_lift
    have hId : Z.p.IsHomLift (𝟙 R) (𝟙 y) :=
      IsHomLift.id (IsHomLift.domain_eq Z.p f a)
    letI : Z.p.IsHomLift (𝟙 R) (𝟙 y) := hId
    apply Functor.IsStronglyCartesian.ext (p := Z.p) (f := f) (φ := a) (g := 𝟙 R)
    calc
      (αh ≫ αi) ≫ a = αh ≫ (αi ≫ a) := by simp [Category.assoc]
      _ = αh ≫ (a ≫ B.α.inv) := by rw [hαi_eq]
      _ = (αh ≫ a) ≫ B.α.inv := by simp [Category.assoc]
      _ = (a ≫ B.α.hom) ≫ B.α.inv := by rw [hαh_eq]
      _ = a := by simp [Category.assoc]
      _ = (𝟙 y) ≫ a := by simp
  have hαiαh : αi ≫ αh = 𝟙 y := by
    letI : Z.p.IsHomLift (𝟙 R) αh := hαh_lift
    letI : Z.p.IsHomLift (𝟙 R) αi := hαi_lift
    have hId : Z.p.IsHomLift (𝟙 R) (𝟙 y) :=
      IsHomLift.id (IsHomLift.domain_eq Z.p f a)
    letI : Z.p.IsHomLift (𝟙 R) (𝟙 y) := hId
    apply Functor.IsStronglyCartesian.ext (p := Z.p) (f := f) (φ := a) (g := 𝟙 R)
    calc
      (αi ≫ αh) ≫ a = αi ≫ (αh ≫ a) := by simp [Category.assoc]
      _ = αi ≫ (a ≫ B.α.hom) := by rw [hαh_eq]
      _ = (αi ≫ a) ≫ B.α.hom := by simp [Category.assoc]
      _ = (a ≫ B.α.inv) ≫ B.α.hom := by rw [hαi_eq]
      _ = a := by simp [Category.assoc]
      _ = (𝟙 y) ≫ a := by simp
  exact ⟨⟨αh, αi, hαhαi, hαiαh⟩, hαh_lift, hαh_eq⟩

/-- Helper for Chap08 Lemma 8 8 5: every base arrow into an absolute-inertia object has a
strongly cartesian lift whose underlying morphism is strongly cartesian in the ambient fibred
category. -/
private theorem absolute_inertia_exists_cartesian_lift_with_underlying
    {Z : FibredCategoryOver C} (B : (CategoryOver.absoluteInertiaOver Z.toBasedCategory).obj)
    {R : C} (f : R ⟶ Z.p.obj B.x) :
    ∃ A : (CategoryOver.absoluteInertiaOver Z.toBasedCategory).obj,
      ∃ τ : A ⟶ B,
        (CategoryOver.absoluteInertiaOver Z.toBasedCategory).p.IsStronglyCartesian f τ ∧
          Z.p.IsStronglyCartesian f τ.φ := by
  -- Choose a cartesian lift in `Z`, pull back the target automorphism, and then rebuild the
  -- absolute-inertia lift using the forward underlying-cartesian bridge.
  obtain ⟨y, a, ha_cart⟩ := IsPreFibered.exists_isCartesian Z.p rfl f
  letI : Z.p.IsCartesian f a := ha_cart
  letI : Z.p.IsStronglyCartesian f a :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian Z.p f a
  have hy : Z.p.obj y = R := IsHomLift.domain_eq Z.p f a
  obtain ⟨e, he_lift, he_eq⟩ :=
    absolute_inertia_pullback_automorphism_iso (Z := Z) (B := B) (R := R) (y := y) (f := f) a
      (show Z.p.IsStronglyCartesian f a from inferInstance)
  let A : (CategoryOver.absoluteInertiaOver Z.toBasedCategory).obj :=
    { x := y
      α := e
      map_hom_eq_id := absolute_inertia_lift_iso_map_hom_eq_id he_lift hy }
  let τ : A ⟶ B :=
    { φ := a
      comm := he_eq }
  have hτUnderlying : Z.p.IsStronglyCartesian f τ.φ := by
    simpa [τ] using (show Z.p.IsStronglyCartesian f a from inferInstance)
  have hτUnderlyingOwner : Z.p.IsStronglyCartesian (Z.p.map τ.φ) τ.φ := by
    letI : Z.p.IsStronglyCartesian f τ.φ := hτUnderlying
    letI : Z.p.IsHomLift f τ.φ := hτUnderlying.toIsHomLift
    exact BasedFunctor.isStronglyCartesian_rebase_over_target_eq
      (p := Z.p) (hb := rfl) (f := f) τ.φ
  have hτInertiaOwner : (CategoryOver.absoluteInertiaOver Z.toBasedCategory).p.IsStronglyCartesian
      ((CategoryOver.absoluteInertiaOver Z.toBasedCategory).p.map τ) τ :=
    absolute_inertia_isStronglyCartesian_of_underlying hτUnderlyingOwner
  have hτLift : (CategoryOver.absoluteInertiaOver Z.toBasedCategory).p.IsHomLift f τ := by
    apply absolute_inertia_is_hom_lift_iff_underlying.mpr
    exact hτUnderlying.toIsHomLift
  have hτInertia : (CategoryOver.absoluteInertiaOver Z.toBasedCategory).p.IsStronglyCartesian f τ := by
    letI : (CategoryOver.absoluteInertiaOver Z.toBasedCategory).p.IsStronglyCartesian
        ((CategoryOver.absoluteInertiaOver Z.toBasedCategory).p.map τ) τ := hτInertiaOwner
    letI : (CategoryOver.absoluteInertiaOver Z.toBasedCategory).p.IsHomLift f τ := hτLift
    exact BasedFunctor.isStronglyCartesian_of_external_hom_lift
      (CategoryOver.absoluteInertiaOver Z.toBasedCategory).p τ
  exact ⟨A, τ, hτInertia, hτUnderlying⟩

/-- Helper for Chap08 Lemma 8 8 5: cartesianness in absolute inertia reflects to cartesianness
of the underlying morphism in the ambient fibred category. -/
private theorem absolute_inertia_underlying_isStronglyCartesian
    {Z : FibredCategoryOver C}
    {A B : (CategoryOver.absoluteInertiaOver Z.toBasedCategory).obj}
    {φ : A ⟶ B}
    (hφ : (CategoryOver.absoluteInertiaOver Z.toBasedCategory).p.IsStronglyCartesian
      ((CategoryOver.absoluteInertiaOver Z.toBasedCategory).p.map φ) φ) :
    Z.p.IsStronglyCartesian (Z.p.map φ.φ) φ.φ := by
  -- Route correction: do not promote arbitrary underlying competitors to inertia objects.
  -- Instead compare the given inertia-cartesian arrow with a canonical inertia lift whose
  -- underlying arrow is already cartesian.
  -- Compare the given cartesian inertia arrow with a canonical one over the same base arrow,
  -- then cancel the vertical comparison isomorphism on the source.
  let q := (CategoryOver.absoluteInertiaOver Z.toBasedCategory).p
  let f : Z.p.obj A.x ⟶ Z.p.obj B.x := Z.p.map φ.φ
  have hφLift : q.IsHomLift f φ := by
    apply absolute_inertia_is_hom_lift_iff_underlying.mpr
    exact (show Z.p.IsHomLift f φ.φ from inferInstance)
  have hφExternal : q.IsStronglyCartesian f φ := by
    letI : q.IsStronglyCartesian (q.map φ) φ := hφ
    letI : q.IsHomLift f φ := hφLift
    exact BasedFunctor.isStronglyCartesian_of_external_hom_lift q φ
  obtain ⟨A', τ, hτq, hτUnderlying⟩ :=
    absolute_inertia_exists_cartesian_lift_with_underlying (Z := Z) B f
  letI : q.IsStronglyCartesian f φ := hφExternal
  letI : q.IsStronglyCartesian f τ := hτq
  have hf : f = (Iso.refl (Z.p.obj A.x)).hom ≫ f := by simp
  let e : A' ≅ A := Functor.IsStronglyCartesian.domainIsoOfBaseIso q hf φ τ
  have he_hom_fac : e.hom ≫ φ = τ := by
    change (Functor.IsStronglyCartesian.domainIsoOfBaseIso q hf φ τ).hom ≫ φ = τ
    rw [Functor.IsStronglyCartesian.domainIsoOfBaseIso_hom]
    exact Functor.IsStronglyCartesian.fac q f φ hf τ
  have he_inv_fac : e.inv ≫ τ = φ := by
    calc
      e.inv ≫ τ = e.inv ≫ (e.hom ≫ φ) := by rw [← he_hom_fac]
      _ = (e.inv ≫ e.hom) ≫ φ := by simp
      _ = φ := by simp
  have he_inv_lift_q : q.IsHomLift (𝟙 (Z.p.obj A.x)) e.inv := by
    change q.IsHomLift (Iso.refl (Z.p.obj A.x)).inv e.inv
    exact Functor.IsStronglyCartesian.domainUniqueUpToIso_hom_isHomLift q hf φ τ
  have he_inv_lift : Z.p.IsHomLift (𝟙 (Z.p.obj A.x)) e.inv.φ :=
    absolute_inertia_is_hom_lift_iff_underlying.mp he_inv_lift_q
  have hIsoInv : IsIso e.inv.φ := by
    change IsIso ((relativeInertiaStructureFunctor Z.p).map e.inv)
    infer_instance
  letI : IsIso e.inv.φ := hIsoInv
  have hInvStrong : Z.p.IsStronglyCartesian (𝟙 (Z.p.obj A.x)) e.inv.φ := by
    letI : Z.p.IsHomLift (𝟙 (Z.p.obj A.x)) e.inv.φ := he_inv_lift
    infer_instance
  have hcomp : Z.p.IsStronglyCartesian ((𝟙 (Z.p.obj A.x)) ≫ f) (e.inv.φ ≫ τ.φ) := by
    letI : Z.p.IsStronglyCartesian (𝟙 (Z.p.obj A.x)) e.inv.φ := hInvStrong
    letI : Z.p.IsStronglyCartesian f τ.φ := hτUnderlying
    infer_instance
  have he_inv_fac_underlying : e.inv.φ ≫ τ.φ = φ.φ := by
    simpa using congrArg RelativeInertiaHom.φ he_inv_fac
  simpa [f, he_inv_fac_underlying] using hcomp

/-- Helper for Lemma 8.8.5: the canonical relative diagonal over the base preserves strongly
cartesian morphisms. This is the public version of the Chapter 4 private bridge needed by the
explicit `2`-fibre-product model of inertia. -/
private theorem relative_diagonal_preservesStronglyCartesian
    {X Y : FibredCategoryOver.{u, v, max u v, v} C} (F : X ⟶ Y) :
    (BasedFunctor.relativeDiagonalOver
      (FibredCategoryMor.toBasedFunctor F)).PreservesStronglyCartesian := by
  -- The public Chapter 4 theorem records exactly the diagonal preservation statement needed here.
  exact relativeDiagonalOver_preserves_strongly_cartesian F

/-- Helper for Chap08 Lemma 8 8 5: the induced absolute-inertia map has the expected underlying
arrow in the target fibred category. -/
private theorem absoluteInertiaOverMap_map_hom
    {X Y : FibredCategoryOver C} (F : X ⟶ Y)
    {A B : (CategoryOver.absoluteInertiaOver X.toBasedCategory).obj} (φ : A ⟶ B) :
    ((absoluteInertiaOverMap (FibredCategoryMor.toBasedFunctor F)).map φ).φ =
      (FibredCategoryMor.toFunctor F).map φ.φ := by
  -- Unfold just the canonical Chapter 4 map and record the stable relative-inertia computation.
  simpa [CategoryOver.absoluteInertiaOverMap, FibredCategoryOver.absoluteInertiaOver,
    CategoryOver.absoluteInertiaOver, CategoryOver.relativeInertiaOver] using
    (relativeInertiaMap_map_hom (F₁ := FibredCategoryMor.toFunctor F)
      (F₂ := FibredCategoryMor.toFunctor F) (p' := Y.p)
      (comm := eqToIso (FibredCategoryMor.toBasedFunctor F).w) φ)

/-- The canonical map on absolute inertia induced by a morphism of fibred categories preserves
strongly cartesian morphisms. -/
theorem absoluteInertiaOverMap_preservesStronglyCartesian
    {X Y : FibredCategoryOver C} (F : X ⟶ Y) :
    BasedFunctor.PreservesStronglyCartesian
      (absoluteInertiaOverMap (FibredCategoryMor.toBasedFunctor F)) := by
  intro A B φ hφ
  -- Reflect cartesianness to the underlying fibred category before applying the original
  -- morphism `F`.
  have hφUnderlying : X.p.IsStronglyCartesian (X.p.map φ.φ) φ.φ := by
    exact absolute_inertia_underlying_isStronglyCartesian hφ
  have hmapUnderlying :
      Y.p.IsStronglyCartesian
        (Y.p.map ((FibredCategoryMor.toFunctor F).map φ.φ))
        ((FibredCategoryMor.toFunctor F).map φ.φ) :=
    FibredCategoryMor.map_stronglyCartesian F φ.φ hφUnderlying
  -- Rewrite the underlying component of the mapped inertia arrow and rebuild the
  -- strong-cartesian structure in absolute inertia.
  apply absolute_inertia_isStronglyCartesian_of_underlying
  simpa [absoluteInertiaOverMap_map_hom F φ] using hmapUnderlying

end CategoryTheory
