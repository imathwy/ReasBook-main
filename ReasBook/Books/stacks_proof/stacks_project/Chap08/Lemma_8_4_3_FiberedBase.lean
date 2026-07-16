import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import stacks_proof.stacks_project.Chap04.CanonicalPullbackChoice

open CategoryTheory
open CategoryTheory Functor
open Functor.IsPreFibered
open Functor.Fiber

universe u₁ u₂ v₁ v₂

section

variable {C : Type u₁} {X : Type u₂} [Category.{v₁} C] [Category.{v₂} X]
variable (p : X ⥤ C)
variable (P : ObjectProperty X)

/- Domain-style sampling:
- primary domain: stacks over a site, fibred categories, and full subcategories cut out by an
  object property.
- inspected owner-level declarations:
  `ObjectProperty.FullSubcategory`,
  `ObjectProperty.inverseImage`,
  `ObjectProperty.isoClosure`,
  `Functor.Fiber.fiberInclusion`,
  `canonicalPullbackChoice`,
  `IsStackOnSite`.
- best owner abstraction: the restricted projection `P.ι ⋙ p : P.FullSubcategory ⥤ C`.
- primitive data: the object property `P` together with closure of canonical pullback objects up to
  fiberwise isomorphism and a descent-locality hypothesis stated in each fiber.
- derived API: the induced stack structure on the restricted projection.
- layer triage:
  `source-facing`: Lemma 8.4.3, a criterion for the full subcategory to remain a stack;
  `core/canonical`: `p.IsFibered` and the inclusion `P.ι`;
  `bridge/view`: the canonical fiberwise property
  `(P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).isoClosure` on `p.Fiber U`, together with
  the chosen pullback owner `canonicalPullbackChoice p`.
-/

variable [p.IsFibered]

/-- Helper for Lemma 8.4.3: composing in `C` and then passing to the locally discrete opposite is
the same as composing the corresponding `toLoc` arrows in the owner order used by pullback
transport. -/
theorem comp_toLoc_eq
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf) :
    f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc := by
  -- Translate the composite equality to `LocallyDiscrete Cᵒᵖ`.
  simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
    congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op hgf)

/-- Helper for Lemma 8.4.3: a morphism in the full subcategory lifts a base arrow for the
restricted projection exactly when its underlying ambient morphism lifts the same arrow. -/
lemma fullSubcategory_homLift_iff_ambient
    {R S : C} {a b : P.FullSubcategory} (f : R ⟶ S) (φ : a ⟶ b) :
    (P.ι ⋙ p).IsHomLift f φ ↔ p.IsHomLift f φ.hom := by
  constructor
  · intro hφ
    -- Forgetting the full-subcategory structure preserves the same base factorization.
    letI : (P.ι ⋙ p).IsHomLift f φ := hφ
    exact
      IsHomLift.of_fac' p f φ.hom
        (IsHomLift.domain_eq (P.ι ⋙ p) f φ)
        (IsHomLift.codomain_eq (P.ι ⋙ p) f φ) <| by
          simpa using (IsHomLift.fac' (P.ι ⋙ p) f φ)
  · intro hφ
    -- The restricted projection has the same object map and morphism map as the ambient one.
    have hφDom : p.obj a.obj = R := by
      letI : p.IsHomLift f φ.hom := hφ
      exact IsHomLift.domain_eq p f φ.hom
    have hφCod : p.obj b.obj = S := by
      letI : p.IsHomLift f φ.hom := hφ
      exact IsHomLift.codomain_eq p f φ.hom
    exact
      IsHomLift.of_fac' (P.ι ⋙ p) f φ hφDom hφCod <| by
        letI : p.IsHomLift f φ.hom := hφ
        simpa using (IsHomLift.fac' p f φ.hom)

/-- Helper for Lemma 8.4.3: a strongly cartesian morphism in the ambient category between objects
of the full subcategory remains strongly cartesian for the restricted projection. -/
lemma fullSubcategory_hom_isStronglyCartesian_of_ambient
    {R S : C} {a b : P.FullSubcategory} (f : R ⟶ S) (φ : a ⟶ b)
    [hpφ : p.IsStronglyCartesian f φ.hom] :
    (P.ι ⋙ p).IsStronglyCartesian f φ := by
  have hφLift : p.IsHomLift f φ.hom := hpφ.toIsHomLift
  have hφDom : p.obj a.obj = R := IsHomLift.domain_eq p f φ.hom
  have hφCod : p.obj b.obj = S := IsHomLift.codomain_eq p f φ.hom
  have hφOwnerAmbient : p.IsStronglyCartesian (p.map φ.hom) φ.hom := by
    -- The lift witness identifies the external base arrow with the owner map `p.map φ.hom`.
    letI : p.IsStronglyCartesian f φ.hom := hpφ
    subst hφDom
    subst hφCod
    have hbase : f = p.map φ.hom := IsHomLift.eq_of_isHomLift p f φ.hom
    subst hbase
    infer_instance
  have hφOwnerRestricted : (P.ι ⋙ p).IsStronglyCartesian ((P.ι ⋙ p).map φ) φ := by
    -- The restricted universal property is the ambient one, transported across the inclusion
    -- bridge for hom lifts.
    letI : p.IsStronglyCartesian (p.map φ.hom) φ.hom := hφOwnerAmbient
    refine
      { toIsHomLift := by infer_instance
        universal_property' := ?_ }
    intro a' g φ' hφ'
    have hφ'Ambient :
        p.IsHomLift (g ≫ p.map φ.hom) φ'.hom := by
      simpa [Functor.comp_map] using
        (fullSubcategory_homLift_iff_ambient (p := p) (P := P)
          (f := g ≫ (P.ι ⋙ p).map φ) (φ := φ')).1 hφ'
    letI : p.IsHomLift (g ≫ p.map φ.hom) φ'.hom := hφ'Ambient
    obtain ⟨χ, hχ, hχuniq⟩ :=
      IsStronglyCartesian.universal_property p (p.map φ.hom) φ.hom g
        (g ≫ p.map φ.hom) rfl φ'.hom
    refine ⟨ObjectProperty.homMk χ, ?_, ?_⟩
    · refine ⟨(fullSubcategory_homLift_iff_ambient (p := p) (P := P)
        (f := g) (φ := ObjectProperty.homMk χ)).2 hχ.1, ?_⟩
      -- The factorization equality is the same after packaging `χ` back into the full
      -- subcategory.
      apply ObjectProperty.hom_ext
      simpa using hχ.2
    · intro ψ hψ
      -- Uniqueness is checked after forgetting to the ambient category.
      apply ObjectProperty.hom_ext
      exact hχuniq ψ.hom ⟨
        (fullSubcategory_homLift_iff_ambient (p := p) (P := P) (f := g) (φ := ψ)).1 hψ.1,
        by simpa using congrArg (fun k ↦ k.hom) hψ.2⟩
  have hφLiftRestricted : (P.ι ⋙ p).IsHomLift f φ :=
    (fullSubcategory_homLift_iff_ambient (p := p) (P := P) (f := f) (φ := φ)).2 hφLift
  -- Finally rebase the restricted owner-map strong-cartesian structure to the external base map
  -- `f`.
  letI : (P.ι ⋙ p).IsStronglyCartesian ((P.ι ⋙ p).map φ) φ := hφOwnerRestricted
  letI : (P.ι ⋙ p).IsHomLift f φ := hφLiftRestricted
  have hφDomRestricted : (P.ι ⋙ p).obj a = R := IsHomLift.domain_eq (P.ι ⋙ p) f φ
  have hφCodRestricted : (P.ι ⋙ p).obj b = S := IsHomLift.codomain_eq (P.ι ⋙ p) f φ
  subst hφDomRestricted
  subst hφCodRestricted
  have hbase : f = (P.ι ⋙ p).map φ := IsHomLift.eq_of_isHomLift (P.ι ⋙ p) f φ
  subst hbase
  infer_instance

/-- Helper for Lemma 8.4.3: the pullback-closure hypothesis produces strongly cartesian pullbacks
inside the full subcategory, before forgetting back to the ambient category. -/
lemma fullSubcategory_exists_ambient_stronglyCartesian_lift
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {V : C} (x : P.FullSubcategory) (f : V ⟶ (P.ι ⋙ p).obj x) :
    ∃ y : P.FullSubcategory, ∃ φ : y ⟶ x, p.IsStronglyCartesian f φ.hom := by
  let xFiber : p.Fiber ((P.ι ⋙ p).obj x) := Functor.Fiber.mk rfl
  have hpb := hpullback f xFiber x.property
  rw [ObjectProperty.prop_isoClosure_iff] at hpb
  rcases hpb with ⟨y, hy, ⟨e⟩⟩
  let y' : P.FullSubcategory := ⟨y.1, hy⟩
  let eX : (f ^*[canonicalPullbackChoice p] xFiber).1 ≅ y.1 :=
    (fiberInclusion : p.Fiber V ⥤ X).mapIso e
  let eX' : y.1 ≅ (f ^*[canonicalPullbackChoice p] xFiber).1 := eX.symm
  let pbMap : y'.obj ⟶ x.obj :=
    eX'.hom ≫ (canonicalPullbackChoice p).map f xFiber
  have hpbStronglyCartesian :
      p.IsStronglyCartesian f pbMap := by
    -- First move from `y` back to the canonical pullback, then use the chosen pullback arrow.
    letI : p.IsHomLift (𝟙 V) eX'.hom := by
      change p.IsHomLift (𝟙 V) ((fiberInclusion : p.Fiber V ⥤ X).map e.inv)
      infer_instance
    letI : p.IsStronglyCartesian (𝟙 V) eX'.hom :=
      IsStronglyCartesian.of_iso (p := p) (f := 𝟙 V) eX'
    letI : p.IsStronglyCartesian f ((canonicalPullbackChoice p).map f xFiber) :=
      (canonicalPullbackChoice p).isStronglyCartesian f xFiber
    simpa [pbMap] using
      (inferInstance : p.IsStronglyCartesian f
        (eX'.hom ≫ (canonicalPullbackChoice p).map f xFiber))
  exact ⟨y', ObjectProperty.homMk pbMap, hpbStronglyCartesian⟩

/-- Helper for Lemma 8.4.3: the pullback-closure hypothesis produces strongly cartesian pullbacks
inside the restricted projection, so the restricted projection is fibered. -/
lemma fullSubcategory_projection_isFibered
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x)) :
    (P.ι ⋙ p).IsFibered := by
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro x V f
  rcases
      fullSubcategory_exists_ambient_stronglyCartesian_lift
        (p := p) (P := P) (hpullback := hpullback) x f with
    ⟨y, φ, hφ⟩
  -- The restricted strong-cartesian lift is obtained by reusing the ambient one inside the full
  -- subcategory.
  exact
    ⟨y, φ,
      fullSubcategory_hom_isStronglyCartesian_of_ambient
        (p := p) (P := P) (f := f) (φ := φ) (hpφ := hφ)⟩

end
