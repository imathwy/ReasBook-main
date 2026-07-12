import Mathlib
import StacksProject_2024.Chap04.Definition_4_33_6

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/- Domain-style sampling for Lemma 4.33.7:
- primary domain: chosen pullbacks in fibred categories and the associated Cat-valued
  pseudofunctor of fibers.
- inspected owner-level declarations:
  `PullbackChoice.pullbackFunctor`,
  `HasFibers.mkPullback`,
  `Functor.IsFibered.pullbackPullbackIso`,
  `IsCartesian.domainUniqueUpToIso`,
  `LocallyDiscrete.mkPseudofunctor`.
- best owner abstraction: the source-facing owner remains `PullbackChoice p`; the canonical target
  abstraction for the coherence package is a pseudofunctor `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`.
- primitive data: the chosen pullback system `hc : PullbackChoice p`.
- derived API: the comparison isomorphisms for composites and identities and the resulting
  pseudofunctor `hc.fiberPseudofunctor`.

Source/core/bridge triage:
- `source-facing`: the comparison isomorphisms from the textbook's chosen pullback system.
- `core/canonical`: `PullbackChoice p`, `Functor.IsFibered`, and `LocallyDiscrete.mkPseudofunctor`.
- `bridge/view`: `PullbackChoice.pullbackCompIso`, `PullbackChoice.pullbackIdIso`, and
  `PullbackChoice.fiberPseudofunctor`, which package the chosen pullbacks into the canonical
  pseudofunctor language.

This file therefore keeps the chosen pullback data on the existing owner `PullbackChoice` and
avoids exposing a public chosen witness built from `HasFibers.canonical`. -/

namespace PullbackChoice

variable {p : S ⥤ C} (hc : PullbackChoice p)

/-- The component at `x` of the comparison isomorphism
`(g ≫ f)^* ≅ f^* ⋙ g^*` from Lemma 4.33.7 (1). -/
noncomputable def pullbackCompComponentIso
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U) :
    (g ≫ f) ^*[hc] x ≅ g ^*[hc] (f ^*[hc] x) :=
  let _ : p.IsFibered := hc.isFibered
  let e := IsCartesian.domainUniqueUpToIso p (g ≫ f)
    (hc.map g (f ^*[hc] x) ≫ hc.map f x)
    (hc.map (g ≫ f) x)
  { hom := ⟨e.hom, inferInstance⟩
    inv := ⟨e.inv, inferInstance⟩
    hom_inv_id := by
      apply Fiber.hom_ext
      exact e.hom_inv_id
    inv_hom_id := by
      apply Fiber.hom_ext
      exact e.inv_hom_id }

-- Proof sketch: the chosen component is the morphism furnished by uniqueness of morphisms into the
-- strongly cartesian arrow `hc.map g (f ^*[hc] x) ≫ hc.map f x`, so its defining factorization is
-- exactly the commutative square from the textbook statement.
/-- The comparison component for iterated pullback factors the chosen pullback morphisms through the
same map to `x`. -/
theorem pullbackCompComponentIso_fac
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U) :
    (hc.pullbackCompComponentIso f g x).hom.1 ≫ hc.map g (f ^*[hc] x) ≫ hc.map f x =
      hc.map (g ≫ f) x := sorry

-- Proof sketch: both sides are morphisms in the fiber over `W`; after forgetting to the total
-- category, they are the unique morphisms compatible with the factorization property of the two
-- chosen strongly cartesian lifts, so equality follows from uniqueness.
private theorem pullbackCompIso_naturality
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    ∀ {x y : Fiber p U} (φ : x ⟶ y),
      (hc.pullbackFunctor (g ≫ f)).map φ ≫
          (hc.pullbackCompComponentIso f g y).hom =
        (hc.pullbackCompComponentIso f g x).hom ≫
          ((hc.pullbackFunctor f ⋙ hc.pullbackFunctor g).map φ) := sorry

/-- Lemma 4.33.7 (1): for composable morphisms `f : V ⟶ U` and `g : W ⟶ V`, a chosen pullback
system on the fibred category `p : S ⥤ C` provides the canonical isomorphism
`(g ≫ f)^* ≅ f^* ⋙ g^*` between pullback functors on the standard fibers. -/
noncomputable def pullbackCompIso
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    hc.pullbackFunctor (g ≫ f) ≅ hc.pullbackFunctor f ⋙ hc.pullbackFunctor g :=
  NatIso.ofComponents (hc.pullbackCompComponentIso f g) (hc.pullbackCompIso_naturality f g)

-- Proof sketch: the source-text commuting square determines each component uniquely in the fiber
-- over `W`, hence two comparison isomorphisms with the stated factorization property agree
-- componentwise and therefore as natural isomorphisms.
/-- Lemma 4.33.7 (2): the comparison isomorphism `(g ≫ f)^* ≅ f^* ⋙ g^*` is uniquely determined
by the requirement that each component factors the chosen pullback morphisms through the same map
to the original object. -/
theorem pullbackCompIso_unique
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (α : hc.pullbackFunctor (g ≫ f) ≅ hc.pullbackFunctor f ⋙ hc.pullbackFunctor g)
    (hα : ∀ x : Fiber p U,
      (α.hom.app x).1 ≫ hc.map g (f ^*[hc] x) ≫ hc.map f x = hc.map (g ≫ f) x) :
    α = hc.pullbackCompIso f g := sorry

-- Proof sketch: the identity of an object in the fiber lies over `𝟙 U` and is an isomorphism, so
-- the standard fact that isomorphisms over a base morphism are strongly cartesian applies.
private theorem fiberId_isStronglyCartesian
    (U : C) (x : Fiber p U) :
    p.IsStronglyCartesian (𝟙 U) (𝟙 (x.1)) := sorry

/-- The component at `x` of the unit comparison `α_U : 𝟭 ≅ (𝟙 U)^*` from Lemma 4.33.7 (2). -/
noncomputable def pullbackIdComponentIso
    (U : C) (x : Fiber p U) :
    x ≅ (𝟙 U) ^*[hc] x :=
  let _ : p.IsFibered := hc.isFibered
  let _ : p.IsStronglyCartesian (𝟙 U) (𝟙 (x.1)) := fiberId_isStronglyCartesian U x
  let _ : p.IsCartesian (𝟙 U) (𝟙 (x.1)) := inferInstance
  let e := IsCartesian.domainUniqueUpToIso p (𝟙 U) (hc.map (𝟙 U) x) (𝟙 (x.1))
  { hom := ⟨e.hom, inferInstance⟩
    inv := ⟨e.inv, inferInstance⟩
    hom_inv_id := by
      apply Fiber.hom_ext
      exact e.hom_inv_id
    inv_hom_id := by
      apply Fiber.hom_ext
      exact e.inv_hom_id }

-- Proof sketch: the identity of `x` and the chosen pullback arrow `hc.map (𝟙 U) x` are both
-- strongly cartesian over `𝟙 U`, so the chosen comparison component is characterized by the
-- displayed triangle and hence satisfies the required factorization equality.
/-- The identity-pullback comparison component factors the chosen pullback arrow through the
identity of `x`. -/
theorem pullbackIdComponentIso_fac
    (U : C) (x : Fiber p U) :
    (hc.pullbackIdComponentIso U x).hom.1 ≫ hc.map (𝟙 U) x = 𝟙 (x.1) := sorry

-- Proof sketch: after forgetting to the total category, both composites express the same morphism
-- over `𝟙 U` compatible with the defining triangle for the identity pullback comparison; uniqueness
-- in the fiber gives naturality.
private theorem pullbackIdIso_naturality
    (U : C) :
    ∀ {x y : Fiber p U} (φ : x ⟶ y),
      φ ≫ (hc.pullbackIdComponentIso U y).hom =
        (hc.pullbackIdComponentIso U x).hom ≫ (hc.pullbackFunctor (𝟙 U)).map φ := sorry

/-- Lemma 4.33.7 (3): the canonical unit isomorphism
`α_U : 𝟭 (Fiber p U) ≅ (𝟙 U)^*`. -/
noncomputable def pullbackIdIso
    (U : C) :
    𝟭 (Fiber p U) ≅ hc.pullbackFunctor (𝟙 U) :=
  NatIso.ofComponents (hc.pullbackIdComponentIso U) (hc.pullbackIdIso_naturality U)

-- Proof sketch: as in the source text, the displayed triangle over `𝟙 U` determines each
-- component uniquely in the fiber over `U`; extensionality for natural isomorphisms then gives the
-- global uniqueness statement.
/-- Lemma 4.33.7 (4): the unit comparison `α_U : 𝟭 ≅ (𝟙 U)^*` is uniquely determined by the
requirement that its components factor the chosen identity pullback arrows through identities. -/
theorem pullbackIdIso_unique
    (U : C) (α : 𝟭 (Fiber p U) ≅ hc.pullbackFunctor (𝟙 U))
    (hα : ∀ x : Fiber p U, (α.hom.app x).1 ≫ hc.map (𝟙 U) x = 𝟙 (x.1)) :
    α = hc.pullbackIdIso U := sorry

-- Proof sketch: this is exactly the associativity coherence required in Lemma 4.33.7 (3) for the
-- comparison isomorphisms from part (1), expressed in mathlib's pseudofunctor orientation.
private theorem fiberPseudofunctor_map₂_associator
    {U V W X : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (h : W ⟶ X) :
    (Cat.Hom.isoMk (hc.pullbackCompIso (f ≫ g).unop h.unop)).hom ≫
        (Cat.Hom.isoMk (hc.pullbackCompIso f.unop g.unop)).hom ▷
            (hc.pullbackFunctor h.unop).toCatHom ≫
          (α_ ((hc.pullbackFunctor f.unop).toCatHom) ((hc.pullbackFunctor g.unop).toCatHom)
            ((hc.pullbackFunctor h.unop).toCatHom)).hom ≫
            (hc.pullbackFunctor f.unop).toCatHom ◁
              (Cat.Hom.isoMk (hc.pullbackCompIso g.unop h.unop)).inv ≫
              (Cat.Hom.isoMk (hc.pullbackCompIso f.unop (g ≫ h).unop)).inv =
      eqToHom (by
        exact congrArg (fun k ↦ (hc.pullbackFunctor k.unop).toCatHom) (Category.assoc f g h)) :=
  sorry

-- Proof sketch: this is the left unit coherence for the pseudofunctor determined by the chosen
-- pullback system, using the unit comparison isomorphisms from part (2).
private theorem fiberPseudofunctor_map₂_left_unitor
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (Cat.Hom.isoMk (hc.pullbackCompIso (𝟙 U).unop f.unop)).hom ≫
        (Cat.Hom.isoMk ((hc.pullbackIdIso (unop U)).symm)).hom ▷
            (hc.pullbackFunctor f.unop).toCatHom ≫
          (λ_ ((hc.pullbackFunctor f.unop).toCatHom)).hom =
      eqToHom (by
        exact congrArg (fun k ↦ (hc.pullbackFunctor k.unop).toCatHom) (Category.id_comp f)) :=
  sorry

-- Proof sketch: this is the right unit coherence for the same pseudofunctor data.
private theorem fiberPseudofunctor_map₂_right_unitor
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (Cat.Hom.isoMk (hc.pullbackCompIso f.unop (𝟙 V).unop)).hom ≫
        (hc.pullbackFunctor f.unop).toCatHom ◁
          (Cat.Hom.isoMk ((hc.pullbackIdIso (unop V)).symm)).hom ≫
          (ρ_ ((hc.pullbackFunctor f.unop).toCatHom)).hom =
      eqToHom (by
        exact congrArg (fun k ↦ (hc.pullbackFunctor k.unop).toCatHom) (Category.comp_id f)) :=
  sorry

/-- Lemma 4.33.7 (5): the fiber categories, pullback functors, composition comparisons
`α_{g,f}`, and unit comparisons `α_U` assemble into a pseudofunctor `Cᵒᵖ ⥤ᵖ Cat`, i.e. into the
canonical mathlib model of a pseudofunctor to the source text's `(2,1)`-category of categories. -/
noncomputable def fiberPseudofunctor :
    LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun U ↦ Cat.of (Fiber p (unop U)))
    (fun f ↦ (hc.pullbackFunctor f.unop).toCatHom)
    (fun U ↦ Cat.Hom.isoMk ((hc.pullbackIdIso (unop U)).symm))
    (fun f g ↦ Cat.Hom.isoMk (hc.pullbackCompIso f.unop g.unop))
    (fun f g h ↦ hc.fiberPseudofunctor_map₂_associator f g h)
    (fun f ↦ hc.fiberPseudofunctor_map₂_left_unitor f)
    (fun f ↦ hc.fiberPseudofunctor_map₂_right_unitor f)

end PullbackChoice

/-- The canonical chosen pullback system on a fibred category, obtained from the canonical fiber
categories and pullback maps supplied by `HasFibers.canonical`. This is a bridge from the owner
`Functor.IsFibered` to the concrete `PullbackChoice` API used for explicit pullback functors. -/
noncomputable abbrev canonicalPullbackChoice
    (p : S ⥤ C) [p.IsFibered] :
    PullbackChoice p :=
  let _ : HasFibers p := HasFibers.canonical p
  { obj := fun f x ↦ HasFibers.mkPullback f x.2
    map := fun f x ↦ HasFibers.pullbackMap f x.2
    isStronglyCartesian := fun f x ↦
      Functor.IsFibered.isStronglyCartesian_of_isCartesian p f (HasFibers.pullbackMap f x.2) }

/-- The canonical pseudofunctor of fibers attached to a fibred category, obtained from the
canonical pullback choice on the projection functor. This is the standard bridge from the owner
`canonicalPullbackChoice p` to the pseudofunctor surface used downstream. -/
noncomputable abbrev canonicalFiberPseudofunctor
    (p : S ⥤ C) [p.IsFibered] :
    LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat :=
  (canonicalPullbackChoice p).fiberPseudofunctor

end CategoryTheory
