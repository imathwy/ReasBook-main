import Mathlib
import stacks_proof.stacks_project.Chap04.CanonicalPullbackChoice

/-!
# Fiber pullback-composition coherence

For a chosen pullback system `hc : PullbackChoice p` on `p : 𝒳 ⥤ 𝒞`, the chosen pullback of an
object `x : Fiber p U` along a composite `g ≫ f` is canonically isomorphic to the iterated chosen
pullback `g ^*[hc] (f ^*[hc] x)`.

In older Mathlib this identification held *definitionally* (the chosen pullback reduced cheaply),
so the rest of the `Lemma 8.11.8` development used it silently.  After the
`FullSubcategory → ObjectProperty.FullSubcategory` refactor the underlying `whnf` no longer
terminates in a usable budget, so we expose the identification as an explicit, storm-free
isomorphism built from the strongly-cartesian universal property (it never forces `whnf` of the
chosen pullback).  This is the fiber-level analogue of the sheaf-level `pseudofunctor … mapComp'`
coherence.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace PullbackChoice

open Functor Functor.Fiber

variable {C : Type u₁} [Category.{v₁} C] {S : Type u₂} [Category.{v₂} S]
variable {p : S ⥤ C} (hc : PullbackChoice p)

/-- The canonical pullback-composition coherence isomorphism:
`(g ≫ f) ^*[hc] x ≅ g ^*[hc] (f ^*[hc] x)`.

Both sides carry a strongly-cartesian comparison morphism to `x` lying over `g ≫ f`
(`hc.map (g ≫ f) x` on the left, and the composite `hc.map g (f ^*[hc] x) ≫ hc.map f x` on the
right), so they are canonically isomorphic by the uniqueness of cartesian lifts.  The construction
uses the universal property abstractly and does **not** reduce the chosen-pullback data. -/
noncomputable def pullbackComp {U V W : C} (g : W ⟶ V) (f : V ⟶ U) (x : Fiber p U) :
    (g ≫ f) ^*[hc] x ≅ g ^*[hc] (f ^*[hc] x) where
  hom :=
    Functor.Fiber.homMk p W
      (IsCartesian.domainUniqueUpToIso p (g ≫ f) (hc.map (g ≫ f) x)
        (hc.map g (f ^*[hc] x) ≫ hc.map f x)).inv
  inv :=
    Functor.Fiber.homMk p W
      (IsCartesian.domainUniqueUpToIso p (g ≫ f) (hc.map (g ≫ f) x)
        (hc.map g (f ^*[hc] x) ≫ hc.map f x)).hom
  hom_inv_id := by
    apply (fiberInclusion (p := p) (S := W)).map_injective
    exact Iso.inv_hom_id _
  inv_hom_id := by
    apply (fiberInclusion (p := p) (S := W)).map_injective
    exact Iso.hom_inv_id _

@[simp]
lemma fiberInclusion_map_pullbackComp_hom {U V W : C} (g : W ⟶ V) (f : V ⟶ U) (x : Fiber p U) :
    fiberInclusion.map (hc.pullbackComp g f x).hom =
      (IsCartesian.domainUniqueUpToIso p (g ≫ f) (hc.map (g ≫ f) x)
        (hc.map g (f ^*[hc] x) ≫ hc.map f x)).inv :=
  rfl

@[simp]
lemma fiberInclusion_map_pullbackComp_inv {U V W : C} (g : W ⟶ V) (f : V ⟶ U) (x : Fiber p U) :
    fiberInclusion.map (hc.pullbackComp g f x).inv =
      (IsCartesian.domainUniqueUpToIso p (g ≫ f) (hc.map (g ≫ f) x)
        (hc.map g (f ^*[hc] x) ≫ hc.map f x)).hom :=
  rfl

/-- Defining factorization of the inverse comparison through the chosen cartesian lift on the
right: the composite `g ^*[hc] (f ^*[hc] x) ⟶ x` factors `hc.map (g ≫ f) x`. -/
@[reassoc]
lemma pullbackComp_inv_map {U V W : C} (g : W ⟶ V) (f : V ⟶ U) (x : Fiber p U) :
    fiberInclusion.map (hc.pullbackComp g f x).inv ≫ hc.map (g ≫ f) x =
      hc.map g (f ^*[hc] x) ≫ hc.map f x := by
  rw [fiberInclusion_map_pullbackComp_inv, IsCartesian.domainUniqueUpToIso_hom]
  exact IsCartesian.fac p (g ≫ f) (hc.map (g ≫ f) x)
    (hc.map g (f ^*[hc] x) ≫ hc.map f x)

end PullbackChoice

end CategoryTheory
