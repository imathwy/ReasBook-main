import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.stacks_project.Chap08.Definition_8_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory Functor
open Functor.IsPreFibered
open Functor.Fiber

universe u₁ u₂ v₁ v₂

section

variable {C : Type u₁} {X : Type u₂} [Category.{v₁} C] [Category.{v₂} X]
variable (J : GrothendieckTopology C) (p : X ⥤ C)
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
  `core/canonical`: `IsStackOnSite` and the inclusion `P.ι`;
  `bridge/view`: the canonical fiberwise property
  `(P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).isoClosure` on `p.Fiber U`, together with
  the chosen pullback owner `canonicalPullbackChoice p`.
-/

variable [IsStackOnSite J p]

-- Proof sketch: the canonical-pullback closure hypothesis supplies pullbacks in the full
-- subcategory up to isomorphism inside the relevant fiber, hence a fibered structure on
-- `P.FullSubcategory`. Because the inclusion is full, isomorphism presheaves agree with those in
-- the ambient stack, so they are sheaves. For effective descent, descend the local objects in the
-- ambient stack and then use the fiberwise local closure hypothesis to see that the descended
-- global object is isomorphic, in the fiber over the same base object, to an object of the full
-- subcategory.
/-- Lemma 8.4.3: if a stack over the site `(C, J)` has a full subcategory that is closed under
strongly cartesian pullback up to fiberwise isomorphism and is local for descent of objects in
each fiber, then the projection from that full subcategory to `C` is again a stack. -/
theorem fullSubcategory_projection_isStackOnSite
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    (hlocal : ∀ ⦃U : C⦄ (S : J.Cover U) (x : p.Fiber U)
      (hx : ∀ I : S.Arrow,
        ((P.inverseImage (fiberInclusion : p.Fiber I.Y ⥤ X)).isoClosure)
          (I.f ^*[canonicalPullbackChoice p] x)),
      ((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).isoClosure) x) :
    IsStackOnSite J (P.ι ⋙ p) := sorry

end
