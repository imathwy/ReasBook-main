import Mathlib
import StacksProject_2024.Chap15.Lemma_15_65_2
import StacksProject_2024.Chap15.Lemma_15_65_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for Lemma 15.65.6:
- primary domain: pseudo-coherent object properties in the derived category `D(R)` and their
  closure under distinguished triangles;
- sampled owner declarations:
  `DerivedCategory.IsPseudoCoherent`,
  `DerivedCategory.IsMPseudoCoherent`,
  `isMPseudoCoherent_obj₃_of_distinguishedTriangle`,
  `ObjectProperty.IsTriangulated`;
- best owner abstraction: the reusable owner statement is that the object property
  `fun K : DMod ↦ K.IsPseudoCoherent` is triangulated; the three numbered textbook statements are
  its source-facing `obj₁`/`obj₂`/`obj₃` consequences;
- primitive vs. derived:
  primitive data are the absolute notions `DerivedCategory.IsMPseudoCoherent` and
  `DerivedCategory.IsPseudoCoherent` from Definition `15.65.1`;
  the distinguished-triangle closure of `m`-pseudo-coherence from Lemma `15.65.2` is derived API,
  and this file upgrades it to pseudo-coherence;
- source/core/bridge triage:
  `source-facing`: the three numbered two-out-of-three statements below;
  `core/canonical`: `ObjectProperty.IsTriangulated (fun K : DMod ↦ K.IsPseudoCoherent)`;
  `bridge/view`: deriving the three source-facing consequences from that owner theorem.
- layer: this file keeps the source-facing statements but factors them through the canonical
  triangulated-object-property owner. -/

-- Proof sketch: choose any representative cochain complex of `K` in the derived category. Lemma
-- `15.65.5` characterizes pseudo-coherence of that representative by `m`-pseudo-coherence for all
-- integers `m`, and transport across the chosen isomorphism shows that this depends only on the
-- derived object `K`.
/-- Companion bridge for Lemma 15.65.6: a derived `R`-complex is pseudo-coherent exactly when it
is `m`-pseudo-coherent for every integer `m`. -/
theorem isPseudoCoherent_iff_forall_isMPseudoCoherent (K : DMod) :
    K.IsPseudoCoherent ↔ ∀ m : ℤ, K.IsMPseudoCoherent m := by
  sorry

instance isPseudoCoherent_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (fun K : DMod ↦ K.IsPseudoCoherent) where
  of_iso e hK := by
    rw [isPseudoCoherent_iff_forall_isMPseudoCoherent] at hK ⊢
    intro m
    let P : ObjectProperty DMod := fun K ↦ K.IsMPseudoCoherent m
    exact P.prop_of_iso e (hK m)

-- Proof sketch: combine Lemma `15.65.5`, which upgrades pseudo-coherence to
-- `m`-pseudo-coherence in every degree, with Lemma `15.65.2`, which gives the corresponding
-- two-out-of-three property for distinguished triangles degreewise in `m`. The resulting object
-- property is closed under isomorphisms by the previous instance, and the zero/shift axioms are
-- handled directly from the definition.
/-- Canonical owner form of Lemma 15.65.6: pseudo-coherent objects of `D(R)` form a triangulated
object property. -/
instance isPseudoCoherent_isTriangulated :
    ObjectProperty.IsTriangulated (fun K : DMod ↦ K.IsPseudoCoherent) := by
  sorry

-- Proof sketch: this is the `obj₁`-`obj₂` to `obj₃` closure consequence of the triangulated
-- object property instance on pseudo-coherent objects.
/-- Lemma 15.65.6 (1): in a distinguished triangle in `D(R)`, if the first and second terms are
pseudo-coherent, then the third term is pseudo-coherent. -/
theorem isPseudoCoherent_obj₃_of_distinguishedTriangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : T.obj₁.IsPseudoCoherent) (h₂ : T.obj₂.IsPseudoCoherent) :
    T.obj₃.IsPseudoCoherent := by
  let P : ObjectProperty DMod := fun K ↦ K.IsPseudoCoherent
  exact P.ext_of_isTriangulatedClosed₃ T hT h₁ h₂

-- Proof sketch: this is the `obj₁`-`obj₃` to `obj₂` closure consequence of the triangulated
-- object property instance on pseudo-coherent objects.
/-- Lemma 15.65.6 (2): in a distinguished triangle in `D(R)`, if the first and third terms are
pseudo-coherent, then the second term is pseudo-coherent. -/
theorem isPseudoCoherent_obj₂_of_distinguishedTriangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : T.obj₁.IsPseudoCoherent) (h₃ : T.obj₃.IsPseudoCoherent) :
    T.obj₂.IsPseudoCoherent := by
  let P : ObjectProperty DMod := fun K ↦ K.IsPseudoCoherent
  exact P.ext_of_isTriangulatedClosed₂ T hT h₁ h₃

-- Proof sketch: this is the `obj₂`-`obj₃` to `obj₁` closure consequence of the triangulated
-- object property instance on pseudo-coherent objects.
/-- Lemma 15.65.6 (3): in a distinguished triangle in `D(R)`, if the second and third terms are
pseudo-coherent, then the first term is pseudo-coherent. -/
theorem isPseudoCoherent_obj₁_of_distinguishedTriangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₂ : T.obj₂.IsPseudoCoherent) (h₃ : T.obj₃.IsPseudoCoherent) :
    T.obj₁.IsPseudoCoherent := by
  let P : ObjectProperty DMod := fun K ↦ K.IsPseudoCoherent
  exact P.ext_of_isTriangulatedClosed₁ T hT h₂ h₃

end

end CategoryTheory
