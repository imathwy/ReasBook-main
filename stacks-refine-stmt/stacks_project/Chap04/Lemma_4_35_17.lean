import Mathlib
import stacks_project.Chap04.Lemma_4_35_16

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v uX uX' uX'' uY

namespace CategoryTheory

open BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{v, uX} C}
variable {X' : BasedCategory.{v, uX'} C}
variable {X'' : BasedCategory.{v, uX''} C}
variable {Y : BasedCategory.{v, uY} C}

/- Domain-style sampling for Lemma 4.35.17:
- primary domain: factorizations in `Cat/C` through categories fibred in groupoids over a fixed
  target, compared up to equivalence over the base and over the target;
- sampled owner-level declarations:
  `BasedCategory.ofFunctor`,
  `BasedFunctor.IsEquivalenceOverBase`,
  `BasedFunctor.hom_isEquivalenceOverBase`,
  `fibredInGroupoidsFactorizationFromSource`;
- best owner abstraction: the main comparison data lives on based functors and their owner
  predicate `IsEquivalenceOverBase`; Lemma `4.35.16` already supplies the canonical explicit
  factorization model, so this file should add only the source-facing comparison theorems and the
  minimal target-over-target bridge helpers they need.

Primitive-vs-derived split:
- primitive data: the two factorizations `a ⋙ f` and `b ⋙ g` of `F`;
- derived API: the comparison equivalence over `Y`, its forgotten comparison over `C`, and in the
  strict case the induced `2`-isomorphism in `Cat/Y`.

Source/core/bridge triage:
- `source-facing`: the two comparison theorems in this file;
- `core/canonical`: `BasedFunctor.IsEquivalenceOverBase` and the explicit factorization owner from
  Lemma `4.35.16`;
- `bridge/view`: the thin helpers `forgetTarget` and `overTargetOfCompEq`, which only re-express the
  same functors at the target-over-target level needed by the theorem statements. -/

namespace BasedFunctor

variable {F : X ⥤ᵇ Y} {f : X' ⥤ᵇ Y} {g : X'' ⥤ᵇ Y}

/-- A morphism in `Cat/Y` canonically forgets to a morphism in `Cat/C`. -/
abbrev forgetTarget
    (h : BasedCategory.ofFunctor g.toFunctor ⥤ᵇ BasedCategory.ofFunctor f.toFunctor) :
    X'' ⥤ᵇ X' :=
  { toFunctor := h.toFunctor
    w := by
      calc
        h.toFunctor ⋙ X'.p = h.toFunctor ⋙ (f.toFunctor ⋙ Y.p) := by
          simpa [Functor.assoc] using congrArg (Functor.comp h.toFunctor) f.w.symm
        _ = (h.toFunctor ⋙ f.toFunctor) ⋙ Y.p := by rw [Functor.assoc]
        _ = g.toFunctor ⋙ Y.p := by
          simpa [Functor.assoc] using
            congrArg (fun q : X''.obj ⥤ Y.obj ↦ q ⋙ Y.p) h.w
        _ = X''.p := g.w }

/-- A strict factorization `a ⋙ f = F` is the same data as a morphism in `Cat/Y`. -/
abbrev overTargetOfCompEq
    (a : X ⥤ᵇ X') (ha : a ⋙ f = F) :
    BasedCategory.ofFunctor F.toFunctor ⥤ᵇ BasedCategory.ofFunctor f.toFunctor :=
  { toFunctor := a.toFunctor
    w := congrArg toFunctor ha }

end BasedFunctor

section

variable (F : X ⥤ᵇ Y)
variable (a : X ⥤ᵇ X') (f : X' ⥤ᵇ Y)
variable (b : X ⥤ᵇ X'') (g : X'' ⥤ᵇ Y)

variable [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p]
variable [IsFibredInGroupoids f.toFunctor] [IsFibredInGroupoids g.toFunctor]

-- Proof sketch: both `X'` and `X''` are equivalent over `Y` to the explicit `2`-fibre-product
-- factorization of `F` from Lemma `4.35.16`; compose one equivalence with a quasi-inverse to the
-- other and compare the resulting composite with `a` using the given `2`-commutative triangles.
/-- Lemma 4.35.17: if `F : X ⥤ᵇ Y` admits two factorizations through categories fibred in
groupoids over `Y`, and the comparison functors `a : X ⥤ᵇ X'` and `b : X ⥤ᵇ X''` are equivalences
over `C`, then there is an equivalence of categories over `Y` from `g` to `f` whose underlying
functor over `C` makes `b ⋙ h` `2`-isomorphic to `a`. -/
theorem exists_equivalence_over_target_between_fibred_groupoid_factorizations
    (ha_equiv : a.IsEquivalenceOverBase)
    (hb_equiv : b.IsEquivalenceOverBase)
    (ha_comm : Nonempty (a ⋙ f ≅ F))
    (hb_comm : Nonempty (b ⋙ g ≅ F)) :
    ∃ h : BasedCategory.ofFunctor g.toFunctor ⥤ᵇ BasedCategory.ofFunctor f.toFunctor,
      h.IsEquivalenceOverBase ∧
        Nonempty (BasedFunctor.comp b (forgetTarget h) ≅ a) := sorry

-- Proof sketch: in the strict case the same construction as in the main theorem gives `h`. Since
-- both triangles commute on the nose, the comparison isomorphism between `b ⋙ h` and `a` is
-- vertical already over `Y`, not just after projecting further to `C`.
/-- Under strict commutativity of the two triangles, the comparison `2`-isomorphism `b ⋙ h ≅ a`
can be chosen in `Cat/Y`. -/
theorem exists_equivalence_over_target_between_fibred_groupoid_factorizations_of_strict_comm
    (ha_equiv : a.IsEquivalenceOverBase)
    (hb_equiv : b.IsEquivalenceOverBase)
    (ha_strict : a ⋙ f = F)
    (hb_strict : b ⋙ g = F) :
    ∃ h : BasedCategory.ofFunctor g.toFunctor ⥤ᵇ BasedCategory.ofFunctor f.toFunctor,
      h.IsEquivalenceOverBase ∧
        Nonempty (BasedFunctor.comp b (forgetTarget h) ≅ a) ∧
          Nonempty
            (BasedFunctor.comp (overTargetOfCompEq b hb_strict) h ≅
              overTargetOfCompEq a ha_strict) := sorry

end

end CategoryTheory
