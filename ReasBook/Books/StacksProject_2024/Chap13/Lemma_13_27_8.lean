import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

open Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/- Domain-style sampling for Lemma 13.27.8:
- primary domain: injective-dimension bounds in an abelian category, expressed through vanishing of
  higher `Ext` groups;
- sampled owner declarations:
  `CategoryTheory.HasInjectiveDimensionLT`,
  `CategoryTheory.HasInjectiveDimensionLT.mk`,
  `CategoryTheory.HasInjectiveDimensionLT.subsingleton`,
  `CategoryTheory.hasInjectiveDimensionLT_of_enoughProjectives`;
- best owner abstraction: `HasInjectiveDimensionLT A p` is the canonical owner for the statement
  that all `Ext B A i` vanish for `i ≥ p`; the long exact sequence operators and
  `YonedaExtension.toExt` remain proof infrastructure rather than public API;
- primitive data: the degree `p` and the uniform degree-`p` vanishing hypothesis
  `hExt : ∀ A B, Subsingleton (Ext B A p)`;
- derived API: objectwise injective-dimension bounds, together with the fixed-target owner bridge
  `HasInjectiveDimensionLT.of_ext_vanishing`.

Source/core/bridge triage:
- `source-facing`: uniform higher-degree `Ext`-vanishing from vanishing in degree `p`;
- `core/canonical`: `HasInjectiveDimensionLT A p`;
- `bridge/view`: the fixed-target vanishing hypothesis `∀ B, Subsingleton (Ext B A p)` and the
  Yoneda/long-exact-sequence proof infrastructure that turns it into `HasInjectiveDimensionLT A p`.
-/

namespace HasInjectiveDimensionLT

-- Proof sketch: represent any class in `Ext B A i` for `i > p` by a Yoneda extension using
-- Lemma 13.27.5, split that extension at degree `p`, and factor the class through an element of
-- `Ext B C p`, which is zero by the hypothesis.
/-- Companion bridge: if the degree-`p` `Ext` groups into `A` vanish for every source object,
then `A` has injective dimension `< p`. -/
theorem of_ext_vanishing
    (A : C) (p : ℕ) (hExt : ∀ B : C, Subsingleton (Ext B A p)) :
    HasInjectiveDimensionLT A p := by
  sorry

end HasInjectiveDimensionLT

/-- Lemma 13.27.8: if the degree-`p` Ext groups in an abelian category vanish for every pair of
objects, then every object has injective dimension `< p`. -/
theorem hasInjectiveDimensionLT_of_uniform_vanishing
    (p : ℕ) (hExt : ∀ A B : C, Subsingleton (Ext B A p)) (A : C) :
    HasInjectiveDimensionLT A p :=
  HasInjectiveDimensionLT.of_ext_vanishing A p (hExt A)

end CategoryTheory
