import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

open Abelian
open CategoryTheory.Abelian.Ext

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

/-- Helper for Lemma 13.27.8: if every degree-zero `Ext` group into `A` is subsingleton, then
every `Ext` class into `A` is zero. -/
private theorem ext_eq_zero_of_ext0_subsingleton
    (A : C) (hExt : ∀ B : C, Subsingleton (Ext B A 0))
    {B : C} {i : ℕ} (e : Ext B A i) : e = 0 := by
  -- The degree-zero identity class on `A` is already zero under the subsingleton hypothesis.
  have hId : (Ext.mk₀ (𝟙 A) : Ext A A 0) = 0 := by
    exact Subsingleton.elim _ _
  -- Reinsert the degree-zero identity on the right and then replace it by zero.
  calc
    e = e.comp (Ext.mk₀ (𝟙 A)) (Nat.add_zero i) := by
      simpa using (Ext.comp_mk₀_id e).symm
    _ = e.comp 0 (Nat.add_zero i) := by
      rw [hId]
    _ = 0 := by
      simpa using Ext.comp_zero e A 0 i (Nat.add_zero i)

/-- Helper for Lemma 13.27.8: vanishing of all degree-one `Ext` groups into `A` makes `A`
injective. -/
private theorem injective_of_ext1_subsingleton
    (A : C) (hExt : ∀ B : C, Subsingleton (Ext B A 1)) :
    Injective A :=
  (injective_iff_subsingleton_ext_one).2 (fun {B} ↦ hExt B)

/-- Helper for Lemma 13.27.8: if the requested cut degree already equals the full `Ext` degree,
the factorization is given by the degree-zero identity class on the source. -/
private theorem ext_factor_through_same_degree
    {A B : C} (p : ℕ) (e : Ext B A p) :
    ∃ (D : C) (α : Ext B D 0) (β : Ext D A p),
      α.comp β (Nat.zero_add p) = e := by
  -- Use the degree-zero identity class on the source as the left factor.
  refine ⟨B, Ext.mk₀ (𝟙 B), e, ?_⟩
  simpa using (Ext.mk₀_id_comp e)

/-- Helper for Lemma 13.27.8: any higher `Ext` class into a fixed target factors through a
degree-`p` class into that same target. -/
private theorem ext_factor_through_right_tail
    {A B : C} (p i : ℕ) (hp : p ≤ i) (e : Ext B A i) :
    ∃ (D : C) (α : Ext B D (i - p)) (β : Ext D A p),
      α.comp β (Nat.sub_add_cancel hp) = e := by
  -- Route correction: the source proof factors `e` by representing it with a Yoneda extension and
  -- cutting the exact chain at degree `p`. The owner-level Yoneda recursion bridge needed for that
  -- cut is still missing from the dependency-closed public API.
  -- TODO: use `YonedaExtension.toExt_surjective`, then cut the representative chain after the first
  -- `i - p` arrows and identify the resulting Yoneda product with `e`.
  sorry

/-- Helper for Lemma 13.27.8: once an `Ext` class factors through degree `p` into `A`, the
degree-`p` vanishing hypothesis kills it. -/
private theorem ext_eq_zero_of_factorization_through_degree
    (A : C) (p i : ℕ) (hExt : ∀ B : C, Subsingleton (Ext B A p))
    {B D : C} (α : Ext B D (i - p)) (β : Ext D A p)
    (hcomp : (i - p) + p = i) :
    α.comp β hcomp = 0 := by
  -- The fixed-target degree-`p` hypothesis makes the right factor trivial.
  have hβ : β = 0 := Subsingleton.elim _ _
  rw [hβ]
  -- The Yoneda product with the zero right factor is zero.
  simpa using Ext.comp_zero α A p (i - p) hcomp

-- Proof sketch: keep the low-degree branches owner-level, and reduce the higher-degree branch to
-- the fixed-target right-tail factorization supplied by `ext_factor_through_right_tail`.
/-- Companion bridge: if the degree-`p` `Ext` groups into `A` vanish for every source object,
then `A` has injective dimension `< p`. -/
theorem of_ext_vanishing
    (A : C) (p : ℕ) (hExt : ∀ B : C, Subsingleton (Ext B A p)) :
    HasInjectiveDimensionLT A p := by
  cases p with
  | zero =>
      -- Degree-zero vanishing makes every `Ext` class into `A` trivial, so the owner condition
      -- holds directly at all degrees.
      refine HasInjectiveDimensionLT.mk ?_
      intro i hi B e
      exact ext_eq_zero_of_ext0_subsingleton A hExt e
  | succ p =>
      cases p with
      | zero =>
          -- Degree-one vanishing is the owner-level criterion for injectivity.
          let hA : Injective A := injective_of_ext1_subsingleton A hExt
          exact (injective_iff_hasInjectiveDimensionLT_one).1 hA
      | succ p =>
          -- Route correction: the injective-presentation shift route needs `[EnoughInjectives C]`,
          -- which is not available here. The fixed-target proof therefore reduces to the source-
          -- faithful right-tail Yoneda factorization packaged in the helper below.
          refine HasInjectiveDimensionLT.mk ?_
          intro i hi B e
          -- Cut the representing class at the fixed target `A`, so the right factor has degree
          -- `p + 2` and is killed directly by `hExt`.
          obtain ⟨D, α, β, rfl⟩ :=
            ext_factor_through_right_tail (A := A) (B := B) (p := p + 2) (i := i) hi e
          exact ext_eq_zero_of_factorization_through_degree A (p + 2) i hExt α β
            (Nat.sub_add_cancel hi)

end HasInjectiveDimensionLT

/-- Lemma 13.27.8: if the degree-`p` Ext groups in an abelian category vanish for every pair of
objects, then every object has injective dimension `< p`. -/
theorem hasInjectiveDimensionLT_of_uniform_vanishing
    (p : ℕ) (hExt : ∀ A B : C, Subsingleton (Ext B A p)) (A : C) :
    HasInjectiveDimensionLT A p :=
  HasInjectiveDimensionLT.of_ext_vanishing A p (hExt A)

end CategoryTheory
