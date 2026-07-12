import Mathlib.CategoryTheory.Abelian.Injective.Dimension
import Mathlib.CategoryTheory.Abelian.Injective.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open Limits

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

-- Domain-style sampling:
-- * primary domain: injective objects in an abelian category, detected through `Injective`,
--   `preadditiveYonedaObj`, `ShortComplex.ShortExact`, and `Ext`.
-- * inspected owner declarations:
--   `preservesFiniteColimits_preadditiveYonedaObj_of_injective`,
--   `injective_of_preservesFiniteColimits_preadditiveYonedaObj`,
--   `ShortComplex.ShortExact.splittingOfInjective`,
--   `injective_iff_subsingleton_ext_one`.
-- * layer: `source-facing`; the textbook item is genuinely a four-way equivalence, so the main
--   declaration should stay a local `List.TFAE` rather than collapsing to a bare owner `recall`.
-- * core/canonical owner abstraction: `Injective I`.
-- * primitive data: only the object `I`.
-- * derived API: exactness of `preadditiveYonedaObj I`, the split-mono formulation of short exact
--   sequences beginning at `I`, and vanishing of `Ext¹(-, I)`.
--
-- The short-exact-sequence clause is quantified directly over the owner object `ShortComplex C`,
-- with `S.X₁ = I` expressing that the sequence starts at `I`; its splitting is recorded through
-- the canonical Prop-level owner `IsSplitMono S.f` rather than a chosen `S.Splitting`.
--
-- Proof sketch: `(1) ↔ (2)` combines the canonical exactness predicate `exactFunctor` with
-- `exactFunctor_iff`, the finite-limit preservation of `preadditiveYonedaObj I`, and the injective
-- criterion `injective_of_preservesFiniteColimits_preadditiveYonedaObj`. From `(1)`, any short
-- exact sequence starting at `I` has split mono `f` via
-- `ShortComplex.ShortExact.splittingOfInjective`. Conversely, if every short exact sequence
-- starting at `I` has split mono `f`, then pushing out an arbitrary monomorphism along a map into
-- `I` yields a split monomorphism `I ⟶ pushout g f`, hence a retraction that exhibits the
-- extension property defining injectivity. The `Ext¹` clause is equivalent to injectivity via
-- `Ext.eq_zero_of_injective` and `injective_iff_subsingleton_ext_one`.
/-- Lemma 12.27.2: for an object `I` of an abelian category, the following are equivalent:
`I` is injective, the preadditive Yoneda functor `B ↦ Hom(B, I)` is exact, every short exact
sequence `0 ⟶ I ⟶ A ⟶ B ⟶ 0` splits, and every class in `Ext B I 1` vanishes. -/
theorem injective_tfae (I : C) :
    List.TFAE [
      Injective I,
      exactFunctor _ _ (preadditiveYonedaObj I),
      ∀ ⦃S : ShortComplex C⦄ (_ : S.X₁ = I) (_ : S.ShortExact), IsSplitMono S.f,
      ∀ ⦃B : C⦄ (e : Ext B I 1), e = 0
    ] := by
  tfae_have 1 ↔ 2 := by
    constructor
    · intro hI
      letI : Injective I := hI
      letI : PreservesFiniteColimits (preadditiveYonedaObj I) :=
        preservesFiniteColimits_preadditiveYonedaObj_of_injective I
      exact (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩
    · intro hExact
      letI : PreservesFiniteColimits (preadditiveYonedaObj I) :=
        (exactFunctor_iff (preadditiveYonedaObj I)).1 hExact |>.2
      exact injective_of_preservesFiniteColimits_preadditiveYonedaObj I
  tfae_have 1 → 3 := by
    intro hI S hX hS
    subst hX
    letI : Injective S.X₁ := hI
    exact (hS.splittingOfInjective).isSplitMono_f
  tfae_have 3 → 1 := by
    intro hsplit
    refine Injective.mk ?_
    intro X Y g f _
    let i : I ⟶ pushout g f := pushout.inl g f
    let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i) inferInstance inferInstance
    have hs : IsSplitMono i := by
      simpa [S, i] using hsplit rfl hS
    letI : IsSplitMono i := hs
    refine ⟨pushout.inr g f ≫ retraction i, ?_⟩
    calc
      f ≫ pushout.inr g f ≫ retraction i = g ≫ i ≫ retraction i := by
        simpa [i, Category.assoc] using congrArg (fun k ↦ k ≫ retraction i)
          (show g ≫ pushout.inl g f = f ≫ pushout.inr g f from pushout.condition).symm
      _ = g := by simp [i]
  tfae_have 1 → 4 := by
    intro hI B e
    letI : Injective I := hI
    exact e.eq_zero_of_injective
  tfae_have 4 → 1 := by
    intro hExt
    rw [injective_iff_subsingleton_ext_one]
    intro B
    exact (subsingleton_iff_forall_eq 0).2 fun e ↦ hExt e
  tfae_finish

/-- Companion projection of `injective_tfae`: an object is injective exactly when its
preadditive Yoneda functor is exact. -/
theorem injective_iff_exact_preadditiveYonedaObj (I : C) :
    Injective I ↔ exactFunctor _ _ (preadditiveYonedaObj I) :=
  (injective_tfae I).out 0 1

/-- Companion projection of `injective_tfae`: an object is injective exactly when every class in
`Ext¹(-, I)` vanishes. -/
theorem injective_iff_ext_one_eq_zero (I : C) :
    Injective I ↔ ∀ ⦃B : C⦄ (e : Ext B I 1), e = 0 :=
  (injective_tfae I).out 0 3

end CategoryTheory
