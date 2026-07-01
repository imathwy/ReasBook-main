import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Abelian.Projective.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open CategoryTheory.Limits

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

-- Domain-style sampling:
-- * primary domain: projective objects in an abelian category, detected through `Projective`,
--   `preadditiveCoyonedaObj`, `ShortComplex.ShortExact`, and `Ext`.
-- * inspected owner declarations:
--   `preservesFiniteColimits_preadditiveCoyonedaObj_of_projective`,
--   `projective_of_preservesFiniteColimits_preadditiveCoyonedaObj`,
--   `ShortComplex.ShortExact.splittingOfProjective`,
--   `projective_iff_subsingleton_ext_one`.
-- * layer: `source-facing`; the textbook item is genuinely a four-way equivalence, so the main
--   declaration should stay a local `List.TFAE` rather than collapsing to a bare owner `recall`.
-- * core/canonical owner abstraction: `Projective P`.
-- * primitive data: only the object `P`.
-- * derived API: exactness of `preadditiveCoyonedaObj P`, splitting of short exact sequences
--   ending in `P`, and vanishing of `Ext¹(P, -)`.
-- * the exactness criterion is a `core/canonical` bridge living already in the `[Abelian C]`
--   context, while the full four-way TFAE and the `Ext¹` companion are `source-facing` items
--   that genuinely require `[HasExt C]`.
--
-- The short-exact-sequence clause is quantified directly over the owner object `ShortComplex C`,
-- with `S.X₃ = P` expressing that the sequence ends at `P`; its splitting is recorded through
-- the canonical Prop-level owner `IsSplitEpi S.g` rather than a chosen `S.Splitting`.
--
-- Proof sketch: `(1) ↔ (2)` combines the canonical exactness predicate `exactFunctor` with
-- `exactFunctor_iff`, the finite-limit preservation of `preadditiveCoyonedaObj P`, and the
-- projective criterion `projective_of_preservesFiniteColimits_preadditiveCoyonedaObj`. From `(1)`,
-- any short exact sequence ending in `P` has split epimorphism `g` via
-- `ShortComplex.ShortExact.splittingOfProjective`. Conversely, if every short exact sequence
-- ending in `P` has split epimorphism `g`, then pulling back an arbitrary epimorphism along a map
-- out of `P` yields a split epimorphism onto `P`, so `P` satisfies the lifting property that
-- defines projectivity. The `Ext¹` clause is equivalent to projectivity via
-- `Ext.eq_zero_of_projective` and `projective_iff_subsingleton_ext_one`.
/-- An object is projective exactly when its preadditive co-Yoneda functor is exact. This is the
`(1) ↔ (2)` part of Lemma 12.28.2, stated in the weaker ambient `[Abelian C]` context where no
`Ext`-hypothesis is needed. -/
theorem projective_iff_exact_preadditiveCoyonedaObj (P : C) :
    Projective P ↔ exactFunctor _ _ (preadditiveCoyonedaObj P) := by
  constructor
  · intro hP
    letI : Projective P := hP
    letI : PreservesFiniteColimits (preadditiveCoyonedaObj P) :=
      preservesFiniteColimits_preadditiveCoyonedaObj_of_projective P
    exact (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩
  · intro hExact
    letI : PreservesFiniteColimits (preadditiveCoyonedaObj P) :=
      (exactFunctor_iff (preadditiveCoyonedaObj P)).1 hExact |>.2
    exact projective_of_preservesFiniteColimits_preadditiveCoyonedaObj P

section

variable [HasExt.{w} C]

/-- Lemma 12.28.2: for an object `P` of an abelian category, the following are equivalent:
`P` is projective, the preadditive co-Yoneda functor `B ↦ Hom(P, B)` is exact, every short exact
sequence `0 ⟶ A ⟶ B ⟶ P ⟶ 0` splits, and every class in `Ext P A 1` vanishes. -/
theorem projective_tfae (P : C) :
    List.TFAE [
      Projective P,
      exactFunctor _ _ (preadditiveCoyonedaObj P),
      ∀ ⦃S : ShortComplex C⦄ (_ : S.X₃ = P) (_ : S.ShortExact), IsSplitEpi S.g,
      ∀ ⦃A : C⦄ (e : Ext P A 1), e = 0
    ] := by
  tfae_have 1 ↔ 2 := by
    simpa using projective_iff_exact_preadditiveCoyonedaObj P
  tfae_have 1 → 3 := by
    intro hP S hX hS
    subst hX
    letI : Projective S.X₃ := hP
    exact (hS.splittingOfProjective).isSplitEpi_g
  tfae_have 3 → 1 := by
    intro hsplit
    refine Projective.mk (fun {E X} f e _ ↦ ?_)
    let q : pullback e f ⟶ P := pullback.snd e f
    let S := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
    have hS : S.ShortExact := by
      refine { exact := ShortComplex.exact_kernel q }
    letI : IsSplitEpi q := by simpa [S, q] using hsplit rfl hS
    refine ⟨section_ q ≫ pullback.fst e f, ?_⟩
    rw [Category.assoc, pullback.condition]
    change section_ q ≫ q ≫ f = f
    simp
  tfae_have 1 → 4 := by
    intro hP A e
    letI : Projective P := hP
    exact e.eq_zero_of_projective
  tfae_have 4 → 1 := by
    intro hExt
    exact projective_iff_subsingleton_ext_one.2 fun _ ↦
      (subsingleton_iff_forall_eq 0).2 fun e ↦ hExt e
  tfae_finish

/-- Companion projection of `projective_tfae`: an object is projective exactly when every class in
`Ext¹(P, -)` vanishes. -/
theorem projective_iff_ext_one_eq_zero (P : C) :
    Projective P ↔ ∀ ⦃A : C⦄ (e : Ext P A 1), e = 0 :=
  (projective_tfae P).out 0 3

end

end CategoryTheory
