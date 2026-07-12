import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable (A : Type u) [Category.{v} A] [Abelian A]

/- Domain-style sampling for Definition 19.10.1:
- primary domain: Grothendieck-style axioms and generators in abelian categories;
- sampled owner declarations:
  `IsSeparator`,
  `HasSeparator`,
  `ObjectProperty.IsStrongGenerator`,
  `IsGrothendieckAbelian`;
- best owner abstractions: `IsSeparator U` for the object-level generator notion and
  `IsGrothendieckAbelian.{v} A` for the category-level Grothendieck condition; the strong-generator
  owner is relevant background for the subobject criterion, but the source-facing item here is a
  characterization of ordinary generators in an abelian category, so `IsSeparator` remains the
  main public owner;
- primitive data: the exactness axiom `AB5` together with existence of a separator;
- derived API: the Stacks-project subobject criterion for a generator and the source-facing
  reformulation of `IsGrothendieckAbelian.{v} A` as `AB5` plus such a generator.

Source/core/bridge triage:
- `source-facing`: the subobject formulation saying every proper subobject is missed by some map
  from a chosen object;
- `core/canonical`: `IsSeparator`, `HasSeparator`, and `IsGrothendieckAbelian.{v} A`;
- `bridge/view`: the equivalence theorem below relating `IsSeparator` to the Stacks subobject
  criterion, and the companion reformulation of `IsGrothendieckAbelian.{v} A`.

The previous version introduced duplicate local owners `IsGeneratingObject` and
`IsStrictGrothendieckAbelian`. This file now keeps the canonical owners and expresses the Stacks
formulations only as thin companion theorems. -/

/- Definition 19.10.1 (1): an abelian category has direct sums exactly when it has the canonical
coproduct structure `HasCoproducts A`. -/
recall HasCoproducts

/- Definition 19.10.1 (2): the condition “has AB3 and direct sums are exact” is the canonical
Grothendieck axiom `AB4 A`. -/
recall AB4

/- Definition 19.10.1 (3): the condition “has AB3 and filtered colimits are exact” is the
canonical Grothendieck axiom `AB5 A`. -/
recall AB5

/- Definition 19.10.1 (4): the dual condition that an abelian category has products is the
canonical limit structure `HasProducts A`. -/
recall HasProducts

/- Definition 19.10.1 (5): the dual condition “has AB3* and products are exact” is the canonical
Grothendieck axiom `AB4Star A`. -/
recall AB4Star

/- Definition 19.10.1 (6): the dual condition “has AB3* and cofiltered limits are exact” is the
canonical Grothendieck axiom `AB5Star A`. -/
recall AB5Star

/- Definition 19.10.1 (7): in an abelian category, the Stacks-project notion of a generator is
the canonical predicate `IsSeparator U`. -/
recall IsSeparator

-- Proof sketch: if `U` is a separator and every map `U ⟶ M` factors through a subobject `N`,
-- then the mono `N.arrow` is right-orthogonal to `U`, hence an isomorphism because separators are
-- detectors in abelian categories. Conversely, if every proper subobject is missed by some map
-- from `U`, then any nonzero morphism `f` has a proper kernel subobject, and a map missing that
-- kernel contradicts `h ≫ f = 0`.
/-- In an abelian category, an object is a separator exactly when every proper subobject is missed
by some map from it. -/
theorem isSeparator_iff_exists_not_factors_subobject (U : A) :
    IsSeparator U ↔
      ∀ ⦃M : A⦄ (N : Subobject M), N ≠ ⊤ → ∃ f : U ⟶ M, ¬ N.Factors f := by
  refine ⟨?_, ?_⟩
  · intro hU M N hN
    by_contra h
    have hN' : ∀ f : U ⟶ M, N.Factors f := by
      intro f
      by_contra hf
      exact h ⟨f, hf⟩
    have hIso : IsIso N.arrow := hU.isDetector.def N.arrow fun f ↦ by
      refine ⟨N.factorThru f (hN' f), by simp, ?_⟩
      intro g hg
      exact (cancel_mono N.arrow).1 (by simp [hg])
    exact hN ((Subobject.isIso_arrow_iff_eq_top N).mp hIso)
  · intro hU
    rw [Preadditive.isSeparator_iff]
    intro X Y f hf
    by_contra hf'
    have hkernel : kernelSubobject f ≠ ⊤ := by
      intro htop
      have hcomp : (kernelSubobject f).arrow ≫ f = 0 := kernelSubobject_arrow_comp f
      have hIso : IsIso (kernelSubobject f).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 htop
      have hcancel : inv (kernelSubobject f).arrow ≫ ((kernelSubobject f).arrow ≫ f) = f := by
        simpa [Category.assoc] using IsIso.inv_hom_id_assoc (kernelSubobject f).arrow f
      exact hf' <| by
        rw [← hcancel]
        simp [hcomp]
    obtain ⟨g, hg⟩ := hU (kernelSubobject f) hkernel
    exact hg (kernelSubobject_factors f g (hf g))

/- Definition 19.10.1 (8): the Grothendieck-abelian condition is the canonical owner
`IsGrothendieckAbelian.{v} A`. -/
recall IsGrothendieckAbelian

/-- In the strict Stacks sense, a Grothendieck abelian category is exactly an abelian category
with `AB5` and an object satisfying the subobject criterion for a generator. -/
theorem isGrothendieckAbelian_iff_ab5_and_exists_generator [HasFilteredColimits A] :
    IsGrothendieckAbelian.{v} A ↔
      AB5 A ∧
        ∃ U : A, ∀ ⦃M : A⦄ (N : Subobject M), N ≠ ⊤ → ∃ f : U ⟶ M, ¬ N.Factors f := by
  refine ⟨?_, ?_⟩
  · intro
    refine ⟨inferInstance, ⟨separator A, ?_⟩⟩
    exact (isSeparator_iff_exists_not_factors_subobject A (separator A)).mp
      (isSeparator_separator A)
  · rintro ⟨_, U, hU⟩
    have hSep : IsSeparator U := (isSeparator_iff_exists_not_factors_subobject A U).mpr hU
    letI : HasSeparator A := ⟨⟨U, hSep⟩⟩
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end CategoryTheory
