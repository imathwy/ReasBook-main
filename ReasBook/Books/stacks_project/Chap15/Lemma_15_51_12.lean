import Mathlib
import stacks_project.Chap10.Definition_10_104_6
import stacks_project.Chap15.Lemma_15_51_10
import stacks_project.Chap15.Lemma_15_51_11

-- Declarations for this item will be appended below by the statement pipeline.

namespace Algebra

universe u

open IsLocalRing
open scoped TensorProduct

section

/-
Domain sampling pass:
* primary domain: Chapter 15 formal-fiber axioms for field-algebra properties, specialized to the
  Cohen-Macaulay ring property from Chapter 10;
* sampled owner declarations:
  - `CohenMacaulayRing` from `Definition_10_104_6`, the source-facing ring owner;
  - `cohenMacaulayRing_tensorProduct_of_finitelyGeneratedFieldExtension` from `Lemma_10_167_1`,
    the canonical one-sided tensor-product theorem for finitely generated field extensions;
  - `SerreConditionSProperty` from `Lemma_15_51_11`, the chapter owner for the fiberwise
    `(S_n)` formal-fiber axioms;
  - `FieldAlgebraProperty.HasPropertiesABCDE` from `Lemma_15_51_10`, the chapter owner for the five
    formal-fiber axioms.

Source/core/bridge triage:
* `source-facing`: the ring property `CohenMacaulayRing`;
* `core/canonical`: the Chapter 15 owner `FieldAlgebraProperty.HasPropertiesABCDE`;
* `bridge/view`: the already-packaged chapter owner `SerreConditionSProperty n`, used internally to
  recover the `(C)` and `(D)` clauses for `CohenMacaulayRing` via the characterization by all
  Serre conditions.

Primitive data are only the canonical owner `CohenMacaulayRing`. The chapter package `(A)` through
`(E)` is derived API, so the owner-form declarations below should use the canonical predicate
directly rather than a one-file alias.
-/
-- Proof sketch: `CohenMacaulayRing A` depends only on the underlying Noetherian ring `A`, so
-- changing the base field along a separable algebraic extension does not alter the property.
/-- Lemma 15.51.12 (5), owner-form: Cohen-Macaulayness has property `(E)` in the Chapter 15
formal-fiber package, i.e. it is unchanged by replacing the ground field with a separable
algebraic extension. -/
theorem cohenMacaulay_hasPropertyE :
    FieldAlgebraProperty.HasPropertyE
      (fun k A ↦ fun [Field k] [CommRing A] [Algebra k A] ↦ CohenMacaulayRing A) := by
  refine ⟨?_⟩
  intro k k' A _ _ _ _ _ _ _ _ hCM
  exact hCM

-- Proof sketch: property `(A)` is the canonical tensor-product theorem from Lemma `10.167.1`.
-- Property `(B)` is reconstructed from the owner theorem
-- `serreConditionS_iff_localizationAtPrime`. Properties `(C)` and `(D)` are recovered from the
-- already-packaged Chapter 15 owner `SerreConditionSProperty n` for each `n`, then reassembled by
-- the canonical characterization `CohenMacaulayRing.of_serreConditionS`. Property `(E)` is the
-- base-field independence theorem above.
/-- Lemma 15.51.12 packages Cohen-Macaulayness into the canonical Chapter 15 owner for
field-algebra properties satisfying the formal-fiber axioms `(A)` through `(E)`. -/
instance cohenMacaulay_hasPropertiesABCDE :
    FieldAlgebraProperty.HasPropertiesABCDE
      (fun k A ↦ fun [Field k] [CommRing A] [Algebra k A] ↦ CohenMacaulayRing A) where
  baseChange := by
    intro k A K _ _ _ _ _ _ _ hA
    letI : CohenMacaulayRing A := hA
    let T := TensorProduct k K A
    let _ : SerreConditionS A 0 := CohenMacaulayRing.serreConditionS A 0
    let _ : SerreConditionS T 0 := serreConditionS_tensorProduct_of_finitelyGeneratedFieldExtension
    exact CohenMacaulayRing.of_serreConditionS T fun n ↦
      let _ : SerreConditionS A n := CohenMacaulayRing.serreConditionS A n
      (serreConditionS_tensorProduct_of_finitelyGeneratedFieldExtension : SerreConditionS T n)
  localizationCriterion := by
    intro k A _ _ _ _
    constructor
    · intro hA p
      letI : CohenMacaulayRing A := hA
      let _ :
          Module.CohenMacaulay (Localization.AtPrime p.asIdeal)
            (Localization.AtPrime p.asIdeal) :=
        localizedRing_cohenMacaulay A p
      exact
        { toIsNoetherian := inferInstance
          toLocallyCohenMacaulay := inferInstance }
    · intro hA
      refine CohenMacaulayRing.of_serreConditionS A fun n ↦ ?_
      have hSerre :
          SerreConditionS A n ↔
            ∀ p : PrimeSpectrum A, SerreConditionS (Localization.AtPrime p.asIdeal) n :=
        serreConditionS_iff_localizationAtPrime
      exact hSerre.2 fun p ↦ by
        letI : CohenMacaulayRing (Localization.AtPrime p.asIdeal) := hA p
        exact CohenMacaulayRing.serreConditionS (Localization.AtPrime p.asIdeal) n
  regularAscent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hfiber p
    let T := TensorProduct A C p.asIdeal.ResidueField
    let _ : Algebra.EssFiniteType C T := inferInstance
    let _ : IsNoetherianRing T := Algebra.EssFiniteType.isNoetherianRing C T
    let _ : IsNoetherianRing (p.asIdeal.Fiber C) :=
      isNoetherianRing_of_ringEquiv T
        (Algebra.TensorProduct.comm A p.asIdeal.ResidueField C).toRingEquiv.symm
    refine CohenMacaulayRing.of_serreConditionS (p.asIdeal.Fiber C) fun n ↦ ?_
    have hSerre :
        ∀ q : PrimeSpectrum A, SerreConditionS (q.asIdeal.Fiber C) n :=
      fiber_serreConditionS_of_regularRingMap fun q ↦ by
        letI : CohenMacaulayRing (q.asIdeal.Fiber B) := hfiber q
        exact CohenMacaulayRing.serreConditionS (q.asIdeal.Fiber B) n
    exact hSerre p
  closedFiberDescent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hBC hC
    let T := TensorProduct A B (maximalIdeal A).ResidueField
    let _ : Algebra.EssFiniteType B T := inferInstance
    let _ : IsNoetherianRing T := Algebra.EssFiniteType.isNoetherianRing B T
    let _ : IsNoetherianRing ((maximalIdeal A).Fiber B) :=
      isNoetherianRing_of_ringEquiv T
        (Algebra.TensorProduct.comm A (maximalIdeal A).ResidueField B).toRingEquiv.symm
    refine CohenMacaulayRing.of_serreConditionS ((maximalIdeal A).Fiber B) fun n ↦ ?_
    have hCSerre : SerreConditionS ((maximalIdeal A).Fiber C) n := by
      letI : CohenMacaulayRing ((maximalIdeal A).Fiber C) := hC
      exact CohenMacaulayRing.serreConditionS ((maximalIdeal A).Fiber C) n
    exact
      ((inferInstance : (SerreConditionSProperty n).HasPropertyD).closedFiberDescent
        A B C hBC hCSerre)
  separableBaseChange := by
    simpa using
      cohenMacaulay_hasPropertyE.separableBaseChange

end

end Algebra
