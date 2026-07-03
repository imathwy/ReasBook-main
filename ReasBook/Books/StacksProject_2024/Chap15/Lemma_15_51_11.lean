import Mathlib
import StacksProject_2024.Chap10.Definition_10_157_1
import StacksProject_2024.Chap10.Lemma_10_164_5
import StacksProject_2024.Chap15.Definition_15_41_1
import StacksProject_2024.Chap15.Lemma_15_51_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra
open IsLocalRing

universe u

/-
Domain sampling pass:
* primary domain: permanence properties of LinearRepresentations_Serre_1977's condition `(S_n)` for Noetherian rings under
  finitely generated field extensions and on fibers of ring maps;
* sampled owner declarations:
  - `Algebra.EssFiniteType` from Definition `9.6.6`, the canonical owner for finitely generated
    field extensions;
  - `SerreConditionS` from `Definition_10_157_1`, the canonical owner for the ring-theoretic
    condition `(S_n)`;
  - `cohenMacaulayRing_tensorProduct_of_fieldExtensions_of_finitelyGeneratedFieldExtension` from
    `Lemma_10_167_1`, the tensor-product fiber input behind the base-change step;
  - `serreConditionS_of_flat_of_fiber` from `Lemma_10_163_4`, the canonical ascent theorem along
    flat maps with fiberwise `(S_n)`;
  - `FieldAlgebraProperty.HasPropertiesABCDE` from `Lemma_15_51_10`, the chapter owner for the five
    formal-fiber axioms attached to a field-algebra property.

Source/core/bridge triage:
* `source-facing`: the tensor-product, localization, and fiberwise permanence statements in parts
  `(1)` through `(4)`;
* `core/canonical`: `SerreConditionS` together with `FieldAlgebraProperty.HasPropertiesABCDE`;
* `bridge/view`: the direct Chapter 15 field-algebra specialization `SerreConditionSProperty n`
  of the ring owner `SerreConditionS`, including the separable-ground-field clause `(5)` as
  property `(E)`.

Primitive data are only the owner property `SerreConditionS`; the chapter-level `(A)`--`(E)`
package is derived API and should reuse the existing owner class rather than a bespoke wrapper.
-/

section

variable {n : ℕ}

-- Proof sketch: the ring map `R → k' ⊗[k] R` is flat, and its fibers are Cohen-Macaulay by
-- Lemma `10.167.1` because they are tensor products of field extensions with one side
-- finitely generated over the base. Apply Lemma `10.163.4` to ascend LinearRepresentations_Serre_1977's condition `(S_n)`
-- along this flat base change.
/-- Lemma 15.51.11 (1): if `k → R` is a map from a field to a Noetherian ring, and
`k' / k` is a finitely generated field extension, then `R` having LinearRepresentations_Serre_1977's condition `(S_n)`
implies that `k' ⊗[k] R` also has LinearRepresentations_Serre_1977's condition `(S_n)`. -/
theorem serreConditionS_tensorProduct_of_finitelyGeneratedFieldExtension
    {k : Type u} {k' : Type u} {R : Type u}
    [Field k] [Field k'] [CommRing R] [Algebra k k'] [Algebra k R]
    [Algebra.EssFiniteType k k'] [SerreConditionS R n] :
    SerreConditionS (k' ⊗[k] R) n := sorry

-- Proof sketch: the forward implication is inherited by localizations of a ring satisfying
-- `(S_n)`. For the converse, a Noetherian ring has `(S_n)` exactly when each localization at a
-- prime does, which is the local formulation built into `SerreConditionS`.
/-- Lemma 15.51.11 (2): if `R` is Noetherian, then `R` has LinearRepresentations_Serre_1977's condition `(S_n)`
if and only if every localization `R_𝔭` has LinearRepresentations_Serre_1977's condition `(S_n)`. -/
theorem serreConditionS_iff_localizationAtPrime
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    SerreConditionS R n ↔
      ∀ p : PrimeSpectrum R, SerreConditionS (Localization.AtPrime p.asIdeal) n := sorry

-- Proof sketch: for each `p : Spec(A)`, base change the regular map `B → C` along
-- `A → κ(p)` to obtain a regular map on the fibers. Regular fibers are geometrically regular,
-- hence Cohen-Macaulay, so Lemma `10.163.4` ascends `(S_n)` from the fiber of `A → B` to the
-- fiber of `A → C`.
/-- Lemma 15.51.11 (3): if `A → B → C` are maps of commutative rings, `C` is Noetherian, the
fibers of `A → B` satisfy LinearRepresentations_Serre_1977's condition `(S_n)`, and `B → C` is a regular ring map, then the
fibers of `A → C` satisfy LinearRepresentations_Serre_1977's condition `(S_n)`. -/
theorem fiber_serreConditionS_of_regularRingMap
    {A : Type u} {B : Type u} {C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing C] [(algebraMap B C).IsRegularRingMap]
    (hfiber : ∀ p : PrimeSpectrum A, SerreConditionS (p.asIdeal.Fiber B) n) :
    ∀ p : PrimeSpectrum A, SerreConditionS (p.asIdeal.Fiber C) n := sorry

-- Proof sketch: for each `p : Spec(A)`, base change the faithfully flat map `B → C` along
-- `A → κ(p)` to obtain a faithfully flat map on fibers. Then apply Lemma `10.164.5` to descend
-- LinearRepresentations_Serre_1977's condition `(S_n)` from the fiber of `A → C` to the corresponding fiber of `A → B`.
/-- Lemma 15.51.11 (4): if `A → B → C` are maps of commutative rings, the fibers of `A → C`
satisfy LinearRepresentations_Serre_1977's condition `(S_n)`, and `B → C` is faithfully flat, then the fibers of `A → B`
satisfy LinearRepresentations_Serre_1977's condition `(S_n)`. -/
theorem fiber_serreConditionS_of_faithfullyFlat
    {A : Type u} {B : Type u} {C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hff : (algebraMap B C).FaithfullyFlat)
    (hfiber : ∀ p : PrimeSpectrum A, SerreConditionS (p.asIdeal.Fiber C) n) :
    ∀ p : PrimeSpectrum A, SerreConditionS (p.asIdeal.Fiber B) n := sorry

end

namespace Algebra

section

variable {n : ℕ}

/-- The canonical `FieldAlgebraProperty` bridge for LinearRepresentations_Serre_1977's condition `(S_n)`. -/
abbrev SerreConditionSProperty (n : ℕ) : FieldAlgebraProperty :=
  fun k A ↦ fun [Field k] [CommRing A] [Algebra k A] ↦ SerreConditionS A n

-- Proof sketch: `SerreConditionS A n` depends only on the underlying Noetherian ring `A`, so
-- changing the base field along a separable algebraic extension leaves the same ring property.
/-- Lemma 15.51.11 (5), owner-form: the Chapter 15 field-algebra property
`SerreConditionSProperty n` has property `(E)`, i.e. LinearRepresentations_Serre_1977's condition `(S_n)` is
unchanged under separable algebraic extension of the ground field. -/
theorem serreConditionS_hasPropertyE :
    (SerreConditionSProperty n).HasPropertyE := by
  refine { separableBaseChange := ?_ }
  intro k k' A _ _ _ _ _ _ _ _ hS
  exact hS

-- Proof sketch: the five source-facing parts of Lemma `15.51.11` already match the five fields of
-- the canonical chapter owner `FieldAlgebraProperty.HasPropertiesABCDE` for the property
-- `SerreConditionSProperty n`, so the instance reuses those owner theorems directly and only
-- spells out the closed-fiber faithfully flat descent step.
/-- Lemma 15.51.11 packages LinearRepresentations_Serre_1977's condition `(S_n)` into the canonical Chapter 15 owner for
field-algebra properties satisfying `(A)` through `(E)`. -/
instance serreConditionS_hasPropertiesABCDE :
    (SerreConditionSProperty n).HasPropertiesABCDE where
  baseChange := by
    intro k R K _ _ _ _ _ _ _ hR
    letI : SerreConditionS R n := hR
    exact serreConditionS_tensorProduct_of_finitelyGeneratedFieldExtension
  localizationCriterion := by
    intro k R _ _ _ _
    exact serreConditionS_iff_localizationAtPrime
  regularAscent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hfiber q
    exact fiber_serreConditionS_of_regularRingMap hfiber q
  closedFiberDescent := by
    intro A B C
    intro _ _ _ _ _ _ _
    intro _ _ _
    intro _ _ _
    intro _ _
    intro hBC hC
    letI : SerreConditionS ((maximalIdeal A).Fiber C) n := hC
    letI : Algebra B ((maximalIdeal A).Fiber B) := Algebra.TensorProduct.rightAlgebra
    let D := ((maximalIdeal A).Fiber B) ⊗[B] C
    letI : CommRing D := inferInstance
    letI : Algebra ((maximalIdeal A).Fiber B) D := Algebra.TensorProduct.leftAlgebra
    letI : Algebra C D := Algebra.TensorProduct.rightAlgebra
    letI : Module.FaithfullyFlat B C := RingHom.faithfullyFlat_algebraMap_iff.mp hBC
    let f : ((maximalIdeal A).Fiber B) →+* D := algebraMap ((maximalIdeal A).Fiber B) D
    have hf : f.FaithfullyFlat := by
      letI : Module.FaithfullyFlat ((maximalIdeal A).Fiber B) D := by infer_instance
      simpa [f] using (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance : f.FaithfullyFlat)
    let e : D ≃+* ((maximalIdeal A).Fiber C) :=
      (Algebra.IsPushout.cancelBaseChangeAlg A ((maximalIdeal A).ResidueField)
        B ((maximalIdeal A).Fiber B) C).toRingEquiv
    let g : D →+* ((maximalIdeal A).Fiber C) := e.toRingHom
    have hg : g.FaithfullyFlat := by
      simpa [g] using (RingHom.FaithfullyFlat.of_bijective e.bijective : g.FaithfullyFlat)
    have hfiber_ff : (g.comp f).FaithfullyFlat := by
      change (RingHom.comp g f).FaithfullyFlat
      exact RingHom.FaithfullyFlat.stableUnderComposition f g hf hg
    letI : Algebra ((maximalIdeal A).Fiber B) ((maximalIdeal A).Fiber C) := RingHom.toAlgebra (g.comp f)
    simpa [f, g] using
      (serreConditionS_of_faithfullyFlat
        (algebraMap ((maximalIdeal A).Fiber B) ((maximalIdeal A).Fiber C)) hfiber_ff :
          SerreConditionS ((maximalIdeal A).Fiber B) n)
  separableBaseChange := serreConditionS_hasPropertyE.separableBaseChange

end

end Algebra
