import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_157_1
import stacks_proof.stacks_project.Chap10.Lemma_10_39_10
import stacks_proof.stacks_project.Chap10.Lemma_10_31_8
import stacks_proof.stacks_project.Chap10.Lemma_10_112_8
import stacks_proof.stacks_project.Chap10.Lemma_10_130_3
import stacks_proof.stacks_project.Chap10.Lemma_10_163_4
import stacks_proof.stacks_project.Chap10.Lemma_10_163_2
import stacks_proof.stacks_project.Chap10.Lemma_10_164_4
import stacks_proof.stacks_project.Chap10.Lemma_10_164_5
import stacks_proof.stacks_project.Chap10.Lemma_10_166_1
import stacks_proof.stacks_project.Chap10.Lemma_10_166_3
import stacks_proof.stacks_project.Chap10.Lemma_10_167_1
import stacks_proof.stacks_project.Chap15.Definition_15_41_1
import stacks_proof.stacks_project.Chap15.Lemma_15_41_3_Regular_maps_and_base_change

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra
open IsLocalRing

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

/-
Domain sampling pass:
* primary domain: permanence properties of Serre's condition `(S_n)` for Noetherian rings under
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

/-- Helper for Lemma 15.51.11: a field-algebra property assigns a proposition to each algebra over
a field. -/
abbrev FieldAlgebraProperty : Type (u + 1) :=
  ∀ (k A : Type u), [Field k] → [CommRing A] → [Algebra k A] → Prop

namespace FieldAlgebraProperty

/-- Helper for Lemma 15.51.11: property `(A)` is stability under finitely generated base change of
the ground field. -/
class HasPropertyA (P : FieldAlgebraProperty) : Prop where
  /-- Base change along a finitely generated field extension preserves `P`. -/
  baseChange (k A K : Type u) [Field k] [CommRing A] [Algebra k A] [IsNoetherianRing A]
      [Field K] [Algebra k K] [Algebra.EssFiniteType k K] (hA : P k A) :
      P K (K ⊗[k] A)

/-- Helper for Lemma 15.51.11: property `(B)` is the localization criterion over a fixed ground
field. -/
class HasPropertyB (P : FieldAlgebraProperty) : Prop where
  /-- The prime-local criterion for `P`. -/
  localizationCriterion (k A : Type u) [Field k] [CommRing A] [Algebra k A]
      [IsNoetherianRing A] :
      P k A ↔ ∀ p : PrimeSpectrum A, P k (Localization.AtPrime p.asIdeal)

/-- Helper for Lemma 15.51.11: property `(C)` is ascent on fibers along regular morphisms. -/
class HasPropertyC (P : FieldAlgebraProperty) : Prop where
  /-- Property `(C)` ascends from fibers of `A → B` to fibers of `A → C`. -/
  regularAscent (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [(algebraMap B C).IsRegularRingMap]
      (hB : ∀ q : PrimeSpectrum A, P q.asIdeal.ResidueField (q.asIdeal.Fiber B))
      (q : PrimeSpectrum A) :
      P q.asIdeal.ResidueField (q.asIdeal.Fiber C)

/-- Helper for Lemma 15.51.11: property `(D)` is faithfully flat descent on closed fibers of
local rings. -/
class HasPropertyD (P : FieldAlgebraProperty) : Prop where
  /-- Property `(D)` descends from the closed fiber over `A → C` to that over `A → B`. -/
  closedFiberDescent (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
      [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]
      (hBC : RingHom.FaithfullyFlat (algebraMap B C))
      (hC : P (ResidueField A) ((maximalIdeal A).Fiber C)) :
      P (ResidueField A) ((maximalIdeal A).Fiber B)

/-- Helper for Lemma 15.51.11: property `(E)` is invariance under separable algebraic extension
of the ground field. -/
class HasPropertyE (P : FieldAlgebraProperty) : Prop where
  /-- Changing the ground field along a separable algebraic extension preserves `P`. -/
  separableBaseChange (k k' A : Type u) [Field k] [Field k'] [CommRing A]
      [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
      [Algebra.IsSeparable k k'] (hA : P k A) :
      P k' A

/-- Helper for Lemma 15.51.11: the full Chapter 15 package of properties `(A)` through `(E)`. -/
class HasPropertiesABCDE (P : FieldAlgebraProperty) : Prop
    extends P.HasPropertyA, P.HasPropertyB, P.HasPropertyC, P.HasPropertyD, P.HasPropertyE

end FieldAlgebraProperty

section

variable {n : ℕ}

/-- Helper for Lemma 15.51.11: for a prime of an essentially finite type algebra, the residue
field extension over the contracted prime is again essentially finite type. -/
theorem residueField_extension_essFiniteType_of_comap
    {R : Type u} {R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    [Algebra.EssFiniteType R R'] (p' : PrimeSpectrum R') :
    let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R R') p'
    Algebra.EssFiniteType p.asIdeal.ResidueField p'.asIdeal.ResidueField := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R R') p'
  let _ : Algebra.EssFiniteType R' p'.asIdeal.ResidueField := inferInstance
  let _ : Algebra.EssFiniteType R p'.asIdeal.ResidueField :=
    Algebra.EssFiniteType.comp R R' p'.asIdeal.ResidueField
  exact
    Algebra.EssFiniteType.of_comp R p.asIdeal.ResidueField p'.asIdeal.ResidueField

/-- Helper for Lemma 15.51.11: tensor-product base change of a regular ring map along an
essentially finite type algebra is still regular. -/
theorem regularRingMap_tensorBaseChange_of_essFiniteType
    {R : Type u} {R' : Type u} {Λ : Type u}
    [CommRing R] [CommRing R'] [CommRing Λ]
    [Algebra R Λ] [Algebra R R'] [Algebra.EssFiniteType R R']
    (h : (algebraMap R Λ).IsRegularRingMap) :
    (algebraMap R' (R' ⊗[R] Λ)).IsRegularRingMap := by
  simpa using RingHom.IsRegularRingMap.baseChange_of_essFiniteType
    (R := R) (R' := R') (Λ := Λ) h

/-- Helper for Lemma 15.51.11: faithful flatness descends flatness from a composite map. -/
theorem ringHom_flat_of_comp_of_faithfullyFlat
    {A : Type u} {B : Type u} {C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    {f : A →+* B} {g : B →+* C}
    (hgf : (g.comp f).Flat) (hg : g.FaithfullyFlat) :
    f.Flat := by
  letI : Algebra A B := f.toAlgebra
  letI : Algebra B C := g.toAlgebra
  letI : Algebra A C := (g.comp f).toAlgebra
  letI : Module.FaithfullyFlat B C := RingHom.faithfullyFlat_algebraMap_iff.mp <| by
    simpa [RingHom.algebraMap_toAlgebra] using hg
  letI : Module.Flat A C := RingHom.flat_algebraMap_iff.mp <| by
    simpa [RingHom.algebraMap_toAlgebra] using hgf
  letI : Module.Flat A (RestrictScalars A B C) := by
    change Module.Flat A C
    infer_instance
  simpa [RingHom.algebraMap_toAlgebra] using
    (algebraMap_flat_of_flat_of_faithfullyFlat C : (algebraMap A B).Flat)

/-- Helper for Lemma 15.51.11: geometric regularity of the composite fiber descends through a
faithfully flat base-changed map. -/
theorem fiber_isGeometricallyRegular_of_comp_faithfullyFlat
    {A : Type u} {B : Type u} {C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    {f : A →+* B} {g : B →+* C}
    (hgf : (g.comp f).IsRegularRingMap) (hg : g.FaithfullyFlat) (p : PrimeSpectrum A) :
    let _ : Algebra A B := f.toAlgebra
    Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber B) := by
  let _ : Algebra A B := f.toAlgebra
  let _ : Algebra B C := g.toAlgebra
  let _ : Algebra A C := (g.comp f).toAlgebra
  let _ : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' <| by
    ext x
    rfl
  let _ : Algebra B (p.asIdeal.Fiber B) := Algebra.TensorProduct.rightAlgebra
  let D := (p.asIdeal.Fiber B) ⊗[B] C
  let _ : CommRing D := inferInstance
  let _ : Algebra (p.asIdeal.Fiber B) D := Algebra.TensorProduct.leftAlgebra
  let _ : Algebra C D := Algebra.TensorProduct.rightAlgebra
  have hgAlg : (algebraMap B C).FaithfullyFlat := by
    simpa [RingHom.algebraMap_toAlgebra] using hg
  let _ : Module.FaithfullyFlat B C := RingHom.faithfullyFlat_algebraMap_iff.mp hgAlg
  let f1 : (p.asIdeal.Fiber B) →+* D := algebraMap (p.asIdeal.Fiber B) D
  have hf1 : f1.FaithfullyFlat := by
    let hDff : Module.FaithfullyFlat (p.asIdeal.Fiber B) D := inferInstance
    simpa [f1] using
      (RingHom.faithfullyFlat_algebraMap_iff.mpr hDff : f1.FaithfullyFlat)
  let e : D ≃ₐ[p.asIdeal.ResidueField] (p.asIdeal.Fiber C) :=
    Algebra.IsPushout.cancelBaseChangeAlg A p.asIdeal.ResidueField
      B (p.asIdeal.Fiber B) C
  let g1 : D →+* (p.asIdeal.Fiber C) := e.toRingHom
  have hg1 : g1.FaithfullyFlat := by
    simpa [g1] using
      (RingHom.FaithfullyFlat.of_bijective e.bijective : g1.FaithfullyFlat)
  have hDGeom : Algebra.IsGeometricallyRegular p.asIdeal.ResidueField D := by
    let _ : Algebra D (p.asIdeal.Fiber C) := g1.toAlgebra
    let _ : IsScalarTower p.asIdeal.ResidueField D (p.asIdeal.Fiber C) :=
      IsScalarTower.of_algebraMap_eq' <|
        RingHom.ext fun x ↦ by
          change algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C) x =
            g1 (algebraMap p.asIdeal.ResidueField D x)
          exact (e.commutes x).symm
    let _ : Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber C) :=
      hgf.isGeometricallyRegular_fiber p
    exact
      (Algebra.isGeometricallyRegular_of_faithfullyFlat
        (k := p.asIdeal.ResidueField)
        (A := D)
        (B := p.asIdeal.Fiber C)
        (by simpa [g1, RingHom.algebraMap_toAlgebra] using hg1) :
          Algebra.IsGeometricallyRegular p.asIdeal.ResidueField D)
  let _ : Algebra.IsGeometricallyRegular p.asIdeal.ResidueField D := hDGeom
  let _ : IsScalarTower p.asIdeal.ResidueField (p.asIdeal.Fiber B) D :=
    IsScalarTower.of_algebraMap_eq' <| RingHom.ext fun _ ↦ rfl
  exact
    (Algebra.isGeometricallyRegular_of_faithfullyFlat
      (k := p.asIdeal.ResidueField)
      (A := p.asIdeal.Fiber B)
      (B := D)
      (by simpa [f1] using hf1) :
        Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber B))

/-- Helper for Lemma 15.51.11: faithful flatness descends regularity from a composite map. -/
theorem regularRingMap_of_comp_of_faithfullyFlat
    {A : Type u} {B : Type u} {C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    {f : A →+* B} {g : B →+* C}
    (hgf : (g.comp f).IsRegularRingMap) (hg : g.FaithfullyFlat) :
    f.IsRegularRingMap := by
  let _ : Algebra A B := f.toAlgebra
  let _ : Algebra B C := g.toAlgebra
  let _ : Algebra A C := (g.comp f).toAlgebra
  refine
    { toFlat := ?_
      isGeometricallyRegular_fiber := ?_ }
  · exact ringHom_flat_of_comp_of_faithfullyFlat hgf.toFlat hg
  · intro p
    simpa using fiber_isGeometricallyRegular_of_comp_faithfullyFlat hgf hg p

/-- Helper for Lemma 15.51.11: a ring equivalence defines a regular ring map on its underlying
ring homomorphism. -/
theorem RingEquiv.isRegularRingMap
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    e.toRingHom.IsRegularRingMap := by
  -- Compare the equivalence map with the identity after composing with the inverse equivalence.
  have hcomp : (e.symm.toRingHom.comp e.toRingHom).IsRegularRingMap := by
    simpa using (inferInstance : (RingHom.id R).IsRegularRingMap)
  have hff : e.symm.toRingHom.FaithfullyFlat := by
    exact RingHom.FaithfullyFlat.of_bijective e.symm.bijective
  exact regularRingMap_of_comp_of_faithfullyFlat hcomp hff

/-- Helper for Lemma 15.51.11: Serre's condition `(S_n)` ascends along a regular ring map. -/
theorem serreConditionS_of_regularRingHom
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    [f.IsRegularRingMap] [IsNoetherianRing S] [SerreConditionS R n] :
    SerreConditionS S n := by
  let _ : Algebra R S := f.toAlgebra
  let hRS : f.IsRegularRingMap := inferInstance
  letI : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hRS.toFlat
  -- Apply the flat ascent theorem once the regular fibers are recognized as Cohen-Macaulay.
  refine serreConditionS_of_flat_of_fiber fun p : PrimeSpectrum R ↦ ?_
  let _ : IsRegularRing (p.asIdeal.Fiber S) := hRS.isRegularRing_fiber p
  exact CohenMacaulayRing.serreConditionS (p.asIdeal.Fiber S) n

/-- Helper for Lemma 15.51.11: Serre's condition `(S_n)` is invariant under ring equivalence. -/
theorem serreConditionS_iff_of_ringEquiv
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    SerreConditionS R n ↔ SerreConditionS S n := by
  constructor
  · intro hR
    letI : SerreConditionS R n := hR
    exact
      serreConditionS_of_faithfullyFlat e.symm.toRingHom
        (RingHom.FaithfullyFlat.of_bijective e.symm.bijective)
  · intro hS
    letI : SerreConditionS S n := hS
    exact
      serreConditionS_of_faithfullyFlat e.toRingHom
        (RingHom.FaithfullyFlat.of_bijective e.bijective)

/-- Helper for Lemma 15.51.11: the self-depth of a field is zero. -/
theorem moduleDepth_self_eq_zero_of_field (K : Type u) [Field K] :
    moduleDepth K K = 0 := by
  let _ : Ring.KrullDimLE 0 K :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr <| ringKrullDim_eq_zero_of_field K
  have hCM : Module.CohenMacaulay K K := self_cohenMacaulay_of_krullDimLE_zero K
  have hdepth : ringKrullDim K = .some (moduleDepth K K) :=
    (Module.supportDim_self_eq_ringKrullDim K).symm.trans hCM.supportDim_eq_moduleDepth
  rw [ringKrullDim_eq_zero_of_field K] at hdepth
  simpa using hdepth.symm

/-- Helper for Lemma 15.51.11: the closed fiber of a local homomorphism between local rings is
again a local ring. -/
theorem closedFiber_isLocalRing_aux
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] :
    IsLocalRing (Ideal.Fiber (maximalIdeal R) S) := by
  let e :
      Ideal.Fiber (maximalIdeal R) S ≃ₐ[R]
        S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R) :=
    closedFiberQuotAlgEquiv
  letI : IsLocalRing (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) := by
    have hmap : Ideal.map (algebraMap R S) (maximalIdeal R) < (⊤ : Ideal S) :=
      IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)
    have : Nontrivial (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) :=
      Ideal.Quotient.nontrivial_iff.2 hmap.ne
    exact IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (maximalIdeal R)))
      Ideal.Quotient.mk_surjective
  exact
    (e.toRingEquiv.symm :
      S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R) ≃+*
        Ideal.Fiber (maximalIdeal R) S).isLocalRing

/-- Helper for Lemma 15.51.11: if a local homomorphism maps the source maximal ideal onto the
target maximal ideal, then its closed fiber has depth zero. -/
theorem moduleDepth_closedFiber_eq_zero_of_map_maximalIdeal
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S]
    [IsLocalRing (Ideal.Fiber (maximalIdeal R) S)]
    (hmap : Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S) :
    moduleDepth (Ideal.Fiber (maximalIdeal R) S) (Ideal.Fiber (maximalIdeal R) S) = 0 := by
  let e : Ideal.Fiber (maximalIdeal R) S ≃+* S ⧸ maximalIdeal S :=
    (closedFiberQuotAlgEquiv :
        Ideal.Fiber (maximalIdeal R) S ≃ₐ[R]
          S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)).toRingEquiv.trans <|
      Ideal.quotEquivOfEq hmap
  letI : Field (S ⧸ maximalIdeal S) := Ideal.Quotient.field (maximalIdeal S)
  letI : Field (Ideal.Fiber (maximalIdeal R) S) :=
    IsField.toField <| e.toMulEquiv.isField (Field.toIsField _)
  simpa using moduleDepth_self_eq_zero_of_field (Ideal.Fiber (maximalIdeal R) S)

/-- Helper for Lemma 15.51.11: a ring equivalence between Noetherian local rings preserves the
self-module depth. -/
theorem moduleDepth_self_eq_of_ringEquiv
    {R : Type u} {S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    (e : R ≃+* S) :
    moduleDepth R R = moduleDepth S S := by
  let _ : Algebra R S := e.toRingHom.toAlgebra
  letI : IsLocalHom (algebraMap R S) :=
    IsLocalHom.of_surjective (algebraMap R S) e.surjective
  letI : Module.Flat R S := RingHom.flat_algebraMap_iff.mp <| by
    simpa [RingHom.algebraMap_toAlgebra] using
      (RingHom.Flat.of_bijective e.bijective : e.toRingHom.Flat)
  letI : IsLocalRing (Ideal.Fiber (maximalIdeal R) S) :=
    closedFiber_isLocalRing_aux
  have hdepth :
      moduleDepth S S =
        moduleDepth R R +
          moduleDepth (Ideal.Fiber (maximalIdeal R) S) (Ideal.Fiber (maximalIdeal R) S) :=
    depth_target_eq_depth_source_add_depth_closed_fiber
  have hmap :
      Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S := by
    exact IsLocalRing.map_maximalIdeal_of_surjective (algebraMap R S) e.surjective
  simpa [moduleDepth_closedFiber_eq_zero_of_map_maximalIdeal hmap] using hdepth.symm

/-- Helper for Lemma 15.51.11: the fiber of `R → k' ⊗[k] R` over `p` is canonically the tensor
product `k' ⊗[k] κ(p)`. -/
noncomputable def fiber_tensorProduct_fieldExtension_equiv
    {k : Type u} {k' : Type u} {R : Type u}
    [Field k] [Field k'] [CommRing R] [Algebra k k'] [Algebra k R]
    (p : PrimeSpectrum R) :
    p.asIdeal.Fiber (k' ⊗[k] R) ≃+* (k' ⊗[k] p.asIdeal.ResidueField) :=
  let _ : Algebra R (k' ⊗[k] R) := Algebra.TensorProduct.rightAlgebra
  -- First swap the fiber tensor factors, then cancel the middle `R`-base change.
  (Algebra.TensorProduct.comm R p.asIdeal.ResidueField (k' ⊗[k] R)).toRingEquiv.trans <|
    (Algebra.IsPushout.cancelBaseChangeAlg k k' R (k' ⊗[k] R)
      p.asIdeal.ResidueField).toRingEquiv

/-- Helper for Lemma 15.51.11: fibers of a Noetherian algebra over a prime are Noetherian. -/
theorem fiber_isNoetherianRing_of_noetherian_algebra
    {A : Type u} {B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing B] (p : PrimeSpectrum A) :
    IsNoetherianRing (p.asIdeal.Fiber B) := by
  let _ : Algebra.EssFiniteType B (B ⊗[A] p.asIdeal.ResidueField) := inferInstance
  let _ : IsNoetherianRing (B ⊗[A] p.asIdeal.ResidueField) :=
    Algebra.EssFiniteType.isNoetherianRing B (B ⊗[A] p.asIdeal.ResidueField)
  exact
    isNoetherianRing_of_ringEquiv (B ⊗[A] p.asIdeal.ResidueField)
      (Algebra.TensorProduct.comm A p.asIdeal.ResidueField B).toRingEquiv.symm

-- Proof sketch: the ring map `R → k' ⊗[k] R` is flat, and its fibers are Cohen-Macaulay by
-- Lemma `10.167.1` because they are tensor products of field extensions with one side
-- finitely generated over the base. Apply Lemma `10.163.4` to ascend Serre's condition `(S_n)`
-- along this flat base change.
/-- Lemma 15.51.11 (1): if `k → R` is a map from a field to a Noetherian ring, and
`k' / k` is a finitely generated field extension, then `R` having Serre's condition `(S_n)`
implies that `k' ⊗[k] R` also has Serre's condition `(S_n)`. -/
@[stacks 0BIY]
theorem serreConditionS_tensorProduct_of_finitelyGeneratedFieldExtension
    {k : Type u} {k' : Type u} {R : Type u}
    [Field k] [Field k'] [CommRing R] [Algebra k k'] [Algebra k R]
    [Algebra.EssFiniteType k k'] [SerreConditionS R n] :
    SerreConditionS (k' ⊗[k] R) n := by
  let T := k' ⊗[k] R
  letI : Algebra R T := Algebra.TensorProduct.rightAlgebra
  let U := R ⊗[k] k'
  letI : Algebra R U := Algebra.TensorProduct.leftAlgebra
  let _ : Module.Flat k k' := inferInstance
  letI : Module.Flat R U := Module.Flat.baseChange k R k'
  let eRT : U ≃+* T := (Algebra.TensorProduct.comm k R k').toRingEquiv
  have hflatU : (algebraMap R U).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hflatT : (algebraMap R T).Flat := by
    have hcomp : (eRT.toRingHom.comp (algebraMap R U)).Flat :=
      RingHom.Flat.comp hflatU (RingHom.Flat.of_bijective eRT.bijective)
    have hmap : eRT.toRingHom.comp (algebraMap R U) = algebraMap R T := by
      ext x
      rfl
    simpa [hmap] using hcomp
  letI : Module.Flat R T := RingHom.flat_algebraMap_iff.mp hflatT
  letI : IsNoetherianRing T :=
    isNoetherianRing_tensorProduct_of_finitelyGeneratedFieldExtension
  -- Apply flat ascent once the fibers are identified with tensor products of fields.
  refine serreConditionS_of_flat_of_fiber fun p : PrimeSpectrum R ↦ ?_
  let e : p.asIdeal.Fiber T ≃+* (k' ⊗[k] p.asIdeal.ResidueField) :=
    fiber_tensorProduct_fieldExtension_equiv (k := k) (k' := k') (R := R) p
  letI : CohenMacaulayRing (k' ⊗[k] p.asIdeal.ResidueField) :=
    cohenMacaulayRing_tensorProduct_of_finitelyGeneratedFieldExtension
  have hSerre : SerreConditionS (k' ⊗[k] p.asIdeal.ResidueField) n :=
    CohenMacaulayRing.serreConditionS (k' ⊗[k] p.asIdeal.ResidueField) n
  exact (serreConditionS_iff_of_ringEquiv (n := n) e).2 hSerre

/-- Helper for Lemma 15.51.11: localizing `R_𝔭` again at a prime `𝔮` agrees with localizing `R`
at the contracted prime `𝔮 ∩ R`. -/
theorem localizationAtPrime_comap_isLocalizationAtPrime
    {R : Type u} [CommRing R] (p : PrimeSpectrum R)
    (q : PrimeSpectrum (Localization.AtPrime p.asIdeal)) :
    let p' : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q
    IsLocalization.AtPrime (Localization.AtPrime q.asIdeal) p'.asIdeal := by
  let p' : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q
  simpa [p'] using
    (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization p.asIdeal.primeCompl
      (Localization.AtPrime q.asIdeal) q.asIdeal)

/-- Helper for Lemma 15.51.11: localizing `R_𝔭` again at a prime `𝔮` agrees with localizing `R`
at the contracted prime `𝔮 ∩ R`. -/
noncomputable def localizationAtPrime_comap_algEquiv
    {R : Type u} [CommRing R] (p : PrimeSpectrum R)
    (q : PrimeSpectrum (Localization.AtPrime p.asIdeal)) :
    Localization.AtPrime
        (PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q).asIdeal ≃ₐ[R]
      Localization.AtPrime q.asIdeal :=
  let p' : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q
  let _ : IsLocalization.AtPrime (Localization.AtPrime q.asIdeal) p'.asIdeal :=
    localizationAtPrime_comap_isLocalizationAtPrime p q
  IsLocalization.algEquiv p'.asIdeal.primeCompl
    (Localization.AtPrime p'.asIdeal) (Localization.AtPrime q.asIdeal)

-- Proof sketch: to prove `(S_n)` for `R_𝔭`, localize once more at an arbitrary prime `𝔮`, rewrite
-- `(R_𝔭)_𝔮` as `R_(𝔮 ∩ R)`, and transport the known depth/Krull-dimension inequality from `R`.
/-- Helper for Lemma 15.51.11: Serre's condition `(S_n)` is preserved by localization at a prime.
-/
theorem serreConditionS_localizationAtPrime
    {R : Type u} [CommRing R] [IsNoetherianRing R] [SerreConditionS R n]
    (p : PrimeSpectrum R) :
    SerreConditionS (Localization.AtPrime p.asIdeal) n := by
  refine
    { toIsNoetherian := inferInstance
      toSerreConditionS := ?_ }
  refine
    { toFinite := inferInstance
      moduleDepth_localizationAtPrime_ge_min_supportDim := ?_ }
  intro q
  rw [Module.supportDim_self_eq_ringKrullDim]
  let p' : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q
  let e : Localization.AtPrime p'.asIdeal ≃ₐ[R] Localization.AtPrime q.asIdeal :=
    localizationAtPrime_comap_algEquiv p q
  have hsrc :
      WithBot.some
          (moduleDepth (Localization.AtPrime p'.asIdeal) (Localization.AtPrime p'.asIdeal) : ℕ∞) ≥
        min (n : WithBot ℕ∞) (ringKrullDim (Localization.AtPrime p'.asIdeal)) :=
    SerreConditionS.moduleDepth_localizationAtPrime_ge_min (R := R) (k := n)
      (h := inferInstance) p'
  have hdepth :
      moduleDepth (Localization.AtPrime p'.asIdeal) (Localization.AtPrime p'.asIdeal) =
        moduleDepth (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) := by
    exact moduleDepth_self_eq_of_ringEquiv e.toRingEquiv
  have hdim :
      ringKrullDim (Localization.AtPrime p'.asIdeal) =
        ringKrullDim (Localization.AtPrime q.asIdeal) := by
    simpa using ringKrullDim_eq_of_ringEquiv e.toRingEquiv
  simpa [hdepth, hdim] using hsrc

/-- Helper for Lemma 15.51.11: a local ring is the localization of itself away from its maximal
ideal. -/
theorem self_isLocalization_away_maximalIdeal
    (A : Type u) [CommRing A] [IsLocalRing A] :
    IsLocalization (maximalIdeal A).primeCompl A := by
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    exact IsLocalRing.notMem_maximalIdeal.mp y.2
  · intro z
    exact ⟨⟨z, 1⟩, by simp⟩
  · intro x y hxy
    exact ⟨1, by simpa using hxy⟩

/-- Helper for Lemma 15.51.11: the closed point of a local ring is its maximal ideal. -/
theorem closedPoint_asIdeal_eq_maximalIdeal
    (A : Type u) [CommRing A] [IsLocalRing A] :
    (closedPoint A).asIdeal = maximalIdeal A := by
  rfl

/-- Helper for Lemma 15.51.11: the closed point of a local ring is the prime defined by its
maximal ideal. -/
theorem closedPoint_eq_maximalIdeal_primeSpectrum
    (A : Type u) [CommRing A] [IsLocalRing A] :
    closedPoint A = ⟨maximalIdeal A, inferInstance⟩ := by
  rfl

/-- Helper for Lemma 15.51.11: localizing a local ring at its closed point gives the ring back. -/
noncomputable def localizationAtClosedPoint_algEquiv_self
    (A : Type u) [CommRing A] [IsLocalRing A] :
    Localization.AtPrime (closedPoint A).asIdeal ≃ₐ[A] A :=
  let _ : IsLocalization (maximalIdeal A).primeCompl A := self_isLocalization_away_maximalIdeal A
  Eq.ndrec
    (motive := fun p : PrimeSpectrum A => Localization.AtPrime p.asIdeal ≃ₐ[A] A)
    (Localization.algEquiv (maximalIdeal A).primeCompl A)
    (closedPoint_eq_maximalIdeal_primeSpectrum A).symm

-- Proof sketch: the forward implication is inherited by localizations of a ring satisfying
-- `(S_n)`. For the converse, a Noetherian ring has `(S_n)` exactly when each localization at a
-- prime does, which is the local formulation built into `SerreConditionS`.
/-- Lemma 15.51.11 (2): if `R` is Noetherian, then `R` has Serre's condition `(S_n)`
if and only if every localization `R_𝔭` has Serre's condition `(S_n)`. -/
@[stacks 0BIY]
theorem serreConditionS_iff_localizationAtPrime
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    SerreConditionS R n ↔
      ∀ p : PrimeSpectrum R, SerreConditionS (Localization.AtPrime p.asIdeal) n := by
  constructor
  · intro hR p
    letI : SerreConditionS R n := hR
    exact serreConditionS_localizationAtPrime (n := n) p
  · intro hlocal
    refine
      { toIsNoetherian := inferInstance
        toSerreConditionS := ?_ }
    refine
      { toFinite := inferInstance
        moduleDepth_localizationAtPrime_ge_min_supportDim := ?_ }
    intro p
    rw [Module.supportDim_self_eq_ringKrullDim]
    let A := Localization.AtPrime p.asIdeal
    letI : SerreConditionS A n := hlocal p
    have hloc :
        WithBot.some
            (moduleDepth (Localization.AtPrime (closedPoint A).asIdeal)
              (Localization.AtPrime (closedPoint A).asIdeal) : ℕ∞) ≥
          min (n : WithBot ℕ∞)
            (ringKrullDim (Localization.AtPrime (closedPoint A).asIdeal)) :=
      SerreConditionS.moduleDepth_localizationAtPrime_ge_min (R := A) (k := n)
        (h := inferInstance) (closedPoint A)
    let e : Localization.AtPrime (closedPoint A).asIdeal ≃ₐ[A] A :=
      localizationAtClosedPoint_algEquiv_self A
    have hdepth :
        moduleDepth (Localization.AtPrime (closedPoint A).asIdeal)
            (Localization.AtPrime (closedPoint A).asIdeal) =
          moduleDepth A A := by
      exact moduleDepth_self_eq_of_ringEquiv e.toRingEquiv
    have hdim :
        ringKrullDim (Localization.AtPrime (closedPoint A).asIdeal) =
          ringKrullDim A := by
      simpa using ringKrullDim_eq_of_ringEquiv e.toRingEquiv
    simpa [A, hdepth, hdim] using hloc

-- Proof sketch: for each `p : Spec(A)`, base change the regular map `B → C` along
-- `A → κ(p)` to obtain a regular map on the fibers. Regular fibers are geometrically regular,
-- hence Cohen-Macaulay, so Lemma `10.163.4` ascends `(S_n)` from the fiber of `A → B` to the
-- fiber of `A → C`.
/-- Lemma 15.51.11 (3): if `A → B → C` are maps of commutative rings, `C` is Noetherian, the
fibers of `A → B` satisfy Serre's condition `(S_n)`, and `B → C` is a regular ring map, then the
fibers of `A → C` satisfy Serre's condition `(S_n)`. -/
@[stacks 0BIY]
theorem fiber_serreConditionS_of_regularRingMap
    {A : Type u} {B : Type u} {C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing C] [(algebraMap B C).IsRegularRingMap]
    (hfiber : ∀ p : PrimeSpectrum A, SerreConditionS (p.asIdeal.Fiber B) n) :
    ∀ p : PrimeSpectrum A, SerreConditionS (p.asIdeal.Fiber C) n := by
  intro p
  let κ := p.asIdeal.ResidueField
  let S0 := B ⊗[A] κ
  let S := p.asIdeal.Fiber B
  let D := S0 ⊗[B] C
  let T := p.asIdeal.Fiber C
  letI : CommRing S0 := inferInstance
  letI : CommRing S := inferInstance
  letI : CommRing D := inferInstance
  letI : CommRing T := inferInstance
  letI : Algebra B S0 := Algebra.TensorProduct.leftAlgebra
  letI : Algebra κ S := Algebra.TensorProduct.leftAlgebra
  letI : Algebra S0 D := Algebra.TensorProduct.leftAlgebra
  letI : Algebra C D := Algebra.TensorProduct.rightAlgebra
  let eS : S0 ≃+* S := (Algebra.TensorProduct.comm A B κ).toRingEquiv
  letI : (algebraMap S0 D).IsRegularRingMap :=
    regularRingMap_tensorBaseChange_of_essFiniteType
      (R := B) (R' := S0) (Λ := C)
      (inferInstance : (algebraMap B C).IsRegularRingMap)
  have hS0 : SerreConditionS S0 n :=
    (serreConditionS_iff_of_ringEquiv (n := n) eS).2 (hfiber p)
  letI : SerreConditionS S0 n := hS0
  let e : D ≃ₐ[κ] T :=
    Algebra.IsPushout.cancelBaseChangeAlg A κ B S0 C
  letI : IsNoetherianRing T := fiber_isNoetherianRing_of_noetherian_algebra (A := A) (B := C) p
  letI : IsNoetherianRing D := isNoetherianRing_of_ringEquiv T e.toRingEquiv.symm
  have hD : SerreConditionS D n := by
    exact serreConditionS_of_regularRingHom (n := n) (algebraMap S0 D)
  exact (serreConditionS_iff_of_ringEquiv (n := n) e.toRingEquiv).1 hD

-- Proof sketch: for each `p : Spec(A)`, base change the faithfully flat map `B → C` along
-- `A → κ(p)` to obtain a faithfully flat map on fibers. Then apply Lemma `10.164.5` to descend
-- Serre's condition `(S_n)` from the fiber of `A → C` to the corresponding fiber of `A → B`.
/-- Lemma 15.51.11 (4): if `A → B → C` are maps of commutative rings, the fibers of `A → C`
satisfy Serre's condition `(S_n)`, and `B → C` is faithfully flat, then the fibers of `A → B`
satisfy Serre's condition `(S_n)`. -/
@[stacks 0BIY]
theorem fiber_serreConditionS_of_faithfullyFlat
    {A : Type u} {B : Type u} {C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hff : (algebraMap B C).FaithfullyFlat)
    (hfiber : ∀ p : PrimeSpectrum A, SerreConditionS (p.asIdeal.Fiber C) n) :
    ∀ p : PrimeSpectrum A, SerreConditionS (p.asIdeal.Fiber B) n := by
  intro p
  letI : SerreConditionS (p.asIdeal.Fiber C) n := hfiber p
  letI : Algebra B (p.asIdeal.Fiber B) := Algebra.TensorProduct.rightAlgebra
  let D := (p.asIdeal.Fiber B) ⊗[B] C
  letI : CommRing D := inferInstance
  letI : Algebra (p.asIdeal.Fiber B) D := Algebra.TensorProduct.leftAlgebra
  letI : Algebra C D := Algebra.TensorProduct.rightAlgebra
  letI : Module.FaithfullyFlat B C := RingHom.faithfullyFlat_algebraMap_iff.mp hff
  let f : (p.asIdeal.Fiber B) →+* D := algebraMap (p.asIdeal.Fiber B) D
  have hf : f.FaithfullyFlat := by
    letI : Module.FaithfullyFlat (p.asIdeal.Fiber B) D := by infer_instance
    simpa [f] using
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance : f.FaithfullyFlat)
  let e : D ≃+* (p.asIdeal.Fiber C) :=
    (Algebra.IsPushout.cancelBaseChangeAlg A p.asIdeal.ResidueField
      B (p.asIdeal.Fiber B) C).toRingEquiv
  let g : D →+* (p.asIdeal.Fiber C) := e.toRingHom
  have hg : g.FaithfullyFlat := by
    simpa [g] using
      (RingHom.FaithfullyFlat.of_bijective e.bijective : g.FaithfullyFlat)
  have hfiber_ff : (g.comp f).FaithfullyFlat := by
    -- The comparison map on fibers is the composition of a base-changed faithfully flat map
    -- with a ring equivalence, so it is faithfully flat.
    change (RingHom.comp g f).FaithfullyFlat
    exact RingHom.FaithfullyFlat.stableUnderComposition f g hf hg
  letI : Algebra (p.asIdeal.Fiber B) (p.asIdeal.Fiber C) := RingHom.toAlgebra (g.comp f)
  simpa [f, g] using
    (serreConditionS_of_faithfullyFlat
      (algebraMap (p.asIdeal.Fiber B) (p.asIdeal.Fiber C)) hfiber_ff :
        SerreConditionS (p.asIdeal.Fiber B) n)

-- Proof sketch: repeat the source-faithful closed-fiber base-change argument from part `(D)` once,
-- then reuse the resulting theorem inside the final owner instance instead of duplicating the proof.
/-- Helper for Lemma 15.51.11: Serre's condition `(S_n)` descends on the closed fiber along a
faithfully flat local extension. -/
theorem closedFiber_serreConditionS_of_faithfullyFlat
    {A : Type u} {B : Type u} {C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]
    (hBC : (algebraMap B C).FaithfullyFlat)
    [SerreConditionS ((maximalIdeal A).Fiber C) n] :
    SerreConditionS ((maximalIdeal A).Fiber B) n := by
  letI : Algebra B ((maximalIdeal A).Fiber B) := Algebra.TensorProduct.rightAlgebra
  let D := ((maximalIdeal A).Fiber B) ⊗[B] C
  letI : CommRing D := inferInstance
  letI : Algebra ((maximalIdeal A).Fiber B) D := Algebra.TensorProduct.leftAlgebra
  letI : Algebra C D := Algebra.TensorProduct.rightAlgebra
  letI : Module.FaithfullyFlat B C := RingHom.faithfullyFlat_algebraMap_iff.mp hBC
  let f : ((maximalIdeal A).Fiber B) →+* D := algebraMap ((maximalIdeal A).Fiber B) D
  have hf : f.FaithfullyFlat := by
    letI : Module.FaithfullyFlat ((maximalIdeal A).Fiber B) D := by infer_instance
    simpa [f] using
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance : f.FaithfullyFlat)
  let e : D ≃+* ((maximalIdeal A).Fiber C) :=
    (Algebra.IsPushout.cancelBaseChangeAlg A ((maximalIdeal A).ResidueField)
      B ((maximalIdeal A).Fiber B) C).toRingEquiv
  let g : D →+* ((maximalIdeal A).Fiber C) := e.toRingHom
  have hg : g.FaithfullyFlat := by
    simpa [g] using
      (RingHom.FaithfullyFlat.of_bijective e.bijective : g.FaithfullyFlat)
  have hfiber_ff : (g.comp f).FaithfullyFlat := by
    -- The closed-fiber comparison map is a base change of `B → C` followed by a ring equivalence.
    change (RingHom.comp g f).FaithfullyFlat
    exact RingHom.FaithfullyFlat.stableUnderComposition f g hf hg
  letI : Algebra ((maximalIdeal A).Fiber B) ((maximalIdeal A).Fiber C) :=
    RingHom.toAlgebra (g.comp f)
  simpa [f, g] using
    (serreConditionS_of_faithfullyFlat
      (algebraMap ((maximalIdeal A).Fiber B) ((maximalIdeal A).Fiber C)) hfiber_ff :
        SerreConditionS ((maximalIdeal A).Fiber B) n)

end

namespace Algebra

section

variable {n : ℕ}

/-- The canonical `FieldAlgebraProperty` bridge for Serre's condition `(S_n)`. -/
abbrev SerreConditionSProperty (n : ℕ) : FieldAlgebraProperty :=
  fun k A ↦ fun [Field k] [CommRing A] [Algebra k A] ↦ SerreConditionS A n

-- Proof sketch: `SerreConditionS A n` depends only on the underlying Noetherian ring `A`, so
-- changing the base field along a separable algebraic extension leaves the same ring property.
/-- Lemma 15.51.11 (5), owner-form: the Chapter 15 field-algebra property
`SerreConditionSProperty n` has property `(E)`, i.e. Serre's condition `(S_n)` is
unchanged under separable algebraic extension of the ground field. -/
@[stacks 0BIY]
theorem serreConditionS_hasPropertyE :
    (SerreConditionSProperty n).HasPropertyE := by
  refine { separableBaseChange := ?_ }
  intro k k' A _ _ _ _ _ _ _ _ hS
  exact hS

-- Proof sketch: the five source-facing parts of Lemma `15.51.11` already match the five fields of
-- the canonical chapter owner `FieldAlgebraProperty.HasPropertiesABCDE` for the property
-- `SerreConditionSProperty n`, so the instance reuses those owner theorems directly and only
-- spells out the closed-fiber faithfully flat descent step.
/-- Lemma 15.51.11 packages Serre's condition `(S_n)` into the canonical Chapter 15 owner for
field-algebra properties satisfying `(A)` through `(E)`. -/
@[stacks 0BIY]
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
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hBC hC
    letI : SerreConditionS ((maximalIdeal A).Fiber C) n := hC
    exact closedFiber_serreConditionS_of_faithfullyFlat (n := n) hBC
  separableBaseChange := serreConditionS_hasPropertyE.separableBaseChange

end

end Algebra
