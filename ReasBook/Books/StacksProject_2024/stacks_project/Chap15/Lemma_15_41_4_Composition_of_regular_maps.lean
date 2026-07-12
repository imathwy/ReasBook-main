import Mathlib
import StacksProject_2024.Chap10.Definition_10_112_5
import StacksProject_2024.Chap10.Lemma_10_163_5
import StacksProject_2024.Chap10.Lemma_10_112_8
import StacksProject_2024.Chap15.Definition_15_41_1
import StacksProject_2024.Chap15.Lemma_15_41_3_Regular_maps_and_base_change

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open IsLocalRing

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingHom.IsRegularRingMap

universe u v w t

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable {f : A →+* B} {g : B →+* C}

/-- Helper for Lemma 15.41.4 (Composition of regular maps): a regular ring map from a field has
regular target ring. -/
lemma isRegularRing_of_regularRingMap_from_field
    {k : Type t} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    (h : (algebraMap k S).IsRegularRingMap) :
    IsRegularRing S := by
  let _ : Algebra k S := (algebraMap k S).toAlgebra
  let p0 : PrimeSpectrum k := ⟨⊥, Ideal.isPrime_bot⟩
  let eκ := Algebra.residueField_algEquiv_self_of_field_prime (k := k) p0
  let _ : Algebra p0.asIdeal.ResidueField k := eκ.toRingHom.toAlgebra
  let _ : Algebra p0.asIdeal.ResidueField S :=
    ((algebraMap k S).comp (algebraMap p0.asIdeal.ResidueField k)).toAlgebra
  let _ : IsScalarTower p0.asIdeal.ResidueField k S := IsScalarTower.of_algebraMap_eq' rfl
  let e : p0.asIdeal.Fiber S ≃ₐ[p0.asIdeal.ResidueField] S :=
    Algebra.field_fiber_algEquiv (k := k) (A := S) p0
  have hfiber : IsRegularRing (p0.asIdeal.Fiber S) := by
    -- Evaluate the regular map at the unique prime of the field.
    simpa using h.isRegularRing_fiber p0
  let _ : IsRegularRing (p0.asIdeal.Fiber S) := hfiber
  -- Transport regularity from the fiber back to the target ring.
  exact isRegularRing_of_faithfullyFlat e.symm.toRingHom
    (RingHom.FaithfullyFlat.of_bijective e.symm.bijective)

/-- Helper for Lemma 15.41.4 (Composition of regular maps): after base changing a regular map
`A → B` to an essentially finite type field algebra `K`, the resulting source ring `K ⊗[A] B` is
regular. -/
lemma field_baseChange_source_isRegularRing
    {K : Type t} [Field K] [Algebra A K] [Algebra.EssFiniteType A K]
    (hf : f.IsRegularRingMap) :
    let _ : Algebra A B := f.toAlgebra
    IsRegularRing (K ⊗[A] B) := by
  let _ : Algebra A B := f.toAlgebra
  have hbase :
      (algebraMap K (K ⊗[A] B)).IsRegularRingMap := by
    -- Base change the regular map `A → B` along `A → K`.
    simpa using
      (RingHom.IsRegularRingMap.baseChange_of_essFiniteType
        (R := A) (R' := K) (Λ := B) hf)
  -- A regular map out of a field has regular target.
  exact isRegularRing_of_regularRingMap_from_field hbase

/-- Helper for Lemma 15.41.4 (Composition of regular maps): the tensor model of the composite
fiber over `p` is Noetherian because it is equivalent to the assumed Noetherian fiber
`p.asIdeal.Fiber C`. -/
lemma field_baseChange_target_isNoetherianRing (p : PrimeSpectrum A)
    {K : Type t} [Field K] [Algebra p.asIdeal.ResidueField K]
    [Algebra.EssFiniteType p.asIdeal.ResidueField K]
    (hfiber_noetherian :
      let _ : Algebra A C := (g.comp f).toAlgebra
      ∀ p : PrimeSpectrum A, IsNoetherianRing (p.asIdeal.Fiber C)) :
    let _ : Algebra A C := (g.comp f).toAlgebra
    let _ : Algebra A K :=
      RingHom.toAlgebra
        ((algebraMap p.asIdeal.ResidueField K).comp (algebraMap A p.asIdeal.ResidueField))
    let _ : IsScalarTower A p.asIdeal.ResidueField K := IsScalarTower.of_algebraMap_eq' rfl
    IsNoetherianRing (K ⊗[A] C) := by
  let _ : Algebra A C := (g.comp f).toAlgebra
  let _ : Algebra A K :=
    RingHom.toAlgebra
      ((algebraMap p.asIdeal.ResidueField K).comp (algebraMap A p.asIdeal.ResidueField))
  let _ : IsScalarTower A p.asIdeal.ResidueField K := IsScalarTower.of_algebraMap_eq' rfl
  have hfiber :
      IsNoetherianRing (p.asIdeal.Fiber C) := by
    simpa using hfiber_noetherian p
  let e :
      K ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber C ≃+* K ⊗[A] C := by
    -- Cancel the residue-field base change to reach the ambient tensor model.
    simpa using
      (Algebra.TensorProduct.cancelBaseChange A p.asIdeal.ResidueField
        p.asIdeal.ResidueField K C).toRingEquiv
  let T := (p.asIdeal.Fiber C) ⊗[p.asIdeal.ResidueField] K
  let _ : Algebra.EssFiniteType (p.asIdeal.Fiber C) T := inferInstance
  let _ : IsNoetherianRing T :=
    Algebra.EssFiniteType.isNoetherianRing (p.asIdeal.Fiber C) T
  let ecomm :
      T ≃+* K ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber C :=
    (Algebra.TensorProduct.comm p.asIdeal.ResidueField (p.asIdeal.Fiber C) K).toRingEquiv
  let _ : IsNoetherianRing (K ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber C) :=
    isNoetherianRing_of_ringEquiv T ecomm
  -- Transfer Noetherianity across the explicit tensor cancellation equivalence.
  let hNoeth : IsNoetherianRing (K ⊗[A] C) :=
    isNoetherianRing_of_ringEquiv
      (K ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber C) e
  exact hNoeth

/-- Helper for Lemma 15.41.4 (Composition of regular maps): base changing `B → C` along
the canonical left tensor model `B ⊗[A] K` yields a regular map to the explicit pushout ring
`(B ⊗[A] K) ⊗[B] C`. -/
lemma tensorSource_leftModel_regular_map
    {K : Type t} [Field K] [Algebra A K] [Algebra.EssFiniteType A K]
    (hg : g.IsRegularRingMap) :
    let _ : Algebra A B := f.toAlgebra
    let S₀ := B ⊗[A] K
    let _ : CommRing S₀ := inferInstance
    let _ : Algebra B S₀ := Algebra.TensorProduct.leftAlgebra
    let _ : Algebra B C := g.toAlgebra
    let _ : CommRing (S₀ ⊗[B] C) := inferInstance
    (algebraMap S₀ (S₀ ⊗[B] C)).IsRegularRingMap := by
  let _ : Algebra A B := f.toAlgebra
  let S₀ := B ⊗[A] K
  let _ : CommRing S₀ := inferInstance
  let _ : Algebra B S₀ := Algebra.TensorProduct.leftAlgebra
  let _ : Algebra B C := g.toAlgebra
  let _ : CommRing (S₀ ⊗[B] C) := inferInstance
  -- Route correction: prove regularity first on the canonical left-tensor model, where the
  -- `B`-algebra structure is definitionally the one expected by base change.
  simpa [S₀] using
    (RingHom.IsRegularRingMap.baseChange_of_essFiniteType
      (R := B) (R' := S₀) (Λ := C) hg)

/-- Helper for Lemma 15.41.4 (Composition of regular maps): base changing `B → C` along
`B → K ⊗[A] B` yields a regular map to the explicit pushout ring
`(K ⊗[A] B) ⊗[B] C`. -/
lemma field_baseChange_target_regular_map
    {K : Type t} [Field K] [Algebra A K] [Algebra.EssFiniteType A K]
    (hg : g.IsRegularRingMap) :
    let _ : Algebra A B := f.toAlgebra
    let S := K ⊗[A] B
    let _ : CommRing S := inferInstance
    let _ : Algebra B S := Algebra.TensorProduct.rightAlgebra
    let _ : Algebra B C := g.toAlgebra
    let _ : CommRing (S ⊗[B] C) := inferInstance
    (algebraMap S (S ⊗[B] C)).IsRegularRingMap := by
  let _ : Algebra A B := f.toAlgebra
  let S := K ⊗[A] B
  let _ : CommRing S := inferInstance
  let _ : Algebra B S := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra B C := g.toAlgebra
  let _ : CommRing (S ⊗[B] C) := inferInstance
  let eS : B ⊗[A] K ≃ₐ[B] S := by
    -- `commRight` is the canonical source-model swap from the left tensor model to the
    -- right tensor model used in the main theorem.
    simpa [S] using (Algebra.TensorProduct.commRight A B K)
  let _ : Algebra.EssFiniteType B S :=
    (Algebra.EssFiniteType.iff_of_algEquiv eS).1 inferInstance
  -- Route correction: transport only the `B`-algebra finite-type structure to the right tensor
  -- model, then apply the base-change theorem directly to `B → C`.
  simpa [S] using
    (RingHom.IsRegularRingMap.baseChange_of_essFiniteType
      (R := B) (R' := S) (Λ := C) hg)

/-- Helper for Lemma 15.41.4 (Composition of regular maps): regularity of a fiber ring is
unchanged when the ambient algebra structure on the target is replaced by an equal one. -/
lemma fiber_isRegularRing_of_algebra_eq
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (p : PrimeSpectrum R) {A₁ A₂ : Algebra R S} (hA : A₁ = A₂) :
    @IsRegularRing (@Ideal.Fiber R _ p.asIdeal _ S _ A₁) _ →
      @IsRegularRing (@Ideal.Fiber R _ p.asIdeal _ S _ A₂) _ := by
  -- The two fiber rings are definitionally identical after substituting the algebra structure.
  subst hA
  intro hreg
  exact hreg

/-- Helper for Lemma 15.41.4 (Composition of regular maps): the local fiber ring at a target prime
of a regular map is a regular local ring. -/
lemma fiberLocalRingAt_isRegularLocalRing_of_regular_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hRS : (algebraMap R S).IsRegularRingMap) (q : PrimeSpectrum S) :
    IsRegularLocalRing (fiberLocalRingAt R S q) := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  have hfiber :
      IsRegularRing (p.asIdeal.Fiber S) := by
    have hA : (algebraMap R S).toAlgebra = (inferInstance : Algebra R S) := by
      apply Algebra.algebra_ext
      intro x
      rfl
    -- First pass from regularity of the map to regularity of the global fiber over `q ∩ R`.
    exact
      fiber_isRegularRing_of_algebra_eq
          (p := p)
          (A₁ := (algebraMap R S).toAlgebra)
          (A₂ := (inferInstance : Algebra R S))
          hA <|
        by simpa [p] using hRS.isRegularRing_fiber p
  let _ : IsRegularRing (p.asIdeal.Fiber S) := hfiber
  -- Route correction: the local fiber ring is already the prime localization of that global
  -- fiber, so no closed-fiber comparison is needed at this stage.
  simpa [fiberLocalRingAt, fiberPrimeAt, p] using
    (IsRegularRing.isRegularLocalRing_atPrime (R := p.asIdeal.Fiber S) (fiberPrimeAt R S q))

/-- Helper for Lemma 15.41.4 (Composition of regular maps): after localizing `R → S` at
`q : Spec S`, the maximal ideal of the source localization is exactly the image of the contracted
prime `q ∩ R` inside the target localization. -/
lemma localizationAtPrime_map_maximalIdeal_eq_map_comap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) :
    let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
    Ideal.map (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal))
      (maximalIdeal (Localization.AtPrime p.asIdeal)) =
      Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  calc
    Ideal.map (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal))
        (maximalIdeal (Localization.AtPrime p.asIdeal)) =
      Ideal.map (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal))
        (Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) p.asIdeal) := by
          -- Rewrite the source maximal ideal using the canonical at-prime localization formula.
          rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p.asIdeal
            (Localization.AtPrime p.asIdeal)]
    _ = Ideal.map
        ((algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)).comp
          (algebraMap R (Localization.AtPrime p.asIdeal))) p.asIdeal := by
          -- Then compress the two successive ideal images into one ambient image in `S_q`.
          rw [Ideal.map_map]
    _ = Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal := by
          -- Finally identify the composite algebra map with the direct localization map.
          rw [← IsScalarTower.algebraMap_eq R (Localization.AtPrime p.asIdeal)
            (Localization.AtPrime q.asIdeal)]

/-- Helper for Lemma 15.41.4 (Composition of regular maps): the localized closed-fiber quotient can
be rewritten from the local maximal ideal presentation to the ambient image of `q ∩ R`. -/
noncomputable def localizedClosedFiberQuotientEquivQuotientMapComap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) :
    let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
    ((Localization.AtPrime q.asIdeal) ⧸
        Ideal.map (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal))
          (maximalIdeal (Localization.AtPrime p.asIdeal))) ≃+*
      ((Localization.AtPrime q.asIdeal) ⧸
        Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal) := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  -- Normalize the quotient ideal once so later transport lemmas can target the canonical
  -- `Ideal.map (algebraMap R S_q) (q ∩ R)` presentation directly.
  exact Ideal.quotEquivOfEq
    (localizationAtPrime_map_maximalIdeal_eq_map_comap (R := R) (S := S) q)

/-- Helper for Lemma 15.41.4 (Composition of regular maps): a regular map with regular source and
Noetherian target has regular target. -/
lemma isRegularRing_of_regular_map_of_isRegularRing
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hRS : (algebraMap R S).IsRegularRingMap)
    [IsNoetherianRing S] [IsRegularRing R] :
    IsRegularRing S := by
  let _ : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hRS.toFlat
  refine ⟨fun p ↦ ?_⟩
  let I := p.asIdeal
  have hI_ne_top : I.height ≠ ⊤ :=
    Ideal.height_ne_top (Ideal.IsPrime.ne_top inferInstance)
  let k := I.height.toNat
  have hk : I.primeHeight ≤ k := by
    -- Choose the Serre index from the height of the target prime so the local criterion applies.
    simpa [Ideal.height_eq_primeHeight, k] using (ENat.coe_toNat hI_ne_top).symm.le
  letI : SerreConditionR R k := IsRegularRing.serreConditionR k
  letI : SerreConditionR S k :=
    by
      -- Ascend Serre's condition along the flat map using regularity of every fiber.
      exact serreConditionR_of_flat_of_fiber (R := R) (S := S) (k := k) fun q ↦ by
        have hA : (algebraMap R S).toAlgebra = (inferInstance : Algebra R S) := by
          apply Algebra.algebra_ext
          intro x
          rfl
        have hfiber : IsRegularRing (q.asIdeal.Fiber S) :=
          fiber_isRegularRing_of_algebra_eq
            (R := R)
            (S := S)
            (p := q)
            (A₁ := (algebraMap R S).toAlgebra)
            (A₂ := (inferInstance : Algebra R S))
            hA <| by
              simpa using hRS.isRegularRing_fiber q
        let _ : IsRegularRing (q.asIdeal.Fiber S) := hfiber
        exact IsRegularRing.serreConditionR k
  -- The target localization at `p` is regular once `(R_k)` is known up to the height of `p`.
  exact SerreConditionR.isRegularLocalRing_localizationAtPrime p hk

/- Domain triage:
- primary domain: regular ring maps and composition through fiberwise geometric regularity in
  commutative algebra;
- sampled owner declarations of the same kind:
  `IsRegularRingMap`,
  `IsGeometricallyRegular`,
  `baseChange_of_essFiniteType`,
  `isRegularLocalRing_of_flat_localHom_of_regular_closedFiber`;
- best owner abstraction: `IsRegularRingMap` on composable ring homomorphisms
  `f : A →+* B` and `g : B →+* C`, with `IsGeometricallyRegular` supplying the canonical owner on
  each fiber over a residue field;
- primitive data: the ring homs `f` and `g`, regularity of `f` and `g`, and the Noetherianity
  hypothesis on the fibers `p.asIdeal.Fiber C` of the composite `g.comp f`;
- derived API: field-valued base change of regular maps and the local regularity criterion for flat
  local maps with regular closed fiber.

Layering:
- `comp_of_noetherianFibers` is `source-facing`;
- the core/canonical owners are `IsRegularRingMap` and `IsGeometricallyRegular`;
- the Noetherian-fiber hypothesis is auxiliary input, not a new owner-level wrapper.
-/

-- Proof sketch: for each prime `p : PrimeSpectrum A` and each finite purely inseparable extension
-- `κ(p) ⊂ k`, base change along `A → k` using
-- `baseChange_of_essFiniteType` to reduce to the case where the
-- source is the field `k`. Then `k ⊗[A] B` is regular because `A → B` is regular, and
-- `k ⊗[A] C` is Noetherian by the fiber hypothesis. The induced map `k ⊗[A] B → k ⊗[A] C` is
-- regular because `B → C` is regular, so Lemma `10.112.8` upgrades regularity of the source and
-- of the fibers to regularity of `k ⊗[A] C`, which is exactly the geometric regularity needed for
-- `A → C`.
/-- Lemma 15.41.4 (Composition of regular maps): let `f : A →+* B` and `g : B →+* C` be regular
ring maps. If every fiber ring `p.asIdeal.Fiber C = C ⊗[A] κ(p)` of `g.comp f : A →+* C` is
Noetherian, then `g.comp f` is a regular ring map. -/
theorem comp_of_noetherianFibers (hf : f.IsRegularRingMap) (hg : g.IsRegularRingMap)
    (hfiber_noetherian :
      let _ : Algebra A C := (g.comp f).toAlgebra
      ∀ p : PrimeSpectrum A, IsNoetherianRing (p.asIdeal.Fiber C)) :
    (g.comp f).IsRegularRingMap := by
  let _ : Algebra A B := f.toAlgebra
  let _ : Algebra B C := g.toAlgebra
  let _ : Algebra A C := (g.comp f).toAlgebra
  let _ : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  refine
    (RingHom.isRegularRingMap_iff_flat_and_geometricallyRegular_fiber
      (f := g.comp f)).mpr ?_
  constructor
  · -- Regular maps are flat, and flatness is stable under composition.
    exact RingHom.Flat.comp hf.toFlat hg.toFlat
  · intro p
    -- Route correction: stay on the source-proof route by testing geometric regularity after an
    -- essentially finite type residue-field extension `K / κ(p)`.
    rw [Algebra.isGeometricallyRegular_iff_forall_essFiniteType_fieldExtension_tensorBaseChange_isRegularRing]
    intro K _ _ _
    let _ : Algebra A K :=
      RingHom.toAlgebra
        ((algebraMap p.asIdeal.ResidueField K).comp (algebraMap A p.asIdeal.ResidueField))
    let _ : IsScalarTower A p.asIdeal.ResidueField K := IsScalarTower.of_algebraMap_eq' rfl
    let _ : Algebra.EssFiniteType A p.asIdeal.ResidueField := inferInstance
    let _ : Algebra.EssFiniteType A K :=
      Algebra.EssFiniteType.comp A p.asIdeal.ResidueField K
    have hKB :
        IsRegularRing (K ⊗[A] B) := by
      -- First handle the source tensor factor by base changing `A → B` to `K`.
      simpa using field_baseChange_source_isRegularRing (f := f) (K := K) hf
    have hKC_noetherian :
        IsNoetherianRing (K ⊗[A] C) := by
      -- Then carry the Noetherian fiber hypothesis to the same tensor model.
      simpa using
        field_baseChange_target_isNoetherianRing
          (f := f) (g := g) (p := p) (K := K) hfiber_noetherian
    let eKC :
        K ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber C ≃+* K ⊗[A] C := by
      -- This is the canonical cancellation equivalence from the fiber tensor model back to
      -- the ambient base change used for the regular-map argument.
      simpa using
        (Algebra.TensorProduct.cancelBaseChange A p.asIdeal.ResidueField
          p.asIdeal.ResidueField K C).toRingEquiv
    let S := K ⊗[A] B
    let _ : CommRing S := inferInstance
    let _ : Algebra B S := Algebra.TensorProduct.rightAlgebra
    let _ : Algebra B C := g.toAlgebra
    let _ : CommRing (S ⊗[B] C) := inferInstance
    have hSD :
        (algebraMap S (S ⊗[B] C)).IsRegularRingMap := by
      -- Base change `B → C` along the source tensor algebra `S`.
      simpa [S] using
        field_baseChange_target_regular_map
          (f := f) (g := g) (K := K) hg
    let _ : IsRegularRing S := hKB
    let D := S ⊗[B] C
    let _ : CommRing D := inferInstance
    let _ : Algebra S D := Algebra.TensorProduct.leftAlgebra
    let _ : Algebra C D := Algebra.TensorProduct.rightAlgebra
    let e : D ≃+* K ⊗[A] C :=
      (Algebra.IsPushout.cancelBaseChangeAlg A K B S C).toRingEquiv
    let _ : IsNoetherianRing D :=
      isNoetherianRing_of_ringEquiv (K ⊗[A] C) e.symm
    have hD_regular : IsRegularRing D := by
      -- First prove regularity on the pushout model where `B → C` was base changed directly.
      exact isRegularRing_of_regular_map_of_isRegularRing (R := S) (S := D) hSD
    let _ : IsRegularRing D := hD_regular
    let φ : K ⊗[A] C →+* D := e.symm.toRingHom
    have hφff : φ.FaithfullyFlat := RingHom.FaithfullyFlat.of_bijective e.symm.bijective
    have hKC_regular : IsRegularRing (K ⊗[A] C) := by
      -- Descend regularity from the pushout model `D` to the ambient tensor model `K ⊗[A] C`.
      exact (isRegularRing_of_faithfullyFlat (f := φ) hφff : IsRegularRing (K ⊗[A] C))
    let _ : IsRegularRing (K ⊗[A] C) := hKC_regular
    -- Then descend regularity across the canonical pushout equivalence to the target tensor model.
    exact
      isRegularRing_of_faithfullyFlat eKC.toRingHom
        (RingHom.FaithfullyFlat.of_bijective eKC.bijective)

end

end RingHom.IsRegularRingMap
