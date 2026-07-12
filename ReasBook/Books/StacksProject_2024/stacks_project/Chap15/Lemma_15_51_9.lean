import Mathlib
import StacksProject_2024.Chap10.Lemma_10_43_2
import StacksProject_2024.Chap10.Lemma_10_43_7
import StacksProject_2024.Chap10.Lemma_10_163_6
import StacksProject_2024.Chap10.Lemma_10_164_2
import StacksProject_2024.Chap10.Lemma_10_164_4
import StacksProject_2024.Chap10.Lemma_10_44_4
import StacksProject_2024.Chap10.Lemma_10_43_9
import StacksProject_2024.Chap10.Lemma_10_166_1
import StacksProject_2024.Chap15.Lemma_15_41_3_Regular_maps_and_base_change
import StacksProject_2024.Chap15.Lemma_15_41_7
import StacksProject_2024.Chap15.Lemma_15_42_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open IsLocalRing

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

/-- Helper for Lemma 15.51.9: a field-algebra property assigns a proposition to each algebra over
a field. -/
abbrev FieldAlgebraProperty : Type (u + 1) :=
  ∀ (k A : Type u), [Field k] → [CommRing A] → [Algebra k A] → Prop

namespace FieldAlgebraProperty

/-- Helper for Lemma 15.51.9: property `(A)` is stability under finitely generated base change of
the ground field. -/
class HasPropertyA (P : FieldAlgebraProperty) : Prop where
  /-- Base change along a finitely generated field extension preserves `P`. -/
  baseChange (k A K : Type u) [Field k] [CommRing A] [Algebra k A] [IsNoetherianRing A]
      [Field K] [Algebra k K] [Algebra.EssFiniteType k K] (hA : P k A) :
      P K (K ⊗[k] A)

/-- Helper for Lemma 15.51.9: property `(B)` is the localization criterion over a fixed ground
field. -/
class HasPropertyB (P : FieldAlgebraProperty) : Prop where
  /-- The prime-local criterion for `P`. -/
  localizationCriterion (k A : Type u) [Field k] [CommRing A] [Algebra k A]
      [IsNoetherianRing A] :
      P k A ↔ ∀ p : PrimeSpectrum A, P k (Localization.AtPrime p.asIdeal)

/-- Helper for Lemma 15.51.9: property `(C)` is ascent on fibers along regular morphisms. -/
class HasPropertyC (P : FieldAlgebraProperty) : Prop where
  /-- Property `(C)` ascends from fibers of `A → B` to fibers of `A → C`. -/
  regularAscent (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [(algebraMap B C).IsRegularRingMap]
      (hB : ∀ q : PrimeSpectrum A, P q.asIdeal.ResidueField (q.asIdeal.Fiber B))
      (q : PrimeSpectrum A) :
      P q.asIdeal.ResidueField (q.asIdeal.Fiber C)

/-- Helper for Lemma 15.51.9: property `(D)` is faithfully flat descent on closed fibers of local
rings. -/
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

/-- Helper for Lemma 15.51.9: property `(E)` is invariance under separable algebraic extension of
the ground field. -/
class HasPropertyE (P : FieldAlgebraProperty) : Prop where
  /-- Changing the ground field along a separable algebraic extension preserves `P`. -/
  separableBaseChange (k k' A : Type u) [Field k] [Field k'] [CommRing A]
      [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
      [Algebra.IsSeparable k k'] (hA : P k A) :
      P k' A

/-- Helper for Lemma 15.51.9: the Chapter 15 package of properties `(A)` through `(E)`. -/
class HasPropertiesABCDE (P : FieldAlgebraProperty) : Prop
    extends P.HasPropertyA, P.HasPropertyB, P.HasPropertyC, P.HasPropertyD, P.HasPropertyE

end FieldAlgebraProperty

namespace Algebra

/- Domain triage:
- primary domain: geometrically reduced algebras over fields and the Chapter 15 formal-fiber
  axioms for field-algebra properties;
- sampled owner declarations:
  `Algebra.IsGeometricallyReduced`,
  `IsRegularRingMap`,
  `RingHom.FaithfullyFlat`,
  `isReduced_of_faithfullyFlat`,
  `FieldAlgebraProperty.HasPropertyA`,
  `FieldAlgebraProperty.HasPropertyB`,
  `FieldAlgebraProperty.HasPropertyC`,
  `FieldAlgebraProperty.HasPropertiesABCDE`,
  `isGeometricallyReduced_iff_of_isSeparable`;
- best owner abstraction: the public owner is the Chapter 15 package
  `FieldAlgebraProperty.HasPropertiesABCDE`, specialized directly to the canonical
  field-algebra predicate `fun k R ↦ fun [Field k] [CommRing R] [Algebra k R] ↦
    IsGeometricallyReduced k R`;
- source/core/bridge triage:
  clauses `(1)` through `(5)` are the source-facing companions, while the chapter-level
  `FieldAlgebraProperty.HasPropertiesABCDE` instance is the core/canonical owner interface.

Primitive data are the ambient field/ring maps and the fiber hypotheses. Reducedness after
tensoring, localization stability, regular/faithfully-flat fiber transfer, and separable-base-field
invariance stay in derived owner API rather than being repackaged by a local wrapper.
-/

/-- The canonical `FieldAlgebraProperty` bridge for geometric reducedness. -/
abbrev IsGeometricallyReducedProperty : FieldAlgebraProperty :=
  fun k R ↦ fun [Field k] [CommRing R] [Algebra k R] ↦ IsGeometricallyReduced k R

-- Proof sketch: a finitely generated field extension is built from a purely transcendental
-- extension and a finite algebraic extension. Polynomial extensions and localizations preserve
-- geometric reducedness, and algebraic field extensions preserve reducedness after tensoring with
-- a geometrically reduced algebra.
/-- Lemma 15.51.9 (1): geometric reducedness is preserved after base change along a finitely
generated field extension. -/
theorem isGeometricallyReduced_baseChange_of_finitelyGeneratedFieldExtension
    {k : Type u} {K : Type u} {R : Type u}
    [Field k] [Field K] [CommRing R] [Algebra k K] [Algebra k R] [Algebra.EssFiniteType k K]
    [IsGeometricallyReduced k R] :
    IsGeometricallyReduced K (K ⊗[k] R) := by
  -- Test geometric reducedness of the base change against an arbitrary further field extension.
  rw [isGeometricallyReduced_iff_forall_isReduced_tensorProduct]
  intro L _ _
  letI : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  letI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
  -- Cancel the intermediate base change `K` to compare with the original `k`-geometric test ring.
  let e : L ⊗[K] (K ⊗[k] R) ≃ₐ[K] L ⊗[k] R :=
    Algebra.TensorProduct.cancelBaseChange k K K L R
  letI : IsReduced (L ⊗[k] R) :=
    (isGeometricallyReduced_iff_forall_isReduced_tensorProduct.mp
      (inferInstance : IsGeometricallyReduced k R)) L
  exact isReduced_of_injective e.toRingHom e.injective

section

variable {k : Type u} {R : Type u} [Field k] [CommRing R] [Algebra k R]

/-- Helper for Lemma 15.51.9: a Noetherian ring is reduced once all of its prime localizations are
reduced. -/
lemma isReduced_of_forall_prime_localization_isReduced [IsNoetherianRing R]
    (hlocal : ∀ p : PrimeSpectrum R, IsReduced (Localization.AtPrime p.asIdeal)) :
    IsReduced R := by
  classical
  refine ⟨fun x hxnil ↦ ?_⟩
  rcases hxnil with ⟨n, hn⟩
  by_contra hx
  let I : Ideal R := Ideal.torsionOf R R x
  -- Choose a maximal ideal above the annihilator ideal of `x`, then a minimal prime under it.
  have hIproper : I ≠ ⊤ := by
    intro htop
    have hmem : (1 : R) ∈ I := by
      rw [htop]
      simp
    rw [Ideal.mem_torsionOf_iff] at hmem
    have hxzero : x = 0 := by
      simpa using hmem
    exact hx hxzero
  obtain ⟨m, hmmax, hIm⟩ := Ideal.exists_le_maximal I hIproper
  let J : Ideal R := m
  letI : J.IsPrime := hmmax.isPrime
  obtain ⟨q, hqmin, hqJ⟩ := Ideal.exists_minimalPrimes_le hIm
  change Minimal (fun p : Ideal R ↦ p.IsPrime ∧ I ≤ p) q at hqmin
  have hIq : I ≤ q := hqmin.prop.2
  let p : PrimeSpectrum R := ⟨q, Ideal.minimalPrimes_isPrime hqmin⟩
  letI : p.asIdeal.IsPrime := p.isPrime
  -- The chosen localization still sees `x` as nonzero because every denominator avoiding `q`
  -- lies outside the annihilator ideal.
  have hxp_nonzero : algebraMap R (Localization.AtPrime p.asIdeal) x ≠ 0 := by
    intro hzero
    obtain ⟨s, hs⟩ :=
      (IsLocalization.map_eq_zero_iff p.asIdeal.primeCompl
        (Localization.AtPrime p.asIdeal) x).mp hzero
    have hs_ann : (s : R) ∈ I := by
      rw [Ideal.mem_torsionOf_iff]
      simpa [smul_eq_mul] using hs
    have hsq : (s : R) ∈ q := hIq hs_ann
    exact s.2 hsq
  -- But the nilpotence relation survives in the localization, contradicting reducedness there.
  have hxpow : algebraMap R (Localization.AtPrime p.asIdeal) x ^ n = 0 := by
    simpa [map_pow] using congrArg (algebraMap R (Localization.AtPrime p.asIdeal)) hn
  letI : IsReduced (Localization.AtPrime p.asIdeal) := hlocal p
  exact hxp_nonzero (eq_zero_of_pow_eq_zero hxpow)

-- Proof sketch: geometric reducedness is defined by reducedness after tensoring with field
-- extensions. Reducedness is a local property of commutative rings, and localizing a
-- geometrically reduced algebra stays geometrically reduced, so the global ring is geometrically
-- reduced exactly when all of its prime localizations are.
/-- Lemma 15.51.9 (2): a Noetherian `k`-algebra is geometrically reduced if and only if all of its
prime localizations are geometrically reduced over `k`. -/
theorem isGeometricallyReduced_iff_forall_localization_atPrime [IsNoetherianRing R] :
    IsGeometricallyReduced k R ↔
      ∀ p : PrimeSpectrum R, IsGeometricallyReduced k (Localization.AtPrime p.asIdeal) := by
  constructor
  · intro h p
    -- Localization preserves geometric reducedness directly.
    exact isGeometricallyReduced_localization p.asIdeal.primeCompl h
  · intro hlocal
    -- First recover global reducedness from reducedness of all prime localizations.
    have hred : IsReduced R := by
      exact isReduced_of_forall_prime_localization_isReduced fun p ↦
        Algebra.isReduced_of_isGeometricallyReduced k
    -- Then invoke the minimal-prime localization criterion from Chapter 10.
    exact isGeometricallyReduced_of_forall_minimalPrime_localization hred fun p ↦ by
      exact hlocal ⟨p.1, Ideal.minimalPrimes_isPrime p.2⟩

end

section

variable {A : Type u} {B : Type u} {C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- Helper for Lemma 15.51.9: fibers of a Noetherian algebra over a prime of the base are
Noetherian. -/
private theorem fiber_isNoetherianRing {D : Type u} [CommRing D] [Algebra A D]
    [IsNoetherianRing D] (p : PrimeSpectrum A) :
    IsNoetherianRing (p.asIdeal.Fiber D) := by
  -- Commute the tensor factors so the fiber is viewed as an essentially finite type `B`-algebra.
  let _ : Algebra.EssFiniteType D (D ⊗[A] p.asIdeal.ResidueField) := inferInstance
  let _ : IsNoetherianRing (D ⊗[A] p.asIdeal.ResidueField) :=
    Algebra.EssFiniteType.isNoetherianRing D (D ⊗[A] p.asIdeal.ResidueField)
  exact
    isNoetherianRing_of_ringEquiv (D ⊗[A] p.asIdeal.ResidueField)
      (Algebra.TensorProduct.comm A p.asIdeal.ResidueField D).toRingEquiv.symm

/-- Helper for Lemma 15.51.9: the explicit source tensor model `B ⊗[A] κ(p)` identifies with the
actual fiber of `B` over `p`. -/
noncomputable abbrev explicit_fiber_model_algEquiv (p : PrimeSpectrum A) :
    let κ := p.asIdeal.ResidueField
    let _ : Algebra κ (B ⊗[A] κ) := Algebra.TensorProduct.rightAlgebra
    (B ⊗[A] κ) ≃ₐ[κ] p.asIdeal.Fiber B := by
  let κ := p.asIdeal.ResidueField
  -- Keep the `κ(p)`-algebra structure on the right tensor factor explicit.
  simpa [Ideal.Fiber] using (Algebra.TensorProduct.commRight A κ B).symm

/-- Helper for Lemma 15.51.9: tensoring the explicit source fiber model with `K` in the
`K ⊗[κ(p)] -` orientation identifies it with the tensor product of the actual fiber of `B`. -/
noncomputable abbrev explicit_fiber_tensor_source_ringEquiv (p : PrimeSpectrum A)
    {K : Type u} [Field K] [Algebra p.asIdeal.ResidueField K] :
    let κ := p.asIdeal.ResidueField
    let S₀ := B ⊗[A] κ
    let _ : CommRing S₀ := inferInstance
    let _ : Algebra κ S₀ := Algebra.TensorProduct.rightAlgebra
    (K ⊗[κ] S₀) ≃+* K ⊗[κ] p.asIdeal.Fiber B := by
  let κ := p.asIdeal.ResidueField
  let S₀ := B ⊗[A] κ
  let _ : CommRing S₀ := inferInstance
  let _ : Algebra κ S₀ := Algebra.TensorProduct.rightAlgebra
  -- Compare both tensor products in the same `K ⊗[κ] -` orientation before any factor swap.
  exact
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : K ≃ₐ[κ] K)
      (explicit_fiber_model_algEquiv (A := A) (B := B) p)).toRingEquiv

/-- Helper for Lemma 15.51.9: the explicit source fiber model over `p`. -/
private abbrev explicitFiberSource (p : PrimeSpectrum A) :=
  B ⊗[A] p.asIdeal.ResidueField

/-- Helper for Lemma 15.51.9: the explicit target fiber model over `p`. -/
private abbrev explicitFiberTarget (p : PrimeSpectrum A) :=
  explicitFiberSource (A := A) (B := B) p ⊗[B] C

/-- Helper for Lemma 15.51.9: the explicit source fiber model after base change along
`κ(p) → K`. -/
private abbrev explicitFiberSourceBaseChange (p : PrimeSpectrum A)
    (K : Type u) [Field K] [Algebra p.asIdeal.ResidueField K] :=
  explicitFiberSource (A := A) (B := B) p ⊗[p.asIdeal.ResidueField] K

/-- Helper for Lemma 15.51.9: the explicit target tensor model after base change along
`κ(p) → K`. -/
private abbrev explicitFiberTargetBaseChange (p : PrimeSpectrum A)
    (K : Type u) [Field K] [Algebra p.asIdeal.ResidueField K] :=
  explicitFiberSourceBaseChange (A := A) (B := B) p K ⊗[
    explicitFiberSource (A := A) (B := B) p] explicitFiberTarget (A := A) (B := B) (C := C) p

/-- Helper for Lemma 15.51.9: the explicit fiber base change of a regular map is again regular. -/
lemma fiber_regularRingMap [(algebraMap B C).IsRegularRingMap] (p : PrimeSpectrum A) :
    let κ := p.asIdeal.ResidueField
    let S₀ := B ⊗[A] κ
    let D₀ := S₀ ⊗[B] C
    let _ : Algebra B S₀ := Algebra.TensorProduct.leftAlgebra
    let _ : CommRing S₀ := inferInstance
    let _ : CommRing D₀ := inferInstance
    let _ : Algebra S₀ D₀ := Algebra.TensorProduct.leftAlgebra
    (algebraMap S₀ D₀).IsRegularRingMap := by
  let κ := p.asIdeal.ResidueField
  let S₀ := B ⊗[A] κ
  let D₀ := S₀ ⊗[B] C
  letI : Algebra B S₀ := Algebra.TensorProduct.leftAlgebra
  letI : CommRing S₀ := inferInstance
  letI : CommRing D₀ := inferInstance
  letI : Algebra S₀ D₀ := Algebra.TensorProduct.leftAlgebra
  letI : Algebra C D₀ := Algebra.TensorProduct.rightAlgebra
  -- Route correction: prove regularity directly on the explicit fiber model `S₀`, where the
  -- standard essentially-finite-type base-change theorem applies without any fiber transport.
  simpa [κ, S₀, D₀] using
    RingHom.IsRegularRingMap.baseChange_of_essFiniteType
      (R := B) (R' := S₀) (Λ := C) (inferInstance : (algebraMap B C).IsRegularRingMap)

/-- Helper for Lemma 15.51.9: after a finite purely inseparable residue-field extension, the
fiber regular map remains regular on the explicit tensor-product model. -/
lemma fiber_base_changed_regularRingMap [(algebraMap B C).IsRegularRingMap] (p : PrimeSpectrum A)
    {K : Type u} [Field K] [Algebra p.asIdeal.ResidueField K]
    [FiniteDimensional p.asIdeal.ResidueField K] [IsPurelyInseparable p.asIdeal.ResidueField K] :
    let κ := p.asIdeal.ResidueField
    let S₀ := B ⊗[A] κ
    let D₀ := S₀ ⊗[B] C
    let U₀ := S₀ ⊗[κ] K
    let _ : CommRing S₀ := inferInstance
    let _ : CommRing D₀ := inferInstance
    let _ : CommRing U₀ := inferInstance
    let _ : Algebra B S₀ := Algebra.TensorProduct.leftAlgebra
    let _ : Algebra κ S₀ := Algebra.TensorProduct.rightAlgebra
    let _ : Algebra S₀ U₀ := Algebra.TensorProduct.leftAlgebra
    let _ : Algebra S₀ D₀ := Algebra.TensorProduct.leftAlgebra
    let _ : Algebra U₀ (U₀ ⊗[S₀] D₀) := Algebra.TensorProduct.leftAlgebra
    (algebraMap U₀ (U₀ ⊗[S₀] D₀)).IsRegularRingMap := by
  let κ := p.asIdeal.ResidueField
  let S₀ := B ⊗[A] κ
  let D₀ := S₀ ⊗[B] C
  let U₀ := S₀ ⊗[κ] K
  letI : CommRing S₀ := inferInstance
  letI : CommRing D₀ := inferInstance
  letI : CommRing U₀ := inferInstance
  letI : Algebra B S₀ := Algebra.TensorProduct.leftAlgebra
  letI : Algebra κ S₀ := Algebra.TensorProduct.rightAlgebra
  letI : Algebra S₀ U₀ := Algebra.TensorProduct.leftAlgebra
  letI : Algebra S₀ D₀ := Algebra.TensorProduct.leftAlgebra
  letI : Algebra U₀ (U₀ ⊗[S₀] D₀) := Algebra.TensorProduct.leftAlgebra
  have hSD : (algebraMap S₀ D₀).IsRegularRingMap :=
    fiber_regularRingMap (A := A) (B := B) (C := C) p
  -- After fixing the explicit fiber model, clause `(C)` needs only one more base change
  -- along the purely inseparable extension `κ(p) → K`.
  simpa [κ, S₀, D₀, U₀] using
    RingHom.IsRegularRingMap.baseChange_of_essFiniteType
      (R := S₀) (R' := U₀) (Λ := D₀) hSD

/-- Helper for Lemma 15.51.9: the explicit target fiber model identifies with the actual fiber of
`C` over `p`. -/
noncomputable abbrev explicit_target_fiber_algEquiv (p : PrimeSpectrum A) :
    explicitFiberTarget (A := A) (B := B) (C := C) p ≃ₐ[p.asIdeal.ResidueField] p.asIdeal.Fiber C := by
  let κ := p.asIdeal.ResidueField
  let S₀ := explicitFiberSource (A := A) (B := B) p
  let D₀ := explicitFiberTarget (A := A) (B := B) (C := C) p
  letI : CommRing S₀ := inferInstance
  letI : CommRing D₀ := inferInstance
  letI : Algebra B S₀ := Algebra.TensorProduct.leftAlgebra
  letI : Algebra κ S₀ := Algebra.TensorProduct.rightAlgebra
  letI : Algebra S₀ D₀ := Algebra.TensorProduct.leftAlgebra
  letI : Algebra C D₀ := Algebra.TensorProduct.rightAlgebra
  -- This is the second pushout cancellation in the explicit tensor-model proof.
  simpa [Ideal.Fiber] using
    (Algebra.IsPushout.cancelBaseChangeAlg A κ B S₀ C)

/-- Helper for Lemma 15.51.9: the explicit `K`-base change of the fiber model identifies with the
corresponding `K`-base change of the actual fiber of `C` after the standard pushout
cancellations. -/
noncomputable def fiber_tensor_compare_ringEquiv (p : PrimeSpectrum A)
    (K : Type u) [Field K] [Algebra p.asIdeal.ResidueField K] :
    explicitFiberTargetBaseChange (A := A) (B := B) (C := C) p K ≃+*
      (K ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber C) := by
  let κ := p.asIdeal.ResidueField
  let S₀ := explicitFiberSource (A := A) (B := B) p
  let D₀ := explicitFiberTarget (A := A) (B := B) (C := C) p
  let U₀ := explicitFiberSourceBaseChange (A := A) (B := B) p K
  letI : CommRing S₀ := inferInstance
  letI : CommRing D₀ := inferInstance
  letI : CommRing U₀ := inferInstance
  letI : Algebra B S₀ := Algebra.TensorProduct.leftAlgebra
  letI : Algebra κ S₀ := Algebra.TensorProduct.rightAlgebra
  letI : Algebra S₀ D₀ := Algebra.TensorProduct.leftAlgebra
  letI : Algebra C D₀ := Algebra.TensorProduct.rightAlgebra
  letI : Algebra S₀ U₀ := Algebra.TensorProduct.leftAlgebra
  let e₁ : (U₀ ⊗[S₀] D₀) ≃+* K ⊗[κ] D₀ :=
    (Algebra.IsPushout.cancelBaseChangeAlg κ K S₀ U₀ D₀).toRingEquiv
  let e₂κ : D₀ ≃ₐ[κ] p.asIdeal.Fiber C :=
    explicit_target_fiber_algEquiv (A := A) (B := B) (C := C) p
  let e₂ : K ⊗[κ] D₀ ≃+* K ⊗[κ] p.asIdeal.Fiber C :=
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : K ≃ₐ[κ] K)
      e₂κ).toRingEquiv
  -- Compare first with the explicit pushout model, then cancel the target fiber itself.
  exact e₁.trans e₂

/-- Helper for Lemma 15.51.9: the explicit tensor-model target is reduced once the source is
reduced and the base-changed fiber map is regular. -/
lemma explicit_fiber_source_isReduced [IsNoetherianRing A] [IsNoetherianRing B]
    (p : PrimeSpectrum A)
    (hfiber : IsGeometricallyReduced p.asIdeal.ResidueField (p.asIdeal.Fiber B))
    {K : Type u} [Field K] [Algebra p.asIdeal.ResidueField K]
    [FiniteDimensional p.asIdeal.ResidueField K] [IsPurelyInseparable p.asIdeal.ResidueField K] :
    IsReduced (explicitFiberSourceBaseChange (A := A) (B := B) p K) := by
  let κ := p.asIdeal.ResidueField
  let S₀ := explicitFiberSource (A := A) (B := B) p
  let U₀ := explicitFiberSourceBaseChange (A := A) (B := B) p K
  let U₁ := K ⊗[κ] S₀
  letI : CommRing S₀ := inferInstance
  letI : CommRing U₀ := inferInstance
  letI : CommRing U₁ := inferInstance
  letI : Algebra κ S₀ := Algebra.TensorProduct.rightAlgebra
  have hActualSource : IsReduced (K ⊗[κ] p.asIdeal.Fiber B) :=
    (isGeometricallyReduced_iff_isReduced_tensorProduct_finitePurelyInseparable.mp hfiber) K
  letI : IsReduced (K ⊗[κ] p.asIdeal.Fiber B) := hActualSource
  have hExplicitSource₁ : IsReduced U₁ := by
    -- First move reducedness from the actual fiber to the explicit source tensor model.
    exact
      isReduced_of_injective
        (explicit_fiber_tensor_source_ringEquiv (A := A) (B := B) (p := p) (K := K)).toRingHom
        (explicit_fiber_tensor_source_ringEquiv (A := A) (B := B) (p := p) (K := K)).injective
  letI : IsReduced U₁ := hExplicitSource₁
  -- Route correction: commute the tensor factors only after reducedness sits on the explicit
  -- source orientation `K ⊗[κ] S₀`.
  exact
    isReduced_of_injective
      (Algebra.TensorProduct.commRight κ K S₀).symm.toRingHom
      (Algebra.TensorProduct.commRight κ K S₀).symm.injective

/-- Helper for Lemma 15.51.9: reducedness transports across a ring equivalence. -/
private theorem isReduced_of_ringEquiv
    {R : Type u} {S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) [IsReduced R] :
    IsReduced S := by
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

/-- Helper for Lemma 15.51.9: the explicit tensor-model target is reduced once the source is
reduced and the base-changed fiber map is regular. -/
lemma explicit_fiber_target_model_isReduced [IsNoetherianRing A] [IsNoetherianRing B]
    [IsNoetherianRing C] [(algebraMap B C).IsRegularRingMap] (p : PrimeSpectrum A)
    (hfiber : IsGeometricallyReduced p.asIdeal.ResidueField (p.asIdeal.Fiber B))
    {K : Type u} [Field K] [Algebra p.asIdeal.ResidueField K]
    [FiniteDimensional p.asIdeal.ResidueField K] [IsPurelyInseparable p.asIdeal.ResidueField K] :
    IsReduced (explicitFiberTargetBaseChange (A := A) (B := B) (C := C) p K) := by
  let κ := p.asIdeal.ResidueField
  let S₀ := explicitFiberSource (A := A) (B := B) p
  let D₀ := explicitFiberTarget (A := A) (B := B) (C := C) p
  let U₀ := explicitFiberSourceBaseChange (A := A) (B := B) p K
  let T₀ := explicitFiberTargetBaseChange (A := A) (B := B) (C := C) p K
  letI : CommRing S₀ := inferInstance
  letI : CommRing D₀ := inferInstance
  letI : CommRing U₀ := inferInstance
  letI : CommRing T₀ := inferInstance
  letI : Algebra B S₀ := Algebra.TensorProduct.leftAlgebra
  letI : Algebra κ S₀ := Algebra.TensorProduct.rightAlgebra
  letI : Algebra S₀ D₀ := Algebra.TensorProduct.leftAlgebra
  letI : Algebra C D₀ := Algebra.TensorProduct.rightAlgebra
  letI : Algebra S₀ U₀ := Algebra.TensorProduct.leftAlgebra
  letI : Algebra U₀ T₀ := Algebra.TensorProduct.leftAlgebra
  letI : IsNoetherianRing S₀ := Algebra.EssFiniteType.isNoetherianRing B S₀
  letI : IsNoetherianRing U₀ := Algebra.EssFiniteType.isNoetherianRing S₀ U₀
  let T₁ := p.asIdeal.Fiber C ⊗[κ] K
  letI : CommRing T₁ := inferInstance
  letI : IsNoetherianRing (p.asIdeal.Fiber C) :=
    fiber_isNoetherianRing (A := A) (D := C) p
  letI : IsNoetherianRing T₁ :=
    Algebra.EssFiniteType.isNoetherianRing (p.asIdeal.Fiber C) T₁
  let eTargetNoeth : T₁ ≃+* (K ⊗[κ] p.asIdeal.Fiber C) :=
    (Algebra.TensorProduct.commRight κ K (p.asIdeal.Fiber C)).symm.toRingEquiv
  letI : IsNoetherianRing (K ⊗[κ] p.asIdeal.Fiber C) :=
    isNoetherianRing_of_ringEquiv T₁ eTargetNoeth
  let eCompare : T₀ ≃+* (K ⊗[κ] p.asIdeal.Fiber C) :=
    fiber_tensor_compare_ringEquiv (A := A) (B := B) (C := C) p K
  letI : IsNoetherianRing T₀ :=
    isNoetherianRing_of_ringEquiv (K ⊗[κ] p.asIdeal.Fiber C) eCompare.symm
  letI : IsReduced U₀ :=
    explicit_fiber_source_isReduced (A := A) (B := B) (p := p) (hfiber := hfiber) (K := K)
  have hbase : (algebraMap U₀ T₀).IsRegularRingMap := by
    -- Base change the explicit regular fiber map `S₀ → D₀` along `κ(p) → K`.
    simpa [κ, S₀, D₀, U₀, T₀] using
      fiber_base_changed_regularRingMap
        (A := A) (B := B) (C := C) (p := p) (K := K)
  letI : (algebraMap U₀ T₀).IsRegularRingMap := hbase
  -- Apply Lemma `15.42.1` on the explicit base-changed regular fiber map.
  exact Algebra.isReduced_of_regularRingMap (algebraMap U₀ T₀)

/-- Helper for Lemma 15.51.9: the explicit tensor-model target is reduced once the source is
reduced and the base-changed fiber map is regular. -/
lemma explicit_fiber_target_isReduced [IsNoetherianRing A] [IsNoetherianRing B]
    [IsNoetherianRing C] [(algebraMap B C).IsRegularRingMap] (p : PrimeSpectrum A)
    (hfiber : IsGeometricallyReduced p.asIdeal.ResidueField (p.asIdeal.Fiber B))
    {K : Type u} [Field K] [Algebra p.asIdeal.ResidueField K]
    [FiniteDimensional p.asIdeal.ResidueField K] [IsPurelyInseparable p.asIdeal.ResidueField K] :
    IsReduced (K ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber C) := by
  let κ := p.asIdeal.ResidueField
  let T₀ := explicitFiberTargetBaseChange (A := A) (B := B) (C := C) p K
  letI : CommRing T₀ := inferInstance
  let e : T₀ ≃+* (K ⊗[κ] p.asIdeal.Fiber C) :=
    fiber_tensor_compare_ringEquiv (A := A) (B := B) (C := C) p K
  letI : IsReduced T₀ :=
    explicit_fiber_target_model_isReduced
      (A := A) (B := B) (C := C) (p := p) (hfiber := hfiber) (K := K)
  -- Transport reducedness back from the explicit tensor model to the actual tensor product of the
  -- target fiber.
  exact isReduced_of_ringEquiv e

-- Proof sketch: fix `p : Spec(A)` and base change the regular map `B → C` along `κ(p)`. The
-- induced map on fibers is regular. Since the fiber of `A → B` over `p` is geometrically reduced,
-- its base change to an algebraic closure of `κ(p)` is reduced; then Lemma `15.42.1` applied to
-- the regular map on base-changed fibers shows the corresponding base change of the fiber of
-- `A → C` is reduced, which is exactly geometric reducedness.
/-- Lemma 15.51.9 (3): if `A → B → C` are maps of commutative rings, `A → B` is flat, every fiber
of `A → B` is geometrically reduced, and `B → C` is a regular ring map, then every fiber of
`A → C` is geometrically reduced. -/
theorem fibers_areGeometricallyReduced_of_flat_of_regular [IsNoetherianRing A]
    [IsNoetherianRing B] [IsNoetherianRing C] [Module.Flat A B]
    [(algebraMap B C).IsRegularRingMap]
    (hAB :
      ∀ p : PrimeSpectrum A, IsGeometricallyReduced p.asIdeal.ResidueField (p.asIdeal.Fiber B)) :
    ∀ p : PrimeSpectrum A, IsGeometricallyReduced p.asIdeal.ResidueField (p.asIdeal.Fiber C) := by
  intro p
  -- Route correction: clause `(C)` is the finite purely inseparable reducedness test on the
  -- target fiber, closed by the explicit tensor-model ascent lemma above.
  exact
    (isGeometricallyReduced_iff_isReduced_tensorProduct_finitePurelyInseparable
      (k := p.asIdeal.ResidueField) (S := p.asIdeal.Fiber C)).2 <| by
        intro K _ _ _ _
        -- Evaluate the target fiber on the chosen purely inseparable test field.
        exact
          explicit_fiber_target_isReduced
            (A := A) (B := B) (C := C) (p := p) (hfiber := hAB p) (K := K)

/-- Helper for Lemma 15.51.9: faithful flatness of `B → C` induces a faithfully flat map on the
fiber over any prime of `A`. -/
lemma fiber_faithfullyFlat
    (p : PrimeSpectrum A) (hBC_ff : (algebraMap B C).FaithfullyFlat) :
    let S := p.asIdeal.Fiber B
    let D := S ⊗[B] C
    (algebraMap S D).FaithfullyFlat := by
  let S := p.asIdeal.Fiber B
  let D := S ⊗[B] C
  -- This is exactly the faithfully flat fiber-base-change theorem from Lemma 15.41.7.
  simpa [S, D, RingHom.IsRegularRingMap.fiberBaseChange] using
    (RingHom.IsRegularRingMap.fiber_baseChange_faithfullyFlat
      (A := A) (B := B) (C := C) hBC_ff p)

/-- Helper for Lemma 15.51.9: after tensoring a faithfully flat `κ`-algebra map by `K`,
reducedness descends from `K ⊗[κ] S` to `K ⊗[κ] R`. -/
theorem tensor_product_reduced_of_faithfullyFlat
    {κ R S : Type u} [Field κ] [CommRing R] [CommRing S]
    [Algebra κ R] [Algebra κ S] [Algebra R S]
    [Module.FaithfullyFlat R S]
    (hcomm : ∀ x : κ, algebraMap κ S x = (algebraMap R S) ((algebraMap κ R) x))
    (K : Type u) [Field K] [Algebra κ K]
    (hKS : IsReduced (K ⊗[κ] S)) :
    IsReduced (K ⊗[κ] R) := by
  letI : IsScalarTower κ R S := IsScalarTower.of_algebraMap_eq hcomm
  letI : Algebra R (K ⊗[κ] R) := Algebra.TensorProduct.rightAlgebra
  letI : IsReduced (K ⊗[κ] S) := hKS
  let D := (K ⊗[κ] R) ⊗[R] S
  letI : CommRing D := inferInstance
  letI : Algebra (K ⊗[κ] R) D := Algebra.TensorProduct.leftAlgebra
  letI : Algebra S D := Algebra.TensorProduct.rightAlgebra
  let f : (K ⊗[κ] R) →+* D := algebraMap (K ⊗[κ] R) D
  have hf : f.FaithfullyFlat := by
    -- Base change preserves faithful flatness at the tensor-product level.
    letI : Module.FaithfullyFlat (K ⊗[κ] R) D := inferInstance
    simpa [f] using
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance : f.FaithfullyFlat)
  let e : D ≃ₐ[K] (K ⊗[κ] S) :=
    Algebra.IsPushout.cancelBaseChangeAlg κ K R (K ⊗[κ] R) S
  have hD : IsReduced D := by
    -- The explicit tensor square is just the pushout model of `K ⊗[κ] S`.
    exact isReduced_of_injective e.toRingHom e.injective
  letI : IsReduced D := hD
  -- Descend reducedness along the faithfully flat tensor extension.
  exact isReduced_of_faithfullyFlat f hf

/-- Helper for Lemma 15.51.9: geometric reducedness descends from the fiber of `C` to the
corresponding fiber of `B` over a fixed prime along a faithfully flat map. -/
theorem fiber_isGeometricallyReduced_of_faithfullyFlat
    (p : PrimeSpectrum A) (hBC_ff : (algebraMap B C).FaithfullyFlat)
    (hTp : IsGeometricallyReduced p.asIdeal.ResidueField (p.asIdeal.Fiber C)) :
    IsGeometricallyReduced p.asIdeal.ResidueField (p.asIdeal.Fiber B) := by
  let κ := p.asIdeal.ResidueField
  let S := p.asIdeal.Fiber B
  let T := p.asIdeal.Fiber C
  letI : IsGeometricallyReduced κ T := hTp
  refine isGeometricallyReduced_iff_isReduced_tensorProduct_finitePurelyInseparable.2 ?_
  intro K _ _ _ _
  letI : Algebra B S := Algebra.TensorProduct.rightAlgebra
  let D := S ⊗[B] C
  letI : CommRing D := inferInstance
  letI : Algebra S D := Algebra.TensorProduct.leftAlgebra
  letI : Algebra C D := Algebra.TensorProduct.rightAlgebra
  let f : S →+* D := algebraMap S D
  have hf : f.FaithfullyFlat := by
    -- First pass from `B → C` to the explicit faithfully flat map on the chosen fiber.
    simpa [S, D, f] using fiber_faithfullyFlat (A := A) (B := B) (C := C) p hBC_ff
  let e₀ : D ≃ₐ[κ] T :=
    RingHom.IsRegularRingMap.fiber_baseChange_algEquiv (A := A) (B := B) (C := C) p
  let g₀ : D →+* T := e₀.toRingHom
  have hg₀ : g₀.FaithfullyFlat := by
    simpa [g₀] using
      (RingHom.FaithfullyFlat.of_bijective e₀.bijective : g₀.FaithfullyFlat)
  have hff₀ : (g₀.comp f).FaithfullyFlat := by
    -- The actual fiber map factors as the explicit base change followed by the comparison isomorphism.
    change (RingHom.comp g₀ f).FaithfullyFlat
    exact RingHom.FaithfullyFlat.stableUnderComposition f g₀ hf hg₀
  letI : Algebra S T := RingHom.toAlgebra (g₀.comp f)
  letI : Module.FaithfullyFlat S T :=
    RingHom.faithfullyFlat_algebraMap_iff.mp (by simpa [f, g₀] using hff₀)
  have hcomm :
      ∀ x : κ, algebraMap κ T x = (algebraMap S T) ((algebraMap κ S) x) := by
    intro x
    -- The comparison equivalence is an algebra equivalence over `κ(p)`.
    change algebraMap κ T x = e₀ (algebraMap κ D x)
    simpa using (e₀.commutes x).symm
  have hKT : IsReduced (K ⊗[κ] T) :=
    (isGeometricallyReduced_iff_isReduced_tensorProduct_finitePurelyInseparable.mp hTp) K
  -- Apply ordinary faithfully flat reducedness descent after tensoring with the test field `K`.
  exact
    tensor_product_reduced_of_faithfullyFlat
      (κ := κ) (R := S) (S := T) hcomm K hKT

-- Proof sketch: fix `p : Spec(A)` and base change the faithfully flat map `B → C` along `κ(p)`.
-- This gives a faithfully flat map of fiber rings. If the fiber of `A → C` over `p` is
-- geometrically reduced, then after tensoring with an algebraic closure of `κ(p)` the target
-- fiber is reduced. Lemma `10.164.2` descends reducedness along the faithfully flat map of these
-- base-changed fibers, giving geometric reducedness of the fiber of `A → B` over `p`.
/-- Lemma 15.51.9 (4): if `A → B → C` are maps of commutative rings, every fiber of `A → C` is
geometrically reduced, and `B → C` is faithfully flat, then every fiber of `A → B` is
geometrically reduced. -/
theorem fibers_areGeometricallyReduced_of_comp_of_faithfullyFlat
    (hBC_ff : (algebraMap B C).FaithfullyFlat)
    (hAC :
      ∀ p : PrimeSpectrum A, IsGeometricallyReduced p.asIdeal.ResidueField (p.asIdeal.Fiber C)) :
    ∀ p : PrimeSpectrum A, IsGeometricallyReduced p.asIdeal.ResidueField (p.asIdeal.Fiber B) := by
  intro p
  -- Apply the fixed-prime descent theorem on the chosen fiber.
  exact fiber_isGeometricallyReduced_of_faithfullyFlat (A := A) (B := B) (C := C) p hBC_ff (hAC p)

end

section

variable {k : Type u} {k' : Type u} {R : Type u}
variable [Field k] [Field k'] [CommRing R]
variable [Algebra k k'] [Algebra k' R] [Algebra k R] [IsScalarTower k k' R]

-- Proof sketch: this is exactly the separable-base-field invariance of geometric reducedness from
-- Lemma `10.43.9`; apply that result and take the forward implication.
/-- Lemma 15.51.9 (5): if `k' / k` is a separable algebraic field extension and `R` is
geometrically reduced over `k`, then `R` is geometrically reduced over `k'`. -/
theorem isGeometricallyReduced_of_separableAlgebraicExtension [Algebra.IsSeparable k k']
    [IsGeometricallyReduced k R] :
    IsGeometricallyReduced k' R :=
  (isGeometricallyReduced_iff_of_isSeparable : IsGeometricallyReduced k R ↔
    IsGeometricallyReduced k' R).1 inferInstance

-- Proof sketch: this repackages source-facing clause `(5)` as the Chapter 15 axiom `(E)` for the
-- canonical field-algebra property `fun k R ↦ IsGeometricallyReduced k R`.
/-- Lemma 15.51.9 (5), owner-form: geometric reducedness has property `(E)` in the Chapter 15
formal-fiber package. -/
theorem isGeometricallyReduced_hasPropertyE :
    IsGeometricallyReducedProperty.HasPropertyE := by
  refine ⟨?_⟩
  intro k k' R _ _ _ _ _ _ _ _ hR
  exact
    (isGeometricallyReduced_iff_of_isSeparable :
      IsGeometricallyReduced k R ↔ IsGeometricallyReduced k' R).1 hR

end

section

/-- Helper for Lemma 15.51.9: the maximal-ideal residue field of a local ring agrees with its
usual residue field. -/
private noncomputable abbrev maximalIdeal_residueField_equiv
    (R : Type u) [CommRing R] [IsLocalRing R] :
    (maximalIdeal R).ResidueField ≃+* ResidueField R :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).symm

/-- Helper for Lemma 15.51.9: the maximal-ideal residue-field comparison sends the canonical
maximal-ideal residue class of an element to the usual residue class. -/
private theorem maximalIdeal_residueField_equiv_apply_algebraMap
    (R : Type u) [CommRing R] [IsLocalRing R] (x : ResidueField R) :
    maximalIdeal_residueField_equiv R (algebraMap (ResidueField R) (maximalIdeal R).ResidueField x) =
      x := by
  change
    maximalIdeal_residueField_equiv R ((maximalIdeal_residueField_equiv R).symm x) = x
  exact (maximalIdeal_residueField_equiv R).apply_symm_apply x

/-- Helper for Lemma 15.51.9: the canonical residue-field comparison is an algebra equivalence
over the usual residue field. -/
private noncomputable abbrev maximalIdeal_residueField_algEquiv
    (R : Type u) [CommRing R] [IsLocalRing R] :
    (maximalIdeal R).ResidueField ≃ₐ[ResidueField R] ResidueField R :=
  AlgEquiv.ofRingEquiv
    (f := maximalIdeal_residueField_equiv R)
    (maximalIdeal_residueField_equiv_apply_algebraMap R)

/-- Helper for Lemma 15.51.9: geometric reducedness of the closed fiber is unchanged when the
ground field is rewritten from `ResidueField A` to `(maximalIdeal A).ResidueField`. -/
private theorem closedFiber_residueField_compare
    {A : Type u} {R : Type u} [CommRing A] [CommRing R]
    [IsLocalRing A] [Algebra A R] :
    IsGeometricallyReduced (ResidueField A) ((maximalIdeal A).Fiber R) ↔
      IsGeometricallyReduced (maximalIdeal A).ResidueField ((maximalIdeal A).Fiber R) := by
  let eκ :
      (maximalIdeal A).ResidueField ≃ₐ[ResidueField A] ResidueField A :=
    maximalIdeal_residueField_algEquiv A
  letI : Algebra.IsSeparable (ResidueField A) ((maximalIdeal A).ResidueField) :=
    AlgEquiv.Algebra.isSeparable eκ.symm
  -- The two base fields are canonically isomorphic, so separable invariance compares the two
  -- geometric reducedness predicates on the same closed fiber ring.
  exact isGeometricallyReduced_iff_of_isSeparable

-- Proof sketch: first descend the faithfully flat local map `B → C` to the induced faithfully
-- flat map on closed fibers over the residue field `κ(A)`. Then test geometric reducedness of the
-- source closed fiber by tensoring with arbitrary field extensions of `κ(A)` and descend
-- reducedness along that faithfully flat base change using Lemma `10.164.2`.
/-- Geometric reducedness descends on the closed fiber along a faithfully flat local extension. -/
theorem isGeometricallyReduced_closedFiberDescent
    {A : Type u} {B : Type u} {C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]
    (hBC : RingHom.FaithfullyFlat (algebraMap B C))
    (hC : IsGeometricallyReduced (ResidueField A) ((maximalIdeal A).Fiber C)) :
    IsGeometricallyReduced (ResidueField A) ((maximalIdeal A).Fiber B) := by
  let p : PrimeSpectrum A := ⟨maximalIdeal A, inferInstance⟩
  have hCκ :
      IsGeometricallyReduced (maximalIdeal A).ResidueField ((maximalIdeal A).Fiber C) :=
    (closedFiber_residueField_compare (A := A) (R := C)).mp hC
  have hBκ :
      IsGeometricallyReduced (maximalIdeal A).ResidueField ((maximalIdeal A).Fiber B) := by
    -- Route correction: first specialize primewise faithfully flat descent to the closed point,
    -- then only at the end rewrite the residue field back to `ResidueField A`.
    simpa [p] using
      fiber_isGeometricallyReduced_of_faithfullyFlat
        (A := A) (B := B) (C := C) p hBC (by simpa [p] using hCκ)
  exact (closedFiber_residueField_compare (A := A) (R := B)).mpr hBκ

-- Proof sketch: the five source-facing clauses above match the five fields of the canonical
-- Chapter 15 owner `FieldAlgebraProperty.HasPropertiesABCDE` for the property
-- `fun k R ↦ IsGeometricallyReduced k R`; only property `(B)` needs a symmetry to match the
-- owner's local-to-global orientation.
/-- Lemma 15.51.9 packages geometric reducedness into the canonical Chapter 15 owner for
field-algebra properties satisfying the formal-fiber axioms `(A)` through `(E)`. -/
instance isGeometricallyReduced_hasPropertiesABCDE :
    IsGeometricallyReducedProperty.HasPropertiesABCDE where
  baseChange := by
    intro k R K _ _ _ _ _ _ _ hR
    letI : IsGeometricallyReduced k R := hR
    exact isGeometricallyReduced_baseChange_of_finitelyGeneratedFieldExtension
  localizationCriterion := by
    intro k R _ _ _ _
    simpa using
      (isGeometricallyReduced_iff_forall_localization_atPrime :
        IsGeometricallyReduced k R ↔
          ∀ p : PrimeSpectrum R, IsGeometricallyReduced k (Localization.AtPrime p.asIdeal))
  regularAscent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hAB q
    exact fibers_areGeometricallyReduced_of_flat_of_regular hAB q
  closedFiberDescent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hBC hC
    exact isGeometricallyReduced_closedFiberDescent hBC hC
  separableBaseChange := by
    intro k k' R _ _ _ _ _ _ _ _ hR
    exact isGeometricallyReduced_hasPropertyE.separableBaseChange k k' R hR

end

end Algebra
