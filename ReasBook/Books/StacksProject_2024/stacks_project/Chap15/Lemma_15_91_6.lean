import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Localization.Away.Basic
import StacksProject_2024.stacks_project.Chap15.Definition_15_89_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_91_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open scoped IdealPowerTorsion

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R']

/- Domain-style sampling:
* primary domain: commutative algebra of the Beauville-Laszlo Cech sequence and principal-ideal
  power torsion.
* sampled owner declarations:
  `Module.primaryComponent_principalIdeal_eq_fPowerTorsion`,
  `ModuleCat.shortComplexOfCompEqZero`,
  `ShortComplex.ShortExact`,
  `principalPowerIdealImageQuotientMap`,
  `principalAdicCompletion`.
* owner abstraction: the canonical short-complex owner is `beauvilleLaszloCechSequence φ f`,
  while the source-facing Beauville-Laszlo owner
  `IsBeauvilleLaszloGlueingPairAlong φ f` packages the positive-power quotient comparison maps
  together with short exactness of that Cech sequence.
* primitive data: the ring map `φ : R →+* R'`, the element `f : R`, the positive-power quotient
  comparison maps, and the two Cech maps.
* derived API: the Cech short complex owner, the glueing-pair owner, the torsion comparison map,
  and the completion specialization.
-/

/-- The canonical map `R[f^∞] → R'[f^∞]` induced by the ring map `φ : R →+* R'`. -/
abbrev fPowerTorsionToExtension
    (φ : R →+* R') (f : R) :
    let _ : Algebra R R' := φ.toAlgebra
    (R[f^∞] : Submodule R R) →ₗ[R] (R'[f^∞] : Submodule R R') :=
  let _ : Algebra R R' := φ.toAlgebra
  show (R[f^∞] : Submodule R R) →ₗ[R] (R'[f^∞] : Submodule R R') from
    ((Algebra.linearMap R R').domRestrict
        (R[f^∞] : Submodule R R)).codRestrict
      (R'[f^∞] : Submodule R R') fun x ↦ by
      rcases (Submodule.mem_torsion'_iff (Submonoid.powers f) (x : R)).1 x.2 with ⟨a, hx⟩
      refine (Submodule.mem_torsion'_iff (Submonoid.powers f) ((Algebra.linearMap R R') x)).2 ?_
      refine ⟨a, ?_⟩
      have hx0 : (a : R) * (x : R) = 0 := by
        simpa [smul_eq_mul] using hx
      have hx' : (Algebra.linearMap R R') ((a : R) * (x : R)) = 0 := by
        simpa using congrArg (Algebra.linearMap R R') hx0
      simpa [Algebra.smul_def, map_mul] using hx'

/-- The left map `R → R' × R_f` in the Beauville-Laszlo Cech sequence attached to `φ`. -/
abbrev beauvilleLaszloCechLeftMap
    (φ : R →+* R') (f : R) :
    let _ : Algebra R R' := φ.toAlgebra
    R →ₗ[R] R' × Localization.Away f :=
  let _ : Algebra R R' := φ.toAlgebra
  show R →ₗ[R] R' × Localization.Away f from
    LinearMap.prod
      (Algebra.linearMap R R')
      (Algebra.linearMap R (Localization.Away f))

/-- The right map `R' × R_f → R'_f` in the Beauville-Laszlo Cech sequence attached to `φ`. -/
abbrev beauvilleLaszloCechRightMap
    (φ : R →+* R') (f : R) :
    let _ : Algebra R R' := φ.toAlgebra
    R' × Localization.Away f →ₗ[R] Localization.Away (algebraMap R R' f) :=
  let _ : Algebra R R' := φ.toAlgebra
  let left : R' × Localization.Away f →ₗ[R] Localization.Away (algebraMap R R' f) :=
    ((Algebra.linearMap R' (Localization.Away (algebraMap R R' f))).restrictScalars R).comp
      (LinearMap.fst R R' (Localization.Away f))
  let right : R' × Localization.Away f →ₗ[R] Localization.Away (algebraMap R R' f) :=
    ((Localization.awayMapₐ (Algebra.ofId R R') f).toLinearMap).comp
      (LinearMap.snd R R' (Localization.Away f))
  left - right

/-- The Beauville-Laszlo Cech maps form a complex. -/
theorem beauvilleLaszloCech_comp_eq_zero
    (φ : R →+* R') (f : R) :
    let _ : Algebra R R' := φ.toAlgebra
    (beauvilleLaszloCechRightMap φ f).comp (beauvilleLaszloCechLeftMap φ f) =
      (0 : R →ₗ[R] Localization.Away (algebraMap R R' f)) := by
  let _ : Algebra R R' := φ.toAlgebra
  -- Evaluate the composite on `x : R` and compare the two canonical maps into the overlap ring.
  apply LinearMap.ext
  intro x
  apply sub_eq_zero.mpr
  simp [beauvilleLaszloCechLeftMap]
  exact (AlgHom.commutes (Localization.awayMapₐ (Algebra.ofId R R') f) x).symm

/-- The Beauville-Laszlo Cech sequence attached to `φ : R →+* R'` and `f`, viewed in the
canonical owner `ShortComplex (ModuleCat R)`. -/
noncomputable abbrev beauvilleLaszloCechSequence
    (φ : R →+* R') (f : R) :
    let _ : Algebra R R' := φ.toAlgebra
    ShortComplex (ModuleCat R) :=
  let _ : Algebra R R' := φ.toAlgebra
  let α : R →ₗ[R] R' × Localization.Away f := beauvilleLaszloCechLeftMap φ f
  let β : R' × Localization.Away f →ₗ[R] Localization.Away (algebraMap R R' f) :=
    beauvilleLaszloCechRightMap φ f
  let h : β.comp α = 0 := by
    change (beauvilleLaszloCechRightMap φ f).comp (beauvilleLaszloCechLeftMap φ f) = 0
    exact beauvilleLaszloCech_comp_eq_zero φ f
  ModuleCat.shortComplexOfCompEqZero α β h

/-- The pair `(φ : R →+* R', f)` is a Beauville-Laszlo glueing pair when the induced maps
`R / (f^n) → R' / (φ(f)^n)` are bijective for all positive integers `n` and the canonical Cech
sequence `0 → R → R' × R_f → R'_f → 0` is short exact. -/
class IsBeauvilleLaszloGlueingPairAlong
    (φ : R →+* R') (f : R) : Prop where
  quotientMapBijective :
    ∀ n : ℕ+, Function.Bijective (principalPowerIdealImageQuotientMap φ f n)
  shortExact :
    let _ : Algebra R R' := φ.toAlgebra
    (beauvilleLaszloCechSequence φ f).ShortExact

section

variable (φ : R →+* R') (f : R)

/-- Helper for Lemma 15.91.6: an element of `R` is `f`-power torsion exactly when it maps to zero
in `R_f`. -/
theorem mem_fPowerTorsion_iff_away_eq_zero (x : R) :
    x ∈ (R[f^∞] : Submodule R R) ↔
      (Algebra.linearMap R (Localization.Away f)) x = 0 := by
  -- The source proof identifies the kernel of `R → R_f` with the `f`-power torsion submodule.
  rw [Submodule.mem_torsion'_iff (Submonoid.powers f) x]
  constructor
  · rintro ⟨a, ha⟩
    change x ∈ (LocalizedModule.mkLinearMap (Submonoid.powers f) R).ker
    exact (LocalizedModule.mem_ker_mkLinearMap_iff (S := Submonoid.powers f) (m := x)).2
      ⟨a, a.2, ha⟩
  · intro hx
    change x ∈ (LocalizedModule.mkLinearMap (Submonoid.powers f) R).ker at hx
    rcases (LocalizedModule.mem_ker_mkLinearMap_iff (S := Submonoid.powers f) (m := x)).1 hx with
      ⟨a, ha, hax⟩
    exact ⟨⟨a, ha⟩, hax⟩

/-- Helper for Lemma 15.91.6: an element of `R'` is `f`-power torsion over `R` exactly when its
image in the overlap localization `R'_f` vanishes. -/
theorem mem_fPowerTorsion_iff_overlap_eq_zero (y : R') :
    let _ : Algebra R R' := φ.toAlgebra
    y ∈ (R'[f^∞] : Submodule R R') ↔
      ((Algebra.linearMap R' (Localization.Away (algebraMap R R' f))).restrictScalars R) y = 0 := by
  let _ : Algebra R R' := φ.toAlgebra
  -- The target-side kernel is computed by the same localization argument, now over `R'`.
  show y ∈ (R'[f^∞] : Submodule R R') ↔
      ((Algebra.linearMap R' (Localization.Away (algebraMap R R' f))).restrictScalars R) y = 0
  rw [Submodule.mem_torsion'_iff (Submonoid.powers f) y]
  constructor
  · rintro ⟨⟨a, ha_mem⟩, ha⟩
    rcases ha_mem with ⟨n, rfl⟩
    have hmul :
        (algebraMap R' (Localization.Away (algebraMap R R' f)) ((algebraMap R R' f) ^ n)) *
            (((Algebra.linearMap R' (Localization.Away (algebraMap R R' f))).restrictScalars R) y) =
          0 := by
      -- Map the torsion relation into the overlap ring and rewrite it as a product.
      have hmap :
          (Algebra.linearMap R' (Localization.Away (algebraMap R R' f))) ((f ^ n : R) • y) = 0 := by
        simpa using congrArg (Algebra.linearMap R' (Localization.Away (algebraMap R R' f))) ha
      simpa [Algebra.smul_def, map_mul, map_pow] using hmap
    have haunit :
        IsUnit (algebraMap R' (Localization.Away (algebraMap R R' f)) ((algebraMap R R' f) ^ n)) := by
      -- Every power of `φ(f)` becomes a unit after localizing away from `φ(f)`.
      have hpow : (algebraMap R R' f) ^ n ∈ Submonoid.powers (algebraMap R R' f) := ⟨n, rfl⟩
      simpa using
        (IsLocalization.map_units (Localization.Away (algebraMap R R' f))
          ⟨(algebraMap R R' f) ^ n, hpow⟩)
    exact (IsUnit.mul_left_cancel haunit) (by simpa using hmul)
  · intro hy
    change (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R R' f)) R') y = 0 at hy
    rcases (LocalizedModule.mem_ker_mkLinearMap_iff
      (S := Submonoid.powers (algebraMap R R' f)) (m := y)).1 (by
        simpa [LinearMap.mem_ker] using hy) with ⟨b, hb, hby⟩
    rcases hb with ⟨n, rfl⟩
    -- Rewrite the target-side witness back as a power of the original element `f`.
    refine ⟨⟨f ^ n, ⟨n, rfl⟩⟩, ?_⟩
    change (f ^ n : R) • y = 0
    simpa [Algebra.smul_def, map_pow] using hby

/-- Helper for Lemma 15.91.6: injectivity of the quotient comparison modulo `f^n` forces
preimages of `(φ(f)^n)` to lie in `(f^n)`. -/
theorem preimage_principalPowerIdeal_of_quotient_injective
    (n : ℕ+) (hinj : Function.Injective (principalPowerIdealImageQuotientMap φ f n))
    {x : R} (hx : φ x ∈ principalPowerIdeal (φ f) (n : ℕ)) :
    x ∈ principalPowerIdeal f (n : ℕ) := by
  -- Compare the classes of `x` and `0` modulo `f^n`, then pull back vanishing by injectivity.
  have hzero_tgt :
      principalPowerIdealImageQuotientMap φ f n
          ((Ideal.Quotient.mk (principalPowerIdeal f (n : ℕ))) x) =
        0 := by
    change (Ideal.Quotient.mk (principalPowerIdeal (φ f) (n : ℕ))) (φ x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact hx
  have hzero_src : (Ideal.Quotient.mk (principalPowerIdeal f (n : ℕ))) x = 0 := by
    apply hinj
    simpa using hzero_tgt
  rw [Ideal.Quotient.eq_zero_iff_mem] at hzero_src
  exact hzero_src

/-- Helper for Lemma 15.91.6: surjectivity of the positive-power quotient comparison lifts any
target element modulo `(φ(f)^n)` to a source element up to a remainder divisible by `φ(f)^n`. -/
theorem exists_lift_remainder_of_principalPowerQuotient_surjective
    (n : ℕ+) (y : R')
    (hbij : Function.Bijective (principalPowerIdealImageQuotientMap φ f n)) :
    let _ : Algebra R R' := φ.toAlgebra
    ∃ x : R, ∃ z : R', y = φ x + (algebraMap R R' f) ^ (n : ℕ) * z := by
  let _ : Algebra R R' := φ.toAlgebra
  -- Lift the quotient class of `y`, then rewrite the quotient equality as divisibility by
  -- `(φ(f)^n)` in the target ring.
  obtain ⟨xbar, hxbar⟩ :=
    hbij.2 ((Ideal.Quotient.mk (principalPowerIdeal (φ f) (n : ℕ))) y)
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xbar
  have hquot :
      (Ideal.Quotient.mk (principalPowerIdeal (φ f) (n : ℕ))) (φ x) =
        (Ideal.Quotient.mk (principalPowerIdeal (φ f) (n : ℕ))) y := by
    simpa [principalPowerIdealImageQuotientMap, principalPowerIdealQuotientMap] using hxbar
  have hmem :
      y - φ x ∈ principalPowerIdeal (φ f) (n : ℕ) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa [map_sub] using
      (sub_eq_zero.mpr hquot.symm :
        (Ideal.Quotient.mk (principalPowerIdeal (φ f) (n : ℕ))) y -
            (Ideal.Quotient.mk (principalPowerIdeal (φ f) (n : ℕ))) (φ x) =
          0)
  rcases
      (Ideal.mem_span_singleton.mp
        (by
          simpa [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow] using hmem)) with
    ⟨z, hz⟩
  refine ⟨x, z, ?_⟩
  exact sub_eq_iff_eq_add'.1 <| by simpa [mul_comm] using hz

/-
The next helper lemmas isolate the overlap-localization calculations used in the proof of
Lemma 15.91.6.
-/
/-- Helper for Lemma 15.91.6: on a pair `(y, 0)`, the right Cech map is just the canonical overlap
localization map on `R'`. -/
theorem beauvilleLaszloCechRightMap_apply_zero_snd
    (y : R') :
    let _ : Algebra R R' := φ.toAlgebra
    beauvilleLaszloCechRightMap φ f (y, 0) =
      ((Algebra.linearMap R' (Localization.Away (algebraMap R R' f))).restrictScalars R) y := by
  let _ : Algebra R R' := φ.toAlgebra
  let left : R' × Localization.Away f →ₗ[R] Localization.Away (algebraMap R R' f) :=
    ((Algebra.linearMap R' (Localization.Away (algebraMap R R' f))).restrictScalars R).comp
      (LinearMap.fst R R' (Localization.Away f))
  let right : R' × Localization.Away f →ₗ[R] Localization.Away (algebraMap R R' f) :=
    ((Localization.awayMapₐ (Algebra.ofId R R') f).toLinearMap).comp
      (LinearMap.snd R R' (Localization.Away f))
  -- The second coordinate vanishes, so only the first overlap map remains.
  have hright : right (y, 0) = 0 := by
    change ((Localization.awayMapₐ (Algebra.ofId R R') f).toLinearMap) (0 : Localization.Away f) =
      0
    exact LinearMap.map_zero _
  change (left - right) (y, 0) = _
  rw [LinearMap.sub_apply, hright, sub_zero]
  rfl

/-- Helper for Lemma 15.91.6: on a normalized pair `(z, -x / f^n)`, the right Cech map clears the
denominator and records the corrected numerator in the overlap localization. -/
theorem beauvilleLaszloCechRightMap_apply_neg_power_fraction
    (n : ℕ) (x : R) (z : R') :
    let _ : Algebra R R' := φ.toAlgebra
    let s : Submonoid.powers f := ⟨f ^ n, ⟨n, rfl⟩⟩
    let t : Submonoid.powers (algebraMap R R' f) := ⟨(algebraMap R R' f) ^ n, ⟨n, rfl⟩⟩
    beauvilleLaszloCechRightMap φ f (z, - IsLocalization.mk' (Localization.Away f) x s) =
      IsLocalization.mk' (Localization.Away (algebraMap R R' f))
        ((algebraMap R R' f) ^ n * z + φ x) t := by
  let _ : Algebra R R' := φ.toAlgebra
  let s : Submonoid.powers f := ⟨f ^ n, ⟨n, rfl⟩⟩
  let t : Submonoid.powers (algebraMap R R' f) := ⟨(algebraMap R R' f) ^ n, ⟨n, rfl⟩⟩
  let left : R' × Localization.Away f →ₗ[R] Localization.Away (algebraMap R R' f) :=
    ((Algebra.linearMap R' (Localization.Away (algebraMap R R' f))).restrictScalars R).comp
      (LinearMap.fst R R' (Localization.Away f))
  let right : R' × Localization.Away f →ₗ[R] Localization.Away (algebraMap R R' f) :=
    ((Localization.awayMapₐ (Algebra.ofId R R') f).toLinearMap).comp
      (LinearMap.snd R R' (Localization.Away f))
  -- Rewrite the second overlap coordinate through the canonical localization map.
  have hright :
      right (z, - IsLocalization.mk' (Localization.Away f) x s) =
        - IsLocalization.mk' (Localization.Away (algebraMap R R' f)) (φ x) t := by
    change ((Localization.awayMapₐ (Algebra.ofId R R') f).toLinearMap)
        (- IsLocalization.mk' (Localization.Away f) x s) = _
    rw [map_neg]
    congr 1
    simpa [s, t] using
      (IsLocalization.map_mk'
        (Q := Localization.Away (algebraMap R R' f))
        (g := φ)
        (hy := by
          intro y hy
          rcases hy with ⟨m, hm⟩
          have hφ : algebraMap R R' f = φ f := rfl
          refine ⟨m, ?_⟩
          rw [← hm]
          simp [hφ, map_pow])
        x s)
  -- Once the second coordinate is normalized, the result is the standard `mk'` denominator-clearing
  -- identity in the overlap ring.
  change (left - right) (z, - IsLocalization.mk' (Localization.Away f) x s) = _
  rw [LinearMap.sub_apply, hright, sub_neg_eq_add]
  change (algebraMap R' (Localization.Away (algebraMap R R' f)) z) +
      IsLocalization.mk' (Localization.Away (algebraMap R R' f)) (φ x) t = _
  rw [eq_comm]
  apply (IsLocalization.mk'_eq_iff_eq_mul).2
  have hmk :
      (algebraMap R' (Localization.Away (algebraMap R R' f))) (φ x) =
        IsLocalization.mk' (Localization.Away (algebraMap R R' f)) (φ x) t *
          (algebraMap R' (Localization.Away (algebraMap R R' f))) ((algebraMap R R' f) ^ n) := by
    exact (IsLocalization.mk'_eq_iff_eq_mul).1 rfl
  simp [map_add, map_mul, hmk, t, mul_add, mul_comm]

/-- Helper for Lemma 15.91.6: a kernel element `(x, y' / f^n)` produces an `f`-power-torsion
numerator `f^n x - φ(y')` in `R'`. -/
theorem kernel_numerator_mem_fPowerTorsion_of_rightMap_eq_zero
    (n : ℕ) (x : R') (y' : R)
    (hker :
      let _ : Algebra R R' := φ.toAlgebra
      let s : Submonoid.powers f := ⟨f ^ n, ⟨n, rfl⟩⟩
      beauvilleLaszloCechRightMap φ f (x, IsLocalization.mk' (Localization.Away f) y' s) = 0) :
    let _ : Algebra R R' := φ.toAlgebra
    ((f ^ n : R) • x - φ y') ∈ (R'[f^∞] : Submodule R R') := by
  let _ : Algebra R R' := φ.toAlgebra
  let s : Submonoid.powers f := ⟨f ^ n, ⟨n, rfl⟩⟩
  let t : Submonoid.powers (algebraMap R R' f) := ⟨(algebraMap R R' f) ^ n, ⟨n, rfl⟩⟩
  let left : R' × Localization.Away f →ₗ[R] Localization.Away (algebraMap R R' f) :=
    ((Algebra.linearMap R' (Localization.Away (algebraMap R R' f))).restrictScalars R).comp
      (LinearMap.fst R R' (Localization.Away f))
  let right : R' × Localization.Away f →ₗ[R] Localization.Away (algebraMap R R' f) :=
    ((Localization.awayMapₐ (Algebra.ofId R R') f).toLinearMap).comp
      (LinearMap.snd R R' (Localization.Away f))
  -- The kernel equation says the two overlap-coordinate maps agree on `(x, y' / f^n)`.
  have hover :
      left (x, IsLocalization.mk' (Localization.Away f) y' s) =
        right (x, IsLocalization.mk' (Localization.Away f) y' s) := by
    change (left - right) (x, IsLocalization.mk' (Localization.Away f) y' s) = 0 at hker
    exact sub_eq_zero.mp hker
  have hmap :
      right (x, IsLocalization.mk' (Localization.Away f) y' s) =
        IsLocalization.mk' (Localization.Away (algebraMap R R' f)) (φ y') t := by
    change ((Localization.awayMapₐ (Algebra.ofId R R') f).toLinearMap)
        (IsLocalization.mk' (Localization.Away f) y' s) = _
    simpa [s, t] using
      (IsLocalization.map_mk'
        (Q := Localization.Away (algebraMap R R' f))
        (g := φ)
        (hy := by
          intro y hy
          rcases hy with ⟨m, hm⟩
          have hφ : algebraMap R R' f = φ f := rfl
          refine ⟨m, ?_⟩
          rw [← hm]
          simp [hφ, map_pow])
        y' s)
  -- The corrected numerator maps to zero in the overlap, hence lies in the torsion submodule.
  apply
    (mem_fPowerTorsion_iff_overlap_eq_zero (φ := φ) (f := f)
      (((f ^ n : R) • x) - φ y')).2
  rw [map_sub, map_smul]
  have hover' :
      algebraMap R' (Localization.Away (algebraMap R R' f)) x =
        IsLocalization.mk' (Localization.Away (algebraMap R R' f)) (φ y') t := by
    simpa [left, LinearMap.comp_apply] using hover.trans hmap
  have hmul := (IsLocalization.mk'_eq_iff_eq_mul).1 hover'.symm
  have hmul0 :
      (f ^ n : R) •
          ((Algebra.linearMap R' (Localization.Away (algebraMap R R' f))).restrictScalars R) x =
        (Algebra.linearMap R' (Localization.Away (algebraMap R R' f))) (φ y') := by
    have hφ : algebraMap R R' f = φ f := rfl
    have hpow_map :
        algebraMap R (Localization.Away (algebraMap R R' f)) (f ^ n) =
          algebraMap R' (Localization.Away (algebraMap R R' f)) ((φ f) ^ n) := by
      change
        (Algebra.linearMap R' (Localization.Away (algebraMap R R' f)))
            ((algebraMap R R') (f ^ n)) =
          (Algebra.linearMap R' (Localization.Away (algebraMap R R' f))) ((φ f) ^ n)
      simp [hφ, map_pow]
    calc
      (f ^ n : R) •
          ((Algebra.linearMap R' (Localization.Away (algebraMap R R' f))).restrictScalars R) x =
        algebraMap R (Localization.Away (algebraMap R R' f)) (f ^ n) *
          algebraMap R' (Localization.Away (algebraMap R R' f)) x := by
            simp [Algebra.smul_def]
      _ =
        algebraMap R' (Localization.Away (algebraMap R R' f)) ((φ f) ^ n) *
          algebraMap R' (Localization.Away (algebraMap R R' f)) x := by
            rw [hpow_map]
      _ =
        algebraMap R' (Localization.Away (algebraMap R R' f)) x *
          algebraMap R' (Localization.Away (algebraMap R R' f)) ((φ f) ^ n) := by
            rw [mul_comm]
      _ =
        algebraMap R' (Localization.Away (algebraMap R R' f)) (φ y') := hmul.symm
      _ = (Algebra.linearMap R' (Localization.Away (algebraMap R R' f))) (φ y') := rfl
  exact sub_eq_zero.mpr hmul0

/-- Helper for Lemma 15.91.6: surjectivity on `f^∞`-torsion lifts every kernel element of the
right Cech map to an element of `R`. -/
theorem exists_preimage_of_beauvilleLaszloCechRightMap_eq_zero_of_fPowerTorsion_surjective
    (hquot : ∀ n : ℕ+, Function.Bijective (principalPowerIdealImageQuotientMap φ f n))
    (hsurj :
      let _ : Algebra R R' := φ.toAlgebra
      Function.Surjective (fPowerTorsionToExtension φ f))
    {p : R' × Localization.Away f}
    (hp :
      let _ : Algebra R R' := φ.toAlgebra
      beauvilleLaszloCechRightMap φ f p = 0) :
    let _ : Algebra R R' := φ.toAlgebra
    ∃ r : R, beauvilleLaszloCechLeftMap φ f r = p := by
  let _ : Algebra R R' := φ.toAlgebra
  rcases p with ⟨x, y⟩
  rcases IsLocalization.surj (Submonoid.powers f) y with ⟨⟨y', ⟨_, ⟨n, rfl⟩⟩⟩, hy_mul⟩
  let s : Submonoid.powers f := ⟨f ^ n, ⟨n, rfl⟩⟩
  have hy :
      y = IsLocalization.mk' (Localization.Away f) y' s := by
    rw [eq_comm]
    apply (IsLocalization.mk'_eq_iff_eq_mul).2
    simpa [s, mul_comm] using hy_mul.symm
  have hker :
      beauvilleLaszloCechRightMap φ f (x, IsLocalization.mk' (Localization.Away f) y' s) = 0 := by
    simpa [hy] using hp
  cases n with
  | zero =>
      -- When the denominator is already `1`, a single torsion lift gives a preimage in `R`.
      let s0 : Submonoid.powers f := ⟨1, ⟨0, by simp⟩⟩
      have hy0 : y = IsLocalization.mk' (Localization.Away f) y' s0 := by
        simpa [s, s0] using hy
      have htors :
          (x - φ y') ∈ (R'[f^∞] : Submodule R R') := by
        simpa using
          kernel_numerator_mem_fPowerTorsion_of_rightMap_eq_zero
            (φ := φ) (f := f) 0 x y' hker
      obtain ⟨z, hz⟩ := hsurj ⟨x - φ y', htors⟩
      have hz0 :
          (Algebra.linearMap R (Localization.Away f)) (z : R) = 0 := by
        exact (mem_fPowerTorsion_iff_away_eq_zero (f := f) (x := (z : R))).1 z.2
      have hy_base0 : (Algebra.linearMap R (Localization.Away f)) y' = y := by
        calc
          (Algebra.linearMap R (Localization.Away f)) y' =
              IsLocalization.mk' (Localization.Away f) y' s0 := by
                rw [eq_comm]
                apply (IsLocalization.mk'_eq_iff_eq_mul).2
                simp [s0]
          _ = y := hy0.symm
      refine ⟨y' + z, ?_⟩
      ext
      · have hzfst : φ (z : R) = x - φ y' := congrArg Subtype.val hz
        calc
          φ (y' + z) = φ y' + φ (z : R) := by simp
          _ = φ y' + (x - φ y') := by rw [hzfst]
          _ = x := by abel
      · calc
          (Algebra.linearMap R (Localization.Away f)) (y' + z) =
              (Algebra.linearMap R (Localization.Away f)) y' +
                (Algebra.linearMap R (Localization.Away f)) (z : R) := by
                  simp
          _ = y + 0 := by rw [hy_base0, hz0]
          _ = y := by simp
  | succ m =>
      -- Route correction: for a positive denominator, first kill the numerator torsion,
      -- rewrite the localization coordinate with denominator `1`, and then lift the residual
      -- torsion in the first coordinate.
      let npos : ℕ+ := ⟨m + 1, Nat.succ_pos _⟩
      have htors_num :
          (((f ^ (m + 1) : R) • x) - φ y') ∈ (R'[f^∞] : Submodule R R') := by
        simpa using
          kernel_numerator_mem_fPowerTorsion_of_rightMap_eq_zero
            (φ := φ) (f := f) (m + 1) x y' hker
      obtain ⟨z, hz⟩ := hsurj ⟨((f ^ (m + 1) : R) • x) - φ y', htors_num⟩
      have hz0 :
          (Algebra.linearMap R (Localization.Away f)) (z : R) = 0 := by
        exact (mem_fPowerTorsion_iff_away_eq_zero (f := f) (x := (z : R))).1 z.2
      have hyz :
          φ (y' + (z : R)) = (f ^ (m + 1) : R) • x := by
        have hzfst : φ (z : R) = ((f ^ (m + 1) : R) • x) - φ y' := congrArg Subtype.val hz
        calc
          φ (y' + (z : R)) = φ y' + φ (z : R) := by simp
          _ = φ y' + (((f ^ (m + 1) : R) • x) - φ y') := by rw [hzfst]
          _ = (f ^ (m + 1) : R) • x := by abel
      have hpow_mem_tgt :
          φ (y' + (z : R)) ∈ principalPowerIdeal (φ f) (m + 1) := by
        have hφ : algebraMap R R' f = φ f := rfl
        rw [hyz, principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow]
        exact Ideal.mem_span_singleton.mpr ⟨x, by simp [Algebra.smul_def, map_pow, hφ, mul_comm]⟩
      have hpow_mem_src :
          y' + (z : R) ∈ principalPowerIdeal f (m + 1) := by
        exact
          preimage_principalPowerIdeal_of_quotient_injective
            (φ := φ) (f := f) npos (hquot npos).1 hpow_mem_tgt
      rcases
          (Ideal.mem_span_singleton.mp
            (by
              simpa [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow] using
                hpow_mem_src)) with
        ⟨y'', hy''⟩
      have hy_plus :
          y = (Algebra.linearMap R (Localization.Away f)) y'' := by
        have hy_num :
            y = IsLocalization.mk' (Localization.Away f) (y' + (z : R)) s := by
          rw [eq_comm]
          apply (IsLocalization.mk'_eq_iff_eq_mul).2
          calc
            algebraMap R (Localization.Away f) (y' + (z : R)) =
                algebraMap R (Localization.Away f) y' +
                  algebraMap R (Localization.Away f) (z : R) := by
                    simp
            _ = y * algebraMap R (Localization.Away f) (f ^ (m + 1)) + 0 := by
                  rw [show algebraMap R (Localization.Away f) y' =
                      y * algebraMap R (Localization.Away f) (f ^ (m + 1)) by
                        simpa [s, mul_comm] using hy_mul.symm]
                  rw [show algebraMap R (Localization.Away f) (z : R) = 0 by simpa using hz0]
            _ = y * algebraMap R (Localization.Away f) (f ^ (m + 1)) := by simp
        have hy_base :
            IsLocalization.mk' (Localization.Away f) (y' + (z : R)) s =
              (Algebra.linearMap R (Localization.Away f)) y'' := by
          rw [hy'']
          apply (IsLocalization.mk'_eq_iff_eq_mul).2
          simp [s, mul_comm, mul_left_comm, mul_assoc]
        exact hy_num.trans hy_base
      have hsmul_eq :
          (f ^ (m + 1) : R) • x = (f ^ (m + 1) : R) • φ y'' := by
        have hφ : algebraMap R R' f = φ f := rfl
        calc
          (f ^ (m + 1) : R) • x = φ (y' + (z : R)) := hyz.symm
          _ = φ (f ^ (m + 1) * y'') := by rw [hy'']
          _ = (f ^ (m + 1) : R) • φ y'' := by
                simp [Algebra.smul_def, map_mul, map_pow, mul_comm, hφ]
      have htors_residual :
          (x - φ y'') ∈ (R'[f^∞] : Submodule R R') := by
        rw [Submodule.mem_torsion'_iff (Submonoid.powers f)]
        refine ⟨⟨f ^ (m + 1), ⟨m + 1, rfl⟩⟩, ?_⟩
        have hsmul_zero :
            (f ^ (m + 1) : R) • x - (f ^ (m + 1) : R) • φ y'' = 0 := by
          exact sub_eq_zero.mpr hsmul_eq
        simpa [smul_sub] using hsmul_zero
      obtain ⟨z', hz'⟩ := hsurj ⟨x - φ y'', htors_residual⟩
      have hz'0 :
          (Algebra.linearMap R (Localization.Away f)) (z' : R) = 0 := by
        exact (mem_fPowerTorsion_iff_away_eq_zero (f := f) (x := (z' : R))).1 z'.2
      refine ⟨y'' + z', ?_⟩
      ext
      · have hz'fst : φ (z' : R) = x - φ y'' := congrArg Subtype.val hz'
        calc
          φ (y'' + z') = φ y'' + φ (z' : R) := by simp
          _ = φ y'' + (x - φ y'') := by rw [hz'fst]
          _ = x := by abel
      · calc
          (Algebra.linearMap R (Localization.Away f)) (y'' + z') =
              (Algebra.linearMap R (Localization.Away f)) y'' +
                (Algebra.linearMap R (Localization.Away f)) (z' : R) := by
                  simp
          _ = y + 0 := by rw [hy_plus, hz'0]
          _ = y := by simp

theorem beauvilleLaszloCechRightMap_surjective_of_principalPowerQuotientMapBijective
    (hquot : ∀ n : ℕ+, Function.Bijective (principalPowerIdealImageQuotientMap φ f n))
    :
    let _ : Algebra R R' := φ.toAlgebra
    Function.Surjective
      (beauvilleLaszloCechRightMap φ f :
        R' × Localization.Away f →ₗ[R] Localization.Away (algebraMap R R' f)) := by
  let _ : Algebra R R' := φ.toAlgebra
  change Function.Surjective
    (beauvilleLaszloCechRightMap φ f :
      R' × Localization.Away f →ₗ[R] Localization.Away (algebraMap R R' f))
  intro z
  rcases IsLocalization.surj (Submonoid.powers (algebraMap R R' f)) z with
    ⟨⟨x', ⟨_, ⟨n, rfl⟩⟩⟩, hz_mul⟩
  let t : Submonoid.powers (algebraMap R R' f) := ⟨(algebraMap R R' f) ^ n, ⟨n, rfl⟩⟩
  have hz :
      z =
        IsLocalization.mk' (Localization.Away (algebraMap R R' f)) x' t := by
    rw [eq_comm]
    apply (IsLocalization.mk'_eq_iff_eq_mul).2
    simpa [t, mul_comm] using hz_mul.symm
  cases n with
  | zero =>
      -- A denominator `1` is already in the image of the pair `(x', 0)`.
      let t0 : Submonoid.powers (algebraMap R R' f) := ⟨1, ⟨0, by simp⟩⟩
      have hz0 : z = IsLocalization.mk' (Localization.Away (algebraMap R R' f)) x' t0 := by
        simpa [t, t0] using hz
      have hx'_base : (Algebra.linearMap R' (Localization.Away (algebraMap R R' f))) x' = z := by
        calc
          (Algebra.linearMap R' (Localization.Away (algebraMap R R' f))) x' =
              IsLocalization.mk' (Localization.Away (algebraMap R R' f)) x' t0 := by
                rw [eq_comm]
                apply (IsLocalization.mk'_eq_iff_eq_mul).2
                simp [t0]
          _ = z := hz0.symm
      refine ⟨(x', 0), ?_⟩
      calc
        beauvilleLaszloCechRightMap φ f (x', 0) =
            ((Algebra.linearMap R' (Localization.Away (algebraMap R R' f))).restrictScalars R) x' := by
              exact beauvilleLaszloCechRightMap_apply_zero_snd (φ := φ) (f := f) x'
        _ = z := by exact hx'_base
  | succ m =>
      -- For a positive denominator, lift the numerator modulo `(φ(f)^(m + 1))` and use the
      -- normalized denominator-clearing computation.
      let npos : ℕ+ := ⟨m + 1, Nat.succ_pos _⟩
      rcases exists_lift_remainder_of_principalPowerQuotient_surjective
          (φ := φ) (f := f) npos x' (hquot npos) with ⟨x'', y, hy⟩
      let s : Submonoid.powers f := ⟨f ^ (m + 1), ⟨m + 1, rfl⟩⟩
      refine ⟨(y, - IsLocalization.mk' (Localization.Away f) x'' s), ?_⟩
      calc
        beauvilleLaszloCechRightMap φ f (y, - IsLocalization.mk' (Localization.Away f) x'' s) =
            IsLocalization.mk' (Localization.Away (algebraMap R R' f))
              ((algebraMap R R' f) ^ (m + 1) * y + φ x'') t := by
                simpa [s, t] using
                  beauvilleLaszloCechRightMap_apply_neg_power_fraction
                    (φ := φ) (f := f) (m + 1) x'' y
        _ = IsLocalization.mk' (Localization.Away (algebraMap R R' f))
              (φ x'' + (algebraMap R R' f) ^ ↑npos * y) t := by
              congr 1
              simp [npos, add_comm, mul_comm]
        _ = IsLocalization.mk' (Localization.Away (algebraMap R R' f)) x' t := by
              rw [hy]
        _ = z := hz.symm

/-- Helper for Lemma 15.91.6: exactness of the Beauville-Laszlo Cech sequence sends a torsion
element `y ∈ R'[f^∞]` to a torsion preimage in `R` by testing exactness on the kernel element
`(y, 0)`. -/
theorem fPowerTorsionToExtension_surjective_of_beauvilleLaszloCechMiddle_exact
    (hexact :
      let _ : Algebra R R' := φ.toAlgebra
      Function.Exact
        (beauvilleLaszloCechLeftMap φ f : R →ₗ[R] R' × Localization.Away f)
        (beauvilleLaszloCechRightMap φ f :
          R' × Localization.Away f →ₗ[R] Localization.Away (algebraMap R R' f))) :
    let _ : Algebra R R' := φ.toAlgebra
    Function.Surjective (fPowerTorsionToExtension φ f) := by
  let _ : Algebra R R' := φ.toAlgebra
  change Function.Surjective (fPowerTorsionToExtension φ f)
  intro y
  have hy0 :
      beauvilleLaszloCechRightMap φ f ((y : R'), 0) = 0 := by
    -- The kernel test on `(y, 0)` is exactly the overlap-vanishing characterization of torsion.
    rw [beauvilleLaszloCechRightMap_apply_zero_snd (φ := φ) (f := f)]
    exact (mem_fPowerTorsion_iff_overlap_eq_zero (φ := φ) (f := f) (y := (y : R'))).1 y.2
  have hy_range :
      ((y : R'), (0 : Localization.Away f)) ∈ Set.range (beauvilleLaszloCechLeftMap φ f) := by
    exact (hexact ((y : R'), 0)).1 hy0
  rcases hy_range with ⟨x, hx⟩
  have hx0 :
      (Algebra.linearMap R (Localization.Away f)) x = 0 := by
    simpa [beauvilleLaszloCechLeftMap] using congrArg Prod.snd hx
  have hxtors : x ∈ (R[f^∞] : Submodule R R) :=
    (mem_fPowerTorsion_iff_away_eq_zero (f := f) (x := x)).2 hx0
  refine ⟨⟨x, hxtors⟩, ?_⟩
  apply Subtype.ext
  simpa [fPowerTorsionToExtension, beauvilleLaszloCechLeftMap] using congrArg Prod.fst hx

/-- Under the quotient-bijectivity hypothesis, the Beauville-Laszlo Cech sequence is exact on the
left exactly when `R[f^∞] → R'[f^∞]` is injective. -/
theorem beauvilleLaszloCechLeftMap_injective_iff_fPowerTorsionToExtension_injective
    (hquot : ∀ n : ℕ+, Function.Bijective (principalPowerIdealImageQuotientMap φ f n))
    :
    let _ : Algebra R R' := φ.toAlgebra
    Function.Injective
      (beauvilleLaszloCechLeftMap φ f : R →ₗ[R] R' × Localization.Away f) ↔
    Function.Injective (fPowerTorsionToExtension φ f) := by
  let _ : Algebra R R' := φ.toAlgebra
  let _ := hquot
  constructor
  · intro hleft
    intro x y hxy
    apply Subtype.ext
    -- Equal torsion images have equal first components, and both localization components vanish.
    apply hleft
    ext
    · exact congrArg Subtype.val hxy
    · have hx0 : (Algebra.linearMap R (Localization.Away f)) (x : R) = 0 :=
        (mem_fPowerTorsion_iff_away_eq_zero (f := f) (x := (x : R))).1 x.2
      have hy0 : (Algebra.linearMap R (Localization.Away f)) (y : R) = 0 :=
        (mem_fPowerTorsion_iff_away_eq_zero (f := f) (x := (y : R))).1 y.2
      simp [beauvilleLaszloCechLeftMap, hx0, hy0]
  · intro htors
    intro x y hxy
    -- Reduce injectivity of the left map to the vanishing of `x - y` in the torsion submodule.
    have hsnd :
        (Algebra.linearMap R (Localization.Away f)) (x - y) = 0 := by
      have hsnd_eq :
          (Algebra.linearMap R (Localization.Away f)) x =
            (Algebra.linearMap R (Localization.Away f)) y := by
        simpa [beauvilleLaszloCechLeftMap] using congrArg Prod.snd hxy
      simpa [LinearMap.map_sub] using (sub_eq_zero.mpr hsnd_eq :
        (Algebra.linearMap R (Localization.Away f)) x -
            (Algebra.linearMap R (Localization.Away f)) y =
          0)
    have htors_mem : x - y ∈ (R[f^∞] : Submodule R R) :=
      (mem_fPowerTorsion_iff_away_eq_zero (f := f) (x := x - y)).2 hsnd
    have hfst :
        φ (x - y) = 0 := by
      have hfst_eq : φ x = φ y := by
        simpa [beauvilleLaszloCechLeftMap] using congrArg Prod.fst hxy
      simpa [map_sub] using (sub_eq_zero.mpr hfst_eq : φ x - φ y = 0)
    have htors_zero :
        (fPowerTorsionToExtension φ f) ⟨x - y, htors_mem⟩ =
          (fPowerTorsionToExtension φ f) 0 := by
      apply Subtype.ext
      simpa [fPowerTorsionToExtension] using hfst
    have hsub_zero : (⟨x - y, htors_mem⟩ : (R[f^∞] : Submodule R R)) = 0 := htors htors_zero
    exact sub_eq_zero.mp <| congrArg Subtype.val hsub_zero

/-- Under the quotient-bijectivity hypothesis, the Beauville-Laszlo Cech sequence is exact in the
middle exactly when `R[f^∞] → R'[f^∞]` is surjective. -/
theorem beauvilleLaszloCechMiddle_exact_iff_fPowerTorsionToExtension_surjective
    (hquot : ∀ n : ℕ+, Function.Bijective (principalPowerIdealImageQuotientMap φ f n))
    :
    let _ : Algebra R R' := φ.toAlgebra
    Function.Exact
      (beauvilleLaszloCechLeftMap φ f : R →ₗ[R] R' × Localization.Away f)
      (beauvilleLaszloCechRightMap φ f :
        R' × Localization.Away f →ₗ[R] Localization.Away (algebraMap R R' f)) ↔
    Function.Surjective (fPowerTorsionToExtension φ f) := by
  let _ : Algebra R R' := φ.toAlgebra
  constructor
  · intro hexact
    exact
      fPowerTorsionToExtension_surjective_of_beauvilleLaszloCechMiddle_exact
        (φ := φ) (f := f) hexact
  · intro hsurj
    intro p
    constructor
    · intro hp
      rcases
          exists_preimage_of_beauvilleLaszloCechRightMap_eq_zero_of_fPowerTorsion_surjective
            (φ := φ) (f := f) hquot hsurj hp with
        ⟨r, hr⟩
      exact ⟨r, hr⟩
    · rintro ⟨r, rfl⟩
      exact LinearMap.congr_fun (beauvilleLaszloCech_comp_eq_zero (φ := φ) (f := f)) r

/-- Lemma 15.91.6: if `φ : R →+* R'` induces isomorphisms
`R / (f^n) → R' / (φ(f)^n)R'` for all positive integers `n`, then `(φ, f)` is a
Beauville-Laszlo glueing pair if and only if the induced map `R[f^∞] → R'[f^∞]` is bijective. -/
theorem isBeauvilleLaszloGlueingPairAlong_iff_bijective_fPowerTorsionToExtension
    (hquot : ∀ n : ℕ+, Function.Bijective (principalPowerIdealImageQuotientMap φ f n))
    :
    let _ : Algebra R R' := φ.toAlgebra
    IsBeauvilleLaszloGlueingPairAlong φ f ↔
    Function.Bijective (fPowerTorsionToExtension φ f) := by
  let _ : Algebra R R' := φ.toAlgebra
  constructor
  · intro hpair
    constructor
    · -- Left exactness of the short complex gives injectivity on `f`-power torsion.
      have hmono :
          Function.Injective
            ((beauvilleLaszloCechSequence φ f).f.hom) := by
        exact (ModuleCat.mono_iff_injective _).1 hpair.shortExact.mono_f
      exact
        (beauvilleLaszloCechLeftMap_injective_iff_fPowerTorsionToExtension_injective
          (φ := φ) (f := f) hquot).1 (by simpa [beauvilleLaszloCechSequence] using hmono)
    · -- Middle exactness of the short complex gives surjectivity on `f`-power torsion.
      have hexact :
          Function.Exact
            ((beauvilleLaszloCechSequence φ f).f.hom)
            ((beauvilleLaszloCechSequence φ f).g.hom) := by
        exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
          (beauvilleLaszloCechSequence φ f)).1 hpair.shortExact.exact
      exact
        (beauvilleLaszloCechMiddle_exact_iff_fPowerTorsionToExtension_surjective
          (φ := φ) (f := f) hquot).1 (by simpa [beauvilleLaszloCechSequence] using hexact)
  · rintro ⟨hinj, hsurj⟩
    refine
      { quotientMapBijective := hquot
        shortExact := ?_ }
    -- Source route: combine right exactness with the left and middle criteria already identified.
    refine ModuleCat.shortComplex_shortExact (beauvilleLaszloCechSequence φ f) ?_ ?_ ?_
    · change Function.Exact
        (beauvilleLaszloCechLeftMap φ f : R →ₗ[R] R' × Localization.Away f)
        (beauvilleLaszloCechRightMap φ f :
          R' × Localization.Away f →ₗ[R] Localization.Away (algebraMap R R' f))
      exact
        (beauvilleLaszloCechMiddle_exact_iff_fPowerTorsionToExtension_surjective
          (φ := φ) (f := f) hquot).2 hsurj
    · change Function.Injective
        (beauvilleLaszloCechLeftMap φ f : R →ₗ[R] R' × Localization.Away f)
      exact
        (beauvilleLaszloCechLeftMap_injective_iff_fPowerTorsionToExtension_injective
          (φ := φ) (f := f) hquot).2 hinj
    · change Function.Surjective
        (beauvilleLaszloCechRightMap φ f :
          R' × Localization.Away f →ₗ[R] Localization.Away (algebraMap R R' f))
      exact
        beauvilleLaszloCechRightMap_surjective_of_principalPowerQuotientMapBijective
          (φ := φ) (f := f) hquot

end

end

section PrincipalAdicCompletion

variable {R : Type u} [CommRing R] (f : R)

/-- For the `(f)`-adic completion, the Beauville-Laszlo glueing-pair condition is equivalent to the
bijection `R[f^∞] → R^∧[f^∞]`. -/
theorem principalAdicCompletion_isBeauvilleLaszloGlueingPairAlong_iff_bijective_fPowerTorsion :
    IsBeauvilleLaszloGlueingPairAlong
      (algebraMap R (principalAdicCompletion f))
      f ↔
      Function.Bijective
        (fPowerTorsionToExtension (algebraMap R (principalAdicCompletion f)) f) := by
  let hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R (principalAdicCompletion f)) f n) :=
    principalAdicCompletion_quotientMap_bijective f
  simpa using
    (isBeauvilleLaszloGlueingPairAlong_iff_bijective_fPowerTorsionToExtension
      (algebraMap R (principalAdicCompletion f))
      f
      hquot)

end PrincipalAdicCompletion
