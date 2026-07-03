import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Localization.Away.Basic
import stacks_project.Chap15.Definition_15_89_1
import stacks_project.Chap15.Lemma_15_91_1

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
  sorry

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

/-- Under the quotient-bijectivity hypothesis, the Beauville-Laszlo Cech sequence is exact on the
right. -/
theorem beauvilleLaszloCechRightMap_surjective_of_principalPowerQuotientMapBijective
    (hquot : ∀ n : ℕ+, Function.Bijective (principalPowerIdealImageQuotientMap φ f n))
    :
    let _ : Algebra R R' := φ.toAlgebra
    Function.Surjective
      (beauvilleLaszloCechRightMap φ f :
        R' × Localization.Away f →ₗ[R] Localization.Away (algebraMap R R' f)) := by
  sorry

/-- Under the quotient-bijectivity hypothesis, the Beauville-Laszlo Cech sequence is exact on the
left exactly when `R[f^∞] → R'[f^∞]` is injective. -/
theorem beauvilleLaszloCechLeftMap_injective_iff_fPowerTorsionToExtension_injective
    (hquot : ∀ n : ℕ+, Function.Bijective (principalPowerIdealImageQuotientMap φ f n))
    :
    let _ : Algebra R R' := φ.toAlgebra
    Function.Injective
      (beauvilleLaszloCechLeftMap φ f : R →ₗ[R] R' × Localization.Away f) ↔
    Function.Injective (fPowerTorsionToExtension φ f) := by
  sorry

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
  sorry

/-- Lemma 15.91.6: if `φ : R →+* R'` induces isomorphisms
`R / (f^n) → R' / (φ(f)^n)R'` for all positive integers `n`, then `(φ, f)` is a
Beauville-Laszlo glueing pair if and only if the induced map `R[f^∞] → R'[f^∞]` is bijective. -/
theorem isBeauvilleLaszloGlueingPairAlong_iff_bijective_fPowerTorsionToExtension
    (hquot : ∀ n : ℕ+, Function.Bijective (principalPowerIdealImageQuotientMap φ f n))
    :
    let _ : Algebra R R' := φ.toAlgebra
    IsBeauvilleLaszloGlueingPairAlong φ f ↔
    Function.Bijective (fPowerTorsionToExtension φ f) := by
  sorry

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
