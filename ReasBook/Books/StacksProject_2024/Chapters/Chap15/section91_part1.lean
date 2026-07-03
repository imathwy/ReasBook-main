import Mathlib
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Localization.Away.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_91_1 (from Chap15) -/
noncomputable section

universe u

/-
Domain-style sampling:
* primary domain: principal-power quotient comparison maps in commutative algebra, specialized
  later to principal adic completion.
* sampled owner declarations:
  `principalIdeal`,
  `principalPowerIdealQuotientMap`,
  `principalPowerIdeal`,
  `AdicCompletion`,
  `adicCompletion_quotientMap_bijective`,
  `tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective`.
* owner abstraction: the source-facing quotient map is the chapter owner
  `principalPowerIdealQuotientMap`, while its completion comparison is supplied canonically by
  `adicCompletion_quotientMap_bijective` after specializing to `AdicCompletion (principalIdeal f) R`.
* primitive data: the ring `R`, the principal ideal `principalIdeal f`, and the exponent `n : ℕ`.
* derived API: bijectivity of the induced quotient maps, and the completion specialization below.
* triage: `core/canonical` owner = `adicCompletion_quotientMap_bijective` for the ideal powers
  `((Ideal.map _ (principalIdeal f))^n)` on the completion side; the Beauville-Laszlo completion
  statement below is the positive-integer specialization to the principal ideal `(f)`.
-/

section

variable {R : Type u} [CommRing R] (f : R)

-- Proof sketch: this is the canonical adic-completion quotient-map bijectivity theorem applied to
-- the finitely generated principal ideal `(f)`, then specialized through the chapter owner
-- `AdicCompletion (principalIdeal f) R`.
/-- Lemma 15.91.1: for every positive integer `n`, the canonical map
`R / (f)^n → R^∧ / (f)^n R^∧` for the `(f)`-adic completion is bijective. This is the thin
completion-specialized bridge to the canonical `Ideal.quotientMap` owner used by the later
base-change API. -/
theorem principalAdicCompletion_quotientMap_bijective (n : ℕ+) :
    Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R (principalAdicCompletion f)) f n) := by
  let σ : R →+* principalAdicCompletion f := algebraMap R (principalAdicCompletion f)
  let qraw :
      R ⧸ principalPowerIdeal f n →+* principalAdicCompletion f ⧸
        Ideal.map σ (principalIdeal f ^ (n : ℕ)) :=
    Ideal.quotientMap (Ideal.map σ (principalIdeal f ^ (n : ℕ))) σ Ideal.le_comap_map
  have hraw : Function.Bijective qraw := by
    simpa [qraw, σ, principalPowerIdeal] using
      adicCompletion_quotientMap_bijective
        (principalIdeal f)
        (Submodule.fg_span_singleton f)
        n
  have hmap :
      Ideal.map σ (principalIdeal f ^ (n : ℕ)) =
        principalPowerIdeal (σ f) n := by
    simp [σ, principalPowerIdeal, principalIdeal, Ideal.map_pow, Ideal.map_span,
      Set.image_singleton]
  have hcomp :
      principalPowerIdealImageQuotientMap σ f n =
        (Ideal.quotEquivOfEq hmap).toRingHom.comp qraw := by
    apply Ideal.Quotient.ringHom_ext
    exact RingHom.ext fun x ↦ by
      simpa [RingHom.comp_apply, qraw, σ, principalPowerIdealImageQuotientMap,
        principalPowerIdealQuotientMap, Ideal.quotientMap_mk] using
        (Ideal.quotEquivOfEq_mk hmap (σ x)).symm
  rw [hcomp]
  exact (RingEquiv.bijective <| Ideal.quotEquivOfEq hmap).comp hraw

end

/-! ### Lemma_15_91_2 (from Chap15) -/
open scoped TensorProduct

universe u v w

section

variable {R : Type u} [CommRing R]
variable {R' : Type w} [CommRing R'] [Algebra R R']
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (f : R)

/-
Domain-style sampling:
- primary domain: commutative algebra of tensor base change along completion/localization, together
  with the canonical tensor-product/product comparison;
- sampled owner declarations:
  `principalPowerIdealImageQuotientMap`,
  `principalAdicCompletion_quotientMap_bijective`,
  `tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective`,
  `TensorProduct.prodRight`;
- best owner abstraction: the source-facing statement is nontriviality after base change to the
  product ring `R' × R_f`; its core support comes from the canonical quotient-map owner
  `principalPowerIdealImageQuotientMap` on the powers of `(f)`, the ideal-power-torsion
  base-change theorem from Lemma `15.89.9`, the principal completion specialization
  `principalAdicCompletion_quotientMap_bijective`, and the product tensor equivalence
  `TensorProduct.prodRight`;
- primitive data: the algebra map `R → R'`, the element `f`, the `R`-module `M`, and the
  quotient-map bijectivity hypothesis for `(f)^n`;
- derived API: the completion specialization and the decomposition of the tensor product with a
  product algebra into the corresponding product of tensor products;
- triage: the first theorem is `source-facing`, the completion specialization is a `bridge/view`,
  and the tensor-product/product equivalence is the `core/canonical` owner abstraction.
-/

-- Proof sketch: if `M ⊗[R] Localization.Away f` were trivial, then every element of `M` would be
-- killed by a power of `f`. Lemma `tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective`
-- then identifies `M ⊗[R] R'` with `M`, so the `R'`-summand stays nontrivial. Finally, tensoring
-- with the finite direct sum `R' ⊕ R_f` decomposes into the corresponding product of tensor
-- products.
/-- Lemma 15.91.2: if the canonical maps `R / (f)^n → R' / (f)^n R'` are bijective for every
positive integer `n`, then tensoring any nontrivial `R`-module with `R' × R_f` remains
nontrivial. -/
theorem tensorProduct_prod_localizationAway_nontrivial_of_quotientMapBijective
    [Nontrivial M]
    (hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R R') f n)) :
    Nontrivial (M ⊗[R] (R' × Localization.Away f)) := sorry

-- Proof sketch: apply
-- `tensorProduct_prod_localizationAway_nontrivial_of_quotientMapBijective` with
-- `R' = principalAdicCompletion f`, and use
-- `principalAdicCompletion_quotientMap_bijective` to verify the quotient-map hypothesis in the
-- principal-image form used above.
/-- The `(f)`-adic completion and the localization away from `f` jointly detect nontrivial
`R`-modules. -/
theorem tensorProduct_completion_prod_localizationAway_nontrivial
    [Nontrivial M] :
    Nontrivial
      (M ⊗[R] (principalAdicCompletion f × Localization.Away f)) := sorry

end

/-! ### Lemma_15_91_3 (from Chap15) -/
open PrimeSpectrum

universe u v

section

variable {R : Type u} [CommRing R]

/- Domain-style sampling:
* primary domain: commutative algebra of prime spectra under quotient and localization;
* sampled owner declarations:
  `principalIdealQuotientMap`,
  `PrimeSpectrum.comap`,
  `PrimeSpectrum.localization_away_comap_range`,
  `principalAdicCompletion_quotientMap_bijective`;
* best owner abstraction: the chapter owner `principalIdealQuotientMap` for reduction modulo
  `(f)`, together with the canonical prime-spectrum maps `PrimeSpectrum.comap`;
* primitive data: a ring map `R → R'` and an element `f : R`;
* derived API: the surjectivity of
  `Spec R' ⊔ Spec R_f → Spec R` under the quotient-map bijectivity hypothesis;
* triage: `source-facing` = the surjectivity statement below, `core/canonical` =
  `principalIdealQuotientMap` and `PrimeSpectrum.comap`, `bridge/view` =
  the completion specialization.
-/

-- Proof sketch: decompose `Spec(R)` as `V(f) ∪ D(f)`. The quotient-bijectivity hypothesis
-- identifies the image of `Spec(R')` with `V(f)` via the canonical quotient map
-- `principalIdealQuotientMap (algebraMap R R') f rfl : R ⧸ (f) →+* R' ⧸ (f R')`,
-- while `PrimeSpectrum.localization_away_comap_range` identifies the localization summand with
-- `D(f)`.
/-- Lemma 15.91.3: if `R → R'` induces an isomorphism `R / (f) → R' / (f)R'`, then the induced
map `Spec(R') ⊔ Spec(R_f) → Spec(R)` is surjective. -/
theorem primeSpectrum_sum_surjective_of_quotientByPrincipalIdeal_bijective
    {R' : Type v} [CommRing R'] [Algebra R R']
    (f : R)
    (hquot : Function.Bijective (principalIdealQuotientMap (algebraMap R R') f rfl)) :
    Function.Surjective
      (Sum.elim
        (comap (algebraMap R R'))
        (comap (algebraMap R (Localization.Away f)))) := sorry

-- Proof sketch: apply
-- `primeSpectrum_sum_surjective_of_quotientByPrincipalIdeal_bijective` with
-- `R' = principalAdicCompletion f`; Lemma `15.91.1` supplies the quotient
-- bijectivity assumption.
/-- The `(f)`-adic completion and the localization away from `f` cover `Spec(R)`. -/
theorem primeSpectrum_completion_sum_surjective (f : R) :
    Function.Surjective
      (Sum.elim
        (comap (algebraMap R (principalAdicCompletion f)))
        (comap (algebraMap R (Localization.Away f)))) := sorry

end

/-! ### Lemma_15_91_4 (from Chap15) -/
open scoped TensorProduct

universe u v w

section

variable {R : Type u} [CommRing R]
variable {R' : Type w} [CommRing R'] [Algebra R R']
variable {M : Type v} [AddCommMonoid M] [Module R M]

local notation "Away" => LocalizedModule.Away

/- Domain-style sampling:
- primary domain: finite-generation descent for modules in the Beauville-Laszlo completion and
  localization setting;
- sampled owner declarations:
  `principalPowerIdealImageQuotientMap`,
  `tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective`,
  `LocalizedModule.equivTensorProduct`,
  `adicCompletion_quotientMap_bijective`;
- best owner abstraction: the finite-generation criterion naturally lives on the pair of canonical
  base-change objects `R' ⊗[R] M` and `Away f M`; the completion case is a source-faithful
  specialization through `principalAdicCompletion`;
- primitive data: the algebra map `R → R'`, the element `f : R`, the `R`-module `M`, and the
  principal-power quotient bijectivity hypothesis;
- derived API: the completion specialization;
- triage:
  - `source-facing`: the finite-generation descent criterion;
  - `core/canonical`: the owner objects `R' ⊗[R] M`, `Away f M`, and the chapter owner
    `principalPowerIdealImageQuotientMap`;
  - `bridge/view`: the specialization to `principalAdicCompletion f`.
-/

-- Proof sketch: the forward implication is preserved by extension of scalars and localization. For
-- the converse, choose a surjection from a finite free `R`-module onto `M` whose image generates
-- both `R' ⊗[R] M` and `M_f`; its cokernel becomes zero after tensoring with `R'` and after
-- localizing away from `f`, so Lemma `15.91.2` forces that cokernel to vanish, proving that `M`
-- is finitely generated over `R`.
/-- Lemma 15.91.4: if the quotient maps `R / (f)^n → R' / (f)^n R'` are bijective for all
positive integers `n`, then an `R`-module `M` is finitely generated if and only if both its base
change `R' ⊗[R] M` and its localization `Away f M` are finitely generated over
`R'` and `Localization.Away f`, respectively. -/
theorem moduleFinite_iff_finite_tensor_and_localizedAway_of_quotientMapBijective
    (f : R)
    (hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R R') f n)) :
    Module.Finite R M ↔
      Module.Finite R' (R' ⊗[R] M) ∧
        Module.Finite (Localization.Away f) (Away f M) := sorry

-- Proof sketch: apply
-- `moduleFinite_iff_finite_tensor_and_localizedAway_of_quotientMapBijective` with
-- `R' = principalAdicCompletion f`, and use Lemma `15.91.1` to supply the
-- required quotient-map bijectivity for the `(f)`-adic completion.
/-- The completion-localization Beauville-Laszlo criterion for finite generation, in owner form. -/
theorem moduleFinite_of_finite_completion_and_localizedAway
    (f : R)
    (hfiniteCompletion :
      Module.Finite
        (principalAdicCompletion f)
        (principalAdicCompletion f ⊗[R] M))
    (hfiniteLocalization :
      Module.Finite (Localization.Away f) (Away f M)) :
    Module.Finite R M := sorry

end

/-! ### Remark_15_91_5 (from Chap15) -/
/- Domain-style sampling:
* primary domain: Beauville-Laszlo completion/localization counterexamples in commutative algebra;
* sampled owner declarations:
  `principalAdicCompletion`,
  `IsLocalization.flat`,
  `Localization.Away`,
  `firstBeauvilleLaszloCounterexample_completion_not_flat`;
* owner abstraction: the canonical completion-side owner is
  the direct flatness predicate on the canonical completion map
  `R → principalAdicCompletion f`; the localization side stays on the canonical map
  `R → Localization.Away f`, with flatness recorded by `RingHom.Flat`;
* primitive data: a commutative ring `R` and an element `f : R`;
* derived API: the explicit first Beauville-Laszlo counterexample together with the upstream
  completion nonflatness theorem from Example `15.91.9`.

Source/core/bridge triage:
* `source-facing`: the existential comparison in Remark `15.91.5`;
* `core/canonical`: `principalAdicCompletion`, `Localization.Away`, and `RingHom.Flat`;
* `bridge/view`: the explicit quotient-ring counterexample from Example `15.91.9`, especially its
  direct completion nonflatness theorem.
-/

/-- Remark 15.91.5: there exist a commutative ring `R` and an element `f : R` such that the
localization map `R → R_f` is flat, but the `f`-adic completion map
`R → principalAdicCompletion f` is not flat. Consequently, the Beauville-Laszlo cover
`R → R^∧ ⊕ R_f` cannot in general be treated by faithfully flat descent. -/
theorem exists_flat_localization_and_nonflat_principalAdicCompletion :
    ∃ (R : Type) (_ : CommRing R) (f : R),
      (algebraMap R (Localization.Away f)).Flat ∧
        ¬ (algebraMap R (principalAdicCompletion f)).Flat := by
  refine ⟨firstBeauvilleLaszloCounterexampleRing ℚ, inferInstance,
    firstBeauvilleLaszloCounterexample_f ℚ, ?_⟩
  exact ⟨RingHom.flat_algebraMap_iff.mpr <|
      IsLocalization.flat
        (Localization.Away (firstBeauvilleLaszloCounterexample_f ℚ))
        (Submonoid.powers (firstBeauvilleLaszloCounterexample_f ℚ)),
    firstBeauvilleLaszloCounterexample_completion_not_flat ℚ⟩

/-! ### Lemma_15_91_6 (from Chap15) -/
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

/-! ### Remark_15_91_7 (from Chap15) -/
universe u

section

open Module
open scoped nonZeroDivisors
open AdicCompletion

variable {R : Type u} [CommRing R]

/-
Domain-style sampling:
- primary domain: commutative algebra of the Beauville-Laszlo Cech sequence for the principal-adic
  completion map `R → principalAdicCompletion f`;
- sampled owner declarations:
  `principalAdicCompletion`,
  `IsBeauvilleLaszloGlueingPairAlong`,
  `principalAdicCompletion_isBeauvilleLaszloGlueingPairAlong_iff_bijective_fPowerTorsion`,
  `primaryComponent_principalIdeal_eq_fPowerTorsion`,
  `powerTorsionSubmodule_eq_bot_of_injective_awayLocalizationFamilyMap`,
  `Ideal.primaryComponent`;
- best owner abstraction: the chapter owner `IsBeauvilleLaszloGlueingPairAlong`, specialized to
  the completion owner `principalAdicCompletion`; the source-facing `f^∞`-torsion notation is a
  bridge to the canonical torsion owner `(principalIdeal f).primaryComponent`;
- primitive data: a commutative ring `R` and an element `f : R`;
- derived API: the completion-side nonzerodivisor statement and the source theorem that a
  nonzerodivisor yields this exact completion-localization glueing pair;
- triage: `core/canonical` = `principalAdicCompletion` together with
  `IsBeauvilleLaszloGlueingPairAlong` and `Ideal.primaryComponent`,
  `bridge/view` = the completion specialization below,
  `source-facing` =
  `principalAdicCompletion_isBeauvilleLaszloGlueingPairAlong_of_mem_nonZeroDivisors`,
  `bridge/view` also includes the torsion-vanishing and completion-side nonzerodivisor comparison
  theorems below.
-/

private theorem fPowerTorsion_eq_bot_of_algebraMap_mem_nonZeroDivisors
    {S : Type u} [CommRing S] [Algebra R S] (f : R)
    (hf : algebraMap R S f ∈ nonZeroDivisors S) :
    Submodule.torsion' R S (Submonoid.powers f) = ⊥ := by
  sorry

-- Proof sketch: apply Algebra Lemma `10.96.4` to the exact sequence
-- `0 → R --f--> R → R / (f) → 0`. The induced completion map on the first arrow is
-- multiplication by the image of `f`, so its injectivity shows that image is a nonzerodivisor.
private theorem principalAdicCompletion_mem_nonZeroDivisors_of_mem_nonZeroDivisors
    (f : R) (hf : f ∈ nonZeroDivisors R) :
    algebraMap R (principalAdicCompletion f) f ∈
      nonZeroDivisors (principalAdicCompletion f) := by
  sorry

-- Proof sketch: after the previous theorem, both `R[f^∞]` and `R^∧[f^∞]` vanish, so Lemma
-- `15.91.6` gives the exact Beauville-Laszlo Cech condition for the completion pair.
/-- Remark 15.91.7: if `f` is a nonzerodivisor in `R`, then `(R, f)` is a Beauville-Laszlo
glueing pair for the completion map. -/
theorem principalAdicCompletion_isBeauvilleLaszloGlueingPairAlong_of_mem_nonZeroDivisors
    (f : R) (hf : f ∈ nonZeroDivisors R) :
    IsBeauvilleLaszloGlueingPairAlong (algebraMap R (principalAdicCompletion f)) f := by
  sorry

end

/-! ### Remark_15_91_8 (from Chap15) -/
noncomputable section

universe u

open scoped IdealPowerTorsion

/-
Domain-style sampling:
* primary domain: Beauville-Laszlo glueing pairs for principal-adic completion, with fixed-power
  torsion as a bridge statement;
* sampled owner declarations:
  `IsBeauvilleLaszloGlueingPairAlong`,
  `principalAdicCompletion_isBeauvilleLaszloGlueingPairAlong_iff_bijective_fPowerTorsion`,
  `tensorBaseChangeUnitPrimaryComponent_bijective`,
  `Submodule.torsionBy`,
  `principalAdicCompletion`;
* owner abstraction: the chapter-level glueing-pair owner
  `IsBeauvilleLaszloGlueingPairAlong (algebraMap R (principalAdicCompletion f)) f`;
* primitive data: a commutative ring `R`, an element `f : R`, and flatness of
  `R → principalAdicCompletion f`;
* derived API: the induced map on `f ^ n`-torsion, its bijectivity consequences, and the resulting
  Beauville-Laszlo glueing-pair criterion.

Source/core/bridge triage:
* `source-facing`: the fixed-power torsion comparison together with the concluding
  Beauville-Laszlo glueing-pair statement in Remark `15.91.8`;
* `core/canonical`: `IsBeauvilleLaszloGlueingPairAlong`,
  `principalAdicCompletion_isBeauvilleLaszloGlueingPairAlong_iff_bijective_fPowerTorsion`, and
  `tensorBaseChangeUnitPrimaryComponent_bijective`;
* `bridge/view`: the restricted completion map between the two torsion submodules.
-/

section

variable {R : Type u} [CommRing R]

-- Proof sketch: if `x` is killed by `f^n` in `R`, then applying the algebra map to the equality
-- `(f^n) * x = 0` shows that the image of `x` is killed by the image of `f^n` in the completion.
/-- The algebra map sends `f^n`-torsion elements of `R` to `f^n`-torsion elements of the
principal adic completion. -/
private theorem completionMap_mem_powTorsion
    (f : R) (n : ℕ) (x : (R[f ^ n] : Submodule R R)) :
    Algebra.linearMap R (principalAdicCompletion f) x ∈
      ((principalAdicCompletion f)[f ^ n] : Submodule R (principalAdicCompletion f)) := sorry

/-- The canonical map from the `f^n`-torsion of `R` to the `f^n`-torsion of its principal adic
completion. -/
abbrev powTorsionToPrincipalAdicCompletion (f : R) (n : ℕ) :
    (R[f ^ n] : Submodule R R) →ₗ[R]
      ((principalAdicCompletion f)[f ^ n] : Submodule R (principalAdicCompletion f)) :=
  ((Algebra.linearMap R (principalAdicCompletion f)).domRestrict
      (R[f ^ n] : Submodule R R)).codRestrict
    ((principalAdicCompletion f)[f ^ n] : Submodule R (principalAdicCompletion f))
    (completionMap_mem_powTorsion f n)

-- Proof sketch: tensor the exact sequence `0 → R[f^n] → R → R` with the flat completion
-- `principalAdicCompletion f`. Flatness preserves exactness, so the tensor product identifies with
-- the kernel of multiplication by `f^n` on the completion. Apply
-- `tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective` with
-- `R' = principalAdicCompletion f`, using `principalAdicCompletion_quotientMap_bijective` to
-- discharge the quotient-map hypothesis, to identify `R[f^n]` with that tensor product.
/-- Remark 15.91.8: if the canonical map from `R` to its `(f)`-adic completion is flat, then for
every natural number `n` the induced map `R[f^n] → R^∧[f^n]` is bijective; this source-faithful
statement is generalized from positive `n` by the canonical trivial case `n = 0`. -/
theorem powTorsionToPrincipalAdicCompletion_bijective_of_flat
    (f : R)
    (hflat : (algebraMap R (principalAdicCompletion f)).Flat)
    (n : ℕ) :
    Function.Bijective (powTorsionToPrincipalAdicCompletion f n) := sorry

-- Proof sketch: the chapter owner theorem
-- `principalAdicCompletion_isBeauvilleLaszloGlueingPairAlong_iff_bijective_fPowerTorsion`
-- reduces the Beauville-Laszlo condition to bijectivity on `f^∞`-torsion. Lemma `15.90.3`
-- supplies that bijectivity from flatness of the completion map together with the quotient
-- comparison for `(f)`, and Lemma `15.91.1` provides the latter comparison.
/-- Remark 15.91.8: if the canonical map from `R` to its `(f)`-adic completion is flat, then
`(R, f)` is a Beauville-Laszlo glueing pair. -/
theorem isBeauvilleLaszloGlueingPair_of_flat
    (f : R)
    (hflat : (algebraMap R (principalAdicCompletion f)).Flat) :
    IsBeauvilleLaszloGlueingPairAlong (algebraMap R (principalAdicCompletion f)) f := by
  sorry

-- Proof sketch: for a Noetherian ring, Algebra Lemma `10.97.2` gives flatness of the canonical
-- map `R → principalAdicCompletion f`. Applying the previous theorem supplies the bijectivity for
-- each natural number `n`.
/-- Over a Noetherian ring, the map on `f^n`-torsion from `R` to its `(f)`-adic completion is
bijective for every natural number `n`. -/
theorem powTorsionToPrincipalAdicCompletion_bijective_of_isNoetherianRing
    [IsNoetherianRing R] (f : R) (n : ℕ) :
    Function.Bijective (powTorsionToPrincipalAdicCompletion f n) := by
  simpa using powTorsionToPrincipalAdicCompletion_bijective_of_flat f
    (adicCompletion_algebraMap_flat (Ideal.span ({f} : Set R))) n

-- Proof sketch: for Noetherian `R`, Lemma `10.97.2` gives flatness of the completion map, and the
-- previous theorem upgrades this to the canonical Beauville-Laszlo owner statement.
/-- In particular, if `R` is Noetherian, then `(R, f)` is a Beauville-Laszlo glueing pair. -/
theorem isBeauvilleLaszloGlueingPair_of_isNoetherianRing
    [IsNoetherianRing R] (f : R) :
    IsBeauvilleLaszloGlueingPairAlong (algebraMap R (principalAdicCompletion f)) f := by
  simpa using isBeauvilleLaszloGlueingPair_of_flat f
    (adicCompletion_algebraMap_flat (Ideal.span ({f} : Set R)))

end

/-! ### Example_15_91_9 (from Chap15) -/
noncomputable section

universe u

/- Domain-style sampling:
* primary domain: Beauville-Laszlo completion counterexamples in commutative algebra;
* sampled owner declarations:
  `MvPolynomial.X`,
  `Ideal.Quotient.mk`,
  `principalAdicCompletion`,
  `IsBeauvilleLaszloGlueingPairAlong`;
* owner abstraction: the chapter owners governing the `f^∞`-torsion comparison map and the
  Beauville-Laszlo glueing-pair property for the completion pair `(R → R^∧, f)`;
* primitive data: the two explicit quotient rings, their distinguished element `f`, and their
  completions, all definable over `[CommRing k]`;
* derived API: noninjectivity or nonsurjectivity of the torsion comparison map, and the resulting
  non-glueing and non-flatness consequences, which keep the later `[Field k]` hypothesis.

Source/core/bridge triage:
* `source-facing`: the two explicit quotient-ring counterexamples themselves;
* `core/canonical`: `fPowerTorsionToExtension`,
  `IsBeauvilleLaszloGlueingPairAlong`, and `isBeauvilleLaszloGlueingPair_of_flat`;
* `bridge/view`: the specialization of those chapter owners to the two explicit rings in this
  file.
-/

section

variable (k : Type u) [CommRing k]

/-- The indeterminates `f, T₁, T₂, \ldots` used in the Beauville-Laszlo completion counterexamples.
-/
inductive BeauvilleLaszloCounterexampleVar
  | f
  | t (n : ℕ)
  deriving DecidableEq

/-- The polynomial variable `f` in the explicit Beauville-Laszlo counterexample rings. -/
abbrev beauvilleLaszloCounterexample_fVar :
    MvPolynomial BeauvilleLaszloCounterexampleVar k :=
  MvPolynomial.X .f

/-- The polynomial variable `T_(n+1)` in the explicit Beauville-Laszlo counterexample rings. -/
abbrev beauvilleLaszloCounterexample_tVar (n : ℕ) :
    MvPolynomial BeauvilleLaszloCounterexampleVar k :=
  MvPolynomial.X (.t n)

/-- The `n`-th defining relation of
`k[f, T₁, T₂, \ldots] / (fT₁, fT₂ - T₁, fT₃ - T₂, \ldots)`. -/
def firstBeauvilleLaszloCounterexampleRelation :
    ℕ → MvPolynomial BeauvilleLaszloCounterexampleVar k
  | 0 =>
      beauvilleLaszloCounterexample_fVar k * beauvilleLaszloCounterexample_tVar k 0
  | n + 1 =>
      beauvilleLaszloCounterexample_fVar k * beauvilleLaszloCounterexample_tVar k (n + 1) -
        beauvilleLaszloCounterexample_tVar k n

/-- The ideal generated by the relations
`fT₁, fT₂ - T₁, fT₃ - T₂, \ldots`. -/
def firstBeauvilleLaszloCounterexampleIdeal :
    Ideal (MvPolynomial BeauvilleLaszloCounterexampleVar k) :=
  Ideal.span (Set.range (firstBeauvilleLaszloCounterexampleRelation k))

/-- The ring
`k[f, T₁, T₂, \ldots] / (fT₁, fT₂ - T₁, fT₃ - T₂, \ldots)`. -/
abbrev firstBeauvilleLaszloCounterexampleRing :=
  MvPolynomial BeauvilleLaszloCounterexampleVar k ⧸ firstBeauvilleLaszloCounterexampleIdeal k

/-- The distinguished element `f` in the first Beauville-Laszlo counterexample ring. -/
abbrev firstBeauvilleLaszloCounterexample_f :
    firstBeauvilleLaszloCounterexampleRing k :=
  Ideal.Quotient.mk _ (beauvilleLaszloCounterexample_fVar k)

/-- The class of `T₁` in the first Beauville-Laszlo counterexample ring. -/
abbrev firstBeauvilleLaszloCounterexample_t1 :
    firstBeauvilleLaszloCounterexampleRing k :=
  Ideal.Quotient.mk _ (beauvilleLaszloCounterexample_tVar k 0)

/-- The `n`-th defining relation of
`k[f, T₁, T₂, \ldots] / (fT₁, f^2 T₂, f^3 T₃, \ldots)`. -/
def secondBeauvilleLaszloCounterexampleRelation :
    ℕ → MvPolynomial BeauvilleLaszloCounterexampleVar k
  | n =>
      beauvilleLaszloCounterexample_fVar k ^ (n + 1) *
        beauvilleLaszloCounterexample_tVar k n

/-- The ideal generated by the relations `fT₁, f^2 T₂, f^3 T₃, \ldots`. -/
def secondBeauvilleLaszloCounterexampleIdeal :
    Ideal (MvPolynomial BeauvilleLaszloCounterexampleVar k) :=
  Ideal.span (Set.range (secondBeauvilleLaszloCounterexampleRelation k))

/-- The ring `k[f, T₁, T₂, \ldots] / (fT₁, f^2 T₂, f^3 T₃, \ldots)`. -/
abbrev secondBeauvilleLaszloCounterexampleRing :=
  MvPolynomial BeauvilleLaszloCounterexampleVar k ⧸ secondBeauvilleLaszloCounterexampleIdeal k

/-- The distinguished element `f` in the second Beauville-Laszlo counterexample ring. -/
abbrev secondBeauvilleLaszloCounterexample_f :
    secondBeauvilleLaszloCounterexampleRing k :=
  Ideal.Quotient.mk _ (beauvilleLaszloCounterexample_fVar k)

/-- The class of `T₁` in the second Beauville-Laszlo counterexample ring. -/
abbrev secondBeauvilleLaszloCounterexample_t1 :
    secondBeauvilleLaszloCounterexampleRing k :=
  Ideal.Quotient.mk _ (beauvilleLaszloCounterexample_tVar k 0)

section

variable [Field k]

/-- In the first ring, the map `R[f^∞] → R^∧[f^∞]` is not injective. -/
theorem firstBeauvilleLaszloCounterexample_fPowerTorsionToExtension_not_injective
    :
    ¬ Function.Injective
      (fPowerTorsionToExtension
        (algebraMap
          (firstBeauvilleLaszloCounterexampleRing k)
          (principalAdicCompletion (firstBeauvilleLaszloCounterexample_f k)))
        (firstBeauvilleLaszloCounterexample_f k)) := by
  sorry

/-- In the second ring, the map `R[f^∞] → R^∧[f^∞]` is not surjective. -/
theorem secondBeauvilleLaszloCounterexample_fPowerTorsionToExtension_not_surjective
    :
    ¬ Function.Surjective
      (fPowerTorsionToExtension
        (algebraMap
          (secondBeauvilleLaszloCounterexampleRing k)
          (principalAdicCompletion (secondBeauvilleLaszloCounterexample_f k)))
        (secondBeauvilleLaszloCounterexample_f k)) := by
  sorry

/-- Consequently, the first pair `(R, f)` is not a Beauville-Laszlo glueing pair. -/
theorem firstBeauvilleLaszloCounterexample_not_glueing_pair
    :
    ¬ IsBeauvilleLaszloGlueingPairAlong
        (algebraMap
          (firstBeauvilleLaszloCounterexampleRing k)
          (principalAdicCompletion (firstBeauvilleLaszloCounterexample_f k)))
        (firstBeauvilleLaszloCounterexample_f k) := by
  sorry

/-- By Remark `15.91.8`, the completion map in the first example is not flat. -/
theorem firstBeauvilleLaszloCounterexample_completion_not_flat
    :
    ¬ (algebraMap
        (firstBeauvilleLaszloCounterexampleRing k)
        (principalAdicCompletion (firstBeauvilleLaszloCounterexample_f k))).Flat := by
  sorry

/-- By Remark `15.91.8`, the completion map in the second example is not flat. -/
theorem secondBeauvilleLaszloCounterexample_completion_not_flat
    :
    ¬ (algebraMap
        (secondBeauvilleLaszloCounterexampleRing k)
        (principalAdicCompletion (secondBeauvilleLaszloCounterexample_f k))).Flat := by
  sorry

end

end

/-! ### Lemma_15_91_10 (from Chap15) -/
open scoped TensorProduct
open scoped IdealPowerTorsion

noncomputable section

universe u

/- Domain-style sampling:
- primary domain: Beauville-Laszlo module glueability, expressed through the module Cech short
  complex and the canonical tensor base-change map on `(f)^∞`-torsion;
- sampled owner declarations:
  `beauvilleLaszloModuleCechSequence`,
  `tensorBaseChangeUnitPrimaryComponent`,
  `TensorProduct.comm`,
  `IsBeauvilleLaszloGlueingPairAlong`;
- best owner abstraction: the primitive comparison map is the chapter owner
  `tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M`, i.e. the canonical tensor
  base-change unit restricted to the primary component for `(f)`;
- primitive data vs derived API: the primitive data are the module Cech short complex and the
  canonical primary-component base-change map; the injectivity, surjectivity, and glueability
  criteria are derived API.

Source/core/bridge triage:
- `source-facing`: the Beauville-Laszlo exactness criteria for modules;
- `core/canonical`: `(beauvilleLaszloModuleCechSequence R' M f).ShortExact` and
  `tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M`;
- `bridge/view`: the textbook right-tensor order `M ⊗[R] R'`, related by tensor symmetry to the
  canonical owner `R' ⊗[R] M`.
-/

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable {M : Type u} [AddCommGroup M] [Module R M]

-- Proof sketch: tensor the right exact ring sequence `R → R' → R'_f` with `M`. Right exactness of
-- `M ⊗[R] -` turns the surjectivity statement from Lemma `15.91.6` into surjectivity of the
-- module-side right map.
/-- The module Beauville-Laszlo sequence is exact on the right under the quotient-isomorphism
hypothesis. -/
theorem beauvilleLaszloModuleCechRightMap_surjective_of_principalPowerQuotientMapBijective
    (f : R) (hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R R') f n)) :
    Function.Surjective ((beauvilleLaszloModuleCechSequence R' M f).g.hom) := sorry

-- Proof sketch: the kernel of `M → M ⊗[R] Localization.Away f` is `M[f^∞]`. Therefore the left
-- Cech map is injective exactly when the comparison map from `M[f^∞]` to the `f^∞`-torsion of
-- `R' ⊗[R] M` is injective; via tensor symmetry this is the usual map to `(M ⊗[R] R')[f^∞]`.
/-- The module Beauville-Laszlo sequence is exact on the left exactly when the canonical
base-change map on `(f)^∞`-torsion is injective. -/
theorem beauvilleLaszloModuleCechLeftMap_injective_iff_fPowerTorsionToTensor_injective
    (f : R) :
    Function.Injective ((beauvilleLaszloModuleCechSequence R' M f).f.hom) ↔
      Function.Injective (tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M) := sorry

-- Proof sketch: if the sequence is exact in the middle, then an `f^∞`-torsion element of
-- `R' ⊗[R] M` yields a kernel element of the right map and so comes from `M`. Conversely,
-- surjectivity on `f^∞`-torsion lets one lift the torsion correction needed to express a kernel
-- element of the right map as the image of an element of `M`.
/-- Under the quotient-isomorphism hypothesis, the module Beauville-Laszlo sequence is exact in the
middle exactly when the canonical base-change map on `(f)^∞`-torsion is surjective. -/
theorem beauvilleLaszloModuleCech_exact_iff_fPowerTorsionToTensor_surjective
    (f : R) (hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R R') f n)) :
    Function.Exact
      ((beauvilleLaszloModuleCechSequence R' M f).f.hom)
      ((beauvilleLaszloModuleCechSequence R' M f).g.hom) ↔
    Function.Surjective (tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M) := sorry

-- Proof sketch: combine right exactness with the previous injectivity and surjectivity criteria.
-- Glueability is injectivity on the left, exactness in the middle, and surjectivity on the right,
-- so under the quotient-isomorphism hypothesis it is equivalent to bijectivity on `f^∞`-torsion.
/-- Lemma 15.91.10: if `R → R'` induces isomorphisms `R / f^n R → R' / f^n R'` for all positive
integers `n`, then `M` is glueable for `(R → R', f)` if and only if the induced map
on `(f)^∞`-torsion is bijective. -/
theorem isBeauvilleLaszloGlueableAlong_iff_bijective_fPowerTorsionToTensor
    (f : R) (hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R R') f n)) :
    (beauvilleLaszloModuleCechSequence R' M f).ShortExact ↔
      Function.Bijective (tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M) := sorry

-- Proof sketch: if `(R → R', f)` is a glueing pair, the ring-level Beauville-Laszlo sequence is
-- exact, and tensoring that exact sequence with `M` gives exactness in the middle for the
-- module-side sequence. The main criterion then reduces glueability to injectivity on
-- the canonical base-change map on `(f)^∞`-torsion.
/-- For a Beauville-Laszlo glueing pair `(R → R', f)`, module glueability is equivalent to
injectivity on `f^∞`-torsion. -/
theorem isBeauvilleLaszloGlueableAlong_iff_injective_fPowerTorsionToTensor_of_glueingPair
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    (beauvilleLaszloModuleCechSequence R' M f).ShortExact ↔
      Function.Injective (tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M) := sorry

end

section

variable {R : Type u} [CommRing R]

variable {M : Type u} [AddCommGroup M] [Module R M]

-- Proof sketch: specialize the previous theorem to `R' = R^∧`. For a Beauville-Laszlo glueing
-- pair `(R, f)`, the completion pair is exact in the middle for every `M`, so only injectivity of
-- the canonical base-change map on `(f)^∞`-torsion remains.
/-- If `(R, f)` is a Beauville-Laszlo glueing pair, then `M` is glueable along the completion map
if and only if the canonical base-change map on `(f)^∞`-torsion is injective. -/
theorem isBeauvilleLaszloGlueableAlong_principalAdicCompletion_iff_injective_fPowerTorsionToTensor_of_glueingPair
    (f : R)
    (hpair : IsBeauvilleLaszloGlueingPairAlong
      (algebraMap R (principalAdicCompletion f))
      f) :
    (beauvilleLaszloModuleCechSequence (principalAdicCompletion f) M f).ShortExact ↔
      Function.Injective
        (tensorBaseChangeUnitPrimaryComponent
          (principalAdicCompletion f)
          (principalIdeal f)
          M) := sorry

end

/-! ### Remark_15_91_11 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open scoped IdealPowerTorsion
open scoped TensorProduct

noncomputable section

universe u

/- Domain-style sampling:
- primary domain: Beauville-Laszlo glueability for the completion pair, expressed through
  principal-power torsion and completion maps;
- sampled owner declarations:
  `principalAdicCompletion`,
  `(beauvilleLaszloModuleCechSequence R' M f).ShortExact`,
  `Tor[R, p](M, N)`,
  `tensorBaseChangeUnitPrimaryComponent`,
  `AdicCompletion.of`,
  `Submodule.torsionBy`,
  `isBeauvilleLaszloGlueableAlong_principalAdicCompletion_iff_injective_fPowerTorsionToTensor_of_glueingPair`,
  `AdicCompletion.of_injective_iff`,
  `LinearMap.injective_domRestrict_iff`;
- best owner abstraction: the canonical glueability owner
  `(beauvilleLaszloModuleCechSequence R' M f).ShortExact`, with the principal-component
  comparison map `tensorBaseChangeUnitPrimaryComponent` specialized to
  `R' = principalAdicCompletion f`; the source-facing completion bridge is the restriction
  `fTorsionToAdicCompletion M f` of `AdicCompletion.of (principalIdeal f) M` to the
  canonical finite-stage torsion submodule `M[f^1]`.

Primitive-vs-derived split:
- primitive data: a commutative ring `R`, an `R`-module `M`, an element `f : R`, and in the
  completion case the owner map
  `tensorBaseChangeUnitPrimaryComponent (principalAdicCompletion f) (principalIdeal f) M`
  together with the canonical completion map `AdicCompletion.of (principalIdeal f) M`;
- derived API: the source-facing bridge maps to the full completion tensor product and to the
  module completion itself, together with the remark’s injectivity and Tor-vanishing criteria.

Layer triage:
- `source-facing`: the completion-valued criteria stated in Remark `15.91.11`;
- `core/canonical`: `(beauvilleLaszloModuleCechSequence R' M f).ShortExact`,
  `principalAdicCompletion`, and
  `tensorBaseChangeUnitPrimaryComponent (principalAdicCompletion f) (principalIdeal f) M`;
- `bridge/view`: `completionFPowerTorsionToCompletionTensor` and
  `fTorsionToAdicCompletion`.
-/

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']

/-- The map `M[f^∞] → M ⊗[R] R^∧` obtained by composing the Beauville-Laszlo torsion comparison
with the inclusion of `(M ⊗[R] R^∧)[f^∞]` into the full tensor product. -/
abbrev completionFPowerTorsionToCompletionTensor
    (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    (M[f^∞] : Submodule R M) →ₗ[R] M ⊗[R] principalAdicCompletion f :=
  let A := principalAdicCompletion f
  let targetTorsion : Submodule R (A ⊗[R] M) :=
    ((Ideal.map (algebraMap R A) (principalIdeal f)).primaryComponent (A ⊗[R] M)).restrictScalars R
  let hsource : (principalIdeal f).primaryComponent M = (M[f^∞] : Submodule R M) :=
    Module.primaryComponent_principalIdeal_eq_fPowerTorsion f
  let η : (M[f^∞] : Submodule R M) →ₗ[R] targetTorsion :=
    (tensorBaseChangeUnitPrimaryComponent A (principalIdeal f) M).comp
      (LinearEquiv.ofEq _ _ hsource).symm.toLinearMap
  (TensorProduct.comm R A M).toLinearMap.comp <|
    targetTorsion.subtype.comp η

variable {M : Type u} [AddCommGroup M] [Module R M]

/-- The canonical map `M[f^1] → M^∧` to the `(f)`-adic completion of `M`, modeled as the
restriction of `AdicCompletion.of (principalIdeal f) M` to the canonical finite-stage
`f`-torsion submodule `M[f^1]`. -/
abbrev fTorsionToAdicCompletion (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    (M[f^1] : Submodule R M) →ₗ[R] AdicCompletion (principalIdeal f) M :=
  (AdicCompletion.of (principalIdeal f) M).domRestrict (M[f^1] : Submodule R M)

/-- The source-facing completion-tensor map is injective exactly when the canonical Beauville-
Laszlo torsion comparison map into the completion-side `f^∞`-torsion submodule is injective. -/
theorem completionFPowerTorsionToCompletionTensor_injective_iff
    (f : R) :
    Function.Injective (completionFPowerTorsionToCompletionTensor M f) ↔
      Function.Injective
        (tensorBaseChangeUnitPrimaryComponent
          (principalAdicCompletion f)
          (principalIdeal f)
          M) := sorry

-- Proof sketch: specialize the completion-side Beauville-Laszlo criterion, then compose the
-- target with the inclusion of the completion-side `f^∞`-torsion submodule into the full tensor
-- product `M ⊗[R] R^∧`.
/-- Remark 15.91.11 (1): the module `M` is glueable along the completion map exactly when the
natural map `M[f^∞] → M ⊗[R] R^∧` is injective. -/
theorem isBeauvilleLaszloGlueableAlong_principalAdicCompletion_iff_injective_fPowerTorsionToCompletionTensor
    (f : R) :
    (beauvilleLaszloModuleCechSequence (principalAdicCompletion f) M f).ShortExact ↔
      Function.Injective (completionFPowerTorsionToCompletionTensor M f) := sorry

/-- A nonzero `f^∞`-torsion class mapping to zero in `M ⊗[R] R^∧` obstructs Beauville-Laszlo
glueability for the completion pair. -/
theorem not_glueable_along_principalAdicCompletion_of_nonzero_completionTensor_kernel
    (f : R)
    {x : M[f^∞]} (hx_ne : x ≠ 0)
    (hcompletion : completionFPowerTorsionToCompletionTensor M f x = 0) :
    ¬ (beauvilleLaszloModuleCechSequence (principalAdicCompletion f) M f).ShortExact := by
  intro hshortExact
  have hinj :
      Function.Injective (completionFPowerTorsionToCompletionTensor M f) :=
    (isBeauvilleLaszloGlueableAlong_principalAdicCompletion_iff_injective_fPowerTorsionToCompletionTensor
      f).mp hshortExact
  have hx : x = 0 := by
    apply hinj
    simpa using hcompletion
  exact hx_ne hx

-- Proof sketch: by the previous clause, glueability along the completion map is implied by
-- injectivity of
-- `M[f^∞] → M ⊗[R] R^∧`. Injectivity on the smaller source `M[f^1]` gives a sufficient criterion
-- for that torsion map to be injective.
/-- Remark 15.91.11 (2): injectivity of `M[f^1] → M^∧` is a sufficient condition for `M` to be
glueable along the completion map. -/
theorem isBeauvilleLaszloGlueableAlong_principalAdicCompletion_of_injective_fTorsionToAdicCompletion
    (f : R)
    (hinj : Function.Injective (fTorsionToAdicCompletion M f)) :
    (beauvilleLaszloModuleCechSequence (principalAdicCompletion f) M f).ShortExact := sorry

-- Proof sketch: `fTorsionToAdicCompletion M f` is the restriction of
-- `AdicCompletion.of (principalIdeal f) M` to `M[f^1]`. By
-- `LinearMap.injective_domRestrict_iff`, injectivity of this restricted map is equivalent to
-- `M[f^1] ∩ ker(AdicCompletion.of ...) = 0`, and `AdicCompletion.of_injective_iff` identifies that
-- kernel with the intersection of the principal powers in the source-facing separatedness
-- criterion.
/-- Remark 15.91.11 (3): the map `M[f^1] → M^∧` is injective if and only if the intersection
`M[f^1] ∩ ⋂_{n > 0} f^n M` is zero. -/
theorem fTorsionToAdicCompletion_injective_iff_torsion_inf_principalPowers_eq_bot
    (f : R)
    :
    Function.Injective (fTorsionToAdicCompletion M f) ↔
      (M[f^1] : Submodule R M) ⊓
          ⨅ n : ℕ+, principalPowerIdeal f (n : ℕ) • (⊤ : Submodule R M) =
        ⊥ := sorry

-- Proof sketch: apply Algebra Lemma `10.75.2` to the Beauville-Laszlo short exact sequence
-- `0 → R' → R'_f → C → 0`. Vanishing of `Tor₁^R(M, R'_f)` gives the needed injectivity in the
-- tensor sequence, and the glueing-pair hypothesis supplies the rest of the Beauville-Laszlo
-- exactness package.
/-- Remark 15.91.11 (4): if `(R → R', f)` is a Beauville-Laszlo glueing pair and
`Tor₁^R(M, R'_f) = 0`, then `M` is glueable for `(R → R', f)`. -/
theorem isBeauvilleLaszloGlueableAlong_of_torOne_localizedTarget_isZero
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f)
    (hTor :
      Limits.IsZero (Tor[R, 1](M, Localization.Away (algebraMap R R' f)))) :
    (beauvilleLaszloModuleCechSequence R' M f).ShortExact := sorry

-- Proof sketch: localizing `Tor₁^R(M, R')` away from `f` identifies it with
-- `Tor₁^R(M, R'_f)`. Hence vanishing after localizing away from `f` is equivalent to saying that
-- every element of `Tor₁^R(M, R')` is killed by some power of `f`.
/-- Remark 15.91.11 (5): the vanishing of `Tor₁^R(M, R'_f)` is equivalent to saying that
`Tor₁^R(M, R')` is torsion for the powers of `f`. -/
theorem torOne_extension_isTorsion'_powers_iff_torOne_localizedTarget_isZero
    (f : R) :
    Module.IsTorsion'
        (Tor[R, 1](M, R'))
        (Submonoid.powers f) ↔
      Limits.IsZero (Tor[R, 1](M, Localization.Away (algebraMap R R' f))) := sorry

-- Proof sketch: flat modules have vanishing first Tor against every `R`-module. Apply the
-- previous criterion with `R'_f`.
/-- Remark 15.91.11 (6): every flat `R`-module is Beauville-Laszlo glueable for a glueing pair
`(R → R', f)`. -/
theorem isBeauvilleLaszloGlueableAlong_of_flat_module
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f)
    [Module.Flat R M] :
    (beauvilleLaszloModuleCechSequence R' M f).ShortExact := sorry

-- Proof sketch: if `R → R'` is flat, then so is the localization `R'_f`, so
-- `Tor₁^R(M, R'_f)` vanishes for every `R`-module `M`. Apply clause `(4)`.
/-- Remark 15.91.11 (7): if `R → R'` is flat, then every `R`-module is Beauville-Laszlo glueable
for `(R → R', f)`. -/
theorem isBeauvilleLaszloGlueableAlong_of_flat_extension
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f)
    [Module.Flat R R'] :
    (beauvilleLaszloModuleCechSequence R' M f).ShortExact := sorry

-- Proof sketch: Remark `15.91.8` gives the canonical Beauville-Laszlo glueing-pair owner for the
-- completion map over a Noetherian ring, and the adic-completion flatness instance supplies the
-- flat-extension hypothesis needed by clause `(7)`.
/-- Remark 15.91.11 (8): if `R` is Noetherian, then every `R`-module is glueable for the
completion pair `(R → R^∧, f)`. -/
theorem isBeauvilleLaszloGlueableAlong_principalAdicCompletion_of_isNoetherianRing
    (f : R) [IsNoetherianRing R] :
    (beauvilleLaszloModuleCechSequence (principalAdicCompletion f) M f).ShortExact := sorry

end

/-! ### Example_15_91_12_Non_glueable_module (from Chap15) -/
open scoped IdealPowerTorsion
open scoped TensorProduct
open Ideal.Quotient (eq_zero_iff_mem)

noncomputable section

universe u

/- Domain-style sampling:
- primary domain: Beauville-Laszlo completion glueability for modules over the principal-adic
  completion pair;
- sampled owner declarations:
  `principalAdicCompletion`,
  `(beauvilleLaszloModuleCechSequence (principalAdicCompletion f) Q f).ShortExact`,
  `completionFPowerTorsionToCompletionTensor`,
  `isBeauvilleLaszloGlueableAlong_principalAdicCompletion_iff_injective_fPowerTorsionToCompletionTensor`;
- best owner abstraction: the source-facing chapter owner
  `(beauvilleLaszloModuleCechSequence (principalAdicCompletion f) Q f).ShortExact`; the
  completion-specific injectivity criterion in Remark `15.91.11` is the canonical bridge/view
  specialization used to detect failure of that owner;
- primitive data: the quotient module `R ⧸ φR` and an explicit witness `ψ` whose class in
  `R ⧸ φR` is `f`-torsion, nonzero, and maps to zero in
  `(R ⧸ φR) ⊗[R] principalAdicCompletion f`;
- derived API: the generic completion-kernel obstruction from Remark `15.91.11`, and the
  resulting non-glueability statement for the quotient module;
- triage: the theorem below is `source-facing`; `principalAdicCompletion`,
  `(beauvilleLaszloModuleCechSequence (principalAdicCompletion f) Q f).ShortExact` are the
  `core/canonical` owners; `completionFPowerTorsionToCompletionTensor` and the completion-specific
  kernel-obstruction criterion from Remark `15.91.11` are the `bridge/view` API to the full
  tensor product.
-/

section

variable {R : Type u} [CommRing R]
variable {f φ : R}

local notation "I" => principalIdeal φ
local notation "Q" => R ⧸ I

lemma quotientBySingleElement_mk_mem_fPowerTorsion {ψ : R} (hmul : f * ψ = φ) :
    Ideal.Quotient.mk I ψ ∈ (Q[f^∞] : Submodule R Q) := by
  rw [Submodule.mem_torsion'_iff]
  refine ⟨⟨f, ⟨1, by simp⟩⟩, ?_⟩
  change Ideal.Quotient.mk I (f * ψ) = 0
  rw [eq_zero_iff_mem, hmul]
  exact Ideal.subset_span (by simp)

-- Proof sketch: in the textbook example, `R` is the ring of germs at `0` of smooth real-valued
-- functions, `f(x) = x`, `φ(x) = exp(-1 / x^2)`, and `ψ = φ / f`. The class of `ψ` in `R / φR`
-- gives a nonzero element of `M[f] ⊆ M[f^∞]` whose image in `M ⊗[R] R^∧` is zero.
/-- Example 15.91.12 (Non glueable module): let `M = R / φR`. If `ψ : R` has image `f * ψ = φ`,
the class of `ψ` in `M` is nonzero, and that class maps to zero in
`M ⊗[R] R^∧`, then `M` is not Beauville-Laszlo glueable for the principal completion pair
`(R → R^∧, f)`. In the smooth-germ ring from the source text, one takes `ψ = φ / f`. -/
theorem quotientBySingleElement_not_glueable_along_principalAdicCompletion_of_nonzero_completionTensor_kernel
    {ψ : R}
    (hmul : f * ψ = φ)
    (hψ_ne : Ideal.Quotient.mk I ψ ≠ 0)
    (hcompletion :
      completionFPowerTorsionToCompletionTensor Q f
          ⟨Ideal.Quotient.mk I ψ, quotientBySingleElement_mk_mem_fPowerTorsion hmul⟩ = 0) :
    ¬ (beauvilleLaszloModuleCechSequence (principalAdicCompletion f) Q f).ShortExact := by
  let x : Q[f^∞] :=
    ⟨Ideal.Quotient.mk I ψ, quotientBySingleElement_mk_mem_fPowerTorsion hmul⟩
  have hx_ne : x ≠ 0 := by
    simpa [x] using hψ_ne
  have hx_completion : completionFPowerTorsionToCompletionTensor Q f x = 0 := by
    simpa [x] using hcompletion
  exact
    not_glueable_along_principalAdicCompletion_of_nonzero_completionTensor_kernel
      f
      hx_ne
      hx_completion

end

/-! ### Lemma_15_91_13 (from Chap15) -/
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

section

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

/- Domain-style sampling:
* primary domain: Beauville-Laszlo glueing pairs and Tor-vanishing for principal-power ideals.
* sampled owner declarations:
  `IsBeauvilleLaszloGlueingPairAlong`,
  `Tor[R, p](N, M)`,
  `principalPowerIdeal`,
  `tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective`,
  `Tor`,
  `IsZero`.
* owner abstraction: the canonical Tor object `Tor (ModuleCat R) 1` together with the chapter owner
  `IsBeauvilleLaszloGlueingPairAlong`; the source-facing ideal owner is `principalPowerIdeal`.
* primitive data: the algebra map `R → R'`, the element `f : R`, and the positive integer `n`.
* derived API: the Tor-vanishing conclusion for the principal ideal `(f^n)`.
* triage: this theorem is `source-facing`; `IsBeauvilleLaszloGlueingPairAlong`, `Tor`, and
  `principalPowerIdeal` and `IsZero` are `core/canonical`; the tensor-base-change argument from
  Lemma `15.89.9` is the supporting `bridge/view`.
-/

-- Proof sketch: tensor the short exact sequence
-- `0 → principalPowerIdeal f n → R → R ⧸ principalPowerIdeal f n → 0` with `R'`.
-- The needed exactness package is the Beauville-Laszlo glueing-pair owner
-- `IsBeauvilleLaszloGlueingPairAlong f`.
-- Under those hypotheses, the argument from the source reduces the vanishing of
-- `Tor_1^R(R', f^n R)` to injectivity on the `f^n`-torsion submodule after base change; Lemma
-- `15.89.9` identifies that base change with the original torsion submodule, and Lemma `15.91.6`
-- supplies the required injectivity for a glueing pair.
/-- Lemma 15.91.13: if `(R → R', f)` is a Beauville-Laszlo glueing pair, then for every positive
integer `n` the first Tor group `Tor_1^R(R', f^n R)` vanishes. In Lean, `f^n R` is represented by
the chapter owner `principalPowerIdeal f n`, and vanishing is recorded by the canonical owner
`IsZero` of the Tor object. -/
theorem torOne_extension_principalPowIdeal_isZero_of_glueingPair
    (f : R)
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f)
    (n : ℕ+) :
    IsZero (Tor[R, 1](R', principalPowerIdeal f (n : ℕ))) := by
  let _ : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f := hpair
  sorry

end

/-! ### Lemma_15_91_14 (from Chap15) -/
open CategoryTheory CategoryTheory.Limits
open scoped IdealPowerTorsion

noncomputable section

universe u

section

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

/- Domain-style sampling:
* primary domain: Beauville-Laszlo glueing pairs and Tor-vanishing for the quotient by `f^∞`-torsion.
* sampled owner declarations:
  `Ideal.primaryComponent`,
  `IsBeauvilleLaszloGlueingPairAlong`,
  `Tor[R, p](N, M)`,
  `Tor`,
  `IsZero`.
* owner abstraction: the chapter owner
  `IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f` for the exact
  Beauville-Laszlo hypotheses, together with the canonical torsion owner `R[f^∞]`; the Tor
  bifunctor `Tor (ModuleCat R) 1` is the ambient canonical owner.
* primitive data: the algebra map `R → R'` and the element `f : R`.
* derived API: the vanishing statement for `Tor₁^R(R', R / R[f^∞])`, recorded by the canonical
  zero-object interface `IsZero`.
* triage: this theorem is `source-facing`; `IsBeauvilleLaszloGlueingPairAlong`, `R[f^∞]`, and
  `Tor` and `IsZero` are `core/canonical`.
-/

-- Proof sketch: write `R / R[f^∞]` as the filtered colimit of the quotients `R / R[f^n]`, or
-- equivalently of the principal ideals `(f^n)`. The functor `Tor_1^R(R', -)` commutes with filtered
-- colimits, so the previous lemma reduces the claim to the vanishing of
-- `Tor_1^R(R', (f^n))` for each positive integer `n`.
/-- Lemma 15.91.14: if `(R → R', f)` is a Beauville-Laszlo glueing pair, then the first Tor group
`Tor_1^R(R', R / R[f^\infty])` vanishes. Lean records this vanishing with the canonical owner
`IsZero` of the Tor object, with `R[f^\infty]` represented by the chapter notation for the
principal-ideal primary component. -/
theorem torOne_extension_quotientByFPowerTorsion_isZero_of_glueingPair
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    IsZero (Tor[R, 1](R', R ⧸ (R[f^∞] : Submodule R R))) := by
  let _ : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f := hpair
  sorry

end

/-! ### Lemma_15_91_15 (from Chap15) -/
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

section

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

/- Domain-style sampling:
* primary domain: Beauville-Laszlo glueing pairs and Tor-vanishing for the cokernel of
  `M → M_f`.
* sampled owner declarations:
  `IsBeauvilleLaszloGlueingPairAlong`,
  `Tor[R, p](N, M)`,
  `LocalizedModule.mkLinearMap`,
  `ModuleCat.cokernelIsoRangeQuotient`,
  `Tor`.
* owner abstraction: the source-facing quotient owner is the canonical module quotient
  `LocalizedModule.Away f M ⧸ range(M → M_f)`, while the chapter owner
  `IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f` supplies the Beauville-Laszlo
  hypotheses and the chapter owner notation `Tor[R, 1](R', -)` exposes the ambient canonical Tor
  object `Tor (ModuleCat R) 1`.
* primitive data: the algebra map `R → R'`, the element `f : R`, and the explicit `R`-module `M`.
* derived API: the Tor-vanishing conclusion for the canonical quotient `M_f / M`.
* triage: the quotient `LocalizedModule.Away f M ⧸ range(M → M_f)` is `source-facing`;
  `IsBeauvilleLaszloGlueingPairAlong`, `Tor`, and `IsZero` are `core/canonical`; and
  `ModuleCat.cokernelIsoRangeQuotient` is the supporting `bridge/view` identifying the
  categorical cokernel with the quotient model.
-/
-- Proof sketch: rewrite the categorical cokernel of `M → M_f` as the source-facing quotient
-- `M_f / M` via `ModuleCat.cokernelIsoRangeQuotient`, then replace that quotient by the filtered
-- colimit of the quotients `M / f^n M` after killing `f`-power torsion. Lemma `15.91.14` handles
-- the cyclic torsion case, and Lemma `15.89.9` identifies the relevant base changes needed to
-- descend from a free `R / R[f^∞]`-presentation to a general module.
/-- Lemma 15.91.15: if `(R → R', f)` is a Beauville-Laszlo glueing pair, then for every
`R`-module `M` the first Tor group `Tor_1^R(R', \operatorname{Coker}(M → M_f))` vanishes. Lean
states this directly for the canonical quotient
`LocalizedModule.Away f M ⧸ range(M → M_f)`, with `ModuleCat.cokernelIsoRangeQuotient`
remaining only as the internal bridge from the categorical cokernel, and records the vanishing by
the canonical owner `IsZero` of the chapter Tor notation `Tor[R, 1](R', -)`. -/
theorem torOne_extension_cokernel_toLocalizationAway_isZero_of_glueingPair
    (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    IsZero (Tor[R, 1](R',
      LocalizedModule.Away f M ⧸
        LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers f) M))) := by
  let _ : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f := hpair
  sorry

end

/-! ### Theorem_15_91_16 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable (f : R)

variable (R') in
/-- The full subcategory of `ModuleCat R` consisting of modules glueable for the
Beauville-Laszlo pair `(R → R', f)`. -/
abbrev beauvilleLaszloGlueableProperty (f : R) : ObjectProperty (ModuleCat R) :=
  fun M ↦ (beauvilleLaszloModuleCechSequence R' M f).ShortExact

-- Proof sketch: for a glueing datum `(M', M₁, α₁)`, define `H^0` as the kernel of the
-- Beauville-Laszlo differential from `15.91.16.1`. The surjectivity and exactness statements in
-- `15.91.16.1`-`15.91.16.3`, together with Lemmas `15.91.15`, `15.89.9`, and `15.90.11`, show
-- that this kernel is glueable, that `Can(H^0(-))` reconstructs the original glueing datum, and
-- that `H^0(Can(M)) = M` for every glueable module `M`.
/-- Theorem 15.91.16: if `(R → R', f)` is a Beauville-Laszlo glueing pair, then the canonical
functor `Can : Mod_R → Glue(R → R', f)` induces an equivalence from the category of glueable
`R`-modules for `(R → R', f)` to the category of Beauville-Laszlo glueing data. In this
library-facing formalization, the source is the full subcategory
`(beauvilleLaszloGlueableProperty R' f).FullSubcategory` of `ModuleCat R`, and the target is the
categorical pullback `Mod_{R'} ×_{Mod_{R'_f}} Mod_{R_f}`. -/
theorem beauvilleLaszloGlueableCan_isEquivalence
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    Functor.IsEquivalence
      ((beauvilleLaszloGlueableProperty R' f).ι ⋙ formalGlueingSingleFunctor R' f) := sorry

end

/-! ### Remark_15_91_17 (from Chap15) -/
open CategoryTheory
open scoped TensorProduct

universe u

noncomputable section

/- Domain-style sampling:
- primary domain: Beauville-Laszlo glueability for a single localization, expressed through the
  canonical module Cech short complex and its cycles object;
- sampled owner declarations:
  `beauvilleLaszloModuleCechSequence`,
  `ShortComplex.moduleCatToCycles`,
  `ShortComplex.exact_iff_surjective_moduleCatToCycles`,
  `(beauvilleLaszloModuleCechSequence R' M f).ShortExact`;
- best owner abstraction: the source-facing replacement module `\tilde M = H^0(Can(M))` should be
  exposed as the cycles object of the canonical owner
  `beauvilleLaszloModuleCechSequence R' M f`, and the canonical map `M → \tilde M` should reuse
  `ShortComplex.moduleCatToCycles` directly;
- primitive data vs derived API: the primitive data are the module Cech short complex and its
  canonical map to cycles; the replacement module, its glueability, the induced base-change and
  localization bijectivity, and the surjectivity conclusion are derived API.

Source/core/bridge triage:
- `source-facing`: the replacement module `\tilde M = H^0(Can(M))` and the canonical map
  `M → \tilde M` from Remark `15.91.17`;
- `core/canonical`: `beauvilleLaszloModuleCechSequence`, `ShortComplex.moduleCatToCycles`, and
  `ShortComplex.exact_iff_surjective_moduleCatToCycles`;
- `bridge/view`: the induced maps after tensoring with `R'` and localizing away from `f`.
-/

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable {M : Type u} [AddCommGroup M] [Module R M]
variable {f : R}

-- Proof sketch: Theorem `15.91.16` identifies the single-localization glueing datum `Can(M)` with
-- the Beauville-Laszlo datum of `\tilde M = H^0(Can(M))`, so `\tilde M` is glueable for the
-- pair `(R → R', f)`.
/-- Remark 15.91.17: if `(R → R', f)` is a Beauville-Laszlo glueing pair, then the replacement
module `\tilde M = H^0(Can(M))`, i.e. the cycles object
`(beauvilleLaszloModuleCechSequence R' M f).cycles`, is glueable. -/
theorem beauvilleLaszloModuleCechH0_shortExact
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    (beauvilleLaszloModuleCechSequence R'
      (beauvilleLaszloModuleCechSequence R' M f).cycles
      f).ShortExact := by
  sorry

-- Proof sketch: Theorem `15.91.16` says the canonical map `M → H^0(Can(M))` reconstructs the
-- same Beauville-Laszlo glueing datum after tensoring with `R'`.
/-- The canonical map `M → \tilde M = H^0(Can(M))`, namely
`(beauvilleLaszloModuleCechSequence R' M f).moduleCatToCycles`, becomes bijective after base
change to `R'`. -/
theorem beauvilleLaszloModuleCechH0Map_baseChange_bijective
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    Function.Bijective
      (((beauvilleLaszloModuleCechSequence R' M f).moduleCatToCycles).baseChange R') := by
  sorry

-- Proof sketch: The same Beauville-Laszlo equivalence identifies the localized components of
-- `Can(M)` and `Can(\tilde M)`, so localizing the canonical map away from `f` gives a bijection.
/-- The canonical map `M → \tilde M` from Remark 15.91.17 becomes bijective after localizing away
from `f`. -/
theorem beauvilleLaszloModuleCechH0Map_localizedAway_bijective
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    Function.Bijective
      (LocalizedModule.map
        (Submonoid.powers f)
        (beauvilleLaszloModuleCechSequence R' M f).moduleCatToCycles) := by
  sorry

-- Proof sketch: for a glueing pair, the module Cech sequence for `M` is exact in the middle; the
-- canonical map to cycles is therefore surjective by
-- `ShortComplex.exact_iff_surjective_moduleCatToCycles`.
/-- Remark 15.91.17: for a Beauville-Laszlo glueing pair, the canonical map `M → \tilde M` is
surjective. -/
theorem beauvilleLaszloModuleCechH0Map_surjective
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    Function.Surjective (beauvilleLaszloModuleCechSequence R' M f).moduleCatToCycles := by
  sorry

end
