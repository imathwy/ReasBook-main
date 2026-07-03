import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_163_1 (from Chap10) -/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

open Ideal IsLocalRing
open TensorProduct.AlgebraTensorModule
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {M : Type w} {N : Type x}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
variable [Module.Finite S N] [Module.Flat R N]

local notation "𝔪S" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S
local notation "ClosedFiberModule" => ClosedFiber ⊗[S] N

/- Domain-style sampling pass:
* primary domain: local commutative algebra of depth for finite modules under flat local base
  change, with the closed fiber carried by the canonical fiber-ring owner;
* sampled owner declarations:
  `moduleDepth`,
  `Ideal.Fiber`,
  `Module.Finite.base_change`,
  `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`;
* best owner abstraction: the right-hand side belongs on the canonical local depth
  `moduleDepth ClosedFiber ClosedFiberModule`, where
  `ClosedFiber = Ideal.Fiber (maximalIdeal R) S` and
  `ClosedFiberModule = ClosedFiber ⊗[S] N`; the quotient module
  `N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N))` is only a bridge.

Primitive data vs. derived API:
* primitive data: the local flat map `R → S`, the finite `R`-module `M`, and the finite
  `S`-module `N` that is flat over `R`;
* derived API: the quotient presentation of the closed fiber and of the closed-fiber module.

Source/core/bridge triage:
* `source-facing`: the Stacks additivity formula for depth under flat local base change;
* `core/canonical`: `moduleDepth` on the owner ring/module pair `ClosedFiber` and
  `ClosedFiberModule`;
* `bridge/view`: the quotient presentation `S ⧸ 𝔪S` and
  `N ⧸ (𝔪S • (⊤ : Submodule S N))`.
-/

/-- The canonical closed fiber `ClosedFiber = (maximalIdeal R).Fiber S` is a local ring. -/
local instance closedFiber_isLocalRing : IsLocalRing ClosedFiber := by
  let e : ClosedFiber ≃ₐ[R] S ⧸ 𝔪S :=
    (Algebra.TensorProduct.congr (.symm <| .ofBijective _
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))) .refl).trans <|
      (Algebra.TensorProduct.comm _ _ _).trans
        ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot _ _).symm.restrictScalars _)
  letI : IsLocalRing (S ⧸ 𝔪S) := by
    have h𝔪S : 𝔪S < (⊤ : Ideal S) :=
      IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)
    have : Nontrivial (S ⧸ 𝔪S) :=
      Quotient.nontrivial_iff.mpr h𝔪S.ne
    exact IsLocalRing.of_surjective' (Ideal.Quotient.mk 𝔪S) Ideal.Quotient.mk_surjective
  exact (e.symm : S ⧸ 𝔪S ≃+* ClosedFiber).isLocalRing

/-- The tensor product `N ⊗[R] M`, which represents `M ⊗[R] N` in a form carrying its natural
`S`-module structure, is finite over `S` under the flat local algebra hypotheses. -/
local instance : Module.Finite S (N ⊗[R] M) := sorry

-- Proof sketch: argue by induction on the sum of the two depths. If the closed fiber has positive
-- depth, choose a nonzerodivisor in the maximal ideal of `S` on the closed fiber, use the flat
-- lifting lemma to show it is a nonzerodivisor on `N`, reduce to `N / fN`, and apply the depth
-- drop lemma. If the closed fiber has depth zero but the sum is positive, choose a
-- nonzerodivisor in the maximal ideal of `R` on `M`, use flatness of `N` to keep it regular on
-- the tensor product, pass to `M / xM`, and conclude by induction.
/-- Lemma 10.163.1: for a flat local homomorphism `R → S` of Noetherian local rings, a finite
`R`-module `M`, and a finite `S`-module `N` that is flat over `R`, the local depth of the tensor
product equals the local depth of `M` plus the local depth of the canonical closed-fiber module
`ClosedFiberModule = ((maximalIdeal R).Fiber S) ⊗[S] N`, equivalently
`N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N))`, over the canonical
closed-fiber ring `ClosedFiber = (maximalIdeal R).Fiber S`, equivalently
`S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`. -/
theorem depth_tensorProduct_eq_depth_add_depth_closedFiber :
    moduleDepth S (N ⊗[R] M) =
      moduleDepth R M + moduleDepth ClosedFiber ClosedFiberModule := sorry

end

/-! ### Lemma_10_163_2 (from Chap10) -/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

open IsLocalRing
open scoped TensorProduct

universe u v

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S

/- Domain-style sampling pass:
* primary domain: local commutative algebra of depth under flat local base change, with the closed
  fiber carried by the canonical owner `Ideal.Fiber`;
* sampled owner declarations:
  `moduleDepth`,
  `Ideal.Fiber`,
  `depth_tensorProduct_eq_depth_add_depth_closedFiber`,
  `Algebra.TensorProduct.rid`;
* best owner abstraction: the public statement should live on the local-depth bridge
  `moduleDepth` and on the canonical closed-fiber ring `ClosedFiber = (maximalIdeal R).Fiber S`,
  while the quotient presentation `S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)` is only a
  bridge/view.

Primitive data vs. derived API:
* primitive data: the flat local algebra map `R → S`;
* derived API: the tensor-product presentations `S ⊗[R] R` and `ClosedFiber ⊗[S] S`, and the
  quotient presentation of the closed fiber.

Source/core/bridge triage:
* `source-facing`: the Stacks depth formula for the ring map `R → S`;
* `core/canonical`: `moduleDepth` and `Ideal.Fiber`;
* `bridge/view`: the tensor and quotient identifications used to compare this source-facing
  statement with the module-level owner theorem `depth_tensorProduct_eq_depth_add_depth_closedFiber`.
-/
attribute [local instance] closedFiber_isLocalRing

private theorem regularSequenceLengths_eq_of_equiv {A M N : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (I : Ideal A)
    (e : M ≃ₗ[A] N) :
    Ideal.regularSequenceLengths I M = Ideal.regularSequenceLengths I N := by
  ext d
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).1 hreg, hI, rfl⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).2 hreg, hI, rfl⟩

private theorem ideal_depth_eq_of_equiv {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module.Finite A M] [Module.Finite A N] (I : Ideal A)
    (e : M ≃ₗ[A] N) :
    Ideal.depth I M = Ideal.depth I N := by
  have htop : I • (⊤ : Submodule A M) = ⊤ ↔ I • (⊤ : Submodule A N) = ⊤ := by
    constructor
    · intro h
      have := congrArg (Submodule.map e.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.surjective] using this
    · intro h
      have := congrArg (Submodule.map e.symm.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.symm.surjective] using this
  by_cases hM : I • (⊤ : Submodule A M) = ⊤
  · rw [Ideal.depth_eq_top_of_smul_top I M hM, Ideal.depth_eq_top_of_smul_top I N (htop.mp hM)]
  · rw [Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I M hM,
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I N (mt htop.mpr hM),
      regularSequenceLengths_eq_of_equiv I e]

private theorem moduleDepth_eq_of_equiv {A M N : Type*} [CommRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Finite A M] [Module.Finite A N] (e : M ≃ₗ[A] N) :
    moduleDepth A M = moduleDepth A N :=
  ideal_depth_eq_of_equiv (maximalIdeal A) e

-- Proof sketch: specialize Lemma `10.163.1` to `M = R` and `N = S`, so the tensor product on the
-- left becomes `S ⊗[R] R` and the closed-fiber module on the right becomes `ClosedFiber ⊗[S] S`.
-- Then transport the two depth terms across the canonical algebra-tensor identifications
-- `S ⊗[R] R ≃ S` and `ClosedFiber ⊗[S] S ≃ ClosedFiber`.
/-- Lemma 10.163.2: for a flat local homomorphism `R → S` of Noetherian local rings, the depth of
`S` equals the depth of `R` plus the depth of the canonical closed fiber
`ClosedFiber = (maximalIdeal R).Fiber S`, equivalently
`S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`. -/
theorem depth_target_eq_depth_source_add_depth_closed_fiber :
    moduleDepth S S = moduleDepth R R + moduleDepth ClosedFiber ClosedFiber := by
  rw [← moduleDepth_eq_of_equiv (Algebra.TensorProduct.rid R S S).toLinearEquiv,
    ← moduleDepth_eq_of_equiv (Algebra.TensorProduct.rid S ClosedFiber ClosedFiber).toLinearEquiv]
  simpa using
    (depth_tensorProduct_eq_depth_add_depth_closedFiber :
      moduleDepth S (S ⊗[R] R) =
        moduleDepth R R + moduleDepth ClosedFiber (ClosedFiber ⊗[S] S))

end

/-! ### Lemma_10_163_3 (from Chap10) -/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

open Ideal IsLocalRing
open TensorProduct.AlgebraTensorModule
open scoped TensorProduct

universe u v

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]

local notation "𝔪S" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S

/-
Domain-style sampling pass:
* primary domain: local commutative algebra of Cohen-Macaulay local rings under flat local
  homomorphisms, with the closed fiber carried by the canonical owner `Ideal.Fiber`;
* sampled owner declarations:
  `Module.CohenMacaulay`,
  `Ideal.Fiber`,
  `depth_target_eq_depth_source_add_depth_closed_fiber`,
  `Module.supportDim_self_eq_ringKrullDim`;
* best owner abstraction: the Cohen-Macaulay conditions should stay on the owner
  `Module.CohenMacaulay`, and the closed fiber should be expressed by the canonical ring
  `ClosedFiber = Ideal.Fiber (maximalIdeal R) S`; the quotient `S ⧸ 𝔪S` is only a bridge/view.

Primitive data vs. derived API:
* primitive data: only the flat local algebra map `R → S`;
* derived API: the quotient presentation `S ⧸ 𝔪S` of the closed fiber and the induced local and
  Noetherian instances used to formulate the owner statement on `ClosedFiber`.

Source/core/bridge triage:
* `source-facing`: the Stacks equivalence saying that `S` is Cohen-Macaulay iff both `R` and the
  closed fiber are Cohen-Macaulay;
* `core/canonical`: `Module.CohenMacaulay` and `ClosedFiber = Ideal.Fiber (maximalIdeal R) S`;
* `bridge/view`: the quotient presentation `S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`.
-/

private noncomputable def closedFiberQuotEquiv : ClosedFiber ≃ₐ[R] S ⧸ 𝔪S :=
  (Algebra.TensorProduct.congr (.symm <| .ofBijective _
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))) .refl).trans <|
    (Algebra.TensorProduct.comm _ _ _).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot _ _).symm.restrictScalars _)

/-- The canonical closed fiber `ClosedFiber = (maximalIdeal R).Fiber S` is a local ring. -/
local instance closedFiber_isLocalRing : IsLocalRing ClosedFiber := by
  have h𝔪S : 𝔪S < (⊤ : Ideal S) :=
    IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)
  letI : Nontrivial (S ⧸ 𝔪S) :=
    Quotient.nontrivial_iff.mpr h𝔪S.ne
  letI : IsLocalRing (S ⧸ 𝔪S) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk 𝔪S) Ideal.Quotient.mk_surjective
  exact (closedFiberQuotEquiv.toRingEquiv.symm : S ⧸ 𝔪S ≃+* ClosedFiber).isLocalRing

/-- The canonical closed fiber inherits Noetherianity from its quotient presentation `S ⧸ 𝔪S`. -/
local instance closedFiber_isNoetherianRing : IsNoetherianRing ClosedFiber :=
  isNoetherianRing_of_ringEquiv (S ⧸ 𝔪S) closedFiberQuotEquiv.toRingEquiv.symm

-- Proof sketch: combine Lemma `10.163.2`, which gives the additivity formula for the depth of
-- `S`, with Lemma `10.112.7`, which gives the corresponding dimension formula for the canonical
-- closed fiber `ClosedFiber`. Then rewrite the Cohen-Macaulay condition on `R`, `S`, and
-- `ClosedFiber` as the equality between depth and Krull dimension, using the quotient view only
-- internally, and compare the two formulas.
/-- Lemma 10.163.3: for a flat local homomorphism `R → S` of local Noetherian rings, `S` is
Cohen-Macaulay if and only if both `R` and the canonical closed fiber
`ClosedFiber = (maximalIdeal R).Fiber S`, equivalently `S / 𝔪_R S`, are Cohen-Macaulay. -/
theorem cohenMacaulayRing_iff_source_and_closedFiber :
    Module.CohenMacaulay S S ↔
      Module.CohenMacaulay R R ∧ Module.CohenMacaulay ClosedFiber ClosedFiber := sorry

end

/-! ### Lemma_10_163_4 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {k : ℕ}
variable [SerreConditionS R k] [IsNoetherianRing S] [Module.Flat R S]

/-
Domain-style sampling pass:
* primary domain: LinearRepresentations_Serre_1977's condition `(S_k)` in commutative algebra under flat base change and
  fiberwise hypotheses;
* sampled owner declarations:
  - `SerreConditionS`, the chapter owner for the ring-theoretic `(S_k)` condition from
    `Definition_10_157_1.lean`;
  - `SerreConditionS.moduleDepth_localizationAtPrime_ge_min`, the primewise localized depth bound
    already derived from that owner;
  - `depth_target_eq_depth_source_add_depth_closed_fiber`, the local depth-additivity owner from
    `Lemma_10_163_2.lean`;
  - `ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown`,
    the local fiber-dimension formula from `Lemma_10_112_7.lean`.

Best owner abstraction:
* the public statement should stay on the canonical ring owner `SerreConditionS`;
* the canonical fiber input is `p.asIdeal.Fiber S`;
* the local ring `fiberLocalRingAt R S q` is supporting bridge data for the proof, not a second
  public owner.

Primitive data vs. derived API:
* primitive data: the flat algebra `R → S`, the owner hypothesis `[SerreConditionS R k]`, the
  Noetherian target hypothesis on `S`, and the fiberwise owner hypothesis `hfiber`;
* derived API: the localized depth inequalities, the closed-fiber depth formula, and the
  local-fiber dimension formula used to verify the defining primewise inequality for
  `SerreConditionS S k`.

Source/core/bridge triage:
* `source-facing`: `serreConditionS_of_flat_of_fiber`, the textbook ascent statement for `(S_k)`;
* `core/canonical`: `SerreConditionS` together with its primewise localized depth theorem;
* `bridge/view`: the local flat map `R_(q ∩ R) → S_q`, its closed fiber, and the canonical local
  fiber ring `fiberLocalRingAt R S q`.
-/
-- Proof sketch: for each `q : PrimeSpectrum S`, set `p = q.asIdeal.under R`. The owner theorem
-- `SerreConditionS.moduleDepth_localizationAtPrime_ge_min` gives the `(S_k)` bound on `R_p`, and
-- the same owner theorem applied to `hfiber p` gives the `(S_k)` bound on the local fiber over
-- `q`. The local depth formula `depth_target_eq_depth_source_add_depth_closed_fiber` for
-- `R_p → S_q` and the local dimension formula
-- `ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown`
-- combine these two bounds to yield `depth S_q ≥ min(k, dim S_q)`.
/-- Lemma 10.163.4: for a flat ring map `R → S`, if `R` satisfies LinearRepresentations_Serre_1977's condition `(S_k)`, `S`
is Noetherian, and every fiber ring `κ(𝔭) ⊗[R] S`, formalized as `p.asIdeal.Fiber S`, satisfies
`(S_k)`, then `S` satisfies `(S_k)`. -/
theorem serreConditionS_of_flat_of_fiber
    (hfiber : ∀ p : PrimeSpectrum R, SerreConditionS (p.asIdeal.Fiber S) k) :
    SerreConditionS S k := sorry

end

/-! ### Lemma_10_163_5 (from Chap10) -/
universe u v

open Ideal.Quotient (eq_zero_iff_mem)
open scoped ENat TensorProduct nonZeroDivisors

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {k : ℕ}
variable [SerreConditionR R k] [IsNoetherianRing S] [Module.Flat R S]

/- Domain sampling pass:
* primary domain: commutative algebra of LinearRepresentations_Serre_1977's condition `(R_k)` under flat ring maps and
  fiberwise regularity;
* sampled owner declarations:
  - `SerreConditionR`, the chapter owner predicate for `(R_k)` from
    `Definition_10_157_1.lean`;
  - `Ideal.Fiber`, the canonical fiber-ring owner `κ(𝔭) ⊗[R] S`;
  - `serreConditionS_of_flat_of_fiber`, the sibling owner-level ascent theorem for `(S_k)` in
    `Lemma_10_163_4.lean`;
  - `isRegularLocalRing_of_flat_localHom_of_regular_closedFiber`, the local regularity transfer
    theorem for flat local maps in `Lemma_10_112_8.lean`.

Source/core/bridge triage:
* source-facing: `serreConditionR_of_flat_of_fiber`, the textbook ascent statement for `(R_k)`;
* core/canonical: the owner predicate `SerreConditionR` together with its primewise localized
  regularity field
  `SerreConditionR.isRegularLocalRing_localizationAtPrime`;
* bridge/view: the canonical fiber presentation `p.asIdeal.Fiber S`.

Primitive data already live in the owner abstraction: `(R_k)` on the base ring and on each fiber.
This file should therefore expose only the source-facing ascent theorem, not a parallel wrapper for
fiberwise regularity or localized regularity data.
-/

section fiberLocalizationBridge

variable (p : PrimeSpectrum R)

local notation "Sbar" => S ⧸ Ideal.map (algebraMap R S) p.asIdeal
local notation "Rbar" => R ⧸ p.asIdeal
local notation "Rbar⁰" => nonZeroDivisors Rbar
local notation "T" => Algebra.algebraMapSubmonoid Sbar Rbar⁰

/-- Helper for Lemma 10.163.5: elements of `pS` vanish in the fiber ring `κ(p) ⊗[R] S`. -/
private lemma algebraMap_fiber_eq_zero_of_mem_map {x : S}
    (hx : x ∈ Ideal.map (algebraMap R S) p.asIdeal) :
    algebraMap S (p.asIdeal.Fiber S) x = 0 := by
  let φ : (R ⧸ p.asIdeal) ⊗[R] S →+* p.asIdeal.Fiber S :=
    (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom R (R ⧸ p.asIdeal) p.asIdeal.ResidueField)
      (AlgHom.id R S)).toRingHom
  have hquot :
      (Ideal.Quotient.mk (Ideal.map (algebraMap R S) p.asIdeal) x : Sbar) = 0 :=
    eq_zero_iff_mem.mpr hx
  have htmul : (1 : Rbar) ⊗ₜ[R] x = 0 := by
    let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p.asIdeal
    have : e (Ideal.Quotient.mk (Ideal.map (algebraMap R S) p.asIdeal) x) =
        (1 : Rbar) ⊗ₜ[R] x := rfl
    rw [← this, hquot]
    simp [e]
  have hφ : φ ((1 : Rbar) ⊗ₜ[R] x) = 0 := by
    rw [htmul, map_zero]
  simpa [φ] using hφ

/-- Helper for Lemma 10.163.5: the quotient `S / pS` acts canonically on the fiber ring. -/
noncomputable instance fiberQuotientAlgebra :
    Algebra Sbar (p.asIdeal.Fiber S) :=
  (Ideal.Quotient.liftₐ (Ideal.map (algebraMap R S) p.asIdeal)
    (Algebra.ofId S (p.asIdeal.Fiber S))
    (fun _ hx ↦ algebraMap_fiber_eq_zero_of_mem_map (R := R) (S := S) p hx)).toRingHom.toAlgebra

/-- Helper for Lemma 10.163.5: the quotient generator `s mod pS` maps to the pure tensor
`1 ⊗ s` in the fiber ring. -/
theorem quotient_to_fiber_algebraMap_mk (s : S) :
    algebraMap Sbar (p.asIdeal.Fiber S)
      (Ideal.Quotient.mk (Ideal.map (algebraMap R S) p.asIdeal) s) =
        1 ⊗ₜ[R] s :=
  rfl

/-- Helper for Lemma 10.163.5: the quotient-base-changed fiber presentation recovers the usual
fiber ring as an `S / pS`-algebra. -/
noncomputable def fiber_tensor_over_quotient_algEquiv :
    Sbar ⊗[Rbar] p.asIdeal.ResidueField ≃ₐ[Sbar] p.asIdeal.Fiber S :=
  let eRing :
      Sbar ⊗[Rbar] p.asIdeal.ResidueField ≃+* p.asIdeal.Fiber S :=
    (Algebra.TensorProduct.commRight Rbar Sbar p.asIdeal.ResidueField).toRingEquiv.trans
      ((Algebra.TensorProduct.congr
          (AlgEquiv.refl : p.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField]
            p.asIdeal.ResidueField)
          (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p.asIdeal)).trans
        (Algebra.TensorProduct.cancelBaseChange R Rbar p.asIdeal.ResidueField
          p.asIdeal.ResidueField S)).toRingEquiv
  { toRingEquiv := eRing
    commutes' := by
      intro x
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
      -- Proof comment: both sides send `s mod pS` to the same pure tensor `1 ⊗ s`.
      simpa [eRing, quotient_to_fiber_algebraMap_mk (R := R) (S := S) (p := p),
        Algebra.TensorProduct.cancelBaseChange_tmul] }

/-- Helper for Lemma 10.163.5: the fiber ring is the localization of `S / pS` at the image of
the nonzerodivisors of `R / p`. -/
noncomputable def fiber_quotient_localization_algEquiv :
    Localization T ≃ₐ[Sbar] p.asIdeal.Fiber S :=
  -- Proof comment: this is the source proof's standard presentation
  -- `(S / pS)[(R / p)^\times] ≃ κ(p) ⊗[R] S`.
  ((Localization.tensorLeftAlgEquiv Rbar⁰ Sbar).symm.trans
      (Algebra.TensorProduct.congr
        (AlgEquiv.refl : Sbar ≃ₐ[Sbar] Sbar)
        (IsLocalization.algEquiv Rbar⁰ (Localization Rbar⁰) p.asIdeal.ResidueField))).trans
    (fiber_tensor_over_quotient_algEquiv (R := R) (S := S) (p := p))

end fiberLocalizationBridge

-- Proof sketch: to prove `(R_k)` for `S`, fix `q : PrimeSpectrum S` of height at most `k` and let
-- `p = q.asIdeal.under R`. Flatness gives going down, so Lemma `10.112.7` expresses
-- `dim S_q = dim R_p + dim ((κ(p) ⊗[R] S)_(q_fiber))`. The bound on `dim S_q` therefore bounds both
-- summands by `k`. Since `R` satisfies `(R_k)`, the localization `R_p` is regular; since the fiber
-- ring over `p` satisfies `(R_k)`, the corresponding localization of the fiber is regular. Lemma
-- `10.112.8` then upgrades these two regularity statements to regularity of `S_q`.
/-- Helper for Lemma 10.163.5: a height bound on `q` bounds both the contracted prime
`q ∩ R` and the corresponding fiber prime. -/
lemma primeHeight_under_and_fiberPrimeAt_le_of_primeHeight_le
    (q : PrimeSpectrum S) (hq : q.asIdeal.primeHeight ≤ k) :
    (q.asIdeal.under R).primeHeight ≤ k ∧
      (fiberPrimeAt R S q).asIdeal.primeHeight ≤ k := by
  letI : Algebra.HasGoingDown R S := by infer_instance
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  have hfiberDim :
      ringKrullDim (fiberLocalRingAt R S q) =
        ((((fiberPrimeAt R S q).asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) := by
    -- Proof comment: the local fiber ring is the localization of the fiber at its fiber prime.
    calc
      ringKrullDim (fiberLocalRingAt R S q) =
          ↑((fiberPrimeAt R S q).asIdeal.height) := by
            simpa [fiberLocalRingAt] using
              (IsLocalization.AtPrime.ringKrullDim_eq_height
                (fiberPrimeAt R S q).asIdeal (fiberLocalRingAt R S q))
      _ =
          ((((fiberPrimeAt R S q).asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) := by
            rw [Ideal.height_eq_primeHeight]
  have hdim :
      (((q.asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) =
        (((p.asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) +
          ((((fiberPrimeAt R S q).asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) := by
    -- Proof comment: Lemma `10.112.7` becomes a prime-height sum after rewriting each local
    -- Krull dimension by the height of the defining prime.
    calc
      (((q.asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) =
          ringKrullDim (Localization.AtPrime q.asIdeal) := by
            rw [← Ideal.height_eq_primeHeight]
            simpa using
              (IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal
                (Localization.AtPrime q.asIdeal)).symm
      _ =
          ringKrullDim (Localization.AtPrime p.asIdeal) +
            ringKrullDim (fiberLocalRingAt R S q) := by
              simpa [p] using
                ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown
                  (R := R) (S := S) q
      _ =
          (((p.asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) +
            ringKrullDim (fiberLocalRingAt R S q) := by
              congr 1
              simpa [Ideal.height_eq_primeHeight] using
                (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal
                  (Localization.AtPrime p.asIdeal))
      _ =
          (((p.asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) +
            ((((fiberPrimeAt R S q).asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) := by
              rw [hfiberDim]
  have hdim_enat :
      q.asIdeal.primeHeight =
        p.asIdeal.primeHeight + (fiberPrimeAt R S q).asIdeal.primeHeight := by
    exact_mod_cast hdim
  have hp :
      p.asIdeal.primeHeight ≤ k := by
    -- Proof comment: each ENat summand is bounded by the total codimension.
    calc
      p.asIdeal.primeHeight ≤
          p.asIdeal.primeHeight + (fiberPrimeAt R S q).asIdeal.primeHeight := by
            exact le_add_right le_rfl
      _ = q.asIdeal.primeHeight := hdim_enat.symm
      _ ≤ k := hq
  have hqf :
      (fiberPrimeAt R S q).asIdeal.primeHeight ≤ k := by
    -- Proof comment: the same argument bounds the fiber-prime contribution.
    calc
      (fiberPrimeAt R S q).asIdeal.primeHeight ≤
          p.asIdeal.primeHeight + (fiberPrimeAt R S q).asIdeal.primeHeight := by
            exact le_add_left le_rfl
      _ = q.asIdeal.primeHeight := hdim_enat.symm
      _ ≤ k := hq
  exact ⟨by simpa [p] using hp, hqf⟩

/-- Helper for Lemma 10.163.5: after quotienting by `I ≤ q`, the induced prime complement on
`A ⧸ I` is exactly the image of `q.primeCompl`. -/
lemma quotient_primeCompl_eq_algebraMapSubmonoid
    {A : Type*} [CommRing A] (I q : Ideal A) [q.IsPrime]
    [(Ideal.map (Ideal.Quotient.mk I) q).IsPrime] (hIq : I ≤ q) :
    Algebra.algebraMapSubmonoid (A ⧸ I) q.primeCompl =
      (Ideal.map (Ideal.Quotient.mk I) q).primeCompl := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    -- Proof comment: if `a mod I` lay in the quotient prime, then pulling back along the
    -- quotient map would force `a ∈ q`, contradicting `a ∉ q`.
    change Ideal.Quotient.mk I a ∉ Ideal.map (Ideal.Quotient.mk I) q
    intro hx
    have hqx : a ∈ Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) q) := by
      exact hx
    exact ha <| by simpa [Ideal.comap_map_mk hIq] using hqx
  · intro hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨a, ?_, rfl⟩
    -- Proof comment: conversely, if `a mod I` avoids the quotient prime then `a` itself avoids
    -- `q`, so it already represents the required source-side denominator.
    intro ha
    exact hx (Ideal.mem_map_of_mem (Ideal.Quotient.mk I) ha)

/-- Helper for Lemma 10.163.5: if the fiber prime of `q` has codimension at most `k`, then the
closed fiber of `R_(q ∩ R) → S_q` is a regular local ring. -/
lemma isRegularLocalRing_localized_quotient_of_fiberPrimeAt_bound
    (hfiber : ∀ p : PrimeSpectrum R, SerreConditionR (p.asIdeal.Fiber S) k)
    (q : PrimeSpectrum S)
    (hqf : (fiberPrimeAt R S q).asIdeal.primeHeight ≤ k) :
    IsRegularLocalRing
      ((Localization.AtPrime q.asIdeal) ⧸
        Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (q.asIdeal.under R)) := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  let I : Ideal S := Ideal.map (algebraMap R S) p.asIdeal
  let Qloc :=
    (Localization.AtPrime q.asIdeal) ⧸
      Ideal.map (algebraMap S (Localization.AtPrime q.asIdeal)) I
  have hQloc :
      Ideal.map (algebraMap S (Localization.AtPrime q.asIdeal)) I =
        Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal := by
    -- Proof comment: extending `p` to `S` and then localizing is the same as extending `p`
    -- directly to the local ring `S_q`.
    dsimp [I]
    simpa [IsScalarTower.algebraMap_eq R S (Localization.AtPrime q.asIdeal)] using
      (Ideal.map_map (I := p.asIdeal) (f := algebraMap R S)
        (g := algebraMap S (Localization.AtPrime q.asIdeal)))
  let eTarget :
      Qloc ≃+*
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal) :=
    Ideal.quotEquivOfEq hQloc
  have hfiberLocal :
      IsRegularLocalRing (fiberLocalRingAt R S q) := by
    -- Proof comment: the fiberwise `(R_k)` hypothesis is used exactly at the prime
    -- `fiberPrimeAt R S q` of the fiber ring over `p = q ∩ R`.
    simpa [fiberLocalRingAt, p] using
      ((hfiber p).isRegularLocalRing_localizationAtPrime (fiberPrimeAt R S q) hqf)
  have hqbarPrime : (Ideal.map (Ideal.Quotient.mk I) q.asIdeal).IsPrime := by
    have hI_le_q : I ≤ q.asIdeal := by
      rw [Ideal.map_le_iff_le_comap]
      simpa [I, p, PrimeSpectrum.comap_asIdeal]
    exact Ideal.map_isPrime_of_surjective (f := Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective <| by
        simpa [Ideal.mk_ker] using hI_le_q
  let qbar : PrimeSpectrum (S ⧸ I) :=
    ⟨Ideal.map (Ideal.Quotient.mk I) q.asIdeal, hqbarPrime⟩
  let M : Submonoid (S ⧸ I) := Algebra.algebraMapSubmonoid (S ⧸ I) q.asIdeal.primeCompl
  let eLoc :
      Localization M ≃ₐ[S ⧸ I] Qloc :=
    Localization.algEquiv M Qloc
  have hSub :
      M = qbar.asIdeal.primeCompl := by
    -- Proof comment: quotienting by `pS` turns `q` into the induced prime `q̄`, so the source
    -- denominator submonoid is exactly `q̄.primeCompl`.
    simpa [M, qbar] using
      quotient_primeCompl_eq_algebraMapSubmonoid I q.asIdeal
        (by
          rw [Ideal.map_le_iff_le_comap]
          simpa [I, p, PrimeSpectrum.comap_asIdeal])
  letI : IsLocalization M (Localization.AtPrime qbar.asIdeal) := by
    simpa [hSub] using
      (inferInstance : IsLocalization qbar.asIdeal.primeCompl (Localization.AtPrime qbar.asIdeal))
  let eQuot :
      Qloc ≃ₐ[S ⧸ I] Localization.AtPrime qbar.asIdeal :=
    eLoc.symm.trans (Localization.algEquiv M (Localization.AtPrime qbar.asIdeal))
  have hquotLocal :
      IsRegularLocalRing (Localization.AtPrime qbar.asIdeal) := by
    let T : Submonoid (S ⧸ I) :=
      Algebra.algebraMapSubmonoid (S ⧸ I) (nonZeroDivisors (R ⧸ p.asIdeal))
    let eFiber :
        Localization T ≃ₐ[S ⧸ I] p.asIdeal.Fiber S :=
      fiber_quotient_localization_algEquiv (R := R) (S := S) p
    let qT : PrimeSpectrum (Localization T) :=
      PrimeSpectrum.comap eFiber.toRingHom (fiberPrimeAt R S q)
    have hI_le_q : I ≤ q.asIdeal := by
      rw [Ideal.map_le_iff_le_comap]
      simpa [I, p, PrimeSpectrum.comap_asIdeal]
    have hqTcomap :
        Ideal.comap (algebraMap (S ⧸ I) (Localization T)) qT.asIdeal = qbar.asIdeal := by
      -- Proof comment: transport the fiber prime back through the quotient presentation of the
      -- fiber ring, then contract further along `S → S / pS`.
      have hFiberComap :
          Ideal.comap (algebraMap S (p.asIdeal.Fiber S)) (fiberPrimeAt R S q).asIdeal =
            q.asIdeal := by
        have hleft :
            ↑((PrimeSpectrum.preimageEquivFiber R S p).symm (fiberPrimeAt R S q)) = q := by
          simpa [p, fiberPrimeAt] using
            congrArg Subtype.val
              ((PrimeSpectrum.preimageEquivFiber R S p).symm_apply_apply ⟨q, rfl⟩)
        have hcomap :
            PrimeSpectrum.comap (algebraMap S (p.asIdeal.Fiber S)) (fiberPrimeAt R S q) = q := by
          calc
            PrimeSpectrum.comap (algebraMap S (p.asIdeal.Fiber S)) (fiberPrimeAt R S q) =
                ↑((PrimeSpectrum.preimageEquivFiber R S p).symm (fiberPrimeAt R S q)) := by
                  change PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom
                      (fiberPrimeAt R S q) =
                    ↑((PrimeSpectrum.preimageEquivFiber R S p).symm (fiberPrimeAt R S q))
                  rfl
            _ = q := hleft
        simpa using congrArg PrimeSpectrum.asIdeal hcomap
      apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
      rw [Ideal.comap_comap, PrimeSpectrum.comap_asIdeal, Ideal.comap_comap]
      rw [show
          eFiber.toRingHom.comp
              ((algebraMap (S ⧸ I) (Localization T)).comp (Ideal.Quotient.mk I)) =
            algebraMap S (p.asIdeal.Fiber S) by
              ext s
              -- Proof comment: the quotient presentation and the fiber inclusion agree on `S`.
              calc
                eFiber.toRingHom
                    ((algebraMap (S ⧸ I) (Localization T)) (Ideal.Quotient.mk I s)) =
                    algebraMap (S ⧸ I) (p.asIdeal.Fiber S) (Ideal.Quotient.mk I s) := by
                      exact eFiber.commutes (Ideal.Quotient.mk I s)
                _ = algebraMap S (p.asIdeal.Fiber S) s := by
                      rw [quotient_to_fiber_algebraMap_mk
                        (R := R) (S := S) (p := p)]
                      rfl]
      simpa [qbar, I, Ideal.comap_map_mk hI_le_q] using
        hFiberComap
    let qbar' : PrimeSpectrum (S ⧸ I) :=
      PrimeSpectrum.comap (algebraMap (S ⧸ I) (Localization T)) qT
    let eSource :
        Localization.AtPrime qbar.asIdeal ≃+* Localization.AtPrime qbar'.asIdeal :=
      Localization.localRingEquiv qbar.asIdeal qbar'.asIdeal (RingEquiv.refl (S ⧸ I))
        (by simpa [qbar'] using hqTcomap.symm)
    let eTower :
        Localization.AtPrime qbar'.asIdeal ≃+* Localization.AtPrime qT.asIdeal :=
      -- Proof comment: localizing the quotient presentation again at the prime over `q̄`
      -- collapses the localization tower.
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := T) qT.asIdeal).toRingEquiv
    let eFiberLocal0 :
        Localization.AtPrime qT.asIdeal ≃+*
          Localization.AtPrime (fiberPrimeAt R S q).asIdeal :=
      -- Proof comment: localizing corresponding primes along the quotient-to-fiber algebra
      -- equivalence recovers the fiber local ring.
      Localization.localRingEquiv qT.asIdeal (fiberPrimeAt R S q).asIdeal eFiber.toRingEquiv
        (PrimeSpectrum.comap_asIdeal (f := eFiber.toRingHom) (fiberPrimeAt R S q))
    let eFiberLocal :
        Localization.AtPrime qT.asIdeal ≃+* fiberLocalRingAt R S q := by
      simpa [fiberLocalRingAt] using eFiberLocal0
    letI : IsRegularLocalRing (fiberLocalRingAt R S q) := hfiberLocal
    exact IsRegularLocalRing.of_ringEquiv ((eSource.trans eTower).trans eFiberLocal).symm
  letI : IsRegularLocalRing (Localization.AtPrime qbar.asIdeal) := hquotLocal
  have hQlocRegular : IsRegularLocalRing Qloc := by
    -- Proof comment: the quotient-localization comparison reduces regularity of `Qloc` to the
    -- same property on the induced quotient-prime localization of `S / pS`.
    exact IsRegularLocalRing.of_ringEquiv eQuot.toRingEquiv.symm
  -- Proof comment: finally transport regularity from the `I = pS` quotient model back to the
  -- literal target quotient appearing in the statement.
  simpa [p] using (IsRegularLocalRing.of_ringEquiv eTarget)

/-- Helper for Lemma 10.163.5: regularity of the quotient presentation `S_q / (q ∩ R)S_q`
implies regularity of the closed fiber of `R_(q ∩ R) → S_q`. -/
lemma isRegularLocalRing_closedFiber_of_localized_quotient_regular
    (q : PrimeSpectrum S)
    [IsRegularLocalRing
      ((Localization.AtPrime q.asIdeal) ⧸
        Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (q.asIdeal.under R))] :
    IsRegularLocalRing
      ((IsLocalRing.maximalIdeal (Localization.AtPrime (q.asIdeal.under R))).Fiber
        (Localization.AtPrime q.asIdeal)) := by
  let p : Ideal R := q.asIdeal.under R
  let Sq := Localization.AtPrime q.asIdeal
  let Rp := Localization.AtPrime p
  letI : q.asIdeal.LiesOver p := by
    simpa [p] using (Ideal.over_under q.asIdeal)
  -- Proof comment: rewrite the local closed-fiber quotient ideal as the localized base prime,
  -- then invoke the closed-fiber-from-quotient criterion from Lemma `10.112.8`.
  have hmap :
      Ideal.map (algebraMap Rp Sq) (IsLocalRing.maximalIdeal Rp) =
        Ideal.map (algebraMap R Sq) p := by
    simpa [p, Rp, Sq] using
      localized_base_prime_eq_map_maximalIdeal (R := R) (S := S) p q.asIdeal
        (Ideal.over_under q.asIdeal)
  have hquot :
      IsRegularLocalRing
        (Sq ⧸ Ideal.map (algebraMap Rp Sq) (IsLocalRing.maximalIdeal Rp)) := by
    rw [hmap]
    infer_instance
  -- Proof comment: the closed fiber is canonically equivalent to that quotient presentation.
  letI :
      IsRegularLocalRing
        (Sq ⧸ Ideal.map (algebraMap Rp Sq) (IsLocalRing.maximalIdeal Rp)) := hquot
  simpa [p, Rp, Sq] using
    (isRegularLocalRing_closedFiber_of_quotient
      (R := Rp) (S := Sq))

/-- Helper for Lemma 10.163.5: if the fiber prime of `q` has codimension at most `k`, then the
closed fiber of `R_(q ∩ R) → S_q` is a regular local ring. -/
lemma isRegularLocalRing_closedFiber_of_fiberPrimeAt_bound
    (hfiber : ∀ p : PrimeSpectrum R, SerreConditionR (p.asIdeal.Fiber S) k)
    (q : PrimeSpectrum S)
    (hqf : (fiberPrimeAt R S q).asIdeal.primeHeight ≤ k) :
    IsRegularLocalRing
      ((IsLocalRing.maximalIdeal (Localization.AtPrime (q.asIdeal.under R))).Fiber
        (Localization.AtPrime q.asIdeal)) := by
  letI :
      IsRegularLocalRing
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (q.asIdeal.under R)) :=
    isRegularLocalRing_localized_quotient_of_fiberPrimeAt_bound
      (R := R) (S := S) (k := k) hfiber q hqf
  -- Proof comment: once the quotient presentation is regular, Lemma `10.112.8` converts it to
  -- the exact closed-fiber object used in the final flat-local regularity step.
  exact
    isRegularLocalRing_closedFiber_of_localized_quotient_regular
      (R := R) (S := S) q

/-- Lemma 10.163.5: for a flat ring map `R → S`, if `R` satisfies LinearRepresentations_Serre_1977's condition `(R_k)`, `S`
is Noetherian, and every fiber ring `κ(𝔭) ⊗[R] S`, formalized as `p.asIdeal.Fiber S`, satisfies
`(R_k)`, then `S` satisfies `(R_k)`. -/
theorem serreConditionR_of_flat_of_fiber
    (hfiber : ∀ p : PrimeSpectrum R, SerreConditionR (p.asIdeal.Fiber S) k) :
    SerreConditionR S k := by
  refine
    { toIsNoetherian := inferInstance
      isRegularLocalRing_localizationAtPrime := ?_ }
  intro q hq
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  letI : q.asIdeal.LiesOver p.asIdeal := by
    simpa [p] using (Ideal.over_under q.asIdeal)
  letI : IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
    -- Proof comment: the dimension formula bounds `q ∩ R` by `k`, so the base localization is
    -- regular by the `(R_k)` hypothesis on `R`.
    exact
      SerreConditionR.isRegularLocalRing_localizationAtPrime p
        (primeHeight_under_and_fiberPrimeAt_le_of_primeHeight_le
          (R := R) (S := S) (k := k) q hq).1
  have hclosedFiber :
      IsRegularLocalRing
        ((IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)).Fiber
          (Localization.AtPrime q.asIdeal)) := by
    -- Proof comment: the second summand in the dimension formula is the local fiber codimension,
    -- so the fiberwise `(R_k)` hypothesis supplies the closed-fiber regularity input.
    simpa [p] using
      isRegularLocalRing_closedFiber_of_fiberPrimeAt_bound
        (R := R) (S := S) (k := k) hfiber q
        (primeHeight_under_and_fiberPrimeAt_le_of_primeHeight_le
          (R := R) (S := S) (k := k) q hq).2
  have halg :
      Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R S)
          (q.asIdeal.over_def p.asIdeal) =
        algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    Localization.localRingHom_unique _ _ _ _ fun x ↦ by
      rw [← IsScalarTower.algebraMap_apply R S (Localization.AtPrime q.asIdeal) x]
      rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime q.asIdeal) x]
  have hflat :
      (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)).Flat := by
    have hflatRS : (algebraMap R S).Flat := by
      rw [RingHom.flat_algebraMap_iff]
      infer_instance
    -- Proof comment: flatness localizes along the canonical local map `R_p → S_q`.
    simpa [halg] using
      (RingHom.Flat.localRingHom hflatRS q.asIdeal p.asIdeal (q.asIdeal.over_def p.asIdeal))
  letI : Module.Flat (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    (RingHom.flat_algebraMap_iff).mp hflat
  letI : IsLocalHom
      (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)) := by
    -- Proof comment: the localized map is a local homomorphism by construction.
    simpa [halg] using
      (Localization.isLocalHom_localRingHom p.asIdeal q.asIdeal
        (algebraMap R S) (q.asIdeal.over_def p.asIdeal))
  -- Proof comment: Lemma `10.112.8` is now applied exactly in the source-proof form.
  exact isRegularLocalRing_of_flat_localHom_of_regular_closedFiber hclosedFiber

end

/-! ### Lemma_10_163_6 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling pass:
* primary domain: Noetherian commutative algebra of ascent of reducedness along flat maps;
* sampled owner declarations of the same kind:
  - `IsReduced`, the owner for ring reducedness;
  - `isReduced_iff_serreConditionR_zero_and_serreConditionS_one`, the canonical owner-level
    characterization of reducedness by LinearRepresentations_Serre_1977 conditions;
  - `serreConditionR_of_flat_of_fiber`, the chapter ascent theorem for `(R₀)`;
  - `serreConditionS_of_flat_of_fiber`, the chapter ascent theorem for `(S₁)`.

Best owner abstraction:
* the public target stays the source-facing reducedness theorem, but the proof should pass entirely
  through the canonical owners `IsReduced`, `SerreConditionR`, and `SerreConditionS`, instead of
  keeping a parallel reducedness-specific local wheel.

Primitive data vs. derived API:
* primitive data: the flat algebra `R → S`, the Noetherian hypotheses on `R` and `S`, the
  reduced base-ring owner `[IsReduced R]`, and the fiberwise reducedness hypothesis `hfiber`;
* derived API: the `(R₀)` and `(S₁)` instances for the base and the fibers, obtained canonically
  from the LinearRepresentations_Serre_1977 criterion and then fed into the existing ascent theorems.

Source/core/bridge triage:
* `source-facing`: `isReduced_of_flat_of_fiber`, the textbook ascent statement for reducedness;
* `core/canonical`: `IsReduced`, `SerreConditionR`, `SerreConditionS`, and the criterion
  `isReduced_iff_serreConditionR_zero_and_serreConditionS_one`;
* `bridge/view`: the two ascent theorems for `(R₀)` and `(S₁)` along the flat map.
-/
-- Proof sketch: for Noetherian rings, reducedness is equivalent to LinearRepresentations_Serre_1977's conditions `(S_1)` and
-- `(R_0)` by Lemma `10.157.3`. Apply the flat ascent results `10.163.4` and `10.163.5` to the base
-- ring `R` and the reduced fiber rings `p.asIdeal.Fiber S`, then invoke Lemma `10.157.3` again to
-- recover reducedness of `S`.
/-- Lemma 10.163.6: if `R → S` is flat, `R` and `S` are Noetherian, `R` is reduced, and every
fiber ring `κ(𝔭) ⊗[R] S`, formalized as `p.asIdeal.Fiber S`, is reduced, then `S` is reduced. -/
theorem isReduced_of_flat_of_fiber
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S] [IsReduced R]
    (hfiber : ∀ p : PrimeSpectrum R, IsReduced (p.asIdeal.Fiber S)) :
    IsReduced S := by
  have hfiber_serre (p : PrimeSpectrum R) :
      SerreConditionR (p.asIdeal.Fiber S) 0 ∧ SerreConditionS (p.asIdeal.Fiber S) 1 :=
    isReduced_iff_serreConditionR_zero_and_serreConditionS_one.1 (hfiber p)
  have hSR : SerreConditionR S 0 :=
    serreConditionR_of_flat_of_fiber fun p ↦ (hfiber_serre p).1
  have hSS : SerreConditionS S 1 :=
    serreConditionS_of_flat_of_fiber fun p ↦ (hfiber_serre p).2
  exact isReduced_iff_serreConditionR_zero_and_serreConditionS_one.2 ⟨hSR, hSS⟩

end

/-! ### Lemma_10_163_7 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.Smooth R S] [IsReduced R]

/- Domain-style sampling pass:
* primary domain: commutative algebra of smooth ring maps and ascent of reducedness;
* sampled owner declarations of the same kind:
  - `Algebra.Smooth`, the ambient owner of the source hypothesis;
  - `Algebra.Smooth.flat`, the canonical flatness consequence used downstream;
  - `isReduced_of_flat_of_fiber`, the chapter owner for reducedness ascent from reduced fibers;
  - `Algebra.IsGeometricallyReduced`, the field-valued owner underlying the fiberwise reducedness
    step in the proof sketch.

Best owner abstraction:
* the source-facing owner here is already `isReduced_of_smooth`; the smooth structure
  `[Algebra.Smooth R S]` is primitive data, while flatness and fiberwise reducedness are derived
  API that should be supplied by canonical owners rather than by a local wrapper.

Primitive data vs. derived API:
* primitive data: the smooth `R`-algebra structure on `S` and the reducedness owner `[IsReduced R]`;
* derived API: flatness of `R → S`, smoothness or geometric reducedness of the residue-field
  fibers, and the final ascent step through `isReduced_of_flat_of_fiber`.

Source/core/bridge triage:
* `source-facing`: `isReduced_of_smooth`, the textbook reducedness ascent statement for smooth
  algebras;
* `core/canonical`: `Algebra.Smooth`, `IsReduced`, and the field-level owner
  `Algebra.IsGeometricallyReduced`;
* `bridge/view`: the canonical fiberwise reducedness consequences of smoothness together with the
  reducedness-ascent theorem `isReduced_of_flat_of_fiber`.
-/
-- Proof sketch: smooth algebras are flat by `Algebra.Smooth.flat`, and smoothness is preserved
-- under base change to residue fields. A smooth algebra over a field is geometrically reduced, so
-- every fiber `κ(𝔭) ⊗[R] S` is reduced; then Lemma `10.163.6` gives the result.
/-- Lemma 10.163.7: if `R → S` is smooth and `R` is reduced, then `S` is reduced. -/
theorem isReduced_of_smooth :
    IsReduced S := sorry

/-- Smooth algebras over reduced base rings are reduced. -/
instance : IsReduced S :=
  isReduced_of_smooth

end

/-! ### Lemma_10_163_8 (from Chap10) -/
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S] [IsNormalRing R]

/-
Domain-style sampling pass:
* primary domain: Noetherian commutative algebra of ascent of normality along flat maps;
* sampled owner declarations of the same kind:
  - `IsNormalRing`, the chapter owner for ring normality;
  - `isNormalRing_iff_serreConditionR_one_and_serreConditionS_two`, the canonical LinearRepresentations_Serre_1977-criterion
    owner-level characterization of normality;
  - `serreConditionR_of_flat_of_fiber`, the chapter ascent theorem for `(R₁)`;
  - `serreConditionS_of_flat_of_fiber`, the chapter ascent theorem for `(S₂)`;
  - `Algebra.EssFiniteType.isNoetherianRing`, the canonical Noetherianity owner for the fiber
    ring `p.asIdeal.Fiber S` via the upstream instance `Algebra.EssFiniteType R p.asIdeal.ResidueField`.

Best owner abstraction:
* the public target stays the source-facing normality theorem, but its proof should pass entirely
  through the owner predicates `IsNormalRing`, `SerreConditionR`, and `SerreConditionS`, rather
  than duplicating local wheel definitions for the LinearRepresentations_Serre_1977 conditions.

Primitive data vs. derived API:
* primitive data: the flat algebra `R → S`, the Noetherian hypotheses on `R` and `S`, the normal
  base-ring owner `[IsNormalRing R]`, and the fiberwise normality hypothesis `hfiber`;
* derived API: the `(R₁)` and `(S₂)` instances for the base and the fibers, obtained canonically
  from the LinearRepresentations_Serre_1977 criterion, together with fiberwise Noetherianity obtained canonically from
  `Algebra.EssFiniteType.isNoetherianRing`, and then fed into the existing ascent theorems.

Source/core/bridge triage:
* `source-facing`: `isNormalRing_of_flat_of_fiber`, the textbook ascent statement for normality;
* `core/canonical`: `IsNormalRing`, `SerreConditionR`, `SerreConditionS`, and the criterion
  `isNormalRing_iff_serreConditionR_one_and_serreConditionS_two`;
* `bridge/view`: the two ascent theorems for `(R₁)` and `(S₂)` along the flat map.
-/

-- Proof sketch: by LinearRepresentations_Serre_1977's criterion, it is enough to prove that `S` satisfies `(R_1)` and
-- `(S_2)`. The normality of `R` and of each fiber ring gives these LinearRepresentations_Serre_1977 conditions on `R` and on
-- every fiber. Apply Lemmas `10.163.5` and `10.163.4` to ascend `(R_1)` and `(S_2)` along the flat
-- map `R → S`, and conclude that `S` is normal by LinearRepresentations_Serre_1977's criterion again.
/-- Lemma 10.163.8: for a flat ring map `R → S` between Noetherian rings, if `R` is normal and
every fiber ring `κ(𝔭) ⊗[R] S`, formalized as `p.asIdeal.Fiber S`, is normal, then `S` is a
normal ring. -/
theorem isNormalRing_of_flat_of_fiber
    (hfiber : ∀ p : PrimeSpectrum R, IsNormalRing (p.asIdeal.Fiber S)) :
    IsNormalRing S := by
  have hR :
      R ⊧ (R₁) ∧ R ⊧ (S₂) :=
    isNormalRing_iff_serreConditionR_one_and_serreConditionS_two.1 inferInstance
  let _ : R ⊧ (R₁) := hR.1
  let _ : R ⊧ (S₂) := hR.2
  have hfiberSerre (p : PrimeSpectrum R) :
      (p.asIdeal.Fiber S) ⊧ (R₁) ∧ (p.asIdeal.Fiber S) ⊧ (S₂) := by
    let _ : Algebra.EssFiniteType S (S ⊗[R] p.asIdeal.ResidueField) := inferInstance
    let _ : IsNoetherianRing (S ⊗[R] p.asIdeal.ResidueField) :=
      Algebra.EssFiniteType.isNoetherianRing S (S ⊗[R] p.asIdeal.ResidueField)
    let _ : IsNoetherianRing (p.asIdeal.Fiber S) :=
      isNoetherianRing_of_ringEquiv (S ⊗[R] p.asIdeal.ResidueField)
        (Algebra.TensorProduct.comm R p.asIdeal.ResidueField S).toRingEquiv.symm
    exact isNormalRing_iff_serreConditionR_one_and_serreConditionS_two.1 (hfiber p)
  have hSR : S ⊧ (R₁) :=
    serreConditionR_of_flat_of_fiber fun p ↦ (hfiberSerre p).1
  have hSS : S ⊧ (S₂) :=
    serreConditionS_of_flat_of_fiber fun p ↦ (hfiberSerre p).2
  exact isNormalRing_iff_serreConditionR_one_and_serreConditionS_two.2 ⟨hSR, hSS⟩

end

/-! ### Lemma_10_163_9 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.Smooth R S] [IsNormalRing R]

/- Domain-style sampling pass:
* primary domain: commutative algebra of smooth ring maps and ascent of normality;
* sampled owner declarations:
  `IsNormalRing`,
  `Algebra.Smooth`,
  `isNormalRing_of_flat_of_fiber`,
  `isRegularRing_of_smooth`,
  `isNormalRing_of_isRegularRing`;
* best owner abstraction: this theorem is a `source-facing` smooth-ascent statement, while the
  canonical owner theorem is `isNormalRing_of_flat_of_fiber`; smoothness and fiber regularity
  should remain derived API rather than being repackaged locally.

Primitive data vs. derived API:
* primitive data: the smooth `R`-algebra structure on `S` and the normal-ring owner `[IsNormalRing R]`;
* derived API: flatness of `R → S`, smoothness of every residue-field fiber by base change,
  regularity of those fibers from `isRegularRing_of_smooth`, and their normality from
  `isNormalRing_of_isRegularRing`.

Layering:
* `source-facing`: `isNormalRing_of_smooth`;
* `core/canonical`: `IsNormalRing`, `Algebra.Smooth`, and `isNormalRing_of_flat_of_fiber`;
* `bridge/view`: smooth base change to `p.asIdeal.Fiber S` and the regular-to-normal bridge on the
  fibers.
-/
-- Proof sketch: smooth algebras are flat, so it is enough to apply the canonical ascent theorem
-- `isNormalRing_of_flat_of_fiber`. Each fiber `κ(𝔭) ⊗[R] S`, formalized as `p.asIdeal.Fiber S`,
-- is smooth over the field `κ(𝔭)` by base change, hence regular by Lemma `10.163.10`, and
-- therefore normal by Lemma `10.157.5`.
/-- Lemma 10.163.9: if `R → S` is smooth and `R` is a normal ring, then `S` is a normal ring. -/
theorem isNormalRing_of_smooth :
    IsNormalRing S := sorry

/-- Smooth algebras over normal base rings are normal. -/
instance : IsNormalRing S :=
  isNormalRing_of_smooth

end

/-! ### Lemma_10_163_10 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.Smooth R S] [IsRegularRing R]

/- Domain-style sampling pass:
* primary domain: commutative algebra of smooth algebras, regular ring maps, and regular rings;
* sampled owner declarations:
  `IsRegularRing`,
  `RingHom.IsRegularRingMap`,
  `Algebra.isGeometricallyRegular_of_smooth`,
  `Algebra.isRegularRing_of_regularRingMap`;
* best owner abstraction: the source-facing statement here remains the smooth-specialized ascent
  theorem, but its canonical proof owner is `RingHom.IsRegularRingMap (algebraMap R S)`; smoothness supplies
  the flatness and geometrically regular fibers needed for that owner, and regularity of `S` is
  then derived API from `Algebra.isRegularRing_of_regularRingMap`.

Primitive data vs. derived API:
* primitive public inputs: `[Algebra.Smooth R S]` and `[IsRegularRing R]`;
* derived API: the regular-map owner on `R → S`, obtained by base-changing smoothness to every
  fiber and applying geometric-regularity ascent over the residue fields.

Source/core/bridge triage:
* `source-facing`: `isRegularRing_of_smooth`;
* `core/canonical`: `RingHom.IsRegularRingMap (algebraMap R S)` and `IsRegularRing S`;
* `bridge/view`: `Algebra.Smooth.baseChange` on the fibers and
  `Algebra.isGeometricallyRegular_of_smooth`.
-/
-- Proof sketch: package the smooth map `R → S` as a regular ring map. Flatness is already a
-- canonical consequence of smoothness, and for each prime `p ⊂ R` the fiber `κ(𝔭) ⊗[R] S` is
-- smooth over `κ(𝔭)` by base change, hence geometrically regular over `κ(𝔭)` by Lemma
-- `10.166.4`. The canonical regular-map ascent theorem then yields `IsRegularRing S`.
/-- Lemma 10.163.10: if `R → S` is smooth and `R` is a regular ring, then `S` is a regular ring. -/
theorem isRegularRing_of_smooth
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] [IsRegularRing R] :
    IsRegularRing S := by
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  let _ : RingHom.IsRegularRingMap (algebraMap R S) := by
    exact
      { toFlat := RingHom.flat_algebraMap_iff.mpr inferInstance
        isGeometricallyRegular_fiber := fun p ↦ by
          letI : Algebra.Smooth p.asIdeal.ResidueField (p.asIdeal.Fiber S) := inferInstance
          letI :
              Algebra.IsGeometricallyRegular p.asIdeal.ResidueField p.asIdeal.ResidueField :=
            inferInstance
          infer_instance }
  exact Algebra.isRegularRing_of_regularRingMap R

end
