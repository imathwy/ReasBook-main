import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Noetherian.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_27_1 (from Chap15) -/
open scoped DirectSum
open AdicCompletion
open LinearMap

universe u v

section

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (A : Type v)

/- Domain triage:
- primary domain: adic completion functoriality and universal injectivity of linear maps;
- sampled owner declarations of the same kind:
  `mapToComplete` and `mapToComplete_comp_of` from the completion bridge API,
  `AdicCompletion.Families.pi` and `LinearEquiv.piCongrRight` for the canonical product
  comparison,
  the owner criterion `LinearMap.universallyInjective_iff_injective_mod_finite_ideal`,
  and the owner flatness theorem `Module.noetherian_pi_flat_and_mittagLeffler`;
- primitive data: the ideal `I`, the index type `A`, and the direct-sum inclusion
  `DirectSum.coeFnLinearMap R`;
- source/core/bridge triage:
  `source-facing`: the universally injective comparison map from the completed direct sum to the
  product `A → R`;
  `core/canonical`: the owner predicate `LinearMap.UniversallyInjective`;
  `bridge/view`: the canonical comparison is the composite of
  `AdicCompletion.map I (DirectSum.coeFnLinearMap R)`,
  `AdicCompletion.Families.pi I (fun _ : A ↦ R)`,
  and the pointwise completion equivalence
  `LinearEquiv.piCongrRight (fun _ : A ↦ (AdicCompletion.ofLinearEquiv I R).symm)`.
-/
variable [IsAdicComplete I R]

/-- The canonical map from the completed direct sum `AdicCompletion I (⨁ a, R)` to the product
`A → R`, obtained by functoriality of completion followed by the coordinatewise identification of
the completion of a product with the product of the completed coordinates. -/
noncomputable abbrev adicCompletionDirectSumToPi :
    AdicCompletion I (⨁ _ : A, R) →ₗ[R] A → R :=
  ((LinearEquiv.piCongrRight fun _ : A ↦ (ofLinearEquiv I R).symm).toLinearMap).comp
    (((AdicCompletion.pi I (fun _ : A ↦ R)).restrictScalars R).comp
      ((map I (DirectSum.coeFnLinearMap R)).restrictScalars R))

@[simp]
theorem adicCompletionDirectSumToPi_of (x : ⨁ _ : A, R) :
    adicCompletionDirectSumToPi I A (of I (⨁ _ : A, R) x) = DirectSum.coeFnLinearMap R x := by
  ext a
  change (ofLinearEquiv I R).symm
      (map I (LinearMap.proj a) ((map I (DirectSum.coeFnLinearMap R)) (of I (⨁ _ : A, R) x))) =
    x a
  rw [map_of, map_of, ofLinearEquiv_symm_of]
  rfl

@[simp]
theorem adicCompletionDirectSumToPi_comp_of :
    (adicCompletionDirectSumToPi I A).comp (of I (⨁ _ : A, R)) = DirectSum.coeFnLinearMap R := by
  ext x a
  rw [LinearMap.comp_apply, adicCompletionDirectSumToPi_of]

variable [IsNoetherianRing R]

-- Proof sketch: the product module `A → R` is flat by `Module.noetherian_pi_flat_and_mittagLeffler`,
-- so the owner criterion `LinearMap.universallyInjective_iff_injective_mod_finite_ideal` reduces
-- the goal to injectivity modulo finitely generated ideals. For such an ideal, test after
-- tensoring with the finite quotient module, use completion exactness together with Artin-Rees to
-- control lifts through the completed direct sum, and identify the resulting comparison map with
-- the coordinatewise inclusion via the canonical computation
-- `adicCompletionDirectSumToPi_comp_of I A`.
/-- Lemma 15.27.1: if `R` is Noetherian and `I`-adically complete, then the canonical map from the
`I`-adic completion of `⨁ a, R` to the product `∀ a, R` is universally injective. -/
theorem adicCompletionDirectSumToPi_universallyInjective :
    (adicCompletionDirectSumToPi I A).UniversallyInjective := by
  letI : Module.Flat R (A → R) :=
    (Module.noetherian_pi_flat_and_mittagLeffler : _
      ∧ Module.MittagLeffler R (A → R)).1
  refine (universallyInjective_iff_injective_mod_finite_ideal
    (adicCompletionDirectSumToPi I A)).2 ?_
  intro J hJ
  sorry

end

/-! ### Lemma_15_27_2 (from Chap15) -/
open scoped DirectSum

universe u v

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/- Domain triage:
- primary domain: flatness of adic completions of free modules over a Noetherian ring;
- sampled owner declarations of the same kind:
  `Module.Flat`,
  `AdicCompletion.flat_of_isNoetherian`,
  `adicCompletionDirectSumToPi_universallyInjective`,
  `adicCompletion_isNoetherian_and_flat_of_flat_mod_ideal_and_tor_one_vanishing`;
- primitive data: the ideal `I`, the index type `A`, and the free `R`-module `⨁ a : A, R`;
- derived API: the universally injective comparison with the product module from
  Lemma `15.27.1`, and the more general completion-flatness criterion later packaged in
  Lemma `15.27.5`.

Source/core/bridge triage:
- `source-facing`: the flatness statement for the completed direct sum from the Stacks lemma;
- `core/canonical`: the owner predicate `Module.Flat`;
- `bridge/view`: the canonical comparison map from the completed direct sum to the product module.
-/

-- Proof sketch: combine the universally injective comparison map from Lemma `15.27.1` with the
-- flatness of the product module over a Noetherian ring and the flat completion map
-- `R → AdicCompletion I R`. The public statement should remain on the canonical owner
-- `Module.Flat R (AdicCompletion I (⨁ a, R))`; the comparison map and any quotient/tensor bridges
-- belong to the proof route rather than the theorem surface.
/-- Lemma 15.27.2: for a Noetherian ring `R`, ideal `I`, and set `A`, the `I`-adic completion of
the direct sum `⨁ a : A, R` is a flat `R`-module. -/
theorem adicCompletion_directSum_flat (I : Ideal R) (A : Type v) :
    Module.Flat R (AdicCompletion I (⨁ _ : A, R)) := sorry

end

/-! ### Lemma_15_27_3 (from Chap15) -/
noncomputable section

open CategoryTheory ModuleCat AdicCompletion

universe u

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I : Ideal A)
variable {M : Type u} [AddCommGroup M] [Module A M]

/- Domain-style sampling for the Artin-Rees vanishing statement on Tor:
- primary domain: commutative algebra and homological algebra of the Tor tower
  `Tor_p^A(M, A / I^n)` over ideal-power quotients;
- sampled owner declarations of the same kind:
  `Tor[A, p](M, N)`,
  `AdicCompletion.transitionMap`,
  `CategoryTheory.SequentialInverseSystem.transitionMap`,
  `Functor.ofOpSequence`;
- best owner abstraction: the source-facing theorem should use the canonical Tor tower as a
  `SequentialInverseSystem (ModuleCat A)`, with transition maps derived from the owner API
  `SequentialInverseSystem.transitionMap`; the Artin-Rees argument is proof-level and should not
  appear as extra public data;
- primitive data: the ideal `I`, the finite `A`-module `M`, and the positive degree `p`;
- derived API: the quotient-power Tor inverse system and the eventual vanishing theorem for its
  canonical transition morphisms; the associated inverse system should be assembled directly with
  `Functor.ofOpSequence`.

Source/core/bridge triage:
- `source-facing`: the eventual vanishing statement for
  `Tor_p^A(M, A / I^n) ⟶ Tor_p^A(M, A / I^(n - c))`;
- `core/canonical`: `Tor[A, p](M, N)`, `SequentialInverseSystem.transitionMap`, and
  `Functor.ofOpSequence`;
- `bridge/view`: the quotient transition morphisms `A ⧸ I^(n + 1) → A ⧸ I^n`, pushed through the
  canonical functor `Tor[A, p](M, -)` and assembled by `Functor.ofOpSequence`; the only public
  derived owner remains the resulting inverse system.
-/

/-- The inverse system `(Tor_p^A(M, A ⧸ I^n))_n` attached to the ideal-power quotients of `A`.
Since `I ^ 0 = ⊤`, stage `0` is the zero Tor object. -/
abbrev idealPowerQuotientTorInverseSystem (I : Ideal A) (M : Type u) [AddCommGroup M]
    [Module A M] (p : ℕ) : SequentialInverseSystem (ModuleCat A) :=
  let X : ℕ → ModuleCat A := fun n ↦ Tor[A, p](M, A ⧸ I ^ n • (⊤ : Submodule A A))
  let f : ∀ n : ℕ, X (n + 1) ⟶ X n := fun n ↦
    ((Tor (ModuleCat A) p).obj (of A M)).map <| ofHom <| transitionMap I A (Nat.le_succ n)
  Functor.ofOpSequence f

variable [Module.Finite A M]

-- Proof sketch: present `M` by a finite free module, identify `Tor_1^A(M, A/I^n)` with
-- `(K ∩ I^n F) / I^n K`, apply Artin-Rees to make the transition map vanish for `p = 1`, and then
-- deduce the higher-degree case by dimension shifting along the presentation.
/-- Lemma 15.27.3: over a Noetherian ring, for every `p > 0` there is `c` such that the map
on `Tor_p^A(M, A ⧸ I^n)` induced by `A ⧸ I^n → A ⧸ I^(n - c)` is zero for all `n ≥ c`. -/
theorem tor_eventually_zero_map_quotient_pow (p : ℕ) (hp : 0 < p) :
    ∃ c : ℕ, ∀ n ≥ c,
      (idealPowerQuotientTorInverseSystem I M p).transitionMap (Nat.sub_le n c) = 0 := sorry

end

/-! ### Lemma_15_27_4 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open MonoidalCategory
open OrderDual

noncomputable section

universe u

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/- Domain triage:
* `source-facing`: Lemma `15.27.4` studies a sequential inverse system of `A`-modules over `ℕ+`
  and the canonical comparison map from tensoring after inverse limit to the inverse limit of the
  tensorized system.
* `core/canonical` owners: the inverse system itself as a functor `OrderDual ℕ+ ⥤ ModuleCat A`,
  its transition maps coming from `Functor.map`, the canonical comparison morphism
  `CategoryTheory.Limits.limit.post`, and the flatness owner `Module.Flat`.
* `bridge/view`: bijectivity of the comparison morphism for finite modules, then flatness of the
  inverse limit deduced from that bijectivity criterion.

Relevant owner declarations sampled for this refinement:
* `CategoryTheory.SequentialInverseSystem.stepMap`
* `CategoryTheory.Functor.map`
* `CategoryTheory.Limits.limit.post`
* `CategoryTheory.Limits.limit.post_π`
* `Module.Flat.iff_preservesFiniteLimits_tensorLeft`

Primitive data are only the inverse system `M_`, the stagewise quotient-flat hypotheses, and the
surjectivity of the successive transition maps. The tensor-limit comparison itself is canonical
derived API, so the public statement uses `limit.post` directly rather than a local wrapper.
Because the system is indexed by `OrderDual ℕ+` rather than the chapter owner `ℕᵒᵖ`, the
successor map is kept only as a private `stepMap` helper mirroring the canonical owner vocabulary. -/

private theorem pnat_le_succ (n : ℕ+) : n ≤ n + 1 := by
  exact_mod_cast Nat.le_succ (n : ℕ)

/-- The successor map `M_{n + 1} → M_n` in a positive-index inverse system of `A`-modules. -/
private abbrev stepMap (M_ : OrderDual ℕ+ ⥤ ModuleCat A) (n : ℕ+) :
    M_.obj (toDual (n + 1)) ⟶ M_.obj (toDual n) :=
  M_.map (homOfLE (pnat_le_succ n))

variable (I : Ideal A) (M_ : OrderDual ℕ+ ⥤ ModuleCat A)
variable [∀ n : ℕ+, Module (A ⧸ I ^ (n : ℕ)) (M_.obj (toDual n))]
variable [∀ n : ℕ+, IsScalarTower A (A ⧸ I ^ (n : ℕ)) (M_.obj (toDual n))]

-- Proof sketch: resolve the finite `A`-module `Q` by finite free modules, tensor that resolution
-- with each stage `M_n`, use flatness over `A ⧸ I^n` and Lemma `15.27.3` to make the inverse
-- systems of `Tor₁^A(Q, M_n)` eventually zero, then pass to inverse limits through the resulting
-- exact complexes. Because finite free modules commute with inverse limits, the cokernel computed
-- after passing to the limit identifies with `Q ⊗[A] lim M_n`.
/-- Lemma 15.27.4 (1): for a surjective inverse system `M_n` of `A`-modules whose stage `M_n` is
flat over `A ⧸ I^n`, the canonical map from `Q ⊗[A] lim M_n` to `lim (Q ⊗[A] M_n)` is bijective
for every finite `A`-module `Q`. -/
theorem inverseLimit_tensor_finiteModule_bijective_of_surjective_and_quotientFlat
    (hflat :
      ∀ n : ℕ+, Module.Flat (A ⧸ I ^ (n : ℕ)) (M_.obj (toDual n)))
    (hsurj : ∀ n : ℕ+, Function.Surjective (stepMap M_ n))
    (Q : Type u) [AddCommGroup Q] [Module A Q] [Module.Finite A Q] :
    Function.Bijective (limit.post M_ (tensorLeft (ModuleCat.of A Q))) := sorry

-- Proof sketch: by Lemma `10.39.5`, it is enough to test injectivity after tensoring with every
-- injective map of finite `A`-modules. Part `(1)` identifies tensoring with `lim M_n` against a
-- finite module with the inverse limit of the stagewise tensors. The stagewise long exact Tor
-- sequences and Lemma `15.27.3` make the obstruction on kernels eventually vanish, and the
-- exactness of inverse limits for surjective systems then yields the needed injectivity.
/-- Lemma 15.27.4 (2): if `M_n` is a surjective inverse system of `A`-modules and each stage
`M_n` is flat over `A ⧸ I^n`, then the inverse limit `lim M_n` is flat over `A`. -/
theorem inverseLimit_flat_of_surjective_and_quotientFlat
    (hflat :
      ∀ n : ℕ+, Module.Flat (A ⧸ I ^ (n : ℕ)) (M_.obj (toDual n)))
    (hsurj : ∀ n : ℕ+, Function.Surjective (stepMap M_ n)) :
    Module.Flat A ↑(limit M_) := sorry

end

/-! ### Lemma_15_27_5 (from Chap15) -/
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable {M : Type u} [AddCommGroup M] [Module R M]
variable [IsNoetherianRing (R ⧸ I)]

set_option quotPrecheck false in
local notation "Tor₁[" R "](" M ", " N ")" =>
  (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R N))

/- Domain triage:
* `source-facing`: Lemma `15.27.5` is the textbook adic-flatness criterion for a module `M`,
  keeping the hypotheses on `M / IM` and `Tor₁^R(M, R / I)` explicit.
* `core/canonical` owners: `AdicCompletion I R`, `AdicCompletion I M`, the Tor bifunctor
  `Tor₁[R](M, N)`, and the flatness owner `Module.Flat`.
* `bridge/view`: the inverse-system presentation of completion used in Lemma `15.27.4`.
* sampled declarations in the same domain:
  `Tor₁[R](M, N)`,
  `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal`,
  `flat_of_residueField_tor_one_vanishing`,
  `AdicCompletion.isAdicComplete`,
  `adicCompletion_isNoetherian_and_isAdicComplete`,
  `flat_quotient_pow_of_flat_mod_ideal_and_tor_one_quotient_vanishes`,
  `inverseLimit_flat_of_surjective_and_quotientFlat`.
* primitive data: the finitely generated ideal `I`, the quotient-flat hypothesis on
  `M ⧸ (I • ⊤)`, and the vanishing of the owner `Tor₁[R](M, R ⧸ I)`.
* derived API: Noetherianity and flatness of the completed ring/module.

The public binder is kept on the chapter source-facing surface `Tor₁[R](M, N)` rather than on the
later general `Tor[R, p]` wrapper specialized to degree `1`. -/

-- Proof sketch: Lemma `10.99.8` gives flatness of each quotient `M ⧸ (I^n • ⊤)` over
-- `R ⧸ I^n`. Lemma `10.96.3` identifies `AdicCompletion I R` and `AdicCompletion I M` with the
-- corresponding inverse limits and their quotient stages, Lemma `10.97.5` makes the completed ring
-- Noetherian, and Lemma `15.27.4` then yields flatness of the completed module over the completed
-- ring.
/-- Lemma 15.27.5: if `I` is finitely generated, `R ⧸ I` is Noetherian,
`M ⧸ (I • ⊤)` is flat over `R ⧸ I`, and `Tor₁^R(M, R ⧸ I)` vanishes, then the `I`-adic
completion `AdicCompletion I R` is Noetherian and `AdicCompletion I M` is flat over
`AdicCompletion I R`. Lean records the Tor-vanishing hypothesis as
`IsZero (Tor₁[R](M, R ⧸ I))`. -/
theorem adicCompletion_isNoetherian_and_flat_of_flat_mod_ideal_and_tor_one_vanishing
    (hI : I.FG)
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (htor : IsZero (Tor₁[R](M, R ⧸ I))) :
    IsNoetherianRing (AdicCompletion I R) ∧
      Module.Flat (AdicCompletion I R) (AdicCompletion I M) := by
  have hnoeth : IsNoetherianRing (AdicCompletion I R) :=
    (adicCompletion_isNoetherian_and_isAdicComplete I hI).1
  refine ⟨hnoeth, ?_⟩
  sorry

end
