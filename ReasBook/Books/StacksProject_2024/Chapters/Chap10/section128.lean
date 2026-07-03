import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_128_1 (from Chap10) -/
universe u v

open IsLocalRing

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsRegularLocalRing R]
variable [IsLocalRing S] [IsNoetherianRing S]
variable [IsLocalHom (algebraMap R S)]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S

/- Domain-style sampling for the miracle-flatness statement:
* primary domain: local commutative algebra of flat local maps from regular local rings with
  Cohen-Macaulay target and a closed-fiber dimension formula;
* sampled owner declarations:
  `Ideal.Fiber`,
  `Module.CohenMacaulay`,
  `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal`,
  `algebraMap_flat_of_flat_closedFiber_and_flat_over_base`;
* best owner abstraction: the closed fiber should live on the canonical owner
  `ClosedFiber = Ideal.Fiber (maximalIdeal R) S`, while the conclusion belongs on the canonical
  flatness owner `(algebraMap R S).Flat`;
* primitive data: the local map `R → S`, regularity of `R`, the explicit owner hypothesis
  `hCM : Module.CohenMacaulay S S`, and the dimension formula for `S` and the canonical closed
  fiber;
* derived API: the quotient presentation
  `S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)` of the closed fiber and the flatness
  conclusion for the algebra map.

Source/core/bridge triage:
* `source-facing`: the Stacks miracle-flatness lemma itself;
* `core/canonical`: `Module.CohenMacaulay`, `Ideal.Fiber`, and `(algebraMap R S).Flat`;
* `bridge/view`: the quotient presentation of `ClosedFiber`.
-/

-- Proof sketch: induct on `ringKrullDim R`. For positive dimension, use prime avoidance to choose
-- `x ∈ maximalIdeal R \ maximalIdeal R ^ 2` avoiding the contractions of the minimal primes of
-- `S`; this makes `x` a nonzerodivisor on the Cohen-Macaulay ring `S`. Quotienting by `x` lowers
-- both dimensions by one and preserves regularity of `R / xR` and Cohen-Macaulayness of `S / xS`,
-- so the induction hypothesis gives flatness modulo `x`. Then apply the variant of the local
-- criterion for flatness to lift flatness from the quotient.
/-- Lemma 10.128.1: let `R → S` be a local homomorphism of Noetherian local rings. If `R` is a
regular local ring, `S` is Cohen-Macaulay, and the dimension formula
`dim S = dim R + dim ((maximalIdeal R).Fiber S)`, equivalently
`dim S = dim R + dim (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))`, holds, then `R → S` is
flat. -/
theorem algebraMap_flat_of_isRegularLocalRing_of_cohenMacaulay_of_dimension_formula
    (hCM : Module.CohenMacaulay S S)
    (hdim : ringKrullDim S = ringKrullDim R + ringKrullDim ClosedFiber) :
    (algebraMap R S).Flat := sorry

end

/-! ### Lemma_10_128_2 (from Chap10) -/
universe u v

open RingTheory Sequence IsLocalRing

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsRegularLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
variable [IsLocalHom (algebraMap R S)]

/- Domain-style sampling pass.
* primary domain: local commutative algebra of flat local homomorphisms out of a regular local
  ring, detected by the image of a regular system of parameters;
* sampled owner declarations:
  `IsRegularSystemOfParameters`,
  `IsRegularSystemOfParameters.isRegular`,
  `IsRegularSystemOfParameters.isRegularLocalRing_quotient_parameterIdeal`,
  `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal`;
* best owner abstraction: the source-facing primitive datum is the chosen family
  `x : Fin d → maximalIdeal R` together with `hx : IsRegularSystemOfParameters x`; the list
  `List.ofFn fun i ↦ algebraMap R S (x i : R)` is only the bridge/view presenting the induced
  sequence in `S`, while the conclusion belongs on the canonical flatness owner `Module.Flat R S`.
* primitive data: the local map `R → S`, the regular-local owner on `R`, the Noetherian-local
  owner on `S`, the chosen regular system of parameters `x`, and regularity of its image in `S`;
* derived API: regularity of the underlying sequence in `R` from `hx.isRegular`, the regular-local
  prefix quotients from
  `IsRegularSystemOfParameters.isRegularLocalRing_quotient_parameterIdeal`, and the inductive
  flatness step furnished by `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal`.

Source/core/bridge triage:
* source-facing: Lemma `10.128.2` itself;
* core/canonical: `IsRegularSystemOfParameters`, `Sequence.IsRegular`, and `Module.Flat`;
* bridge/view: the `List.ofFn` presentation of the image sequence in `S`.
-/

-- Proof sketch: let `d = ringKrullDim R`, and write the chosen regular system of parameters as
-- `x₁, …, x_d`. Since `R / (x₁, …, x_d)` is a field, the final quotient of `S` is flat over the
-- final quotient of `R`. Then apply
-- `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal` inductively up the regular sequence,
-- using at each step that the next parameter is a nonzerodivisor on the corresponding quotient of
-- `S`.
/-- Lemma 10.128.2: let `R → S` be a local homomorphism of Noetherian local rings. If `R` is a
regular local ring and a regular system of parameters of length `d = ringKrullDim R` maps to a
regular sequence in `S`, then `S` is flat over `R`. -/
theorem flat_of_regularSystemOfParameters_image_isRegular
    {d : ℕ} (x : Fin d → maximalIdeal R)
    (hx : IsRegularSystemOfParameters x)
    (hreg : IsRegular S (List.ofFn fun i ↦ algebraMap R S (x i : R))) :
    Module.Flat R S := sorry

end

/-! ### Lemma_10_128_3 (from Chap10) -/
universe uR uS uM

open scoped TensorProduct

section

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
variable {f : R →+* S} [IsLocalHom f]
variable {M : Type uM} [AddCommGroup M] [Module S M]

-- Proof sketch: for a fixed stage `λ`, Remark `10.75.9` identifies
-- `Tor₁^{R_λ}(M_λ, R_λ / 𝔪_λ)` with the kernel of `𝔪_λ ⊗[R_λ] M_λ → M_λ`, so this Tor module is
-- finite over `S_λ`. Because `M` is flat over `R`, the corresponding kernel vanishes after
-- passing to the colimit, hence finitely many generators die at some larger stage `λ'`. Applying
-- Lemma `10.99.14` to the local base-change square supplied by the approximation then yields
-- flatness of `M_{λ'}` over `R_{λ'}`.
namespace DirectedLocalEssFinitePresentationModuleApproximation

/-- Lemma 10.128.3: for explicit local approximation data as in Lemma `10.127.13`, if `M` is flat
over `R`, then some stage module `M_λ` is flat over the corresponding source ring `R_λ`. -/
theorem exists_flat_stage_of_flat
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (hflat :
      let _ : Module R M := Module.compHom M f
      Module.Flat R M) :
    ∃ i : A.Λ, Module.Flat (A.RStage i) (A.moduleStage i) := sorry

end DirectedLocalEssFinitePresentationModuleApproximation

end

/-! ### Lemma_10_128_4 (from Chap10) -/
open IsLocalRing
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {M : Type w} {N : Type x}
variable [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/- Domain-style sampling for Lemma 10.128.4:
- primary domain: the local flatness criterion for finitely presented modules over a local
  homomorphism, with the closed-fiber injectivity hypothesis on the quotient map modulo the
  maximal ideal and a standard residue-field tensor reformulation;
- sampled owner declarations:
  `LinearMap.quotientMapByIdeal`,
  `TensorProduct.quotTensorEquivQuotSMul`,
  `injective_of_mod_maximalIdeal_injective`,
  `flat_quotient_of_mod_maximalIdeal_injective`;
- best owner abstraction: the source-facing closed-fiber map is the reduction map
  `LinearMap.quotientMapByIdeal (maximalIdeal R)`; the residue-field tensor formulation is only a
  bridge to this owner via `TensorProduct.quotTensorEquivQuotSMul`;
- primitive data: the local map `R → S`, the essentially finitely presented `R`-algebra structure
  on `S`, canonically exposed in Chapter 10 as
  `RingHom.EssFinitePresentation (algebraMap R S)`, the finitely presented `S`-modules `M` and
  `N`, the `R`-flatness of `N`, and the injectivity of the closed-fiber map of `u`;
- derived API: injectivity of `u` and `R`-flatness of the quotient by its image.

Source/core/bridge triage:
- `source-facing`: Lemma 10.128.4 itself, phrased with injectivity of
  `M / maximalIdeal R • M → N / maximalIdeal R • N`;
- `core/canonical`: `Function.Injective`, `Module.Flat`, and the Chapter 10 owner theorems
  `injective_of_mod_maximalIdeal_injective` and
  `flat_quotient_of_mod_maximalIdeal_injective`;
- `bridge/view`: the standard closed-fiber identification
  `(R ⧸ maximalIdeal R) ⊗[R] M ≃ M ⧸ maximalIdeal R • ⊤`, implemented by
  `TensorProduct.quotTensorEquivQuotSMul`, converts the source-facing hypothesis to the quotient
  criterion used by the core owner theorems.
-/

-- Proof sketch: use the canonical closed-fiber identification
-- `(R ⧸ maximalIdeal R) ⊗[R] M ≃ M / maximalIdeal R • M` to convert the source-facing residue-field
-- injectivity hypothesis into injectivity of the quotient reduction map
-- `M / maximalIdeal R • M → N / maximalIdeal R • N`. Then apply the owner theorems from Lemma
-- `10.99.1` to obtain injectivity of `u` and flatness of its quotient.
/-- Bridge theorem: injectivity after tensoring with the residue field implies injectivity of the
reduction map modulo `maximalIdeal R`, which is the canonical quotient criterion used by Lemma
`10.99.1`. -/
theorem injective_mod_maximalIdeal_of_lTensor_residueField_injective
    (u : M →ₗ[S] N)
    (hbar : Function.Injective ((u.restrictScalars R).lTensor (ResidueField R))) :
    Function.Injective ((u.restrictScalars R).quotientMapByIdeal (maximalIdeal R)) := by
  sorry

-- Proof sketch: apply the owner theorems from Lemma `10.99.1` directly to the closed-fiber map
-- modulo `maximalIdeal R`; the quotient by the `R`-linear range of `u.restrictScalars R` is
-- definitionally the same module as the quotient by the `S`-linear range of `u`, viewed by
-- restriction of scalars.
/-- Lemma 10.128.4: for a local homomorphism `R → S` with `S` essentially of finite presentation
over `R`, if `M` and `N` are finitely presented `S`-modules, `N` is flat over `R`, and the
induced map `M / maximalIdeal R • M → N / maximalIdeal R • N` is injective, then `u` is injective
and its quotient is flat over `R`. -/
theorem injective_and_flat_quotient_of_mod_maximalIdeal_injective
    [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Module.FinitePresentation S M] [Module.FinitePresentation S N] [Module.Flat R N]
    (hess : RingHom.EssFinitePresentation (algebraMap R S)) (u : M →ₗ[S] N)
    (hmod : Function.Injective ((u.restrictScalars R).quotientMapByIdeal (maximalIdeal R))) :
    Function.Injective u ∧ Module.Flat R (N ⧸ LinearMap.range u) := by
  have hess' : Algebra.EssFinitePresentation R S :=
    RingHom.essFinitePresentation_algebraMap.mp hess
  letI := hess'
  have hu : Function.Injective (u.restrictScalars R) :=
    injective_of_mod_maximalIdeal_injective (u.restrictScalars R) hmod
  have hflat : Module.Flat R (N ⧸ LinearMap.range (u.restrictScalars R)) :=
    flat_quotient_of_mod_maximalIdeal_injective (u.restrictScalars R) hmod
  refine ⟨hu, ?_⟩
  simpa [LinearMap.range_restrictScalars] using hflat

-- Proof sketch: bridge the residue-field injectivity hypothesis to injectivity of the closed-fiber
-- quotient map, then apply Lemma `10.128.4` in its source-facing quotient form.
/-- Companion reformulation of Lemma 10.128.4: the residue-field tensor criterion implies the
source-facing closed-fiber injectivity hypothesis, hence the same injectivity and flat-quotient
conclusion. -/
theorem injective_and_flat_quotient_of_lTensor_residueField_injective
    [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Module.FinitePresentation S M] [Module.FinitePresentation S N] [Module.Flat R N]
    (hess : RingHom.EssFinitePresentation (algebraMap R S)) (u : M →ₗ[S] N)
    (hbar : Function.Injective ((u.restrictScalars R).lTensor (ResidueField R))) :
    Function.Injective u ∧ Module.Flat R (N ⧸ LinearMap.range u) := by
  exact
    injective_and_flat_quotient_of_mod_maximalIdeal_injective hess u
      (injective_mod_maximalIdeal_of_lTensor_residueField_injective u hbar)

end

/-! ### Lemma_10_128_5 (from Chap10) -/
open IsLocalRing
open scoped nonZeroDivisors

universe u v w

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
variable [IsLocalHom (algebraMap R S)] [Module.Flat R S]

local notation "𝔪S" => Ideal.map (algebraMap R S) (maximalIdeal R)

/- Domain-style sampling for Lemma 10.128.5:
- primary domain: the single-element form of the local flatness criterion for an essentially
  finitely presented flat local map, where regularity on the closed fiber is transported to
  regularity in the total ring together with flatness of the quotient;
- sampled owner declarations:
  `RingHom.EssFinitePresentation`,
  `injective_and_flat_quotient_of_mod_maximalIdeal_injective`,
  `Ideal.range_mul'`,
  `isRegular_iff_mem_nonZeroDivisors`;
- best owner abstraction: the core owner is the linear-map theorem
  `injective_and_flat_quotient_of_mod_maximalIdeal_injective`; the present lemma is its
  `source-facing` specialization to multiplication by a single element;
- primitive data: the local map `R → S`, the essential finite presentation hypothesis `hess`, the
  element `f : S`, and regularity of its image in the closed fiber;
- derived API: flatness of `S / fS` over `R` and regularity of `f` in `S`.

Source/core/bridge triage:
- `source-facing`: the Stacks single-element statement;
- `core/canonical`: `injective_and_flat_quotient_of_mod_maximalIdeal_injective`;
- `bridge/view`: the `S`-linear endomorphism `LinearMap.mul S S f` and the identification
  `LinearMap.range (LinearMap.mul S S f) = Ideal.span {f}`.
-/

-- Proof sketch: apply Lemma `10.128.4` to the `S`-linear map `S →ₗ[S] S` given by multiplication
-- by `f`. The hypothesis that `f` is a nonzerodivisor on the closed fiber gives injectivity of
-- the induced map modulo `maximalIdeal R`. Lemma `10.128.4` then yields injectivity of
-- multiplication by `f` on `S`, i.e. `f` is regular in `S`, and flatness of its cokernel, whose
-- range ideal is canonically `fS = Ideal.span {f}`.
/-- Lemma 10.128.5: for a flat essentially finitely presented local map `R → S`, if `f ∈ S` is a
nonzerodivisor on the closed fiber `S / 𝔪_R S`, then the quotient `S / fS` is flat over `R` and
`f` is a nonzerodivisor in `S`. -/
theorem flat_quotient_and_isRegular_of_isRegular_closedFiber_of_essFinitePresentation
    (hess : (algebraMap R S).EssFinitePresentation) (f : S)
    (hbar : IsRegular (Ideal.Quotient.mk 𝔪S f)) :
    Module.Flat R (S ⧸ Ideal.span ({f} : Set S)) ∧ IsRegular f := by
  let u : S →ₗ[S] S := LinearMap.mul S S f
  have hf : Ideal.Quotient.mk 𝔪S f ∈ nonZeroDivisors (S ⧸ 𝔪S) :=
    isRegular_iff_mem_nonZeroDivisors.mp hbar
  have hmod : Function.Injective ((u.restrictScalars R).quotientMapByIdeal (maximalIdeal R)) := by
    intro x y hxy
    refine Quotient.inductionOn₂' x y ?_ hxy
    intro a b hab
    have hab' : (Submodule.Quotient.mk (f * a) : S ⧸ maximalIdeal R • (⊤ : Submodule R S)) =
        Submodule.Quotient.mk (f * b) := by
      simpa [LinearMap.quotientMapByIdeal, u] using hab
    have hab'' : f * a - f * b ∈ maximalIdeal R • (⊤ : Submodule R S) :=
      (Submodule.Quotient.eq _).1 hab'
    apply (Submodule.Quotient.eq _).2
    rw [Ideal.smul_top_eq_map] at hab'' ⊢
    change f * a - f * b ∈ 𝔪S at hab''
    change a - b ∈ 𝔪S
    have hmul : f * (a - b) ∈ 𝔪S := by
      simpa [mul_sub] using hab''
    have hzero : Ideal.Quotient.mk 𝔪S (a - b) = 0 := by
      rw [mem_nonZeroDivisors_iff_left] at hf
      exact hf (Ideal.Quotient.mk 𝔪S (a - b)) <| by
        rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
        simpa [mul_comm] using hmul
    exact (Ideal.Quotient.eq_zero_iff_mem).1 hzero
  obtain ⟨hinj, hflat⟩ :=
    injective_and_flat_quotient_of_mod_maximalIdeal_injective hess u hmod
  have hrange : LinearMap.range u = Ideal.span ({f} : Set S) := by
    simp [u]
  rw [hrange] at hflat
  refine ⟨hflat, ?_⟩
  rw [isRegular_iff_mem_nonZeroDivisors, mem_nonZeroDivisors_iff_left]
  intro x hx
  exact hinj <| by simpa [u] using hx

end

/-! ### Lemma_10_128_6 (from Chap10) -/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v

open IsLocalRing RingTheory

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
variable [IsLocalHom (algebraMap R S)] [Module.Flat R S]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S

/- Domain-style sampling for Lemma 10.128.6:
- primary domain: regular sequences on the canonical closed fiber of a flat local map, together
  with flatness of the successive quotient rings over the base;
- sampled owner declarations:
  `Ideal.Fiber`,
  `RingTheory.Sequence.IsRegular`,
  `RingTheory.Sequence.isRegular_cons_iff'`,
  `flat_quotient_and_isRegular_of_isRegular_closedFiber_of_essFinitePresentation`,
  `isRegular_and_flat_quotient_take_of_closedFiber_isRegular`;
- best owner abstraction: the core owner is the regular-sequence predicate
  `RingTheory.Sequence.IsRegular` on the canonical fiber ring
  `ClosedFiber = Ideal.Fiber (maximalIdeal R) S`, while the quotient-by-prefix rings
  `S ⧸ Ideal.ofList (fs.take (i + 1))` are derived bridge data;
- primitive data: the flat local map `R → S`, the essential finite presentation hypothesis
  `RingHom.EssFinitePresentation (algebraMap R S)`, and regularity of the image sequence in the
  canonical closed fiber under `algebraMap S ClosedFiber`;
- derived API: regularity of `fs` in `S` and flatness of the nonempty prefix quotients over `R`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma for sequences regular on the closed fiber;
- `core/canonical`: `Ideal.Fiber`, `RingTheory.Sequence.IsRegular`,
  `RingHom.EssFinitePresentation`, and `Module.Flat`;
- `bridge/view`: the quotient presentation
  `S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)` of `ClosedFiber`, together with the explicit
  quotient rings `S ⧸ Ideal.ofList (fs.take (i + 1))`.
-/

-- Proof sketch: argue by induction on `fs`. The base step is trivial. For the inductive step,
-- transport regularity of the head along the canonical quotient view
-- `ClosedFiber ≃ₐ[R] S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)` and apply Lemma `10.128.5`
-- to get that the head is regular in `S` and that the first quotient is flat over `R`. Then pass
-- to the quotient by the head and apply the induction hypothesis to the tail sequence.
/-- Lemma 10.128.6: for a flat essentially finitely presented local homomorphism `R → S`, if the
images of a finite sequence `fs` in the canonical closed fiber
`ClosedFiber = (maximalIdeal R).Fiber S`, equivalently in the quotient
`S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`, form a regular sequence, then `fs` is a
regular sequence in `S`, and each quotient by a nonempty initial segment of `fs` is flat over
`R`. -/
theorem isRegular_and_flat_quotient_take_of_closedFiber_isRegular_of_essFinitePresentation
    (hess : RingHom.EssFinitePresentation (algebraMap R S)) (fs : List S)
    (hfs : Sequence.IsRegular ClosedFiber (fs.map (algebraMap S ClosedFiber))) :
    Sequence.IsRegular S fs ∧
      ∀ i : Fin fs.length, Module.Flat R (S ⧸ Ideal.ofList (fs.take (i + 1))) := sorry

end

/-! ### Lemma_10_128_7 (from Chap10) -/
open CategoryTheory.Limits

universe u v

section

variable {R : Type u} {S : Type v} {M : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.FinitePresentation S M]

/- Domain-style sampling for the approximation-based flatness criterion:
- primary domain: flatness of a finitely presented module over an essentially finitely presented
  local map, detected from a quotient-flatness hypothesis and a `Tor₁` vanishing hypothesis;
- sampled owner declarations of the same kind:
  `RingHom.EssFinitePresentation`,
  `DirectedLocalEssFinitePresentationModuleApproximation`,
  `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal`,
  `Tor₁[R](M, N)`;
- best owner abstraction: the source-facing theorem here still concludes in the canonical owner
  `Module.Flat`, and its homological hypothesis should reuse the chapter owner notation
  `Tor₁[R](M, R ⧸ I)` rather than a raw derived-functor term;
- primitive data: the local map `R → S`, the essentially finitely presented hypothesis, the
  finitely presented `S`-module `M`, the proper ideal `I`, the vanishing of `Tor₁^R(M, R / I)`,
  and flatness of `M / IM` over `R / I`;
- derived API: flatness of `M` over `R`.

Source/core/bridge triage:
- `source-facing`: Lemma 10.128.7 itself;
- `core/canonical`: `Module.Flat`, `RingHom.EssFinitePresentation`, and the chapter owner notation
  `Tor₁[R](M, N)`;
- `bridge/view`: the directed approximation owner
  `DirectedLocalEssFinitePresentationModuleApproximation` and the stagewise descent/ascent lemmas
  `10.127.13`, `10.128.3`, `10.99.12`, and `10.99.10`, which belong to the proof route rather
  than to the public statement.
-/

-- Proof sketch: use Lemma `10.127.13` to approximate the local map `R → S` and the finitely
-- presented `S`-module `M` by finite type stage data. Descend flatness of `M / IM` to a stage via
-- Lemma `10.128.3`, then use finite generation of the stage `Tor₁` module together with the
-- vanishing of `Tor₁^R(M, R / I)` and the surjectivity-up-to-localization statement from
-- Lemma `10.99.12` to force stagewise vanishing of `Tor₁`. Finally apply the variant of the local
-- criterion from Lemma `10.99.10` at that stage and pass back to the limit.
/-- Lemma 10.128.7: let `R → S` be a local homomorphism of local rings, let `I ≠ R` be an ideal of
`R`, and let `M` be an `S`-module. If `S` is essentially of finite presentation over `R`, `M` is
of finite presentation over `S`, `Tor₁^R(M, R / I)` vanishes, and `M / IM` is flat over `R / I`,
then `M` is flat over `R`. -/
theorem flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal_of_essFinitePresentation
    (hess : (algebraMap R S).EssFinitePresentation)
    (I : Ideal R) (hI : I ≠ ⊤)
    (hTor : IsZero (Tor₁[R](M, R ⧸ I)))
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))) :
    Module.Flat R M := sorry

end

/-! ### Lemma_10_128_8_Crit_re_de_platitude_par_fibres (from Chap10) -/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

open IsLocalRing
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {S' : Type w} {M : Type x}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
variable [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
variable [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
variable [AddCommGroup M] [Module S M] [Module S' M] [Module R M]
variable [IsScalarTower S S' M] [IsScalarTower R S M] [IsScalarTower R S' M]
variable [Module.FinitePresentation S' M]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S
local notation "ClosedFiberModule" => ClosedFiber ⊗[S] M

/- Domain-style sampling for the fiberwise flatness criterion with essentially finitely presented
local maps:
* primary domain: local commutative algebra of flatness along local ring maps, with closed fibers
  carried by the canonical owner `Ideal.Fiber`;
* sampled owner declarations:
  `Ideal.Fiber`,
  `RingHom.EssFinitePresentation`,
  `flat_over_middleRing_of_flat_closedFiber_and_flat_over_base`,
  `algebraMap_flat_of_flat_of_faithfullyFlat`;
* best owner abstraction: the closed fiber should live on the canonical owners
  `ClosedFiber = Ideal.Fiber (maximalIdeal R) S` and `ClosedFiberModule = ClosedFiber ⊗[S] M`,
  while the conclusions belong on `Module.Flat S M` and `(algebraMap R S).Flat`; the quotient
  models `S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)` and
  `M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))` are only bridge
  views.

Primitive data vs. derived API:
* primitive data: the local diagram `R → S → S'`, essential finite presentation of `R → S` and
  `R → S'`, a finitely presented `S'`-module `M`, flatness of the canonical closed-fiber module
  `ClosedFiberModule` over `ClosedFiber`, and flatness of `M` over `R`;
* derived API: flatness of `M` over `S`, and with the extra source-facing nontriviality hypothesis,
  flatness of the local map `R → S`.

Source/core/bridge triage:
* `source-facing`: the two clauses of Lemma `10.128.8`;
* `core/canonical`: `RingHom.EssFinitePresentation`, `Ideal.Fiber`, `Module.Flat`, and
  `RingHom.Flat`;
* `bridge/view`: the quotient presentations of the closed fiber ring and module.
-/

-- Proof sketch: approximate the two essentially finitely presented local maps `R → S` and
-- `R → S'` together with the finitely presented `S'`-module `M` by a sufficiently large Noetherian
-- stage using Lemmas `10.127.11` and `10.127.13`. Lemma `10.128.3` descends the flatness of `M`
-- over `R` and of the canonical closed fiber `ClosedFiberModule` over `ClosedFiber` to that stage,
-- where Lemma `10.99.15` applies. Base-changing the resulting stagewise flatness statement back to
-- `R → S → S'` yields flatness of the local map `R → S`.
/-- Lemma 10.128.8 (Critère de platitude par fibres) (1): for local rings `R`, `S`, `S'` and local
homomorphisms `R → S → S'`, assume `R → S` and `R → S'` are essentially of finite presentation,
`M` is a nonzero finitely presented `S'`-module, the canonical closed fiber
`ClosedFiberModule = ((maximalIdeal R).Fiber S) ⊗[S] M`, equivalently
`M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))`, is flat over
`ClosedFiber = (maximalIdeal R).Fiber S`, equivalently
`S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`, and `M` is flat over `R`. Then `R → S` is
flat. -/
theorem algebraMap_flat_of_essFinitePresentation_of_flat_closedFiber_and_flat_over_base
    (hRS : RingHom.EssFinitePresentation (algebraMap R S))
    (hRS' : RingHom.EssFinitePresentation (algebraMap R S')) [Nontrivial M]
    (hflat_closedFiber : Module.Flat ClosedFiber ClosedFiberModule) (hflat_R : Module.Flat R M) :
    (algebraMap R S).Flat := sorry

-- Proof sketch: use the same Noetherian approximation argument as in clause (1). At a large
-- enough stage the data satisfy the Noetherian fiberwise flatness criterion of Lemma `10.99.15`,
-- which gives flatness of the stage module over the stage middle ring. Flatness is preserved under
-- base change along the colimit identification, so the original `S'`-module `M` is flat over `S`.
/-- Lemma 10.128.8 (Critère de platitude par fibres) (2): under the same hypotheses, the
`S'`-module `M` is flat over `S`. Here the fiberwise hypothesis is expressed on the canonical
closed-fiber owner `ClosedFiberModule = ((maximalIdeal R).Fiber S) ⊗[S] M` over
`ClosedFiber = (maximalIdeal R).Fiber S`, not on a separate quotient-packaged wrapper. -/
theorem flat_over_middleRing_of_essFinitePresentation_of_flat_closedFiber_and_flat_over_base
    (hRS : RingHom.EssFinitePresentation (algebraMap R S))
    (hRS' : RingHom.EssFinitePresentation (algebraMap R S'))
    (hflat_closedFiber : Module.Flat ClosedFiber ClosedFiberModule) (hflat_R : Module.Flat R M) :
    Module.Flat S M := sorry

end

/-! ### Lemma_10_128_9 (from Chap10) -/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

open IsLocalRing
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {S' : Type w} {M : Type x}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
variable [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
variable [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
variable [AddCommGroup M] [Module S' M] [Module.FinitePresentation S' M]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S
local notation "ClosedFiberModule" => ClosedFiber ⊗[S] RestrictScalars S S' M

/- Domain-style sampling for Lemma 10.128.9:
* primary domain: local commutative algebra of essential finite presentation and fiberwise
  flatness along a local tower `R → S → S'`;
* sampled owner declarations:
  `Algebra.EssFiniteType`,
  `Algebra.EssFinitePresentation`,
  `Ideal.Fiber`,
  `algebraMap_flat_of_essFinitePresentation_of_flat_closedFiber_and_flat_over_base`,
  `flat_over_middleRing_of_essFinitePresentation_of_flat_closedFiber_and_flat_over_base`;
* best owner abstraction: the new source-facing content is the upgrade
  `Algebra.EssFiniteType R S ⟶ Algebra.EssFinitePresentation R S` under fiberwise flatness
  hypotheses, while the closed fiber itself should live on the canonical owners
  `ClosedFiber = Ideal.Fiber (maximalIdeal R) S` and
  `ClosedFiberModule = ClosedFiber ⊗[S] RestrictScalars S S' M`.

Primitive data vs. derived API:
* primitive data: the local tower `R → S → S'`, the essential finite type hypothesis on `R → S`,
  the essential finite presentation hypothesis on `R → S'`, the finitely presented `S'`-module
  `M`, flatness of `ClosedFiberModule` over `ClosedFiber`, and flatness of `M` over `R` after
  restriction of scalars along `R → S'`;
* derived API: essential finite presentation of `R → S`, then the flatness conclusions from
  Lemma `10.128.8`.

Source/core/bridge triage:
* `source-facing`: the first theorem below, which is the extra Stacks content of Lemma `10.128.9`;
* `core/canonical`: `Algebra.EssFiniteType`, `Algebra.EssFinitePresentation`, `Ideal.Fiber`,
  `Module.Flat`, and `RingHom.Flat`;
* `bridge/view`: the quotient presentation
  `M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))` of the canonical
  closed-fiber module after restricting scalars from `S'` to `S`.
-/

-- Proof sketch: write the essentially finite type local algebra `S` as a localization of a finite
-- type `R`-algebra. Choose a finitely generated subideal cutting out the same closed fiber modulo
-- `maximalIdeal R`, apply Lemma `10.128.8` to each finite-presentation approximation `R → B / J' →
-- S'`, and use Lemma `10.128.4` to show two such approximations coincide once they agree modulo the
-- maximal ideal. Hence the defining ideal is finitely generated, so `R → S` is essentially of
-- finite presentation.
/-- Lemma 10.128.9 (1): if `R → S → S'` are local ring homomorphisms, `R → S'` is essentially of
finite presentation, `R → S` is essentially of finite type, `M` is a nonzero finitely presented
`S'`-module, the canonical closed-fiber module
`ClosedFiberModule = ((maximalIdeal R).Fiber S) ⊗[S] M`, equivalently `M / 𝔪_R M`, is flat over
the canonical closed-fiber ring `ClosedFiber = (maximalIdeal R).Fiber S`, equivalently
`S / 𝔪_R S`, and `M` is flat over `R`, then `R → S` is essentially of finite presentation. -/
theorem middleRing_essFinitePresentation_of_essFiniteType_of_flat_closedFiber_and_flat_over_base
    (hM : Nontrivial M) (hRS : Algebra.EssFiniteType R S)
    (hRS' : Algebra.EssFinitePresentation R S')
    (hflat_closedFiber : Module.Flat ClosedFiber ClosedFiberModule)
    (hflat_R : Module.Flat R (RestrictScalars R S' M)) :
    Algebra.EssFinitePresentation R S := sorry

-- Proof sketch: first obtain that `R → S` is essentially of finite presentation from the previous
-- theorem. Then apply Lemma `10.128.8 (1)` to the local maps `R → S → S'` and the module `M`.
/-- Under the hypotheses of Lemma 10.128.9, the local homomorphism `R → S` is flat. -/
theorem algebraMap_flat_of_essFiniteType_of_flat_closedFiber_and_flat_over_base
    (hM : Nontrivial M) (hRS : Algebra.EssFiniteType R S)
    (hRS' : Algebra.EssFinitePresentation R S')
    (hflat_closedFiber : Module.Flat ClosedFiber ClosedFiberModule)
    (hflat_R : Module.Flat R (RestrictScalars R S' M)) :
    (algebraMap R S).Flat := by
  letI : Nontrivial M := hM
  letI : Module S M := Module.compHom M (algebraMap S S')
  letI : Module R M := Module.compHom M (algebraMap R S')
  letI : IsScalarTower S S' M := IsScalarTower.of_algebraMap_smul fun s m ↦ by
    rfl
  letI : IsScalarTower R S' M := IsScalarTower.of_algebraMap_smul fun r m ↦ by
    rfl
  letI : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul fun r m ↦ by
    simpa [Module.compHom, RingHom.comp_apply] using
      (congrArg (fun f : R →+* S' ↦ f r • m) (IsScalarTower.algebraMap_eq R S S')).symm
  have hmid : Algebra.EssFinitePresentation R S :=
    middleRing_essFinitePresentation_of_essFiniteType_of_flat_closedFiber_and_flat_over_base
      hM hRS hRS' hflat_closedFiber hflat_R
  have hflat_closedFiber' : Module.Flat ClosedFiber (ClosedFiber ⊗[S] M) := by
    simpa using hflat_closedFiber
  have hflat_R' : Module.Flat R M := by
    simpa using hflat_R
  exact
    algebraMap_flat_of_essFinitePresentation_of_flat_closedFiber_and_flat_over_base
      (RingHom.essFinitePresentation_algebraMap.mpr hmid)
      (RingHom.essFinitePresentation_algebraMap.mpr hRS')
      hflat_closedFiber'
      hflat_R'

-- Proof sketch: if `M` is nontrivial, combine the essential finite presentation statement proved
-- above with Lemma `10.128.8 (2)`. If `M` is subsingleton, then `M` is flat over every ring, so
-- the conclusion is immediate.
/-- Under the hypotheses of Lemma 10.128.9, the `S'`-module `M` is flat over `S`. -/
theorem flat_over_middleRing_of_essFiniteType_of_flat_closedFiber_and_flat_over_base
    (hRS : Algebra.EssFiniteType R S) (hRS' : Algebra.EssFinitePresentation R S')
    (hflat_closedFiber : Module.Flat ClosedFiber ClosedFiberModule)
    (hflat_R : Module.Flat R (RestrictScalars R S' M)) :
    Module.Flat S (RestrictScalars S S' M) := by
  obtain hM | hM := subsingleton_or_nontrivial M
  · letI : Subsingleton (RestrictScalars S S' M) := by
      change Subsingleton M
      exact hM
    infer_instance
  · letI : Nontrivial M := hM
    letI : Module S M := Module.compHom M (algebraMap S S')
    letI : Module R M := Module.compHom M (algebraMap R S')
    letI : IsScalarTower S S' M := IsScalarTower.of_algebraMap_smul fun s m ↦ by
      rfl
    letI : IsScalarTower R S' M := IsScalarTower.of_algebraMap_smul fun r m ↦ by
      rfl
    letI : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul fun r m ↦ by
      simpa [Module.compHom, RingHom.comp_apply] using
        (congrArg (fun f : R →+* S' ↦ f r • m) (IsScalarTower.algebraMap_eq R S S')).symm
    have hmid : Algebra.EssFinitePresentation R S :=
      middleRing_essFinitePresentation_of_essFiniteType_of_flat_closedFiber_and_flat_over_base
        hM hRS hRS' hflat_closedFiber hflat_R
    have hflat_closedFiber' : Module.Flat ClosedFiber (ClosedFiber ⊗[S] M) := by
      simpa using hflat_closedFiber
    have hflat_R' : Module.Flat R M := by
      simpa using hflat_R
    have hflat_S : Module.Flat S M :=
      flat_over_middleRing_of_essFinitePresentation_of_flat_closedFiber_and_flat_over_base
        (RingHom.essFinitePresentation_algebraMap.mpr hmid)
        (RingHom.essFinitePresentation_algebraMap.mpr hRS')
        hflat_closedFiber'
        hflat_R'
    simpa using hflat_S

end

/-! ### Lemma_10_128_10_Crit_re_de_platitude_par_fibres_locally_nilpotent_case (from Chap10) -/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

open scoped TensorProduct

universe u v w x y

section

variable {R : Type u} {S : Type v} {S' : Type w} {M : Type x}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
variable {I : Ideal R}
variable [AddCommGroup M] [Module S' M]
variable [Algebra.FiniteType R S] [Algebra.FinitePresentation R S'] [Module.FinitePresentation S' M]

local notation "IS" => Ideal.map (algebraMap R S) I
local notation "FiberRing" => S ⧸ IS
local notation "FiberModule" => FiberRing ⊗[S] RestrictScalars S S' M

/- Domain-style sampling for the locally nilpotent fiberwise flatness criterion:
* primary domain: fiberwise flatness for finitely presented modules over a locally nilpotent
  thickening, with fiber hypotheses carried by the canonical fiber module owner;
* sampled owner declarations of the same kind:
  `Ideal.qoutMapEquivTensorQout`,
  `Definition_10_65_2.mem_relativeAssassin_iff_fiber`,
  `flat_over_middleRing_of_essFinitePresentation_of_flat_closedFiber_and_flat_over_base`,
  `middleRing_essFinitePresentation_of_essFiniteType_of_flat_closedFiber_and_flat_over_base`;
* best owner abstraction: the primitive fiber hypothesis should live on
  `FiberModule = FiberRing ⊗[S] M`, where `FiberRing = S ⧸ Ideal.map (algebraMap R S) I` is the
  quotient presentation of the arbitrary-ideal fiber ring, equivalently
  `(R ⧸ I) ⊗[R] S` via `Ideal.qoutMapEquivTensorQout`; the quotient module
  `M ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S M))` is only a bridge view.

Primitive data vs. derived API:
* primitive data: the locally nilpotent ideal `I`, the algebra tower `R → S → S'`, the finite-type
  and finite-presentation hypotheses, the finitely presented `S'`-module `M`, flatness of the
  canonical fiber module `FiberModule` over `FiberRing`, and flatness of the restricted
  `R`-module `RestrictScalars R S' M`;
* derived API: flatness of the restricted `S`-module `RestrictScalars S S' M`, then flatness and
  essential finite presentation of the localizations `S_q` over `R`.

Source/core/bridge triage:
* `source-facing`: the three theorems below, which are the locally nilpotent variant of the
  fiberwise flatness criterion;
* `core/canonical`: the fiber module owner `FiberModule`, `Module.Flat`, and
  `RingHom.EssFinitePresentation`;
* `bridge/view`: the quotient models of the fiber ring and fiber module modulo `IS`.
-/

-- Proof sketch: first pass from the locally nilpotent ideal `I` to the closed fibers over the
-- primes `p = q ∩ R`; since `I ⊆ p`, base change of the canonical fiber-flatness hypothesis on
-- `FiberModule` yields flatness of the closed fiber over `p`. Apply the local fiberwise flatness
-- criterion of Lemma `10.128.9` to `R_p → S_q → S'_{q'}` for primes `q'` of `S'` above `q`,
-- obtaining flatness of the localized module over `S_q`. Then use the prime-local criterion for
-- flatness to conclude `RestrictScalars S S' M` is flat over `S`.
/-- Lemma 10.128.10 (Critère de platitude par fibres: locally nilpotent case): if `I` is a locally
nilpotent ideal of `R`, `R → S` is of finite type, `R → S'` is of finite presentation, `M` is a
finitely presented `S'`-module, the canonical fiber module
`FiberModule = (S ⧸ Ideal.map (algebraMap R S) I) ⊗[S] M`,
equivalently `M ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S M))`, is flat over the
canonical fiber ring `FiberRing = S ⧸ Ideal.map (algebraMap R S) I`, equivalently
`(R ⧸ I) ⊗[R] S`, and the restricted `R`-module `RestrictScalars R S' M` is flat over `R`, then
the restricted `S`-module `RestrictScalars S S' M` is flat over `S`. -/
theorem flat_over_middleRing_of_locallyNilpotent_of_flat_over_base_and_flat_mod_extended_ideal
    (hI : I.IsLocallyNilpotent)
    (hflat_fiber : Module.Flat FiberRing FiberModule)
    (hflat_R : Module.Flat R (RestrictScalars R S' M)) :
    Module.Flat S (RestrictScalars S S' M) := sorry

-- Proof sketch: choose a prime `q'` of `S'` above `q` using the nontrivial fiber hypothesis and
-- Lemma `10.18.6`. For `p = q ∩ R`, the locally nilpotent hypothesis gives `I ⊆ p`, so base
-- change of `hflat_fiber` gives flatness of the canonical fiber over `p`. Apply Lemma `10.128.9`
-- to the local diagram `R_p → S_q → S'_{q'}` and the localized module `M_{q'}`.
/-- If the residue-field fiber `(RestrictScalars S S' M) ⊗[S] κ(q)` is nontrivial, then the
localization `S_q` is flat over `R`. -/
theorem localized_flat_of_locallyNilpotent_of_nontrivial_fiber
    (hI : I.IsLocallyNilpotent)
    (hflat_fiber : Module.Flat FiberRing FiberModule)
    (hflat_R : Module.Flat R (RestrictScalars R S' M))
    (q : PrimeSpectrum S)
    (hq : Nontrivial ((RestrictScalars S S' M) ⊗[S] q.asIdeal.ResidueField)) :
    (algebraMap R (Localization.AtPrime q.asIdeal)).Flat := sorry

-- Proof sketch: with the same localization setup as above, Lemma `10.128.9` shows that the local
-- ring map `R_p → S_q` is essentially of finite presentation. Interpreting this as a statement
-- about the localized `R`-algebra `S_q` gives the claimed essential finite presentation.
/-- If the residue-field fiber `(RestrictScalars S S' M) ⊗[S] κ(q)` is nontrivial, then the
localization `S_q` is essentially of finite presentation over `R`. -/
theorem localized_essFinitePresentation_of_locallyNilpotent_of_nontrivial_fiber
    (hI : I.IsLocallyNilpotent)
    (hflat_fiber : Module.Flat FiberRing FiberModule)
    (hflat_R : Module.Flat R (RestrictScalars R S' M))
    (q : PrimeSpectrum S)
    (hq : Nontrivial ((RestrictScalars S S' M) ⊗[S] q.asIdeal.ResidueField)) :
    RingHom.EssFinitePresentation (algebraMap R (Localization.AtPrime q.asIdeal)) := sorry

end

/-! ### Lemma_10_128_10_Critère_de_platitude_par_fibres_locally_nilpotent_case (from Chap10) -/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

open scoped TensorProduct

universe u v w x y

section

variable {R : Type u} {S : Type v} {S' : Type w} {M : Type x}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
variable {I : Ideal R}
variable [AddCommGroup M] [Module S' M]
variable [Algebra.FiniteType R S] [Algebra.FinitePresentation R S'] [Module.FinitePresentation S' M]

local notation "IS" => Ideal.map (algebraMap R S) I
local notation "FiberRing" => S ⧸ IS
local notation "FiberModule" => FiberRing ⊗[S] RestrictScalars S S' M

/- Domain-style sampling for the locally nilpotent fiberwise flatness criterion:
* primary domain: fiberwise flatness for finitely presented modules over a locally nilpotent
  thickening, with fiber hypotheses carried by the canonical fiber module owner;
* sampled owner declarations of the same kind:
  `Ideal.qoutMapEquivTensorQout`,
  `Definition_10_65_2.mem_relativeAssassin_iff_fiber`,
  `flat_over_middleRing_of_essFinitePresentation_of_flat_closedFiber_and_flat_over_base`,
  `middleRing_essFinitePresentation_of_essFiniteType_of_flat_closedFiber_and_flat_over_base`;
* best owner abstraction: the primitive fiber hypothesis should live on
  `FiberModule = FiberRing ⊗[S] M`, where `FiberRing = S ⧸ Ideal.map (algebraMap R S) I` is the
  quotient presentation of the arbitrary-ideal fiber ring, equivalently
  `(R ⧸ I) ⊗[R] S` via `Ideal.qoutMapEquivTensorQout`; the quotient module
  `M ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S M))` is only a bridge view.

Primitive data vs. derived API:
* primitive data: the locally nilpotent ideal `I`, the algebra tower `R → S → S'`, the finite-type
  and finite-presentation hypotheses, the finitely presented `S'`-module `M`, flatness of the
  canonical fiber module `FiberModule` over `FiberRing`, and flatness of the restricted
  `R`-module `RestrictScalars R S' M`;
* derived API: flatness of the restricted `S`-module `RestrictScalars S S' M`, then flatness and
  essential finite presentation of the localizations `S_q` over `R`.

Source/core/bridge triage:
* `source-facing`: the three theorems below, which are the locally nilpotent variant of the
  fiberwise flatness criterion;
* `core/canonical`: the fiber module owner `FiberModule`, `Module.Flat`, and
  `RingHom.EssFinitePresentation`;
* `bridge/view`: the quotient models of the fiber ring and fiber module modulo `IS`.
-/

-- Proof sketch: first pass from the locally nilpotent ideal `I` to the closed fibers over the
-- primes `p = q ∩ R`; since `I ⊆ p`, base change of the canonical fiber-flatness hypothesis on
-- `FiberModule` yields flatness of the closed fiber over `p`. Apply the local fiberwise flatness
-- criterion of Lemma `10.128.9` to `R_p → S_q → S'_{q'}` for primes `q'` of `S'` above `q`,
-- obtaining flatness of the localized module over `S_q`. Then use the prime-local criterion for
-- flatness to conclude `RestrictScalars S S' M` is flat over `S`.
/-- Lemma 10.128.10 (Critère de platitude par fibres: locally nilpotent case): if `I` is a locally
nilpotent ideal of `R`, `R → S` is of finite type, `R → S'` is of finite presentation, `M` is a
finitely presented `S'`-module, the canonical fiber module
`FiberModule = (S ⧸ Ideal.map (algebraMap R S) I) ⊗[S] M`,
equivalently `M ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S M))`, is flat over the
canonical fiber ring `FiberRing = S ⧸ Ideal.map (algebraMap R S) I`, equivalently
`(R ⧸ I) ⊗[R] S`, and the restricted `R`-module `RestrictScalars R S' M` is flat over `R`, then
the restricted `S`-module `RestrictScalars S S' M` is flat over `S`. -/
theorem flat_over_middleRing_of_locallyNilpotent_of_flat_over_base_and_flat_mod_extended_ideal
    (hI : I.IsLocallyNilpotent)
    (hflat_fiber : Module.Flat FiberRing FiberModule)
    (hflat_R : Module.Flat R (RestrictScalars R S' M)) :
    Module.Flat S (RestrictScalars S S' M) := sorry

-- Proof sketch: choose a prime `q'` of `S'` above `q` using the nontrivial fiber hypothesis and
-- Lemma `10.18.6`. For `p = q ∩ R`, the locally nilpotent hypothesis gives `I ⊆ p`, so base
-- change of `hflat_fiber` gives flatness of the canonical fiber over `p`. Apply Lemma `10.128.9`
-- to the local diagram `R_p → S_q → S'_{q'}` and the localized module `M_{q'}`.
/-- If the residue-field fiber `(RestrictScalars S S' M) ⊗[S] κ(q)` is nontrivial, then the
localization `S_q` is flat over `R`. -/
theorem localized_flat_of_locallyNilpotent_of_nontrivial_fiber
    (hI : I.IsLocallyNilpotent)
    (hflat_fiber : Module.Flat FiberRing FiberModule)
    (hflat_R : Module.Flat R (RestrictScalars R S' M))
    (q : PrimeSpectrum S)
    (hq : Nontrivial ((RestrictScalars S S' M) ⊗[S] q.asIdeal.ResidueField)) :
    (algebraMap R (Localization.AtPrime q.asIdeal)).Flat := sorry

-- Proof sketch: with the same localization setup as above, Lemma `10.128.9` shows that the local
-- ring map `R_p → S_q` is essentially of finite presentation. Interpreting this as a statement
-- about the localized `R`-algebra `S_q` gives the claimed essential finite presentation.
/-- If the residue-field fiber `(RestrictScalars S S' M) ⊗[S] κ(q)` is nontrivial, then the
localization `S_q` is essentially of finite presentation over `R`. -/
theorem localized_essFinitePresentation_of_locallyNilpotent_of_nontrivial_fiber
    (hI : I.IsLocallyNilpotent)
    (hflat_fiber : Module.Flat FiberRing FiberModule)
    (hflat_R : Module.Flat R (RestrictScalars R S' M))
    (q : PrimeSpectrum S)
    (hq : Nontrivial ((RestrictScalars S S' M) ⊗[S] q.asIdeal.ResidueField)) :
    RingHom.EssFinitePresentation (algebraMap R (Localization.AtPrime q.asIdeal)) := sorry

end
