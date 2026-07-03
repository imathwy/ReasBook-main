import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_99_1 (from Chap10) -/
open IsLocalRing

section CriteriaForFlatness

universe u v w x

variable {R : Type u} {S : Type v} {M : Type w} {N : Type x}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
variable [AddCommGroup M] [Module R M] [Module.Flat R M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] [Module.Finite S N]

/-- Lemma 10.99.1 (1): if the reduction of an `R`-linear map `u : N → M` modulo the maximal ideal
of `R` is injective, then `u` itself is injective. -/
-- Proof sketch: prove by induction that the induced maps
-- `N / 𝔪^n N → M / 𝔪^n M` are injective for all `n`, using flatness of `M` to control the left
-- exactness of reduction modulo `𝔪^(n+1)` and the finite generation of `N` over the Noetherian
-- ring `S`; then use Krull intersection for the ideal `𝔪S` on `N`.
theorem injective_of_mod_maximalIdeal_injective
    (u : N →ₗ[R] M)
    (hmod : Function.Injective (u.quotientMapByIdeal (maximalIdeal R))) :
    Function.Injective u := sorry

/-- Lemma 10.99.1 (2): under the same hypothesis, the quotient of `M` by the image of `u` is flat
over `R`. -/
-- Proof sketch: use the injectivity from part (1) to obtain a short exact sequence
-- `0 → N → M → M / range u → 0`; then test flatness of the quotient against `R / I` for an
-- arbitrary ideal `I`, reduce the needed injectivity of `N / IN → M / IM` to part (1) over the
-- local homomorphism `R / I → S / IS`, and conclude by the Tor criterion for flatness.
theorem flat_quotient_of_mod_maximalIdeal_injective
    (u : N →ₗ[R] M)
    (hmod : Function.Injective (u.quotientMapByIdeal (maximalIdeal R))) :
    Module.Flat R (M ⧸ LinearMap.range u) := sorry

end CriteriaForFlatness

/-! ### Lemma_10_99_2 (from Chap10) -/
universe u v

open IsLocalRing
open scoped nonZeroDivisors

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing S] [Module.Flat R S]

local notation "𝔪S" => Ideal.map (algebraMap R S) (maximalIdeal R)

-- Proof sketch: apply Lemma `10.99.1` to the `R`-linear endomorphism of `S` given by
-- multiplication by `f`. The hypothesis says exactly that the induced map on the fibre ring
-- `S / 𝔪S` is injective, so Lemma `10.99.1` gives flatness of the cokernel, which is `S / fS`,
-- and injectivity of multiplication by `f` on `S`, i.e. that `f` is regular in the canonical
-- mathlib sense and hence a nonzerodivisor in `S`.
/-- Lemma 10.99.2: if `R → S` is a flat local homomorphism of Noetherian local rings and the
image of `f` in the fibre ring `S / 𝔪S`, where `𝔪` is the maximal ideal of `R`, is a
nonzerodivisor, then `S / fS` is flat over `R` and `f` is a nonzerodivisor in `S`. -/
theorem flat_quotient_and_nonZeroDivisor_of_fiber_nonZeroDivisor (f : S)
    (hbar : IsRegular (Ideal.Quotient.mk 𝔪S f)) :
    Module.Flat R (S ⧸ Ideal.span ({f} : Set S)) ∧ IsRegular f := by
  let u : S →ₗ[R] S := (LinearMap.mul R S) f
  have hf : Ideal.Quotient.mk 𝔪S f ∈ nonZeroDivisors (S ⧸ 𝔪S) := by
    exact isRegular_iff_mem_nonZeroDivisors.mp hbar
  have hmod : Function.Injective (u.quotientMapByIdeal (maximalIdeal R)) := by
    intro x y hxy
    refine Quotient.inductionOn₂' x y ?_ hxy
    intro a b hab
    have hab' : (Submodule.Quotient.mk (f * a) : S ⧸ maximalIdeal R • (⊤ : Submodule R S)) =
        Submodule.Quotient.mk (f * b) := by
      simpa [LinearMap.quotientMapByIdeal] using hab
    have hab'' : f * a - f * b ∈ maximalIdeal R • (⊤ : Submodule R S) :=
      (Submodule.Quotient.eq _).1 hab'
    apply (Submodule.Quotient.eq _).2
    rw [Ideal.smul_top_eq_map] at hab'' ⊢
    change f * a - f * b ∈ 𝔪S at hab''
    change a - b ∈ 𝔪S
    have hmul : f * (a - b) ∈ 𝔪S := by
      simpa [mul_sub] using hab''
    have hbar : Ideal.Quotient.mk 𝔪S (a - b) = 0 := by
      rw [mem_nonZeroDivisors_iff_right] at hf
      apply hf
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      simpa [mul_comm] using hmul
    exact (Ideal.Quotient.eq_zero_iff_mem).1 hbar
  refine ⟨?_, ?_⟩
  · have hrange : LinearMap.range u = (Ideal.span ({f} : Set S)).restrictScalars R := by
      simp [u]
    have hflat : Module.Flat R (S ⧸ LinearMap.range u) :=
      flat_quotient_of_mod_maximalIdeal_injective u hmod
    rw [hrange] at hflat
    let e : (S ⧸ Ideal.span ({f} : Set S)) ≃ₗ[R] S ⧸ (Ideal.span ({f} : Set S)).restrictScalars R :=
      (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span ({f} : Set S) : Ideal S)).symm
    exact Module.Flat.of_linearEquiv e
  · have hinj : Function.Injective u := injective_of_mod_maximalIdeal_injective u hmod
    rw [isRegular_iff_mem_nonZeroDivisors, mem_nonZeroDivisors_iff_left]
    intro x hx
    exact hinj <| by simpa [u] using hx

end

/-! ### Lemma_10_99_3 (from Chap10) -/
universe u v

open IsLocalRing RingTheory

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing S] [Module.Flat R S]

local notation "𝔪S" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "ClosedFiber" => S ⧸ 𝔪S

/- Domain sampling pass:
* primary domain: regular sequences under flat local base change and flatness of the resulting
  quotient rings;
* sampled owner declarations:
  - `RingTheory.Sequence.IsRegular`;
  - `RingTheory.Sequence.isRegular_cons_iff'`;
  - `RingTheory.Sequence.IsRegular.ndrecIterModByRegularWithRing`;
  - `flat_quotient_and_nonZeroDivisor_of_fiber_nonZeroDivisor`;
* source-facing layer: regularity of the image of `fs` in the closed-fiber quotient `ClosedFiber`;
* core/canonical layer: the owner predicate `RingTheory.Sequence.IsRegular`;
* bridge/view layer: the prefix quotients `S ⧸ Ideal.ofList (fs.take (i + 1))`.

Primitive data vs derived API:
* primitive data: the flat local map `R → S` and the regularity hypothesis on the image sequence in
  `ClosedFiber`, together with the Noetherian hypothesis on `S` needed by the flat-quotient owner
  theorem for each regular element;
* derived API: regularity of `fs` in `S` and flatness of the successive quotient rings.
-/

-- Proof sketch: use the owner induction principle
-- `Sequence.IsRegular.ndrecIterModByRegularWithRing` on the regular sequence in `ClosedFiber`. For
-- the first element, apply `flat_quotient_and_nonZeroDivisor_of_fiber_nonZeroDivisor` to the head
-- in the closed fiber. Then pass to the quotient by that head and use the inductive
-- characterization of `Sequence.IsRegular` for the tail.
/-- Lemma 10.99.3: if `R → S` is a flat local homomorphism of local rings, `S` is Noetherian, and
the images of a finite sequence `fs` in the closed fibre `S / 𝔪S`, where `𝔪` is the maximal ideal
of `R`, form a regular sequence, then `fs` is a regular sequence in `S`, and each quotient by a
nonempty initial segment of `fs` is flat over `R`. -/
theorem isRegular_and_flat_quotient_take_of_closedFiber_isRegular (fs : List S)
    (hfs : Sequence.IsRegular ClosedFiber (fs.map (Ideal.Quotient.mk 𝔪S))) :
    Sequence.IsRegular S fs ∧
      ∀ i : Fin fs.length, Module.Flat R (S ⧸ Ideal.ofList (fs.take (i + 1))) := sorry

end

/-! ### Lemma_10_99_4 (from Chap10) -/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

open TensorProduct.AlgebraTensorModule
open scoped TensorProduct
open IsLocalRing

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S]
variable [IsLocalRing R] [IsLocalRing S]
variable [IsNoetherianRing S]
variable [Algebra R S] [IsLocalHom (algebraMap R S)]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite S M]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S
local notation "ClosedFiberModule" => ClosedFiber ⊗[S] M

/- Domain sampling pass:
* primary domain: local commutative algebra of finite modules over flat local homomorphisms and
  their closed fibers;
* sampled owner declarations:
  - `Ideal.Fiber`, the canonical closed-fiber ring owner `κ(maximalIdeal R) ⊗[R] S`;
  - `Definition_10_65_2.mem_relativeAssassin_iff_fiber`, which uses the fiber module
    `((q.asIdeal.under R).Fiber S) ⊗[S] N` as the canonical module-level fiber;
  - `Lemma_10_39_15.nontrivial_tensor_residueField_iff_nontrivial_quotSMul`, the quotient bridge
    between residue-field fibers and reduction modulo the maximal ideal;
  - `Lemma_10_39_10.algebraMap_flat_of_flat_of_faithfullyFlat`, the owner descent statement for
    flatness of the algebra map.

Source/core/bridge triage:
* source-facing: the two textbook statements about freeness of `M` and flatness of `R → S`;
* core/canonical: the closed-fiber ring `ClosedFiber` and its fiber module `ClosedFiber ⊗[S] M`;
* bridge/view: the quotient presentation
  `M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))`.

Primitive data vs derived API:
* primitive owner data is the ambient local algebra map and the finite `S`-module `M`;
* freeness of the closed fiber is naturally a property of the canonical fiber module over
  `ClosedFiber`, not of a bespoke quotient wrapper.
-/

-- Proof sketch: choose lifts in `M` of a basis of the closed fiber module
-- `ClosedFiberModule = ClosedFiber ⊗[S] M`, equivalently
-- `M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))`, yielding an
-- `S`-linear map `S^n → M`. The induced map on the closed fiber is injective because the chosen
-- images form a basis there, so Lemma 10.99.1 gives injectivity upstairs. Nakayama's lemma gives
-- surjectivity, and hence `M` is free over `S`.
/-- Lemma 10.99.4 (1): if the closed fiber module `ClosedFiber ⊗[S] M`, equivalently
`M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))`, is free over the closed
fiber ring `ClosedFiber = (maximalIdeal R).Fiber S` and `M` is flat over `R`, then `M` is free
over `S`. -/
theorem free_of_flat_of_free_closedFiber [Module.Flat R M] [Module.Free ClosedFiber ClosedFiberModule] :
    Module.Free S M := sorry

-- Proof sketch: part (1) makes `M` into a free `S`-module. Because `M` is nontrivial, a nonzero
-- free `S`-module is faithfully flat over `S`; then apply Lemma 10.39.10 to descend the given
-- `R`-flatness of `M` to flatness of the algebra map `R → S`.
/-- Lemma 10.99.4 (2): if the closed fiber module `ClosedFiber ⊗[S] M`, equivalently
`M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))`, is free over the closed
fiber ring `ClosedFiber = (maximalIdeal R).Fiber S`, `M` is flat over `R`, and `M` is nonzero,
then the local homomorphism `R → S` is flat. -/
theorem algebraMap_flat_of_nontrivial_flat_module_of_free_closedFiber
    [Nontrivial M] [Module.Flat R M] [Module.Free ClosedFiber ClosedFiberModule] :
    (algebraMap R S).Flat := sorry

end

/-! ### Lemma_10_99_5 (from Chap10) -/
open IsLocalRing
open CategoryTheory

section CriteriaForFlatness

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing S]
variable {n : ℕ}
variable {F : Fin (n + 2) → Type v}
variable [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
variable [∀ i, IsScalarTower R S (F i)]

/- Domain-style sampling:
* primary domain: finite exact sequences of modules over a local ring map, together with reduction
  modulo the maximal ideal.
* inspected owner declarations:
  `CategoryTheory.ComposableArrows.Exact`,
  `CategoryTheory.ComposableArrows.mkOfObjOfMapSucc`,
  `CategoryTheory.HomologicalComplex.ExactAt`,
  `LinearMap.quotientMapByIdeal`.
* best owner abstraction: the finite family of differentials should be organized by the canonical
  finite-sequence owner `ComposableArrows`, with exactness carried by `ComposableArrows.Exact`;
  the leftmost injectivity clause remains separate source-facing edge data for the augmented
  sequence `0 → F_{n+1} → ⋯ → F₀`.
* primitive data: the maps `d i : F_{i+1} → F_i`, the finite/flat hypotheses on the modules, and
  the reduction modulo `maximalIdeal R`.
* derived API: the finite sequence `finiteSequence d` and the reduced sequence
  `reducedFiniteSequence R d`, together with their owner predicate `.Exact`.
* source/core/bridge triage:
  `source-facing`: the two lemmas about exactness and flat cokernels for a finite sequence of
    `S`-modules;
  `core/canonical`: `ComposableArrows.Exact`;
  `bridge/view`: `finiteSequence` and `reducedFiniteSequence`, which package the displayed maps into
    the canonical owner object.
-/

namespace CriteriaForFlatness

/-- The finite sequence
`F_{n+1} ⟶ F_n ⟶ ⋯ ⟶ F_0`
attached to the displayed differentials, organized by the canonical owner
`ComposableArrows (ModuleCat S) (n + 1)`. -/
noncomputable abbrev finiteSequence
    (d : ∀ i : Fin (n + 1), F i.succ →ₗ[S] F i.castSucc) :
    ComposableArrows (ModuleCat S) (n + 1) :=
  ComposableArrows.mkOfObjOfMapSucc
    (fun i ↦ ModuleCat.of S (F i.rev))
    (fun i ↦ by
      change ModuleCat.of S (F i.castSucc.rev) ⟶ ModuleCat.of S (F i.succ.rev)
      rw [Fin.rev_castSucc, Fin.rev_succ]
      exact ModuleCat.ofHom (d i.rev))

variable (R) in
/-- The reduction modulo `maximalIdeal R` of the finite sequence
`F_{n+1} ⟶ F_n ⟶ ⋯ ⟶ F_0`,
organized by the same canonical owner `ComposableArrows`. -/
noncomputable abbrev reducedFiniteSequence
    (d : ∀ i : Fin (n + 1), F i.succ →ₗ[S] F i.castSucc) :
    ComposableArrows (ModuleCat R) (n + 1) :=
  ComposableArrows.mkOfObjOfMapSucc
    (fun i ↦
      ModuleCat.of R
        (F i.rev ⧸ (maximalIdeal R • (⊤ : Submodule R (F i.rev)))))
    (fun i ↦ by
      change
        ModuleCat.of R
            (F i.castSucc.rev ⧸ (maximalIdeal R • (⊤ : Submodule R (F i.castSucc.rev)))) ⟶
          ModuleCat.of R
            (F i.succ.rev ⧸ (maximalIdeal R • (⊤ : Submodule R (F i.succ.rev))))
      rw [Fin.rev_castSucc, Fin.rev_succ]
      exact ModuleCat.ofHom
        (((d i.rev).restrictScalars R).quotientMapByIdeal (maximalIdeal R)))

end CriteriaForFlatness

/-- Lemma 10.99.5 (1): for a local homomorphism `R → S` of local rings with `S` Noetherian, if
`0 → F_{n+1}/𝔪F_{n+1} → F_n/𝔪F_n → ⋯ → F_0/𝔪F_0` is exact and every `F_i` is a finite `S`-module
flat over `R`, then `0 → F_{n+1} → F_n → ⋯ → F_0` is exact. The middle exactness is organized by
the canonical finite-sequence owner `ComposableArrows.Exact`, while injectivity of the leftmost
map remains the separate source-facing edge condition. -/
-- Proof sketch: argue by induction on `n + 1`. The base case is Lemma `10.99.1`, applied to the
-- leftmost map. For the inductive step, first use Lemma `10.99.1` on `F_{n+1} → F_n` to obtain
-- injectivity and flatness of its cokernel, then apply the induction hypothesis to the shortened
-- sequence obtained by replacing `F_n` with that cokernel.
theorem finiteComplexExact_of_reducedFiniteComplexExact
    (d : ∀ i : Fin (n + 1), F i.succ →ₗ[S] F i.castSucc)
    (hfinite : ∀ i, Module.Finite S (F i))
    (hflat : ∀ i, Module.Flat R (F i))
    (hexact_mod :
      Function.Injective
          (((d (Fin.last n)).restrictScalars R).quotientMapByIdeal (maximalIdeal R)) ∧
        (CriteriaForFlatness.reducedFiniteSequence R d).Exact) :
    Function.Injective (d (Fin.last n)) ∧
      (CriteriaForFlatness.finiteSequence d).Exact := sorry

/-- Lemma 10.99.5 (2): under the same hypotheses, the cokernel of `F₁ → F₀` is flat over `R`. -/
-- Proof sketch: after part (1) gives exactness of the original sequence, the same induction on
-- the length of the sequence shows that the cokernel of the rightmost differential is obtained
-- from a shorter exact sequence whose terms are still finite over `S` and flat over `R`; the base
-- case is again Lemma `10.99.1`.
theorem flat_cokernel_of_reducedFiniteComplexExact
    (d : ∀ i : Fin (n + 1), F i.succ →ₗ[S] F i.castSucc)
    (hfinite : ∀ i, Module.Finite S (F i))
    (hflat : ∀ i, Module.Flat R (F i))
    (hexact_mod :
      Function.Injective
          (((d (Fin.last n)).restrictScalars R).quotientMapByIdeal (maximalIdeal R)) ∧
        (CriteriaForFlatness.reducedFiniteSequence R d).Exact) :
    Module.Flat R (F 0 ⧸ LinearMap.range (d 0)) := sorry

end CriteriaForFlatness

/-! ### Lemma_10_99_6 (from Chap10) -/
open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/- Domain-style sampling:
- primary domain: low-degree `Tor₁` over a local ring, propagated from the residue field to
  finite-length modules in the textbook source-facing argument order;
- sampled owner declarations of the same kind:
  `CategoryTheory.Tor`,
  `CategoryTheory.isZero_Tor_succ_of_projective`,
  `ModuleCat.torTensorSixTermSequence_exact`,
  `CategoryTheory.tor_flip_iso`;
- best owner abstraction: the homological owner is the canonical bifunctor
  `CategoryTheory.Tor (ModuleCat R) 1`, while the induction owner on the finite-length source
  module is `IsFiniteLength R N`;
- primitive data vs derived API: the primitive data are only the fixed right `R`-module `M`, the
  local ring `R`, and the finite-length source module `N`. The vanishing statement below is
  derived API; the proof may pass through the canonical exact-sequence orientation
  `Tor₁^R(M, -)` via `tor_flip_iso`, but that symmetry comparison is bridge data rather than the
  main public statement.

Source/core/bridge triage:
- `source-facing`: Lemma 10.99.6, propagating vanishing of `Tor₁^R(ResidueField R, M)` to
  `Tor₁^R(N, M)` for finite-length `N`;
- `core/canonical`: `CategoryTheory.Tor (ModuleCat R) 1` and `IsFiniteLength R N`;
- `bridge/view`: the composition-series reduction to simple factors and the symmetry comparison
  `tor_flip_iso` used to move to the exact-sequence-friendly orientation belong to the proof, not
  to the public statement.
-/

-- Proof sketch: argue by induction on a finite-length composition series for `N`. Use
-- `tor_flip_iso` only as an internal bridge to pass to the exact-sequence-friendly orientation
-- `Tor₁^R(M, -)`. The base case is the simple-module case, which over a local ring identifies `N`
-- with `ResidueField R`. For the induction step, splice a short exact sequence with smaller
-- finite-length subquotients and apply the six-term exact Tor sequence from Lemma `10.75.2`.
/-- Lemma 10.99.6: if `Tor₁^R(ResidueField R, M)` vanishes for a local ring `R`, then
`Tor₁^R(N, M)` vanishes for every finite-length `R`-module `N`. -/
theorem isZero_tor_one_of_isFiniteLength_of_residueField_vanishing
    (hκ : IsZero (Tor₁[R](ResidueField R, M))) (hN : IsFiniteLength R N) :
    IsZero (Tor₁[R](N, M)) := sorry

end

/-! ### Lemma_10_99_7_Local_criterion_for_flatness (from Chap10) -/
open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v

section

variable {R : Type u} {S : Type v} {M : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite S M]

/- Domain-style sampling:
- primary domain: the local flatness criterion for a finite module over a local homomorphism of
  local Noetherian rings, expressed through residue-field `Tor₁`-vanishing;
- sampled owner declarations of the same kind:
  `Module.Flat`,
  `Module.Flat.iff_lift_lsmul_comp_subtype_injective`,
  `tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module`,
  `isZero_tor_one_of_isFiniteLength_of_residueField_vanishing`;
- best owner abstraction: the public owner is `Module.Flat`, while the source-facing homological
  hypothesis should use the chapter owner notation `Tor₁[R](ResidueField R, M)` rather than a raw
  derived-functor term;
- primitive data: the local map `R → S`, the finite `S`-module `M`, and the residue-field
  `Tor₁`-vanishing hypothesis;
- derived API: the flatness conclusion over the base ring `R`.

Source/core/bridge triage:
- `source-facing`: Lemma 10.99.7 itself;
- `core/canonical`: `Module.Flat` together with the canonical `Tor₁` owner from
  `Remark_10_75_9`;
- `bridge/view`: the quotient-by-ideal Tor/kernel comparison and the finite-length propagation of
  Lemma `10.99.6` belong to the proof route, not to the public statement.
-/

-- Proof sketch: by Lemma `10.39.5`, it is enough to prove injectivity of `I ⊗[R] M → M` for every
-- ideal `I` of `R`. Remark `10.75.9` identifies the kernel with `Tor₁^R(M, R / I)`, and Lemma
-- `10.99.6` gives vanishing for ideals of finite colength from the residue-field hypothesis. Use
-- the Artin-Rees argument from the textbook to reduce the general ideal case to finite-colength
-- ideals, then conclude by the faithfully flat maximal-ideal-adic completion from Lemma `10.97.3`.
/-- Lemma 10.99.7 (Local criterion for flatness): if `R → S` is a local homomorphism of local
Noetherian rings, `M` is a finite `S`-module, and `Tor₁^R(ResidueField R, M)` vanishes, then `M`
is flat over `R`. -/
theorem flat_of_residueField_tor_one_vanishing
    (hTor : IsZero (Tor₁[R](ResidueField R, M))) :
    Module.Flat R M := sorry

end

/-! ### Lemma_10_99_8 (from Chap10) -/
open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable {M : Type u} [AddCommGroup M] [Module R M]

-- These three helper theorems were in the deleted backup directory and need to be re-proved.
private theorem flat_quotient_pow_of_flat_mod_ideal_and_tor_one_quotient_vanishes
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (htor :
      IsZero
        (((Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of R M)))
    (n : ℕ) (_ : 1 ≤ n) :
    Module.Flat (R ⧸ I ^ n) (M ⧸ (I ^ n • ⊤ : Submodule R M)) := by
  sorry

private theorem tor_one_vanishes_of_annihilated_by_ideal_pow
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (htor :
      IsZero
        (((Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of R M)))
    {N : Type u} [AddCommGroup N] [Module R N]
    (m : ℕ) (_ : I ^ m ≤ Module.annihilator R N) :
    IsZero (((Tor (ModuleCat R) 1).obj (ModuleCat.of R N)).obj (ModuleCat.of R M)) := by
  sorry

private theorem flat_of_nilpotent_ideal_of_flat_mod_ideal_and_tor_one_quotient_vanishes
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (htor :
      IsZero
        (((Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of R M)))
    (_ : IsNilpotent I) :
    Module.Flat R M := by
  sorry

/-- Lemma 10.99.8: if `M / IM` is flat over `R / I` and `Tor₁^R(R / I, M)` vanishes, then
`M / I^n M` is flat over `R / I^n` for all `n ≥ 1`; for every `R`-module `N` annihilated by a
power of `I`, `Tor₁^R(N, M)` vanishes; and if `I` is nilpotent, then `M` is flat over `R`. -/
theorem flatness_and_tor_vanishing_along_ideal_powers
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (htor :
      IsZero
        (((Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of R M))) :
    (∀ n : ℕ, 1 ≤ n → Module.Flat (R ⧸ I ^ n) (M ⧸ (I ^ n • ⊤ : Submodule R M))) ∧
      (∀ {N : Type u} [AddCommGroup N] [Module R N],
        (∃ m : ℕ, I ^ m ≤ Module.annihilator R N) →
          IsZero (((Tor (ModuleCat R) 1).obj (ModuleCat.of R N)).obj (ModuleCat.of R M))) ∧
      (IsNilpotent I → Module.Flat R M) := by
  constructor
  · intro n hn
    exact flat_quotient_pow_of_flat_mod_ideal_and_tor_one_quotient_vanishes hflat htor n hn
  constructor
  · intro N _ _ hN
    rcases hN with ⟨m, hm⟩
    exact tor_one_vanishes_of_annihilated_by_ideal_pow hflat htor m hm
  · intro hI
    exact flat_of_nilpotent_ideal_of_flat_mod_ideal_and_tor_one_quotient_vanishes hflat htor hI

end

/-! ### Lemma_10_99_9 (from Chap10) -/
open scoped Pointwise
open TensorProduct
open LinearMap
open RingTheory.Sequence

universe u

section

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

-- Domain-style sampling:
-- * primary domain: commutative algebra of tensor products and successive ideal-power quotients.
-- * source-facing owner: the canonical map
--   `idealPowTensorToModuleSuccQuotient M :
--      M ⊗[R] (I^n / I^(n+1)) → I^n M / I^(n+1) M`.
-- * sampled core/canonical owners of the same construction style:
--   `Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow`,
--   `idealAssociatedGradedPiece`,
--   `TensorProduct.tensorQuotientEquiv`,
--   `Submodule.mapQ`,
--   `LinearMap.codRestrict`,
--   `TensorProduct.rid`.
-- * primitive data: the tensor-to-smul map `M ⊗[R] I^n → I^n M`.
-- * derived API: the descent to the canonical owner types for `I^n / I^(n+1)` and
--   `idealAssociatedGradedPiece I M n`, together with the pure-tensor evaluation lemma.
-- * refinement target: keep the source-facing map and remove the one-off public quotient aliases in
--   favor of the chapter/mathlib owners above.

-- Proof sketch: an element of `I ^ n` acts on `M` by scalar multiplication, so its image lies in
-- the submodule `I ^ n M = I ^ n • ⊤`.
/-- Scalar multiplication by an element of `I ^ n` lands in the submodule `I ^ n M`. -/
private theorem idealPowSmul_mem (I : Ideal R) (n : ℕ) (m : M) (a : ↥(I ^ n : Ideal R)) :
    a.1 • m ∈ idealAssociatedGradedStage I M n := sorry

private noncomputable def idealPowTensorToSmul (I : Ideal R) (n : ℕ) :
    M ⊗[R] ↥(I ^ n : Ideal R) →ₗ[R] ↥(idealAssociatedGradedStage I M n) :=
  LinearMap.codRestrict (idealAssociatedGradedStage I M n)
    ((TensorProduct.rid R M).toLinearMap.comp
      (TensorProduct.map (LinearMap.id : M →ₗ[R] M) ((I ^ n : Ideal R).subtype)))
    (by
      intro x
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · simp
      · intro m a
        simpa using idealPowSmul_mem I n m a
      · intro x y hx hy
        simpa using Submodule.add_mem (idealAssociatedGradedStage I M n) hx hy)

-- Proof sketch: the tensor-to-smul map carries the quotienting submodule
-- `M ⊗[R] I(I^n)` into `I(I^n M)`.
private theorem idealPowTensorToSmul_range_le (I : Ideal R) (n : ℕ) :
    LinearMap.range
        (TensorProduct.map (LinearMap.id : M →ₗ[R] M)
          ((I • (⊤ : Submodule R ↥(I ^ n : Ideal R))).subtype)) ≤
      Submodule.comap (idealPowTensorToSmul I n)
        (I • (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n))) := by
  rintro _ ⟨x, rfl⟩
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [idealPowTensorToSmul]
  · intro m a
    change idealPowTensorToSmul I n (m ⊗ₜ[R] a.1) ∈
      I • (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n))
    refine Submodule.smul_induction_on a.2 ?_ ?_
    · intro r hr b hb
      let c : ↥(idealAssociatedGradedStage I M n) := ⟨b.1 • m, idealPowSmul_mem I n m b⟩
      have hc : c ∈ (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n)) := by simp
      have hs : idealPowTensorToSmul I n (m ⊗ₜ[R] (r • b : ↥(I ^ n : Ideal R))) = r • c := by
        ext
        simp [idealPowTensorToSmul, c]
      rw [hs]
      exact Submodule.smul_mem_smul hr hc
    · intro x y hx hy
      simpa [tmul_add, map_add] using
        Submodule.add_mem (I • (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n))) hx hy
  · intro x y hx hy
    simpa using Submodule.add_mem
      (Submodule.comap (idealPowTensorToSmul I n)
        (I • (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n)))) hx hy

private theorem idealPowModuleInternalDenominator_eq (I : Ideal R) (n : ℕ) :
    I • (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n)) =
      (idealAssociatedGradedStage I M (n + 1)).submoduleOf (idealAssociatedGradedStage I M n) := by
  ext x
  rw [Submodule.mem_smul_top_iff]
  change ((x : M) ∈ I • idealAssociatedGradedStage I M n) ↔
    ((x : M) ∈ idealAssociatedGradedStage I M (n + 1))
  simp [idealAssociatedGradedStage, ← mul_smul, Ideal.mul_comm, pow_succ]

private noncomputable def idealPowModuleInternalPieceEquiv (I : Ideal R) (n : ℕ) :
    (↥(idealAssociatedGradedStage I M n) ⧸
        (I • (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n)))) ≃ₗ[R]
      idealAssociatedGradedPiece I M n :=
  Submodule.quotEquivOfEq _ _ (idealPowModuleInternalDenominator_eq I n)

variable (M) in
/-- The canonical map `M ⊗[R] (I^n / I^(n+1)) → I^n M / I^(n+1) M`, with codomain given by the
`n`th associated graded piece. -/
noncomputable def idealPowTensorToModuleSuccQuotient (I : Ideal R) (n : ℕ) :
    M ⊗[R] ((I ^ n : Ideal R) ⧸ (I • (⊤ : Submodule R ↥(I ^ n : Ideal R)))) →ₗ[R]
      idealAssociatedGradedPiece I M n :=
  (idealPowModuleInternalPieceEquiv I n).toLinearMap.comp
    (((LinearMap.range
        (TensorProduct.map (LinearMap.id : M →ₗ[R] M)
          ((I • (⊤ : Submodule R ↥(I ^ n : Ideal R))).subtype))).mapQ
      (I • (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n)))
      (idealPowTensorToSmul I n)
      (idealPowTensorToSmul_range_le I n)).comp
      (TensorProduct.tensorQuotientEquiv M
        (I • (⊤ : Submodule R ↥(I ^ n : Ideal R)))).toLinearMap)

/-- The canonical tensor-to-quotient map sends `m ⊗ a` to the class of `a • m`. -/
theorem idealPowTensorToModuleSuccQuotient_tmul_mk
    (I : Ideal R) (n : ℕ) (m : M) (a : ↥(I ^ n : Ideal R)) :
    idealPowTensorToModuleSuccQuotient M I n (m ⊗ₜ[R] Submodule.Quotient.mk a) =
      Submodule.Quotient.mk
        ⟨a.1 • m, idealPowSmul_mem I n m a⟩ := by
  have hsmul :
      idealPowTensorToSmul I n (m ⊗ₜ[R] a) =
        (⟨a.1 • m, idealPowSmul_mem I n m a⟩ : ↥(idealAssociatedGradedStage I M n)) := rfl
  simp only [idealPowTensorToModuleSuccQuotient, LinearMap.comp_apply]
  change
    idealPowModuleInternalPieceEquiv I n
      (((LinearMap.range
        (TensorProduct.map (LinearMap.id : M →ₗ[R] M)
          ((I • (⊤ : Submodule R ↥(I ^ n : Ideal R))).subtype))).mapQ
        (I • (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n)))
        (idealPowTensorToSmul I n)
        (idealPowTensorToSmul_range_le I n))
      (Submodule.Quotient.mk (m ⊗ₜ[R] a))) =
    _
  rw [Submodule.mapQ_apply, hsmul]
  simp [idealPowModuleInternalPieceEquiv]

-- Proof sketch: apply the flatness criterion of Lemma `10.99.8` to `R / I²` and `M / I² M`. By
-- Remark `10.75.9`, the injectivity of the displayed tensor map identifies with the vanishing of
-- the relevant `Tor₁`, which is exactly the hypothesis needed there.
/-- Lemma 10.99.9 (1): if `M / IM` is flat over `R / I` and the canonical map
`M ⊗[R] (I / I^2) → IM / I^2 M` is injective, then `M / I^2 M` is flat over `R / I^2`. -/
theorem flat_mod_ideal_sq_of_flat_mod_ideal_and_injective_tensor_ideal_quotient
    {I : Ideal R}
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (hinj : Function.Injective (idealPowTensorToModuleSuccQuotient M I 1)) :
    Module.Flat (R ⧸ I ^ 2) (M ⧸ (I ^ 2 • (⊤ : Submodule R M))) := sorry

-- Proof sketch: argue by induction on `k`. The case `k = 0` is the given flatness of `M / IM`,
-- and the induction step applies part (1) over the ring `R / I^(n+1)` using Remark `10.75.9` to
-- translate the injectivity hypothesis for `I^n / I^(n+1)` into the needed `Tor₁`-vanishing.
/-- Lemma 10.99.9 (2): if `M / IM` is flat over `R / I` and for every `1 ≤ n ≤ k` the canonical
map `M ⊗[R] (I^n / I^(n+1)) → I^n M / I^(n+1) M` is injective, then `M / I^(k+1) M` is flat over
`R / I^(k+1)`. -/
theorem flat_mod_ideal_pow_succ_of_flat_mod_ideal_and_injective_tensor_successive_quotients
    {I : Ideal R} (k : ℕ)
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (hinj :
      ∀ n : ℕ, 1 ≤ n → n ≤ k →
        Function.Injective (idealPowTensorToModuleSuccQuotient M I n)) :
    Module.Flat (R ⧸ I ^ (k + 1)) (M ⧸ (I ^ (k + 1) • (⊤ : Submodule R M))) := sorry

end

/-! ### Lemma_10_99_10_Variant_of_the_local_criterion (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} {M : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite S M]

/- Domain-style sampling for the variant local criterion for flatness:
- primary domain: flatness of a finite module over a local homomorphism of Noetherian local rings,
  detected from a quotient-flatness hypothesis and a `Tor₁` vanishing hypothesis over the
  quotient ring;
- sampled owner declarations of the same kind:
  `Module.Flat`,
  `Tor₁[R](M, N)`,
  `flat_of_residueField_tor_one_vanishing`,
  `tor_one_vanishes_of_annihilated_by_ideal_pow`;
- best owner abstraction: the public conclusion is the canonical owner `Module.Flat`, and the
  homological input should be expressed by the chapter owner notation `Tor₁[R](M, R ⧸ I)` rather
  than by the raw derived-functor term;
- primitive data: the local map `R → S`, the finite `S`-module `M`, the proper ideal `I`, the
  vanishing of `Tor₁^R(M, R / I)`, and flatness of `M / IM` over `R / I`;
- derived API: the flatness conclusion over `R`.

Source/core/bridge triage:
- `source-facing`: the Stacks variant local criterion itself;
- `core/canonical`: `Module.Flat` together with the chapter owner notation `Tor₁[R](M, N)`;
- `bridge/view`: Lemma `10.99.8` upgrades quotient flatness and quotient `Tor₁` vanishing to the
  residue-field vanishing input for Lemma `10.99.7`, and those intermediate reductions belong to
  the proof route rather than the public statement.
-/

-- Proof sketch: apply Lemma `10.99.8` to the ideal `I` to promote flatness of `M / IM` over
-- `R / I` and the assumed vanishing of `Tor₁^R(M, R / I)` to vanishing of `Tor₁^R(κ(R), M)`,
-- using the symmetry of `Tor` to match the orientation in Lemma `10.99.7`. Then invoke the local
-- criterion for flatness from Lemma `10.99.7`.
/-- Lemma 10.99.10 (Variant of the local criterion): let `R → S` be a local homomorphism of
Noetherian local rings, let `I ≠ R` be an ideal of `R`, and let `M` be a finite `S`-module. If
`Tor₁^R(M, R / I)` vanishes and `M / IM` is flat over `R / I`, then `M` is flat over `R`. -/
theorem flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal
    (I : Ideal R) (hI : I ≠ ⊤)
    (hTor : CategoryTheory.Limits.IsZero (Tor₁[R](M, R ⧸ I)))
    (hflat :
      Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))) :
    Module.Flat R M := sorry

end

/-! ### Lemma_10_99_11 (from Chap10) -/
open IsLocalRing

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite S M]

/- Domain-style sampling for Lemma 10.99.11:
- primary domain: flatness of a finite module over a Noetherian base, detected primewise after
  localizing the target ring and using flatness of the quotient modules by ideal powers;
- sampled owner declarations in the same domain:
  `Module.Flat`,
  `LocalizedModule.AtPrime`,
  `flat_iff_flat_localizedModule_atPrime_over_under`,
  `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal`;
- best owner abstraction: the public conclusions belong on the canonical flatness owner
  `Module.Flat`, with `LocalizedModule.AtPrime` as the prime-local view and
  `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal` as the local owner theorem reused in the
  proof;
- primitive data: the ideal `I`, the prime `q` containing `IS`, and the hypothesis that every
  quotient `M / I^n M` is flat over `R / I^n`;
- derived API: flatness of `M_q` over `R`, and the local-ring specialization obtained by taking
  the unique closed point.

Source/core/bridge triage:
- `source-facing`: the Stacks prime-local flatness criterion and its local-ring specialization;
- `core/canonical`: `Module.Flat`, `LocalizedModule.AtPrime`,
  `flat_iff_flat_localizedModule_atPrime_over_under`, and
  `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal`;
- `bridge/view`: Lemma `10.51.5` supplies the annihilation-after-localization step needed to turn
  the quotient-flatness hypotheses into the Tor-vanishing input of the local criterion, and the
  local-ring theorem is the closed-point specialization of the prime-local statement.
-/

private abbrev FlatQuotientsByIdealPowers (M : Type w) [AddCommGroup M] [Module R M]
    (I : Ideal R) : Prop :=
  ∀ n : ℕ, 1 ≤ n → Module.Flat (R ⧸ I ^ n) (M ⧸ (I ^ n • (⊤ : Submodule R M)))

-- Proof sketch: localize at `q` and apply the variant of the local criterion from Lemma
-- `10.99.10` over the local map `R_(q ∩ R) → S_q`. The hypothesis on all quotients `M / I^n M`
-- gives flatness modulo powers after localization, Remark `10.75.9` identifies the relevant
-- `Tor₁` group with the kernel of `I ⊗ M → M`, and Lemma `10.51.5` kills that kernel after
-- localizing at `q`.
/-- Lemma 10.99.11: let `R → S` be a ring map, let `I` be an ideal of `R`, and let `M` be a
finite `S`-module. Assume `R` and `S` are Noetherian and that `M / I^n M` is flat over `R / I^n`
for every `n ≥ 1`. Then for every prime `q` of `S` containing `IS`, the localization `M_q` is
flat over `R`. -/
theorem flat_localizedModule_atPrime_of_flat_quotients_by_ideal_powers
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal)
    (hflat : FlatQuotientsByIdealPowers M I) :
    Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) := sorry

-- Proof sketch: specialize the prime-local statement to the closed point of `Spec S`; this is the
-- prime `⊤`, whose underlying ideal is `maximalIdeal S`.
/-- If the target ring `S` is local and `IS` is contained in its maximal ideal, then `M` is flat
over `R` under the same quotient-flatness hypotheses. -/
theorem flat_of_isLocalRing_and_flat_quotients_by_ideal_powers
    [IsLocalRing S] (I : Ideal R) (hI : I.map (algebraMap R S) ≤ maximalIdeal S)
    (hflat : FlatQuotientsByIdealPowers M I) :
    Module.Flat R M := sorry

end

/-! ### Lemma_10_99_12 (from Chap10) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped TensorProduct ChangeOfRings

universe u

noncomputable section

section

variable {R R' R'' S : Type u}
variable [CommRing R] [CommRing R'] [CommRing R''] [CommRing S]
variable [Algebra R R'] [Algebra R R''] [Algebra R' R''] [IsScalarTower R R' R'']
variable [Algebra R S]
variable {M : Type u} [AddCommGroup M] [Module R M]

set_option quotPrecheck false in
local notation "Tor₁[" R "](" M ", " S ")" =>
  (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R S))

/-- Helper for Lemma 10.99.12: in an abelian category with projective resolutions, the chosen
projective-resolution functor is additive because the lift of `f + g` is homotopic to the sum of
the chosen lifts of `f` and `g`. -/
private lemma projective_resolutions_additive (C : Type u) [Category C] [Abelian C]
    [HasProjectiveResolutions C] :
    Functor.Additive (projectiveResolutions C) := by
  constructor
  intro X Y f g
  -- Compare the chosen lift of `f + g` with the sum of the chosen lifts in the homotopy category.
  change
    (HomotopyCategory.quotient C (ComplexShape.down ℕ)).map
        (ProjectiveResolution.lift (f + g) (projectiveResolution X) (projectiveResolution Y)) =
      (HomotopyCategory.quotient C (ComplexShape.down ℕ)).map
          (ProjectiveResolution.lift f (projectiveResolution X) (projectiveResolution Y)) +
        (HomotopyCategory.quotient C (ComplexShape.down ℕ)).map
          (ProjectiveResolution.lift g (projectiveResolution X) (projectiveResolution Y))
  rw [← Functor.map_add]
  -- Two lifts of the same morphism are homotopic, so they coincide in the homotopy category.
  exact
    HomotopyCategory.eq_of_homotopy _ _
      (ProjectiveResolution.liftHomotopy (f + g)
        (ProjectiveResolution.lift (f + g) (projectiveResolution X) (projectiveResolution Y))
        (ProjectiveResolution.lift f (projectiveResolution X) (projectiveResolution Y) +
          ProjectiveResolution.lift g (projectiveResolution X) (projectiveResolution Y))
        (by simp)
        (by simp [Preadditive.comp_add, Preadditive.add_comp]))

/-- Helper for Lemma 10.99.12: left-derived functors of additive functors remain additive, since
their projective-resolution presentation and the homology functor are both additive. -/
private lemma left_derived_additive {C : Type u} [Category C] [Abelian C]
    [HasProjectiveResolutions C] (F : C ⥤ C) [F.Additive] (n : ℕ) :
    Functor.Additive (F.leftDerived n) := by
  -- Unfold the left-derived functor into the additive projective-resolution stage followed by
  -- additive homology on the homotopy category.
  let _ : Functor.Additive (projectiveResolutions C) := projective_resolutions_additive C
  dsimp [Functor.leftDerived, Functor.leftDerivedToHomotopyCategory]
  infer_instance

/-- Helper for Lemma 10.99.12: the right-variable `Tor₁` functor for a fixed left argument is
additive, so its map on endomorphisms respects zero and addition. -/
private lemma tor_right_functor_additive :
    Functor.Additive (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M))) := by
  -- `Tor₁` is the first left-derived functor of tensoring on the left by `M`, so the additive
  -- structure comes from the additive resolution/homology presentation above.
  simpa [Tor] using
    (left_derived_additive
      ((tensoringLeft (ModuleCat R)).obj (ModuleCat.of R M)) 1)

/-- Helper for Lemma 10.99.12: the coefficient ring acts on `Tor₁^R(M, S)` through the
right-variable `Tor` functor applied to multiplication endomorphisms of `S`. -/
private noncomputable def torOneActionEnd :
    S →+* Module.End R (Tor₁[R](M, S)) := by
  let F := ((Tor (ModuleCat R) 1).obj (ModuleCat.of R M))
  let eS : End (ModuleCat.of R S) ≃+* Module.End R (ModuleCat.of R S) :=
    (ModuleCat.of R S).endRingEquiv
  let eT : End (Tor₁[R](M, S)) ≃+* Module.End R (Tor₁[R](M, S)) :=
    (Tor₁[R](M, S)).endRingEquiv
  refine
    { toFun := fun s ↦ eT <| F.map (eS.symm (Module.toModuleEnd R S s))
      map_one' := by
        -- The scalar `1` acts through the identity endomorphism, and `Tor` preserves identities.
        have hone : eS.symm (Module.toModuleEnd R S (1 : S)) = 1 := by
          simpa using congrArg eS.symm (RingHom.map_one (Module.toModuleEnd R S))
        have hmapone :
            F.map (𝟙 (ModuleCat.of R S)) = 𝟙 (F.obj (ModuleCat.of R S)) := by
          simpa using ((CategoryTheory.Functor.mapEnd (f := F) (X := ModuleCat.of R S)).map_one)
        rw [hone]
        change eT (F.map (𝟙 (ModuleCat.of R S))) = 1
        rw [hmapone]
        change eT (1 : End (F.obj (ModuleCat.of R S))) = 1
        rw [eT.map_one]
      map_mul' := by
        intro x y
        -- Multiplication of scalars matches composition of multiplication endomorphisms.
        have hmul :
            eS.symm (Module.toModuleEnd R S (x * y)) =
              eS.symm (Module.toModuleEnd R S x) * eS.symm (Module.toModuleEnd R S y) := by
          simpa using congrArg eS.symm ((Module.toModuleEnd R S).map_mul x y)
        let fx : End (F.obj (ModuleCat.of R S)) :=
          F.map (eS.symm (Module.toModuleEnd R S x))
        let fy : End (F.obj (ModuleCat.of R S)) :=
          F.map (eS.symm (Module.toModuleEnd R S y))
        have hmapmul :
            (F.map (eS.symm (Module.toModuleEnd R S (x * y))) :
                End (F.obj (ModuleCat.of R S))) =
              fx * fy := by
          rw [hmul]
          simpa [fx, fy] using
            ((CategoryTheory.Functor.mapEnd (f := F) (X := ModuleCat.of R S)).map_mul
              (eS.symm (Module.toModuleEnd R S x))
              (eS.symm (Module.toModuleEnd R S y)))
        exact congrArg eT hmapmul
      map_zero' := by
        letI : F.Additive := tor_right_functor_additive (R := R) (M := M)
        -- Additivity gives the zero morphism comparison after transporting through `endRingEquiv`.
        have hzero : eS.symm (Module.toModuleEnd R S (0 : S)) = 0 := by
          simpa using congrArg eS.symm (RingHom.map_zero (Module.toModuleEnd R S))
        have hmapzero : F.map (eS.symm (Module.toModuleEnd R S (0 : S))) = 0 := by
          rw [hzero]
          exact Functor.map_zero F (ModuleCat.of R S) (ModuleCat.of R S)
        rw [hmapzero]
        change eT (0 : End (F.obj (ModuleCat.of R S))) = 0
        rw [eT.map_zero]
      map_add' := by
        intro x y
        letI : F.Additive := tor_right_functor_additive (R := R) (M := M)
        -- The scalar-addition law is inherited from additivity of the right-variable `Tor` functor.
        have hadd :
            eS.symm (Module.toModuleEnd R S (x + y)) =
              eS.symm (Module.toModuleEnd R S x) + eS.symm (Module.toModuleEnd R S y) := by
          simpa using congrArg eS.symm ((Module.toModuleEnd R S).map_add x y)
        have hmapadd :
            F.map (eS.symm (Module.toModuleEnd R S x) + eS.symm (Module.toModuleEnd R S y)) =
              F.map (eS.symm (Module.toModuleEnd R S x)) +
                F.map (eS.symm (Module.toModuleEnd R S y)) := by
          exact
            (Functor.map_add (F := F)
              (f := eS.symm (Module.toModuleEnd R S x))
              (g := eS.symm (Module.toModuleEnd R S y)))
        rw [hadd, hmapadd]
        exact eT.map_add _ _ }

/-- Helper for Lemma 10.99.12: the theorem statement views `Tor₁^R(M, S)` as an `S`-module, so
we temporarily package that action via `torOneActionEnd`. -/
private noncomputable instance torOneModule :
    Module S (Tor₁[R](M, S)) := by
  let _ : Module (Module.End R (Tor₁[R](M, S))) (Tor₁[R](M, S)) := inferInstance
  let f : S →+* Module.End R (Tor₁[R](M, S)) := torOneActionEnd
  simpa using (Module.compHom (Tor₁[R](M, S)) f : Module S (Tor₁[R](M, S)))

local notation "Tor₁Obj[" R "](" M ", " S ")" =>
  (ModuleCat.of S (Tor₁[R](M, S)))
local notation "extScalars" => ModuleCat.extendScalars (algebraMap R' R'')
local notation "resScalars" => ModuleCat.restrictScalars (algebraMap R' R'')

variable [Module.Flat R' (TensorProduct R R' M)]

private noncomputable instance torOneBaseChangeTargetModule :
    Module R' (Tor₁[R](M, R'')) :=
  Module.compHom (Tor₁[R](M, R'')) (algebraMap R' R'')

private noncomputable instance torOneBaseChangeSourceModule :
    Module R' ↑((extScalars).obj (Tor₁Obj[R](M, R'))) :=
  Module.compHom _ (algebraMap R' R'')

/-- Helper for Lemma 10.99.12: a projective object of `ModuleCat` yields the usual module-theoretic
projectivity on its underlying module. -/
private lemma module_projective_of_categorical_projective
    {A : Type u} [CommRing A] (P : ModuleCat A) (hP : Projective P) :
    Module.Projective A P := by
  -- TODO: restore the `ModuleCat` projective-to-module-projective bridge with the right
  -- smallness universe so the scalar-extended resolution terms inherit module projectivity.
  sorry

/-- Helper for Lemma 10.99.12: the scalar-extension functor along `R → R'`. -/
private noncomputable abbrev scalar_extension_functor : ModuleCat R ⥤ ModuleCat R' :=
  ModuleCat.extendScalars (algebraMap R R')

/-- Helper for Lemma 10.99.12: scalar extension preserves projective objects because restriction of
scalars preserves epimorphisms. -/
private noncomputable instance scalar_extension_functor_preservesProjectiveObjects :
    (scalar_extension_functor (R := R) (R' := R')).PreservesProjectiveObjects :=
  by
    -- TODO: restore the universe-aligned adjunction proof for scalar extension preserving projectives.
    sorry

/-- Helper for Lemma 10.99.12: the fixed source projective resolution of `M` before scalar
extension. -/
private noncomputable abbrev scalar_extended_source_resolution :
    CategoryTheory.ProjectiveResolution (ModuleCat.of R M) :=
  CategoryTheory.projectiveResolution (ModuleCat.of R M)

/-- Helper for Lemma 10.99.12: the degree-`n` term of the scalar-extended fixed source
resolution. -/
private noncomputable abbrev scalar_extended_resolution_X (n : ℕ) : ModuleCat R' :=
  (scalar_extension_functor (R := R) (R' := R')).obj
    ((scalar_extended_source_resolution (R := R) (M := M)).complex.X n)

/-- Helper for Lemma 10.99.12: the scalar-extended differential `F₁' ⟶ F₀'`. -/
private noncomputable abbrev scalar_extended_d_one :
    scalar_extended_resolution_X (R := R) (R' := R') (M := M) 1 ⟶
      scalar_extended_resolution_X (R := R) (R' := R') (M := M) 0 :=
  (scalar_extension_functor (R := R) (R' := R')).map
    ((scalar_extended_source_resolution (R := R) (M := M)).complex.d 1 0)

/-- Helper for Lemma 10.99.12: the scalar-extended differential `F₂' ⟶ F₁'`. -/
private noncomputable abbrev scalar_extended_d_two :
    scalar_extended_resolution_X (R := R) (R' := R') (M := M) 2 ⟶
      scalar_extended_resolution_X (R := R) (R' := R') (M := M) 1 :=
  (scalar_extension_functor (R := R) (R' := R')).map
    ((scalar_extended_source_resolution (R := R) (M := M)).complex.d 2 1)

/-- Helper for Lemma 10.99.12: the scalar-extended augmentation `F₀' ⟶ M ⊗[R] R'`. -/
private noncomputable abbrev scalar_extended_pi_zero :
    scalar_extended_resolution_X (R := R) (R' := R') (M := M) 0 ⟶
      (scalar_extension_functor (R := R) (R' := R')).obj (ModuleCat.of R M) :=
  (scalar_extension_functor (R := R) (R' := R')).map
    ((scalar_extended_source_resolution (R := R) (M := M)).π.f 0)

/-- Helper for Lemma 10.99.12: the scalar-extended lower differential still composes to zero with
the scalar-extended augmentation. -/
private theorem scalar_extended_d_one_comp_pi_zero :
    scalar_extended_d_one (R := R) (R' := R') (M := M) ≫
        scalar_extended_pi_zero (R := R) (R' := R') (M := M) =
      0 := by
  -- Map the original augmentation relation through scalar extension.
  have hzero :
      ((scalar_extended_source_resolution (R := R) (M := M)).complex.d 1 0) ≫
          ((scalar_extended_source_resolution (R := R) (M := M)).π.f 0) =
        0 :=
    CategoryTheory.ProjectiveResolution.complex_d_comp_π_f_zero
      (P := scalar_extended_source_resolution (R := R) (M := M))
  have hmap_zero :
      (scalar_extension_functor (R := R) (R' := R')).map
          (0 :
            ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 1) ⟶
              ModuleCat.of R M) =
        0 := by
    simpa using
      (Functor.map_zero (F := scalar_extension_functor (R := R) (R' := R'))
        ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 1)
        (ModuleCat.of R M))
  rw [scalar_extended_d_one, scalar_extended_pi_zero, ← Functor.map_comp]
  exact
    (congrArg ((scalar_extension_functor (R := R) (R' := R')).map) hzero).trans
      hmap_zero

/-- Helper for Lemma 10.99.12: the scalar-extended degree-two and degree-one differentials still
compose to zero. -/
private theorem scalar_extended_d_two_comp_d_one :
    scalar_extended_d_two (R := R) (R' := R') (M := M) ≫
        scalar_extended_d_one (R := R) (R' := R') (M := M) =
      0 := by
  -- Map the original `d₂ ≫ d₁ = 0` relation through scalar extension.
  have hzero :
      ((scalar_extended_source_resolution (R := R) (M := M)).complex.d 2 1) ≫
          ((scalar_extended_source_resolution (R := R) (M := M)).complex.d 1 0) =
        0 :=
    ((scalar_extended_source_resolution (R := R) (M := M)).complex.d_comp_d 2 1 0)
  have hmap_zero :
      (scalar_extension_functor (R := R) (R' := R')).map
          (0 :
            ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 2) ⟶
              ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 0)) =
        0 := by
    simpa using
      (Functor.map_zero (F := scalar_extension_functor (R := R) (R' := R'))
        ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 2)
        ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 0))
  rw [scalar_extended_d_two, scalar_extended_d_one, ← Functor.map_comp]
  exact
    (congrArg ((scalar_extension_functor (R := R) (R' := R')).map) hzero).trans
      hmap_zero

/-- Helper for Lemma 10.99.12: after extending scalars on the fixed projective resolution of `M`,
the lower window `F₁' ⟶ F₀' ⟶ M ⊗[R] R'` is still exact and surjective at the augmentation. -/
private theorem scalar_extended_augmentation_exact :
    (ShortComplex.mk
        (scalar_extended_d_one (R := R) (R' := R') (M := M))
        (scalar_extended_pi_zero (R := R) (R' := R') (M := M))
        (scalar_extended_d_one_comp_pi_zero (R := R) (R' := R') (M := M))).Exact ∧
      Epi (scalar_extended_pi_zero (R := R) (R' := R') (M := M)) := by
  -- TODO: rebuild this scalar-extended cokernel argument with the current `CokernelCofork` API.
  sorry

/-- Helper for Lemma 10.99.12: in a short exact sequence, flatness of the middle and right terms
forces flatness of the kernel. This is the local copy needed for the `B'` step of the source
proof, avoiding a new chapter import. -/
private theorem shortExact_flat_X₁
    {A : Type u} [CommRing A] {S : ShortComplex (ModuleCat A)}
    (hS : S.ShortExact) [Module.Flat A S.X₂] [Module.Flat A S.X₃] :
    Module.Flat A S.X₁ := by
  -- TODO: prove this directly from the flatness criterion without the now-missing
  -- `ShortComplex.UniversallyExact` helper API.
  sorry

/-- Helper for Lemma 10.99.12: the lower kernel `B' = ker(F₀' ⟶ M ⊗[R] R')` is flat over `R'`.
This is the exact place where the source hypothesis on `M ⊗[R] R'` enters the proof. -/
private theorem source_window_lower_kernel_flat :
    Module.Flat R' (LinearMap.ker (scalar_extended_pi_zero (R := R) (R' := R') (M := M)).hom) := by
  -- TODO: after the scalar-extended lower row is reconstructed as a short exact sequence again,
  -- this is the flatness-of-kernel step from the textbook proof.
  sorry

/-- Helper for Lemma 10.99.12: the image of the scalar-extended differential `d₁'` lands in the
lower kernel `B' = ker(F₀' ⟶ M ⊗[R] R')`. -/
private theorem scalar_extended_d_one_mem_lower_kernel :
    ∀ x : scalar_extended_resolution_X (R := R) (R' := R') (M := M) 1,
      (scalar_extended_d_one (R := R) (R' := R') (M := M)).hom x ∈
        LinearMap.ker (scalar_extended_pi_zero (R := R) (R' := R') (M := M)).hom := by
  intro x
  -- Evaluate the already-proved composition identity on the chosen element.
  change
    (scalar_extended_pi_zero (R := R) (R' := R') (M := M)).hom
        ((scalar_extended_d_one (R := R) (R' := R') (M := M)).hom x) = 0
  simpa using
    DFunLike.congr_fun
      (congrArg ModuleCat.Hom.hom
        (scalar_extended_d_one_comp_pi_zero (R := R) (R' := R') (M := M))) x

/-- Helper for Lemma 10.99.12: the scalar-extended lower window
`F₁' ⟶ F₀' ⟶ M ⊗[R] R'` viewed as a short complex. -/
private noncomputable abbrev source_window_lower_shortComplex :
    ShortComplex (ModuleCat R') :=
  ShortComplex.mk
    (scalar_extended_d_one (R := R) (R' := R') (M := M))
    (scalar_extended_pi_zero (R := R) (R' := R') (M := M))
    (scalar_extended_d_one_comp_pi_zero (R := R) (R' := R') (M := M))

/-- Helper for Lemma 10.99.12: the source-proof cod-restricted map `F₁' ⟶ B'`, where
`B' = ker(F₀' ⟶ M ⊗[R] R')`. -/
private noncomputable abbrev source_window_upper_to_lower_kernel :
    scalar_extended_resolution_X (R := R) (R' := R') (M := M) 1 ⟶
      (source_window_lower_shortComplex (R := R) (R' := R') (M := M)).moduleCatLeftHomologyData.K :=
  (source_window_lower_shortComplex (R := R) (R' := R') (M := M)).moduleCatLeftHomologyData.liftK
    (scalar_extended_d_one (R := R) (R' := R') (M := M))
    (scalar_extended_d_one_comp_pi_zero (R := R) (R' := R') (M := M))

/-- Helper for Lemma 10.99.12: replacing `d₁'` by its cod-restriction to `B'` does not change the
kernel, so the source cycles object is still `K' = ker(d₁')`. -/
private theorem source_window_upper_to_lower_kernel_ker_eq :
    LinearMap.ker (source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom =
      LinearMap.ker (scalar_extended_d_one (R := R) (R' := R') (M := M)).hom := by
  -- The upper map is just `d₁'` cod-restricted into the lower kernel, so its kernel is unchanged.
  simpa [source_window_upper_to_lower_kernel, source_window_lower_shortComplex] using
    LinearMap.ker_codRestrict
      (LinearMap.ker (scalar_extended_pi_zero (R := R) (R' := R') (M := M)).hom)
      (scalar_extended_d_one (R := R) (R' := R') (M := M)).hom
      (scalar_extended_d_one_mem_lower_kernel (R := R) (R' := R') (M := M))

/-- Helper for Lemma 10.99.12: the cod-restricted upper map `F₁' ⟶ B'` is surjective because
exactness at `F₀'` identifies `B'` with the image of `d₁'`. -/
private theorem source_window_upper_to_lower_kernel_surjective :
    Function.Surjective
      (source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom := by
  -- TODO: after exactness of the lower row is repaired, this is the image-equals-kernel argument.
  sorry

/-- Helper for Lemma 10.99.12: the source-proof upper row
`0 → K' → F₁' → B' → 0` is short exact after scalar extension to `R'`. -/
private theorem source_window_upper_shortExact :
    (LinearMap.shortComplexKer
      (source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom).ShortExact := by
  -- The cod-restricted upper map is surjective, so its kernel short complex is short exact.
  exact
    LinearMap.shortExact_shortComplexKer
      (source_window_upper_to_lower_kernel_surjective (R := R) (R' := R') (M := M))

/-- Helper for Lemma 10.99.12: tensoring the source-proof upper row on the right by `R''` keeps
the pair `K' ⊗[R'] R'' → F₁' ⊗[R'] R'' → B' ⊗[R'] R''` exact. This is the quotient-level part of
the textbook argument that does not yet use the comparison `B' ⊗[R'] R'' ≅ ker(π₀'')`. -/
private theorem tensorized_source_window_upper_exact :
    Function.Exact
      (((LinearMap.ker
          (source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom).subtype).rTensor
        R'')
      (((source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom).rTensor R'') := by
  have hExact :
      Function.Exact
        (LinearMap.ker
          (source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom).subtype
        (source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom := by
    -- Rewrite the already-constructed short exact row into the `LinearMap.Exact` API.
    simpa [LinearMap.shortComplexKer] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (LinearMap.shortComplexKer
          (source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom)).mp
        (source_window_upper_shortExact (R := R) (R' := R') (M := M)).exact
  have hSurj :
      Function.Surjective
        (source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom :=
    source_window_upper_to_lower_kernel_surjective (R := R) (R' := R') (M := M)
  -- Right exactness of tensor product carries the upper short exact row to the tensorized row.
  exact rTensor_exact R'' hExact hSurj

/-- Helper for Lemma 10.99.12: after tensoring the source-proof upper row with `R''`, the image of
`K' ⊗[R'] R'' → F₁' ⊗[R'] R''` is exactly the kernel of
`F₁' ⊗[R'] R'' → B' ⊗[R'] R''`. -/
private theorem tensorized_source_window_upper_range_eq_ker :
    LinearMap.range
        ((((LinearMap.ker
            (source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom).subtype).rTensor
          R'')) =
      LinearMap.ker
        (((source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom).rTensor R'') := by
  -- This is the range-kernel form of the exactness statement recorded above.
  exact
    (LinearMap.exact_iff.mp
      (tensorized_source_window_upper_exact (R := R) (R' := R') (R'' := R'') (M := M))).symm

/-- Helper for Lemma 10.99.12: the `2 → 1 → 0` window of the coefficient-tensored projective
resolution of `X` over `R`. This isolates the exact textbook complex used to compute `Tor₁`. -/
private noncomputable abbrev tensorRight_degree_one_window
    (A X : ModuleCat R) : ShortComplex (ModuleCat R) :=
  (HomologicalComplex.shortComplexFunctor' (ModuleCat R) (ComplexShape.down ℕ) 2 1 0).obj
    (((tensorRight A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (CategoryTheory.ProjectiveResolution.complex
        (CategoryTheory.projectiveResolution X)))

/-- Helper for Lemma 10.99.12: degree-one homology of the coefficient-tensored projective
resolution is canonically the homology of its `2 → 1 → 0` window. -/
private noncomputable def tensorRight_degree_one_window_homology_iso
    (A X : ModuleCat R) :
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 1).obj
      (((tensorRight A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (CategoryTheory.ProjectiveResolution.complex
          (CategoryTheory.projectiveResolution X))) ≅
      ShortComplex.homology (tensorRight_degree_one_window (R := R) A X) :=
  -- The standard `homologyFunctorIso'` API turns the full degree-one homology computation into
  -- the explicit three-term window used in the source proof.
  (HomologicalComplex.homologyFunctorIso' (C := ModuleCat R) (c := ComplexShape.down ℕ)
      (i := 2) (j := 1) (k := 0) (by simp) (by simp)).app
    (((tensorRight A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (CategoryTheory.ProjectiveResolution.complex
        (CategoryTheory.projectiveResolution X)))

/-- Helper for Lemma 10.99.12: after flipping the public `Tor₁^R(M, A)` owner, the fixed
projective resolution of `M` computes the target via the left-derived `tensorRight A`
presentation. -/
private noncomputable def tor_flip_target_to_tensorRight_leftDerived_iso
    (A : ModuleCat R) :
    (((Functor.flip (Tor' (ModuleCat R) 1)).obj (ModuleCat.of R M)).obj A) ≅
      (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 1).obj
        (((tensorRight A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (CategoryTheory.ProjectiveResolution.complex
            (CategoryTheory.projectiveResolution (ModuleCat.of R M)))) := sorry

/-- Helper for Lemma 10.99.12: `Tor₁^R(M, A)` is computed by the `2 → 1 → 0` window obtained by
tensoring the fixed projective resolution of `M` with `A`. -/
private noncomputable def tor_one_flip_window_iso (A : ModuleCat R) :
    (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj A) ≅
      ShortComplex.homology
        (tensorRight_degree_one_window (R := R) A (ModuleCat.of R M)) :=
  -- Route correction: first flip the public owner to the right-variable presentation, then
  -- resolve `M`, and finally reduce the full degree-one homology computation to the window.
  (((tor_flip_iso (ModuleCat R) 1).app (ModuleCat.of R M)).app A) ≪≫
    tor_flip_target_to_tensorRight_leftDerived_iso (R := R) (M := M) A ≪≫
      tensorRight_degree_one_window_homology_iso (R := R) A (ModuleCat.of R M)

/-- Helper for Lemma 10.99.12: conjugating a surjective module morphism by source and target
isomorphisms preserves surjectivity of the underlying function. -/
private theorem surjective_of_iso_conjugation
    {A B X Y : ModuleCat R'} (eSource : A ≅ X) (eTarget : B ≅ Y) (f : X ⟶ Y)
    (hf : Function.Surjective f) :
    Function.Surjective (eSource.hom ≫ f ≫ eTarget.inv) := by
  -- Move the target element across the chosen target isomorphism, then pull the preimage back
  -- across the chosen source isomorphism.
  intro y
  rcases hf (eTarget.hom y) with ⟨x, hx⟩
  refine ⟨eSource.inv x, ?_⟩
  change eTarget.inv (f (eSource.hom (eSource.inv x))) = y
  simp [hx]

/-- Helper for Lemma 10.99.12: the textbook tensor source is not just a linear map but a linear
equivalence, coming from tensor symmetry after identifying `extendScalars` with a tensor product. -/
private noncomputable def torOneTextbookTensorSourceEquiv :
    TensorProduct R' (Tor₁[R](M, R')) R'' ≃ₗ[R']
      ↑((extScalars).obj (Tor₁Obj[R](M, R'))) := by
  let eR'' : R'' ≃ₗ[R'] ↑((resScalars).obj (ModuleCat.of R'' R'')) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ by
        have h_source : r • x = (algebraMap R' R'') r * x := Algebra.smul_def r x
        have h_target :
            r • (show ↑((resScalars).obj (ModuleCat.of R'' R'')) from x) =
              (algebraMap R' R'') r * x := by
          simpa [Algebra.smul_def] using
            (@ModuleCat.restrictScalars.smul_def' _ _ _ _ (algebraMap R' R'')
              (ModuleCat.of R'' R'') r x)
        exact h_source.trans h_target.symm }
  let e :
      TensorProduct R' (Tor₁[R](M, R')) R'' ≃ₗ[R']
        TensorProduct R' (Tor₁[R](M, R')) ↑((resScalars).obj (ModuleCat.of R'' R'')) :=
    TensorProduct.congr (LinearEquiv.refl R' _) eR''
  let c :
      TensorProduct R' (Tor₁[R](M, R')) ↑((resScalars).obj (ModuleCat.of R'' R'')) ≃ₗ[R']
        ↑((extScalars).obj (Tor₁Obj[R](M, R'))) := by
      simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
        (TensorProduct.comm R' (Tor₁[R](M, R')) ((resScalars).obj (ModuleCat.of R'' R'')))
  exact e.trans c

/-- Helper for Lemma 10.99.12: the textbook tensor source map is surjective because it comes from
the preceding linear equivalence. -/
private theorem torOneTextbookTensorSource_surjective :
    Function.Surjective
      ((torOneTextbookTensorSourceEquiv :
          TensorProduct R' (Tor₁[R](M, R')) R'' ≃ₗ[R']
            ↑((extScalars).obj (Tor₁Obj[R](M, R')))).toLinearMap) :=
  (torOneTextbookTensorSourceEquiv :
      TensorProduct R' (Tor₁[R](M, R')) R'' ≃ₗ[R']
        ↑((extScalars).obj (Tor₁Obj[R](M, R')))).surjective

/-- The source-facing tensor-product identification used in Lemma 10.99.12. -/
noncomputable def torOneTextbookTensorSource :
    TensorProduct R' (Tor₁[R](M, R')) R'' →ₗ[R']
      ↑((extScalars).obj (Tor₁Obj[R](M, R'))) :=
  let e :
      TensorProduct R' (Tor₁[R](M, R')) R'' ≃ₗ[R']
        ↑((extScalars).obj (Tor₁Obj[R](M, R'))) :=
    torOneTextbookTensorSourceEquiv
  e.toLinearMap

/-- The base-change comparison for Lemma 10.99.12, now intended to be defined by conjugating the
window-level homology map from the textbook proof. -/
noncomputable def torOneBaseChangeComparison :
    (extScalars).obj (Tor₁Obj[R](M, R')) ⟶ Tor₁Obj[R](M, R'') :=
  -- TODO: the next source-faithful step is to tensor the now-closed upper short exact sequence
  -- `0 → K' → F₁' → B' → 0` from `source_window_upper_shortExact`, use the flatness of `B'` from
  -- `source_window_lower_kernel_flat` to obtain a surjection on tensorized cycles, descend that
  -- surjection to degree-one homology, and only then transport it through `tor_one_flip_window_iso`.
  sorry

/-- Helper for Lemma 10.99.12: once `torOneBaseChangeComparison` is rebuilt from the explicit
window comparison, its surjectivity is exactly the source proof's statement on degree-one
homology. -/
private theorem tor_one_baseChangeComparison_surjective_of_flat_baseChange :
    Function.Surjective
      (torOneBaseChangeComparison.hom :
        ↑((extScalars).obj (Tor₁Obj[R](M, R'))) → Tor₁[R](M, R'')) := by
  -- Route correction: the remaining work is no longer an owner-level `map_smul'` problem.
  -- TODO: define `torOneBaseChangeComparison` by descending the tensorized-cycles surjection from
  -- `source_window_upper_shortExact` and `source_window_lower_kernel_flat` to the quotient
  -- description of `ShortComplex.homology`, then conjugate the resulting homology map through
  -- `tor_one_flip_window_iso` on the source and target sides.
  sorry

/-- The source-facing tensor-product map for Lemma 10.99.12. Its source is the textbook tensor
view, while its middle comparison is the categorical base-change map. -/
noncomputable def torOneBaseChangeMap :
    TensorProduct R' (Tor₁[R](M, R')) R'' →ₗ[R'] Tor₁[R](M, R'') :=
  let comparisonLinear :
      ↑((extScalars).obj (Tor₁Obj[R](M, R'))) →ₗ[R'] Tor₁[R](M, R'') :=
    { toFun := torOneBaseChangeComparison.hom
      map_add' := torOneBaseChangeComparison.hom.map_add
      map_smul' := fun c x ↦ by
        change torOneBaseChangeComparison.hom ((algebraMap R' R'' c) • x) =
          (algebraMap R' R'' c) • torOneBaseChangeComparison.hom x
        simpa using torOneBaseChangeComparison.hom.map_smul (algebraMap R' R'' c) x }
  comparisonLinear.comp torOneTextbookTensorSource

-- Proof sketch: choose a free resolution of `M` over `R`, tensor the `2 → 1 → 0` window with
-- `R'`, and write `K'` for the cycles. Flatness of `M ⊗[R] R'` over `R'` keeps the lower exact
-- sequence exact after tensoring with `R''`, so `K' ⊗[R'] R'' → K''` is surjective. Passing to
-- the degree-one homology quotients and conjugating by the window identifications gives the
-- desired surjection on `Tor₁`.
/-- Lemma 10.99.12, textbook tensor-product form: if `M ⊗[R] R'` is flat over `R'`, then the
natural base-change map `Tor₁^R(M, R') ⊗[R'] R'' → Tor₁^R(M, R'')` is surjective. -/
theorem torOne_baseChangeMap_surjective_of_flat_baseChange :
    Function.Surjective
      (torOneBaseChangeMap : TensorProduct R' (Tor₁[R](M, R')) R'' → Tor₁[R](M, R'')) := by
  -- The only remaining input is surjectivity of the window-level comparison packaged above.
  have hcomparison :
      Function.Surjective
        (torOneBaseChangeComparison.hom :
          ↑((extScalars).obj (Tor₁Obj[R](M, R'))) → Tor₁[R](M, R'')) :=
    tor_one_baseChangeComparison_surjective_of_flat_baseChange
  have hsource :
      Function.Surjective
        (torOneTextbookTensorSource :
          TensorProduct R' (Tor₁[R](M, R')) R'' →
            ↑((extScalars).obj (Tor₁Obj[R](M, R')))) :=
    torOneTextbookTensorSource_surjective
  intro y
  rcases hcomparison y with ⟨x, hx⟩
  rcases hsource x with
      ⟨z, rfl⟩
  exact ⟨z, hx⟩

end
