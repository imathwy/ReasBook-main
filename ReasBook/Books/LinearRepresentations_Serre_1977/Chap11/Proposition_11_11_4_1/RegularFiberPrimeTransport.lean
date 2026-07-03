import LinearRepresentations_Serre_1977.Chap11.Proposition_11_11_4_1.ConjClassFunctionRealization

-- Stable regular-fiber prime-transport helpers extracted from Proposition 11-11.4-1.

universe u v

noncomputable section

open Representation
open scoped Representation SubgroupInduction TensorProduct

section

variable {G : Type} [Group G]
variable {A : Type v} [CommRing A]
variable [Finite G] [Algebra A ℂ]

local instance regularFiberPrimeTransportFintypeGroup : Fintype G := Fintype.ofFinite G
local instance regularFiberPrimeTransportFintypeSubgroup (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

local notation "SpecARG" =>
  PrimeSpectrum (A ⊗R(G))

local notation "P0" => tensorCharacterRingZeroPrimeIdeal
local notation "ℐ" => tensorCharacterRingInductionIdeal

section RegularPrime

variable [IsDomain A] [Ring.HasFiniteQuotients A]

/-- Helper for Proposition 11-11.4-1: the coordinate-evaluation prime at a `p`-regular class in
the residue-field function ring on `PRegularConjClass G p`. This is the model prime that the
regular-fiber transport should recover on `A ⊗ R(G)`. -/
noncomputable def pregular_coordinate_eval_prime
    (p : Nat.Primes) {K : Type*} [Field K] (c : PRegularConjClass G p) :
    PrimeSpectrum (PRegularConjClass G p → K) :=
  PrimeSpectrum.comap (Pi.evalRingHom (fun _ : PRegularConjClass G p ↦ K) c)
    ⟨(⊥ : Ideal K), inferInstance⟩

/-- Helper for Proposition 11-11.4-1: distinct `p`-regular classes already define distinct
coordinate-evaluation primes on the function ring `PRegularConjClass G p → K`. This isolates the
uniqueness part of the regular-fiber route entirely on the function-ring side. -/
theorem pregular_coordinate_eval_prime_eq_iff
    (p : Nat.Primes) {K : Type*} [Field K]
    (c₁ c₂ : PRegularConjClass G p) :
    pregular_coordinate_eval_prime (G := G) (p := p) (K := K) c₁ =
        pregular_coordinate_eval_prime (G := G) (p := p) (K := K) c₂ ↔
      c₁ = c₂ := by
  constructor
  · intro hP
    -- The point-mass function at `c₁` lies in the kernel at `c₂` but not in the kernel at `c₁`
    -- unless the two class parameters coincide.
    by_contra hc
    classical
    let f : PRegularConjClass G p → K := fun d ↦ if d = c₁ then 1 else 0
    have hc' : c₂ ≠ c₁ := fun h ↦ hc h.symm
    have hf₂ :
        f ∈ (pregular_coordinate_eval_prime (G := G) (p := p) (K := K) c₂).asIdeal := by
      change Pi.evalRingHom (fun _ : PRegularConjClass G p ↦ K) c₂ f = 0
      simp [f, hc']
    have hf₁ :
        f ∉ (pregular_coordinate_eval_prime (G := G) (p := p) (K := K) c₁).asIdeal := by
      change Pi.evalRingHom (fun _ : PRegularConjClass G p ↦ K) c₁ f ≠ 0
      simp [f]
    exact hf₁ (by simpa [hP] using hf₂)
  · intro hc
    -- Matching class parameters make the coordinate kernels definitionally equal.
    subst hc
    rfl

/-- Helper for Proposition 11-11.4-1: an algebra equivalence from the regular fiber over `M` to
the residue-field function ring on `PRegularConjClass G p` transports coordinate-evaluation
primes back to the fiber. -/
noncomputable def regular_fiber_lift
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (e : (M.1.asIdeal.Fiber (A ⊗R(G))) ≃ₐ[M.1.asIdeal.ResidueField]
      (PRegularConjClass G p → M.1.asIdeal.ResidueField))
    (c : PRegularConjClass G p) :
    PrimeSpectrum (M.1.asIdeal.Fiber (A ⊗R(G))) :=
  (PrimeSpectrum.comapEquiv e.toRingEquiv).symm
    (pregular_coordinate_eval_prime (G := G) (p := p)
      (K := M.1.asIdeal.ResidueField) c)

/-- Helper for Proposition 11-11.4-1: after transporting the regular fiber over `M` to the
function ring on `PRegularConjClass G p`, equality of two lifted coordinate primes is already
equivalent to equality of the underlying `p`-regular classes. This closes the transport-side
uniqueness once the structural fiber equivalence is available. -/
theorem regular_fiber_lift_eq_iff
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (e : (M.1.asIdeal.Fiber (A ⊗R(G))) ≃ₐ[M.1.asIdeal.ResidueField]
      (PRegularConjClass G p → M.1.asIdeal.ResidueField))
    (c₁ c₂ : PRegularConjClass G p) :
    regular_fiber_lift (A := A) (G := G) p M e c₁ =
        regular_fiber_lift (A := A) (G := G) p M e c₂ ↔
      c₁ = c₂ := by
  let E :
      PrimeSpectrum (PRegularConjClass G p → M.1.asIdeal.ResidueField) ≃o
        PrimeSpectrum (M.1.asIdeal.Fiber (A ⊗R(G))) :=
    (PrimeSpectrum.comapEquiv
      (R := M.1.asIdeal.Fiber (A ⊗R(G)))
      (S := PRegularConjClass G p → M.1.asIdeal.ResidueField)
      e.toRingEquiv).symm
  constructor
  · intro hlift
    -- Injectivity of the prime-spectrum transport reduces equality in the fiber to equality of
    -- the underlying coordinate primes in the function ring.
    have heval :
        pregular_coordinate_eval_prime (G := G) (p := p)
            (K := M.1.asIdeal.ResidueField) c₁ =
          pregular_coordinate_eval_prime (G := G) (p := p)
            (K := M.1.asIdeal.ResidueField) c₂ := by
      exact E.injective <| by simpa [regular_fiber_lift, E] using hlift
    exact
      (pregular_coordinate_eval_prime_eq_iff
        (G := G) (p := p) (K := M.1.asIdeal.ResidueField) c₁ c₂).mp heval
  · intro hc
    -- Equal class parameters yield equal transported coordinate primes by substitution.
    subst hc
    rfl

/-- Helper for Proposition 11-11.4-1: once the regular fiber is identified with the
`p`-regular function ring, the lifted coordinate-prime assignment is injective. This is the
function-ring uniqueness packaged in a reusable form for the later transport step. -/
theorem regular_fiber_lift_injective
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (e : (M.1.asIdeal.Fiber (A ⊗R(G))) ≃ₐ[M.1.asIdeal.ResidueField]
      (PRegularConjClass G p → M.1.asIdeal.ResidueField)) :
    Function.Injective (regular_fiber_lift (A := A) (G := G) p M e) := by
  intro c₁ c₂ hlift
  -- The already-isolated `↔` turns equality of transported coordinate primes back into equality
  -- of the underlying `p`-regular classes.
  exact
    (regular_fiber_lift_eq_iff (A := A) (G := G) p M e c₁ c₂).mp hlift

/-- Helper for Proposition 11-11.4-1: every prime of the regular fiber over `M` is the lift of a
coordinate-evaluation prime from the residue-field function ring on `PRegularConjClass G p`. -/
theorem regular_fiber_lift_surjective
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (e : (M.1.asIdeal.Fiber (A ⊗R(G))) ≃ₐ[M.1.asIdeal.ResidueField]
      (PRegularConjClass G p → M.1.asIdeal.ResidueField)) :
    Function.Surjective (regular_fiber_lift (A := A) (G := G) p M e) := by
  intro q
  let E :
      PrimeSpectrum (PRegularConjClass G p → M.1.asIdeal.ResidueField) ≃o
        PrimeSpectrum (M.1.asIdeal.Fiber (A ⊗R(G))) :=
    (PrimeSpectrum.comapEquiv
      (R := M.1.asIdeal.Fiber (A ⊗R(G)))
      (S := PRegularConjClass G p → M.1.asIdeal.ResidueField)
      e.toRingEquiv).symm
  -- Classify the pushed-forward fiber prime by a coordinate of the function ring.
  obtain ⟨c, hc⟩ :=
    exists_eq_comap_evalRingHom_bot_of_primeSpectrum_pRegularConjClass
      (G := G) p (E.symm q)
  refine ⟨c, ?_⟩
  calc
    regular_fiber_lift (A := A) (G := G) p M e c
        = E (pregular_coordinate_eval_prime (G := G) (p := p)
            (K := M.1.asIdeal.ResidueField) c) := by
              rfl
    _ = E (E.symm q) := by
          simpa [E, pregular_coordinate_eval_prime] using congrArg E hc
    _ = q := by
          simpa [E] using E.apply_symm_apply q

/-- Helper for Proposition 11-11.4-1: transporting a prime of the regular fiber over `M` back
through `PrimeSpectrum.primesOverOrderIsoFiber` gives the corresponding prime of `A ⊗ R(G)`. -/
noncomputable def regular_fiber_prime_to_tensor_prime
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (q : PrimeSpectrum (M.1.asIdeal.Fiber (A ⊗R(G)))) :
    PrimeSpectrum (A ⊗R(G)) :=
  ⟨((PrimeSpectrum.primesOverOrderIsoFiber A (A ⊗R(G)) M.1.asIdeal).symm q).1,
    inferInstance⟩

/-- Helper for Proposition 11-11.4-1: the transport from regular-fiber primes to primes of
`A ⊗ R(G)` over the fixed maximal ideal `M` is injective. This isolates the
`PrimeSpectrum.primesOverOrderIsoFiber` reflection step so later uniqueness arguments can work in
the ambient spectrum without losing the underlying fiber point. -/
theorem regular_fiber_prime_to_tensor_prime_injective
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    Function.Injective
      (regular_fiber_prime_to_tensor_prime (A := A) (G := G) p M) := by
  intro q₁ q₂ hq
  -- Equality of the transported ambient primes forces equality of the corresponding
  -- `primesOver` points over `M`.
  have hsub :
      (PrimeSpectrum.primesOverOrderIsoFiber A (A ⊗R(G)) M.1.asIdeal).symm q₁ =
        (PrimeSpectrum.primesOverOrderIsoFiber A (A ⊗R(G)) M.1.asIdeal).symm q₂ := by
    apply Subtype.ext
    simpa [regular_fiber_prime_to_tensor_prime] using congrArg PrimeSpectrum.asIdeal hq
  -- The fiber/order equivalence then reflects that equality back to the original fiber primes.
  exact
    (PrimeSpectrum.primesOverOrderIsoFiber A (A ⊗R(G)) M.1.asIdeal).symm.injective hsub

/-- Helper for Proposition 11-11.4-1: sending an ambient prime over `M` into the regular fiber
and transporting it back through `regular_fiber_prime_to_tensor_prime` returns the original
prime. -/
theorem regular_fiber_prime_to_tensor_prime_prime_over_fixed_maximal_to_fiber
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (𝔭 : PrimeSpectrum (A ⊗R(G)))
    (h𝔭 : Ideal.comap (algebraMap A (A ⊗R(G))) 𝔭.asIdeal = M.1.asIdeal) :
    regular_fiber_prime_to_tensor_prime (A := A) (G := G) p M
        (prime_over_fixed_maximal_to_fiber (A := A) (G := G) p M 𝔭 h𝔭) =
      𝔭 := by
  apply PrimeSpectrum.ext
  -- The inverse-side normalization of the fiber/primes-over equivalence identifies the ideals.
  simpa [regular_fiber_prime_to_tensor_prime] using
    prime_over_fixed_maximal_to_fiber_symm (A := A) (G := G) p M 𝔭 h𝔭

/-- Helper for Proposition 11-11.4-1: after identifying the regular fiber over `M` with the
function ring on `PRegularConjClass G p`, the coordinate-evaluation prime at `c` transports to a
prime of `A ⊗ R(G)`. -/
noncomputable def regular_fiber_coordinate_prime
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (e : (M.1.asIdeal.Fiber (A ⊗R(G))) ≃ₐ[M.1.asIdeal.ResidueField]
      (PRegularConjClass G p → M.1.asIdeal.ResidueField))
    (c : PRegularConjClass G p) :
    PrimeSpectrum (A ⊗R(G)) :=
  regular_fiber_prime_to_tensor_prime (A := A) (G := G) p M
    (regular_fiber_lift (A := A) (G := G) p M e c)

/-- Helper for Proposition 11-11.4-1: after identifying the regular fiber over `M` with the
function ring on `PRegularConjClass G p`, equality of the transported coordinate primes in the
ambient tensor character ring is already equivalent to equality of the underlying `p`-regular
classes. This removes the remaining transport bookkeeping from the regular-branch uniqueness
frontier. -/
theorem regular_fiber_coordinate_prime_eq_iff
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (e : (M.1.asIdeal.Fiber (A ⊗R(G))) ≃ₐ[M.1.asIdeal.ResidueField]
      (PRegularConjClass G p → M.1.asIdeal.ResidueField))
    (c₁ c₂ : PRegularConjClass G p) :
    regular_fiber_coordinate_prime (A := A) (G := G) p M e c₁ =
        regular_fiber_coordinate_prime (A := A) (G := G) p M e c₂ ↔
      c₁ = c₂ := by
  constructor
  · intro hambient
    -- Injectivity of the ambient transport reduces equality of ambient coordinate primes back to
    -- equality of the corresponding fiber primes.
    have hfiber :
        regular_fiber_lift (A := A) (G := G) p M e c₁ =
          regular_fiber_lift (A := A) (G := G) p M e c₂ := by
      exact
        regular_fiber_prime_to_tensor_prime_injective (A := A) (G := G) (p := p) (M := M)
          (by simpa [regular_fiber_coordinate_prime] using hambient)
    -- The previously isolated function-ring argument now recovers equality of the class
    -- parameters themselves.
    exact (regular_fiber_lift_eq_iff (A := A) (G := G) p M e c₁ c₂).mp hfiber
  · intro hc
    -- Equal class parameters give definitionally equal transported coordinate primes.
    subst hc
    rfl

/-- Helper for Proposition 11-11.4-1: every transported coordinate prime from the regular fiber
lies over the fixed maximal ideal `M`. This is the formal contraction statement coming directly
from `PrimeSpectrum.primesOverOrderIsoFiber`, before any Brauer-theoretic input is used. -/
theorem regular_fiber_coordinate_prime_comap_eq_fixed_maximal
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (e : (M.1.asIdeal.Fiber (A ⊗R(G))) ≃ₐ[M.1.asIdeal.ResidueField]
      (PRegularConjClass G p → M.1.asIdeal.ResidueField))
    (c : PRegularConjClass G p) :
    Ideal.comap (algebraMap A (A ⊗R(G)))
        (regular_fiber_coordinate_prime (A := A) (G := G) p M e c).asIdeal =
      M.1.asIdeal := by
  -- The ambient prime is obtained by transporting a fiber prime back through
  -- `PrimeSpectrum.primesOverOrderIsoFiber`, so its contraction equality is exactly the
  -- packaged `primesOver` datum of that inverse image.
  let q :
      M.1.asIdeal.primesOver (A ⊗R(G)) :=
    (PrimeSpectrum.primesOverOrderIsoFiber A (A ⊗R(G)) M.1.asIdeal).symm
      (regular_fiber_lift (A := A) (G := G) p M e c)
  simpa [Ideal.under_def, regular_fiber_coordinate_prime, regular_fiber_prime_to_tensor_prime, q]
    using q.2.2.1.symm

end RegularPrime

end
