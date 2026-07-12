import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap10.Definition_10_112_5
import StacksProject_2024.Chap15.Lemma_15_51_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u

section

variable (P : FieldAlgebraProperty)
variable {R Λ : Type u} [CommRing R] [CommRing Λ] [Algebra R Λ]

/- Domain sampling pass:
* primary domain: commutative algebra of fiber algebras, prime localizations, and local criteria
  for residue-field algebra properties on Noetherian fibers;
* sampled owner declarations:
  - `FieldAlgebraProperty`, the Chapter 15 owner for properties of residue-field algebras;
  - `FieldAlgebraProperty.HasPropertyB`, the canonical owner for axiom `(B)`;
  - `Ideal.Fiber`, the canonical owner for the fiber algebra `κ(𝔭) ⊗[R] Λ`;
  - `fiberLocalRingAt R Λ q` from `Definition_10_112_5`, the canonical owner for the local ring of
    the fiber at `q`;
  - `fiberLocalRingAtResidueFieldAlgebra`, the Chapter 10 owner-level bridge making
    `fiberLocalRingAt R Λ q` a `κ(q ∩ R)`-algebra;
  - `PrimeSpectrum.preimageHomeomorphFiber`, the canonical identification between primes of a fiber
    algebra and primes of `Λ` lying over a fixed base prime;
  - `isRegularRingMap_local_tfae` from `Lemma_15_41_2_Regular_is_a_local_property`, the same
    source-facing local-to-global TFAE pattern in the nearby chapter development.

Source/core/bridge triage:
* `source-facing`: `fiberProperty_tfae`, the textbook local criterion on fiber
  algebras and their localization at maximal source/target pairs;
* `core/canonical`: `FieldAlgebraProperty.HasPropertyB`, `Ideal.Fiber`, `fiberLocalRingAt`, and
  the owner-level bridge `fiberLocalRingAtResidueFieldAlgebra`;
* `bridge/view`: the identification between primes of the fiber algebra and primes of `Λ` lying
  over a fixed base prime.

Primitive data are the field-algebra property `P k A` together with the Chapter 15 owner axiom
`FieldAlgebraProperty.HasPropertyB`. The theorem below applies that owner directly to the fiber
algebras and their localizations. Following the chapter owner pattern from
`Lemma_15_41_2_Regular_is_a_local_property`, the source-facing theorem is phrased directly on the
three clauses rather than through one-off public wrapper names. In the maximal-ideal clause, the
source tests the single local fiber of `R_(m' ∩ R) → Λ_(m')` at each `m' : MaximalSpectrum Λ`;
the auxiliary source-localization choice is already absorbed by the canonical owner
`fiberLocalRingAt`.
-/

end

namespace Algebra

section

variable {R Λ : Type u} [CommRing R] [CommRing Λ] [Algebra R Λ]
variable [IsNoetherianRing Λ]
variable (P : FieldAlgebraProperty) [P.HasPropertyB]

/-- Helper for Lemma 15.51.2: each fiber algebra `κ(p) ⊗[R] Λ` is Noetherian when `Λ` is
Noetherian. -/
private theorem fiber_isNoetherianRing
    (p : PrimeSpectrum R) :
    IsNoetherianRing (p.asIdeal.Fiber Λ) := by
  -- Commute the tensor factors so the fiber is viewed as an essentially finite type `Λ`-algebra.
  let _ : Algebra.EssFiniteType Λ (Λ ⊗[R] p.asIdeal.ResidueField) := inferInstance
  let _ : IsNoetherianRing (Λ ⊗[R] p.asIdeal.ResidueField) :=
    Algebra.EssFiniteType.isNoetherianRing Λ (Λ ⊗[R] p.asIdeal.ResidueField)
  exact
    isNoetherianRing_of_ringEquiv (Λ ⊗[R] p.asIdeal.ResidueField)
      (Algebra.TensorProduct.comm R p.asIdeal.ResidueField Λ).toRingEquiv.symm

/-- Helper for Lemma 15.51.2: the fixed-fiber localization at the prime corresponding to
`q : Spec Λ` is the canonical local fiber ring `fiberLocalRingAt R Λ q`. -/
private theorem fiber_local_ringAt_over_eq
    (p : PrimeSpectrum R) (q : PrimeSpectrum Λ)
    (hq : PrimeSpectrum.comap (algebraMap R Λ) q = p) :
    P p.asIdeal.ResidueField
      (Localization.AtPrime ((PrimeSpectrum.preimageEquivFiber R Λ p ⟨q, hq⟩).asIdeal)) ↔
      P (q.asIdeal.under R).ResidueField (fiberLocalRingAt R Λ q) := by
  -- The source-facing local fiber ring is defined to be exactly this localization.
  simpa [fiberLocalRingAt, fiberPrimeAt, hq]

/-- Helper for Lemma 15.51.2: property `(B)` on the fixed fiber over `p` is equivalent to checking
all local fibers above primes of `Λ` lying over `p`. -/
private theorem fiber_property_iff_forall_prime_local_fibers
    (p : PrimeSpectrum R) :
    P p.asIdeal.ResidueField (p.asIdeal.Fiber Λ) ↔
      ∀ q : PrimeSpectrum Λ,
        PrimeSpectrum.comap (algebraMap R Λ) q = p →
          P (q.asIdeal.under R).ResidueField (fiberLocalRingAt R Λ q) := by
  let A := p.asIdeal.Fiber Λ
  let _ : IsNoetherianRing A := fiber_isNoetherianRing (Λ := Λ) p
  have hcriterion :
      P p.asIdeal.ResidueField A ↔
        ∀ Q : PrimeSpectrum A,
          P p.asIdeal.ResidueField (Localization.AtPrime Q.asIdeal) :=
    FieldAlgebraProperty.HasPropertyB.localizationCriterion (P := P) p.asIdeal.ResidueField A
  -- Apply property `(B)` to the Noetherian fiber algebra and reindex its primes by the fiber
  -- spectrum equivalence.
  constructor
  · intro hP q hq
    have hlocal :
        ∀ Q : PrimeSpectrum A,
          P p.asIdeal.ResidueField (Localization.AtPrime Q.asIdeal) :=
      hcriterion.1 hP
    exact
      (fiber_local_ringAt_over_eq (P := P) p q hq).1 <|
        hlocal (PrimeSpectrum.preimageEquivFiber R Λ p ⟨q, hq⟩)
  · intro hlocal
    refine hcriterion.2 ?_
    intro Q
    let q := (PrimeSpectrum.preimageEquivFiber R Λ p).symm Q
    -- Rewrite the abstract prime of the fiber back to the corresponding prime of `Λ`.
    have hQ :
        (PrimeSpectrum.preimageEquivFiber R Λ p) q = Q :=
      (PrimeSpectrum.preimageEquivFiber R Λ p).apply_symm_apply Q
    have hlocalq :
        P (q.1.asIdeal.under R).ResidueField (fiberLocalRingAt R Λ q.1) :=
      hlocal q.1 q.2
    have hrew :
        P p.asIdeal.ResidueField (Localization.AtPrime Q.asIdeal) := by
      simpa [hQ] using
        (fiber_local_ringAt_over_eq (P := P) p q.1 q.2).2 hlocalq
    exact hrew

/-- Helper for Lemma 15.51.2: within the fixed fiber over `p`, every prime specializes to a
closed point of that same fiber. The lifted prime still lies over `p`, but at this stage it is
only a prime of `Λ`, not yet a global maximal ideal of `Λ`. -/
private theorem fiber_prime_over_closed_specialization_exists
    (p : PrimeSpectrum R) (q : PrimeSpectrum Λ)
    (hq : PrimeSpectrum.comap (algebraMap R Λ) q = p) :
    ∃ q' : PrimeSpectrum Λ, ∃ hq' : PrimeSpectrum.comap (algebraMap R Λ) q' = p,
      q.asIdeal ≤ q'.asIdeal ∧
      ((PrimeSpectrum.preimageOrderIsoFiber R Λ p) ⟨q', hq'⟩).asIdeal.IsMaximal := by
  classical
  let e := PrimeSpectrum.preimageOrderIsoFiber R Λ p
  let Q : PrimeSpectrum (p.asIdeal.Fiber Λ) := e ⟨q, hq⟩
  -- Choose a closed specialization of the corresponding prime inside the fixed fiber algebra.
  obtain ⟨mA, hmAmax, hQmA⟩ := Q.asIdeal.exists_le_maximal Q.2.1
  let M : PrimeSpectrum (p.asIdeal.Fiber Λ) := ⟨mA, hmAmax.isPrime⟩
  let q'over : PrimeSpectrum.comap (algebraMap R Λ) ⁻¹' {p} := e.symm M
  refine ⟨q'over.1, q'over.2, ?_, ?_⟩
  · have hQM : Q ≤ M := hQmA
    -- Transport the specialization order back across the fiber/order correspondence.
    simpa [Q, q'over] using (e.symm.monotone hQM : e.symm Q ≤ e.symm M)
  · have hmaxM : M.asIdeal.IsMaximal := by
      simpa [M] using hmAmax
    -- The chosen specialization is closed exactly because its fiber prime is maximal.
    simpa [q'over, e] using hmaxM

-- Proof sketch: for each `p : Spec(R)`, the prime spectrum of the fiber algebra
-- `p.asIdeal.Fiber Λ = κ(p) ⊗[R] Λ` is identified with the primes of `Λ` lying over `p` by
-- `PrimeSpectrum.preimageHomeomorphFiber`. Under that identification, clause `(2)` says exactly
-- that every localization of the fiber algebra at a prime has `P`. Clause `(3)` is the same
-- local test specialized to the maximal-local fiber `R_(m' ∩ R) → Λ_(m')`. Apply property `(B)`
-- to each Noetherian fiber algebra; Noetherianity comes from the Noetherian target ring `Λ`, and
-- the maximal-local clause is the corresponding specialization of the prime-local one.
/-- Lemma 15.51.2: let `R → Λ` be a ring map with `Λ` Noetherian, and let `P` be a
field-algebra property satisfying `(B)`. Then the following are equivalent: every fiber algebra
`κ(p) ⊗[R] Λ` has `P` over `κ(p)`; for every prime `q` of `Λ`, the local fiber ring at `q`,
equivalently the fiber of `R_(q ∩ R) → Λ_q`, has `P` over `κ(q ∩ R)`; and it suffices to test
that local condition only for maximal ideals `m'` of `Λ`, using the maximal-local fiber of
`R_(m' ∩ R) → Λ_(m')`. -/
theorem fiberProperty_tfae :
    ([ ∀ p : PrimeSpectrum R, P p.asIdeal.ResidueField (p.asIdeal.Fiber Λ)
      , ∀ q : PrimeSpectrum Λ, P (q.asIdeal.under R).ResidueField (fiberLocalRingAt R Λ q)
      , ∀ m' : MaximalSpectrum Λ,
          let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
          P (q.asIdeal.under R).ResidueField (fiberLocalRingAt R Λ q)
      ] : List Prop).TFAE := by
  -- Route correction: first identify the fixed-fiber prime-local criterion exactly, then isolate
  -- the remaining maximal-to-prime descent inside a single fiber algebra.
  tfae_have 1 ↔ 2 := by
    constructor
    · intro h₁ q
      exact
        (fiber_property_iff_forall_prime_local_fibers
          (P := P) (R := R) (Λ := Λ) (q.asIdeal.under R)).1
          (h₁ (q.asIdeal.under R)) q rfl
    · intro h₂ p
      exact
        (fiber_property_iff_forall_prime_local_fibers
          (P := P) (R := R) (Λ := Λ) p).2 h₂
  tfae_have 2 → 3 := by
    intro h₂ m'
    let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
    -- The maximal-local clause is the prime-local clause specialized to a maximal point.
    simpa [q] using h₂ q
  tfae_have 3 → 2 := by
    intro h₃ q
    let p : PrimeSpectrum R := q.asIdeal.under R
    -- Route correction: first move from `q` to a closed point of the fixed fiber over `p`.
    obtain ⟨q', hq', hqq', hq'max⟩ :=
      fiber_prime_over_closed_specialization_exists (R := R) (Λ := Λ) p q rfl
    -- TODO: the remaining source-faithful step must compare this closed point of the fixed fiber
    -- with the maximal-local hypothesis `h₃`, whose index type is `MaximalSpectrum Λ`. The current
    -- frontier is therefore a bridge from a closed point of `Spec (κ(p) ⊗[R] Λ)` back to a global
    -- maximal ideal of `Λ`, together with the transport from that maximal-local fiber to
    -- `fiberLocalRingAt R Λ q`.
    let _ := h₃
    let _ := hq'
    let _ := hqq'
    let _ := hq'max
    sorry
  tfae_finish

end

end Algebra
