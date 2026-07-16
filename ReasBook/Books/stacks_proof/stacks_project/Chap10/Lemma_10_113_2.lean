import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_113_1.DimensionInequality

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
  [Algebra A B] [Algebra (FractionRing A) (FractionRing B)]
  [IsScalarTower A (FractionRing A) (FractionRing B)]
  [FiniteDimensional (FractionRing A) (FractionRing B)]

omit [IsDomain B] [Algebra A B] [IsScalarTower A (FractionRing A) (FractionRing B)] in
/-- Helper for Chap10 Lemma 10 113 2: the finite fraction-field extension has transcendence
degree zero. -/
private lemma fractionRing_trdeg_eq_zero_of_finiteDimensional :
    Algebra.trdeg (FractionRing A) (FractionRing B) = 0 := by
  -- Finite-dimensional field extensions are algebraic, and algebraic extensions have zero
  -- transcendence degree.
  simpa using (trdeg_eq_zero (R := FractionRing A) (A := FractionRing B))

omit [IsDomain B] [Algebra A B] [IsScalarTower A (FractionRing A) (FractionRing B)] in
/-- Helper for Chap10 Lemma 10 113 2: the natural-number generic transcendence term vanishes
for the finite fraction-field extension in this target. -/
private lemma fractionRing_trdeg_toNat_eq_zero_of_finiteDimensional :
    Cardinal.toNat (Algebra.trdeg (FractionRing A) (FractionRing B)) = 0 := by
  -- Apply `Cardinal.toNat` to the zero transcendence-degree computation.
  simpa using
    congrArg Cardinal.toNat
      (fractionRing_trdeg_eq_zero_of_finiteDimensional (A := A) (B := B))

omit [Algebra (FractionRing A) (FractionRing B)]
    [IsScalarTower A (FractionRing A) (FractionRing B)]
    [FiniteDimensional (FractionRing A) (FractionRing B)] in
/-- Helper for Chap10 Lemma 10 113 2: every prime over a height-one source prime is nonzero,
so its prime height is at least one. -/
private lemma one_le_primeHeight_of_primesOver_height_one
    [IsNoetherianRing A] [Algebra.FiniteType A B]
    (hinj : Function.Injective (algebraMap A B))
    {p : Ideal A} [p.IsPrime] (hp : Ideal.primeHeight p = 1)
    (q : p.primesOver B) :
    (1 : ℕ∞) ≤ Ideal.primeHeight q.1 := by
  -- First show that the height-one source prime cannot be the zero prime of the domain.
  have hbot_height : Ideal.primeHeight (⊥ : Ideal A) = 0 := by
    rw [Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]
    simp
  have hp_ne_bot : p ≠ ⊥ := by
    intro hp_bot
    simpa [hp_bot, hbot_height] using hp
  -- Injectivity makes the contraction of the zero ideal of `B` the zero ideal of `A`, so a prime
  -- over nonzero `p` is itself nonzero.
  have hunder_bot : Ideal.under A (⊥ : Ideal B) = ⊥ := by
    simpa [Ideal.under_def] using Ideal.comap_bot_of_injective (algebraMap A B) hinj
  have hq_ne_bot : q.1 ≠ ⊥ := by
    intro hq_bot
    have hq_under : q.1.under A = p := by
      simpa using (Ideal.LiesOver.over (P := q.1) (p := p)).symm
    apply hp_ne_bot
    rw [← hq_under, hq_bot, hunder_bot]
  -- Strict containment above the zero prime raises prime height by one.
  have hbot_lt : (⊥ : Ideal B) < q.1 := bot_lt_iff_ne_bot.mpr hq_ne_bot
  have hbot_height_B : Ideal.primeHeight (⊥ : Ideal B) = 0 := by
    rw [Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]
    simp
  simpa [hbot_height_B] using
    (Ideal.primeHeight_add_one_le_of_lt (I := (⊥ : Ideal B)) (J := q.1) hbot_lt)

/-- Helper for Chap10 Lemma 10 113 2: Lemma 10.113.1 bounds the natural-number height of every
prime over a height-one source prime by one. -/
private lemma primeHeight_toNat_le_one_of_primesOver_height_one
    [IsNoetherianRing A] [Algebra.FiniteType A B]
    (hinj : Function.Injective (algebraMap A B))
    {p : Ideal A} [p.IsPrime] (hp : Ideal.primeHeight p = 1)
    (q : p.primesOver B) :
    ENat.toNat (Ideal.primeHeight q.1) ≤ 1 := by
  -- Route correction: use the Lemma 10.113.1 dimension inequality shape directly instead of
  -- recreating its generic-fiber bridge lemmas locally; until that owner compiles, consume the
  -- isolated predecessor statement above.
  have hbound :
      ENat.toNat (Ideal.primeHeight q.1) +
          Cardinal.toNat (Algebra.trdeg p.ResidueField q.1.ResidueField) ≤
        ENat.toNat (Ideal.primeHeight p) +
          Cardinal.toNat (Algebra.trdeg (FractionRing A) (FractionRing B)) :=
    primeHeight_add_residueFieldTrdeg_le_primeHeight_add_fractionRing_trdeg_of_finiteType
      (R := A) (S := B) hinj p q.1 (show q.1.LiesOver p from inferInstance)
  have hpNat : ENat.toNat (Ideal.primeHeight p) = 1 := by
    simpa [hp]
  have hgeneric : Cardinal.toNat (Algebra.trdeg (FractionRing A) (FractionRing B)) = 0 :=
    fractionRing_trdeg_toNat_eq_zero_of_finiteDimensional (A := A) (B := B)
  have hbound' :
      ENat.toNat (Ideal.primeHeight q.1) +
          Cardinal.toNat (Algebra.trdeg p.ResidueField q.1.ResidueField) ≤ 1 := by
    simpa [hpNat, hgeneric] using hbound
  -- The residue-field transcendence term is a natural number, so dropping it preserves the bound.
  omega

/-- Helper for Chap10 Lemma 10 113 2: convert the natural-number upper bound from the dimension
inequality back to the `ℕ∞` prime-height order. -/
private lemma primeHeight_le_one_of_primesOver_height_one
    [IsNoetherianRing A] [Algebra.FiniteType A B]
    (hinj : Function.Injective (algebraMap A B))
    {p : Ideal A} [p.IsPrime] (hp : Ideal.primeHeight p = 1)
    (q : p.primesOver B) :
    Ideal.primeHeight q.1 ≤ (1 : ℕ∞) := by
  -- Noetherianity makes the target prime height finite, so `toNat` faithfully reflects the
  -- `ℕ∞` value for the final comparison.
  letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have hfinite : Ideal.primeHeight q.1 ≠ ⊤ := Ideal.primeHeight_ne_top q.1
  rw [← ENat.coe_toNat hfinite]
  exact_mod_cast
    primeHeight_toNat_le_one_of_primesOver_height_one
      (A := A) (B := B) hinj hp q

/-- Helper for Chap10 Lemma 10 113 2: over a height-one prime, the interval argument forces
every prime in the fiber owner set to have height one. -/
private lemma primeHeight_eq_one_of_primesOver_height_one
    [IsNoetherianRing A] [Algebra.FiniteType A B]
    (hinj : Function.Injective (algebraMap A B))
    {p : Ideal A} [p.IsPrime] (hp : Ideal.primeHeight p = 1) :
    ∀ q : p.primesOver B, Ideal.primeHeight q.1 = 1 := by
  -- Route correction: the planned aggregate import for Lemma 10.113.1 is currently unbuildable, so
  -- the main proof isolates exactly the missing height conclusion instead of depending on that file.
  intro q
  -- The lower bound is local: lying over a nonzero height-one prime makes `q` nonzero.
  have hlower : (1 : ℕ∞) ≤ Ideal.primeHeight q.1 :=
    one_le_primeHeight_of_primesOver_height_one
      (A := A) (B := B) hinj hp q
  have hupper : Ideal.primeHeight q.1 ≤ (1 : ℕ∞) := by
    -- The remaining natural-number upper-bound helper gives the upper side of antisymmetry.
    exact primeHeight_le_one_of_primesOver_height_one
      (A := A) (B := B) hinj hp q
  exact le_antisymm hupper hlower

omit [IsDomain A] [IsDomain B] [Algebra (FractionRing A) (FractionRing B)]
    [IsScalarTower A (FractionRing A) (FractionRing B)]
    [FiniteDimensional (FractionRing A) (FractionRing B)] in
/-- Helper for Chap10 Lemma 10 113 2: if all primes over `p` have height one, then the canonical
fiber ring over `p` is zero-dimensional. -/
private lemma fiber_krullDimLE_zero_of_primeHeight_eq_one_primesOver
    {p : Ideal A} [p.IsPrime]
    (hheight : ∀ q : p.primesOver B, Ideal.primeHeight q.1 = 1) :
    Ring.KrullDimLE 0 (p.Fiber B) := by
  refine Ring.KrullDimLE.mk₀ fun I hI ↦ ?_
  let x : PrimeSpectrum (p.Fiber B) := ⟨I, hI⟩
  refine (PrimeSpectrum.isMax_iff (x := x)).mp ?_
  rw [isMax_iff_forall_not_lt]
  intro y hxy
  let e := PrimeSpectrum.primesOverOrderIsoFiber A B p
  let qx : p.primesOver B := e.symm x
  let qy : p.primesOver B := e.symm y
  -- A strict specialization in the fiber transports to a strict containment among primes over `p`,
  -- which would raise the prime height by one.
  have hq_lt : qx < qy := by
    exact e.symm.strictMono hxy
  have hideal_lt : qx.1 < qy.1 := hq_lt
  have hstep : Ideal.primeHeight qx.1 + 1 ≤ Ideal.primeHeight qy.1 :=
    Ideal.primeHeight_add_one_le_of_lt hideal_lt
  rw [hheight qx, hheight qy] at hstep
  norm_num at hstep

omit [IsDomain A] [IsDomain B] [Algebra (FractionRing A) (FractionRing B)]
    [IsScalarTower A (FractionRing A) (FractionRing B)]
    [FiniteDimensional (FractionRing A) (FractionRing B)] in
/-- Helper for Chap10 Lemma 10 113 2: a zero-dimensional finite-type fiber over the residue field
has only finitely many primes over the base prime. -/
private lemma finite_primesOver_of_fiber_krullDimLE_zero
    [Algebra.FiniteType A B] {p : Ideal A} [p.IsPrime]
    (hdim : Ring.KrullDimLE 0 (p.Fiber B)) :
    Finite (p.primesOver B) := by
  -- Finite type over the Artinian residue field converts zero-dimensionality into module
  -- finiteness, then into an Artinian fiber ring with finite prime spectrum.
  letI : Module.Finite p.ResidueField (p.Fiber B) :=
    (Module.finite_iff_krullDimLE_zero p.ResidueField (p.Fiber B)).mpr hdim
  letI : IsArtinianRing (p.Fiber B) := IsArtinianRing.of_finite p.ResidueField (p.Fiber B)
  have hfiber : Finite (PrimeSpectrum (p.Fiber B)) := inferInstance
  exact Finite.of_equiv (PrimeSpectrum (p.Fiber B))
    (PrimeSpectrum.primesOverOrderIsoFiber A B p).symm.toEquiv

/-
Domain triage:
* primary domain: finite-type maps of domains, the height-one fiber over a prime, and the induced
  fraction-ring extension;
* source-facing layer: the finite fiber `p.primesOver B` over a height-one prime and the height of
  each prime in that fiber;
* core/canonical owners sampled for this refinement:
  `FiniteDimensional (FractionRing A) (FractionRing B)`,
  `Algebra (FractionRing A) (FractionRing B)`,
  `IsScalarTower A (FractionRing A) (FractionRing B)`,
  `Ideal.primesOver`,
  `primeHeight_le_primeHeight_add_trdeg_sub_residueFieldTrdeg_of_finiteType`,
  `isMaximal_of_liesOver_of_isAlgebraic_residueField`;
* bridge/view: no extra wrapper is needed here, since the source statement already lives on the
  canonical owner set `p.primesOver B`.

Primitive data are the rings `A`, `B`, the canonical finite-dimensional fraction-field extension
`Frac(A) → Frac(B)`, and the height-one prime `p`. The injectivity of `A → B` is derived
internally from
`algebraMap_injective_of_field_isFractionRing A B (FractionRing A) (FractionRing B)` and the given
fraction-field tower. The public theorem is
derived API on the owner set `p.primesOver B`. -/

-- Proof sketch: first derive injectivity of `A → B` from the fraction-field tower via
-- `algebraMap_injective_of_field_isFractionRing`, then apply Lemma `10.113.1` with transcendence
-- degree `0`, since a finite extension of fraction fields is algebraic. For every `q` over `p`,
-- the dimension inequality forces
-- `primeHeight q = 1`, and the residue-field extension `κ(q) / κ(p)` is algebraic. Hence each such
-- `q` is a closed point of the fiber over `p` by Lemma `10.35.9`. The fiber is Noetherian because
-- `B` is finite type over the Noetherian ring `A`, so its prime spectrum is a Noetherian space;
-- a Noetherian space all of whose points are closed is finite, yielding finiteness of
-- `p.primesOver B`.
/-- Helper for Chap10 Lemma 10 113 2: the final fiber argument only needs an explicit
injectivity hypothesis on the source algebra map. -/
private lemma finite_primesOver_and_primeHeight_eq_one_of_primeHeight_eq_one_of_injective
    [IsNoetherianRing A] [Algebra.FiniteType A B]
    (hinj : Function.Injective (algebraMap A B))
    (p : Ideal A) [p.IsPrime] (hp : Ideal.primeHeight p = 1) :
    Finite (p.primesOver B) ∧ ∀ q : p.primesOver B, Ideal.primeHeight q.1 = 1 := by
  -- Lemma 10.113.1 turns the generic fraction-field data into the height-one invariant over `p`.
  have hheight : ∀ q : p.primesOver B, Ideal.primeHeight q.1 = 1 :=
    primeHeight_eq_one_of_primesOver_height_one
      (A := A) (B := B) hinj hp
  -- The invariant rules out nontrivial chains in the canonical fiber.
  have hdim : Ring.KrullDimLE 0 (p.Fiber B) :=
    fiber_krullDimLE_zero_of_primeHeight_eq_one_primesOver
      (A := A) (B := B) hheight
  -- A finite-type zero-dimensional fiber over a field has finite prime spectrum.
  have hfinite : Finite (p.primesOver B) :=
    finite_primesOver_of_fiber_krullDimLE_zero (A := A) (B := B) hdim
  exact ⟨hfinite, hheight⟩

omit [FiniteDimensional (FractionRing A) (FractionRing B)] in
/-- Helper for Chap10 Lemma 10 113 2: the fraction-field tower hypotheses force the source
algebra map to be injective. -/
private lemma algebraMap_injective_of_fractionRing_tower :
    Function.Injective (algebraMap A B) := by
  -- The canonical map to the fraction field of `B` factors through `Frac(A)`, so an element of
  -- `A` killed in `B` is already killed in the fraction field of `A`.
  exact algebraMap_injective_of_field_isFractionRing A B (FractionRing A) (FractionRing B)

/-- Chap10 Lemma 10 113 2: if `A → B` is a finite type map of domains, `A` is Noetherian, the induced
extension of fraction rings is finite, and `p` is a height-one prime of `A`, then there are only
finitely many prime ideals of `B` lying over `p`, and every such prime also has height one. Under
the fraction-field tower hypotheses, injectivity of `A → B` is automatic. -/
@[stacks 02MA]
theorem finite_primesOver_and_primeHeight_eq_one_of_primeHeight_eq_one
    [IsNoetherianRing A] [Algebra.FiniteType A B]
    (p : Ideal A) [p.IsPrime] (hp : Ideal.primeHeight p = 1) :
    Finite (p.primesOver B) ∧ ∀ q : p.primesOver B, Ideal.primeHeight q.1 = 1 := by
  -- The fraction-field tower supplies injectivity, so the explicit-injectivity helper applies.
  have hinj : Function.Injective (algebraMap A B) :=
    algebraMap_injective_of_fractionRing_tower (A := A) (B := B)
  exact
    finite_primesOver_and_primeHeight_eq_one_of_primeHeight_eq_one_of_injective
      (A := A) (B := B) hinj p hp

end
