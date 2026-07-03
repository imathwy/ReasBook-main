import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_125_1 (from Chap10) -/
noncomputable section

universe u v

section

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]

/-- Definition 10.125.1 (1): for a prime `q : Spec S`, the relative dimension of `S/R` at `q`
is the Krull dimension of the local ring of the fiber `κ(q ∩ R) ⊗[R] S` at the prime
corresponding to `q`. -/
noncomputable abbrev relativeDimensionAt (q : PrimeSpectrum S) : WithBot ℕ∞ :=
  ringKrullDim (fiberLocalRingAt R S q)

/-- Definition 10.125.1 (2): the relative dimension of `S/R` is the supremum of the relative
dimensions at all primes `q : Spec S`. -/
noncomputable abbrev relativeDimension : WithBot ℕ∞ :=
  ⨆ q : PrimeSpectrum S, relativeDimensionAt R S q

end

/-! ### Lemma_10_125_2 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/- Domain-style sampling:
- primary domain: relative fiber dimension and quasi-finite polynomial presentations of
  localizations of finite-type algebras;
- sampled owner declarations:
  `relativeDimensionAt`,
  `fiberLocalRingAt`,
  `RingHom.QuasiFinite`,
  `Algebra.QuasiFiniteAt`;
- best owner abstraction: the local fiber-dimension owner `relativeDimensionAt`, together with the
  canonical morphism-level quasi-finite predicate on the witnessing polynomial map.

Source/core/bridge triage:
- `source-facing`: the existence of a localization `S_g` and a quasi-finite map
  `R[t₁, ..., tₙ] → S_g`;
- `core/canonical`: `relativeDimensionAt`, `fiberLocalRingAt`, and `RingHom.QuasiFinite`;
- `bridge/view`: passing from the fiber-local dimension statement to a polynomial presentation of
  a localization away from an element `g ∉ q`.

Primitive data are only the prime `q`, the integer `n`, and the relative-dimension equality. The
map `MvPolynomial (Fin n) R →ₐ[R] Localization.Away g` is the source-facing witness itself, while
its quasi-finiteness should be expressed by the canonical owner predicate on the morphism, not via
an explicit `toRingHom` projection in the public theorem surface.
-/

-- Proof sketch: let `p = q.asIdeal.under R` and identify the fiber through `q` with
-- `Spec ((q.asIdeal.under R).Fiber S)`. The hypothesis `relativeDimensionAt R S q = n` says that
-- this fiber has local dimension `n` at the corresponding point. Shrink to a basic open
-- neighbourhood of that fiber point of dimension `n`, apply the finite-type-over-a-field
-- Noether-normalization statement to the fiber ring to obtain `n` algebraically independent
-- coordinates, and then use openness of the quasi-finite locus to lift the resulting
-- quasi-finite-at-`q` polynomial presentation to a localization `S_g`.
/-- Lemma 10.125.2: let `R → S` be a finite type ring map, let `q : Spec(S)` be a prime, and
assume the relative dimension `dim_q(S/R)`, formalized as `relativeDimensionAt R S q`, is `n`.
Then there exists `g ∈ S` with `g ∉ q` such that `S_g`, formalized as `Localization.Away g`, is
quasi-finite over the polynomial algebra `R[t₁, …, tₙ]`, formalized as `MvPolynomial (Fin n) R`. -/
theorem exists_quasiFinite_polynomial_localizationAway_of_relativeDimensionAt_eq
    (n : ℕ) (q : PrimeSpectrum S) (hq : relativeDimensionAt R S q = (n : WithBot ℕ∞)) :
    ∃ g : S, g ∉ q.asIdeal ∧
      ∃ φ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g,
        φ.QuasiFinite := sorry

end

/-! ### Lemma_10_125_3 (from Chap10) -/
noncomputable section

open MvPolynomial

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/- Domain-style sampling:
- primary domain: relative fiber dimension, quasi-finite localizations, and the coordinate-ideal
  normal form for primes in polynomial algebras over residue fields;
- sampled owner declarations:
  `relativeDimensionAt`,
  `tailVariablesIdeal`,
  `exists_quasiFinite_polynomial_localizationAway_of_relativeDimensionAt_eq`,
  `exists_finite_selfAlgHom_comap_eq_tailVariablesIdeal`;
- best owner abstraction: the primewise owner `q : PrimeSpectrum S`, with the base prime recovered
  canonically as `q.asIdeal.under R`;
- primitive data: the prime `q`, the integer `n`, and the relative-dimension equality;
- derived API: the contracted base prime, its residue field, and the localized extension/tail ideal
  expressions appearing in the conclusion.

Source/core/bridge triage:
- `source-facing`: the existence of localizations `R_f` and `S_g` together with a quasi-finite
  polynomial presentation whose contracted prime is the extension of `q` with the expected tail
  variables;
- `core/canonical`: `relativeDimensionAt`, `tailVariablesIdeal`, and the quasi-finite owner on the
  witnessing ring homomorphism;
- `bridge/view`: the explicit ideal expressions
  `Ideal.map (algebraMap S (Localization.Away g)) q.asIdeal` and
  `Ideal.map (algebraMap R (MvPolynomial (Fin n) (Localization.Away f)))
    (q.asIdeal.under R) ⊔ tailVariablesIdeal _ _ _`.

The two deleted local wrappers were one-off bridges, not owner declarations. Keeping the theorem
indexed only by `q` matches the chapter's primewise API discipline and removes redundant primitive
data without changing the source mathematics.
-/

-- Proof sketch: first apply Lemma `10.125.2` to replace `S` near `q` by a quasi-finite
-- localization over a polynomial algebra in `n` variables. Then use Lemma `10.115.6` on the fiber
-- over `q ∩ R` to change coordinates so that the contracted prime becomes the tail coordinate
-- ideal,
-- lift the resulting coordinates from the fiber to a localization `R_f`, and finally shrink once
-- more using openness of the quasi-finite locus from Lemma `10.123.13`.
/-- Lemma 10.125.3: let `R → S` be a finite type ring map, let `q : Spec(S)`, and assume
`relativeDimensionAt R S q = n`. Then after inverting some `f ∉ q ∩ R` and some `g ∉ q`, there
exists a quasi-finite ring map from the polynomial ring
`(Localization.Away f)[x₁, …, xₙ]` to `Localization.Away g` whose inverse image of the localized
prime `qS_g` is exactly the ideal generated by the extension of `q ∩ R` together with the tail
variables `x_{r+1}, …, xₙ`, where
`r = trdeg_{κ(q ∩ R)} κ(q)`. -/
theorem exists_quasiFinite_localizedPolynomial_ringHom_comap_eq_localizedPrimeAndTailIdeal
    (q : PrimeSpectrum S) (n : ℕ)
    (hdim : relativeDimensionAt R S q = (n : WithBot ℕ∞)) :
    ∃ f : R, f ∉ q.asIdeal.under R ∧
      ∃ g : S, g ∉ q.asIdeal ∧
        ∃ φ : MvPolynomial (Fin n) (Localization.Away f) →+* Localization.Away g,
          φ.QuasiFinite ∧
            Ideal.comap φ (Ideal.map (algebraMap S (Localization.Away g)) q.asIdeal) =
                Ideal.map
                  (algebraMap R (MvPolynomial (Fin n) (Localization.Away f)))
                  (q.asIdeal.under R) ⊔
                tailVariablesIdeal (Localization.Away f) n
                  (Cardinal.toNat
                    (Algebra.trdeg (q.asIdeal.under R).ResidueField
                      q.asIdeal.ResidueField)) :=
  sorry

end

/-! ### Lemma_10_125_4 (from Chap10) -/
universe u v

/-
Domain-style sampling:
- primary domain: quasi-finite localizations of finite-type commutative-algebra maps and Krull
  dimension comparisons at primes;
- sampled owner declarations:
  `Algebra.QuasiFiniteAt`,
  `Ideal.under`,
  `ringKrullDim_localizationAtPrime_le_ringKrullDim_localizationAtPrime_add_ringKrullDim_fiberLocalRingAt_of_liesOver`,
  `ringKrullDim_le_of_isIntegral`;
- best owner abstraction: the primewise owner `Algebra.QuasiFiniteAt R q`, with the base prime
  recovered canonically as `q.under R`;
- primitive data: the target prime `q` and the canonical quasi-finite owner structure;
- derived API: the base prime `p` together with `[q.LiesOver p]`, which are redundant once `q` is
  fixed.

This item is therefore kept at the `source-facing` layer as the local-dimension inequality, but
its public interface is refined to the canonical owner shape indexed only by `q`.
-/

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

-- Proof sketch: apply Zariski's main theorem at `q` to replace `S_q` by the localization at a
-- prime of the integral closure of `R_p` in `S_p`; then use the integral-extension dimension bound
-- from Lemma `10.112.3` for that integral closure over `R_p`.
/-- Lemma 10.125.4: for a finite type ring map `R → S`, if `q` is a prime ideal of `S` and the
map is quasi-finite at `q`, then the Krull dimension of the local ring `S_q` is at most the Krull
dimension of the local ring `R_(q ∩ R)`. -/
theorem ringKrullDim_localizationAtPrime_le_of_quasiFiniteAt
    (q : Ideal S) [q.IsPrime] [Algebra.QuasiFiniteAt R q] :
    ringKrullDim (Localization.AtPrime q) ≤ ringKrullDim (Localization.AtPrime (q.under R)) := sorry

end

/-! ### Lemma_10_125_5 (from Chap10) -/
universe u v

/-
Domain-style sampling:
- primary domain: Krull-dimension bounds for quasi-finite maps from polynomial algebras over a
  field;
- sampled owner declarations:
  `Algebra.QuasiFinite`,
  `Algebra.FiniteType.of_restrictScalars_finiteType`,
  `ringKrullDim_localizationAtPrime_le_of_quasiFiniteAt`,
  `ringKrullDim_le_iff_isMaximal_height_le`;
- best owner abstraction: the global owner `Algebra.QuasiFinite (MvPolynomial (Fin n) k) S`,
  with the primewise local-dimension inequality as derived API;
- primitive data: the polynomial-algebra structure on `S` and the ambient finite-type
  `k`-algebra structure, which canonically yields finite type over `MvPolynomial (Fin n) k` by
  restriction of scalars;
- derived API: quasi-finiteness at each prime of `S` and the maximal-ideal height bounds used to
  recover `ringKrullDim S ≤ n`.

Source/core/bridge triage:
- `source-facing`: the global dimension bound `ringKrullDim S ≤ n`;
- `core/canonical`: `Algebra.QuasiFinite`, `ringKrullDim`, and the polynomial-ring dimension
  theorem `MvPolynomial.ringKrullDim_of_isNoetherianRing`;
- `bridge/view`: finite-type restriction of scalars and the local bound
  `ringKrullDim_localizationAtPrime_le_of_quasiFiniteAt`.
-/
-- Proof sketch: for each prime `q` of `S`, let `p` be its contraction to `k[t₁, …, tₙ]`.
-- Lemma `10.125.4` gives `dim S_q ≤ dim (k[t₁, …, tₙ])_p`. The latter is bounded by `n` via the
-- canonical height formula for localizations at primes together with the polynomial-ring dimension
-- theorem `MvPolynomial.ringKrullDim_of_isNoetherianRing`. Applying this bound to every maximal
-- ideal of `S` and invoking `ringKrullDim_le_iff_isMaximal_height_le` yields the result.
/-- Lemma 10.125.5: if `S` is a finite type `k`-algebra and `k[t_1, \ldots, t_n] → S`,
formalized by `MvPolynomial (Fin n) k → S`, is quasi-finite, then the Krull dimension of `S` is at
most `n`. -/
theorem ringKrullDim_le_of_quasiFinite_mvPolynomial_algebra
    {k : Type u} [Field k] {n : ℕ}
    {S : Type v} [CommRing S] [Algebra k S]
    [Algebra (MvPolynomial (Fin n) k) S]
    [IsScalarTower k (MvPolynomial (Fin n) k) S]
    [Algebra.FiniteType k S] [Algebra.QuasiFinite (MvPolynomial (Fin n) k) S] :
    ringKrullDim S ≤ n := by
  have hmv :
      ringKrullDim (MvPolynomial (Fin n) k) =
        ringKrullDim k + Nat.card (Fin n) :=
    MvPolynomial.ringKrullDim_of_isNoetherianRing
  letI : Algebra.FiniteType (MvPolynomial (Fin n) k) S :=
    Algebra.FiniteType.of_restrictScalars_finiteType k (MvPolynomial (Fin n) k) S
  refine (ringKrullDim_le_iff_isMaximal_height_le n).2 fun q hq ↦ ?_
  letI : q.IsPrime := hq.isPrime
  rw [← IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)]
  have hq :
      ringKrullDim (Localization.AtPrime q) ≤
        ringKrullDim (Localization.AtPrime (q.under (MvPolynomial (Fin n) k))) :=
    ringKrullDim_localizationAtPrime_le_of_quasiFiniteAt q
  refine hq.trans ?_
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (q.under (MvPolynomial (Fin n) k))
    (Localization.AtPrime (q.under (MvPolynomial (Fin n) k)))]
  refine le_trans (Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top') ?_
  simp [hmv]

/-! ### Lemma_10_125_6 (from Chap10) -/
open TopologicalSpace

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- 
Domain-style sampling:
- primary domain: local relative fiber dimension on `Spec(S)` and the corresponding bounded
  locus;
- sampled owner declarations of the same kind:
  `relativeDimensionAt`,
  `Module.flatOverBaseLocus`,
  `Module.mem_flatOverBaseLocus`,
  `Module.isOpen_flatOverBaseLocus_of_finitePresentation`;
- best owner abstraction: the bounded-dimension locus
  `{ q : PrimeSpectrum S | relativeDimensionAt R S q ≤ n }` should be a named owner on
  `PrimeSpectrum S`, while the source-facing theorem remains the equality-at-the-point
  neighborhood statement from the Stacks lemma and the locus-membership version is only companion
  API.

Source/core/bridge triage:
- `source-facing`: the equality-at-the-point neighborhood statement of Lemma `10.125.6`;
- `core/canonical`: `relativeDimensionAt` and the induced bounded-dimension locus owner;
- `bridge/view`: the membership lemma for the named locus and the strengthened
  locus-membership-neighborhood formulation.

Primitive data are only `n` and the prime `q`; the repeated inequality
`relativeDimensionAt R S q ≤ n` is derived API from the locus owner.
-/

/-- The locus in `Spec(S)` where the relative dimension of `S/R` is at most `n`. -/
def relativeDimensionAtLELocus (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (n : ℕ) : Set (PrimeSpectrum S) :=
  { q : PrimeSpectrum S | relativeDimensionAt R S q ≤ (n : WithBot ℕ∞) }

-- Proof sketch: unfold `relativeDimensionAtLELocus`.
/-- Membership in `relativeDimensionAtLELocus` means that the local fiber dimension is at most
`n`. -/
theorem mem_relativeDimensionAtLELocus (n : ℕ) (q : PrimeSpectrum S) :
    q ∈ relativeDimensionAtLELocus R S n ↔ relativeDimensionAt R S q ≤ (n : WithBot ℕ∞) := sorry

variable [Algebra.FiniteType R S]

/-- Lemma 10.125.6: let `R → S` be a finite type ring map, let `q : Spec(S)` be a prime, and
assume the relative dimension of `S/R` at `q` is exactly `n`. Then there exists an open
neighbourhood of `q` in `Spec(S)` contained in `relativeDimensionAtLELocus R S n`, i.e. on which
the relative fiber dimension is everywhere at most `n`. -/
theorem exists_openNhdsOf_relativeDimensionAt_eq
    (n : ℕ) (q : PrimeSpectrum S) (hq : relativeDimensionAt R S q = (n : WithBot ℕ∞)) :
    ∃ U : OpenNhdsOf q, ∀ q' ∈ U, q' ∈ relativeDimensionAtLELocus R S n := sorry

-- Proof sketch: if `q ∈ relativeDimensionAtLELocus R S n`, let `m := relativeDimensionAt R S q`.
-- The equality-case argument at the actual local dimension `m` gives an open neighborhood of `q`
-- contained in the `≤ m` locus; since `m ≤ n`, that neighborhood is also contained in the
-- `≤ n` locus.
/-- Companion strengthening: if `q` already lies in the bounded-dimension locus
`relativeDimensionAtLELocus R S n`, then there is an open neighbourhood of `q` contained in that
locus. -/
theorem exists_openNhdsOf_mem_relativeDimensionAtLELocus
    (n : ℕ) (q : PrimeSpectrum S) (hq : q ∈ relativeDimensionAtLELocus R S n) :
    ∃ U : OpenNhdsOf q, ∀ q' ∈ U, q' ∈ relativeDimensionAtLELocus R S n := by
  sorry

end

/-! ### Lemma_10_125_7 (from Chap10) -/
open scoped TensorProduct
open Algebra.TensorProduct

noncomputable section

universe u v w

section

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

/- 
Domain-style sampling:
- primary domain: base change of source-facing loci on `PrimeSpectrum` defined by a local fiber
  invariant attached to a ring map;
- sampled owner declarations of the same kind:
  `relativeDimensionAtLELocus`,
  `smoothLocus_baseChange_preimage_eq`,
  `cohenMacaulayFiberLocus_baseChange_preimage_eq`;
- best owner abstraction: the upstream named locus owner `relativeDimensionAtLELocus`, with the
  base-change theorem stated as equality for that owner rather than as a raw set-builder identity;
- primitive data: the algebra `R → S`, the base change `R → R'`, and the bound `n`;
- derived API: the preimage formula for the named locus.

Source/core/bridge triage:
* `source-facing`: the locus where the relative dimension of `S/R` is at most `n`;
* `core/canonical`: `relativeDimensionAt` and the upstream owner `relativeDimensionAtLELocus`;
* `bridge/view`: inverse image along `Spec(R' ⊗[R] S) → Spec(S)` induced by `includeRight`.
-/

variable [Algebra.FiniteType R S]

-- Proof sketch: for `q' : Spec(R' ⊗[R] S)`, let `q` be its image in `Spec(S)`. The fiber of
-- `Spec(S') → Spec(R')` at `q' ∩ R'` is canonically the same finite type algebra over the same
-- residue field as the fiber of `Spec(S) → Spec(R)` at `q ∩ R`; equivalently, the corresponding
-- local fiber rings have equal Krull dimension. Apply Lemma `10.116.6` to this residue-field base
-- change of fibers and then extensionality of inverse images.
/-- Lemma 10.125.7: for a finite type ring map `R → S`, an arbitrary base change `R → R'`, and
`S' = R' ⊗[R] S`, the inverse image in `Spec(S')` of the locus where the relative dimension
`dim_q(S/R)` is at most `n` is exactly the locus where the relative dimension
`dim_q(S'/R')` is at most `n`. -/
theorem relativeDimensionAt_le_preimage_eq_baseChange (n : ℕ) :
    PrimeSpectrum.comap includeRight.toRingHom ⁻¹'
        relativeDimensionAtLELocus R S n =
      relativeDimensionAtLELocus R' (R' ⊗[R] S) n := sorry

end

/-! ### Lemma_10_125_8 (from Chap10) -/
open TopologicalSpace

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FinitePresentation R S]

/- 
Domain-style sampling:
- primary domain: source-facing loci on `Spec(S)` cut out by local fiber invariants of a finite
  presentation ring map, together with their topological finiteness properties;
- sampled owner declarations of the same kind:
  `relativeDimensionAtLELocus`,
  `exists_openNhdsOf_mem_relativeDimensionAtLELocus`,
  `Module.flatOverBaseLocus`,
  `Module.isOpen_flatOverBaseLocus_of_finitePresentation`;
- best owner abstraction: the named locus owner `relativeDimensionAtLELocus`; openness and
  quasi-compactness are derived API of that owner rather than new primitive data;
- primitive data: the finite presentation map `R → S` and the bound `n`;
- derived API: the open and compactness statements for the owner locus.

Source/core/bridge triage:
- `source-facing`: the Stacks statement that the bounded relative-dimension locus is open and
  quasi-compact;
- `core/canonical`: the owner `relativeDimensionAtLELocus R S n`;
- `bridge/view`: the separate `IsOpen` and `IsCompact` companion theorems below.
-/

-- Proof sketch: openness is exactly the local neighborhood criterion from
-- `exists_openNhdsOf_mem_relativeDimensionAtLELocus`.
/-- The locus where the relative dimension of a finitely presented algebra is at most `n` is open
in `Spec(S)`. -/
theorem isOpen_relativeDimensionAtLELocus_of_finitePresentation (n : ℕ) :
    IsOpen (relativeDimensionAtLELocus R S n) := by
  rw [isOpen_iff_mem_nhds]
  intro q hq
  rcases exists_openNhdsOf_mem_relativeDimensionAtLELocus n q hq with ⟨U, hU⟩
  exact Filter.mem_of_superset (U.isOpen.mem_nhds U.mem) hU

-- Proof sketch: descend the finite presentation to a finite type `ℤ`-model, identify the locus by
-- `relativeDimensionAt_le_preimage_eq_baseChange`, and use quasi-compactness of open subsets of the
-- Noetherian spectrum downstairs.
/-- The locus where the relative dimension of a finitely presented algebra is at most `n` is
quasi-compact in `Spec(S)`. -/
theorem isCompact_relativeDimensionAtLELocus_of_finitePresentation (n : ℕ) :
    IsCompact (relativeDimensionAtLELocus R S n) := sorry

-- Proof sketch: openness is the pointwise neighborhood statement of Lemma `10.125.6`. For
-- quasi-compactness, descend the finite presentation to a finitely generated `ℤ`-subalgebra of
-- the source, identify the locus with the inverse image of the corresponding locus after base
-- change using Lemma `10.125.7`, and use that open subsets of the Noetherian spectrum downstairs
-- are quasi-compact.
/-- Lemma 10.125.8: if `R → S` is of finite presentation, then the locus
`{ q ∈ Spec(S) | dim_q(S/R) ≤ n }` is an open and quasi-compact subset of `Spec(S)`. -/
theorem isOpen_isCompact_relativeDimensionAtLELocus_of_finitePresentation (n : ℕ) :
    IsOpen (relativeDimensionAtLELocus R S n) ∧
      IsCompact (relativeDimensionAtLELocus R S n) :=
  ⟨isOpen_relativeDimensionAtLELocus_of_finitePresentation n,
    isCompact_relativeDimensionAtLELocus_of_finitePresentation n⟩

end

/-! ### Lemma_10_125_9 (from Chap10) -/
universe u v

open TopologicalSpace PrimeSpectrum
open IsLocalRing

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [IsDomain R] [ValuationRing R]
variable [CommRing S] [IsDomain S] [Algebra R S] [Algebra.FiniteType R S]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S
local notation "GenericFiber" => Ideal.Fiber (⊥ : Ideal R) S

/- Domain-style sampling:
- primary domain: fibers of finite-type algebras over valuation rings, with the special fiber
  and generic fiber both expressed by the canonical fiber owner `Ideal.Fiber`;
- sampled owner declarations:
  `Ideal.Fiber`,
  `PrimeSpectrum.preimageHomeomorphFiber`,
  `relativeDimensionAt`,
  `EquidimensionalSpace`,
  `ringKrullDim`;
- best owner abstraction: the special fiber should be written as the canonical owner
  `ClosedFiber = Ideal.Fiber (maximalIdeal R) S`, and the generic fiber should live on the same
  owner level `GenericFiber = Ideal.Fiber (⊥ : Ideal R) S`; the tensor model
  `S ⊗[R] FractionRing R` is only a bridge presentation of `GenericFiber`, while the public
  conclusions belong on `PrimeSpectrum ClosedFiber`, `ringKrullDim ClosedFiber`, and
  `ringKrullDim GenericFiber`;
- primitive data: the valuation-ring map `R → S`, injectivity of `algebraMap R S`, the canonical
  closed fiber `ClosedFiber`, and the generic fiber `GenericFiber`;
- derived API: equidimensionality of `PrimeSpectrum ClosedFiber` and the dimension equality
  `ringKrullDim ClosedFiber = ringKrullDim GenericFiber`.

Source/core/bridge triage:
- `source-facing`: the special-fiber equidimensionality and dimension-comparison statements;
- `core/canonical`: `Ideal.Fiber`, `EquidimensionalSpace`, and `ringKrullDim`;
- `bridge/view`: the tensor-product presentations of `ClosedFiber` and `GenericFiber`.
-/

-- Proof sketch: if the special fiber is trivial then its prime spectrum is empty, hence
-- equidimensional. Otherwise apply the quasi-finite presentation from Lemma 10.125.2 near each
-- prime of the special fiber and combine it with the lower bound from Lemma 10.125.6 to identify
-- the local dimension at every prime with the common dimension of the generic fiber.
/-- Lemma 10.125.9: if `R` is a valuation ring, `S` is a finite type domain over `R`, and the
structure map `R → S` is injective, then the canonical closed fiber
`ClosedFiber = Ideal.Fiber (maximalIdeal R) S`, canonically presented by `κ(R) ⊗[R] S`, has
equidimensional prime spectrum. -/
theorem primeSpectrum_specialFiber_equidimensional_of_finiteType_over_valuationRing
    (hRS : Function.Injective (algebraMap R S)) :
    EquidimensionalSpace (PrimeSpectrum ClosedFiber) := sorry

-- Proof sketch: once the special fiber spectrum is equidimensional with every irreducible
-- component having the generic-fiber dimension, the Krull dimension of the special fiber ring is
-- exactly the Krull dimension of the canonical generic fiber `GenericFiber`, which is presented
-- by the tensor model `S ⊗[R] FractionRing R`.
/-- If the special fiber of a finite type domain over a valuation ring is nontrivial, then its
Krull dimension agrees with that of the canonical generic fiber
`GenericFiber = Ideal.Fiber (⊥ : Ideal R) S`, presented by `S ⊗[R] FractionRing R`. -/
theorem ringKrullDim_specialFiber_eq_genericFiber_of_finiteType_over_valuationRing
    (hRS : Function.Injective (algebraMap R S))
    (hspecial : Nontrivial ClosedFiber) :
    ringKrullDim ClosedFiber = ringKrullDim GenericFiber := sorry

end
