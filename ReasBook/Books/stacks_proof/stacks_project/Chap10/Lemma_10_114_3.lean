import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_105_1
import stacks_proof.stacks_project.Chap10.Lemma_10_104_4
import stacks_proof.stacks_project.Chap10.Lemma_10_105_9
import stacks_proof.stacks_project.Chap10.Proposition_10_114_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Order Set

section

variable {k : Type u} [Field k]
variable {n : ℕ}

local notation "A" => MvPolynomial (Fin n) k

/- Domain-style sampling:
- primary domain: catenary prime-chain lengths in spectra of finite polynomial rings over a field;
- sampled owner declarations of the same kind:
  `IsCatenaryRing.maximalPrimeChainsHaveSameLength`,
  `CatenarySpace.maximalIrreducibleClosedChainsHaveLength`,
  `ringKrullDim_eq_ringKrullDim_atPrime_add_ringKrullDim_quotient_of_cohenMacaulayRing`,
  `universallyCatenaryRing_of_cohenMacaulayRing`;
- best owner abstraction: the interval-chain owner is `IsCatenaryRing A`; the polynomial-ring
  theorem below is a `source-facing` specialization of that catenary owner together with the local
  Cohen-Macaulay height formula;
- primitive data: the owner ring `A`, points `p q : PrimeSpectrum A`, the comparison `hpq : p ≤ q`,
  and a maximal chain `s` in `[p, q]`;
- derived API: catenarity of `A`, obtained from Proposition `10.114.2` through the chapter
  regular/Cohen-Macaulay/universally-catenary bridge, and the identification of the interval
  codimension with `q.asIdeal.height - p.asIdeal.height`.

Source/core/bridge triage:
* `source-facing`: the explicit textbook statement about maximal chains between two primes of
  `k[x₁, \ldots, xₙ]`;
* `core/canonical`: `IsCatenaryRing A` and the Chapter 5 catenary-space chain-length owner on
  intervals of `Spec A`;
* `bridge/view`: the local Cohen-Macaulay dimension formula computing that interval codimension as
  a height difference.

This file should remain a thin specialization of the existing catenary/Cohen-Macaulay owners, not
introduce a second local prime-chain owner for polynomial rings.
-/
-- Proof sketch: by Proposition `10.114.2`, every localization of
-- `MvPolynomial (Fin n) k` at a maximal ideal is a regular local ring of dimension `n`, hence
-- Cohen-Macaulay. Then Lemmas `10.104.3` and `10.104.4` identify the length of a maximal chain
-- in the interval `[p, q]` with the difference `height q - height p`.
/-- Helper for Chap10 Lemma 10 114 3: the irreducible closed subset of the prime spectrum
corresponding to a prime. -/
private noncomputable abbrev primeIrreducibleClosed (R : Type u) [CommRing R] (p : PrimeSpectrum R) :
    TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R) :=
  show TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R) from
    PrimeSpectrum.pointsEquivIrreducibleCloseds R p

/-- Helper for Chap10 Lemma 10 114 3: a prime in `[p, q]` maps to the corresponding irreducible
closed subset in `[V(q), V(p)]`. -/
private lemma primeIntervalIrreducibleClosedMem {R : Type u} [CommRing R]
    (p q : PrimeSpectrum R) (x : Set.Icc p q) :
    primeIrreducibleClosed R x.1 ∈
      Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p) := by
  -- Passing from primes to irreducible closed subsets reverses the displayed endpoints.
  constructor
  · exact (PrimeSpectrum.pointsEquivIrreducibleCloseds R).monotone x.2.2
  · exact (PrimeSpectrum.pointsEquivIrreducibleCloseds R).monotone x.2.1

/-- Helper for Chap10 Lemma 10 114 3: an irreducible-closed interval point maps back to the
corresponding prime interval. -/
private lemma irreducibleClosedIntervalPrimeMem {R : Type u} [CommRing R]
    (p q : PrimeSpectrum R)
    (x : Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p)) :
    (PrimeSpectrum.pointsEquivIrreducibleCloseds R).symm
      (show (TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R))ᵒᵈ from x.1) ∈
      Set.Icc p q := by
  -- Endpoint inequalities in the dual irreducible-closed order become prime inequalities.
  constructor
  · have hx :
        (PrimeSpectrum.pointsEquivIrreducibleCloseds R p) ≤
          (show (TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R))ᵒᵈ from x.1) := by
      exact x.2.2
    simpa using (PrimeSpectrum.pointsEquivIrreducibleCloseds R).symm.monotone hx
  · have hx :
        (show (TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R))ᵒᵈ from x.1) ≤
          PrimeSpectrum.pointsEquivIrreducibleCloseds R q := by
      exact x.2.1
    simpa using (PrimeSpectrum.pointsEquivIrreducibleCloseds R).symm.monotone hx

/-- Helper for Chap10 Lemma 10 114 3: the forward map from prime intervals to
irreducible-closed intervals. -/
private noncomputable def primeIntervalToIrreducibleClosed {R : Type u} [CommRing R]
    (p q : PrimeSpectrum R) :
    Set.Icc p q → Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p) :=
  fun x ↦ ⟨primeIrreducibleClosed R x.1,
    primeIntervalIrreducibleClosedMem (p := p) (q := q) x⟩

/-- Helper for Chap10 Lemma 10 114 3: the inverse map from irreducible-closed intervals to
prime intervals. -/
private noncomputable def irreducibleClosedIntervalToPrime {R : Type u} [CommRing R]
    (p q : PrimeSpectrum R) :
    Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p) → Set.Icc p q :=
  fun x ↦ ⟨(PrimeSpectrum.pointsEquivIrreducibleCloseds R).symm
    (show (TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R))ᵒᵈ from x.1),
    irreducibleClosedIntervalPrimeMem (p := p) (q := q) x⟩

/-- Helper for Chap10 Lemma 10 114 3: the interval maps are left inverses. -/
private lemma irreducibleClosedIntervalToPrime_leftInverse {R : Type u} [CommRing R]
    (p q : PrimeSpectrum R) :
    Function.LeftInverse (irreducibleClosedIntervalToPrime p q)
      (primeIntervalToIrreducibleClosed p q) := by
  -- Subtype extensionality reduces the inverse calculation to the spectrum order isomorphism.
  intro x
  ext
  simp [primeIntervalToIrreducibleClosed, irreducibleClosedIntervalToPrime,
    primeIrreducibleClosed]

/-- Helper for Chap10 Lemma 10 114 3: the interval maps are right inverses. -/
private lemma irreducibleClosedIntervalToPrime_rightInverse {R : Type u} [CommRing R]
    (p q : PrimeSpectrum R) :
    Function.RightInverse (irreducibleClosedIntervalToPrime p q)
      (primeIntervalToIrreducibleClosed p q) := by
  -- The same subtype extensionality proves the reverse inverse identity.
  intro x
  ext
  simp [primeIntervalToIrreducibleClosed, irreducibleClosedIntervalToPrime,
    primeIrreducibleClosed]

/-- Helper for Chap10 Lemma 10 114 3: the interval map reverses the displayed order. -/
private lemma primeIntervalToIrreducibleClosed_rel_iff {R : Type u} [CommRing R]
    (p q : PrimeSpectrum R) (x y : Set.Icc p q) :
    flip (fun a b : Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p) ↦
        a ≤ b)
        (primeIntervalToIrreducibleClosed p q x)
        (primeIntervalToIrreducibleClosed p q y) ↔ x ≤ y := by
  -- The codomain of `pointsEquivIrreducibleCloseds` is an order dual.
  constructor
  · intro h
    have hdual :
        (PrimeSpectrum.pointsEquivIrreducibleCloseds R) x.1 ≤
          (PrimeSpectrum.pointsEquivIrreducibleCloseds R) y.1 := h
    exact (PrimeSpectrum.pointsEquivIrreducibleCloseds R).le_iff_le.mp hdual
  · intro h
    exact (PrimeSpectrum.pointsEquivIrreducibleCloseds R).monotone h

/-- Helper for Chap10 Lemma 10 114 3: prime intervals are relation-isomorphic to
irreducible-closed intervals with the relation flipped. -/
private noncomputable def primeIntervalRelIsoIrreducibleClosed {R : Type u} [CommRing R]
    (p q : PrimeSpectrum R) :
    (fun x y : Set.Icc p q ↦ x ≤ y) ≃r
      flip (fun x y : Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p) ↦
        x ≤ y) :=
  { toEquiv :=
      { toFun := primeIntervalToIrreducibleClosed p q
        invFun := irreducibleClosedIntervalToPrime p q
        left_inv := irreducibleClosedIntervalToPrime_leftInverse p q
        right_inv := irreducibleClosedIntervalToPrime_rightInverse p q }
    map_rel_iff' := fun {x y} ↦ primeIntervalToIrreducibleClosed_rel_iff p q x y }

/-- Helper for Chap10 Lemma 10 114 3: the prime-to-irreducible interval map is monotone when the
codomain is dualized. -/
private lemma primeIntervalRelIsoIrreducibleClosedDual_monotone {R : Type u} [CommRing R]
    (p q : PrimeSpectrum R) :
    Monotone (fun x : Set.Icc p q ↦
      (show (Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p))ᵒᵈ from
        primeIntervalRelIsoIrreducibleClosed p q x)) := by
  -- Dualizing the codomain turns the relation isomorphism into a monotone map.
  intro x y hxy
  change primeIntervalRelIsoIrreducibleClosed p q y ≤
    primeIntervalRelIsoIrreducibleClosed p q x
  exact (primeIntervalRelIsoIrreducibleClosed p q).map_rel_iff.mpr hxy

/-- Helper for Chap10 Lemma 10 114 3: the inverse interval map is monotone from the dualized
irreducible-closed interval. -/
private lemma primeIntervalRelIsoIrreducibleClosedDual_symm_monotone {R : Type u} [CommRing R]
    (p q : PrimeSpectrum R) :
    Monotone (fun x :
      (Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p))ᵒᵈ ↦
        (primeIntervalRelIsoIrreducibleClosed p q).symm
          (show Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p) from x)) := by
  -- This is the inverse monotonicity needed to package the dualized order isomorphism.
  intro x y hxy
  change (primeIntervalRelIsoIrreducibleClosed p q).symm
      (show Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p) from x) ≤
    (primeIntervalRelIsoIrreducibleClosed p q).symm
      (show Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p) from y)
  have hrel :
      flip (fun a b : Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p) ↦
        a ≤ b)
        (show Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p) from x)
        (show Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p) from y) := by
    exact hxy
  exact (primeIntervalRelIsoIrreducibleClosed p q).symm.map_rel_iff.mpr hrel

/-- Helper for Chap10 Lemma 10 114 3: prime intervals are order-isomorphic to the dual of the
corresponding irreducible-closed interval. -/
private noncomputable def primeIntervalOrderIsoIrreducibleClosedDual {R : Type u} [CommRing R]
    (p q : PrimeSpectrum R) :
    Set.Icc p q ≃o
      (Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p))ᵒᵈ :=
  { toFun := fun x ↦
      (show (Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p))ᵒᵈ from
        primeIntervalToIrreducibleClosed p q x)
    invFun := fun x ↦
      irreducibleClosedIntervalToPrime p q
        (show Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p) from x)
    left_inv := irreducibleClosedIntervalToPrime_leftInverse p q
    right_inv := fun x ↦ irreducibleClosedIntervalToPrime_rightInverse p q
      (show Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p) from x)
    map_rel_iff' := fun {x y} ↦ by
      change primeIntervalToIrreducibleClosed p q y ≤ primeIntervalToIrreducibleClosed p q x ↔
        x ≤ y
      exact primeIntervalToIrreducibleClosed_rel_iff p q x y }

/-- Helper for Chap10 Lemma 10 114 3: the irreducible-closed codimension of `[V(q), V(p)]`
is the coheight of the bottom of the prime interval `[p, q]`. -/
private lemma codimBetween_primeIrreducibleClosed_eq_intervalCoheight {R : Type u} [CommRing R]
    (p q : PrimeSpectrum R) [Fact (p ≤ q)] :
    codimBetween (primeIrreducibleClosed R q) (primeIrreducibleClosed R p)
        ((PrimeSpectrum.pointsEquivIrreducibleCloseds R).monotone (show p ≤ q from Fact.out)) =
      Order.coheight (⊥ : Set.Icc p q) := by
  -- Compare both quantities through the Krull dimension of the transported interval.
  apply WithBot.coe_injective
  calc
    (codimBetween (primeIrreducibleClosed R q) (primeIrreducibleClosed R p)
        ((PrimeSpectrum.pointsEquivIrreducibleCloseds R).monotone (show p ≤ q from Fact.out)) :
        WithBot ℕ∞) =
        Order.krullDim (Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p)) :=
      codimBetween_eq_krullDim _
    _ =
        Order.krullDim
          ((Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p))ᵒᵈ) := by
      exact (Order.krullDim_orderDual
        (α := Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p))).symm
    _ = Order.krullDim (Set.Icc p q) := by
      exact Order.krullDim_eq_of_orderIso
        (primeIntervalOrderIsoIrreducibleClosedDual p q).symm
    _ = (Order.coheight (⊥ : Set.Icc p q) : WithBot ℕ∞) := by
      rw [Order.coheight_bot_eq_krullDim]

/-- Helper for Chap10 Lemma 10 114 3: in a catenary ring, a maximal prime chain in `[p, q]`
has cardinality one more than the coheight of the bottom of that interval. -/
private lemma maximalPrimeChain_encard_eq_intervalCoheight {R : Type u} [CommRing R]
    [IsCatenaryRing R] (p q : PrimeSpectrum R) [Fact (p ≤ q)]
    {s : Set (Set.Icc p q)} (hs : IsMaxChain (· ≤ ·) s) :
    s.encard = ENat.toNat (Order.coheight (⊥ : Set.Icc p q)) + 1 := by
  -- Transport the maximal prime chain to the irreducible-closed interval where catenarity applies.
  let e := primeIntervalRelIsoIrreducibleClosed p q
  have hsImage :
      IsMaxChain (· ≤ ·)
        (e '' s : Set (Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p))) := by
    simpa [e, flip] using (IsMaxChain.image e hs).symm
  have hlen :=
    CatenarySpace.maximalIrreducibleClosedChainsHaveLength
      (X := PrimeSpectrum R)
      ((PrimeSpectrum.pointsEquivIrreducibleCloseds R).monotone (show p ≤ q from Fact.out))
      (e '' s) hsImage
  have hlenToEquiv :
      (e.toEquiv '' s).encard =
        ENat.toNat (codimBetween (primeIrreducibleClosed R q) (primeIrreducibleClosed R p)
          ((PrimeSpectrum.pointsEquivIrreducibleCloseds R).monotone
            (show p ≤ q from Fact.out))) + 1 := by
    simpa using hlen
  -- The relation isomorphism preserves cardinality, and the interval codimension is coheight.
  rw [← e.toEquiv.injective.encard_image s]
  rw [hlenToEquiv]
  rw [codimBetween_primeIrreducibleClosed_eq_intervalCoheight (R := R) p q]

/-- Helper for Chap10 Lemma 10 114 3: the lower prime `p` viewed inside the localization at
the upper prime `q`. -/
private noncomputable def localizedLowerPrime {R : Type u} [CommRing R]
  (p q : PrimeSpectrum R) [Fact (p ≤ q)] :
    PrimeSpectrum (Localization.AtPrime q.asIdeal) :=
  (IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime q.asIdeal) q.asIdeal).symm
    ⟨p, (show p ≤ q from Fact.out)⟩

/-- Helper for Chap10 Lemma 10 114 3: the localized lower prime lies below every localized point
coming from the interval `[p, q]`. -/
private lemma localizedLowerPrime_le_of_mem_interval {R : Type u} [CommRing R]
    (p q : PrimeSpectrum R) [Fact (p ≤ q)] (x : Set.Icc p q) :
    localizedLowerPrime p q ≤
      (IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime q.asIdeal) q.asIdeal).symm
        ⟨x.1, x.2.2⟩ := by
  -- Monotonicity of the inverse localization order isomorphism transports `p ≤ x`.
  let e := IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime q.asIdeal) q.asIdeal
  change e.symm ⟨p, (show p ≤ q from Fact.out)⟩ ≤ e.symm ⟨x.1, x.2.2⟩
  exact e.symm.monotone x.2.1

/-- Helper for Chap10 Lemma 10 114 3: a point above the localized lower prime contracts to a
prime above `p`. -/
private lemma localizedLowerPrime_interval_mem_left {R : Type u} [CommRing R]
    (p q : PrimeSpectrum R) [Fact (p ≤ q)] (y : Set.Ici (localizedLowerPrime p q)) :
    p ≤ ((IsLocalization.AtPrime.primeSpectrumOrderIso
      (Localization.AtPrime q.asIdeal) q.asIdeal) y.1).1 := by
  -- Apply the localization order isomorphism to the inequality above the localized lower prime.
  let e := IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime q.asIdeal) q.asIdeal
  have hy := e.monotone y.2
  have hleft :
      e (localizedLowerPrime p q) = (⟨p, (show p ≤ q from Fact.out)⟩ : Set.Iic q) := by
    simp [localizedLowerPrime, e]
  rw [hleft] at hy
  exact hy

/-- Helper for Chap10 Lemma 10 114 3: the interval-localization maps are left inverses. -/
private lemma localizedLowerPrime_interval_leftInverse {R : Type u} [CommRing R]
    (p q : PrimeSpectrum R) [Fact (p ≤ q)] :
    Function.LeftInverse
      (fun y : Set.Ici (localizedLowerPrime p q) ↦
        (⟨((IsLocalization.AtPrime.primeSpectrumOrderIso
          (Localization.AtPrime q.asIdeal) q.asIdeal) y.1).1,
          localizedLowerPrime_interval_mem_left p q y,
          ((IsLocalization.AtPrime.primeSpectrumOrderIso
            (Localization.AtPrime q.asIdeal) q.asIdeal) y.1).2⟩ : Set.Icc p q))
      (fun x : Set.Icc p q ↦
        (⟨(IsLocalization.AtPrime.primeSpectrumOrderIso
          (Localization.AtPrime q.asIdeal) q.asIdeal).symm ⟨x.1, x.2.2⟩,
          localizedLowerPrime_le_of_mem_interval p q x⟩ : Set.Ici (localizedLowerPrime p q))) := by
  -- The underlying point is recovered by applying the order isomorphism and its inverse.
  intro x
  ext
  simp

/-- Helper for Chap10 Lemma 10 114 3: the interval-localization maps are right inverses. -/
private lemma localizedLowerPrime_interval_rightInverse {R : Type u} [CommRing R]
    (p q : PrimeSpectrum R) [Fact (p ≤ q)] :
    Function.RightInverse
      (fun y : Set.Ici (localizedLowerPrime p q) ↦
        (⟨((IsLocalization.AtPrime.primeSpectrumOrderIso
          (Localization.AtPrime q.asIdeal) q.asIdeal) y.1).1,
          localizedLowerPrime_interval_mem_left p q y,
          ((IsLocalization.AtPrime.primeSpectrumOrderIso
            (Localization.AtPrime q.asIdeal) q.asIdeal) y.1).2⟩ : Set.Icc p q))
      (fun x : Set.Icc p q ↦
        (⟨(IsLocalization.AtPrime.primeSpectrumOrderIso
          (Localization.AtPrime q.asIdeal) q.asIdeal).symm ⟨x.1, x.2.2⟩,
          localizedLowerPrime_le_of_mem_interval p q x⟩ : Set.Ici (localizedLowerPrime p q))) := by
  -- The localization point is recovered by the inverse followed by the order isomorphism.
  intro y
  ext
  simp

/-- Helper for Chap10 Lemma 10 114 3: the interval-localization map reflects order. -/
private lemma localizedLowerPrime_interval_rel_iff {R : Type u} [CommRing R]
    (p q : PrimeSpectrum R) [Fact (p ≤ q)] (x y : Set.Icc p q) :
    (⟨(IsLocalization.AtPrime.primeSpectrumOrderIso
          (Localization.AtPrime q.asIdeal) q.asIdeal).symm ⟨x.1, x.2.2⟩,
        localizedLowerPrime_le_of_mem_interval p q x⟩ : Set.Ici (localizedLowerPrime p q)) ≤
    (⟨(IsLocalization.AtPrime.primeSpectrumOrderIso
          (Localization.AtPrime q.asIdeal) q.asIdeal).symm ⟨y.1, y.2.2⟩,
        localizedLowerPrime_le_of_mem_interval p q y⟩ : Set.Ici (localizedLowerPrime p q)) ↔
      x ≤ y := by
  -- Order reflection is exactly the order reflection of the localization spectrum isomorphism.
  let e := IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime q.asIdeal) q.asIdeal
  change e.symm ⟨x.1, x.2.2⟩ ≤ e.symm ⟨y.1, y.2.2⟩ ↔ x.1 ≤ y.1
  simpa using e.symm.le_iff_le

/-- Helper for Chap10 Lemma 10 114 3: the interval `[p, q]` is the upper interval above the
localized lower prime in `Spec A_q`. -/
private noncomputable def primeIntervalOrderIsoLocalizedUpper {R : Type u} [CommRing R]
    (p q : PrimeSpectrum R) [Fact (p ≤ q)] :
    Set.Icc p q ≃o Set.Ici (localizedLowerPrime p q) where
  toFun x :=
    ⟨(IsLocalization.AtPrime.primeSpectrumOrderIso
      (Localization.AtPrime q.asIdeal) q.asIdeal).symm ⟨x.1, x.2.2⟩,
      localizedLowerPrime_le_of_mem_interval p q x⟩
  invFun y :=
    ⟨((IsLocalization.AtPrime.primeSpectrumOrderIso
      (Localization.AtPrime q.asIdeal) q.asIdeal) y.1).1,
      localizedLowerPrime_interval_mem_left p q y,
      ((IsLocalization.AtPrime.primeSpectrumOrderIso
        (Localization.AtPrime q.asIdeal) q.asIdeal) y.1).2⟩
  left_inv := localizedLowerPrime_interval_leftInverse p q
  right_inv := localizedLowerPrime_interval_rightInverse p q
  map_rel_iff' := fun {x y} ↦ localizedLowerPrime_interval_rel_iff p q x y

/-- Helper for Chap10 Lemma 10 114 3: the coheight of the bottom of `[p, q]` is the coheight of
the localized lower prime in `A_q`. -/
private lemma intervalCoheight_eq_localizedLowerPrime_coheight {R : Type u} [CommRing R]
    (p q : PrimeSpectrum R) [Fact (p ≤ q)] :
    Order.coheight (⊥ : Set.Icc p q) = Order.coheight (localizedLowerPrime p q) := by
  -- Transport the interval to `Set.Ici` of the localized lower prime and use the standard
  -- coheight/Krull-dimension bridge.
  apply WithBot.coe_injective
  calc
    (Order.coheight (⊥ : Set.Icc p q) : WithBot ℕ∞) = Order.krullDim (Set.Icc p q) := by
      rw [Order.coheight_bot_eq_krullDim]
    _ = Order.krullDim (Set.Ici (localizedLowerPrime p q)) :=
      Order.krullDim_eq_of_orderIso (primeIntervalOrderIsoLocalizedUpper p q)
    _ = (Order.coheight (localizedLowerPrime p q) : WithBot ℕ∞) :=
      (Order.coheight_eq_krullDim_Ici (localizedLowerPrime p q)).symm

/-- Helper for Chap10 Lemma 10 114 3: the quotient by a prime has Krull dimension equal to the
coheight of that prime. -/
private lemma primeQuotientKrullDim_eq_coheight {R : Type u} [CommRing R]
    (p : PrimeSpectrum R) :
    ringKrullDim (R ⧸ p.asIdeal) = (Order.coheight p : WithBot ℕ∞) := by
  -- Rewrite the quotient spectrum as the upper interval of primes containing `p`.
  rw [ringKrullDim_quotient]
  have hzero : PrimeSpectrum.zeroLocus (p.asIdeal : Set R) = Set.Ici p := by
    ext q
    change p.asIdeal ≤ q.asIdeal ↔ p ≤ q
    rfl
  rw [hzero]
  exact (Order.coheight_eq_krullDim_Ici p).symm

/-- Helper for Chap10 Lemma 10 114 3: the localized lower prime contracts to the original lower
prime. -/
private lemma localizedLowerPrime_comap_asIdeal {R : Type u} [CommRing R]
    (p q : PrimeSpectrum R) [Fact (p ≤ q)] :
    Ideal.comap (algebraMap R (Localization.AtPrime q.asIdeal))
        (localizedLowerPrime p q).asIdeal = p.asIdeal := by
  -- The statement is the defining property of the localization spectrum order isomorphism.
  let Lq := Localization.AtPrime q.asIdeal
  let e := IsLocalization.AtPrime.primeSpectrumOrderIso Lq q.asIdeal
  have hpq_point : PrimeSpectrum.comap (algebraMap R Lq) (localizedLowerPrime p q) = p := by
    change (e (e.symm ⟨p, (show p ≤ q from Fact.out)⟩)).1 = p
    simp [e]
  simpa [PrimeSpectrum.comap_asIdeal, Lq] using congrArg PrimeSpectrum.asIdeal hpq_point

/-- Helper for Chap10 Lemma 10 114 3: localizing the upper localization at the localized lower
prime has Krull dimension `height(p)`. -/
private lemma localizedLowerPrime_localization_ringKrullDim_eq_height {R : Type u} [CommRing R]
    (p q : PrimeSpectrum R) [Fact (p ≤ q)] :
    ringKrullDim (Localization.AtPrime (localizedLowerPrime p q).asIdeal) =
      p.asIdeal.height := by
  -- Compare the double localization with the localization of the original ring at `p`.
  let Lq := Localization.AtPrime q.asIdeal
  let pq := localizedLowerPrime p q
  have hpq_comap : Ideal.comap (algebraMap R Lq) pq.asIdeal = p.asIdeal := by
    simpa [Lq, pq] using localizedLowerPrime_comap_asIdeal (R := R) p q
  let eDouble :=
    IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (M := q.asIdeal.primeCompl) pq.asIdeal
  have hiter0 :
      ringKrullDim (Localization.AtPrime pq.asIdeal) =
        ringKrullDim (Localization.AtPrime (Ideal.comap (algebraMap R Lq) pq.asIdeal)) := by
    exact (ringKrullDim_eq_of_ringEquiv eDouble.toRingEquiv).symm
  let Icomap : Ideal R := Ideal.comap (algebraMap R Lq) pq.asIdeal
  letI : Icomap.IsPrime := Ideal.comap_isPrime (algebraMap R Lq) pq.asIdeal
  have hI : Icomap = p.asIdeal := by
    simpa [Icomap] using hpq_comap
  have htarget :
      ringKrullDim (Localization.AtPrime Icomap) =
        ringKrullDim (Localization.AtPrime p.asIdeal) := by
    let eEq : Localization.AtPrime Icomap ≃+* Localization.AtPrime p.asIdeal :=
      Localization.localRingEquiv Icomap p.asIdeal (RingEquiv.refl R) hI
    exact ringKrullDim_eq_of_ringEquiv eEq
  calc
    ringKrullDim (Localization.AtPrime pq.asIdeal) =
        ringKrullDim (Localization.AtPrime (Ideal.comap (algebraMap R Lq) pq.asIdeal)) := hiter0
    _ = ringKrullDim (Localization.AtPrime Icomap) := by rfl
    _ = ringKrullDim (Localization.AtPrime p.asIdeal) := htarget
    _ = p.asIdeal.height :=
      IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (Localization.AtPrime p.asIdeal)

/-- Helper for Chap10 Lemma 10 114 3: the coheight of the localized lower prime is the height
difference `height(q) - height(p)` in a Cohen-Macaulay ring. -/
private lemma localizedLowerPrime_coheight_eq_height_sub {R : Type u} [CommRing R]
    [CohenMacaulayRing R] (p q : PrimeSpectrum R) [Fact (p ≤ q)] :
    Order.coheight (localizedLowerPrime p q) = q.asIdeal.height - p.asIdeal.height := by
  -- Apply the Cohen-Macaulay dimension formula in the local ring `R_q`.
  let Lq := Localization.AtPrime q.asIdeal
  let pq := localizedLowerPrime p q
  have hformula :
      ringKrullDim Lq =
        ringKrullDim (Localization.AtPrime pq.asIdeal) + ringKrullDim (Lq ⧸ pq.asIdeal) := by
    exact
      ringKrullDim_eq_ringKrullDim_atPrime_add_ringKrullDim_quotient_of_cohenMacaulayRing
        (R := Lq) (localizedRing_cohenMacaulay R q) pq.asIdeal
  have hLq : ringKrullDim Lq = q.asIdeal.height :=
    IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal Lq
  have hpqLoc : ringKrullDim (Localization.AtPrime pq.asIdeal) = p.asIdeal.height := by
    simpa [Lq, pq] using localizedLowerPrime_localization_ringKrullDim_eq_height (R := R) p q
  have hquot : ringKrullDim (Lq ⧸ pq.asIdeal) = (Order.coheight pq : WithBot ℕ∞) :=
    primeQuotientKrullDim_eq_coheight (R := Lq) pq
  have hheight_add : q.asIdeal.height = p.asIdeal.height + Order.coheight pq := by
    apply WithBot.coe_injective
    calc
      ((q.asIdeal.height : ℕ∞) : WithBot ℕ∞) = ringKrullDim Lq := hLq.symm
      _ = ringKrullDim (Localization.AtPrime pq.asIdeal) + ringKrullDim (Lq ⧸ pq.asIdeal) :=
        hformula
      _ = ((p.asIdeal.height + Order.coheight pq : ℕ∞) : WithBot ℕ∞) := by
        rw [hpqLoc, hquot]
        rfl
  -- Since prime heights are finite in a Noetherian ring, subtract `height(p)` from the formula.
  have hp_ne_top : p.asIdeal.height ≠ ⊤ :=
    Ideal.height_ne_top (Ideal.IsPrime.ne_top inferInstance)
  exact (ENat.addLECancellable_of_ne_top hp_ne_top).eq_tsub_of_add_eq
    (by simpa [pq, add_comm] using hheight_add.symm)

/-- Helper for Chap10 Lemma 10 114 3: the interval coheight is the height difference in a
Cohen-Macaulay ring. -/
private lemma intervalCoheight_eq_height_sub_of_cohenMacaulayRing {R : Type u} [CommRing R]
    [CohenMacaulayRing R] (p q : PrimeSpectrum R) [Fact (p ≤ q)] :
    Order.coheight (⊥ : Set.Icc p q) = q.asIdeal.height - p.asIdeal.height := by
  -- Localize at the upper prime and use the local height-subtraction computation.
  calc
    Order.coheight (⊥ : Set.Icc p q) = Order.coheight (localizedLowerPrime p q) :=
      intervalCoheight_eq_localizedLowerPrime_coheight p q
    _ = q.asIdeal.height - p.asIdeal.height :=
      localizedLowerPrime_coheight_eq_height_sub p q

/-- Helper for Chap10 Lemma 10 114 3: finite polynomial rings over fields are Cohen-Macaulay. -/
private theorem cohenMacaulayRing_mvPolynomial_of_field :
    CohenMacaulayRing A := by
  -- Regularity of the polynomial ring gives regular local rings at every prime, hence local
  -- Cohen-Macaulay self-modules.
  refine { toIsNoetherian := inferInstance, toLocallyCohenMacaulay := ?_ }
  refine { toFinite := inferInstance, localizedModule_cohenMacaulay := ?_ }
  intro p
  letI : IsRegularLocalRing (Localization.AtPrime p.asIdeal) :=
    IsRegularRing.isRegularLocalRing_atPrime p
  simpa using
    (regularLocalRing_selfModule_cohenMacaulay
      (R := Localization.AtPrime p.asIdeal))

/-- Chap10 Lemma 10 114 3: if `p ≤ q` are prime ideals of the polynomial ring `k[x_1, \ldots, x_n]`,
then any maximal chain of primes between them has length `height(q) - height(p)`, equivalently,
it has `ENat.toNat (q.asIdeal.height - p.asIdeal.height) + 1` elements. -/
@[stacks 00OR]
theorem maximal_prime_chain_encard_eq_height_sub_add_one_mvPolynomial
    (p q : PrimeSpectrum A) (hpq : p ≤ q)
    {s : Set (Set.Icc p q)} (hs : IsMaxChain (· ≤ ·) s) :
    s.encard = ENat.toNat (q.asIdeal.height - p.asIdeal.height) + 1 := by
  -- Install the Cohen-Macaulay and catenary instances supplied by regularity of the polynomial
  -- ring, then reduce the chain length to the interval coheight.
  letI : CohenMacaulayRing A := cohenMacaulayRing_mvPolynomial_of_field
  letI : UniversallyCatenaryRing A :=
    universallyCatenaryRing_of_cohenMacaulayRing (R := A) inferInstance
  letI : Fact (p ≤ q) := ⟨hpq⟩
  calc
    s.encard = ENat.toNat (Order.coheight (⊥ : Set.Icc p q)) + 1 :=
      maximalPrimeChain_encard_eq_intervalCoheight p q hs
    _ = ENat.toNat (q.asIdeal.height - p.asIdeal.height) + 1 := by
      rw [intervalCoheight_eq_height_sub_of_cohenMacaulayRing p q]

end
