import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_26_1 (from Chap10) -/
/- Lemma 10.26.1 (1): for a prime `𝔭 ⊆ R`, the closure of the singleton `{𝔭}` in `Spec R` is the
closed subset `V(𝔭)`. This is exactly the canonical theorem
`PrimeSpectrum.closure_singleton`. -/
recall PrimeSpectrum.closure_singleton

/- Lemma 10.26.1 (2): the irreducible closed subsets of `Spec R` are exactly the subsets `V(𝔭)`
for prime ideals `𝔭 ⊆ R`. Canonically, this is the inclusion-reversing order isomorphism
`PrimeSpectrum.pointsEquivIrreducibleCloseds`. -/
recall PrimeSpectrum.pointsEquivIrreducibleCloseds

/- Lemma 10.26.1 (3): the irreducible components of `Spec R` are exactly the subsets `V(𝔭)` for
minimal prime ideals `𝔭 ⊆ R`. Canonically, this is the inclusion-reversing order isomorphism
`minimalPrimes.equivIrreducibleComponents`. -/
recall minimalPrimes.equivIrreducibleComponents

/-! ### Lemma_10_26_2 (from Chap10) -/
/- Lemma 10.26.2: for a commutative ring `R`, the prime spectrum `Spec R` is a spectral space in
the sense of Topology, Definition 5.23.1. In mathlib this is the canonical instance
`PrimeSpectrum.instSpectralSpace`. -/
recall PrimeSpectrum.instSpectralSpace

/-! ### Lemma_10_26_3 (from Chap10) -/
noncomputable section

open TopologicalSpace PrimeSpectrum IsLocalization.AtPrime

universe u

section

variable {R : Type u} [CommRing R]

private theorem mem_pointsEquivIrreducibleCloseds_iff_le (p q : PrimeSpectrum R) :
    p ∈ ((show IrreducibleCloseds (PrimeSpectrum R) from
      PrimeSpectrum.pointsEquivIrreducibleCloseds R q) : Set (PrimeSpectrum R)) ↔ q ≤ p := by
  rw [show ((show IrreducibleCloseds (PrimeSpectrum R) from
      PrimeSpectrum.pointsEquivIrreducibleCloseds R q) : Set (PrimeSpectrum R)) =
      closure ({q} : Set (PrimeSpectrum R)) by rfl]
  rw [← specializes_iff_mem_closure, le_iff_specializes]

private noncomputable def irreducibleClosedsContainingOrderIso (p : PrimeSpectrum R) :
    { Z : (IrreducibleCloseds (PrimeSpectrum R))ᵒᵈ //
        p ∈ ((show IrreducibleCloseds (PrimeSpectrum R) from Z) : Set (PrimeSpectrum R)) } ≃o
      ({ Z : IrreducibleCloseds (PrimeSpectrum R) //
        p ∈ (Z : Set (PrimeSpectrum R)) })ᵒᵈ :=
  (((Equiv.refl _).subtypeEquiv fun _ ↦ Iff.rfl).toOrderIso
    (fun _ _ h ↦ h) (fun _ _ h ↦ h))

private noncomputable def irreducibleComponentsOrderIsoIrreducibleCloseds
    (X : Type*) [TopologicalSpace X] :
    irreducibleComponents X ≃o
      { Z : IrreducibleCloseds X // (Z : Set X) ∈ irreducibleComponents X } :=
  let e₁ :
      irreducibleComponents X ≃
        { Z : Set X // Maximal (fun x ↦ IsClosed x ∧ IsIrreducible x) Z } :=
    Equiv.subtypeEquivRight fun Z ↦ by
      simp [irreducibleComponents_eq_maximals_closed]
  let e₂ :
      { Z : Set X // Maximal (fun x ↦ IsClosed x ∧ IsIrreducible x) Z } ≃
        { Z : {s : Set X // IsClosed s ∧ IsIrreducible s} //
          Maximal (fun x ↦ IsClosed x ∧ IsIrreducible x) Z.1 } :=
    { toFun := fun Z ↦ ⟨⟨Z.1, Z.2.1⟩, Z.2⟩
      , invFun := fun Z ↦ ⟨Z.1.1, Z.2⟩
      , left_inv := fun _ ↦ rfl
      , right_inv := fun _ ↦ rfl }
  let e₃ :
      { Z : {s : Set X // IsClosed s ∧ IsIrreducible s} //
          Maximal (fun x ↦ IsClosed x ∧ IsIrreducible x) Z.1 } ≃
        { Z : IrreducibleCloseds X // (Z : Set X) ∈ irreducibleComponents X } :=
    (TopologicalSpace.IrreducibleCloseds.equivSubtype' : IrreducibleCloseds X ≃
      {s : Set X // IsClosed s ∧ IsIrreducible s}).symm.subtypeEquiv fun Z ↦ by
        simp [irreducibleComponents_eq_maximals_closed]
  let e := e₁.trans <| e₂.trans e₃
  e.toOrderIso (fun _ _ h ↦ h) (fun _ _ h ↦ h)

private noncomputable def irreducibleComponentsContainingOrderIso (p : PrimeSpectrum R) :
    { Z : { Z : IrreducibleCloseds (PrimeSpectrum R) //
        p ∈ (Z : Set (PrimeSpectrum R)) } //
        (Z.1 : Set (PrimeSpectrum R)) ∈ irreducibleComponents (PrimeSpectrum R) } ≃o
      { Z : irreducibleComponents (PrimeSpectrum R) //
        p ∈ (Z : Set (PrimeSpectrum R)) } :=
  let e₁ :
      { Z : { Z : IrreducibleCloseds (PrimeSpectrum R) //
          p ∈ (Z : Set (PrimeSpectrum R)) } //
          (Z.1 : Set (PrimeSpectrum R)) ∈ irreducibleComponents (PrimeSpectrum R) } ≃o
        { Z : { Z : IrreducibleCloseds (PrimeSpectrum R) //
            (Z : Set (PrimeSpectrum R)) ∈ irreducibleComponents (PrimeSpectrum R) } //
            p ∈ (Z.1 : Set (PrimeSpectrum R)) } :=
    { toEquiv :=
        { toFun := fun Z ↦ ⟨⟨Z.1.1, Z.2⟩, Z.1.2⟩
        , invFun := fun Z ↦ ⟨⟨Z.1.1, Z.2⟩, Z.1.2⟩
        , left_inv := fun _ ↦ rfl
        , right_inv := fun _ ↦ rfl }
      , map_rel_iff' := by
          intro a b
          rfl }
  let e₂ :
      { Z : { Z : IrreducibleCloseds (PrimeSpectrum R) //
          (Z : Set (PrimeSpectrum R)) ∈ irreducibleComponents (PrimeSpectrum R) } //
          p ∈ (Z.1 : Set (PrimeSpectrum R)) } ≃o
        { Z : irreducibleComponents (PrimeSpectrum R) //
          p ∈ (Z : Set (PrimeSpectrum R)) } :=
    let e := (irreducibleComponentsOrderIsoIrreducibleCloseds (PrimeSpectrum R)).symm
    let e' :
        { Z : { Z : IrreducibleCloseds (PrimeSpectrum R) //
            (Z : Set (PrimeSpectrum R)) ∈ irreducibleComponents (PrimeSpectrum R) } //
            p ∈ (Z.1 : Set (PrimeSpectrum R)) } ≃
          { Z : irreducibleComponents (PrimeSpectrum R) //
            p ∈ (Z : Set (PrimeSpectrum R)) } :=
      e.toEquiv.subtypeEquiv fun Z ↦ Iff.rfl
    e'.toOrderIso
      (fun _ _ h ↦ e.monotone h) (fun _ _ h ↦ e.symm.monotone h)
  e₁.trans e₂

private noncomputable def pointsEquivIrreducibleClosedsContaining
    (p : PrimeSpectrum R) :
    Set.Iic p ≃o
      { Z : (IrreducibleCloseds (PrimeSpectrum R))ᵒᵈ //
        p ∈ ((show IrreducibleCloseds (PrimeSpectrum R) from Z) : Set (PrimeSpectrum R)) } :=
  let e :
      Set.Iic p ≃
        { Z : (IrreducibleCloseds (PrimeSpectrum R))ᵒᵈ //
          p ∈ ((show IrreducibleCloseds (PrimeSpectrum R) from Z) : Set (PrimeSpectrum R)) } :=
    (PrimeSpectrum.pointsEquivIrreducibleCloseds R).toEquiv.subtypeEquiv
      (fun q ↦ (mem_pointsEquivIrreducibleCloseds_iff_le p q).symm)
  e.toOrderIso
    (fun _ _ h ↦ (PrimeSpectrum.pointsEquivIrreducibleCloseds R).monotone h)
    (fun _ _ h ↦ (PrimeSpectrum.pointsEquivIrreducibleCloseds R).symm.monotone h)

/-- The prime spectrum of `R_p` identifies canonically, via an order isomorphism, with the
irreducible closed subsets of `Spec R` containing `p`. -/
noncomputable def PrimeSpectrum.localizationAtPrimeIrreducibleCloseds
    (p : PrimeSpectrum R) :
    PrimeSpectrum (Localization.AtPrime p.asIdeal) ≃o
      ({ Z : IrreducibleCloseds (PrimeSpectrum R) //
        p ∈ (Z : Set (PrimeSpectrum R)) })ᵒᵈ :=
  (primeSpectrumOrderIso (Localization.AtPrime p.asIdeal) p.asIdeal).trans <|
    ((pointsEquivIrreducibleClosedsContaining p).trans
      (irreducibleClosedsContainingOrderIso p))

private noncomputable def localizationAtPrimeIrreducibleClosedsSubtypeOrderIso
    (p : PrimeSpectrum R) :
    IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal)) ≃o
      { Z : IrreducibleCloseds (PrimeSpectrum R) //
        p ∈ (Z : Set (PrimeSpectrum R)) } :=
  ((PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization.AtPrime p.asIdeal)).symm.trans
    (PrimeSpectrum.localizationAtPrimeIrreducibleCloseds p)).dual

/-- Helper for Lemma 10.26.3: an irreducible closed set is an irreducible component exactly when
it is maximal among irreducible closed subsets. -/
private theorem mem_irreducibleComponents_iff_maximal_irreducibleClosed
    {X : Type*} [TopologicalSpace X] (Z : IrreducibleCloseds X) :
    (Z : Set X) ∈ irreducibleComponents X ↔
      Maximal (fun _ : IrreducibleCloseds X ↦ True) Z := by
  -- Rewrite irreducible components using the standard maximality characterization.
  rw [irreducibleComponents_eq_maximals_closed]
  constructor
  · intro h
    -- Any larger bundled irreducible closed set is still closed and irreducible as a set.
    refine ⟨trivial, ?_⟩
    intro W _ hZW
    exact h.2 ⟨W.isClosed, W.isIrreducible⟩ hZW
  · intro h
    -- Bundle a larger closed irreducible set and apply maximality there.
    refine ⟨⟨Z.isClosed, Z.isIrreducible⟩, ?_⟩
    intro s hs hZs
    let W : IrreducibleCloseds X := ⟨s, hs.2, hs.1⟩
    have hZW : Z ≤ W := hZs
    exact h.2 trivial hZW

/-- Helper for Lemma 10.26.3: once an irreducible closed set contains `p`, maximality among
irreducible closed subsets through `p` is the same as being an irreducible component. -/
private theorem maximal_containing_irreducibleClosed_iff_mem_irreducibleComponents
    (p : PrimeSpectrum R) (W : IrreducibleCloseds (PrimeSpectrum R))
    (hp : p ∈ (W : Set (PrimeSpectrum R))) :
    Maximal (fun Z : IrreducibleCloseds (PrimeSpectrum R) ↦
        p ∈ (Z : Set (PrimeSpectrum R))) W ↔
      (W : Set (PrimeSpectrum R)) ∈ irreducibleComponents (PrimeSpectrum R) := by
  constructor
  · intro h
    rw [mem_irreducibleComponents_iff_maximal_irreducibleClosed]
    -- A larger irreducible closed set automatically still contains `p`.
    refine ⟨trivial, ?_⟩
    intro Z _ hWZ
    exact h.2 (hWZ hp) hWZ
  · intro h
    rw [mem_irreducibleComponents_iff_maximal_irreducibleClosed] at h
    -- Global maximality immediately implies maximality in the smaller containing-`p` family.
    refine ⟨hp, ?_⟩
    intro Z _ hWZ
    exact h.2 trivial hWZ

/-- Helper for Lemma 10.26.3: maximality in a subtype is equivalent to maximality for the
underlying ambient predicate. -/
private theorem maximal_subtype_iff_maximal_predicate
    {α : Type*} [Preorder α] (P : α → Prop) (x : {a : α // P a}) :
    Maximal (fun _ : {a : α // P a} ↦ True) x ↔ Maximal P x.1 := by
  constructor
  · intro h
    -- Forget the subtype wrapper and keep the same order comparison.
    refine ⟨x.2, ?_⟩
    intro y hy hxy
    have hxy' : x ≤ ⟨y, hy⟩ := hxy
    exact h.2 trivial hxy'
  · intro h
    -- Repackage ambient candidates back into the subtype.
    refine ⟨trivial, ?_⟩
    intro y _ hxy
    exact h.2 y.2 hxy

/-- Helper for Lemma 10.26.3: the localization order isomorphism preserves maximal irreducible
closed subsets, after identifying the codomain subtype with the ambient containing-`p` predicate.
-/
private theorem localizationAtPrimeIrreducibleClosedsSubtypeOrderIso_preserves_maximal
    (p : PrimeSpectrum R)
    (Z : IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal))) :
    Maximal (fun _ :
        IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal)) ↦ True) Z ↔
      Maximal (fun W : IrreducibleCloseds (PrimeSpectrum R) ↦
          p ∈ (W : Set (PrimeSpectrum R)))
        (localizationAtPrimeIrreducibleClosedsSubtypeOrderIso p Z).1 := by
  let e := localizationAtPrimeIrreducibleClosedsSubtypeOrderIso p
  -- First transport maximality across the order isomorphism itself.
  have htransport :
      Maximal (fun _ :
          IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal)) ↦ True) Z ↔
        Maximal (fun _ :
            { W : IrreducibleCloseds (PrimeSpectrum R) //
              p ∈ (W : Set (PrimeSpectrum R)) } ↦ True)
          (e Z) := by
    constructor
    · intro h
      refine ⟨trivial, ?_⟩
      intro W _ hZW
      have hback : Z ≤ e.symm W := by
        simpa using e.symm.monotone hZW
      simpa using e.monotone (h.2 trivial hback)
    · intro h
      refine ⟨trivial, ?_⟩
      intro W _ hZW
      have hforward : e Z ≤ e W := e.monotone hZW
      simpa using e.symm.monotone (h.2 trivial hforward)
  -- Then forget the subtype wrapper on the codomain side.
  exact htransport.trans <|
    maximal_subtype_iff_maximal_predicate
      (fun W : IrreducibleCloseds (PrimeSpectrum R) ↦ p ∈ (W : Set (PrimeSpectrum R))) (e Z)

private theorem mem_irreducibleComponents_localizationAtPrimeIrreducibleClosedsSubtypeOrderIso_iff
    (p : PrimeSpectrum R)
    (Z : IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal))) :
    (Z : Set (PrimeSpectrum (Localization.AtPrime p.asIdeal))) ∈
        irreducibleComponents (PrimeSpectrum (Localization.AtPrime p.asIdeal)) ↔
      ((localizationAtPrimeIrreducibleClosedsSubtypeOrderIso p Z).1 : Set (PrimeSpectrum R)) ∈
        irreducibleComponents (PrimeSpectrum R) := by
  -- Route correction: transport the maximality characterization of irreducible components through
  -- the localization order isomorphism, then reinterpret the codomain subtype in `Spec R`.
  rw [mem_irreducibleComponents_iff_maximal_irreducibleClosed]
  rw [← maximal_containing_irreducibleClosed_iff_mem_irreducibleComponents
    p (localizationAtPrimeIrreducibleClosedsSubtypeOrderIso p Z).1
    (localizationAtPrimeIrreducibleClosedsSubtypeOrderIso p Z).2]
  -- The remaining step is exactly maximality preservation under the canonical order isomorphism.
  exact localizationAtPrimeIrreducibleClosedsSubtypeOrderIso_preserves_maximal p Z

/-- The minimal primes of `R_p` identify canonically, via an order isomorphism, with the
irreducible components of `Spec R` containing `p`. -/
noncomputable def PrimeSpectrum.localizationAtPrimeIrreducibleComponents
    (p : PrimeSpectrum R) :
    minimalPrimes (Localization.AtPrime p.asIdeal) ≃o
      ({ Z : irreducibleComponents (PrimeSpectrum R) //
        p ∈ (Z : Set (PrimeSpectrum R)) })ᵒᵈ :=
  let e :
      irreducibleComponents (PrimeSpectrum (Localization.AtPrime p.asIdeal)) ≃o
        { Z : irreducibleComponents (PrimeSpectrum R) //
          p ∈ (Z : Set (PrimeSpectrum R)) } :=
    ((irreducibleComponentsOrderIsoIrreducibleCloseds
        (PrimeSpectrum (Localization.AtPrime p.asIdeal))).trans
      (((localizationAtPrimeIrreducibleClosedsSubtypeOrderIso p).toEquiv.subtypeEquiv
        (fun Z ↦
          mem_irreducibleComponents_localizationAtPrimeIrreducibleClosedsSubtypeOrderIso_iff
            p Z)).toOrderIso
          (fun _ _ h ↦ (localizationAtPrimeIrreducibleClosedsSubtypeOrderIso p).monotone h)
          (fun _ _ h ↦ (localizationAtPrimeIrreducibleClosedsSubtypeOrderIso p).symm.monotone
            h))).trans
      (irreducibleComponentsContainingOrderIso p)
  (minimalPrimes.equivIrreducibleComponents (Localization.AtPrime p.asIdeal)).trans e.dual

/-- Lemma 10.26.3 (1): an irreducible closed subset of `Spec R` contains `p` if and only if it
arises from a unique prime of the localized ring `R_p`. -/
-- Proof sketch: use the canonical order isomorphism
-- `PrimeSpectrum.localizationAtPrimeIrreducibleCloseds p`; the unique-existence statement is the
-- source-facing unpacking of that owner-level bridge.
theorem irreducibleClosed_contains_iff_existsUnique_localizationPrime (p : PrimeSpectrum R)
    (Z : IrreducibleCloseds (PrimeSpectrum R)) :
    p ∈ (Z : Set (PrimeSpectrum R)) ↔
      ∃! q : PrimeSpectrum (Localization.AtPrime p.asIdeal),
        (PrimeSpectrum.localizationAtPrimeIrreducibleCloseds p q).1 = Z := by
  let e := PrimeSpectrum.localizationAtPrimeIrreducibleCloseds p
  constructor
  · intro hpZ
    refine ⟨e.symm ⟨Z, hpZ⟩, ?_, ?_⟩
    · simp [e]
    · intro q hq
      have hq' : e q = ⟨Z, hpZ⟩ := Subtype.ext hq
      exact e.injective (by simpa using hq')
  · rintro ⟨q, hq, -⟩
    have hqSet :
        ((((e q).1 : IrreducibleCloseds (PrimeSpectrum R)) : Set (PrimeSpectrum R))) =
          (Z : Set (PrimeSpectrum R)) :=
      congrArg (fun W : IrreducibleCloseds (PrimeSpectrum R) ↦ (W : Set (PrimeSpectrum R))) hq
    exact hqSet ▸ (e q).2

/-- Lemma 10.26.3 (2): an irreducible closed subset of `Spec R` is an irreducible component
containing `p` if and only if it arises from a unique minimal prime of the localized ring `R_p`. -/
-- Proof sketch: use the canonical order isomorphism
-- `PrimeSpectrum.localizationAtPrimeIrreducibleComponents p`; the unique-existence statement is
-- the source-facing unpacking of the owner-level minimal-prime/component bridge.
theorem irreducibleComponent_contains_iff_existsUnique_localizationMinimalPrime
    (p : PrimeSpectrum R) (Z : IrreducibleCloseds (PrimeSpectrum R)) :
    ((Z : Set (PrimeSpectrum R)) ∈ irreducibleComponents (PrimeSpectrum R) ∧
        p ∈ (Z : Set (PrimeSpectrum R))) ↔
      ∃! q : minimalPrimes (Localization.AtPrime p.asIdeal),
        ((PrimeSpectrum.localizationAtPrimeIrreducibleComponents p q).1 : Set (PrimeSpectrum R))
          = Z := by
  let e := PrimeSpectrum.localizationAtPrimeIrreducibleComponents p
  constructor
  · rintro ⟨hZ, hpZ⟩
    refine ⟨e.symm ⟨⟨Z, hZ⟩, hpZ⟩, ?_, ?_⟩
    · simp [e]
    · intro q hq
      have hq' : e q = ⟨⟨Z, hZ⟩, hpZ⟩ := by
        apply Subtype.ext
        exact Subtype.ext hq
      exact e.injective (by simpa using hq')
  · rintro ⟨q, hq, -⟩
    have hcomp : (Z : Set (PrimeSpectrum R)) ∈ irreducibleComponents (PrimeSpectrum R) := by
      have hqComp :
          (((e q).1 : irreducibleComponents (PrimeSpectrum R)) : Set (PrimeSpectrum R)) ∈
            irreducibleComponents (PrimeSpectrum R) :=
        (e q).1.2
      exact hq ▸ hqComp
    have hpZ : p ∈ (Z : Set (PrimeSpectrum R)) := by
      have hqSet :
          ((((e q).1 : irreducibleComponents (PrimeSpectrum R)) : Set (PrimeSpectrum R))) =
            (Z : Set (PrimeSpectrum R)) :=
        hq
      exact hqSet ▸ (e q).2
    exact ⟨hcomp, hpZ⟩

end

/-! ### Lemma_10_26_4 (from Chap10) -/
universe u

section

open PrimeSpectrum
open TopologicalSpace
open scoped BigOperators

variable {R : Type u} [CommRing R]

-- Layering for this item:
-- * source-facing: the set-theoretic formulation `D(f) ∩ W = ∅` in the second theorem.
-- * core/canonical owner: `CompactOpens (PrimeSpectrum R)` together with
--   `PrimeSpectrum.isCompact_isOpen_iff_ideal`.
-- * bridge/view: the second theorem rewrites `Disjoint` back to the textbook equality.

/-- Lemma 10.26.4, in library-facing owner form: if `p` is a minimal prime of `R` and `W` is a
compact open subset of `Spec R` not containing `p`, then some basic open neighborhood `D(f)` of
`p` is disjoint from `W`. -/
-- Proof sketch: cover the quasi-compact open `W` by finitely many basic opens `D(gᵢ)`. Since
-- `p ∉ W`, each `gᵢ` lies in `p.asIdeal`, hence becomes nilpotent in `Localization.AtPrime p.asIdeal`
-- by Lemma `10.25.1`. Clear denominators for the finitely many nilpotence relations to obtain
-- `f ∉ p.asIdeal` with `f * gᵢ ^ nᵢ = 0` for all `i`, which forces `D(f)` to miss each `D(gᵢ)`.
theorem exists_basicOpen_disjoint_of_isCompact_open_not_mem_of_mem_minimalPrimes
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R)
    (W : CompactOpens (PrimeSpectrum R)) (hpW : p ∉ W) :
    ∃ f : R, p ∈ basicOpen f ∧
      Disjoint (basicOpen f : Set (PrimeSpectrum R)) (W : Set (PrimeSpectrum R)) := by
  classical
  let pmin : minimalPrimes R := ⟨p.asIdeal, hp⟩
  obtain ⟨I, hIFG, hW⟩ :=
    (PrimeSpectrum.isCompact_isOpen_iff_ideal :
      IsCompact (W : Set (PrimeSpectrum R)) ∧ IsOpen (W : Set (PrimeSpectrum R)) ↔
        ∃ I : Ideal R, I.FG ∧
          (zeroLocus (I : Set R))ᶜ = (W : Set (PrimeSpectrum R))).mp ⟨W.isCompact, W.isOpen⟩
  obtain ⟨t, htI⟩ := hIFG
  have hpz : p ∈ zeroLocus (I : Set R) := by
    change p ∉ (W : Set (PrimeSpectrum R)) at hpW
    rw [← hW] at hpW
    simpa [Set.mem_compl_iff] using hpW
  have hIp : I ≤ p.asIdeal :=
    (mem_zeroLocus p (I : Set R)).mp hpz
  have hs :
      ∀ g : t, ∃ s : p.asIdeal.primeCompl, ∃ n : ℕ, 0 < n ∧ (s : R) * (g : R) ^ n = 0 := by
    intro g
    have hgmax :
        algebraMap R (Localization.AtPrime p.asIdeal) (g : R) ∈
          IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) := by
      change (g : R) ∈
        Ideal.comap (algebraMap R (Localization.AtPrime p.asIdeal))
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
      rw [Localization.AtPrime.comap_maximalIdeal]
      exact hIp <| by
        rw [← htI]
        exact Ideal.subset_span g.2
    obtain ⟨n, hn⟩ :=
      isNilpotent_of_mem_maximalIdeal_localizationAtPrime_of_minimalPrime pmin hgmax
    have hnpos : 0 < n := by
      refine Nat.pos_of_ne_zero fun h0 ↦ ?_
      simp [h0] at hn
    obtain ⟨s, hs⟩ :=
      (IsLocalization.map_eq_zero_iff p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
        ((g : R) ^ n)).mp <| by
          simpa [map_pow] using hn
    exact ⟨s, n, hnpos, hs⟩
  choose s n hnpos hzero using hs
  let f : R := Finset.univ.prod fun g : t ↦ (s g : R)
  refine ⟨f, ?_, ?_⟩
  · change f ∉ p.asIdeal
    have hf : f ∈ p.asIdeal.primeCompl := by
      simpa [f] using
        (Submonoid.prod_mem p.asIdeal.primeCompl fun g _ ↦ (s g).2)
    exact hf
  · refine Set.disjoint_left.2 fun x hxf hxW ↦ ?_
    have hsf :
        ∀ g : t, (s g : R) ∉ x.asIdeal := by
      intro g hsg
      apply hxf
      have hprod :
          f ∈ x.asIdeal ↔ ∃ g ∈ (Finset.univ : Finset t), (s g : R) ∈ x.asIdeal := by
        exact x.2.prod_mem_iff
      exact hprod.mpr ⟨g, by simp, hsg⟩
    have hxz : x ∉ zeroLocus (t : Set R) := by
      change x ∈ (W : Set (PrimeSpectrum R)) at hxW
      rw [← hW] at hxW
      have hxI : ¬ I ≤ x.asIdeal := by
        simpa [mem_zeroLocus, Set.mem_compl_iff] using hxW
      intro hxt
      apply hxI
      rw [← htI]
      exact Ideal.span_le.mpr hxt
    rw [mem_zeroLocus, Set.not_subset] at hxz
    obtain ⟨g, hg, hxg⟩ := hxz
    let g' : t := ⟨g, hg⟩
    have hxs : x ∈ basicOpen (s g' : R) :=
      hsf g'
    have hxg' : x ∈ basicOpen (g' : R) := by
      simpa [g'] using hxg
    have hxgn : x ∈ basicOpen ((g' : R) ^ n g') := by
      rw [basicOpen_pow (g' : R) (n g') (hnpos g')]
      exact hxg'
    have : x ∈ (basicOpen ((s g' : R) * (g' : R) ^ n g') : Set (PrimeSpectrum R)) := by
      rw [basicOpen_mul]
      exact ⟨hxs, hxgn⟩
    simpa [g', hzero g'] using this

/-- Textbook wording of Lemma 10.26.4: the disjoint basic open can be chosen as `D(f)` with
`f ∉ p`, equivalently `p ∈ D(f)`, and disjointness is the set-theoretic equality
`D(f) ∩ W = ∅`. -/
theorem exists_basicOpen_disjoint_set_of_isCompact_open_not_mem_of_mem_minimalPrimes
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R)
    (W : Opens (PrimeSpectrum R)) (hWqc : IsCompact (W : Set (PrimeSpectrum R))) (hpW : p ∉ W) :
    ∃ f : R, f ∉ p.asIdeal ∧
      ((basicOpen f : Set (PrimeSpectrum R)) ∩ (W : Set (PrimeSpectrum R)) = ∅) := by
  let Wc : CompactOpens (PrimeSpectrum R) := ⟨⟨(W : Set (PrimeSpectrum R)), hWqc⟩, W.isOpen⟩
  rcases exists_basicOpen_disjoint_of_isCompact_open_not_mem_of_mem_minimalPrimes p hp Wc hpW with
    ⟨f, hf, hdisj⟩
  exact ⟨f, hf, by simpa [Set.disjoint_iff_inter_eq_empty] using hdisj⟩

end

/-! ### Lemma_10_26_5 (from Chap10) -/
universe u

open Set PrimeSpectrum TopologicalSpace

section

variable {R : Type u} [CommRing R]

private theorem isClosed_of_isCompact_open_of_basicOpen_closed
    (hbasic : ∀ f : R, IsClosed ((basicOpen f : Set (PrimeSpectrum R)))) :
    ∀ U : Set (PrimeSpectrum R), IsOpen U → IsCompact U → IsClosed U := by
  intro U hU hUcompact
  obtain ⟨t, ht⟩ := PrimeSpectrum.isCompact_isOpen_iff.mp ⟨hUcompact, hU⟩
  have hUeq : U = ⋃ f ∈ t, (basicOpen f : Set (PrimeSpectrum R)) := by
    rw [← ht]
    ext x
    simp [basicOpen_eq_zeroLocus_compl, mem_zeroLocus, Set.not_subset]
  rw [hUeq]
  exact isClosed_biUnion_finset fun f _ ↦ hbasic f

/-- In `Spec R`, being the generic point of its irreducible component is equivalent to `p`
corresponding to a minimal prime ideal of `R`; this is the source-facing companion to the
canonical irreducible-component/minimal-prime correspondence on `Spec R`. -/
theorem isGenericPoint_irreducibleComponent_iff_mem_minimalPrimes (p : PrimeSpectrum R) :
    IsGenericPoint p (irreducibleComponent p) ↔ p.asIdeal ∈ minimalPrimes R := by
  rw [isGenericPoint_def]
  constructor
  · intro hp
    have hcomponent :
        closure ({p} : Set (PrimeSpectrum R)) ∈ irreducibleComponents (PrimeSpectrum R) :=
      hp ▸ irreducibleComponent_mem_irreducibleComponents p
    rw [← vanishingIdeal_singleton]
    exact vanishingIdeal_mem_minimalPrimes.mpr hcomponent
  · intro hp
    have hcomponent :
        closure ({p} : Set (PrimeSpectrum R)) ∈ irreducibleComponents (PrimeSpectrum R) := by
      rw [← vanishingIdeal_singleton] at hp
      exact vanishingIdeal_mem_minimalPrimes.mp hp
    have hsubset :
        closure ({p} : Set (PrimeSpectrum R)) ⊆ irreducibleComponent p := by
      exact closure_minimal (singleton_subset_iff.mpr mem_irreducibleComponent)
        isClosed_irreducibleComponent
    exact Set.Subset.antisymm hsubset <|
      hcomponent.2 isIrreducible_irreducibleComponent hsubset

/-- Lemma 10.26.5: for a commutative ring `R`, the following equivalent conditions on `Spec R`
use the canonical topological predicates from Chapter 5, together with the spectrum-specific basic
open criterion. The textbook ring-theoretic clauses are recovered from these by
`PrimeSpectrum.le_iff_specializes`, `PrimeSpectrum.isClosed_singleton_iff_isMaximal`, and
`isGenericPoint_irreducibleComponent_iff_mem_minimalPrimes`. -/
-- Proof sketch: specialize `spectralSpace_profinite_criteria` to `PrimeSpectrum R`, using Lemma
-- `10.26.2` for spectrality. The only additional clause is closedness of basic opens, which is
-- equivalent to closedness of all quasi-compact opens by quasi-compactness of `D(f)` and Lemma
-- `10.26.4`.
theorem primeSpectrum_profinite_tfae :
    List.TFAE
      [ ∃ P : Profinite.{u}, Nonempty (PrimeSpectrum R ≃ₜ P),
        T2Space (PrimeSpectrum R),
        TotallyDisconnectedSpace (PrimeSpectrum R),
        ∀ U : Set (PrimeSpectrum R), IsOpen U → IsCompact U → IsClosed U,
        ∀ ⦃p q : PrimeSpectrum R⦄, p ⤳ q → p = q,
        ∀ p : PrimeSpectrum R, IsClosed ({p} : Set (PrimeSpectrum R)),
        ∀ p : PrimeSpectrum R, IsGenericPoint p (irreducibleComponent p),
        ∀ f : R, IsClosed ((basicOpen f : Set (PrimeSpectrum R))) ] := by
  classical
  let howner := spectralSpace_profinite_criteria (PrimeSpectrum R)
  tfae_have 1 → 2 := by
    intro h
    exact (howner.out 0 1).mp h
  tfae_have 2 → 3 := by
    intro h
    exact (howner.out 1 2).mp h
  tfae_have 3 → 4 := by
    intro h
    exact (howner.out 2 3).mp h
  tfae_have 4 → 5 := by
    intro h
    exact (howner.out 3 4).mp h
  tfae_have 5 → 6 := by
    intro h
    exact (howner.out 4 5).mp h
  tfae_have 6 → 7 := by
    intro h
    exact (howner.out 5 6).mp h
  tfae_have 7 → 8 := by
    intro h p
    have hclosed :
        ∀ U : Set (PrimeSpectrum R), IsOpen U → IsCompact U → IsClosed U :=
      (howner.out 6 3).mp h
    exact hclosed _ isOpen_basicOpen (isCompact_basicOpen p)
  tfae_have 8 → 1 := by
    intro h
    exact (howner.out 3 0).mp (isClosed_of_isCompact_open_of_basicOpen_closed h)
  tfae_finish

end
