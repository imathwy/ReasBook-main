import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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

private theorem mem_irreducibleComponents_localizationAtPrimeIrreducibleClosedsSubtypeOrderIso_iff
    (p : PrimeSpectrum R)
    (Z : IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal))) :
    (Z : Set (PrimeSpectrum (Localization.AtPrime p.asIdeal))) ∈
        irreducibleComponents (PrimeSpectrum (Localization.AtPrime p.asIdeal)) ↔
      ((localizationAtPrimeIrreducibleClosedsSubtypeOrderIso p Z).1 : Set (PrimeSpectrum R)) ∈
        irreducibleComponents (PrimeSpectrum R) := sorry

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
