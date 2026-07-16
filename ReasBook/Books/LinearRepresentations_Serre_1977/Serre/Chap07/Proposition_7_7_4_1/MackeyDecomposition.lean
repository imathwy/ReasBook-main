import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_4_1.IntertwiningAndInduction

noncomputable section

universe u v

namespace Representation

section MackeyIrreducibilityCriterion

open Rep (of)
open CategoryTheory

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G] [NeZero (Nat.card G : k)]
variable {V : Type v} [AddCommGroup V] [Module k V]

local instance instDecidableEqDoubleCosetQuotientMackeyDecomposition (H : Subgroup G) :
    DecidableEq (DoubleCoset.Quotient (H : Set G) H) :=
  Classical.decEq _

/-- Helper for Proposition 7-7.4-1: lifting the double-coset index aligns the Mackey-index
universe with the `ULift` carrier used for `ρ`. -/
theorem ulift_doubleCosetRepresentative_bijective
    (H : Subgroup G) :
    Function.Bijective
      (fun q : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
        DoubleCoset.mk H H (doubleCosetRepresentative H q.down)) := by
  constructor
  · intro a b hab
    apply ULift.ext
    simpa [doubleCosetRepresentative_spec] using hab
  · intro q
    refine ⟨⟨q⟩, ?_⟩
    simpa [doubleCosetRepresentative_spec]
/-- Helper for Proposition 7-7.4-1: replacing `ρ` by its `ULift` model does not change the Mackey
summands after inducing from the Mackey subgroup. -/
noncomputable def mackeySummand_ulift_equiv
    (H : Subgroup G) (ρ : Representation k H V) (s : G) :
    (mackeySummand H H (of (uliftRepresentation (k := k) ρ)) s).ρ.Equiv
      (mackeySummand H H (of ρ) s).ρ := by
  let eTwist :
      (mackeyTwist H H (of ρ) s).ρ.Equiv
        (mackeyTwist H H (of (uliftRepresentation (k := k) ρ)) s).ρ := by
    -- Restriction commutes definitionally with the `ULift` carrier model.
    simpa [mackeyTwist] using
      (uliftRepresentationEquiv (k := k) ((mackeyTwist H H (of ρ) s).ρ))
  -- Once the twisted source is aligned, induction carries the equivalence to the summands.
  simpa [mackeySummand] using
    inducedRepresentationEquiv (k := k) (H := mackeySubgroup H H s) eTwist.symm
/-- Helper for Proposition 7-7.4-1: the `ULift`-removal equivalence on a Mackey summand sends the
standard seed generator with lifted coefficient back to the original seed generator. -/
theorem mackeySummand_ulift_equiv_apply_mk_one
    (H : Subgroup G) (ρ : Representation k H V) (s : G)
    (x : mackeyTwist H H (of ρ) s) :
    (mackeySummand_ulift_equiv (k := k) H ρ s).toLinearEquiv
      (Representation.IndV.mk
        (mackeySubgroup H H s).subtype
        ((mackeyTwist H H (of (uliftRepresentation (k := k) ρ)) s).ρ)
        1 (ULift.up x)) =
      Representation.IndV.mk
        (mackeySubgroup H H s).subtype
        ((mackeyTwist H H (of ρ) s).ρ)
        1 x := by
  -- The induced `ULift` equivalence acts coefficientwise on the standard seed generator.
  simp [mackeySummand_ulift_equiv, inducedRepresentationEquiv, uliftRepresentationEquiv,
    mackeySummand, mackeyTwist, Representation.IndV.mk]
  rfl

/-- Helper for Proposition 7-7.4-1: the inverse `ULift`-removal equivalence on one Mackey
summand sends the original seed generator to the lifted seed generator. -/
theorem mackeySummand_ulift_equiv_symm_apply_mk_one
    (H : Subgroup G) (ρ : Representation k H V) (s : G)
    (x : mackeyTwist H H (of ρ) s) :
    (mackeySummand_ulift_equiv (k := k) H ρ s).symm.toLinearEquiv
      (Representation.IndV.mk
        (mackeySubgroup H H s).subtype
        ((mackeyTwist H H (of ρ) s).ρ)
        1 x) =
      Representation.IndV.mk
        (mackeySubgroup H H s).subtype
        ((mackeyTwist H H (of (uliftRepresentation (k := k) ρ)) s).ρ)
        1 (ULift.up x) := by
  -- Apply the forward `ULift`-removal equivalence to reduce the inverse seed statement to the
  -- already-established forward seed computation.
  apply (mackeySummand_ulift_equiv (k := k) H ρ s).toLinearEquiv.injective
  simpa using mackeySummand_ulift_equiv_apply_mk_one (k := k) H ρ s x
/-- Helper for Proposition 7-7.4-1: the componentwise `ULift`-removal linear map on the Mackey
direct sum sends the `q`-summand seed with lifted coefficient to the corresponding unlifted seed.
-/
theorem mackey_directSum_ulift_lmap_apply_lof_seed
    (H : Subgroup G) (ρ : Representation k H V)
    (q : ULift (DoubleCoset.Quotient (H : Set G) H))
    (x : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q.down)) :
    (DirectSum.lmap fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
        (mackeySummand_ulift_equiv (k := k) H ρ (doubleCosetRepresentative H q'.down)).toLinearEquiv.toLinearMap :
        DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H))
          (fun q' ↦
            Representation.IndV
              (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
              ((mackeyTwist H H (of (uliftRepresentation (k := k) ρ))
                (doubleCosetRepresentative H q'.down)).ρ)) →ₗ[k]
        DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H))
          (fun q' ↦
            Representation.IndV
              (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
              ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q'.down)).ρ)))
      (DirectSum.lof k _
        (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
          Representation.IndV
            (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
            ((mackeyTwist H H (of (uliftRepresentation (k := k) ρ))
              (doubleCosetRepresentative H q'.down)).ρ))
        q
        (Representation.IndV.mk
          (mackeySubgroup H H (doubleCosetRepresentative H q.down)).subtype
          ((mackeyTwist H H (of (uliftRepresentation (k := k) ρ))
            (doubleCosetRepresentative H q.down)).ρ)
          1 (ULift.up x))) =
      DirectSum.lof k _
        (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
          Representation.IndV
            (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
            ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q'.down)).ρ))
        q
        (Representation.IndV.mk
          (mackeySubgroup H H (doubleCosetRepresentative H q.down)).subtype
          ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q.down)).ρ)
  1 x) := by
  -- `DirectSum.lmap` only touches the active `q`-component, and the single-block computation was
  -- already proved in `mackeySummand_ulift_equiv_apply_mk_one`.
  rw [DirectSum.lmap_lof]
  exact congrArg
    (DirectSum.lof k _
      (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
        Representation.IndV
          (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
          ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q'.down)).ρ))
      q)
    (mackeySummand_ulift_equiv_apply_mk_one (k := k) H ρ
      (doubleCosetRepresentative H q.down) x)

/-- Helper for Proposition 7-7.4-1: the inverse componentwise `ULift`-removal linear map on the
Mackey direct sum sends the `q`-summand seed back to the lifted seed. -/
theorem mackey_directSum_ulift_lmap_inv_apply_lof_seed
    (H : Subgroup G) (ρ : Representation k H V)
    (q : ULift (DoubleCoset.Quotient (H : Set G) H))
    (x : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q.down)) :
    (DirectSum.lmap fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
        (mackeySummand_ulift_equiv (k := k) H ρ
          (doubleCosetRepresentative H q'.down)).symm.toLinearEquiv.toLinearMap :
        DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H))
          (fun q' ↦
            Representation.IndV
              (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
              ((mackeyTwist H H (of ρ)
                (doubleCosetRepresentative H q'.down)).ρ)) →ₗ[k]
        DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H))
          (fun q' ↦
            Representation.IndV
              (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
              ((mackeyTwist H H (of (uliftRepresentation (k := k) ρ))
                (doubleCosetRepresentative H q'.down)).ρ)))
      (DirectSum.lof k _
        (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
          Representation.IndV
            (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
            ((mackeyTwist H H (of ρ)
              (doubleCosetRepresentative H q'.down)).ρ))
        q
        (Representation.IndV.mk
          (mackeySubgroup H H (doubleCosetRepresentative H q.down)).subtype
          ((mackeyTwist H H (of ρ)
            (doubleCosetRepresentative H q.down)).ρ)
          1 x)) =
      DirectSum.lof k _
        (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
          Representation.IndV
            (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
            ((mackeyTwist H H (of (uliftRepresentation (k := k) ρ))
              (doubleCosetRepresentative H q'.down)).ρ))
        q
        (Representation.IndV.mk
          (mackeySubgroup H H (doubleCosetRepresentative H q.down)).subtype
          ((mackeyTwist H H (of (uliftRepresentation (k := k) ρ))
            (doubleCosetRepresentative H q.down)).ρ)
          1 (ULift.up x)) := by
  -- The inverse `DirectSum.lmap` again only touches the active `q`-component, so the inverse
  -- seed computation reduces to the one-block inverse theorem above.
  rw [DirectSum.lmap_lof]
  exact congrArg
    (DirectSum.lof k _
      (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
        Representation.IndV
          (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
          ((mackeyTwist H H (of (uliftRepresentation (k := k) ρ))
            (doubleCosetRepresentative H q'.down)).ρ))
      q)
    (mackeySummand_ulift_equiv_symm_apply_mk_one (k := k) H ρ
      (doubleCosetRepresentative H q.down) x)

/-- Helper for Proposition 7-7.4-1: the `ULift`-indexed family of Mackey summand representations
before removing the lift on coefficients. -/
abbrev mackey_ulift_summand_family
    (H : Subgroup G) (ρ : Representation k H V) :
    ULift (DoubleCoset.Quotient (H : Set G) H) → Rep k H :=
  fun q ↦
    mackeySummand H H (of (uliftRepresentation (k := k) ρ))
      (doubleCosetRepresentative H q.down)

/-- Helper for Proposition 7-7.4-1: the `ULift`-indexed family of Mackey summand representations
after removing the lift on coefficients. -/
abbrev mackey_summand_family
    (H : Subgroup G) (ρ : Representation k H V) :
    ULift (DoubleCoset.Quotient (H : Set G) H) → Rep k H :=
  fun q ↦
    mackeySummand H H (of ρ) (doubleCosetRepresentative H q.down)

/-- Helper for Proposition 7-7.4-1: removing the `ULift` on each Mackey summand is the explicit
componentwise direct-sum equivalence built from `DirectSum.lmap`. -/
noncomputable def mackey_directSum_ulift_iso
    (H : Subgroup G) (ρ : Representation k H V) :
    Rep.of
        (Representation.directSum fun q ↦
          (mackey_ulift_summand_family (k := k) H ρ q).ρ) ≅
      Rep.of
        (Representation.directSum fun q ↦
          (mackey_summand_family (k := k) H ρ q).ρ) := by
  -- Route correction: expose the outer ULift-removal stage as the concrete componentwise
  -- `DirectSum.lmap`, instead of hiding it inside an opaque `Classical.choice`.
  refine Rep.mkIso <| Representation.Equiv.mk ?_ ?_
  · exact
      DirectSum.congrLinearEquiv fun q : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
        (mackeySummand_ulift_equiv (k := k) H ρ
          (doubleCosetRepresentative H q.down)).toLinearEquiv
  · -- Equivariance is checked componentwise on each Mackey summand.
    exact
      directSum_componentwise_intertwines
        (fun q : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
          (mackey_ulift_summand_family (k := k) H ρ q).ρ)
        (fun q : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
          (mackey_summand_family (k := k) H ρ q).ρ)
        (fun q ↦
          mackeySummand_ulift_equiv (k := k) H ρ
            (doubleCosetRepresentative H q.down))
/-- Helper for Proposition 7-7.4-1: Mackey's decomposition gives the restriction of
`Ind_H^G(ρ)` to `H` as the direct sum of the Mackey summands indexed by the universe-lifted
double-coset space. -/
noncomputable def induced_restriction_mackey_iso
    (H : Subgroup G) (ρ : Representation k H V) :
    Rep.res H.subtype (Rep.ind H.subtype (of ρ)) ≅
      Rep.of
        (Representation.directSum fun q : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
          (mackeySummand H H (of ρ) (doubleCosetRepresentative H q.down)).ρ) := by
  classical
  let ρu : Representation k H (ULift.{u} V) := uliftRepresentation (k := k) ρ
  let eInd :
      (Rep.ind H.subtype (of ρ)).ρ.Equiv
        (Rep.ind H.subtype (of ρu)).ρ :=
    inducedRepresentationEquiv (k := k) H (uliftRepresentationEquiv (k := k) ρ)
  let hSource :
      Rep.res H.subtype (Rep.ind H.subtype (of ρ)) ≅
        Rep.res H.subtype (Rep.ind H.subtype (of ρu)) :=
    (Rep.resFunctor H.subtype).mapIso (Rep.mkIso eInd)
  let hMackeyULift :
      Rep.res H.subtype (Rep.ind H.subtype (of ρu)) ≅
        Rep.of
          (Representation.directSum fun q : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
            (mackeySummand H H (of ρu) (doubleCosetRepresentative H q.down)).ρ) :=
    restriction_induced_mackeyDirectSum_iso
      (ι := ULift (DoubleCoset.Quotient (H : Set G) H))
      (K := H) (H := H) (W := of ρu)
      (s := fun q ↦ doubleCosetRepresentative H q.down)
      (ulift_doubleCosetRepresentative_bijective H)
  -- Route correction: use a universe-stable `ULift` index first, then remove the `ULift`
  -- from the Mackey summands through the explicit owner `mackey_directSum_ulift_iso`.
  exact hSource ≪≫ hMackeyULift ≪≫ mackey_directSum_ulift_iso (k := k) H ρ
/-- Helper for Proposition 7-7.4-1: the underlying linear map of a representation isomorphism is
injective. -/
theorem rep_iso_hom_injective
    {Γ : Type*} [Group Γ]
    {A B : Rep k Γ} (i : A ≅ B) :
    Function.Injective i.hom.hom := by
  intro a b hab
  simpa using congrArg i.inv.hom hab
end MackeyIrreducibilityCriterion

end Representation
