import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_4_1.MackeyDecomposition
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_4_1.IdentityBlockIrreducibility

noncomputable section

universe u v

namespace Representation

section MackeyIrreducibilityCriterion

open Rep (of)
open CategoryTheory

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G] [NeZero (Nat.card G : k)]
variable {V : Type v} [AddCommGroup V] [Module k V]

local instance instDecidableEqDoubleCosetQuotientMackeySeedTransport (H : Subgroup G) :
    DecidableEq (DoubleCoset.Quotient (H : Set G) H) :=
  Classical.decEq _

/-- Helper for Proposition 7-7.4-1: the explicit direct-sum `ULift`-removal isomorphism sends a
single lifted Mackey seed to the corresponding unlifted seed. -/
theorem mackey_directSum_ulift_iso_hom_apply_lof_seed
    (H : Subgroup G) (ρ : Representation k H V)
    (q : ULift (DoubleCoset.Quotient (H : Set G) H))
    (x : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q.down)) :
    ((mackey_directSum_ulift_iso H ρ).hom.hom)
      (DirectSum.lof k _
        (fun q' ↦ (mackey_ulift_summand_family (k := k) H ρ q').V)
        q
        (Representation.IndV.mk
          (mackeySubgroup H H (doubleCosetRepresentative H q.down)).subtype
          ((mackeyTwist H H (of (uliftRepresentation (k := k) ρ))
            (doubleCosetRepresentative H q.down)).ρ)
          1 (ULift.up x))) =
      DirectSum.lof k _
        (fun q' ↦ (mackey_summand_family (k := k) H ρ q').V)
        q
        (Representation.IndV.mk
          (mackeySubgroup H H (doubleCosetRepresentative H q.down)).subtype
          ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q.down)).ρ)
          1 x) := by
  -- The owner map is now literally the componentwise `DirectSum.lmap`, so the seed formula is
  -- the existing direct-sum computation from the owner file.
  change
    (DirectSum.congrLinearEquiv
        (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
          (mackeySummand_ulift_equiv (k := k) H ρ
            (doubleCosetRepresentative H q'.down)).toLinearEquiv)).toLinearMap
      (DirectSum.lof k _
        (fun q' ↦ (mackey_ulift_summand_family (k := k) H ρ q').V)
        q
        (Representation.IndV.mk
          (mackeySubgroup H H (doubleCosetRepresentative H q.down)).subtype
          ((mackeyTwist H H (of (uliftRepresentation (k := k) ρ))
            (doubleCosetRepresentative H q.down)).ρ)
          1 (ULift.up x))) =
      DirectSum.lof k _
        (fun q' ↦ (mackey_summand_family (k := k) H ρ q').V)
        q
        (Representation.IndV.mk
          (mackeySubgroup H H (doubleCosetRepresentative H q.down)).subtype
          ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q.down)).ρ)
          1 x)
  rw [DirectSum.congrLinearEquiv_toLinearMap]
  exact mackey_directSum_ulift_lmap_apply_lof_seed (k := k) H ρ q x

omit [Finite G] [NeZero (Nat.card G : k)] in
/-- Helper for Proposition 7-7.4-1: Mackey's decomposition gives the restriction of
`Ind_H^G(ρ)` to `H` as the direct sum of the Mackey summands indexed by the universe-lifted
double-coset space. -/
theorem induced_restriction_source_ulift_iso_hom_apply_translated_seed
    (H : Subgroup G) (ρ : Representation k H V)
    (q : DoubleCoset.Quotient (H : Set G) H)
    (x : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q)) :
    let e :
        Rep.res H.subtype (Rep.ind H.subtype (of ρ)) ≅
          Rep.res H.subtype (Rep.ind H.subtype (of (uliftRepresentation (k := k) ρ))) :=
      (Rep.resFunctor H.subtype).mapIso
        (Rep.mkIso
          (inducedRepresentationEquiv (k := k) H
            (uliftRepresentationEquiv (k := k) ρ)))
    (e.hom.hom :
        Representation.IndV H.subtype ρ →ₗ[k]
          Representation.IndV H.subtype (uliftRepresentation (k := k) ρ))
      (Representation.IndV.mk H.subtype ρ (doubleCosetRepresentative H q)⁻¹ x) =
      Representation.IndV.mk H.subtype (uliftRepresentation (k := k) ρ)
        (doubleCosetRepresentative H q)⁻¹ (ULift.up x) := by
  -- The source-side equivalence is definitionally induced by the `ULift` carrier equivalence.
  rfl

omit [Finite G] [NeZero (Nat.card G : k)] in
/-- Helper for Proposition 7-7.4-1: the local forward-proof aliases really are the translated
source seed, its target index, and the standard block seed. -/
theorem induced_restriction_mackey_ulift_aliases
    (H : Subgroup G) (ρ : Representation k H V)
    (q : DoubleCoset.Quotient (H : Set G) H)
    (x : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q)) :
    let ρu : Representation k H (ULift.{u} V) := uliftRepresentation (k := k) ρ
    let qU : ULift (DoubleCoset.Quotient (H : Set G) H) := ⟨q⟩
    let yu :
        Representation.IndV H.subtype ρu :=
      Representation.IndV.mk H.subtype ρu (doubleCosetRepresentative H q)⁻¹ (ULift.up x)
    let blockSeed :
        Representation.IndV
          (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype
          ((mackeyTwist H H (of ρu) (doubleCosetRepresentative H q)).ρ) :=
      Representation.IndV.mk
        (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype
        ((mackeyTwist H H (of ρu) (doubleCosetRepresentative H q)).ρ)
        1 (ULift.up x)
    qU = ⟨q⟩ ∧
      yu =
        Representation.IndV.mk H.subtype ρu (doubleCosetRepresentative H q)⁻¹ (ULift.up x) ∧
      blockSeed =
        Representation.IndV.mk
          (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype
          ((mackeyTwist H H (of ρu) (doubleCosetRepresentative H q)).ρ)
          1 (ULift.up x) := by
  -- Each local alias is definitionally the object named in the source-guided Mackey skeleton.
  simp

omit [NeZero (Nat.card G : k)] in
/-- Helper for Proposition 7-7.4-1: the middle Mackey decomposition stage already sends the
translated lifted seed to the corresponding `q`-summand seed before the outer `ULift` removal. -/
theorem mackey_ulift_middle_stage_seed_explicit
    (H : Subgroup G) (ρ : Representation k H V)
    (q : DoubleCoset.Quotient (H : Set G) H)
    (x : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q)) :
    let ρu : Representation k H (ULift.{u} V) := uliftRepresentation (k := k) ρ
    let hMackeyULift :
        Rep.res H.subtype (Rep.ind H.subtype (of ρu)) ≅
          Rep.of
            (Representation.directSum fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
              (mackeySummand H H (of ρu) (doubleCosetRepresentative H q'.down)).ρ) :=
      restriction_induced_mackeyDirectSum_iso
        (ι := ULift (DoubleCoset.Quotient (H : Set G) H))
        (K := H) (H := H) (W := of ρu)
        (s := fun q' ↦ doubleCosetRepresentative H q'.down)
        (ulift_doubleCosetRepresentative_bijective H)
    let yu : Representation.IndV H.subtype ρu :=
      Representation.IndV.mk H.subtype ρu (doubleCosetRepresentative H q)⁻¹ (ULift.up x)
    hMackeyULift.hom.hom yu =
      DirectSum.lof k _
        (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
          Representation.IndV
            (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
            ((mackeyTwist H H (of ρu) (doubleCosetRepresentative H q'.down)).ρ))
        ⟨q⟩
        (Representation.IndV.mk
          (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype
          ((mackeyTwist H H (of ρu) (doubleCosetRepresentative H q)).ρ)
          1 (ULift.up x)) := by
  -- Route correction: use the new explicit 7.3 seed corollary, so this transport layer no longer
  -- depends on the private abbreviation names from the owner file.
  simpa using
    restriction_induced_mackeyDirectSum_iso_hom_apply_translated_seed
      (k := k)
      (K := H) (H := H)
      (W := of (uliftRepresentation (k := k) ρ))
      (s := fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
        doubleCosetRepresentative H q'.down)
      (ulift_doubleCosetRepresentative_bijective H)
      ⟨q⟩
      (ULift.up x)

omit [Finite G] [NeZero (Nat.card G : k)] in
/-- Helper for Proposition 7-7.4-1: once the middle Mackey block computation is known, the
source-side `ULift` transport and the final componentwise `ULift` removal finish the full
translated-seed formula. -/
theorem induced_restriction_mackey_iso_hom_apply_translated_seed_of_middle_stage
    (H : Subgroup G) (ρ : Representation k H V)
    (q : DoubleCoset.Quotient (H : Set G) H)
    (x : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q))
    (ρu : Representation k H (ULift.{u} V))
    (hSource :
      Rep.res H.subtype (Rep.ind H.subtype (of ρ)) ≅
        Rep.res H.subtype (Rep.ind H.subtype (of ρu)))
    (hMackeyULift :
      Rep.res H.subtype (Rep.ind H.subtype (of ρu)) ≅
        Rep.of
          (Representation.directSum fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
            (mackeySummand H H (of ρu) (doubleCosetRepresentative H q'.down)).ρ))
    (eComponent :
      Rep.of
          (Representation.directSum fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
            (mackeySummand H H (of ρu) (doubleCosetRepresentative H q'.down)).ρ) ≅
        Rep.of
          (Representation.directSum fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
            (mackeySummand H H (of ρ) (doubleCosetRepresentative H q'.down)).ρ))
    (yu : Representation.IndV H.subtype ρu)
    (blockSeed :
      Representation.IndV
        (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype
        ((mackeyTwist H H (of ρu) (doubleCosetRepresentative H q)).ρ))
    (hSourceSeed :
      hSource.hom.hom
          (Representation.IndV.mk H.subtype ρ (doubleCosetRepresentative H q)⁻¹ x) =
        yu)
    (hBlockSeed :
      hMackeyULift.hom.hom yu =
        DirectSum.lof k _
          (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
            Representation.IndV
              (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
              ((mackeyTwist H H (of ρu) (doubleCosetRepresentative H q'.down)).ρ))
          ⟨q⟩
          blockSeed)
    (hComponentSeed :
      eComponent.hom.hom
          (DirectSum.lof k _
            (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
              Representation.IndV
                (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
                ((mackeyTwist H H (of ρu) (doubleCosetRepresentative H q'.down)).ρ))
            ⟨q⟩
            blockSeed) =
        DirectSum.lof k _
          (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
            Representation.IndV
              (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
              ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q'.down)).ρ))
          ⟨q⟩
          (Representation.IndV.mk
            (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype
            ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q)).ρ)
            1 x)) :
    ((hSource ≪≫ hMackeyULift ≪≫ eComponent).hom.hom
      (Representation.IndV.mk H.subtype ρ (doubleCosetRepresentative H q)⁻¹ x)) =
      DirectSum.lof k _
        (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
          Representation.IndV
            (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
            ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q'.down)).ρ))
        ⟨q⟩
          (Representation.IndV.mk
            (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype
            ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q)).ρ)
            1 x) := by
  -- The full Mackey map is the three-stage source transport, middle Mackey decomposition, and
  -- outer componentwise `ULift` removal. We rewrite each stage on the named seed vectors.
  calc
    ((hSource ≪≫ hMackeyULift ≪≫ eComponent).hom.hom
        (Representation.IndV.mk H.subtype ρ (doubleCosetRepresentative H q)⁻¹ x))
        =
          eComponent.hom.hom
            (hMackeyULift.hom.hom
              (hSource.hom.hom
                (Representation.IndV.mk H.subtype ρ (doubleCosetRepresentative H q)⁻¹ x))) := by
          rfl
    _ = eComponent.hom.hom (hMackeyULift.hom.hom yu) := by
          exact congrArg (fun z ↦ eComponent.hom.hom (hMackeyULift.hom.hom z)) hSourceSeed
    _ = eComponent.hom.hom
          (DirectSum.lof k _
            (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
              Representation.IndV
                (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
                ((mackeyTwist H H (of ρu) (doubleCosetRepresentative H q'.down)).ρ))
            ⟨q⟩
            blockSeed) := by
          exact congrArg eComponent.hom.hom hBlockSeed
    _ = DirectSum.lof k _
          (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
            Representation.IndV
              (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
              ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q'.down)).ρ))
          ⟨q⟩
          (Representation.IndV.mk
            (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype
            ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q)).ρ)
            1 x) := hComponentSeed

/-- Helper for Proposition 7-7.4-1: transporting the canonical seed generator in one Mackey
summand forward through `induced_restriction_mackey_iso` lands in the corresponding
`DirectSum.lof` seed. -/
theorem induced_restriction_mackey_iso_hom_apply_translated_seed
    (H : Subgroup G) (ρ : Representation k H V)
    (q : DoubleCoset.Quotient (H : Set G) H)
    (x : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q)) :
    let e := induced_restriction_mackey_iso (k := k) H ρ
    (e.hom.hom :
        Representation.IndV H.subtype ρ →ₗ[k]
          DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H))
            (fun q' ↦ (mackey_summand_family (k := k) H ρ q').V))
      (Representation.IndV.mk H.subtype ρ (doubleCosetRepresentative H q)⁻¹ x) =
      DirectSum.lof k _
        (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
          (mackey_summand_family (k := k) H ρ q').V)
        ⟨q⟩
        (Representation.IndV.mk
          (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype
          ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q)).ρ)
          1 x) := by
  dsimp [induced_restriction_mackey_iso]
  -- Reduce the public Mackey isomorphism to the translated-seed formula from Proposition 7.7.3
  -- followed by the explicit componentwise `ULift` removal on the active summand.
  calc
    ((mackey_directSum_ulift_iso (k := k) H ρ).hom.hom
        (((restriction_induced_mackeyDirectSum_iso
              (k := k)
              (ι := ULift (DoubleCoset.Quotient (H : Set G) H))
              (K := H) (H := H)
              (W := of (uliftRepresentation (k := k) ρ))
              (s := fun q' ↦ doubleCosetRepresentative H q'.down)
              (ulift_doubleCosetRepresentative_bijective H)).hom.hom)
          (Representation.IndV.mk H.subtype (uliftRepresentation (k := k) ρ)
            (doubleCosetRepresentative H q)⁻¹ (ULift.up x)))) =
      ((mackey_directSum_ulift_iso (k := k) H ρ).hom.hom)
        (DirectSum.lof k _
          (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
            Representation.IndV
              (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
              ((mackeyTwist H H (of (uliftRepresentation (k := k) ρ))
                (doubleCosetRepresentative H q'.down)).ρ))
          ⟨q⟩
          (Representation.IndV.mk
            (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype
            ((mackeyTwist H H (of (uliftRepresentation (k := k) ρ))
              (doubleCosetRepresentative H q)).ρ)
            1 (ULift.up x))) := by
      -- The middle Mackey decomposition is exactly the translated-seed owner theorem.
      exact congrArg ((mackey_directSum_ulift_iso (k := k) H ρ).hom.hom) <| by
        simpa using
          restriction_induced_mackeyDirectSum_iso_hom_apply_translated_seed
            (k := k)
            (K := H) (H := H)
            (W := of (uliftRepresentation (k := k) ρ))
            (s := fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
              doubleCosetRepresentative H q'.down)
            (ulift_doubleCosetRepresentative_bijective H)
            ⟨q⟩
            (ULift.up x)
    _ =
      DirectSum.lof k _
        (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
          (mackey_summand_family (k := k) H ρ q').V)
        ⟨q⟩
        (Representation.IndV.mk
          (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype
          ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q)).ρ)
          1 x) := by
      -- The outer `ULift`-removal isomorphism only changes the active `q`-summand seed.
      simpa [mackey_summand_family] using
        mackey_directSum_ulift_iso_hom_apply_lof_seed (k := k) H ρ ⟨q⟩ x

/-- Helper for Proposition 7-7.4-1: transporting the canonical seed generator in one Mackey
summand back through `induced_restriction_mackey_iso` recovers the translated generator
`IndV.mk ... s⁻¹`. -/
theorem induced_restriction_mackey_iso_inv_apply_lof_seed
    (H : Subgroup G) (ρ : Representation k H V)
    (q : DoubleCoset.Quotient (H : Set G) H)
    (x : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q)) :
    let e := induced_restriction_mackey_iso (k := k) H ρ
    ((e.inv.hom :
        DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H))
          (fun q' ↦ (mackey_summand_family (k := k) H ρ q').V) →ₗ[k]
        Representation.IndV H.subtype ρ)
      (DirectSum.lof k _
        (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
          (mackey_summand_family (k := k) H ρ q').V)
        ⟨q⟩
        (Representation.IndV.mk
          (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype
          ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q)).ρ)
          1 x))) =
      Representation.IndV.mk H.subtype ρ (doubleCosetRepresentative H q)⁻¹ x := by
  dsimp
  -- Route correction: the inverse formula is reduced to the single forward-image identity saying
  -- that the Mackey decomposition sends the translated generator
  -- `IndV.mk ... (doubleCosetRepresentative H q)⁻¹ x` to the `q`-summand seed.
  let e := induced_restriction_mackey_iso (k := k) H ρ
  let y :
      DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H))
        (fun q' ↦ (mackey_summand_family (k := k) H ρ q').V) :=
    DirectSum.lof k _
      (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
        (mackey_summand_family (k := k) H ρ q').V)
      ⟨q⟩
      (Representation.IndV.mk
        (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype
        ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q)).ρ)
        1 x)
  apply (rep_iso_hom_injective (k := k) e)
  change e.hom.hom (e.inv.hom y) =
    e.hom.hom (Representation.IndV.mk H.subtype ρ (doubleCosetRepresentative H q)⁻¹ x)
  -- After applying the forward Mackey isomorphism, the inverse seed becomes the corresponding
  -- direct-sum basis vector in the `q`-summand.
  have hcancel : e.hom.hom (e.inv.hom y) = y := by
    -- The Mackey isomorphism and its inverse cancel on the chosen `q`-summand seed.
    change ((e.inv ≫ e.hom).hom) y = y
    rw [e.inv_hom_id]
    rfl
  have hforward :
      e.hom.hom (Representation.IndV.mk H.subtype ρ (doubleCosetRepresentative H q)⁻¹ x) = y := by
    -- Reuse the forward seed-image lemma instead of rebuilding the three-stage transport inline.
    simpa [e, y] using
      induced_restriction_mackey_iso_hom_apply_translated_seed (k := k) H ρ q x
  calc
    e.hom.hom (e.inv.hom y) = y := hcancel
    _ = e.hom.hom (Representation.IndV.mk H.subtype ρ (doubleCosetRepresentative H q)⁻¹ x) := by
          -- The forward seed-image lemma identifies the translated generator with that same seed.
          symm
          exact hforward

/-- Helper for Proposition 7-7.4-1: the representative of the identity double coset has inverse
equal to `1`, matching the source proof's unit-generator normalization. -/
theorem identity_doubleCosetRepresentative_inv
    (H : Subgroup G) :
    (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)))⁻¹ = 1 := by
  -- The distinguished identity double coset uses representative `1`, so its inverse is again `1`.
  simp [doubleCosetRepresentative_identity]

end MackeyIrreducibilityCriterion

end Representation
