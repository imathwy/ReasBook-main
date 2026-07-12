import StacksProject_2024.Chap15.Lemma_15_11_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {A : Type u} {B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (I : Ideal A) [hH : HenselianRing A I] [Algebra.IsIntegral A B]

/- Domain-style sampling:
- primary domain: henselian pairs in commutative algebra under integral base change;
- sampled owner declarations:
  `HenselianRing`,
  `Ideal.HasIntegralAlgebraIdempotentLifting`,
  `henselianRing_tfae_etaleLift_idempotents_gabberCriterion`;
- best owner abstraction: the public conclusion is still the canonical owner
  `HenselianRing B (Ideal.map (algebraMap A B) I)`, while the idempotent-lifting clause from
  Lemma `15.11.6` is derived API used only to bridge from `(A, I)` to `(B, I B)`;
- primitive data: the ideal `I`, the owner instance `HenselianRing A I`, the integral `A`-algebra
  `B`, and the mapped ideal `Ideal.map (algebraMap A B) I`;
- derived API: integral-idempotent lifting over `A`, its transport to integral `B`-algebras by
  transitivity of integrality, and the `3 → 0` implication of the chapter TFAE.

Source/core/bridge triage:
- `source-facing`: the henselianity of the mapped pair `(B, I B)`;
- `core/canonical`: `HenselianRing` and `Ideal.HasIntegralAlgebraIdempotentLifting`;
- `bridge/view`: the transfer of the integral-idempotent lifting clause from `A` to `B`.
-/

-- Proof sketch: extract the integral-idempotent lifting clause from Lemma `15.11.6` for `(A, I)`.
-- If `C` is integral over `B`, then it is integral over `A` by scalar-tower transitivity, so the
-- same clause applies to `I B`. Applying the reverse implication of the TFAE for `(B, I B)` gives
-- the desired henselian instance.
/-- Lemma 15.11.8: if `(A, I)` is a henselian pair and `A → B` is an integral ring map, then the
pair `(B, I B)` is henselian. -/
instance ideal_map_henselianRing_of_isIntegral :
    HenselianRing B (Ideal.map (algebraMap A B) I) := by
  let J : Ideal B := Ideal.map (algebraMap A B) I
  let Qsrc : Ideal A → Prop := Ideal.HasFiniteAlgebraIdempotentLifting.{u, u}
  let Psrc : Ideal A → Prop := Ideal.HasIntegralAlgebraIdempotentLifting.{u, u}
  let Qtgt : Ideal B → Prop := Ideal.HasFiniteAlgebraIdempotentLifting.{u, u}
  let Ptgt : Ideal B → Prop := Ideal.HasIntegralAlgebraIdempotentLifting.{u, u}
  -- Extract the integral-idempotent lifting clause from the source henselian pair.
  have hTfaeSource :
      List.TFAE [HenselianRing A I, I.HasEtaleLiftProperty, Qsrc I, Psrc I,
        I.SatisfiesGabberRootCriterion] := by
    simpa [Qsrc, Psrc] using henselianRing_tfae_etaleLift_idempotents_gabberCriterion I
  have hSourceIff : HenselianRing A I ↔ Psrc I := by
    simpa using hTfaeSource.out 0 3
  have hSource : Psrc I :=
    hSourceIff.mp inferInstance
  -- Transport the clause along the integral map `A → B` by composing integral algebras.
  have hTarget : Ptgt J := by
    intro C _ _ hC
    let _ : Algebra A C := ((algebraMap B C).comp (algebraMap A B)).toAlgebra
    let _ : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
    let _ : Algebra.IsIntegral A C := Algebra.IsIntegral.trans B
    let IB' : Ideal C := Ideal.map (algebraMap B C) (Ideal.map (algebraMap A B) I)
    let IC : Ideal C := Ideal.map (algebraMap A C) I
    have hMap : IB' = IC := by
      simp [IB', IC, Ideal.map_map, IsScalarTower.algebraMap_eq A B C]
    let e : (C ⧸ IB') ≃+* (C ⧸ IC) := Ideal.quotEquivOfEq hMap
    -- Postcomposing with the quotient equivalence preserves bijectivity on idempotents.
    have heBij : Function.Bijective (RingHom.idempotentMap e.toRingHom) := by
      constructor
      · intro x y hxy
        apply Subtype.ext
        exact e.injective (congrArg Subtype.val hxy)
      · intro y
        refine ⟨RingHom.idempotentMap e.symm.toRingHom y, ?_⟩
        apply Subtype.ext
        simp [RingHom.idempotentMap]
    have hComm :
        RingHom.idempotentMap e.toRingHom ∘ (Ideal.Quotient.mk IB').idempotentMap =
          (Ideal.Quotient.mk IC).idempotentMap := by
      funext x
      apply Subtype.ext
      change e ((Ideal.Quotient.mk IB') x.1) = (Ideal.Quotient.mk IC) x.1
      rw [Ideal.quotEquivOfEq_mk]
    have hSourceC : Function.Bijective (Ideal.Quotient.mk IC).idempotentMap := by
      simpa [IC] using hSource (B := C)
    have hComp :
        Function.Bijective (RingHom.idempotentMap e.toRingHom ∘ (Ideal.Quotient.mk IB').idempotentMap) := by
      rw [hComm]
      exact hSourceC
    have hIB' : Function.Bijective (Ideal.Quotient.mk IB').idempotentMap := by
      constructor
      · intro x y hxy
        apply hComp.1
        simpa [Function.comp, hxy]
      · intro z
        obtain ⟨w, hw⟩ := hComp.2 (RingHom.idempotentMap e.toRingHom z)
        refine ⟨w, ?_⟩
        exact heBij.1 (by simpa [Function.comp] using hw)
    simpa [IB'] using hIB'
  -- Convert the transported clause back to henselianity for the mapped ideal.
  have hTfaeTarget :
      List.TFAE [HenselianRing B J, J.HasEtaleLiftProperty, Qtgt J, Ptgt J,
        J.SatisfiesGabberRootCriterion] := by
    simpa [Qtgt, Ptgt] using henselianRing_tfae_etaleLift_idempotents_gabberCriterion J
  have hTargetIff : HenselianRing B J ↔ Ptgt J := by
    simpa using hTfaeTarget.out 0 3
  exact hTargetIff.mpr hTarget

end
