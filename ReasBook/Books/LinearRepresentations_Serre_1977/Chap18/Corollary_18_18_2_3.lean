import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_1_2
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped Representation TensorProduct

universe u

namespace Representation

section

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {K : Type u} [Field K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]

/- Domain-style sampling for this item:
* `Representation.virtualModularCharacter` in Remark `18-18.1-3` is the source-facing owner on
  `R₀[k](G)`, valued on the `p`-regular subtype of `G`.
* `Representation.virtualModularCharacterOnPRegularConjClass` in Theorem `18-18.2-2` is the
  canonical descended owner on `PRegularConjClass G p`.
* `virtualModularCharacterOnPRegularConjClass_class` and
  `virtualModularCharacterOnPRegularConjClass_class_ofSubtype` from Theorem `18-18.2-2` are the
  owner-level bridge/view API from actual finite-dimensional representations to that descended
  Brauer-character owner.
* `finiteRepGrothendieckClass_eq_iff_nonempty_iso_of_isSemisimple` in Remark `14-14.1-2` is the
  chapter's canonical semisimple-isomorphism owner.
* none of these owners uses a separate `[Fact p.Prime]` or `[CharZero K]` assumption here; the
  only characteristic data needed in this file is `[CharP k p]`.

Layer triage:
* source-facing: equality of Brauer characters of actual finite-dimensional modules, written using
  the Chapter `18` notation `φ[...]`.
* core/canonical: injectivity of
  `virtualModularCharacterOnPRegularConjClass p (PrimeToPRoot.toFieldLift lift)` on `R₀[k](G)`.
* bridge/view: `virtualModularCharacterOnPRegularConjClass_class` and
  `virtualModularCharacterOnPRegularConjClass_class_ofSubtype`.
-/

-- Proof sketch: Theorem `18-18.2-2` identifies the scalar extension of this additive map with a
-- linear equivalence onto the full function space on `PRegularConjClass G p`. The simple-class
-- basis of `R₀[k](G)` therefore has linearly independent Brauer-character image, forcing the
-- descended virtual modular character itself to be injective.
omit [IsAlgClosed k] [Finite G] in
/-- Helper for Corollary 18-18.2-3: choose one representative of each isomorphism class of simple
finite-dimensional `k[G]`-representations. -/
private theorem exists_complete_pairwise_nonisomorphic_simple_family_local :
    ∃ (ι : Type (u + 1)) (π : ι → FDRep k G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let SimpleRep : Type (u + 1) := { τ : FDRep k G // Simple τ }
  let r : Setoid SimpleRep :=
    { r := fun a b ↦ Nonempty (a.1 ≅ b.1)
      iseqv :=
        ⟨fun a ↦ ⟨Iso.refl _⟩,
          fun {a b} hab ↦ by
            rcases hab with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {a b c} hab hbc ↦ by
            rcases hab with ⟨eab⟩
            rcases hbc with ⟨ebc⟩
            exact ⟨eab.trans ebc⟩⟩ }
  let ι : Type (u + 1) := Quotient r
  let π : ι → FDRep k G := fun q ↦ (Quotient.out q).1
  have hπ_pairwise : PairwiseNonisomorphic π := by
    -- If two quotient representatives are isomorphic, their quotient classes coincide.
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨e⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine ⟨?_, ?_⟩
    · intro q
      exact (Quotient.out q).2
    · intro τ hτ
      let q : ι := ⟦⟨τ, hτ⟩⟧
      refine ⟨q, ?_⟩
      have hq :
          Nonempty (((Quotient.out q).1) ≅ τ) := by
        exact Quotient.exact (Quotient.out_eq q)
      rcases hq with ⟨e⟩
      exact ⟨e.symm⟩
  exact ⟨ι, π, hπ_pairwise, hπ_complete⟩

omit [CharZero K] in
/-- Helper for Corollary 18-18.2-3: on a representation class, the descended virtual modular
character agrees with the descended Brauer character on `PRegularConjClass G p`. -/
private theorem virtualModularCharacterOnPRegularConjClass_class_local
    (lift : PrimeToPRoot p k →* Kˣ) (E : FDRep k G) :
    virtualModularCharacterOnPRegularConjClass
        (p := p) (k := k) (A := K) (G := G) (PrimeToPRoot.toFieldLift lift) [E]₀ =
      FDRep.modularCharacterOnPRegularConjClass
        (p := p) (G := G) (A := K) E (PrimeToPRoot.toFieldLift lift) := by
  ext c
  let s := PRegularConjClass.representative (G := G) (p := p) c
  have hs :
      PRegularConjClass.ofSubtype (G := G) p s = c := by
    apply Subtype.ext
    change ConjClasses.mk (PRegularConjClass.representative (G := G) (p := p) c).1 = c.1
    exact PRegularConjClass.mk_representative (G := G) (p := p) c
  rw [← hs]
  rw [virtualModularCharacterOnPRegularConjClass_ofSubtype,
    FDRep.modularCharacterOnPRegularConjClass_ofSubtype]
  exact congrFun (virtualModularCharacter_class (PrimeToPRoot.toFieldLift lift) E) s

/-- Corollary 18-18.2-3 (core/canonical form): for an injective lift of the prime-to-`p` roots of
unity, the descended virtual modular character on LinearRepresentations_Serre_1977's Grothendieck group `R_k(G)` is
injective. -/
theorem virtualModularCharacterOnPRegularConjClass_injective
    (lift : PrimeToPRoot p k →* Kˣ) (hlift : Function.Injective lift) :
    Function.Injective
      (virtualModularCharacterOnPRegularConjClass
        (p := p) (k := k) (A := K) (G := G) (PrimeToPRoot.toFieldLift lift) :
        R₀[k](G) →+ (PRegularConjClass G p → K)) := by
  classical
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_local (k := k) (G := G)
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  let bR₀ : Module.Basis ι ℤ (R₀[k](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let bφ : Module.Basis ι K (PRegularConjClass G p → K) :=
    irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
      (p := p) (k := k) (K := K) (G := G) lift hlift π hπ_pairwise hπ_complete
  let φ : R₀[k](G) →ₗ[ℤ] (PRegularConjClass G p → K) :=
    (virtualModularCharacterOnPRegularConjClass
      (p := p) (k := k) (A := K) (G := G) (PrimeToPRoot.toFieldLift lift)).toIntLinearMap
  have hbasis :
      ∀ i, φ (bR₀ i) = bφ i := by
    intro i
    calc
      φ (bR₀ i)
          = φ [π i]₀ := by
              simp [bR₀, simple_finiteRep_classes_basis_of_complete_family_apply]
      _ = FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := K) (π i) (PrimeToPRoot.toFieldLift lift) := by
              change
                virtualModularCharacterOnPRegularConjClass
                    (p := p) (k := k) (A := K) (G := G) (PrimeToPRoot.toFieldLift lift) [π i]₀ =
                  FDRep.modularCharacterOnPRegularConjClass
                    (p := p) (G := G) (A := K) (π i) (PrimeToPRoot.toFieldLift lift)
              exact virtualModularCharacterOnPRegularConjClass_class_local
                (p := p) (k := k) (K := K) (G := G) lift (π i)
      _ = bφ i := by
            symm
            change
              irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
                  (p := p) (k := k) (K := K) (G := G) lift hlift π hπ_pairwise hπ_complete i =
                FDRep.modularCharacterOnPRegularConjClass
                  (p := p) (G := G) (A := K) (π i) (PrimeToPRoot.toFieldLift lift)
            exact irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions_apply
              (p := p) (k := k) (K := K) (G := G) lift hlift π hπ_pairwise hπ_complete i
  have hrepr :
      ∀ x i, bφ.repr (φ x) i = (bR₀.repr x i : K) := by
    intro x i
    have himage :
        φ x = ∑ j, (bR₀.repr x j : K) • bφ j := by
      calc
        φ x
            = φ (∑ j, (bR₀.repr x j) • bR₀ j) := by
                exact congrArg φ (bR₀.sum_repr x).symm
        _ = ∑ j, (bR₀.repr x j) • φ (bR₀ j) := by
              rw [map_sum]
              refine Finset.sum_congr rfl ?_
              intro j _
              rw [map_zsmul]
        _ = ∑ j, (bR₀.repr x j : K) • bφ j := by
              refine Finset.sum_congr rfl ?_
              intro j _
              calc
                (bR₀.repr x j) • φ (bR₀ j) = (bR₀.repr x j) • bφ j := by rw [hbasis j]
                _ = (bR₀.repr x j : K) • bφ j := by
                      rw [← Int.cast_smul_eq_zsmul K]
    calc
      bφ.repr (φ x) i
          = bφ.repr (∑ j, (bR₀.repr x j : K) • bφ j) i := by rw [himage]
      _ = (bR₀.repr x i : K) := by
            simpa using congrFun (bφ.repr_sum_self fun j ↦ (bR₀.repr x j : K)) i
  intro x y hφ
  apply bR₀.repr.injective
  ext i
  have hcast :
      ((bR₀.repr x i : ℤ) : K) = ((bR₀.repr y i : ℤ) : K) := by
    calc
    (bR₀.repr x i : K) = bφ.repr (φ x) i := by
      symm
      exact hrepr x i
    _ = bφ.repr (φ y) i := by
          simpa [φ] using congrArg (fun z : PRegularConjClass G p → K ↦ bφ.repr z i) hφ
    _ = (bR₀.repr y i : K) := hrepr y i
  exact Int.cast_injective hcast

-- Proof sketch: specialize the injectivity of
-- `virtualModularCharacterOnPRegularConjClass p (PrimeToPRoot.toFieldLift lift)` to the classes
-- `[F]₀` and `[F']₀`, then rewrite with
-- `virtualModularCharacterOnPRegularConjClass_class`.
/-- If two finite-dimensional `k[G]`-modules have the same Brauer character on
`PRegularConjClass G p`, then they define the same class in LinearRepresentations_Serre_1977's Grothendieck group
`R_k(G)`. -/
theorem finiteRepGrothendieckClass_eq_of_modularCharacterOnPRegularConjClass_eq
    (lift : PrimeToPRoot p k →* Kˣ) (hlift : Function.Injective lift)
    {F F' : FDRep k G}
    (hφ :
      FDRep.modularCharacterOnPRegularConjClass F (PrimeToPRoot.toFieldLift lift) =
        FDRep.modularCharacterOnPRegularConjClass F' (PrimeToPRoot.toFieldLift lift)) :
    [F]₀ = [F']₀ := by
  apply virtualModularCharacterOnPRegularConjClass_injective lift hlift
  calc
    virtualModularCharacterOnPRegularConjClass
        (p := p) (k := k) (A := K) (G := G) (PrimeToPRoot.toFieldLift lift) [F]₀
        =
      FDRep.modularCharacterOnPRegularConjClass F (PrimeToPRoot.toFieldLift lift) := by
          simpa using
            virtualModularCharacterOnPRegularConjClass_class_local
              (p := p) (k := k) (K := K) (G := G) lift F
    _ = FDRep.modularCharacterOnPRegularConjClass F' (PrimeToPRoot.toFieldLift lift) := hφ
    _ =
      virtualModularCharacterOnPRegularConjClass
        (p := p) (k := k) (A := K) (G := G) (PrimeToPRoot.toFieldLift lift) [F']₀ := by
          simpa using
            (virtualModularCharacterOnPRegularConjClass_class_local
              (p := p) (k := k) (K := K) (G := G) lift F').symm

-- Proof sketch: descend the source-facing equality on `{ s : G // IsPRegular p s }` to
-- `PRegularConjClass G p` by evaluating the canonical owner
-- `FDRep.modularCharacterOnPRegularConjClass` at representatives via
-- `FDRep.modularCharacterOnPRegularConjClass_ofSubtype`, then invoke the previous descended-owner
-- equality theorem.
/-- Corollary 18-18.2-3 (1): if two finite-dimensional `k[G]`-modules have the same modular
character, then they define the same class in LinearRepresentations_Serre_1977's Grothendieck group `R_k(G)`. -/
theorem finiteRepGrothendieckClass_eq_of_modularCharacter_eq
    (lift : PrimeToPRoot p k →* Kˣ) (hlift : Function.Injective lift)
    {F F' : FDRep k G}
    (hφ : ∀ s : { t : G // IsPRegular p t },
      φ[PrimeToPRoot.toFieldLift lift](F.ρ) s =
        φ[PrimeToPRoot.toFieldLift lift](F'.ρ) s) :
    [F]₀ = [F']₀ := by
  apply finiteRepGrothendieckClass_eq_of_modularCharacterOnPRegularConjClass_eq lift hlift
  ext c
  rcases c with ⟨c, hc⟩
  obtain ⟨s, rfl⟩ := ConjClasses.mk_surjective c
  have hs : IsPRegular p s := hc s <| by
    simp [ConjClasses.mem_carrier_iff_mk_eq]
  have hsubtype :
      PRegularConjClass.ofSubtype p ⟨s, hs⟩ =
        ⟨ConjClasses.mk s, hc⟩ := by
    apply Subtype.ext
    rfl
  rw [← hsubtype]
  rw [FDRep.modularCharacterOnPRegularConjClass_ofSubtype,
    FDRep.modularCharacterOnPRegularConjClass_ofSubtype]
  exact hφ ⟨s, hs⟩

-- Proof sketch: first identify the two Grothendieck classes via
-- `finiteRepGrothendieckClass_eq_of_modularCharacter_eq`, then invoke the canonical semisimple
-- isomorphism criterion from Remark `14-14.1-2`.
/-- Corollary 18-18.2-3 (2): if two semisimple finite-dimensional `k[G]`-modules have the same
modular character, then they are isomorphic. -/
theorem finiteRep_iso_of_isSemisimple_of_modularCharacter_eq
    (lift : PrimeToPRoot p k →* Kˣ) (hlift : Function.Injective lift)
    {F F' : FDRep k G}
    (hF : IsSemisimpleRepresentation F.ρ)
    (hF' : IsSemisimpleRepresentation F'.ρ)
    (hφ : ∀ s : { t : G // IsPRegular p t },
      φ[PrimeToPRoot.toFieldLift lift](F.ρ) s =
        φ[PrimeToPRoot.toFieldLift lift](F'.ρ) s) :
    Nonempty (F ≅ F') :=
  (finiteRepGrothendieckClass_eq_iff_nonempty_iso_of_isSemisimple hF hF').mp <|
    finiteRepGrothendieckClass_eq_of_modularCharacter_eq lift hlift hφ

end

end Representation
