import Mathlib
import Mathlib.RingTheory.Morita.Matrix

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_18_18_1_3 (from Chap18) -/
noncomputable section

open scoped Representation

universe u v

namespace Representation

section VirtualModularCharacters

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v} [AddCommGroup A]
variable {G : Type u} [Group G]

/-
Domain-style sampling:
* source-facing: LinearRepresentations_Serre_1977's virtual modular character on `R₀[k](G)`, obtained by additivity from
  modular characters of finite-dimensional `k[G]`-representations.
* core/canonical owners inspected in this domain: `Representation.modularCharacter`,
  `finiteRepGrothendieckRelations`, `finiteRepGrothendieckCharacter`, and `decompositionHom`.
* primitive data: a lift `PrimeToPRoot p k → A`, the generator-level modular character
  `Representation.modularCharacter lift E.ρ`, and the Grothendieck relations
  `finiteRepGrothendieckRelations k G`.
* derived API: the quotient additive map `virtualModularCharacter` and its compatibility with the
  decomposition homomorphism.
* owner-level refinement: this additive Grothendieck descent only depends on the canonical owner
  `Representation.modularCharacter`, so the bridge/view API here does not keep a redundant
  characteristic-`p` assumption; that hypothesis is reserved for the later reduction comparison.
-/

private abbrev virtualModularCharacterLift
    (lift : PrimeToPRoot p k → A) :
    FreeAbelianGroup (FDRep k G) →+ ({ s : G // IsPRegular p s } → A) :=
  FreeAbelianGroup.lift fun E ↦ modularCharacter lift E.ρ

-- Proof sketch: the generators of `finiteRepGrothendieckRelations k G` come from short exact
-- sequences, and Proposition `18-18.1-2 (3)` states that `Representation.modularCharacter` is
-- additive
-- on exactly those sequences.
private theorem finiteRepGrothendieckRelations_le_virtualModularCharacterLift_ker
    (lift : PrimeToPRoot p k → A) :
    finiteRepGrothendieckRelations k G ≤
      (virtualModularCharacterLift lift).ker := by
  -- Descend along the Grothendieck presentation by checking the short-exact-sequence generators.
  rw [finiteRepGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change virtualModularCharacterLift lift
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  ext s
  -- Proposition `18-18.1-2 (3)` identifies the middle term with the sum of the outer terms.
  have hchar :
      φ[lift](S.X₂.ρ) s = φ[lift](S.X₁.ρ) s + φ[lift](S.X₃.ρ) s :=
    modularCharacter_add_of_shortExactSequence (p := p) (lift := lift) S hS s
  simpa [virtualModularCharacterLift, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    sub_eq_zero.mpr hchar

/-- Remark 18-18.1-3: additivity of the modular character extends it from finite-dimensional
`k[G]`-representations to a virtual modular character on LinearRepresentations_Serre_1977's Grothendieck group `R_k(G)`,
valued on the `p`-regular locus of `G`. -/
def virtualModularCharacter (lift : PrimeToPRoot p k → A) :
    R₀[k](G) →+ ({ s : G // IsPRegular p s } → A) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations k G)
    (virtualModularCharacterLift lift)
    (finiteRepGrothendieckRelations_le_virtualModularCharacterLift_ker lift)

-- Proof sketch: `virtualModularCharacter` is the quotient homomorphism induced by
-- `virtualModularCharacterLift`, so on the class of an actual finite representation it recovers
-- `Representation.modularCharacter`.
/-- Evaluating the virtual modular character on the Grothendieck class of a finite-dimensional
representation recovers its modular character. -/
@[simp] theorem virtualModularCharacter_class
    (lift : PrimeToPRoot p k → A) (E : FDRep k G) :
    virtualModularCharacter lift [E]₀ = modularCharacter lift E.ρ := by
  simp [virtualModularCharacter, virtualModularCharacterLift, finiteRepGrothendieckClass]

/-- Helper for Remark 18-18.1-3: on the class of an honest representation, the virtual modular
character is unchanged under conjugation of a `p`-regular element. -/
private theorem virtualModularCharacter_class_conj
    (lift : PrimeToPRoot p k → A) (E : FDRep k G) (s t : G)
    (hs : IsPRegular p s) :
    virtualModularCharacter lift [E]₀ ⟨t * s * t⁻¹, isPRegular_conj p s t hs⟩ =
      virtualModularCharacter lift [E]₀ ⟨s, hs⟩ := by
  -- Reduce to the modular character of the actual representation `E`.
  rw [virtualModularCharacter_class]
  -- Proposition `18-18.1-2 (2)` gives conjugacy invariance on honest representations.
  exact modularCharacter_conj (p := p) (lift := lift) E.ρ s t hs

-- Proof sketch: compare the two evaluations as additive maps on `R₀[k](G)`; on generator
-- classes this is exactly Proposition `18-18.1-2 (2)`, and the Grothendieck quotient extends the
-- identity to all virtual classes.
/-- The virtual modular character is constant on conjugacy classes of `p`-regular elements. -/
theorem virtualModularCharacter_conj
    (lift : PrimeToPRoot p k → A) (x : R₀[k](G)) (s t : G)
    (hs : IsPRegular p s) :
    virtualModularCharacter lift x ⟨t * s * t⁻¹, isPRegular_conj p s t hs⟩ =
      virtualModularCharacter lift x ⟨s, hs⟩ := by
  -- Descend the conjugacy calculation from honest representations to the Grothendieck quotient.
  refine QuotientAddGroup.induction_on x ?_
  intro a
  -- The free abelian presentation reduces the statement to zero, generator, negation, and sum.
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp [virtualModularCharacter]
  · intro E
    exact virtualModularCharacter_class_conj (lift := lift) E s t hs
  · intro a ha
    simpa using congrArg Neg.neg ha
  · intro a b ha hb
    simp [map_add, ha, hb]

-- Route correction: the decomposition-compatibility comparison belongs to a later support layer.
-- This remark stays minimal so `Theorem_18_18_2_2` can import only the owner API it actually uses.

end VirtualModularCharacters

end Representation

/-! ### Corollary_18_18_2_3 (from Chap18) -/
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

/-! ### Corollary_18_18_2_4 (from Chap18) -/
noncomputable section

open scoped Representation

universe u

namespace Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {K : Type u} [Field K] [CharZero K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]
variable [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

/- Domain-style sampling for this item:
* `virtualModularCharacter` in Remark `18-18.1-3` is the source-facing Grothendieck-group owner
  for modular characters on the `p`-regular locus.
* `virtualModularCharacter_decomposition_eq_character_restriction` in Remark `18-18.1-3` is the
  canonical comparison between that owner and the ordinary virtual character upstairs.
* `virtualModularCharacterOnPRegularConjClass` and
  `bijective_scalarExtensionVirtualModularCharacterOnPRegularConjClass` in Theorem `18-18.2-2`
  provide the chapter's injectivity owner after passing to the canonical quotient
  `PRegularConjClass G p`.

Layer triage:
* source-facing: vanishing of the ordinary virtual character on the `p`-regular elements.
* core/canonical: vanishing of
  `virtualModularCharacterOnPRegularConjClass p lift ((decompositionHom A K G) x)` for an
  injective lift.
* bridge/view:
  `virtualModularCharacterOnPRegularConjClass_ofSubtype` and
  `virtualModularCharacter_decomposition_eq_character_restriction`.
-/

-- Proof sketch: pass from the subtype `{ g : G // IsPRegular p g }` to the canonical owner
-- `PRegularConjClass G p`, then apply the injectivity result from Theorem `18-18.2-2` to the
-- descended Brauer-character owner.
omit [CharZero K] [Fact p.Prime] in
/-- Corollary 18-18.2-4 (core/canonical form): an element of `R_K(G)` lies in the kernel of the
decomposition homomorphism exactly when the descended Brauer character of its reduction is zero on
`PRegularConjClass G p`, for an injective lift of the prime-to-`p` roots. -/
theorem mem_decompositionHom_ker_iff_virtualModularCharacterOnPRegularConjClass_eq_zero
    (lift : PrimeToPRoot p k →* Kˣ) (hlift : Function.Injective lift) (x : R₀[K](G)) :
    x ∈ (decompositionHom A K G).ker ↔
      virtualModularCharacterOnPRegularConjClass p (PrimeToPRoot.toFieldLift lift)
        ((decompositionHom A K G) x) = 0 :=
by
  have hφinj :
      Function.Injective
        (virtualModularCharacterOnPRegularConjClass p (PrimeToPRoot.toFieldLift lift) :
          R₀[k](G) →+ (PRegularConjClass G p → K)) :=
    _root_.Representation.virtualModularCharacterOnPRegularConjClass_injective lift hlift
  rw [AddMonoidHom.mem_ker]
  change (decompositionHom A K G x = 0 ↔
    virtualModularCharacterOnPRegularConjClass p (PrimeToPRoot.toFieldLift lift)
        ((decompositionHom A K G) x) =
      virtualModularCharacterOnPRegularConjClass p (PrimeToPRoot.toFieldLift lift) 0)
  simpa using (Function.Injective.eq_iff hφinj).symm

-- Proof sketch: choose an injective lift from the existence hypothesis, apply the canonical owner
-- statement at `PRegularConjClass.ofSubtype p s`, then rewrite through
-- `virtualModularCharacterOnPRegularConjClass_ofSubtype` and
-- `virtualModularCharacter_decomposition_eq_character_restriction`.
omit [CharZero K] [Fact p.Prime] in
/-- Corollary 18-18.2-4: the kernel of the decomposition homomorphism
`d : R_K(G) → R_k(G)` consists exactly of those elements whose ordinary virtual character
vanishes on the `p`-regular locus of `G`, provided there exists an injective lift of the
prime-to-`p` roots into `Kˣ`. -/
theorem mem_decompositionHom_ker_iff_character_eq_zero_on_pRegular
    (hexists : ∃ lift : PrimeToPRoot p k →* Kˣ, Function.Injective lift) (x : R₀[K](G)) :
    x ∈ (decompositionHom A K G).ker ↔
      ∀ s : { g : G // IsPRegular p g },
        (finiteRepGrothendieckCharacter K G x : G → K) s.1 = 0 := by
  rcases hexists with ⟨lift, hlift⟩
  constructor
  · intro hx s
    have hzero :
        virtualModularCharacterOnPRegularConjClass p (PrimeToPRoot.toFieldLift lift)
          ((decompositionHom A K G) x) = 0 :=
      (mem_decompositionHom_ker_iff_virtualModularCharacterOnPRegularConjClass_eq_zero
        lift hlift x).1 hx
    simpa [virtualModularCharacterOnPRegularConjClass_ofSubtype,
      virtualModularCharacter_decomposition_eq_character_restriction] using
      congrFun hzero (PRegularConjClass.ofSubtype p s)
  · intro hx
    refine
      (mem_decompositionHom_ker_iff_virtualModularCharacterOnPRegularConjClass_eq_zero
        lift hlift x).2 ?_
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
    simpa [virtualModularCharacterOnPRegularConjClass_ofSubtype,
      virtualModularCharacter_decomposition_eq_character_restriction, ← hsubtype] using
      hx ⟨s, hs⟩

end

end Representation

/-! ### Corollary_18_18_2_5 (from Chap18) -/
noncomputable section

open CategoryTheory

universe u w

namespace Representation

section

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type w}

/- Domain-style sampling for this corollary:
* source-facing: the count of irreducibles in a complete simple family;
* core/canonical owner in this domain:
  `irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions`;
* relevant upstream owner data reused here:
  `PRegularConjClass G p`,
  `IsCompleteIrreducibleFamily`,
  `IsCompleteIrreducibleFamily.finite_index`.

Primitive data vs. derived API:
* primitive data: the family `E` with pairwise nonisomorphism and completeness;
* derived API: the induced basis of `PRegularConjClass G p → k`, whose cardinal comparison gives
  the count.

Layer triage:
* source-facing: this cardinality statement;
* core/canonical: the field-valued basis owner from Theorem `18-18.2-1`;
* bridge/view used internally: the canonical subgroup inclusion `(primeToPRoots p k).subtype`.
-/

-- Proof sketch: the canonical owner theorem
-- `irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions`
-- supplies a `k`-basis of the full function space on `PRegularConjClass G p` indexed by the
-- complete simple family `E`. Comparing the cardinality of that basis with the standard basis of
-- the function space yields the count.
/-- Corollary 18-18.2-5: for a complete family of pairwise nonisomorphic simple finite-dimensional
`k[G]`-representations, the number of indices is the number of `p`-regular conjugacy classes of
`G`. -/
theorem card_eq_card_pRegularConjugacyClasses_of_complete_simple_family
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E) :
    Nat.card ι = Nat.card (PRegularConjClass G p) := by
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index E hE_complete hE_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype (PRegularConjClass G p) := Fintype.ofFinite (PRegularConjClass G p)
  let b :=
    irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
      (primeToPRoots p k).subtype (Subgroup.subtype_injective (primeToPRoots p k))
      E hE_pairwise hE_complete
  calc
    Nat.card ι = Fintype.card ι := Nat.card_eq_fintype_card
    _ = Module.finrank k (PRegularConjClass G p → k) := by
      simpa using (Module.finrank_eq_card_basis b).symm
    _ = Fintype.card (PRegularConjClass G p) := Module.finrank_fintype_fun_eq_card k
    _ = Nat.card (PRegularConjClass G p) := Nat.card_eq_fintype_card.symm

end

end Representation

/-! ### Exercise_18_18_2_6 (from Chap18) -/
noncomputable section

universe v w

open scoped Matrix.Module

namespace Representation

section

variable {k : Type} [Field k]
variable {G : Type v} [Monoid G]
variable {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

-- Domain-style sampling for this item:
-- * `Representation.Equiv` is the canonical owner for isomorphism of unbundled
--   `k`-representations.
-- * `Representation.nthExteriorPower` and the Chapter `9` determinant bridge
--   `exteriorPowerCharacterSeries_eval_eq_det` are the canonical owner-level link from
--   `(-ρ s).charpoly.reverse` to exterior-power character data.
-- * `finiteRepGrothendieckClass_eq_iff_nonempty_iso_of_isSemisimple` in Remark `14-14.1-2`
--   is the chapter's semisimple isomorphism owner on bundled finite-dimensional
--   representations.
-- * `Representation.Equiv.toFDRepIso` is the exact bridge from the source-facing unbundled
--   `ρ.Equiv ρ'` language to the bundled `FDRep.of ρ ≅ FDRep.of ρ'` owner used by Chapter `14`.
--
-- Primitive data vs derived API:
-- * primitive data: the semisimple representations `ρ`, `ρ'` and the equality of the basis-free
--   determinant polynomials `(-ρ s).charpoly.reverse`.
-- * derived API: equality of the exterior-power character data, hence equality of the semisimple
--   Grothendieck classes and the resulting isomorphism criterion.
--
-- Layer triage:
-- * source-facing: LinearRepresentations_Serre_1977's determinant-polynomial criterion and its unipotent triviality
--   corollary.
-- * core/canonical: the bundled semisimple owner theorem
--   `finiteRepGrothendieckClass_eq_iff_nonempty_iso_of_isSemisimple` on `FDRep.of ρ` and
--   `FDRep.of ρ'`.
-- * bridge/view: Chapter `9`'s determinant/exterior-power comparison, the rebundling `FDRep.of`,
--   and the source-facing isomorphism bridge `Representation.Equiv.toFDRepIso`.

section EquivalenceCriterion

variable {V W : Type w}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- Helper for Exercise 18-18.2-6: for each exterior degree, equality of the determinant
polynomials `det (1 + ρ(s) T)` forces equality of the corresponding exterior-power characters. -/
lemma nthExteriorPower_character_eq_of_det_one_add_polynomial_eq
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (hdet : ∀ s : G, (-ρ s).charpoly.reverse = (-ρ' s).charpoly.reverse)
    (n : ℕ) :
    (ρ.nthExteriorPower n).character = (ρ'.nthExteriorPower n).character := by
  ext s
  -- Read the `n`th coefficient of `det (1 + ρ(s) T)` through the exterior-power trace bridge.
  calc
    (ρ.nthExteriorPower n).character s =
        LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n (ρ s)) := by
          simp [Representation.character, Representation.nthExteriorPower]
    _ = (((-ρ s).charpoly.reverse : Polynomial k).coeff n) := by
          exact trace_exteriorPower_map_eq_coeff_neg_charpoly_reverse (A := ρ s) n
    _ = (((-ρ' s).charpoly.reverse : Polynomial k).coeff n) := by
          rw [hdet s]
    _ = LinearMap.trace k (⋀[k]^n W) (exteriorPower.map n (ρ' s)) := by
          symm
          exact trace_exteriorPower_map_eq_coeff_neg_charpoly_reverse (A := ρ' s) n
    _ = (ρ'.nthExteriorPower n).character s := by
          simp [Representation.character, Representation.nthExteriorPower]

/-- Helper for Exercise 18-18.2-6: the determinant-polynomial hypothesis supplies trace equality
on the faithful common-kernel quotient algebra. -/
lemma trace_eq_on_common_kernel_quotient_of_det_one_add_polynomial_eq
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (hdet : ∀ s : G, (-ρ s).charpoly.reverse = (-ρ' s).charpoly.reverse) :
    let ψ : MonoidAlgebra k G →ₐ[k] Module.End k V × Module.End k W :=
      ρ.asAlgebraHom.prod ρ'.asAlgebraHom
    let I : Ideal (MonoidAlgebra k G) := RingHom.ker ψ
    let A := MonoidAlgebra k G ⧸ I
    let φV : A →ₐ[k] Module.End k V :=
      Ideal.Quotient.liftₐ I ρ.asAlgebraHom
        (prod_asAlgebraHom_ker_le_left (ρ := ρ) (ρ' := ρ'))
    let φW : A →ₐ[k] Module.End k W :=
      Ideal.Quotient.liftₐ I ρ'.asAlgebraHom
        (prod_asAlgebraHom_ker_le_right (ρ := ρ) (ρ' := ρ'))
    ∀ a : A, LinearMap.trace k V (φV a) = LinearMap.trace k W (φW a) := by
  -- Route correction: LinearRepresentations_Serre_1977's proof only needs trace equality on the common image algebra, so
  -- we first extract ordinary character equality from the determinant polynomials and then
  -- descend that linear invariant across the quotient.
  have hchar :
      ρ.character = ρ'.character :=
    character_eq_of_det_one_add_polynomial_eq (ρ := ρ) (ρ' := ρ') hdet
  simpa using
    trace_eq_on_common_kernel_quotient_of_character_eq (ρ := ρ) (ρ' := ρ') hchar

/-- Helper for Exercise 18-18.2-6: for every exterior degree, the determinant-polynomial
hypothesis gives trace equality on the whole monoid algebra for the induced exterior-power
representations. -/
lemma trace_eq_asAlgebraHom_of_nthExteriorPower_character_eq_of_det_one_add_polynomial_eq
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (hdet : ∀ s : G, (-ρ s).charpoly.reverse = (-ρ' s).charpoly.reverse)
    (n : ℕ) (a : MonoidAlgebra k G) :
    LinearMap.trace k (⋀[k]^n V) ((ρ.nthExteriorPower n).asAlgebraHom a) =
      LinearMap.trace k (⋀[k]^n W) ((ρ'.nthExteriorPower n).asAlgebraHom a) := by
  -- The source proof first upgrades the determinant identity to equality of all exterior-power
  -- characters, and only then extends that additive invariant from `G` to `k[G]`.
  have hchar :
      (ρ.nthExteriorPower n).character = (ρ'.nthExteriorPower n).character :=
    nthExteriorPower_character_eq_of_det_one_add_polynomial_eq (ρ := ρ) (ρ' := ρ') hdet n
  exact
    trace_eq_asAlgebraHom_of_character_eq
      (ρ := ρ.nthExteriorPower n) (ρ' := ρ'.nthExteriorPower n) hchar a

/-- Helper for Exercise 18-18.2-6: an algebra homomorphism acts by the ambient scalar
multiplication on scalar elements. -/
lemma algHom_scalar_action_apply
    {A : Type*} [Ring A] [Algebra k A]
    {X : Type*} [AddCommGroup X] [Module k X]
    (φ : A →ₐ[k] Module.End k X) (r : k) (x : X) :
    (φ (algebraMap k A r)) x = r • x := by
  -- Evaluate the algebra-hom commutation relation at the chosen vector.
  simpa using congrArg (fun f : Module.End k X ↦ f x) (φ.commutes r)

/-- Helper for Exercise 18-18.2-6: the left quotient action on the common-kernel quotient
recovers the original representation after precomposition with the quotient map. -/
lemma common_kernel_quotient_left_lift_comp_eq_asAlgebraHom
    {ρ : Representation k G V} {ρ' : Representation k G W} :
    let ψ : MonoidAlgebra k G →ₐ[k] Module.End k V × Module.End k W :=
      ρ.asAlgebraHom.prod ρ'.asAlgebraHom
    let I : Ideal (MonoidAlgebra k G) := RingHom.ker ψ
    let φV : (MonoidAlgebra k G ⧸ I) →ₐ[k] Module.End k V :=
      Ideal.Quotient.liftₐ I ρ.asAlgebraHom
        (prod_asAlgebraHom_ker_le_left (ρ := ρ) (ρ' := ρ'))
    φV.comp (Ideal.Quotient.mkₐ k I) = ρ.asAlgebraHom := by
  -- The quotient lift is defined exactly to factor the original action through `k[G] ⧸ I`.
  simpa using
    Ideal.Quotient.liftₐ_comp
      (RingHom.ker (ρ.asAlgebraHom.prod ρ'.asAlgebraHom)) ρ.asAlgebraHom
      (prod_asAlgebraHom_ker_le_left (ρ := ρ) (ρ' := ρ'))

/-- Helper for Exercise 18-18.2-6: the right quotient action on the common-kernel quotient
recovers the original representation after precomposition with the quotient map. -/
lemma common_kernel_quotient_right_lift_comp_eq_asAlgebraHom
    {ρ : Representation k G V} {ρ' : Representation k G W} :
    let ψ : MonoidAlgebra k G →ₐ[k] Module.End k V × Module.End k W :=
      ρ.asAlgebraHom.prod ρ'.asAlgebraHom
    let I : Ideal (MonoidAlgebra k G) := RingHom.ker ψ
    let φW : (MonoidAlgebra k G ⧸ I) →ₐ[k] Module.End k W :=
      Ideal.Quotient.liftₐ I ρ'.asAlgebraHom
        (prod_asAlgebraHom_ker_le_right (ρ := ρ) (ρ' := ρ'))
    φW.comp (Ideal.Quotient.mkₐ k I) = ρ'.asAlgebraHom := by
  -- The same quotient-factorization identity holds for the second representation.
  simpa using
    Ideal.Quotient.liftₐ_comp
      (RingHom.ker (ρ.asAlgebraHom.prod ρ'.asAlgebraHom)) ρ'.asAlgebraHom
      (prod_asAlgebraHom_ker_le_right (ρ := ρ) (ρ' := ρ'))

/-- Exercise 18-18.2-6: two semisimple finite-dimensional `k[G]`-modules for an arbitrary monoid
are isomorphic as `k[G]`-modules if, for every `s : G`, the polynomial `det (1 + s T)` agrees on
the two modules; in Lean this is expressed by equality of `(-ρ s).charpoly.reverse`, the
basis-free polynomial corresponding to `det (1 + ρ(s) T)`. -/
-- Proof sketch: the coefficients of `(-ρ s).charpoly.reverse` are the values at `s` of the
-- characters of the exterior powers of `ρ`, via Chapter `9`'s determinant/exterior-power bridge.
-- Equality of these polynomials for all `s` therefore identifies the exterior-power character data
-- of `ρ` and `ρ'`. In the semisimple Grothendieck group this forces the same multiset of simple
-- constituents, and Remark `14-14.1-2` then upgrades equality of classes to an isomorphism.
theorem nonempty_equiv_of_isSemisimple_of_det_one_add_polynomial_eq
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (hρ : IsSemisimpleRepresentation ρ) (hρ' : IsSemisimpleRepresentation ρ')
    (hdet : ∀ s : G, (-ρ s).charpoly.reverse = (-ρ' s).charpoly.reverse) :
    Nonempty (ρ.Equiv ρ') := by
  let ψ : MonoidAlgebra k G →ₐ[k] Module.End k V × Module.End k W :=
    ρ.asAlgebraHom.prod ρ'.asAlgebraHom
  let I : Ideal (MonoidAlgebra k G) := RingHom.ker ψ
  letI : I.IsTwoSided := by
    change (RingHom.ker ψ).IsTwoSided
    infer_instance
  let A := MonoidAlgebra k G ⧸ I
  let φV : A →ₐ[k] Module.End k V :=
    Ideal.Quotient.liftₐ I ρ.asAlgebraHom
      (prod_asAlgebraHom_ker_le_left (ρ := ρ) (ρ' := ρ'))
  let φW : A →ₐ[k] Module.End k W :=
    Ideal.Quotient.liftₐ I ρ'.asAlgebraHom
      (prod_asAlgebraHom_ker_le_right (ρ := ρ) (ρ' := ρ'))
  have htraceA :
      ∀ a : A, LinearMap.trace k V (φV a) = LinearMap.trace k W (φW a) := by
    -- Route correction: this is the last valid quotient-level invariant presently available. The
    -- stronger exterior-power descent on the same quotient algebra is blocked by the
    -- nonadditivity of `A ↦ exteriorPower.map n A`.
    simpa [ψ, I, A, φV, φW] using
      trace_eq_on_common_kernel_quotient_of_det_one_add_polynomial_eq
        (ρ := ρ) (ρ' := ρ') hdet
  let _ : Module.Finite k A := by
    -- The common image algebra is finite-dimensional because it is a quotient of the image in
    -- `End_k(V) × End_k(W)`.
    simpa [ψ, I, A] using common_kernel_quotient_finite (ρ := ρ) (ρ' := ρ')
  let _ : IsSemisimpleRing A := by
    -- The quotient is semisimple because it acts faithfully on the descended semisimple modules.
    simpa [ψ, I, A] using
      common_kernel_quotient_isSemisimpleRing
        (ρ := ρ) (ρ' := ρ') hρ hρ'
  letI : Module A V := Module.compHom V φV.toRingHom
  letI : Module A W := Module.compHom W φW.toRingHom
  have hsemV : IsSemisimpleModule A V := by
    have hsemV_from_monoidAlgebra :
        let _ : Module (MonoidAlgebra k G) V :=
          Module.compHom V (φV.toRingHom.comp (Ideal.Quotient.mkₐ k I).toRingHom)
        IsSemisimpleModule (MonoidAlgebra k G) V := by
      -- Restricting scalars along the quotient map recovers the original `k[G]`-module.
      simpa [A, I, φV, ψ] using
        (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp hρ
    exact
      isSemisimpleModule_of_ringHom_surjective
        (q := (Ideal.Quotient.mkₐ k I).toRingHom)
        (hq := Ideal.Quotient.mk_surjective)
        hsemV_from_monoidAlgebra
  have hsemW : IsSemisimpleModule A W := by
    have hsemW_from_monoidAlgebra :
        let _ : Module (MonoidAlgebra k G) W :=
          Module.compHom W (φW.toRingHom.comp (Ideal.Quotient.mkₐ k I).toRingHom)
        IsSemisimpleModule (MonoidAlgebra k G) W := by
      -- The same quotient-action comparison holds for the second representation.
      simpa [A, I, φW, ψ] using
        (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ').mp hρ'
    exact
      isSemisimpleModule_of_ringHom_surjective
        (q := (Ideal.Quotient.mkₐ k I).toRingHom)
        (hq := Ideal.Quotient.mk_surjective)
        hsemW_from_monoidAlgebra
  have hexteriorTrace :
      ∀ n (a : MonoidAlgebra k G),
        LinearMap.trace k (⋀[k]^n V) ((ρ.nthExteriorPower n).asAlgebraHom a) =
          LinearMap.trace k (⋀[k]^n W) ((ρ'.nthExteriorPower n).asAlgebraHom a) := by
    intro n a
    -- Route correction: this is the exact additive invariant delivered by LinearRepresentations_Serre_1977's proof route on
    -- `k[G]`; the missing owner still has to convert these exterior-power traces into
    -- multiplicity equality on the common semisimple image algebra.
    exact
      trace_eq_asAlgebraHom_of_nthExteriorPower_character_eq_of_det_one_add_polynomial_eq
        (ρ := ρ) (ρ' := ρ') hdet n a
  have hcompV : φV.comp (Ideal.Quotient.mkₐ k I) = ρ.asAlgebraHom := by
    -- The quotient action was defined precisely so that composing with the quotient map recovers
    -- the original representation algebra homomorphism.
    simpa [ψ, I, φV] using
      common_kernel_quotient_left_lift_comp_eq_asAlgebraHom (ρ := ρ) (ρ' := ρ')
  have hcompW : φW.comp (Ideal.Quotient.mkₐ k I) = ρ'.asAlgebraHom := by
    -- The same compatibility holds for the second representation.
    simpa [ψ, I, φW] using
      common_kernel_quotient_right_lift_comp_eq_asAlgebraHom (ρ := ρ) (ρ' := ρ')
  have hAlinear : Nonempty (V ≃ₗ[A] W) := by
    -- Route correction: pass the quotient map and its algebra-hom compatibility directly to the
    -- projector-lift owner, matching the source proof's density step.
    simpa [A, φV, φW] using
      nonempty_linearEquiv_of_exterior_trace_eq_on_finite_semisimple_image
        (A := A) (V := V) (W := W) (ρ := ρ) (ρ' := ρ')
        (φV := φV) (φW := φW) (liftι := Ideal.Quotient.mkₐ k I) hcompV hcompW
        Ideal.Quotient.mk_surjective
        (by simpa [A, φV] using hsemV)
        (by simpa [A, φW] using hsemW)
        hexteriorTrace
  rcases hAlinear with ⟨e⟩
  -- Convert the descended `A`-linear equivalence back into a `G`-equivariant equivalence.
  let eₖ : V ≃ₗ[k] W :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro r x
        have hVscalar : (φV (algebraMap k A r) : V →ₗ[k] V) x = r • x :=
          algHom_scalar_action_apply (k := k) (φ := φV) r x
        have hWscalar : (φW (algebraMap k A r) : W →ₗ[k] W) (e x) = r • e x :=
          algHom_scalar_action_apply (k := k) (φ := φW) r (e x)
        calc
          e (r • x) = e ((φV (algebraMap k A r)) x) := by rw [hVscalar]
          _ = (φW (algebraMap k A r)) (e x) := by
                exact e.map_smul (algebraMap k A r) x
          _ = r • e x := hWscalar }
  refine ⟨Representation.Equiv.mk eₖ ?_⟩
  intro g
  ext x
  let a : A := Ideal.Quotient.mkₐ k I ((MonoidAlgebra.of k G) g)
  have hVg : (φV a : V →ₗ[k] V) x = (ρ g) x := by
    simpa [a, A, I, φV, Representation.asAlgebraHom_of]
  have hWg : (φW a : W →ₗ[k] W) (e x) = (ρ' g) (e x) := by
    simpa [a, A, I, φW, Representation.asAlgebraHom_of]
  calc
    e ((ρ g) x) = e ((φV a) x) := by rw [hVg]
    _ = (φW a) (e x) := by exact e.map_smul a x
    _ = (ρ' g) (e x) := hWg

end EquivalenceCriterion

section TrivialityCriterion

/-- Helper for Exercise 18-18.2-6: a unipotent action endomorphism has the same determinant
polynomial `det (1 + s T)` as the trivial action. -/
lemma charpoly_reverse_neg_eq_trivial_of_isNilpotent_sub_one
    {ρ : Representation k G V} (s : G) (hs : IsNilpotent (ρ s - 1)) :
    (-ρ s).charpoly.reverse = (-(Representation.trivial k G V s)).charpoly.reverse := by
  -- Rewrite unipotence as nilpotence of `1 - ρ(s)` so that `charpoly_sub_smul` applies directly.
  have hneg : IsNilpotent ((1 : V →ₗ[k] V) - ρ s) := by
    simpa [sub_eq_add_neg, add_comm] using hs.neg
  have hnil : (((1 : V →ₗ[k] V) - ρ s)).charpoly = Polynomial.X ^ Module.finrank k V :=
    IsNilpotent.charpoly_eq_X_pow_finrank hneg
  have hchar : (-ρ s).charpoly = (Polynomial.X + 1) ^ Module.finrank k V := by
    -- Translating the characteristic polynomial by `-1` identifies the `-ρ(s)` characteristic
    -- polynomial with the nilpotent polynomial `X^n`.
    have hsub : (((1 : V →ₗ[k] V) - ρ s)).charpoly =
        (-ρ s).charpoly.comp (Polynomial.X + Polynomial.C (-1 : k)) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        LinearMap.charpoly_sub_smul (-ρ s) (-1 : k)
    rw [hnil] at hsub
    have hcomp :=
      congrArg (fun q : Polynomial k ↦ q.comp (Polynomial.X + 1)) hsub.symm
    simpa [Polynomial.comp_assoc, add_comm, add_left_comm, add_assoc, sub_eq_add_neg, pow_mul] using
      hcomp
  -- Both sides are now the reverse of the same binomial characteristic polynomial.
  have htriv : (-(Representation.trivial k G V s)).charpoly =
      (Polynomial.X + 1) ^ Module.finrank k V := by
    simpa [Representation.trivial] using
      LinearMap.charpoly_sub_smul (0 : V →ₗ[k] V) (1 : k)
  rw [hchar, htriv]

/-- Helper for Exercise 18-18.2-6: an equivariant equivalence with the trivial representation
forces the original representation itself to be trivial. -/
lemma isTrivial_of_nonempty_equiv_trivial
    {ρ : Representation k G V}
    (h : Nonempty (ρ.Equiv (Representation.trivial k G V))) :
    ρ.IsTrivial := by
  rcases h with ⟨e⟩
  -- Conjugating `ρ(g)` by the chosen equivalence identifies it with the identity map.
  refine ⟨fun g ↦ ?_⟩
  ext x
  have hx : e ((ρ g) x) = e x := by
    simpa [Representation.trivial] using
      congrArg (fun f : V →ₗ[k] V ↦ f x) (e.isIntertwining' g)
  exact e.injective hx

/-- Helper for Exercise 18-18.2-6: the trivial representation is semisimple because every
subspace is stable under the identity action. -/
lemma trivial_isSemisimpleRepresentation :
    IsSemisimpleRepresentation (Representation.trivial k G V) := by
  let e : Submodule k V ≃o Subrepresentation (Representation.trivial k G V) :=
    { toFun := fun W ↦
        { toSubmodule := W
          apply_mem_toSubmodule := by
            intro g x hx
            simpa [Representation.trivial] using hx }
      invFun := Subrepresentation.toSubmodule
      left_inv := by
        intro W
        rfl
      right_inv := by
        intro W
        rfl
      map_rel_iff' := by
        intro W W'
        rfl }
  letI : ComplementedLattice (Subrepresentation (Representation.trivial k G V)) :=
    OrderIso.complementedLattice e
  infer_instance

/-- A semisimple finite-dimensional representation is trivial when every action endomorphism is
unipotent, i.e. when `ρ s - 1` is nilpotent for every `s : G`. -/
-- Proof sketch: compare `ρ` with the trivial representation on the same vector space. If every
-- `ρ s` is unipotent, then
-- `(-ρ s).charpoly.reverse = (-(Representation.trivial k G V s)).charpoly.reverse`
-- for all `s`, because both equal `(X + 1) ^ finrank k V`. Apply
-- `nonempty_equiv_of_isSemisimple_of_det_one_add_polynomial_eq`, and transport the trivial action
-- across the resulting equivariant linear equivalence.
theorem isTrivial_of_isSemisimple_of_isNilpotent_sub_one
    {ρ : Representation k G V} (hρ : IsSemisimpleRepresentation ρ)
    (hunipotent : ∀ s : G, IsNilpotent (ρ s - 1)) :
    ρ.IsTrivial := by
  -- Compare `ρ` with the trivial representation via the determinant-polynomial criterion above.
  have htriv : IsSemisimpleRepresentation (Representation.trivial k G V) :=
    trivial_isSemisimpleRepresentation
  have hequiv : Nonempty (ρ.Equiv (Representation.trivial k G V)) := by
    apply nonempty_equiv_of_isSemisimple_of_det_one_add_polynomial_eq hρ htriv
    intro s
    exact charpoly_reverse_neg_eq_trivial_of_isNilpotent_sub_one s (hunipotent s)
  -- Once the two representations are equivariantly equivalent, the action must be trivial.
  exact isTrivial_of_nonempty_equiv_trivial hequiv

end TrivialityCriterion

end

end Representation

/-! ### Exercise_18_18_2_7 (from Chap18) -/
noncomputable section

open scoped BigOperators Representation

universe u v x

namespace Representation

section

variable {p : ℕ}
variable {G : Type u} [Group G]

/-- The conjugate of a `p`-regular element of `G` that lies in `H`, viewed as a `p`-regular
element of `H`. -/
def conjPRegularInSubgroup (H : Subgroup G) (s : { t : G // IsPRegular p t }) (r : G)
    (hsr : r⁻¹ * s.1 * r ∈ H) : { t : H // IsPRegular p t } :=
  ⟨⟨r⁻¹ * s.1 * r, hsr⟩, by
    rw [IsPRegular, Subgroup.orderOf_mk]
    simpa using isPRegular_conj p s.1 r⁻¹ s.2⟩

end

section

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v} [AddCommMonoid A]
variable {G : Type u} [Group G] [Finite G]

local instance subgroupMemDecidablePred (H : Subgroup G) : DecidablePred fun g : G ↦ g ∈ H :=
  Classical.decPred _

/-
Domain-style sampling:
* primary domain: induced character formulas for subgroup induction and their Brauer-character
  specialization on `p`-regular elements;
* relevant owner declarations in this domain:
  `Representation.character_eq_sum_over_representatives_of_equiv_induced`,
  `Representation.modularCharacter`,
  `Representation.FDRep.subgroupInduction`,
  and the Chapter 18 notation `φ[lift](ρ)`;
* best owner abstraction: Chapter 3's source-facing representative-sum theorem for induced
  characters, specialized through the Chapter 18 modular-character owner;
* source/core/bridge triage:
  source-facing: the representative-sum formula below for the Brauer character of `Ind_H^G(F)`;
  core/canonical: `Representation.modularCharacter` and
    `Representation.character_eq_sum_over_representatives_of_equiv_induced`;
  bridge/view: the bundled finite-dimensional induced owner `FDRep.subgroupInduction` and the
    subgroup-valued conjugation input `conjPRegularInSubgroup`.
* primitive data: a lift `lift : PrimeToPRoot p k → A`, subgroup `H`, finite-dimensional
  `H`-representation `F`, a representative set `R`, and a `p`-regular element `s`;
* derived API: the value of the modular character of the induced representation as the standard
  sum over left-coset representatives, with the summand evaluated at
  `conjPRegularInSubgroup H s r hsr`.
-/

-- Proof sketch: apply the characteristic-zero induced-character formula to the induced
-- representation, and identify each summand with the modular character of `F` on the corresponding
-- `p`-regular conjugate in `H`, with the sum indexed by left-coset representatives of `H`.
omit [Finite G] in
/-- Helper for Exercise 18-18.2-7: for the canonical scalar-valued lift, the modular character
agrees with the ordinary character on the `p`-regular locus. -/
private theorem modularCharacter_eq_character_of_scalarLift
    {V : Type x} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k G V) (s : { t : G // IsPRegular p t }) :
    φ[(fun x : PrimeToPRoot p k ↦ ((x : kˣ) : k))](ρ) s = ρ.character s.1 := by
  classical
  -- Expand the ordinary character as the sum of the characteristic roots of `ρ s.1`.
  rw [Representation.character]
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  -- Each packaged prime-to-`p` root in the modular-character definition coerces back to the same
  -- scalar root in `k`.
  simp [Representation.modularCharacter, charpolyRoot_primeToPRoot_coe]

/-- Helper for Exercise 18-18.2-7: with the canonical scalar lift to `k`, subgroup induction
satisfies the same representative-sum formula as the ordinary character. -/
private theorem modularCharacter_subgroupInduction_eq_sum_over_representatives_scalarLift
    (H : Subgroup G)
    (F : FDRep k H)
    (R : Finset G) (hR : Subgroup.IsComplement (R : Set G) (H : Set G))
    (s : { t : G // IsPRegular p t }) :
    φ[(fun x : PrimeToPRoot p k ↦ ((x : kˣ) : k))]((FDRep.subgroupInduction F).ρ) s =
      ∑ r ∈ R,
        if hsr : r⁻¹ * s.1 * r ∈ H then
          φ[(fun x : PrimeToPRoot p k ↦ ((x : kˣ) : k))](F.ρ)
            (conjPRegularInSubgroup H s r hsr)
        else
          0 := by
  classical
  let e : Representation.Equiv ((FDRep.subgroupInduction F).ρ) (ind H.subtype F.ρ) := by
    -- `FDRep.subgroupInduction` is just the bundled owner of the standard induced model.
    simpa [FDRep.subgroupInduction] using
      (Representation.Equiv.refl (ind H.subtype F.ρ))
  -- Route correction: first reduce the scalar-valued modular character to the ordinary character,
  -- then invoke the Chapter `3` induced-character formula.
  calc
    φ[(fun x : PrimeToPRoot p k ↦ ((x : kˣ) : k))]((FDRep.subgroupInduction F).ρ) s =
        Representation.character ((FDRep.subgroupInduction F).ρ) s.1 := by
          simpa using
            modularCharacter_eq_character_of_scalarLift (ρ := (FDRep.subgroupInduction F).ρ) s
    _ = ∑ r ∈ R,
          if hsr : r⁻¹ * s.1 * r ∈ H then
            Representation.character F.ρ ⟨r⁻¹ * s.1 * r, hsr⟩
          else
            0 := by
          simpa using
            Representation.character_eq_sum_over_representatives_of_equiv_induced
              ((FDRep.subgroupInduction F).ρ) H F.ρ e R hR s.1
    _ = ∑ r ∈ R,
          if hsr : r⁻¹ * s.1 * r ∈ H then
            φ[(fun x : PrimeToPRoot p k ↦ ((x : kˣ) : k))](F.ρ)
              (conjPRegularInSubgroup H s r hsr)
          else
            0 := by
          -- Each subgroup summand is again a scalar-lift modular-character value.
          refine Finset.sum_congr rfl ?_
          intro r hr
          by_cases hsr : r⁻¹ * s.1 * r ∈ H
          · simpa [hsr] using
              (modularCharacter_eq_character_of_scalarLift
                (ρ := F.ρ) (s := conjPRegularInSubgroup H s r hsr)).symm
          · simp [hsr]

/-- Exercise 18-18.2-7: if `E = Ind_H^G(F)`, then for any finite set `R` of representatives of
the left cosets `G / H`, the modular character of `E` at a `p`-regular element of `G` is given
by the same representative sum as in the characteristic-zero induced-character formula.  This
source-facing Lean form uses the canonical scalar-valued lift of prime-to-`p` roots to `k`; an
arbitrary function `PrimeToPRoot p k → A` is too weak for the induced-cycle cancellation used in
LinearRepresentations_Serre_1977's proof. -/
theorem modularCharacter_subgroupInduction_eq_sum_over_representatives
    (H : Subgroup G)
    (F : FDRep k H)
    (R : Finset G) (hR : Subgroup.IsComplement (R : Set G) (H : Set G))
    (s : { t : G // IsPRegular p t }) :
    φ[(fun x : PrimeToPRoot p k ↦ ((x : kˣ) : k))]((FDRep.subgroupInduction F).ρ) s =
      ∑ r ∈ R,
        if hsr : r⁻¹ * s.1 * r ∈ H then
          φ[(fun x : PrimeToPRoot p k ↦ ((x : kˣ) : k))](F.ρ)
            (conjPRegularInSubgroup H s r hsr)
        else
          0 := by
  exact modularCharacter_subgroupInduction_eq_sum_over_representatives_scalarLift H F R hR s

end

end Representation
