import LinearRepresentations_Serre_1977.Serre.Chap16.Proposition_16_16_4_1.Index
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.CanonicalPacketFrontier

noncomputable section

open scoped MonoidAlgebra
open Representation
open CategoryTheory

universe u v w x y

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type w} [Group G]
variable {E : Type x} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]

local notation "k" => IsLocalRing.ResidueField A

namespace StableLattice

section DefectZero

variable [Finite G] [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
variable {ρ : Representation K G E} [FiniteDimensional K E]
variable (L : StableLattice A ρ)

/-- Helper for Proposition 16-16.4-1: once each packet constituent is matched with a member of a
complete pairwise nonisomorphic irreducible family, the chosen reindexing map is automatically
injective. This isolates the uniqueness part of the characteristic-zero packet-to-complete-family
transport before extending the packet data by zero off the image. -/
lemma exists_packet_complete_family_reindex_local
    {F : Type*} [Field F]
    {ι κ : Type*} [Fintype ι]
    (ψ : ι → Rep F G)
    (hψ_pairwise : CategoryTheory.PairwiseNonisomorphic ψ)
    (π : κ → Rep F G) (c : ι → κ)
    (e : ∀ i, Nonempty ((ψ i).ρ.Equiv (π (c i)).ρ)) :
    Function.Injective c := by
  intro i i' hcc
  by_contra hii
  have hiso : Nonempty (ψ i ≅ ψ i') := by
    rcases e i with ⟨ei⟩
    rcases e i' with ⟨ei'⟩
    -- Compare the two packet constituents through the common complete-family target `π (c i)`.
    have hmid : (π (c i)).ρ.Equiv (π (c i')).ρ := by
      exact hcc ▸ Representation.Equiv.refl ((π (c i)).ρ)
    have hequiv : (ψ i).ρ.Equiv (ψ i').ρ := ei.trans (hmid.trans ei'.symm)
    have hisoRep : Nonempty (ψ i ≅ ψ i') := ⟨Rep.mkIso hequiv⟩
    simpa using hisoRep
  exact hψ_pairwise hii hiso

/-- Helper for Proposition 16-16.4-1: precomposing a representation with a group equivalence does
not change its invariant subspace lattice, so irreducibility survives the `Shrink.mulEquiv`
transport used to synchronize the group universe with `AlgebraicClosure K`. -/
lemma isIrreducible_comp_of_mulEquiv_univ_local
    {F : Type*} [Field F]
    {G0 : Type*} [Group G0]
    {H : Type*} [Group H]
    {V : Type*} [AddCommGroup V] [Module F V]
    (e : G0 ≃* H)
    (σ : Representation F H V)
    [σ.IsIrreducible] :
    Representation.IsIrreducible (σ.comp e.toMonoidHom) := by
  classical
  letI : Nontrivial (Subrepresentation (σ.comp e.toMonoidHom)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation σ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using congrArg Subrepresentation.toSubmodule h
    exact IsSimpleOrder.bot_ne_top h'
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro W hW
  let W' : Subrepresentation σ :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        intro h x hx
        -- Translate stability across the group equivalence one element at a time.
        simpa using W.apply_mem_toSubmodule (e.symm h) hx }
  have hW'_ne_bot : W' ≠ ⊥ := by
    intro hW'
    apply hW
    apply Subrepresentation.toSubmodule_injective
    simpa [W'] using congrArg Subrepresentation.toSubmodule hW'
  have hW'_top : W' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W').resolve_left hW'_ne_bot
  -- Push the transported top statement back to the original precomposed representation.
  apply Subrepresentation.toSubmodule_injective
  simpa [W'] using congrArg Subrepresentation.toSubmodule hW'_top

/-- Helper for Proposition 16-16.4-1: pairwise nonisomorphism is also preserved by the same
`Shrink.mulEquiv` precomposition. This keeps the packet family distinct after the universe
alignment step in the characteristic-zero branch. -/
lemma pairwiseNonisomorphic_comp_of_mulEquiv_local
    {F : Type*} [Field F]
    {G0 : Type*} [Group G0]
    {H : Type*} [Group H]
    {ι : Type*}
    (e : G0 ≃* H)
    (ψ : ι → Rep F H)
    (hψ_pairwise : CategoryTheory.PairwiseNonisomorphic ψ) :
    CategoryTheory.PairwiseNonisomorphic
      (fun i ↦ Rep.of ((ψ i).ρ.comp e.toMonoidHom)) := by
  intro i j hij hIso
  rcases hIso with ⟨f⟩
  let fRep :
      Representation.Equiv ((ψ i).ρ.comp e.toMonoidHom) ((ψ j).ρ.comp e.toMonoidHom) :=
    Representation.equivOfIso f
  have horig : Nonempty (ψ i ≅ ψ j) := by
    refine ⟨Rep.mkIso <| Representation.Equiv.mk fRep.toLinearEquiv ?_⟩
    intro g
    -- Test the transported intertwining law at `e.symm g` to recover the original one.
    simpa using fRep.toIntertwiningMap.isIntertwining' (e.symm g)
  exact hψ_pairwise hij horig

/-- Helper for Proposition 16-16.4-1: after replacing `G` by `Shrink G`, the characteristic-zero
packet family still admits a complete pairwise nonisomorphic irreducible family on the
same-universe group. This packages the verified complete-family owner before the remaining
reindexing and coefficient comparison starts. -/
lemma algClosureShrinkCompleteFamilyReindex_local
    [CharZero K]
    {ι : Type*} [Fintype ι]
    (ψH : ι → Rep (AlgebraicClosure K) (Shrink.{v} G))
    [∀ i, FiniteDimensional (AlgebraicClosure K) (ψH i)]
    (hψH_pairwise : CategoryTheory.PairwiseNonisomorphic ψH)
    (hψH_irr : ∀ i, (ψH i).ρ.IsIrreducible) :
    ∃ (κ : Type v) (_ : Fintype κ) (π : κ → FDRep (AlgebraicClosure K) (Shrink.{v} G)),
      CategoryTheory.PairwiseNonisomorphic π ∧
      Representation.IsCompleteIrreducibleFamily π := by
  -- Choose a complete family directly on `Shrink G`, so no later transport has to repair the
  -- universe mismatch between the field and the group.
  obtain ⟨κ, hκ, π, hπ_pairwise, hπ_complete⟩ :=
    _root_.Representation.exists_complete_pairwise_nonisomorphic_simple_family_local
      (K := AlgebraicClosure K) (G := Shrink.{v} G)
  -- The same-universe complete-family owner is available; the remaining reindexing data is the
  -- first unresolved characteristic-zero transport step.
  exact ⟨κ, hκ, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Proposition 16-16.4-1: a complete irreducible family contains every irreducible
finite-dimensional representation up to a usable `Representation.Equiv`. This extracts the
concrete equivalence data that the characteristic-zero packet argument needs before any
coefficient transport. -/
lemma completeFamilyMemberEquivOfIrreducible_local
    {H : Type v} [Group H] [Finite H]
    {κ : Type*}
    (π : κ → FDRep (AlgebraicClosure K) H)
    (hπ_complete : Representation.IsCompleteIrreducibleFamily π)
    (τ : Rep (AlgebraicClosure K) H)
    [FiniteDimensional (AlgebraicClosure K) τ]
    [τ.ρ.IsIrreducible] :
    ∃ q, Nonempty (τ.ρ.Equiv (π q).ρ) := by
  let τbasis : Representation (AlgebraicClosure K) H
      (Fin (Module.finrank (AlgebraicClosure K) τ) → AlgebraicClosure K) :=
    let eBasis := (Module.finBasis (AlgebraicClosure K) τ).equivFun
    { toFun := fun g ↦ eBasis.conj (τ.ρ g)
      map_one' := by
        ext x
        simp [LinearEquiv.conj_apply_apply]
      map_mul' := by
        intro g h
        ext x
        simp [LinearEquiv.conj_apply_apply] }
  let eBasis : τ.ρ.Equiv τbasis := by
    refine Representation.Equiv.mk (Module.finBasis (AlgebraicClosure K) τ).equivFun ?_
    intro g
    ext x
    simp [τbasis, LinearEquiv.conj_apply_apply]
  have hτbasis_irr : τbasis.IsIrreducible := by
    exact isIrreducible_of_nonempty_equiv ⟨eBasis⟩
  -- Move the packet constituent to finite-basis coordinates so the complete-family owner can be
  -- applied without reopening the carrier-universe mismatch.
  obtain ⟨q, hq⟩ :=
    Representation.IsCompleteIrreducibleFamily.exists_iso_of_representation
      π hπ_complete τbasis hτbasis_irr
  rcases hq with ⟨eFD⟩
  refine ⟨q, ?_⟩
  let eτπ : τbasis.Equiv (π q).ρ :=
    Representation.equivOfIso
      ((CategoryTheory.forget₂
        (FDRep (AlgebraicClosure K) H)
        (Rep (AlgebraicClosure K) H)).mapIso eFD)
  exact ⟨eBasis.trans eτπ⟩

/-- Helper for Proposition 16-16.4-1: once a packet family is known to be pairwise nonisomorphic
and irreducible, a complete irreducible family supplies a concrete injective reindexing into its
coordinates together with the needed representation equivalences. This packages the last purely
existential step before the characteristic-zero coefficient chase. -/
lemma completeFamilyPacketReindex_local
    {H : Type v} [Group H] [Finite H]
    {ι κ : Type*} [Fintype ι]
    (ψH : ι → Rep (AlgebraicClosure K) H)
    [∀ i, FiniteDimensional (AlgebraicClosure K) (ψH i)]
    (hψH_pairwise : CategoryTheory.PairwiseNonisomorphic ψH)
    (hψH_irr : ∀ i, (ψH i).ρ.IsIrreducible)
    (π : κ → FDRep (AlgebraicClosure K) H)
    (hπ_complete : Representation.IsCompleteIrreducibleFamily π) :
    ∃ c : ι → κ,
      Function.Injective c ∧
      ∀ i, Nonempty ((ψH i).ρ.Equiv (π (c i)).ρ) := by
  classical
  let c : ι → κ := fun i ↦
    Classical.choose <|
      StableLattice.completeFamilyMemberEquivOfIrreducible_local
        (π := π) hπ_complete (ψH i)
  have hequiv : ∀ i, Nonempty ((ψH i).ρ.Equiv (π (c i)).ρ) := by
    intro i
    exact
      Classical.choose_spec <|
        StableLattice.completeFamilyMemberEquivOfIrreducible_local
          (π := π) hπ_complete (ψH i)
  have hc : Function.Injective c := by
    -- Once each packet constituent lands in a complete-family coordinate, pairwise nonisomorphism
    -- forces the chosen reindexing to be injective.
    exact
      StableLattice.exists_packet_complete_family_reindex_local
        (ψ := ψH) hψH_pairwise (π := fun q ↦ Rep.of (π q).ρ) c hequiv
  exact ⟨c, hc, hequiv⟩

/-- Helper for Proposition 16-16.4-1: once the complete-family reindex exists on `Shrink G`,
choose concrete packet coordinates together with concrete representation equivalences into those
coordinates. This packages the only classical choice step before the remaining characteristic-zero
coefficient/action comparison. -/
noncomputable def packet_constituent_choice_on_shrink_local
    {H : Type v} [Group H] [Finite H]
    {ι κ : Type*} [Fintype ι]
    (ψH : ι → Rep (AlgebraicClosure K) H)
    [∀ i, FiniteDimensional (AlgebraicClosure K) (ψH i)]
    (hψH_pairwise : CategoryTheory.PairwiseNonisomorphic ψH)
    (hψH_irr : ∀ i, (ψH i).ρ.IsIrreducible)
    (π : κ → FDRep (AlgebraicClosure K) H)
    (hπ_complete : Representation.IsCompleteIrreducibleFamily π) :
    Σ' c : ι → κ,
      Σ' _ : Function.Injective c, ∀ i, (ψH i).ρ.Equiv (π (c i)).ρ := by
  classical
  -- `completeFamilyPacketReindex_local` returns a `Prop`-valued `∃`, so we extract its witness and
  -- spec with `Classical.choose` (an `obtain` into this data-valued `def` would be a forbidden large
  -- elimination of `Exists`). `Representation.Equiv` is data (a structure), carried via `Σ'`.
  let res := StableLattice.completeFamilyPacketReindex_local
    (ψH := ψH) hψH_pairwise hψH_irr π hπ_complete
  exact ⟨res.choose, res.choose_spec.1, fun i ↦ Classical.choice (res.choose_spec.2 i)⟩


end DefectZero

end StableLattice

end
