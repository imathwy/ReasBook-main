import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.Index
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.CanonicalPacketFrontier
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.Frontier_PacketReindex

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

/-- Helper for Proposition 16-16.4-1: for a complete irreducible family over the same-universe
group `H`, the inverse Wedderburn preimage of a family of endomorphisms acts on each coordinate by
the prescribed endomorphism. This is the direct executable replacement for the old placeholder
coordinate-action bridge. -/
lemma charZeroSupportedFamilyCoordinateAction_local
    {H : Type v} [Group H] [Finite H]
    [Invertible (Nat.card H : AlgebraicClosure K)]
    {κ : Type*} [Fintype κ]
    (π : κ → Rep (AlgebraicClosure K) H)
    [∀ q, FiniteDimensional (AlgebraicClosure K) (π q)]
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : Representation.IsCompleteIrreducibleFamily fun q ↦ FDRep.of (π q).ρ)
    (supported : ∀ q, Module.End (AlgebraicClosure K) (π q)) (q : κ) :
    (Representation.irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete)
        ((Representation.irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete).symm supported) q =
      supported q := by
  -- Read the `q`-coordinate directly from `apply_symm_apply`, avoiding the non-executable
  -- placeholder bridge in `PacketBridge`.
  exact
    congrFun
      ((Representation.irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete).apply_symm_apply
        supported)
      q

/-- Helper for Proposition 16-16.4-1: after extending a packet-indexed family by zero away from
`Finset.univ.image c`, the inverse Wedderburn coefficient formula on `H` collapses to the packet
image. This packages the executable coefficient-normalization step before the remaining trace
transport back to the ambient packet data. -/
lemma charZeroSupportedFamilyCoeffCollapseOnShrink_local
    {H : Type v} [Group H] [Finite H]
    [Invertible (Nat.card H : AlgebraicClosure K)]
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (π : κ → Rep (AlgebraicClosure K) H)
    [∀ q, FiniteDimensional (AlgebraicClosure K) (π q)]
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : Representation.IsCompleteIrreducibleFamily fun q ↦ FDRep.of (π q).ρ)
    {ι : Type*} [Fintype ι]
    {c : ι → κ} (hc : Function.Injective c)
    (f : ∀ i, Module.End (AlgebraicClosure K) (π (c i))) (s : H) :
    ((Representation.irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete).symm
        (StableLattice.charZero_supported_family_local (π := π) c hc f)) s =
      (Nat.card H : AlgebraicClosure K)⁻¹ *
        ∑ i : ι, (Module.finrank (AlgebraicClosure K) (π (c i)) : AlgebraicClosure K) *
          LinearMap.trace (AlgebraicClosure K) (π (c i)) ((π (c i)).ρ s⁻¹ * f i) := by
  classical
  let term : κ → AlgebraicClosure K := fun q ↦
    (Module.finrank (AlgebraicClosure K) (π q) : AlgebraicClosure K) *
      LinearMap.trace (AlgebraicClosure K) (π q)
        ((π q).ρ s⁻¹ * StableLattice.charZero_supported_family_local (π := π) c hc f q)
  -- Start from the Chapter `6` coefficient formula for the inverse Wedderburn preimage.
  rw [Representation.irreducibleFamilyEndAlgEquiv_symm_apply (π := π) hπ_pairwise hπ_complete]
  rw [Representation.finsum_eq_sum_univ]
  change (Nat.card H : AlgebraicClosure K)⁻¹ * Finset.univ.sum term = _
  congr 1
  calc
    Finset.univ.sum term = (Finset.univ.image c).sum term := by
      -- Off the packet image, the supported family is zero, so those trace terms vanish.
      symm
      refine Finset.sum_subset ?_ ?_
      · intro q hq
        simp
      · intro q hq hqmem
        exact
          StableLattice.supported_family_trace_summand_eq_zero_of_not_mem_local
            (π := π) (hc := hc) f s hqmem
    _ = ∑ i : ι, term (c i) := by
      -- Reindex the remaining sum along the injective packet map `c`.
      exact
        Finset.sum_image (s := (Finset.univ : Finset ι)) (g := c) (f := term) <| by
          intro i hi j hj hij
          exact hc hij
    _ = ∑ i : ι, (Module.finrank (AlgebraicClosure K) (π (c i)) : AlgebraicClosure K) *
          LinearMap.trace (AlgebraicClosure K) (π (c i)) ((π (c i)).ρ s⁻¹ * f i) := by
      -- On the packet image, the supported family recovers the original packet endomorphism.
      refine Finset.sum_congr rfl ?_
      intro i hi
      dsimp [term]
      rw [StableLattice.supported_family_trace_summand_eq_image_local (π := π) (hc := hc) f s i]

/-- Helper for Proposition 16-16.4-1: transporting a packet endomorphism across the chosen
complete-family equivalence preserves the Fourier trace term on `Shrink G`. This isolates the
single trace-transport rewrite that the remaining characteristic-zero coefficient comparison still
needs. -/
lemma packetEquivTraceTransportOnShrink_local
    {H : Type v} [Group H]
    {ι κ : Type*}
    (ψ : ι → Rep (AlgebraicClosure K) H)
    [∀ i, FiniteDimensional (AlgebraicClosure K) (ψ i)]
    (π : κ → Rep (AlgebraicClosure K) H)
    [∀ q, FiniteDimensional (AlgebraicClosure K) (π q)]
    {c : ι → κ}
    (ePacket : ∀ i, (ψ i).ρ.Equiv (π (c i)).ρ)
    (f : ∀ i, Module.End (AlgebraicClosure K) (ψ i))
    (s : H) (i : ι) :
    LinearMap.trace (AlgebraicClosure K) (π (c i))
        ((π (c i)).ρ s⁻¹ * (ePacket i).toLinearEquiv.conj (f i)) =
      LinearMap.trace (AlgebraicClosure K) (ψ i)
        ((ψ i).ρ s⁻¹ * f i) := by
  -- Rewrite the transported trace term once through the chosen packet equivalence.
  simpa using
    StableLattice.representation_trace_action_conj_eq_local
      (e := ePacket i) (f := f i) s

/-- Helper for Proposition 16-16.4-1: after collapsing the supported complete-family coefficient
formula on `H`, transport each surviving trace term back across the chosen packet equivalence.
This isolates the executable coefficient rewrite that remains before the ambient packet/action
reassembly in the characteristic-zero branch. -/
lemma charZeroSupportedFamilyCoeffTransportOnShrink_local
    {H : Type v} [Group H] [Finite H]
    [Invertible (Nat.card H : AlgebraicClosure K)]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (ψ : ι → Rep (AlgebraicClosure K) H)
    [∀ i, FiniteDimensional (AlgebraicClosure K) (ψ i)]
    (π : κ → Rep (AlgebraicClosure K) H)
    [∀ q, FiniteDimensional (AlgebraicClosure K) (π q)]
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : Representation.IsCompleteIrreducibleFamily fun q ↦ FDRep.of (π q).ρ)
    {c : ι → κ} (hc : Function.Injective c)
    (ePacket : ∀ i, (ψ i).ρ.Equiv (π (c i)).ρ)
    (f : ∀ i, Module.End (AlgebraicClosure K) (ψ i))
    (s : H) :
    ((Representation.irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete).symm
        (StableLattice.charZero_supported_family_local (π := π) c hc
          (fun i ↦ (ePacket i).toLinearEquiv.conj (f i)))) s =
      (Nat.card H : AlgebraicClosure K)⁻¹ *
        ∑ i : ι, (Module.finrank (AlgebraicClosure K) (ψ i) : AlgebraicClosure K) *
          LinearMap.trace (AlgebraicClosure K) (ψ i) ((ψ i).ρ s⁻¹ * f i) := by
  -- First collapse the supported complete-family coefficient to the packet image.
  calc
    ((Representation.irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete).symm
        (StableLattice.charZero_supported_family_local (π := π) c hc
          (fun i ↦ (ePacket i).toLinearEquiv.conj (f i)))) s =
      (Nat.card H : AlgebraicClosure K)⁻¹ *
        ∑ i : ι, (Module.finrank (AlgebraicClosure K) (π (c i)) : AlgebraicClosure K) *
          LinearMap.trace (AlgebraicClosure K) (π (c i))
            ((π (c i)).ρ s⁻¹ * (ePacket i).toLinearEquiv.conj (f i)) := by
          simpa using
            StableLattice.charZeroSupportedFamilyCoeffCollapseOnShrink_local
              (π := π) hπ_pairwise hπ_complete (hc := hc)
              (f := fun i ↦ (ePacket i).toLinearEquiv.conj (f i)) s
    _ =
      (Nat.card H : AlgebraicClosure K)⁻¹ *
        ∑ i : ι, (Module.finrank (AlgebraicClosure K) (ψ i) : AlgebraicClosure K) *
          LinearMap.trace (AlgebraicClosure K) (ψ i) ((ψ i).ρ s⁻¹ * f i) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [StableLattice.packetEquivTraceTransportOnShrink_local
            (ψ := ψ) (π := π) (ePacket := ePacket) (f := f) s i]
          congr 1
          simpa using
            congrArg (fun n : ℕ ↦ (n : AlgebraicClosure K))
              ((ePacket i).toLinearEquiv.finrank_eq.symm)

/-- Helper for Proposition 16-16.4-1: after extending the transported packet endomorphisms by
zero away from `Finset.univ.image c`, the inverse Wedderburn preimage acts on the complete-family
coordinate `c i` by the transported packet endomorphism itself. This isolates the executable
coordinate-action half of the remaining characteristic-zero packet comparison. -/
lemma charZeroPacketSupportedCoordinateActionOnShrink_local
    {H : Type v} [Group H] [Finite H]
    [Invertible (Nat.card H : AlgebraicClosure K)]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (ψ : ι → Rep (AlgebraicClosure K) H)
    [∀ i, FiniteDimensional (AlgebraicClosure K) (ψ i)]
    (π : κ → Rep (AlgebraicClosure K) H)
    [∀ q, FiniteDimensional (AlgebraicClosure K) (π q)]
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : Representation.IsCompleteIrreducibleFamily fun q ↦ FDRep.of (π q).ρ)
    {c : ι → κ} (hc : Function.Injective c)
    (ePacket : ∀ i, (ψ i).ρ.Equiv (π (c i)).ρ)
    (f : ∀ i, Module.End (AlgebraicClosure K) (ψ i))
    (i : ι) :
    (Representation.irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete)
        ((Representation.irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete).symm
          (StableLattice.charZero_supported_family_local (π := π) c hc
            (fun i ↦ (ePacket i).toLinearEquiv.conj (f i)))) (c i) =
      (ePacket i).toLinearEquiv.conj (f i) := by
  -- On the support point `c i`, the supported family already is the transported packet datum.
  simpa using
    StableLattice.charZero_supported_family_local_apply
      (π := π) (hc := hc)
      (f := fun i ↦ (ePacket i).toLinearEquiv.conj (f i)) i

/-- Helper for Proposition 16-16.4-1: once the supported complete-family preimage is read at the
packet coordinate `c i`, transporting that coordinate action back through `ePacket i` recovers the
original packet endomorphism `f i`. This isolates the packet-side action normalization needed
before comparing the supported family with the scalar-extended ambient endomorphism. -/
lemma charZeroPacketSupportedCoordinateActionTransportBackOnShrink_local
    {H : Type v} [Group H] [Finite H]
    [Invertible (Nat.card H : AlgebraicClosure K)]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (ψ : ι → Rep (AlgebraicClosure K) H)
    [∀ i, FiniteDimensional (AlgebraicClosure K) (ψ i)]
    (π : κ → Rep (AlgebraicClosure K) H)
    [∀ q, FiniteDimensional (AlgebraicClosure K) (π q)]
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : Representation.IsCompleteIrreducibleFamily fun q ↦ FDRep.of (π q).ρ)
    {c : ι → κ} (hc : Function.Injective c)
    (ePacket : ∀ i, (ψ i).ρ.Equiv (π (c i)).ρ)
    (f : ∀ i, Module.End (AlgebraicClosure K) (ψ i))
    (i : ι) :
    (ePacket i).toLinearEquiv.symm.conj
        ((Representation.irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete)
            ((Representation.irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete).symm
              (StableLattice.charZero_supported_family_local (π := π) c hc
                (fun i ↦ (ePacket i).toLinearEquiv.conj (f i)))) (c i)) =
      f i := by
  -- First read the supported complete-family action at the packet coordinate `c i`.
  have hcoord :=
    StableLattice.charZeroPacketSupportedCoordinateActionOnShrink_local
      (ψ := ψ) (π := π) hπ_pairwise hπ_complete (hc := hc) (ePacket := ePacket) (f := f) i
  -- Then transport that coordinate action back across `ePacket i`.
  simpa [LinearEquiv.conj_apply_apply] using
    congrArg ((ePacket i).toLinearEquiv.symm.conj) hcoord


end DefectZero

end StableLattice

end
