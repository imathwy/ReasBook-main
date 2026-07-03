import Mathlib
import LinearRepresentations_Serre_1977.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Chap06.Exercise_6_6_3_3
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.CharacterBasisCoefficients
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.ComplexMinimalRealization
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.ExternalTensorUniverseBridge
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.FieldDenominatorDescent
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.FieldDenominatorPrelude
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.FieldTensorCenterBridge
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.PacketCenterDescentCore
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.PacketTransport
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.ScalarExtensionConstituents
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.ScalarExtensionPackets
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.ScalarExtensionPairing
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_2
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_2_1

noncomputable section

open scoped BigOperators
open scoped Representation

universe u v

namespace Representation

open CategoryTheory

namespace Exercise_12_12_2_6

section FieldPart

variable {G : Type u} [Group G] [Finite G]

local instance instFintypeGExercise_12_12_2_6_scalar_extension_block_projectors : Fintype G :=
  Fintype.ofFinite G

/-- Helper for Exercise 12-12.2-6: the local primitive-idempotent coefficient formula is exactly
the coefficient function of Chapter 6's `characterCentralElement`. -/
theorem primitive_central_idempotent_coefficient_eq_characterCentralElement_coeff_local
    {K' : Type v} [Field K'] [CharZero K']
    (V : Rep.{max u v} (AlgebraicClosure K') G)
    [FiniteDimensional (AlgebraicClosure K') V]
    (g : G) :
    (((((Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') / Nat.card G) •
        ∑ s : G, V.ρ.character s⁻¹ • MonoidAlgebra.of (AlgebraicClosure K') G s) :
        MonoidAlgebra (AlgebraicClosure K') G) g) =
      primitive_central_idempotent_coefficient_packet_local (G := G) (V := V) g := by
  have hcoeff :
      ((∑ s : G, V.ρ.character s⁻¹ • MonoidAlgebra.of (AlgebraicClosure K') G s :
          MonoidAlgebra (AlgebraicClosure K') G) g) =
        V.ρ.character g⁻¹ := by
    classical
    -- Evaluate the coefficient of the group-algebra basis expansion at `g`.
    calc
      ((∑ s : G, V.ρ.character s⁻¹ • MonoidAlgebra.of (AlgebraicClosure K') G s :
          MonoidAlgebra (AlgebraicClosure K') G) g)
          =
        ∑ s : G,
          ((V.ρ.character s⁻¹ • MonoidAlgebra.of (AlgebraicClosure K') G s :
              MonoidAlgebra (AlgebraicClosure K') G) g) := by
            exact
              Finsupp.finset_sum_apply Finset.univ
                (fun s : G ↦
                  V.ρ.character s⁻¹ • MonoidAlgebra.of (AlgebraicClosure K') G s) g
      _ = V.ρ.character g⁻¹ := by
            rw [Finset.sum_eq_single g]
            · simp [MonoidAlgebra.of]
            · intro s hs hsg
              simp [MonoidAlgebra.of, hsg]
            · intro hg
              simp at hg
  -- Rewrite the coefficient first, then identify the result with the explicit packet formula.
  calc
    (((((Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') / Nat.card G) •
        ∑ s : G, V.ρ.character s⁻¹ • MonoidAlgebra.of (AlgebraicClosure K') G s) :
        MonoidAlgebra (AlgebraicClosure K') G) g)
        =
      (((Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') / Nat.card G) :
          AlgebraicClosure K') *
        ((∑ s : G, V.ρ.character s⁻¹ • MonoidAlgebra.of (AlgebraicClosure K') G s :
            MonoidAlgebra (AlgebraicClosure K') G) g) := by
          simp
    _ =
      (((Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') / Nat.card G) :
          AlgebraicClosure K') *
        V.ρ.character g⁻¹ := by rw [hcoeff]
    _ = primitive_central_idempotent_coefficient_packet_local (G := G) (V := V) g := by
          rfl

/-- Helper for Exercise 12-12.2-6: scalar extension carries the group-algebra action to the
coefficientwise image of the source action. -/
theorem scalar_extension_asAlgebraHom_mapRingHom_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    (x : MonoidAlgebra K' G) :
    (Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ).asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) x) =
      LinearMap.baseChange (AlgebraicClosure K') (ρ.ρ.asAlgebraHom x) := by
  -- Route correction: compare scalar extension and base change on monoid-algebra generators, then
  -- extend linearly over the group algebra.
  refine MonoidAlgebra.induction_on
    (p := fun y : MonoidAlgebra K' G ↦
      (Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ).asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) y) =
        LinearMap.baseChange (AlgebraicClosure K') (ρ.ρ.asAlgebraHom y))
    x ?_ ?_ ?_
  · intro g
    -- On group elements, scalar extension is definitionally the base-changed group action.
    simp [MonoidAlgebra.of, Representation.scalarExtension]
    rfl
  · intro a b ha hb
    -- Both sides are additive in the group-algebra input.
    simp [ha, hb]
  · intro r a ha
    -- Scalar coefficients commute with `mapRingHom` and with `LinearMap.baseChange`.
    have hmap :
        MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) (r • a) =
          (algebraMap K' (AlgebraicClosure K')) r •
            MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) a := by
      ext g
      simp [MonoidAlgebra.mapRingHom_apply, Algebra.smul_def]
    rw [hmap, AlgHom.map_smul_of_tower, ha]
    simpa using
      (LinearMap.baseChange_smul
        (S := AlgebraicClosure K') (f := ρ.ρ.asAlgebraHom a) r).symm

/-- Helper for Exercise 12-12.2-6: pairwise nonisomorphic packet constituents are determined by
their characters after transport. -/
theorem transported_packet_index_eq_local
    {K' : Type v} [Field K'] [CharZero K']
    {ι : Type*}
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    {i j : ι}
    (hchar :
      ∀ g : G,
        (ψ i).ρ.character g = (ψ j).ρ.character g) :
    i = j := by
  classical
  by_contra hij
  letI : (ψ i).ρ.IsIrreducible := hψ_irr i
  letI : (ψ j).ρ.IsIrreducible := hψ_irr j
  have hself :
      ⟪(ψ i).ρ.character, (ψ i).ρ.character⟫ = (1 : AlgebraicClosure K') := by
    simpa using
      transported_irreducible_character_self_pairing_eq_one_local
        (G := G) (ψ0 := ψ i)
        (σ := (AlgEquiv.refl :
          (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')))
  have hpair_eq_one :
      ⟪(ψ i).ρ.character, (ψ j).ρ.character⟫ = (1 : AlgebraicClosure K') := by
    have hchar_eq : (ψ i).ρ.character = (ψ j).ρ.character := funext hchar
    rw [← hchar_eq]
    exact hself
  have hcard_ne : (Nat.card G : AlgebraicClosure K') ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : AlgebraicClosure K') := invertibleOfNonzero hcard_ne
  have hnot :
      ¬ Nonempty ((ψ i).ρ.Equiv (ψ j).ρ) := by
    intro hIso
    apply hψ_pairwise hij
    rcases hIso with ⟨eIso⟩
    simpa using (show Nonempty (ψ i ≅ ψ j) from ⟨Rep.mkIso eIso⟩)
  have hpair_zero :
      ⟪(ψ i).ρ.character, (ψ j).ρ.character⟫ = (0 : AlgebraicClosure K') := by
    exact
      Representation.groupFunctionPairingOverField_character_eq_zero_of_not_isomorphic
        (K := AlgebraicClosure K') (G := G) (ρ := (ψ i).ρ) (σ := (ψ j).ρ) hnot
  exact one_ne_zero (hpair_eq_one.symm.trans hpair_zero)

/-- Helper for Exercise 12-12.2-6: a finite packet projector supported on a transport-stable
block has coefficients fixed by the corresponding automorphism subgroup, so it descends
coefficientwise to the fixed field. -/
theorem transport_orbit_projector_descends_local
    {K' : Type v} [Field K'] [CharZero K']
    {ι : Type*} [Fintype ι]
    (H : Subgroup ((AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')))
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i))
    (perm :
      ∀ σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K'), σ ∈ H → Equiv.Perm ι)
    (hchar :
      ∀ (σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')) (hσ : σ ∈ H)
        (i : ι) (g : G),
          σ ((ψ i).ρ.character g) = (ψ (perm σ hσ i)).ρ.character g)
    (O : Finset ι)
    (hstable :
      ∀ (σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')) (hσ : σ ∈ H) (i : ι),
        i ∈ O ↔ perm σ hσ i ∈ O) :
    ∃ p0 : MonoidAlgebra (IntermediateField.fixedField H) G,
      ∀ g : G,
        ((p0 g : IntermediateField.fixedField H) : AlgebraicClosure K') =
          Finset.sum O
            (fun i ↦
              primitive_central_idempotent_coefficient_packet_local (G := G) (V := ψ i) g) := by
  classical
  have hcoeff_fixed :
      ∀ (σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')) (hσ : σ ∈ H) (g : G),
        σ
            (Finset.sum O
              (fun i ↦
                primitive_central_idempotent_coefficient_packet_local
                  (G := G) (V := ψ i) g)) =
          Finset.sum O
            (fun i ↦
              primitive_central_idempotent_coefficient_packet_local
                (G := G) (V := ψ i) g) := by
    intro σ hσ g
    -- First transport each primitive idempotent coefficient along the chosen packet permutation.
    calc
      σ
          (Finset.sum O
            (fun i ↦
              primitive_central_idempotent_coefficient_packet_local
                (G := G) (V := ψ i) g))
          =
        Finset.sum O
          (fun i ↦
            σ
              (primitive_central_idempotent_coefficient_packet_local
                (G := G) (V := ψ i) g)) := by
              simp
      _ =
        Finset.sum O
          (fun i ↦
            primitive_central_idempotent_coefficient_packet_local
              (G := G) (V := ψ (perm σ hσ i)) g) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simpa using
                primitive_central_idempotent_coefficient_packet_aut_eq_of_character_transport_local
                  (G := G) (ψ := ψ) (hψ_fd := hψ_fd) (σ := σ) (τ := perm σ hσ)
                  (hchar := fun j g' ↦ hchar σ hσ j g') i g
      _ =
        Finset.sum O
          (fun i ↦
            primitive_central_idempotent_coefficient_packet_local
              (G := G) (V := ψ i) g) := by
              refine Finset.sum_bij (fun i _ ↦ perm σ hσ i) ?_ ?_ ?_ ?_
              · intro i hi
                exact (hstable σ hσ i).mp hi
              · intro i j hi hj hij
                exact (perm σ hσ).injective hij
              · intro j hj
                refine ⟨(perm σ hσ)⁻¹ j, ?_, by simp⟩
                exact (hstable σ hσ ((perm σ hσ)⁻¹ j)).2 (by simpa)
              · intro i hi
                rfl
  have hcoeff_mem :
      ∀ g : G,
        Finset.sum O
            (fun i ↦
              primitive_central_idempotent_coefficient_packet_local
                (G := G) (V := ψ i) g) ∈ IntermediateField.fixedField H := by
    intro g
    -- Fixed-field membership is exactly coefficientwise invariance under the stabilizer subgroup.
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    exact hcoeff_fixed σ hσ g
  let p0 : MonoidAlgebra (IntermediateField.fixedField H) G :=
    Finsupp.equivFunOnFinite.symm
      (fun g : G ↦
        ⟨Finset.sum O
            (fun i ↦
              primitive_central_idempotent_coefficient_packet_local
                (G := G) (V := ψ i) g),
          hcoeff_mem g⟩)
  -- The descended group-algebra element recovers the orbit-projector coefficients after coercion.
  refine ⟨p0, ?_⟩
  intro g
  rfl

/-- Helper for Exercise 12-12.2-6: every algebraic-closure automorphism of the scaled packet
comes with an honest packet permutation, and the scaled packet keeps the quotient coefficients
unchanged along that permutation. -/
theorem packet_transport_with_coeff_invariance_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [FiniteDimensional K' ρ]
    (n : ℕ+)
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (d e : ι → ℕ)
    (hd_pos : ∀ i, 0 < d i)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (he : ∀ i, d i = (n : ℕ) * e i)
    (hscaled_packet :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) =
        ∑ i, (e i : AlgebraicClosure K') • (ψ i).ρ.character)
    (σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')) :
    ∃ τ : Equiv.Perm ι,
      (∀ i : ι, ∀ g : G, σ ((ψ i).ρ.character g) = (ψ (τ i)).ρ.character g) ∧
      (∀ i, e (τ i) = e i) := by
  obtain ⟨τ, hchar⟩ :=
    packet_transport_perm_exists_local
      (G := G) (ρ := ρ) (n := n) (ψ := ψ) (d := d) (e := e)
      hd_pos hψ_fd hψ_pairwise hψ_irr he hscaled_packet σ
  refine ⟨τ, hchar, ?_⟩
  -- Once the packet transport is realized by a permutation, the scaled packet identity forces
  -- the quotient coefficient to stay unchanged on that transported constituent.
  exact
    scaled_packet_coeff_transport_invariant_local
      (G := G) (ρ := ρ) (n := n) (ψ := ψ) (e := e)
      hψ_fd hψ_pairwise hψ_irr hscaled_packet σ τ hchar

/-- Helper for Exercise 12-12.2-6: two packet constituents connected by one algebraic-closure
transport already have the same quotient coefficient in the scaled visible packet. -/
theorem scaled_packet_coeff_eq_of_transport_relation_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [FiniteDimensional K' ρ]
    (n : ℕ+)
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (d e : ι → ℕ)
    (_hd_pos : ∀ i, 0 < d i)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (_he : ∀ i, d i = (n : ℕ) * e i)
    (hscaled_packet :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) =
        ∑ i, (e i : AlgebraicClosure K') • (ψ i).ρ.character)
    {i j : ι}
    (htransport :
      ∃ (σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')) (τ : Equiv.Perm ι),
        (∀ k : ι, ∀ g : G, σ ((ψ k).ρ.character g) = (ψ (τ k)).ρ.character g) ∧
        τ i = j) :
    e j = e i := by
  rcases htransport with ⟨σ, τ, hchar, hij⟩
  -- Rewrite the target constituent as the transported image of `i`, then apply the transport
  -- invariance of the scaled packet coefficients.
  simpa [hij] using
    scaled_packet_coeff_transport_invariant_local
      (G := G) (ρ := ρ) (n := n) (ψ := ψ) (e := e)
      hψ_fd hψ_pairwise hψ_irr hscaled_packet σ τ hchar i

/-- Helper for Exercise 12-12.2-6: once one base packet constituent reaches every other
constituent by a single transport, the quotient coefficients in the scaled packet are already
constant. -/
theorem common_coeff_of_full_transport_image_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [FiniteDimensional K' ρ]
    (n : ℕ+)
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (d e : ι → ℕ)
    (hd_pos : ∀ i, 0 < d i)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (he : ∀ i, d i = (n : ℕ) * e i)
    (hscaled_packet :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) =
        ∑ i, (e i : AlgebraicClosure K') • (ψ i).ρ.character)
    (i0 : ι)
    (hcover :
      ∀ j : ι,
        ∃ (σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')) (τ : Equiv.Perm ι),
          (∀ k : ι, ∀ g : G, σ ((ψ k).ρ.character g) = (ψ (τ k)).ρ.character g) ∧
          τ i0 = j) :
    ∀ i j, e i = e j := by
  intro i j
  have hi : e i = e i0 := by
    -- The existing transport-coefficient lemma applies directly to the chosen transport from the
    -- base index `i0` to `i`.
    exact
      scaled_packet_coeff_eq_of_transport_relation_local
        (G := G) (ρ := ρ) (n := n) (ψ := ψ) (d := d) (e := e)
        hd_pos hψ_fd hψ_pairwise hψ_irr he hscaled_packet
        (i := i0) (j := i) (htransport := hcover i)
  have hj : e j = e i0 := by
    -- The same argument reaches `j`, so both coefficients agree with the base coefficient.
    exact
      scaled_packet_coeff_eq_of_transport_relation_local
        (G := G) (ρ := ρ) (n := n) (ψ := ψ) (d := d) (e := e)
        hd_pos hψ_fd hψ_pairwise hψ_irr he hscaled_packet
        (i := i0) (j := j) (htransport := hcover j)
  exact hi.trans hj.symm

/-- Helper for Exercise 12-12.2-6: the identity automorphism already gives one transport witness,
so every chosen base constituent lies in its own transport-reachable packet orbit. -/
theorem packet_transport_reaches_self_local
    {K' : Type v} [Field K'] [CharZero K']
    {ι : Type*}
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (i0 : ι) :
    ∃ (σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')) (τ : Equiv.Perm ι),
      (∀ k : ι, ∀ g : G, σ ((ψ k).ρ.character g) = (ψ (τ k)).ρ.character g) ∧
      τ i0 = i0 := by
  -- The base-field identity automorphism and the identity packet permutation realize the trivial
  -- transport from `i0` back to itself.
  refine
    ⟨(AlgEquiv.refl : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')),
      (1 : Equiv.Perm ι), ?_, ?_⟩
  · intro k g
    rfl
  · rfl

/-- Helper for Exercise 12-12.2-6: packet-transport witnesses compose, so transport reachability
is transitive along LinearRepresentations_Serre_1977's visible packet. -/
private theorem packet_transport_relation_comp_local
    {K' : Type v} [Field K'] [CharZero K']
    {ι : Type*}
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    {i j k : ι}
    (hij :
      ∃ (σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')) (τ : Equiv.Perm ι),
        (∀ l : ι, ∀ g : G, σ ((ψ l).ρ.character g) = (ψ (τ l)).ρ.character g) ∧
        τ i = j)
    (hjk :
      ∃ (σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')) (τ : Equiv.Perm ι),
        (∀ l : ι, ∀ g : G, σ ((ψ l).ρ.character g) = (ψ (τ l)).ρ.character g) ∧
        τ j = k) :
    ∃ (σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')) (τ : Equiv.Perm ι),
      (∀ l : ι, ∀ g : G, σ ((ψ l).ρ.character g) = (ψ (τ l)).ρ.character g) ∧
      τ i = k := by
  rcases hij with ⟨σ₁, τ₁, hchar₁, hij⟩
  rcases hjk with ⟨σ₂, τ₂, hchar₂, hjk⟩
  refine ⟨σ₁.trans σ₂, τ₁.trans τ₂, ?_, by simp [hij, hjk]⟩
  intro l g
  -- Apply the first transport and then the second one on the transported constituent.
  calc
    (σ₁.trans σ₂) ((ψ l).ρ.character g)
        = σ₂ (σ₁ ((ψ l).ρ.character g)) := rfl
    _ = σ₂ ((ψ (τ₁ l)).ρ.character g) := by rw [hchar₁ l g]
    _ = (ψ (τ₂ (τ₁ l))).ρ.character g := by rw [hchar₂ (τ₁ l) g]
    _ = (ψ ((τ₁.trans τ₂) l)).ρ.character g := rfl

/-- Helper for Exercise 12-12.2-6: inverting a packet transport inverts both the
algebraic-closure automorphism and the packet permutation. -/
private theorem packet_transport_relation_symm_local
    {K' : Type v} [Field K'] [CharZero K']
    {ι : Type*}
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    {i j : ι}
    (hij :
      ∃ (σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')) (τ : Equiv.Perm ι),
        (∀ l : ι, ∀ g : G, σ ((ψ l).ρ.character g) = (ψ (τ l)).ρ.character g) ∧
        τ i = j) :
    ∃ (σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')) (τ : Equiv.Perm ι),
      (∀ l : ι, ∀ g : G, σ ((ψ l).ρ.character g) = (ψ (τ l)).ρ.character g) ∧
      τ j = i := by
  rcases hij with ⟨σ, τ, hchar, hij⟩
  refine ⟨σ.symm, τ.symm, ?_, ?_⟩
  · intro l g
    -- Apply the inverse automorphism to the original transport identity on `τ.symm l`.
    have htransport' :
        σ.symm ((ψ (τ (τ.symm l))).ρ.character g) =
          (ψ (τ.symm l)).ρ.character g := by
      simpa using (congrArg σ.symm (hchar (τ.symm l) g)).symm
    calc
      σ.symm ((ψ l).ρ.character g) = σ.symm ((ψ (τ (τ.symm l))).ρ.character g) := by
        exact congrArg (fun m : ι ↦ σ.symm ((ψ m).ρ.character g))
          (τ.apply_symm_apply l).symm
      _ = (ψ (τ.symm l)).ρ.character g := htransport'
  · rw [← hij]
    simp

/-- Helper for Exercise 12-12.2-6: the transport orbit of a chosen base constituent is stable
under every further packet transport. -/
private theorem packet_transport_orbit_stable_of_transport_local
    {K' : Type v} [Field K'] [CharZero K']
    {ι : Type*}
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (i0 : ι)
    (O : Finset ι)
    (hmem_O :
      ∀ j : ι,
        j ∈ O ↔
          ∃ (σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')) (τ : Equiv.Perm ι),
            (∀ k : ι, ∀ g : G, σ ((ψ k).ρ.character g) = (ψ (τ k)).ρ.character g) ∧
            τ i0 = j)
    {σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')}
    {τ : Equiv.Perm ι}
    (hchar : ∀ k : ι, ∀ g : G, σ ((ψ k).ρ.character g) = (ψ (τ k)).ρ.character g) :
    ∀ j : ι, j ∈ O ↔ τ j ∈ O := by
  intro j
  constructor
  · intro hj
    have hreach_j : ∃ (σ' : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')) (τ' : Equiv.Perm ι),
        (∀ k : ι, ∀ g : G, σ' ((ψ k).ρ.character g) = (ψ (τ' k)).ρ.character g) ∧
        τ' i0 = j := (hmem_O j).mp hj
    -- Compose the existing path from `i0` to `j` with the current transport from `j` to `τ j`.
    exact
      (hmem_O (τ j)).2 <|
        packet_transport_relation_comp_local
          (G := G) (ψ := ψ) hreach_j
          ⟨σ, τ, hchar, rfl⟩
  · intro hτj
    have hreach_τj :
        ∃ (σ' : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')) (τ' : Equiv.Perm ι),
          (∀ k : ι, ∀ g : G, σ' ((ψ k).ρ.character g) = (ψ (τ' k)).ρ.character g) ∧
          τ' i0 = τ j := (hmem_O (τ j)).mp hτj
    have hback :
        ∃ (σ' : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')) (τ' : Equiv.Perm ι),
          (∀ k : ι, ∀ g : G, σ' ((ψ k).ρ.character g) = (ψ (τ' k)).ρ.character g) ∧
          τ' (τ j) = j := by
      exact
        packet_transport_relation_symm_local
          (G := G) (ψ := ψ) (i := j) (j := τ j) ⟨σ, τ, hchar, rfl⟩
    -- The inverse transport brings `τ j` back to `j`, so orbit membership is equivalent.
    exact
      (hmem_O j).2 <|
        packet_transport_relation_comp_local
          (G := G) (ψ := ψ) hreach_τj hback

/-- Helper for Exercise 12-12.2-6: descending a Galois-orbit projector from the scalar-extension
packet should force the visible quotient coefficients to be constant. -/
theorem orbit_block_projector_descends_to_source_forces_common_coeff_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [ρ.ρ.IsIrreducible]
    [FiniteDimensional K' ρ]
    (n : ℕ+)
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (d e : ι → ℕ)
    (hd_pos : ∀ i, 0 < d i)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (hpacket :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character =
        ∑ i, (d i : AlgebraicClosure K') • (ψ i).ρ.character)
    (he : ∀ i, d i = (n : ℕ) * e i)
    (hscaled_packet :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) =
        ∑ i, (e i : AlgebraicClosure K') • (ψ i).ρ.character) :
    ∀ i j, e i = e j := by
  sorry

/-- Helper for Exercise 12-12.2-6: after the quotient coefficients collapse to `1`, descending a
single isotypic block to the stabilizer fixed field should force each constituent degree to be a
multiple of the canonical denominator. -/
theorem isotypic_block_projector_descends_to_stabilizer_forces_degree_multiple_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [ρ.ρ.IsIrreducible]
    [FiniteDimensional K' ρ]
    (n : ℕ+)
    (hcanon : ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) ∈ R̄[K'](G))
    (hmax :
      ∀ d : ℕ+, ((((d : ℕ) : K')⁻¹) • ρ.ρ.character) ∈ R̄[K'](G) → d ≤ n)
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (d e : ι → ℕ)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (hpacket :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character =
        ∑ i, (d i : AlgebraicClosure K') • (ψ i).ρ.character)
    (he : ∀ i, d i = (n : ℕ) * e i)
    (hscaled_packet :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) =
        ∑ i, (e i : AlgebraicClosure K') • (ψ i).ρ.character)
    (hcoeff_one : ∀ i, e i = 1) :
    ∀ i, (n : ℕ) ∣ Module.finrank (AlgebraicClosure K') (ψ i) := by
  sorry

end FieldPart

end Exercise_12_12_2_6

end Representation
