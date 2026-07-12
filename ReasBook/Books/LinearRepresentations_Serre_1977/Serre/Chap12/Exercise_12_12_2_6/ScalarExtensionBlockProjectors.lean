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
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.PacketOrbitProjectors
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

/-- Helper for Exercise 12-12.2-6: Serre's explicit primitive-central-idempotent formula is
still central when the coefficient field and the group live in different universes. -/
private theorem primitiveCentralElement_mem_center_universe_local
    {K' : Type v} [Field K'] [CharZero K']
    (V : Rep.{max u v} (AlgebraicClosure K') G)
    [FiniteDimensional (AlgebraicClosure K') V] :
    (((Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') / Nat.card G) •
        ∑ s : G, V.ρ.character s⁻¹ • MonoidAlgebra.of (AlgebraicClosure K') G s) ∈
      Subalgebra.center (AlgebraicClosure K') (MonoidAlgebra (AlgebraicClosure K') G) := by
  let f : G → AlgebraicClosure K' := fun s ↦
    ((Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') / Nat.card G) *
      V.ρ.character s⁻¹
  have hf : IsClassFunction f := by
    refine ⟨?_⟩
    intro a b hab
    rcases isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hab) with ⟨g, hg⟩
    -- The inverse character stays constant on conjugacy classes, so Serre's coefficient formula
    -- does too.
    calc
      ((Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') / Nat.card G) *
          V.ρ.character a⁻¹
        =
      ((Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') / Nat.card G) *
          V.ρ.character (g * a⁻¹ * g⁻¹) := by
            rw [(V.ρ.char_conj a⁻¹ g).symm]
      _ =
      ((Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') / Nat.card G) *
          V.ρ.character b⁻¹ := by
            have hinv : g * a⁻¹ * g⁻¹ = b⁻¹ := by
              rw [← hg]
              simp [mul_assoc]
            simp [hinv]
  set z : MonoidAlgebra (AlgebraicClosure K') G := Finsupp.equivFunOnFinite.symm f
  have hcoeff :
      z =
        ((Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') / Nat.card G) •
          ∑ s : G, V.ρ.character s⁻¹ • MonoidAlgebra.of (AlgebraicClosure K') G s := by
    calc
      z
          = ∑ s : G,
              ((((Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') /
                    Nat.card G) * V.ρ.character s⁻¹) •
                  MonoidAlgebra.of (AlgebraicClosure K') G s) := by
                simpa [z, MonoidAlgebra.of, f] using
                  (Finsupp.equivFunOnFinite_symm_eq_sum f)
      _ =
          ((Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') / Nat.card G) •
            ∑ s : G, V.ρ.character s⁻¹ • MonoidAlgebra.of (AlgebraicClosure K') G s := by
              rw [Finset.smul_sum]
              refine Finset.sum_congr rfl ?_
              intro s hs
              simp [mul_smul]
  have hz :
      z ∈ Subalgebra.center (AlgebraicClosure K') (MonoidAlgebra (AlgebraicClosure K') G) := by
    have hzsub : z ∈ Subsemiring.center (MonoidAlgebra (AlgebraicClosure K') G) := by
      rw [Subsemiring.mem_center_iff]
      intro y
      ext h
      rw [MonoidAlgebra.mul_apply_left, MonoidAlgebra.mul_apply_right]
      rw [Finsupp.sum, Finsupp.sum]
      refine Finset.sum_congr rfl ?_
      intro a ha
      have hcomm : f (a⁻¹ * h) = f (h * a⁻¹) := by
        have hmk : ConjClasses.mk (a⁻¹ * h) = ConjClasses.mk (h * a⁻¹) := by
          exact ConjClasses.mk_eq_mk_iff_isConj.mpr <|
            isConj_iff.mpr ⟨h, by simp [mul_assoc]⟩
        exact hf.factorsThrough hmk
      -- Class-function coefficients commute with every basis element of the group algebra.
      simpa [mul_comm] using congrArg (fun t : AlgebraicClosure K' ↦ y a * t) hcomm
    simpa using hzsub
  simpa [hcoeff] using hz

/-- Helper for Exercise 12-12.2-6: package the universe-polymorphic primitive central element as
an honest central group-algebra element for later source-action arguments. -/
private def primitiveCentralElement_center_universe_local
    {K' : Type v} [Field K'] [CharZero K']
    (V : Rep.{max u v} (AlgebraicClosure K') G)
    [FiniteDimensional (AlgebraicClosure K') V] :
    Subalgebra.center (AlgebraicClosure K') (MonoidAlgebra (AlgebraicClosure K') G) :=
  ⟨(((Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') / Nat.card G) •
      ∑ s : G, V.ρ.character s⁻¹ • MonoidAlgebra.of (AlgebraicClosure K') G s),
    primitiveCentralElement_mem_center_universe_local (G := G) V⟩

/-- Helper for Exercise 12-12.2-6: an irreducible algebraic-closure representation has nonzero
degree, so its degree is invertible in the coefficient field. -/
private theorem irreducible_rep_finrank_ne_zero_universe_local
    {K' : Type v} [Field K'] [CharZero K']
    (V : Rep.{max u v} (AlgebraicClosure K') G)
    [FiniteDimensional (AlgebraicClosure K') V]
    (hV : V.ρ.IsIrreducible) :
    (Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') ≠ 0 := by
  letI : V.ρ.IsIrreducible := hV
  have hV_nontriv : Nontrivial V := by
    -- An irreducible representation cannot have the zero carrier, or else `⊥ = ⊤`.
    by_contra hV_trivial
    letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV_trivial
    have hbot : (⊥ : Subrepresentation V.ρ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      ext x
      constructor
      · intro _
        trivial
      · intro _
        simpa using (Subsingleton.elim x 0)
    exact bot_ne_top hbot
  exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Module.finrank_pos_iff.mpr hV_nontriv))

/-- Helper for Exercise 12-12.2-6: Serre's explicit primitive central element has central
character `1` on the irreducible constituent that defines it, even when the field and group live
in different universes. -/
private theorem primitiveCentralElement_centralCharacter_eq_one_universe_local
    {K' : Type v} [Field K'] [CharZero K']
    (V : Rep.{max u v} (AlgebraicClosure K') G)
    [FiniteDimensional (AlgebraicClosure K') V]
    (hV : V.ρ.IsIrreducible) :
    ω[V.ρ] (primitiveCentralElement_center_universe_local (G := G) V) = 1 := by
  have hcard_ne : (Nat.card G : AlgebraicClosure K') ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hfcard_ne : (Fintype.card G : AlgebraicClosure K') ≠ 0 := by
    simpa [Nat.card_eq_fintype_card] using hcard_ne
  letI : Invertible (Nat.card G : AlgebraicClosure K') := invertibleOfNonzero hcard_ne
  have hfinrank_ne :
      (Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') ≠ 0 := by
    exact irreducible_rep_finrank_ne_zero_universe_local (G := G) V hV
  have hpair :
      Representation.groupFunctionPairingOverField (AlgebraicClosure K')
          V.ρ.character V.ρ.character = 1 := by
    -- The self-pairing of an irreducible character is `1`.
    simpa using
      transported_irreducible_character_self_pairing_eq_one_local
        (G := G) (ψ0 := V)
        (σ := (AlgEquiv.refl :
          (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')))
  -- Route correction: compute the central character of the explicit projector directly from the
  -- normalized trace formula, instead of transporting the Chapter 6 same-universe theorem.
  rw [Representation.centralCharacter_apply_eq_sum_character
    (ρ := V.ρ) (u := primitiveCentralElement_center_universe_local (G := G) V) hfinrank_ne]
  calc
    (Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K')⁻¹ *
        ∑ s : G,
          ((primitiveCentralElement_center_universe_local (G := G) V :
              MonoidAlgebra (AlgebraicClosure K') G) s) *
            V.ρ.character s
      =
        (Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K')⁻¹ *
          ∑ s : G,
            ((((Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') /
                Nat.card G) *
              V.ρ.character s⁻¹) *
              V.ρ.character s) := by
                -- Rewrite the projector coefficients one term at a time.
                refine congrArg ((Module.finrank (AlgebraicClosure K') V :
                  AlgebraicClosure K')⁻¹ * ·) ?_
                refine Finset.sum_congr rfl ?_
                intro s hs
                have hs_coeff :
                    ((primitiveCentralElement_center_universe_local (G := G) V :
                        MonoidAlgebra (AlgebraicClosure K') G) s) =
                      (((Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') /
                          Nat.card G) *
                        V.ρ.character s⁻¹) := by
                  simpa [primitiveCentralElement_center_universe_local,
                    primitive_central_idempotent_coefficient_packet_local] using
                    primitive_central_idempotent_coefficient_eq_characterCentralElement_coeff_local
                      (G := G) (V := V) s
                simp [hs_coeff]
    _ =
        (Nat.card G : AlgebraicClosure K')⁻¹ *
          ∑ s : G, V.ρ.character s⁻¹ * V.ρ.character s := by
            -- Pull the scalar degree factor out of the sum and cancel it against the trace
            -- normalization.
            calc
              (Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K')⁻¹ *
                  ∑ s : G,
                    ((((Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') /
                        Nat.card G) *
                      V.ρ.character s⁻¹) *
                      V.ρ.character s)
                =
                  (Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K')⁻¹ *
                    (((Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') /
                        Nat.card G) *
                      ∑ s : G, V.ρ.character s⁻¹ * V.ρ.character s) := by
                        congr 1
                        symm
                        rw [Finset.mul_sum]
                        refine Finset.sum_congr rfl ?_
                        intro s hs
                        ring
              _ =
                  (Nat.card G : AlgebraicClosure K')⁻¹ *
                    ∑ s : G, V.ρ.character s⁻¹ * V.ρ.character s := by
                      simp [div_eq_mul_inv, hfinrank_ne, mul_assoc, mul_left_comm, mul_comm]
    _ = 1 := by
      simpa [Representation.groupFunctionPairingOverField] using hpair

/-- Helper for Exercise 12-12.2-6: Serre's explicit primitive central element has central
character `0` on any nonisomorphic irreducible constituent, again without same-universe
restrictions. -/
private theorem primitiveCentralElement_centralCharacter_eq_zero_of_not_isomorphic_universe_local
    {K' : Type v} [Field K'] [CharZero K']
    (V W : Rep.{max u v} (AlgebraicClosure K') G)
    [FiniteDimensional (AlgebraicClosure K') V]
    [FiniteDimensional (AlgebraicClosure K') W]
    (hV : V.ρ.IsIrreducible)
    (hW : W.ρ.IsIrreducible)
    (hVW : ¬ Nonempty (V ≅ W)) :
    ω[W.ρ] (primitiveCentralElement_center_universe_local (G := G) V) = 0 := by
  have hcard_ne : (Nat.card G : AlgebraicClosure K') ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hfcard_ne : (Fintype.card G : AlgebraicClosure K') ≠ 0 := by
    simpa [Nat.card_eq_fintype_card] using hcard_ne
  letI : Invertible (Nat.card G : AlgebraicClosure K') := invertibleOfNonzero hcard_ne
  have hfinrankW_ne :
      (Module.finrank (AlgebraicClosure K') W : AlgebraicClosure K') ≠ 0 := by
    exact irreducible_rep_finrank_ne_zero_universe_local (G := G) W hW
  have hnot_equiv : ¬ Nonempty (V.ρ.Equiv W.ρ) := by
    intro hEquiv
    rcases hEquiv with ⟨e⟩
    exact hVW ⟨Rep.mkIso e⟩
  have hpair :
      Representation.groupFunctionPairingOverField (AlgebraicClosure K')
          V.ρ.character W.ρ.character = 0 := by
    -- Nonisomorphic irreducibles are orthogonal for the normalized pairing.
    exact
      Representation.groupFunctionPairingOverField_character_eq_zero_of_not_isomorphic
        (K := AlgebraicClosure K') (G := G) (ρ := V.ρ) (σ := W.ρ) hnot_equiv
  -- Route correction: the same normalized trace computation reduces the nonisomorphic case to
  -- the orthogonality of irreducible characters.
  rw [Representation.centralCharacter_apply_eq_sum_character
    (ρ := W.ρ) (u := primitiveCentralElement_center_universe_local (G := G) V) hfinrankW_ne]
  calc
    (Module.finrank (AlgebraicClosure K') W : AlgebraicClosure K')⁻¹ *
        ∑ s : G,
          ((primitiveCentralElement_center_universe_local (G := G) V :
              MonoidAlgebra (AlgebraicClosure K') G) s) *
            W.ρ.character s
      =
        (Module.finrank (AlgebraicClosure K') W : AlgebraicClosure K')⁻¹ *
          ∑ s : G,
            ((((Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') /
                Nat.card G) *
              V.ρ.character s⁻¹) *
              W.ρ.character s) := by
                -- Rewrite the projector coefficients one term at a time.
                refine congrArg ((Module.finrank (AlgebraicClosure K') W :
                  AlgebraicClosure K')⁻¹ * ·) ?_
                refine Finset.sum_congr rfl ?_
                intro s hs
                have hs_coeff :
                    ((primitiveCentralElement_center_universe_local (G := G) V :
                        MonoidAlgebra (AlgebraicClosure K') G) s) =
                      (((Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') /
                          Nat.card G) *
                        V.ρ.character s⁻¹) := by
                  simpa [primitiveCentralElement_center_universe_local,
                    primitive_central_idempotent_coefficient_packet_local] using
                    primitive_central_idempotent_coefficient_eq_characterCentralElement_coeff_local
                      (G := G) (V := V) s
                simp [hs_coeff]
    _ =
        ((Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') /
            (Module.finrank (AlgebraicClosure K') W : AlgebraicClosure K')) *
          Representation.groupFunctionPairingOverField (AlgebraicClosure K')
            V.ρ.character W.ρ.character := by
              -- Factor out the scalar degree ratio and identify the remaining normalized pairing.
              rw [Representation.groupFunctionPairingOverField, Nat.card_eq_fintype_card]
              calc
                (Module.finrank (AlgebraicClosure K') W : AlgebraicClosure K')⁻¹ *
                    ∑ s : G,
                      ((((Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') /
                          Fintype.card G) *
                        V.ρ.character s⁻¹) *
                        W.ρ.character s)
                  =
                    (Module.finrank (AlgebraicClosure K') W : AlgebraicClosure K')⁻¹ *
                      (((Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') /
                          Fintype.card G) *
                        ∑ s : G, V.ρ.character s⁻¹ * W.ρ.character s) := by
                          congr 1
                          symm
                          rw [Finset.mul_sum]
                          refine Finset.sum_congr rfl ?_
                          intro s hs
                          ring
                _ =
                    ((Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') /
                        (Module.finrank (AlgebraicClosure K') W : AlgebraicClosure K')) *
                      ((Fintype.card G : AlgebraicClosure K')⁻¹ *
                        ∑ s : G, V.ρ.character s⁻¹ * W.ρ.character s) := by
                          simp [div_eq_mul_inv, hfinrankW_ne, hfcard_ne, mul_assoc, mul_left_comm,
                            mul_comm]
    _ = 0 := by simp [hpair]

/-- Helper for Exercise 12-12.2-6: the universe-separated primitive central element acts as the
identity on its defining irreducible constituent. -/
private theorem primitiveCentralElement_action_eq_id_universe_local
    {K' : Type v} [Field K'] [CharZero K']
    (V : Rep.{max u v} (AlgebraicClosure K') G)
    [FiniteDimensional (AlgebraicClosure K') V]
    (hV : V.ρ.IsIrreducible) :
    V.ρ.asAlgebraHom (primitiveCentralElement_center_universe_local (G := G) V) = LinearMap.id := by
  -- Convert the explicit central character calculation into the corresponding scalar action.
  rw [Representation.asAlgebraHom_center_eq_centralCharacter_smul_id
    (ρ := V.ρ) (u := primitiveCentralElement_center_universe_local (G := G) V)]
  simp [primitiveCentralElement_centralCharacter_eq_one_universe_local (G := G) V hV]

/-- Helper for Exercise 12-12.2-6: the same explicit primitive central element acts by `0` on any
nonisomorphic irreducible constituent. -/
private theorem primitiveCentralElement_action_eq_zero_of_not_isomorphic_universe_local
    {K' : Type v} [Field K'] [CharZero K']
    (V W : Rep.{max u v} (AlgebraicClosure K') G)
    [FiniteDimensional (AlgebraicClosure K') V]
    [FiniteDimensional (AlgebraicClosure K') W]
    (hV : V.ρ.IsIrreducible)
    (hW : W.ρ.IsIrreducible)
    (hVW : ¬ Nonempty (V ≅ W)) :
    W.ρ.asAlgebraHom (primitiveCentralElement_center_universe_local (G := G) V) = 0 := by
  -- Convert the vanishing central character into the corresponding vanishing action.
  rw [Representation.asAlgebraHom_center_eq_centralCharacter_smul_id
    (ρ := W.ρ) (u := primitiveCentralElement_center_universe_local (G := G) V)]
  simp [primitiveCentralElement_centralCharacter_eq_zero_of_not_isomorphic_universe_local
    (G := G) V W hV hW hVW]

/-- Helper for Exercise 12-12.2-6: the orbit-sum projector acts by the identity on the unique
packet constituent indexed by a member of the orbit. -/
private theorem orbitProjector_sum_action_eq_id_local
    {K' : Type v} [Field K'] [CharZero K']
    {ι : Type*}
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (O : Finset ι)
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    {i0 : ι}
    (hi0_mem : i0 ∈ O) :
    (ψ i0).ρ.asAlgebraHom
        (Finset.sum O fun i ↦
          ((primitiveCentralElement_center_universe_local (G := G) (ψ i) :
            Subalgebra.center (AlgebraicClosure K') (MonoidAlgebra (AlgebraicClosure K') G)) :
            MonoidAlgebra (AlgebraicClosure K') G)) =
      LinearMap.id := by
  classical
  -- Evaluate the orbit sum term-by-term: only the `i0`-summand survives by pairwise
  -- nonisomorphism.
  have hsum_rw :
      (ψ i0).ρ.asAlgebraHom
          (Finset.sum O fun i ↦
            ((primitiveCentralElement_center_universe_local (G := G) (ψ i) :
              Subalgebra.center (AlgebraicClosure K') (MonoidAlgebra (AlgebraicClosure K') G)) :
              MonoidAlgebra (AlgebraicClosure K') G)) =
        Finset.sum O (fun i ↦
          (ψ i0).ρ.asAlgebraHom
            (((primitiveCentralElement_center_universe_local (G := G) (ψ i) :
              Subalgebra.center (AlgebraicClosure K') (MonoidAlgebra (AlgebraicClosure K') G)) :
              MonoidAlgebra (AlgebraicClosure K') G))) := by
    simpa using ((ψ i0).ρ.asAlgebraHom.map_sum
      (fun i ↦
        ((primitiveCentralElement_center_universe_local (G := G) (ψ i) :
          Subalgebra.center (AlgebraicClosure K') (MonoidAlgebra (AlgebraicClosure K') G)) :
          MonoidAlgebra (AlgebraicClosure K') G)) O)
  rw [hsum_rw]
  rw [Finset.sum_eq_single i0]
  · simpa using primitiveCentralElement_action_eq_id_universe_local
      (G := G) (V := ψ i0) (hψ_irr i0)
  · intro i hiO hii0
    have hnot : ¬ Nonempty (ψ i ≅ ψ i0) := by
      exact hψ_pairwise hii0
    simpa using
      primitiveCentralElement_action_eq_zero_of_not_isomorphic_universe_local
        (G := G) (V := ψ i) (W := ψ i0) (hψ_irr i) (hψ_irr i0) hnot
  · intro hi0_not_mem
    exact False.elim (hi0_not_mem hi0_mem)

/-- Helper for Exercise 12-12.2-6: the orbit-sum projector acts by zero on any packet constituent
outside the chosen orbit. -/
private theorem orbitProjector_sum_action_eq_zero_of_not_mem_local
    {K' : Type v} [Field K'] [CharZero K']
    {ι : Type*}
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (O : Finset ι)
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    {j : ι}
    (hj : j ∉ O) :
    (ψ j).ρ.asAlgebraHom
        (Finset.sum O fun i ↦
          ((primitiveCentralElement_center_universe_local (G := G) (ψ i) :
            Subalgebra.center (AlgebraicClosure K') (MonoidAlgebra (AlgebraicClosure K') G)) :
            MonoidAlgebra (AlgebraicClosure K') G)) =
      0 := by
  classical
  -- Every summand is orthogonal to the out-of-orbit constituent `ψ j`.
  have hsum_rw :
      (ψ j).ρ.asAlgebraHom
          (Finset.sum O fun i ↦
            ((primitiveCentralElement_center_universe_local (G := G) (ψ i) :
              Subalgebra.center (AlgebraicClosure K') (MonoidAlgebra (AlgebraicClosure K') G)) :
              MonoidAlgebra (AlgebraicClosure K') G)) =
        Finset.sum O (fun i ↦
          (ψ j).ρ.asAlgebraHom
            (((primitiveCentralElement_center_universe_local (G := G) (ψ i) :
              Subalgebra.center (AlgebraicClosure K') (MonoidAlgebra (AlgebraicClosure K') G)) :
              MonoidAlgebra (AlgebraicClosure K') G))) := by
    simpa using ((ψ j).ρ.asAlgebraHom.map_sum
      (fun i ↦
        ((primitiveCentralElement_center_universe_local (G := G) (ψ i) :
          Subalgebra.center (AlgebraicClosure K') (MonoidAlgebra (AlgebraicClosure K') G)) :
          MonoidAlgebra (AlgebraicClosure K') G)) O)
  rw [hsum_rw]
  refine Finset.sum_eq_zero ?_
  intro i hiO
  have hij : i ≠ j := by
    exact fun hij_eq ↦ hj (hij_eq ▸ hiO)
  have hnot : ¬ Nonempty (ψ i ≅ ψ j) := by
    exact hψ_pairwise hij
  simpa using
    primitiveCentralElement_action_eq_zero_of_not_isomorphic_universe_local
      (G := G) (V := ψ i) (W := ψ j) (hψ_irr i) (hψ_irr j) hnot

/-- Helper for Exercise 12-12.2-6: evaluating an honest isotypic-fiber character identity at `1`
turns it into the corresponding degree sum identity. -/
private theorem isotypic_fiber_degree_sum_from_character_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [FiniteDimensional K' ρ]
    {ι : Type*}
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (a : ℕ)
    (σ : Fin a → Subrepresentation
      (Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ))
    (S : ι → Finset (Fin a))
    (d : ι → ℕ)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i))
    (hfiber_char :
      ∀ i,
        Finset.sum
            (S i)
            (fun j ↦ ((σ j).toRepresentation).character) =
          (d i : AlgebraicClosure K') • (ψ i).ρ.character) :
    ∀ i,
      ((Finset.sum (S i)
          (fun j ↦ Module.finrank (AlgebraicClosure K') ↥((σ j).toSubmodule)) : ℕ) :
          AlgebraicClosure K') =
        (d i : AlgebraicClosure K') *
          (Module.finrank (AlgebraicClosure K') (ψ i) : AlgebraicClosure K') := by
  intro i
  letI : FiniteDimensional (AlgebraicClosure K') (ψ i) := hψ_fd i
  -- Evaluate the fiber character identity at the group identity to replace characters by degrees.
  simpa [Representation.char_one, smul_eq_mul] using congrFun (hfiber_char i) 1

/-- Helper for Exercise 12-12.2-6: every honest isotypic fiber is nonempty because its degree sum
is a positive multiple of the degree of an irreducible constituent. -/
private theorem isotypic_fiber_nonempty_of_positive_multiplicity_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [FiniteDimensional K' ρ]
    {ι : Type*}
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (a : ℕ)
    (σ : Fin a → Subrepresentation
      (Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ))
    (S : ι → Finset (Fin a))
    (d : ι → ℕ)
    (hd_pos : ∀ i, 0 < d i)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i))
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (hfiber_char :
      ∀ i,
        Finset.sum
            (S i)
            (fun j ↦ ((σ j).toRepresentation).character) =
          (d i : AlgebraicClosure K') • (ψ i).ρ.character) :
    ∀ i, (S i).Nonempty := by
  intro i
  letI : FiniteDimensional (AlgebraicClosure K') (ψ i) := hψ_fd i
  letI : (ψ i).ρ.IsIrreducible := hψ_irr i
  by_contra hSi_empty
  have hfiber_degree :=
    isotypic_fiber_degree_sum_from_character_local
      (G := G) (ρ := ρ) (ψ := ψ) (a := a) (σ := σ) (S := S) (d := d) hψ_fd hfiber_char i
  have hd_ne : (d i : AlgebraicClosure K') ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hd_pos i))
  have hdim_ne :
      (Module.finrank (AlgebraicClosure K') (ψ i) : AlgebraicClosure K') ≠ 0 := by
    have hψ_nontriv : Nontrivial (ψ i) := by
      -- An irreducible representation cannot have trivial carrier, or else `⊥ = ⊤`.
      by_contra hψ_trivial
      letI : Subsingleton (ψ i) := not_nontrivial_iff_subsingleton.mp hψ_trivial
      have hbot : (⊥ : Subrepresentation (ψ i).ρ) = ⊤ := by
        apply Subrepresentation.toSubmodule_injective
        ext x
        constructor
        · intro _
          trivial
        · intro _
          simpa using (Subsingleton.elim x 0)
      exact bot_ne_top hbot
    exact Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt (Module.finrank_pos_iff.mpr hψ_nontriv))
  have hfiber_degree_zero :
      (((Finset.sum (S i)
          (fun j ↦ Module.finrank (AlgebraicClosure K') ↥((σ j).toSubmodule)) : ℕ) :
          AlgebraicClosure K')) = 0 := by
    -- If the fiber were empty, its degree sum would vanish.
    simp [Finset.not_nonempty_iff_eq_empty.mp hSi_empty]
  have hmul_zero :
      (d i : AlgebraicClosure K') *
          (Module.finrank (AlgebraicClosure K') (ψ i) : AlgebraicClosure K') =
        0 := by
    -- Compare the positive target degree with the vanishing empty-fiber degree sum.
    exact hfiber_degree_zero ▸ hfiber_degree.symm
  exact (mul_ne_zero hd_ne hdim_ne) hmul_zero

/-- Helper for Exercise 12-12.2-6: Serre's visible scaled packet cannot be empty, because the
source character has nonzero value at `1`. -/
private theorem visible_scaled_packet_nonempty_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [ρ.ρ.IsIrreducible]
    [FiniteDimensional K' ρ]
    (n : ℕ+)
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (e : ι → ℕ)
    (hscaled_packet :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) =
        ∑ i, (e i : AlgebraicClosure K') • (ψ i).ρ.character) :
    Nonempty ι := by
  classical
  by_contra hι
  letI : IsEmpty ι := not_nonempty_iff.mp hι
  have hleft_ne_zero :
      (((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character)) 1 ≠ 0 := by
    have hn_ne : ((n : ℕ) : K') ≠ 0 := Nat.cast_ne_zero.mpr n.2.ne'
    have hρ_nontriv : Nontrivial ρ := by
      -- An irreducible representation cannot have trivial carrier, or else `⊥ = ⊤`.
      by_contra hρ_trivial
      letI : Subsingleton ρ := not_nontrivial_iff_subsingleton.mp hρ_trivial
      have hbot : (⊥ : Subrepresentation ρ.ρ) = ⊤ := by
        apply Subrepresentation.toSubmodule_injective
        ext x
        constructor
        · intro _
          trivial
        · intro _
          simpa using (Subsingleton.elim x 0)
      exact bot_ne_top hbot
    have hdim_pos : 0 < Module.finrank K' ρ := by
      simpa using (Module.finrank_pos_iff.mpr hρ_nontriv)
    have hdim_ne : (Module.finrank K' ρ : K') ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hdim_pos)
    have hleft_ne_zero_K :
        ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) 1 ≠ 0 := by
      -- Evaluating the scaled source character at `1` gives the nonzero scaled degree.
      simpa [Representation.char_one, smul_eq_mul] using
        mul_ne_zero (inv_ne_zero hn_ne) hdim_ne
    intro hzero
    apply hleft_ne_zero_K
    apply (algebraMap K' (AlgebraicClosure K')).injective
    simpa using hzero
  have hvalue :
      (((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character)) 1 = 0 := by
    -- With no visible constituents, the packet sum vanishes identically.
    simpa using congrFun hscaled_packet 1
  exact hleft_ne_zero hvalue

/-- Helper for Exercise 12-12.2-6: choose one visible constituent and package its full
transport orbit together with the basic closure properties needed for the orbit-projector
descent. -/
private theorem visible_transport_orbit_setup_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [ρ.ρ.IsIrreducible]
    [FiniteDimensional K' ρ]
    (n : ℕ+)
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (e : ι → ℕ)
    (hscaled_packet :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) =
        ∑ i, (e i : AlgebraicClosure K') • (ψ i).ρ.character) :
    ∃ (i0 : ι) (O : Finset ι),
      i0 ∈ O ∧
      (∀ j : ι,
        j ∈ O ↔
          ∃ (σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')) (τ : Equiv.Perm ι),
            (∀ k : ι, ∀ g : G, σ ((ψ k).ρ.character g) = (ψ (τ k)).ρ.character g) ∧
            τ i0 = j) ∧
      (∀ {σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')} {τ : Equiv.Perm ι},
        (∀ k : ι, ∀ g : G, σ ((ψ k).ρ.character g) = (ψ (τ k)).ρ.character g) →
          ∀ j : ι, j ∈ O ↔ τ j ∈ O) := by
  classical
  obtain ⟨i0⟩ :=
    visible_scaled_packet_nonempty_local
      (G := G) (ρ := ρ) (n := n) (ψ := ψ) (e := e) hscaled_packet
  let O : Finset ι := Finset.univ.filter fun j ↦
    ∃ (σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')) (τ : Equiv.Perm ι),
      (∀ k : ι, ∀ g : G, σ ((ψ k).ρ.character g) = (ψ (τ k)).ρ.character g) ∧
      τ i0 = j
  have hmem_O :
      ∀ j : ι,
        j ∈ O ↔
          ∃ (σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')) (τ : Equiv.Perm ι),
            (∀ k : ι, ∀ g : G, σ ((ψ k).ρ.character g) = (ψ (τ k)).ρ.character g) ∧
            τ i0 = j := by
    intro j
    -- Unfold the orbit definition once so later proofs can use the packaged reachability API.
    simp [O]
  have hi0_mem : i0 ∈ O := by
    -- The identity transport keeps the base constituent inside its own orbit.
    exact (hmem_O i0).2 <|
      packet_transport_reaches_self_local (G := G) (ψ := ψ) i0
  have hstable :
      ∀ {σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')} {τ : Equiv.Perm ι},
        (∀ k : ι, ∀ g : G, σ ((ψ k).ρ.character g) = (ψ (τ k)).ρ.character g) →
          ∀ j : ι, j ∈ O ↔ τ j ∈ O := by
    intro σ τ hchar j
    -- Once `O` is defined as the transport orbit of `i0`, stability is exactly the orbit
    -- closure lemma from the canonical packet-transport owner.
    exact
      packet_transport_orbit_stable_of_transport_local
        (G := G) (ψ := ψ) i0 O hmem_O hchar j
  exact ⟨i0, O, hi0_mem, hmem_O, hstable⟩

/-- Helper for Exercise 12-12.2-6: after the quotient coefficients collapse to `1`, the honest
isotypic fibers already realize the canonical multiple `n • χ_(ψ i)` and are nonempty. -/
private theorem canonical_multiple_honest_fiber_setup_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [FiniteDimensional K' ρ]
    (n : ℕ+)
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
    (hcoeff_one : ∀ i, e i = 1) :
    ∃ (a : ℕ) (σ : Fin a → Subrepresentation
        (Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ))
      (S : ι → Finset (Fin a)),
      DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule) ∧
      (Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ).character =
        ∑ j, ((σ j).toRepresentation).character ∧
      (∀ j, ((σ j).toRepresentation).IsIrreducible) ∧
      (∀ i j, j ∈ S i ↔ Nonempty (((σ j).toRepresentation).Equiv (ψ i).ρ)) ∧
      (∀ i, (S i).Nonempty) ∧
      ∀ i,
        Finset.sum
            (S i)
            (fun j ↦ ((σ j).toRepresentation).character) =
          (n : AlgebraicClosure K') • (ψ i).ρ.character := by
  obtain ⟨a, σ, S, hinternal, hσchar, hσirr, hS, hcanonical_fiber⟩ :=
    actual_scalar_extension_isotypic_fiber_character_eq_canonical_multiple_local
      (G := G) (ρ := ρ) (n := n) (ψ := ψ) (d := d) (e := e)
      hψ_fd hψ_pairwise hψ_irr hpacket he hcoeff_one
  have hS_nonempty : ∀ i, (S i).Nonempty := by
    -- The canonical multiple is the positive constant `n`, so every honest fiber is forced to
    -- contain at least one irreducible summand.
    exact
      isotypic_fiber_nonempty_of_positive_multiplicity_local
        (G := G) (ρ := ρ) (ψ := ψ) (a := a) (σ := σ) (S := S)
        (d := fun _ : ι ↦ (n : ℕ)) (hd_pos := fun _ ↦ n.pos)
        hψ_fd hψ_irr hcanonical_fiber
  exact ⟨a, σ, S, hinternal, hσchar, hσirr, hS, hS_nonempty, hcanonical_fiber⟩

/-- Helper for Exercise 12-12.2-6: evaluating the canonical-multiple honest-fiber identity at
`1` turns it into the corresponding degree sum identity. -/
private theorem actual_scalar_extension_isotypic_fiber_degree_sum_eq_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [FiniteDimensional K' ρ]
    (n : ℕ+)
    {ι : Type*}
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (a : ℕ)
    (σ : Fin a → Subrepresentation
      (Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ))
    (S : ι → Finset (Fin a))
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i))
    (hfiber_char :
      ∀ i,
        Finset.sum
            (S i)
            (fun j ↦ ((σ j).toRepresentation).character) =
          (n : AlgebraicClosure K') • (ψ i).ρ.character) :
    ∀ i,
      ((Finset.sum (S i)
          (fun j ↦ Module.finrank (AlgebraicClosure K') ↥((σ j).toSubmodule)) : ℕ) :
          AlgebraicClosure K') =
        (n : AlgebraicClosure K') *
          (Module.finrank (AlgebraicClosure K') (ψ i) : AlgebraicClosure K') := by
  intro i
  letI : FiniteDimensional (AlgebraicClosure K') (ψ i) := hψ_fd i
  -- Evaluate the honest-fiber character identity at the group identity to replace characters by
  -- degrees.
  simpa [Representation.char_one, smul_eq_mul] using congrFun (hfiber_char i) 1

/-- Helper for Exercise 12-12.2-6: once the honest `i`-th fiber has character `n • χ_(ψ i)`,
that fiber contains exactly `n` irreducible summands. -/
private theorem canonical_isotypic_fiber_card_eq_denominator_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [FiniteDimensional K' ρ]
    (n : ℕ+)
    {ι : Type*}
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (a : ℕ)
    (σ : Fin a → Subrepresentation
      (Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ))
    (S : ι → Finset (Fin a))
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i))
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (hσ_irr : ∀ j, ((σ j).toRepresentation).IsIrreducible)
    (hS : ∀ i j, j ∈ S i ↔ Nonempty (((σ j).toRepresentation).Equiv (ψ i).ρ))
    (hfiber_char :
      ∀ i,
        Finset.sum
            (S i)
            (fun j ↦ ((σ j).toRepresentation).character) =
          (n : AlgebraicClosure K') • (ψ i).ρ.character) :
    ∀ i, (S i).card = n := by
  intro i
  letI : FiniteDimensional (AlgebraicClosure K') (ψ i) := hψ_fd i
  letI : (ψ i).ρ.IsIrreducible := hψ_irr i
  have hfiber_degree :=
    actual_scalar_extension_isotypic_fiber_degree_sum_eq_local
      (G := G) (ρ := ρ) (n := n) (ψ := ψ) (a := a) (σ := σ) (S := S) hψ_fd hfiber_char i
  have hsum_eq :
      (Finset.sum (S i)
          (fun j ↦ Module.finrank (AlgebraicClosure K') ↥((σ j).toSubmodule)) : ℕ) =
        (S i).card * Module.finrank (AlgebraicClosure K') (ψ i) := by
    -- Every summand in the honest `i`-th fiber is isomorphic to `ψ i`, so the degree sum is a
    -- constant-cardinality multiple of `dim ψ i`.
    calc
      (Finset.sum (S i)
          (fun j ↦ Module.finrank (AlgebraicClosure K') ↥((σ j).toSubmodule)) : ℕ)
          =
        Finset.sum (S i) (fun _ ↦ Module.finrank (AlgebraicClosure K') (ψ i)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            letI : ((σ j).toRepresentation).IsIrreducible := hσ_irr j
            letI : FiniteDimensional (AlgebraicClosure K') ↥((σ j).toSubmodule) :=
              Representation.IsIrreducible.finiteDimensional_of_finite
                (ρ := (σ j).toRepresentation)
            have hj_iso : Nonempty (((σ j).toRepresentation).Equiv (ψ i).ρ) := (hS i j).mp hj
            rcases hj_iso with ⟨eIso⟩
            have hdim_cast :
                (Module.finrank (AlgebraicClosure K') ↥((σ j).toSubmodule) :
                    AlgebraicClosure K') =
                  (Module.finrank (AlgebraicClosure K') (ψ i) : AlgebraicClosure K') := by
              simpa [Representation.char_one] using congrFun (Representation.char_iso eIso) 1
            exact Nat.cast_injective hdim_cast
      _ = (S i).card * Module.finrank (AlgebraicClosure K') (ψ i) := by
            simp
  have hmul_eq :
      (S i).card * Module.finrank (AlgebraicClosure K') (ψ i) =
        (n : ℕ) * Module.finrank (AlgebraicClosure K') (ψ i) := by
    have hmul_eq_cast :
        (((S i).card * Module.finrank (AlgebraicClosure K') (ψ i) : ℕ) :
            AlgebraicClosure K') =
          (((n : ℕ) * Module.finrank (AlgebraicClosure K') (ψ i) : ℕ) :
            AlgebraicClosure K') := by
      calc
        (((S i).card * Module.finrank (AlgebraicClosure K') (ψ i) : ℕ) :
            AlgebraicClosure K')
            =
          (((Finset.sum (S i)
              (fun j ↦ Module.finrank (AlgebraicClosure K') ↥((σ j).toSubmodule)) : ℕ)) :
                AlgebraicClosure K') := by
              rw [hsum_eq]
        _ = (n : AlgebraicClosure K') *
            (Module.finrank (AlgebraicClosure K') (ψ i) : AlgebraicClosure K') := hfiber_degree
        _ =
          (((n : ℕ) * Module.finrank (AlgebraicClosure K') (ψ i) : ℕ) :
              AlgebraicClosure K') := by
              simp
    exact Nat.cast_injective hmul_eq_cast
  have hdim_pos : 0 < Module.finrank (AlgebraicClosure K') (ψ i) := by
    have hψ_nontriv : Nontrivial (ψ i) := by
      -- An irreducible representation cannot live on the zero module, or else `⊥ = ⊤`.
      by_contra hψ_trivial
      letI : Subsingleton (ψ i) := not_nontrivial_iff_subsingleton.mp hψ_trivial
      have hbot : (⊥ : Subrepresentation (ψ i).ρ) = ⊤ := by
        apply Subrepresentation.toSubmodule_injective
        ext x
        constructor
        · intro _
          trivial
        · intro _
          simpa using (Subsingleton.elim x 0)
      exact bot_ne_top hbot
    letI : Nontrivial (ψ i) := hψ_nontriv
    exact Module.finrank_pos
  exact Nat.eq_of_mul_eq_mul_right hdim_pos hmul_eq

/-- Helper for Exercise 12-12.2-6: after the quotient coefficients collapse to `1`, each honest
isotypic fiber contains exactly `n` irreducible summands. -/
private theorem canonicalMultipleHonestFiberCardSetup_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [FiniteDimensional K' ρ]
    (n : ℕ+)
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
    (hcoeff_one : ∀ i, e i = 1) :
    ∃ (a : ℕ) (σ : Fin a → Subrepresentation
        (Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ))
      (S : ι → Finset (Fin a)),
      DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule) ∧
      (Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ).character =
        ∑ j, ((σ j).toRepresentation).character ∧
      (∀ j, ((σ j).toRepresentation).IsIrreducible) ∧
      (∀ i j, j ∈ S i ↔ Nonempty (((σ j).toRepresentation).Equiv (ψ i).ρ)) ∧
      (∀ i, (S i).Nonempty) ∧
      (∀ i,
        Finset.sum
            (S i)
            (fun j ↦ ((σ j).toRepresentation).character) =
          (n : AlgebraicClosure K') • (ψ i).ρ.character) ∧
      ∀ i, (S i).card = n := by
  obtain ⟨a, σ, S, hinternal, hσchar, hσirr, hS, hS_nonempty, hcanonical_fiber⟩ :=
    canonical_multiple_honest_fiber_setup_local
      (G := G) (ρ := ρ) (n := n) (ψ := ψ) (d := d) (e := e)
      hψ_fd hψ_pairwise hψ_irr hpacket he hcoeff_one
  have hcard : ∀ i, (S i).card = n := by
    -- Convert the canonical-multiple character identity into a fiber-cardinality statement.
    exact
      canonical_isotypic_fiber_card_eq_denominator_local
        (G := G) (ρ := ρ) (n := n) (ψ := ψ) (a := a) (σ := σ) (S := S)
        hψ_fd hψ_irr hσirr hS hcanonical_fiber
  exact
    ⟨a, σ, S, hinternal, hσchar, hσirr, hS, hS_nonempty, hcanonical_fiber, hcard⟩

/-- Helper for Exercise 12-12.2-6: every honest summand in one fiber has the same degree as the
visible constituent indexing that fiber. -/
private theorem honestFiberSummand_finrank_eq_visible_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [FiniteDimensional K' ρ]
    {ι : Type*}
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    {a : ℕ}
    (σ : Fin a → Subrepresentation
      (Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ))
    (S : ι → Finset (Fin a))
    (hS : ∀ i j, j ∈ S i ↔ Nonempty (((σ j).toRepresentation).Equiv (ψ i).ρ))
    {i : ι} {j : Fin a}
    (hj : j ∈ S i) :
    Module.finrank (AlgebraicClosure K') ↥((σ j).toSubmodule) =
      Module.finrank (AlgebraicClosure K') (ψ i) := by
  -- Transport the carrier through the chosen representation equivalence and forget equivariance.
  rcases (hS i j).mp hj with ⟨e⟩
  simpa using e.toLinearEquiv.finrank_eq

/-- Helper for Exercise 12-12.2-6: summing the degrees over one honest fiber simply multiplies
the constituent degree by the fiber cardinality. -/
private theorem honestFiber_finrank_sum_eq_card_mul_constituent_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [FiniteDimensional K' ρ]
    {ι : Type*}
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    {a : ℕ}
    (σ : Fin a → Subrepresentation
      (Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ))
    (S : ι → Finset (Fin a))
    (hS : ∀ i j, j ∈ S i ↔ Nonempty (((σ j).toRepresentation).Equiv (ψ i).ρ))
    (i : ι) :
    Finset.sum (S i)
        (fun j ↦ Module.finrank (AlgebraicClosure K') ↥((σ j).toSubmodule)) =
      (S i).card * Module.finrank (AlgebraicClosure K') (ψ i) := by
  -- Every term in the honest fiber has the same degree, so the finite sum is a cardinal multiple.
  calc
    Finset.sum (S i)
        (fun j ↦ Module.finrank (AlgebraicClosure K') ↥((σ j).toSubmodule)) =
      Finset.sum (S i)
        (fun _ ↦ Module.finrank (AlgebraicClosure K') (ψ i)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          exact honestFiberSummand_finrank_eq_visible_local
            (G := G) (ρ := ρ) (ψ := ψ) (σ := σ) (S := S) hS hj
    _ = (S i).card * Module.finrank (AlgebraicClosure K') (ψ i) := by
          simp

/-- Helper for Exercise 12-12.2-6: an equivalence of representations intertwines the induced
group-algebra action on every group-algebra element. This packages the transport step needed to
move central-idempotent actions from packet constituents to honest fiber summands. -/
private theorem representationEquiv_asAlgebraHom_comm_local
    {L : Type*} [Field L]
    {V W : Type*} [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    {ρ : Representation L G V} {σ : Representation L G W}
    (e : ρ.Equiv σ)
    (u : MonoidAlgebra L G) :
    e.toLinearEquiv.toLinearMap.comp (ρ.asAlgebraHom u) =
      (σ.asAlgebraHom u).comp e.toLinearEquiv.toLinearMap := by
  refine MonoidAlgebra.induction_on
    (p := fun u : MonoidAlgebra L G ↦
      e.toLinearEquiv.toLinearMap.comp (ρ.asAlgebraHom u) =
        (σ.asAlgebraHom u).comp e.toLinearEquiv.toLinearMap)
    u ?_ ?_ ?_
  · intro g
    ext x
    -- On group elements, this is exactly the intertwining relation carried by `e`.
    simpa [Representation.asAlgebraHom_of, LinearMap.comp_apply] using
      congrArg (fun f : V →ₗ[L] W ↦ f x) (e.toIntertwiningMap.2 g)
  · intro a b ha hb
    -- The intertwining relation is additive in the group-algebra input.
    simp [ha, hb, LinearMap.add_comp, LinearMap.comp_add]
  · intro r a ha
    -- Scalar coefficients commute with both sides of the transported action.
    simp [ha, LinearMap.smul_comp, LinearMap.comp_smul]

/-- Helper for Exercise 12-12.2-6: restricting a group-algebra action to a subrepresentation just
evaluates the ambient action on the underlying vector. -/
private theorem subrepresentation_asAlgebraHom_apply_block_local
    {L : Type*} [Field L]
    {G' : Type*} [Group G']
    {V : Type*} [AddCommGroup V] [Module L V]
    (ρ : Representation L G' V) (σ : Subrepresentation ρ)
    (u : MonoidAlgebra L G') (x : σ) :
    (((σ.toRepresentation).asAlgebraHom u) x : V) = ρ.asAlgebraHom u (x : V) := by
  -- Compare the restricted action with the ambient action on group-algebra generators.
  induction u using MonoidAlgebra.induction_linear with
  | zero =>
      rfl
  | add a b ha hb =>
      simpa [map_add, LinearMap.add_apply] using congrArg₂ HAdd.hAdd ha hb
  | single g a =>
      simp [Representation.asAlgebraHom_single, Representation.single_smul]
      rfl

/-- Helper for Exercise 12-12.2-6: if a group-algebra element acts trivially on the ambient
representation, then it acts trivially on every subrepresentation. -/
private theorem subrepresentation_action_zero_of_ambient_zero_block_local
    {L : Type*} [Field L]
    {G' : Type*} [Group G']
    {V : Type*} [AddCommGroup V] [Module L V]
    (ρ : Representation L G' V) (σ : Subrepresentation ρ)
    (u : MonoidAlgebra L G') (hu : ρ.asAlgebraHom u = 0) :
    σ.toRepresentation.asAlgebraHom u = 0 := by
  ext x
  -- Evaluate the ambient vanishing on the underlying vector and then restrict back.
  have hx := congrArg (fun T : Module.End L V ↦ T (x : V)) hu
  simpa [subrepresentation_asAlgebraHom_apply_block_local ρ σ u x] using hx

/-- Helper for Exercise 12-12.2-6: if a group-algebra element acts as the identity on the ambient
representation, then it acts as the identity on every subrepresentation. -/
private theorem subrepresentation_action_id_of_ambient_id_block_local
    {L : Type*} [Field L]
    {G' : Type*} [Group G']
    {V : Type*} [AddCommGroup V] [Module L V]
    (ρ : Representation L G' V) (σ : Subrepresentation ρ)
    (u : MonoidAlgebra L G') (hu : ρ.asAlgebraHom u = LinearMap.id) :
    σ.toRepresentation.asAlgebraHom u = LinearMap.id := by
  ext x
  -- Evaluate the ambient identity on the underlying vector and then restrict back.
  have hx := congrArg (fun T : Module.End L V ↦ T (x : V)) hu
  simpa [subrepresentation_asAlgebraHom_apply_block_local ρ σ u x] using hx

/-- Helper for Exercise 12-12.2-6: a representation equivalence transports a vanishing
group-algebra action to the target representation. -/
private theorem action_eq_zero_of_equiv_local
    {L : Type*} [Field L]
    {V W : Type*} [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    {ρ : Representation L G V} {σ : Representation L G W}
    (e : ρ.Equiv σ)
    (u : MonoidAlgebra L G)
    (hu : ρ.asAlgebraHom u = 0) :
    σ.asAlgebraHom u = 0 := by
  ext x
  -- Evaluate the intertwining relation on a preimage of `x` to move the zero action across `e`.
  have hcomm := representationEquiv_asAlgebraHom_comm_local (G := G) (ρ := ρ) (σ := σ) e u
  have hpoint :=
    congrArg
      (fun T : V →ₗ[L] W ↦ T (e.toLinearEquiv.symm x))
      hcomm
  have hzero :
      (σ.asAlgebraHom u) (e.toLinearEquiv (e.toLinearEquiv.symm x)) = 0 := by
    simpa [hu, LinearMap.comp_apply] using hpoint.symm
  simpa using (e.toLinearEquiv.apply_symm_apply x ▸ hzero)

/-- Helper for Exercise 12-12.2-6: a representation equivalence transports the identity
group-algebra action to the target representation. -/
private theorem action_eq_id_of_equiv_local
    {L : Type*} [Field L]
    {V W : Type*} [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    {ρ : Representation L G V} {σ : Representation L G W}
    (e : ρ.Equiv σ)
    (u : MonoidAlgebra L G)
    (hu : ρ.asAlgebraHom u = LinearMap.id) :
    σ.asAlgebraHom u = LinearMap.id := by
  ext x
  -- Evaluate the intertwining relation on a preimage of `x` to move the identity action across
  -- the representation equivalence.
  have hcomm := representationEquiv_asAlgebraHom_comm_local (G := G) (ρ := ρ) (σ := σ) e u
  have hpoint :=
    congrArg
      (fun T : V →ₗ[L] W ↦ T (e.toLinearEquiv.symm x))
      hcomm
  have hid :
      (σ.asAlgebraHom u) (e.toLinearEquiv (e.toLinearEquiv.symm x)) =
        e.toLinearEquiv (e.toLinearEquiv.symm x) := by
    simpa [hu, LinearMap.comp_apply] using hpoint.symm
  simpa using (show (σ.asAlgebraHom u) x = x by
    simpa using (e.toLinearEquiv.apply_symm_apply x ▸ hid))

/-- Helper for Exercise 12-12.2-6: if a group-algebra element acts by one scalar on the ambient
representation, then it acts by the same scalar on every subrepresentation. -/
private theorem subrepresentation_action_smul_id_of_ambient_smul_id_block_local
    {L : Type*} [Field L]
    {G' : Type*} [Group G']
    {V : Type*} [AddCommGroup V] [Module L V]
    (ρ : Representation L G' V) (σ : Subrepresentation ρ)
    (u : MonoidAlgebra L G') (c : L)
    (hu : ρ.asAlgebraHom u = c • LinearMap.id) :
    σ.toRepresentation.asAlgebraHom u = c • LinearMap.id := by
  ext x
  -- Evaluate the ambient scalar action on the underlying vector and then restrict back.
  have hx := congrArg (fun T : Module.End L V ↦ T (x : V)) hu
  simpa [subrepresentation_asAlgebraHom_apply_block_local ρ σ u x, LinearMap.smul_apply] using hx

/-- Helper for Exercise 12-12.2-6: a representation equivalence transports a scalar action to the
target representation without changing the scalar. -/
private theorem action_eq_smul_id_of_equiv_local
    {L : Type*} [Field L]
    {V W : Type*} [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    {ρ : Representation L G V} {σ : Representation L G W}
    (e : ρ.Equiv σ)
    (u : MonoidAlgebra L G)
    (c : L)
    (hu : ρ.asAlgebraHom u = c • LinearMap.id) :
    σ.asAlgebraHom u = c • LinearMap.id := by
  ext x
  -- Evaluate the intertwining relation on a preimage of `x` to move the scalar action across `e`.
  have hcomm := representationEquiv_asAlgebraHom_comm_local (G := G) (ρ := ρ) (σ := σ) e u
  have hpoint :=
    congrArg
      (fun T : V →ₗ[L] W ↦ T (e.toLinearEquiv.symm x))
      hcomm
  have hscalar :
      (σ.asAlgebraHom u) (e.toLinearEquiv (e.toLinearEquiv.symm x)) =
        c • e.toLinearEquiv (e.toLinearEquiv.symm x) := by
    simpa [hu, LinearMap.comp_apply, LinearMap.smul_apply] using hpoint.symm
  simpa using (show (σ.asAlgebraHom u) x = c • x by
    simpa using (e.toLinearEquiv.apply_symm_apply x ▸ hscalar))

/-- Helper for Exercise 12-12.2-6: an irreducible representation has nontrivial carrier. -/
private theorem irreducible_rep_nontrivial_block_local
    {L : Type*} [Field L]
    {V : Type*} [AddCommGroup V] [Module L V]
    (ρ : Representation L G V)
    [ρ.IsIrreducible] :
    Nontrivial V := by
  -- A subsingleton carrier would force `⊥ = ⊤`, contradicting irreducibility.
  by_contra hV_trivial
  letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV_trivial
  have hbot : (⊥ : Subrepresentation ρ) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro _
      trivial
    · intro _
      simpa using (Subsingleton.elim x 0)
  exact bot_ne_top hbot

/-- Helper for Exercise 12-12.2-6: if a scalar action equals the identity on a nontrivial
representation, then the scalar is `1`. -/
private theorem scalar_eq_one_of_smul_id_eq_id_block_local
    {L : Type*} [Field L]
    {V : Type*} [AddCommGroup V] [Module L V]
    [Nontrivial V]
    (c : L)
    (h : c • (LinearMap.id : Module.End L V) = LinearMap.id) :
    c = 1 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have hx' : c • x = x := by
    simpa [LinearMap.smul_apply] using congrArg (fun T : Module.End L V ↦ T x) h
  have hcx : (c - 1) • x = 0 := by
    calc
      (c - 1) • x = c • x - (1 : L) • x := by simp [sub_smul]
      _ = x - x := by simpa [hx']
      _ = 0 := sub_self x
  rcases smul_eq_zero.mp hcx with hc | hx0
  · exact sub_eq_zero.mp hc
  · exact False.elim (hx hx0)

/-- Helper for Exercise 12-12.2-6: if a scalar action vanishes on a nontrivial representation,
then the scalar is `0`. -/
private theorem scalar_eq_zero_of_smul_id_eq_zero_block_local
    {L : Type*} [Field L]
    {V : Type*} [AddCommGroup V] [Module L V]
    [Nontrivial V]
    (c : L)
    (h : c • (LinearMap.id : Module.End L V) = 0) :
    c = 0 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have hx' : c • x = 0 := by
    simpa [LinearMap.smul_apply] using congrArg (fun T : Module.End L V ↦ T x) h
  rcases smul_eq_zero.mp hx' with hc | hx0
  · exact hc
  · exact False.elim (hx hx0)

/-- Helper for Exercise 12-12.2-6: a central group-algebra element acts equivariantly on the
source representation. -/
private theorem asAlgebraHom_isIntertwining_of_mem_center_block_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    (u : Subalgebra.center K1 (MonoidAlgebra K1 G)) :
    ρ.ρ.IsIntertwiningMap ρ.ρ (ρ.ρ.asAlgebraHom u) := by
  rw [isIntertwiningMap_iff]
  intro g x
  -- Centrality lets the source action commute with every group element of `G`.
  have h :=
    congrArg (ρ.ρ.asAlgebraHom)
      (((Subalgebra.mem_center_iff.mp u.2) (MonoidAlgebra.of K1 G g)).symm)
  simpa [Representation.asAlgebraHom_of, Module.End.mul_apply] using LinearMap.congr_fun h x

/-- Helper for Exercise 12-12.2-6: an idempotent equivariant endomorphism of an irreducible
source representation is either zero or the identity. -/
private theorem idempotent_intertwining_eq_zero_or_one_block_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    [ρ.ρ.IsIrreducible]
    (f : ρ.ρ.IntertwiningMap ρ.ρ)
    (hidem : f * f = f) :
    f = 0 ∨ f = 1 := by
  by_cases hf : f = 0
  · exact Or.inl hf
  · have hbij : Function.Bijective f :=
      (Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf
    right
    ext x
    rcases hbij.2 x with ⟨y, rfl⟩
    -- Surjectivity turns the idempotence relation into pointwise identity.
    simpa [Module.End.mul_apply] using congrArg (fun T : ρ.ρ.IntertwiningMap ρ.ρ ↦ T y) hidem

/-- Helper for Exercise 12-12.2-6: once a descended central group-algebra element acts
idempotently on the irreducible source representation, that action is forced to be `0` or `1`. -/
private theorem central_idempotent_source_action_eq_zero_or_one_block_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    [ρ.ρ.IsIrreducible]
    (u : Subalgebra.center K1 (MonoidAlgebra K1 G))
    (hidem : ρ.ρ.asAlgebraHom u * ρ.ρ.asAlgebraHom u = ρ.ρ.asAlgebraHom u) :
    ρ.ρ.asAlgebraHom u = 0 ∨ ρ.ρ.asAlgebraHom u = 1 := by
  let f : ρ.ρ.IntertwiningMap ρ.ρ :=
    (ρ.ρ.asAlgebraHom u).intertwiningMap_of_isIntertwiningMap ρ.ρ ρ.ρ
      (asAlgebraHom_isIntertwining_of_mem_center_block_local (G := G) (ρ := ρ) u).isIntertwining
  have hfidem : f * f = f := by
    ext x
    -- Repackage the idempotence of the action inside the intertwining-map structure.
    simpa [f, Module.End.mul_apply] using congrArg (fun T : Module.End K1 ρ ↦ T x) hidem
  rcases idempotent_intertwining_eq_zero_or_one_block_local (G := G) (ρ := ρ) f hfidem with
      hf0 | hf1
  · left
    ext x
    simpa [f] using congrArg (fun T : ρ.ρ.IntertwiningMap ρ.ρ ↦ T x) hf0
  · right
    ext x
    simpa [f] using congrArg (fun T : ρ.ρ.IntertwiningMap ρ.ρ ↦ T x) hf1

/-- Helper for Exercise 12-12.2-6: transport the coefficients of the top fixed field back to the
source field `K'` through the canonical infinite-Galois identification `fixedField ⊤ = ⊥`. -/
private noncomputable def topFixedFieldEquiv_local
    {K' : Type v} [Field K'] [CharZero K'] :
    IntermediateField.fixedField
        (⊤ : Subgroup ((AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K'))) ≃ₐ[K'] K' :=
  (IntermediateField.equivOfEq
      (InfiniteGalois.fixedField_bot (k := K') (K := AlgebraicClosure K'))).trans
    (IntermediateField.botEquiv K' (AlgebraicClosure K'))

/-- Helper for Exercise 12-12.2-6: package the descended coefficients over `fixedField ⊤` as an
honest source-field group-algebra element. -/
private noncomputable def topFixedFieldDescend_local
    {K' : Type v} [Field K'] [CharZero K']
    (p0 : MonoidAlgebra
      (IntermediateField.fixedField
        (⊤ : Subgroup ((AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')))) G) :
    MonoidAlgebra K' G :=
  Finsupp.equivFunOnFinite.symm (fun g : G ↦ topFixedFieldEquiv_local (K' := K') (p0 g))

/-- Helper for Exercise 12-12.2-6: after descending from `fixedField ⊤` to `K'`, mapping the
result back to the algebraic closure recovers the original coefficient. -/
private theorem topFixedFieldDescend_map_apply_local
    {K' : Type v} [Field K'] [CharZero K']
    (p0 : MonoidAlgebra
      (IntermediateField.fixedField
        (⊤ : Subgroup ((AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')))) G)
    (g : G) :
    algebraMap K' (AlgebraicClosure K') ((topFixedFieldDescend_local (K' := K') p0) g) =
      ((p0 g :
        IntermediateField.fixedField
          (⊤ : Subgroup ((AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')))) :
        AlgebraicClosure K') := by
  let y0 : (⊥ : IntermediateField K' (AlgebraicClosure K')) :=
    (IntermediateField.equivOfEq
      (InfiniteGalois.fixedField_bot (k := K') (K := AlgebraicClosure K'))) (p0 g)
  have hy0 :
      algebraMap K' (AlgebraicClosure K') ((IntermediateField.botEquiv K' (AlgebraicClosure K')) y0) =
        (y0 : AlgebraicClosure K') := by
    rcases y0 with ⟨x, hx⟩
    rcases hx with ⟨y, rfl⟩
    -- After exposing the bottom-field presentation, `botEquiv` evaluates at the chosen preimage.
    change
      algebraMap K' (AlgebraicClosure K')
          ((IntermediateField.botEquiv K' (AlgebraicClosure K'))
            ((algebraMap K'
              (⊥ : IntermediateField K' (AlgebraicClosure K'))) y)) =
        algebraMap K' (AlgebraicClosure K') y
    rw [IntermediateField.botEquiv_def]
  simpa [topFixedFieldDescend_local, topFixedFieldEquiv_local, y0] using hy0

/-- Helper for Exercise 12-12.2-6: once a top-fixed-field projector has a prescribed coefficient
function after coercion to the algebraic closure, descending to `K'` and extending scalars again
recovers exactly that coefficient function. -/
private theorem topFixedFieldDescend_map_eq_function_local
    {K' : Type v} [Field K'] [CharZero K']
    (p0 : MonoidAlgebra
      (IntermediateField.fixedField
        (⊤ : Subgroup ((AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')))) G)
    (f : G → AlgebraicClosure K')
    (hp0 :
      ∀ g : G,
        ((p0 g :
          IntermediateField.fixedField
            (⊤ : Subgroup ((AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')))) :
          AlgebraicClosure K') =
            f g) :
    MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K'))
        (topFixedFieldDescend_local (K' := K') p0) =
      Finsupp.equivFunOnFinite.symm f := by
  ext g
  -- Compare the descended source coefficients with the prescribed closure-side coefficient
  -- function one coefficient at a time.
  calc
    MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K'))
        (topFixedFieldDescend_local (K' := K') p0) g
        =
      algebraMap K' (AlgebraicClosure K')
        ((topFixedFieldDescend_local (K' := K') p0) g) := by
          simp [MonoidAlgebra.mapRingHom_apply]
    _ =
      ((p0 g :
        IntermediateField.fixedField
          (⊤ : Subgroup ((AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')))) :
        AlgebraicClosure K') := by
          simpa using topFixedFieldDescend_map_apply_local (K' := K') p0 g
    _ = f g := hp0 g
    _ = Finsupp.equivFunOnFinite.symm f g := by
          rfl

/-- Helper for Exercise 12-12.2-6: coefficient extension on a finite group algebra is injective
whenever the coefficient map is injective. -/
private theorem monoidAlgebra_mapRingHom_injective_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (f : K1 →+* AlgebraicClosure K1)
    (hf : Function.Injective f) :
    Function.Injective (MonoidAlgebra.mapRingHom G f) := by
  intro x y hxy
  ext g
  exact hf (by simpa using congrArg (fun z : MonoidAlgebra (AlgebraicClosure K1) G ↦ z g) hxy)

/-- Helper for Exercise 12-12.2-6: after descending an orbit projector from the top fixed field
back to `K'`, extending scalars again recovers the finite sum of Serre's explicit primitive
central-idempotent formulas over that orbit. -/
private theorem topFixedField_orbitProjector_map_eq_sum_characterCentralElements_local
    {K' : Type v} [Field K'] [CharZero K']
    {ι : Type*}
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i))
    (O : Finset ι)
    (p0 : MonoidAlgebra
      (IntermediateField.fixedField
        (⊤ : Subgroup ((AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')))) G)
    (hp0 :
      ∀ g : G,
        ((p0 g :
          IntermediateField.fixedField
            (⊤ : Subgroup ((AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')))) :
          AlgebraicClosure K') =
            Finset.sum O
              (fun i ↦
                primitive_central_idempotent_coefficient_packet_local
                  (G := G) (V := ψ i) g)) :
    MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K'))
        (topFixedFieldDescend_local (K' := K') p0) =
      Finset.sum O
        (fun i ↦
          ((((Module.finrank (AlgebraicClosure K') (ψ i) : AlgebraicClosure K') / Nat.card G) •
              ∑ s : G, (ψ i).ρ.character s⁻¹ •
                MonoidAlgebra.of (AlgebraicClosure K') G s) :
            MonoidAlgebra (AlgebraicClosure K') G)) := by
  classical
  ext g
  -- First rewrite the descended projector coefficientwise by the prescribed orbit-projector
  -- coefficient function.
  calc
    MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K'))
        (topFixedFieldDescend_local (K' := K') p0) g
        =
      Finset.sum O
        (fun i ↦
          primitive_central_idempotent_coefficient_packet_local
            (G := G) (V := ψ i) g) := by
          simpa using
            congrArg
              (fun z : MonoidAlgebra (AlgebraicClosure K') G ↦ z g)
              (topFixedFieldDescend_map_eq_function_local
                (G := G) (K' := K') p0
                (fun g' ↦
                  Finset.sum O
                    (fun i ↦
                      primitive_central_idempotent_coefficient_packet_local
                        (G := G) (V := ψ i) g'))
                hp0)
    _ =
      Finset.sum O
        (fun i ↦
          (((((Module.finrank (AlgebraicClosure K') (ψ i) : AlgebraicClosure K') / Nat.card G) •
              ∑ s : G, (ψ i).ρ.character s⁻¹ •
                MonoidAlgebra.of (AlgebraicClosure K') G s) :
            MonoidAlgebra (AlgebraicClosure K') G) g)) := by
          -- Replace each orbit-projector coefficient by the corresponding explicit primitive
          -- central-idempotent coefficient formula.
          refine Finset.sum_congr rfl ?_
          intro i hi
          letI : FiniteDimensional (AlgebraicClosure K') (ψ i) := hψ_fd i
          simpa using
            (primitive_central_idempotent_coefficient_eq_characterCentralElement_coeff_local
              (G := G) (V := ψ i) g).symm
    _ =
      (Finset.sum O
        (fun i ↦
          ((((Module.finrank (AlgebraicClosure K') (ψ i) : AlgebraicClosure K') / Nat.card G) •
              ∑ s : G, (ψ i).ρ.character s⁻¹ •
                MonoidAlgebra.of (AlgebraicClosure K') G s) :
            MonoidAlgebra (AlgebraicClosure K') G))) g := by
          -- Reassemble the coefficientwise sum back into the group-algebra value at `g`.
          exact
            (Finsupp.finset_sum_apply O
              (fun i ↦
                ((((Module.finrank (AlgebraicClosure K') (ψ i) : AlgebraicClosure K') /
                    Nat.card G) •
                    ∑ s : G, (ψ i).ρ.character s⁻¹ •
                      MonoidAlgebra.of (AlgebraicClosure K') G s) :
                  MonoidAlgebra (AlgebraicClosure K') G))
              g).symm

/-- Helper for Exercise 12-12.2-6: the visible transport orbit admits a descended projector over
`fixedField ⊤`, expressed coefficientwise by the orbit sum of Serre's primitive-central-element
formula. -/
private theorem topFixedField_orbitProjector_descent_data_local
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
    (he : ∀ i, d i = (n : ℕ) * e i)
    (hscaled_packet :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) =
        ∑ i, (e i : AlgebraicClosure K') • (ψ i).ρ.character)
    (i0 : ι)
    (O : Finset ι)
    (hstable :
      ∀ {σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')} {τ : Equiv.Perm ι},
        (∀ k : ι, ∀ g : G, σ ((ψ k).ρ.character g) = (ψ (τ k)).ρ.character g) →
          ∀ j : ι, j ∈ O ↔ τ j ∈ O) :
    ∃ p0 : MonoidAlgebra
        (IntermediateField.fixedField
          (⊤ : Subgroup ((AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')))) G,
      ∀ g : G,
        ((p0 g :
          IntermediateField.fixedField
            (⊤ : Subgroup ((AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')))) :
          AlgebraicClosure K') =
            Finset.sum O
              (fun i ↦
                primitive_central_idempotent_coefficient_packet_local
                  (G := G) (V := ψ i) g) := by
  classical
  let perm :
      ∀ σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K'),
        σ ∈ (⊤ : Subgroup ((AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K'))) →
          Equiv.Perm ι :=
    fun σ _ ↦
      Classical.choose <|
        packet_transport_perm_exists_local
          (G := G) (ρ := ρ) (n := n) (ψ := ψ) (d := d) (e := e)
          hd_pos hψ_fd hψ_pairwise hψ_irr he hscaled_packet σ
  have hperm_char :
      ∀ (σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K'))
        (hσ : σ ∈ (⊤ : Subgroup ((AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K'))))
        (i : ι) (g : G),
          σ ((ψ i).ρ.character g) = (ψ (perm σ hσ i)).ρ.character g := by
    intro σ hσ i g
    exact
      (Classical.choose_spec <|
        packet_transport_perm_exists_local
          (G := G) (ρ := ρ) (n := n) (ψ := ψ) (d := d) (e := e)
          hd_pos hψ_fd hψ_pairwise hψ_irr he hscaled_packet σ) i g
  have hperm_stable :
      ∀ (σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K'))
        (hσ : σ ∈ (⊤ : Subgroup ((AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K'))))
        (j : ι),
          j ∈ O ↔ perm σ hσ j ∈ O := by
    intro σ hσ j
    exact hstable (hperm_char σ hσ) j
  -- Descend the orbit projector using the top fixed field and the packaged transport stability.
  exact
    transport_orbit_projector_descends_local
      (G := G)
      (H := (⊤ : Subgroup ((AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K'))))
      (ψ := ψ) hψ_fd perm hperm_char O hperm_stable

/-- Helper for Exercise 12-12.2-6: descending a Galois-orbit projector from the scalar-extension
packet forces the transport orbit of any selected visible constituent to be the whole packet. -/
theorem full_transport_cover_of_irreducible_source_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [ρ.ρ.IsIrreducible]
    [FiniteDimensional K' ρ]
    (n : ℕ+)
    (hcanon : ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) ∈ R̄[K'](G))
    (hmax :
      ∀ d' : ℕ+, ((((d' : ℕ) : K')⁻¹) • ρ.ρ.character) ∈ R̄[K'](G) → d' ≤ n)
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
    ∃ i0 : ι,
      ∀ j : ι,
        ∃ (σ' : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')) (τ : Equiv.Perm ι),
          (∀ k : ι, ∀ g : G, σ' ((ψ k).ρ.character g) = (ψ (τ k)).ρ.character g) ∧
          τ i0 = j := by
  classical
  obtain ⟨i0, O, hi0_mem, hmem_O, hstable⟩ :=
    visible_transport_orbit_setup_local
      (G := G) (ρ := ρ) (n := n) (ψ := ψ) (e := e) hscaled_packet
  obtain ⟨a, σ, S, hinternal, hσchar, hσirr, hS, hfiber_char⟩ :=
    Exercise_12_12_2_6.actual_scalar_extension_isotypic_fiber_character_local
      (ρ := ρ) (ψ := ψ) (d := d) hψ_fd hψ_pairwise hψ_irr hpacket
  have hS_nonempty : ∀ k, (S k).Nonempty := by
    -- Every visible multiplicity block is positive, so each honest isotypic fiber is inhabited.
    exact
      isotypic_fiber_nonempty_of_positive_multiplicity_local
        (G := G) (ρ := ρ) (ψ := ψ) (a := a) (σ := σ) (S := S) (d := d)
        hd_pos hψ_fd hψ_irr hfiber_char
  obtain ⟨p0, hp0⟩ :=
    topFixedField_orbitProjector_descent_data_local
      (G := G) (ρ := ρ) (n := n)
      (ψ := ψ) (d := d) (e := e)
      hd_pos hψ_fd hψ_pairwise hψ_irr he hscaled_packet
      i0 O hstable
  let u : MonoidAlgebra K' G := topFixedFieldDescend_local (K' := K') p0
  let p : ι → MonoidAlgebra (AlgebraicClosure K') G :=
    fun k ↦
      ((primitiveCentralElement_center_universe_local (G := G) (ψ k) :
        Subalgebra.center (AlgebraicClosure K') (MonoidAlgebra (AlgebraicClosure K') G)) :
        MonoidAlgebra (AlgebraicClosure K') G)
  have hu_map :
      MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) u =
        Finset.sum O
          (fun k ↦
            ((((Module.finrank (AlgebraicClosure K') (ψ k) : AlgebraicClosure K') / Nat.card G) •
                ∑ s : G, (ψ k).ρ.character s⁻¹ •
                  MonoidAlgebra.of (AlgebraicClosure K') G s) :
              MonoidAlgebra (AlgebraicClosure K') G)) := by
    simpa [u] using
      topFixedField_orbitProjector_map_eq_sum_characterCentralElements_local
        (G := G) (ψ := ψ) hψ_fd O p0 hp0
  have hu_map_center :
      MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) u =
        Finset.sum O p := by
    simpa [p, primitiveCentralElement_center_universe_local] using hu_map
  have hmap_injective :
      Function.Injective
        (MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K'))) := by
    exact
      monoidAlgebra_mapRingHom_injective_local
        (G := G) (f := algebraMap K' (AlgebraicClosure K'))
        (hf := (algebraMap K' (AlgebraicClosure K')).injective)
  have hu_center_map :
      MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) u ∈
        Subalgebra.center (AlgebraicClosure K') (MonoidAlgebra (AlgebraicClosure K') G) := by
    rw [hu_map_center]
    have hsum_center :
        O.sum p ∈
          Subalgebra.center (AlgebraicClosure K') (MonoidAlgebra (AlgebraicClosure K') G) := by
      have hsum_center' :
          ∀ s : Finset ι,
            s.sum p ∈
              Subalgebra.center (AlgebraicClosure K') (MonoidAlgebra (AlgebraicClosure K') G) := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
            simp
        | @insert k s hk hs =>
            rw [Finset.sum_insert hk]
            refine Subalgebra.add_mem _ ?_ hs
            letI : FiniteDimensional (AlgebraicClosure K') (ψ k) := hψ_fd k
            exact (primitiveCentralElement_center_universe_local (G := G) (ψ k)).2
      exact hsum_center' O
    simpa using hsum_center
  have hu_center : u ∈ Subalgebra.center K' (MonoidAlgebra K' G) := by
    refine Subalgebra.mem_center_iff.mpr ?_
    intro x
    apply hmap_injective
    have hcomm :=
      (Subalgebra.mem_center_iff.mp hu_center_map)
        (MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) x)
    simpa [map_mul] using hcomm
  let uc : Subalgebra.center K' (MonoidAlgebra K' G) := ⟨u, hu_center⟩
  let f : ρ.ρ.IntertwiningMap ρ.ρ :=
    (ρ.ρ.asAlgebraHom uc).intertwiningMap_of_isIntertwiningMap ρ.ρ ρ.ρ
      (asAlgebraHom_isIntertwining_of_mem_center_block_local (G := G) (ρ := ρ) uc).isIntertwining
  have hf_nonzero : f ≠ 0 := by
    intro hf_zero
    have hzero : ρ.ρ.asAlgebraHom uc = 0 := by
      ext x
      simpa [f] using congrArg (fun T : ρ.ρ.IntertwiningMap ρ.ρ ↦ T x) hf_zero
    obtain ⟨j0, hj0⟩ := hS_nonempty i0
    rcases (hS i0 j0).1 hj0 with ⟨e0⟩
    have hρext_zero :
        (Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ).asAlgebraHom
            (MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) u) =
          0 := by
      rw [scalar_extension_asAlgebraHom_mapRingHom_local (G := G) (ρ := ρ) u, hzero]
      simp
    have hσj0_zero :
        ((σ j0).toRepresentation).asAlgebraHom
            (MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) u) =
          0 := by
      exact
        subrepresentation_action_zero_of_ambient_zero_block_local
          (ρ := Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ)
          (σ := σ j0)
          (u := MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) u)
          hρext_zero
    have hψi0_zero :
        (ψ i0).ρ.asAlgebraHom
            (MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) u) =
          0 := by
      exact
        action_eq_zero_of_equiv_local
          (G := G) e0
          (MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) u)
          hσj0_zero
    have hψi0_id :
        (ψ i0).ρ.asAlgebraHom
            (MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) u) =
          LinearMap.id := by
      simpa [hu_map_center, p] using
        orbitProjector_sum_action_eq_id_local
          (G := G) (ψ := ψ) (O := O) hψ_pairwise hψ_irr hi0_mem
    letI : Nontrivial (ψ i0) :=
      irreducible_rep_nontrivial_block_local (G := G) ((ψ i0).ρ)
    exact False.elim (one_ne_zero <| hψi0_id.symm.trans hψi0_zero)
  have hf_bij : Function.Bijective f :=
    (Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf_nonzero
  have hsource_bij : Function.Bijective (ρ.ρ.asAlgebraHom uc) := by
    simpa [f] using hf_bij
  let ef : ρ ≃ₗ[K'] ρ := LinearEquiv.ofBijective (ρ.ρ.asAlgebraHom uc) hsource_bij
  have hρext_eq :
      (Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ).asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) u) =
        ((ρ.ρ.asAlgebraHom uc).baseChange (AlgebraicClosure K')) := by
    simpa [uc] using
      scalar_extension_asAlgebraHom_mapRingHom_local (G := G) (ρ := ρ) u
  have hρext_inj :
      Function.Injective
        ((Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ).asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) u)) := by
    rw [hρext_eq]
    have hleft :
        Function.LeftInverse
          ((ef.symm.toLinearMap).baseChange (AlgebraicClosure K'))
          ((ρ.ρ.asAlgebraHom uc).baseChange (AlgebraicClosure K')) := by
      intro x
      have hcomp :
          ((ef.symm.toLinearMap).baseChange (AlgebraicClosure K')).comp
              ((ρ.ρ.asAlgebraHom uc).baseChange (AlgebraicClosure K')) =
            LinearMap.id := by
        rw [← LinearMap.baseChange_comp]
        have hleft_map : ef.symm.toLinearMap.comp (ρ.ρ.asAlgebraHom uc) = LinearMap.id := by
          ext y
          exact ef.left_inv y
        rw [hleft_map, LinearMap.baseChange_id]
      exact LinearMap.congr_fun hcomp x
    exact hleft.injective
  have hall : ∀ k, k ∈ O := by
    intro k
    by_contra hk_not_mem
    obtain ⟨jk, hjk⟩ := hS_nonempty k
    rcases (hS k jk).1 hjk with ⟨ek⟩
    have hψk_zero :
        (ψ k).ρ.asAlgebraHom
            (MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) u) =
          0 := by
      simpa [hu_map_center, p] using
        orbitProjector_sum_action_eq_zero_of_not_mem_local
          (G := G) (ψ := ψ) (O := O) hψ_pairwise hψ_irr hk_not_mem
    have hσjk_zero :
        ((σ jk).toRepresentation).asAlgebraHom
            (MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) u) =
          0 := by
      exact
        action_eq_zero_of_equiv_local
          (G := G) ek.symm
          (MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) u)
          hψk_zero
    have hσjk_inj :
        Function.Injective
          (((σ jk).toRepresentation).asAlgebraHom
            (MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) u)) := by
      intro x y hxy
      apply Subtype.ext
      apply hρext_inj
      calc
        ((Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ).asAlgebraHom
            (MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) u))
            x
            =
          ((((σ jk).toRepresentation).asAlgebraHom
              (MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) u))
            x : _) := by
              symm
              exact
                subrepresentation_asAlgebraHom_apply_block_local
                  (Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ)
                  (σ jk)
                  (MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) u)
                  x
        _ =
          ((((σ jk).toRepresentation).asAlgebraHom
              (MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) u))
            y : _) := by
              exact congrArg Subtype.val hxy
        _ =
          ((Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ).asAlgebraHom
            (MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) u))
            y := by
              exact
                subrepresentation_asAlgebraHom_apply_block_local
                  (Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ)
                  (σ jk)
                  (MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) u)
                  y
    letI : Nontrivial ↥((σ jk).toSubmodule) :=
      irreducible_rep_nontrivial_block_local (G := G) ((σ jk).toRepresentation)
    obtain ⟨x, hx⟩ := exists_ne (0 : ↥((σ jk).toSubmodule))
    have hx_eq : x = 0 := by
      apply hσjk_inj
      simpa [hσjk_zero] using
        (show (((σ jk).toRepresentation).asAlgebraHom
            (MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) u)) x =
              (((σ jk).toRepresentation).asAlgebraHom
                (MonoidAlgebra.mapRingHom G (algebraMap K' (AlgebraicClosure K')) u)) 0 by
          simp [hσjk_zero])
    exact hx hx_eq
  have hcover :
      ∀ j : ι,
        ∃ (σ' : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')) (τ : Equiv.Perm ι),
          (∀ k : ι, ∀ g : G, σ' ((ψ k).ρ.character g) = (ψ (τ k)).ρ.character g) ∧
          τ i0 = j := by
    intro j
    exact (hmem_O j).mp (hall j)
  exact ⟨i0, hcover⟩

/-- Helper for Exercise 12-12.2-6: descending a Galois-orbit projector from the scalar-extension
packet should force the visible quotient coefficients to be constant. -/
theorem orbit_block_projector_descends_to_source_forces_common_coeff_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [ρ.ρ.IsIrreducible]
    [FiniteDimensional K' ρ]
    (n : ℕ+)
    (hcanon : ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) ∈ R̄[K'](G))
    (hmax :
      ∀ d' : ℕ+, ((((d' : ℕ) : K')⁻¹) • ρ.ρ.character) ∈ R̄[K'](G) → d' ≤ n)
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
  obtain ⟨i0, hcover⟩ :=
    full_transport_cover_of_irreducible_source_local
      (G := G) (ρ := ρ) (n := n) hcanon hmax
      (ψ := ψ) (d := d) (e := e)
      hd_pos hψ_fd hψ_pairwise hψ_irr hpacket he hscaled_packet
  exact
    common_coeff_of_full_transport_image_local
      (G := G) (ρ := ρ) (n := n) (ψ := ψ) (d := d) (e := e)
      hd_pos hψ_fd hψ_pairwise hψ_irr he hscaled_packet i0 hcover

/-- Helper for Exercise 12-12.2-6: Schur's division algebra of an irreducible source
representation has dimension dividing the source degree. -/
private theorem sourceIntertwining_finrank_dvd_finrank_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [ρ.ρ.IsIrreducible]
    [FiniteDimensional K' ρ] :
    Module.finrank K' (Representation.IntertwiningMap ρ.ρ ρ.ρ) ∣
      Module.finrank K' ρ := by
  letI : Module (MonoidAlgebra K' G) ρ.ρ.asModule :=
    ρ.ρ.instModuleMonoidAlgebraAsModule
  let D := Module.End (MonoidAlgebra K' G) ρ.ρ.asModule
  have hsimple :
      @IsSimpleModule (MonoidAlgebra K' G) _ ρ.ρ.asModule _
        ρ.ρ.instModuleMonoidAlgebraAsModule := by
    exact (Representation.irreducible_iff_isSimpleModule_asModule (ρ := ρ.ρ)).mp inferInstance
  letI :
      @IsSimpleModule (MonoidAlgebra K' G) _ ρ.ρ.asModule _
        ρ.ρ.instModuleMonoidAlgebraAsModule := hsimple
  letI : DecidableEq D := Classical.decEq D
  letI : DivisionRing D :=
    @Module.End.instDivisionRing (MonoidAlgebra K' G) _ ρ.ρ.asModule _
      ρ.ρ.instModuleMonoidAlgebraAsModule (Classical.decEq D) hsimple
  let instDModule : Module D ρ.ρ.asModule := by
    dsimp [D]
    exact
      { smul := fun f x ↦ f x
        one_smul := by intro x; rfl
        mul_smul := by intro f g x; rfl
        smul_zero := by intro f; exact map_zero f
        smul_add := by intro f x y; exact map_add f x y
        zero_smul := by intro x; rfl
        add_smul := by intro f g x; rfl }
  letI : Module D ρ.ρ.asModule := instDModule
  letI : Algebra K' D := by
    dsimp [D]
    infer_instance
  letI : Module K' D := Algebra.toModule
  have hD_noeth : IsNoetherianRing D := by
    rw [isNoetherianRing_iff_ideal_fg]
    intro I
    by_cases hbot : I = ⊥
    · simpa [hbot] using (Submodule.fg_bot : (⊥ : Ideal D).FG)
    · have hex : ∃ x : D, x ∈ I ∧ x ≠ 0 := by
        by_contra h
        push Not at h
        apply hbot
        ext x
        constructor
        · intro hx
          rw [Submodule.mem_bot]
          exact h x hx
        · intro hx
          rw [Submodule.mem_bot] at hx
          simpa [hx] using (zero_mem I)
      rcases hex with ⟨x, hxI, hxne⟩
      have hone : (1 : D) ∈ I := by
        have hmul : x⁻¹ * x ∈ I := I.mul_mem_left x⁻¹ hxI
        have hxx : x⁻¹ * x = (1 : D) := by
          exact inv_mul_cancel₀ hxne
        exact hxx ▸ hmul
      have htop : I = ⊤ := by
        apply eq_top_iff.mpr
        intro y _hy
        have hyI : y * 1 ∈ I := I.mul_mem_left y hone
        simpa using hyI
      simpa [htop] using (Ideal.fg_top D)
  letI : IsNoetherianRing D := hD_noeth
  letI : StrongRankCondition D := by
    exact IsNoetherianRing.strongRankCondition D
  letI : Module.Free D ρ.ρ.asModule :=
    @Module.Free.of_divisionRing D ρ.ρ.asModule _ _ instDModule
  have htower : IsScalarTower K' D ρ.ρ.asModule := by
    constructor
    intro r d x
    rfl
  letI : IsScalarTower K' D ρ.ρ.asModule := htower
  letI : Module.Free K' D :=
    @Module.Free.of_divisionRing K' D _ _ (Algebra.toModule : Module K' D)
  have hmul : Module.finrank K' D * Module.finrank D ρ.ρ.asModule =
      Module.finrank K' ρ.ρ.asModule :=
    @Module.finrank_mul_finrank K' D ρ.ρ.asModule _ _ _
      (Algebra.toModule : Module K' D) instDModule _ htower _ _ _ _
  have hdvdD : Module.finrank K' D ∣ Module.finrank K' ρ.ρ.asModule :=
    ⟨Module.finrank D ρ.ρ.asModule, hmul.symm⟩
  have hD_eq :
      Module.finrank K' (Representation.IntertwiningMap ρ.ρ ρ.ρ) = Module.finrank K' D := by
    exact (Representation.IntertwiningMap.equivAlgEnd (ρ := ρ.ρ)).toLinearEquiv.finrank_eq
  simpa [D, hD_eq] using hdvdD

/-- Helper for Exercise 12-12.2-6: the self-pairing of the scalar-extension packet computes the
source Schur-division-algebra dimension as the sum of squared visible multiplicities. -/
private theorem sourceIntertwining_finrank_eq_packet_sq_sum_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [FiniteDimensional K' ρ]
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (d : ι → ℕ)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (hpacket :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character =
        ∑ i, (d i : AlgebraicClosure K') • (ψ i).ρ.character) :
    Module.finrank K' (Representation.IntertwiningMap ρ.ρ ρ.ρ) =
      ∑ i, d i * d i := by
  classical
  have hcardK : (Nat.card G : K') ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : K') := invertibleOfNonzero hcardK
  have hcardC : (Nat.card G : AlgebraicClosure K') ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : AlgebraicClosure K') := invertibleOfNonzero hcardC
  let χ : G → AlgebraicClosure K' :=
    ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character
  have hpair_source :
      ⟪ρ.ρ.character, ρ.ρ.character⟫ =
        (Module.finrank K' (Representation.IntertwiningMap ρ.ρ ρ.ρ) : K') := by
    simpa using
      (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
        (K := K') (G := G) (ρ := ρ.ρ) (σ := ρ.ρ))
  have hmap_pair :
      ⟪χ, χ⟫ =
        (Module.finrank K' (Representation.IntertwiningMap ρ.ρ ρ.ρ) :
          AlgebraicClosure K') := by
    calc
      ⟪χ, χ⟫ =
          algebraMap K' (AlgebraicClosure K') ⟪ρ.ρ.character, ρ.ρ.character⟫ := by
            simp [χ, Representation.groupFunctionPairingOverField, map_mul]
      _ = (Module.finrank K' (Representation.IntertwiningMap ρ.ρ ρ.ρ) :
          AlgebraicClosure K') := by
            rw [hpair_source]
            simp
  have hcoeff :
      ∀ j,
        ⟪χ, (ψ j).ρ.character⟫ = (d j : AlgebraicClosure K') := by
    intro j
    simpa [χ] using
      packet_constituent_pairing_eq_multiplicity_universe_local
        (G := G) (ρ := ρ) (ψ := ψ) (d := d)
        hψ_fd hψ_pairwise hψ_irr hpacket j
  have hpair_sum :
      ⟪χ, χ⟫ = ∑ i, (d i : AlgebraicClosure K') * (d i : AlgebraicClosure K') := by
    calc
      ⟪χ, χ⟫ =
          ⟪∑ i, (d i : AlgebraicClosure K') • (ψ i).ρ.character, χ⟫ := by
            change
              ⟪((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
                    ρ.ρ.character, χ⟫ =
                ⟪∑ i, (d i : AlgebraicClosure K') • (ψ i).ρ.character, χ⟫
            rw [hpacket]
      _ = ∑ i, (d i : AlgebraicClosure K') * ⟪(ψ i).ρ.character, χ⟫ := by
            simpa using
              groupFunctionPairing_sum_field_smul_left_universe_local
                (K' := K') (G := G) (s := Finset.univ)
                (a := fun i ↦ (d i : AlgebraicClosure K'))
                (χ := fun i ↦ (ψ i).ρ.character) χ
      _ = ∑ i, (d i : AlgebraicClosure K') * (d i : AlgebraicClosure K') := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Representation.groupFunctionPairing_comm]
            rw [hcoeff i]
  have hcast :
      (Module.finrank K' (Representation.IntertwiningMap ρ.ρ ρ.ρ) : AlgebraicClosure K') =
        ((∑ i, d i * d i : ℕ) : AlgebraicClosure K') := by
    calc
      (Module.finrank K' (Representation.IntertwiningMap ρ.ρ ρ.ρ) :
          AlgebraicClosure K') = ⟪χ, χ⟫ := hmap_pair.symm
      _ = ∑ i, (d i : AlgebraicClosure K') * (d i : AlgebraicClosure K') := hpair_sum
      _ = ((∑ i, d i * d i : ℕ) : AlgebraicClosure K') := by
            simp
  exact Nat.cast_injective hcast

/-- Helper for Exercise 12-12.2-6: a full base-field transport cover makes all visible
constituent degrees equal. -/
private theorem visible_degrees_eq_of_full_transport_cover_local
    {K' : Type v} [Field K'] [CharZero K']
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i))
    (i0 : ι)
    (hcover :
      ∀ j : ι,
        ∃ (σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')) (τ : Equiv.Perm ι),
          (∀ k : ι, ∀ g : G, σ ((ψ k).ρ.character g) = (ψ (τ k)).ρ.character g) ∧
          τ i0 = j) :
    ∀ j, Module.finrank (AlgebraicClosure K') (ψ j) =
      Module.finrank (AlgebraicClosure K') (ψ i0) := by
  intro j
  obtain ⟨σ, τ, hchar, hτ⟩ := hcover j
  letI : FiniteDimensional (AlgebraicClosure K') (ψ i0) := hψ_fd i0
  letI : FiniteDimensional (AlgebraicClosure K') (ψ j) := hψ_fd j
  letI : FiniteDimensional (AlgebraicClosure K') (ψ (τ i0)) := hψ_fd (τ i0)
  have hcast :
      (Module.finrank (AlgebraicClosure K') (ψ i0) : AlgebraicClosure K') =
        (Module.finrank (AlgebraicClosure K') (ψ j) : AlgebraicClosure K') := by
    calc
      (Module.finrank (AlgebraicClosure K') (ψ i0) : AlgebraicClosure K') =
          σ ((Module.finrank (AlgebraicClosure K') (ψ i0) : AlgebraicClosure K')) := by
            simp
      _ = σ ((ψ i0).ρ.character 1) := by
            simp [Representation.char_one]
      _ = (ψ (τ i0)).ρ.character 1 := hchar i0 1
      _ = (Module.finrank (AlgebraicClosure K') (ψ j) : AlgebraicClosure K') := by
            rw [hτ]
            simp [Representation.char_one]
  exact Nat.cast_injective hcast.symm

/-- Helper for Exercise 12-12.2-6: after the quotient coefficients collapse to `1`, the canonical
denominator divides the common degree of the visible algebraic-closure constituents. -/
private theorem canonical_denominator_dvd_visible_degree_of_full_transport_cover_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [ρ.ρ.IsIrreducible]
    [FiniteDimensional K' ρ]
    (n : ℕ+)
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
    (hcoeff_one : ∀ i, e i = 1)
    (i0 : ι)
    (hcover :
      ∀ j : ι,
        ∃ (σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')) (τ : Equiv.Perm ι),
          (∀ k : ι, ∀ g : G, σ ((ψ k).ρ.character g) = (ψ (τ k)).ρ.character g) ∧
          τ i0 = j) :
    (n : ℕ) ∣ Module.finrank (AlgebraicClosure K') (ψ i0) := by
  classical
  let r : ℕ := Module.finrank (AlgebraicClosure K') (ψ i0)
  have hd_eq : ∀ i, d i = (n : ℕ) := by
    intro i
    calc
      d i = (n : ℕ) * e i := he i
      _ = (n : ℕ) * 1 := by rw [hcoeff_one i]
      _ = (n : ℕ) := Nat.mul_one _
  have hdeg_eq :
      ∀ j, Module.finrank (AlgebraicClosure K') (ψ j) = r := by
    intro j
    simpa [r] using
      visible_degrees_eq_of_full_transport_cover_local
        (G := G) (ψ := ψ) hψ_fd i0 hcover j
  have hend_eq :
      Module.finrank K' (Representation.IntertwiningMap ρ.ρ ρ.ρ) =
        Fintype.card ι * ((n : ℕ) * (n : ℕ)) := by
    calc
      Module.finrank K' (Representation.IntertwiningMap ρ.ρ ρ.ρ)
          = ∑ i, d i * d i := by
              exact
                sourceIntertwining_finrank_eq_packet_sq_sum_local
                  (G := G) (ρ := ρ) (ψ := ψ) (d := d)
                  hψ_fd hψ_pairwise hψ_irr hpacket
      _ = ∑ _i : ι, (n : ℕ) * (n : ℕ) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              simp [hd_eq i]
      _ = Fintype.card ι * ((n : ℕ) * (n : ℕ)) := by
              simp
  have hsource_eq :
      Module.finrank K' ρ = Fintype.card ι * ((n : ℕ) * r) := by
    have hdegree_cast :
        (Module.finrank K' ρ : AlgebraicClosure K') =
          ∑ i, (d i : AlgebraicClosure K') *
            Module.finrank (AlgebraicClosure K') (ψ i) := by
      have hpoint := congrFun hpacket 1
      simp only [smul_eq_mul] at hpoint
      simpa using hpoint
    have hnat :
        Module.finrank K' ρ =
          ∑ i, d i * Module.finrank (AlgebraicClosure K') (ψ i) := by
      apply Nat.cast_injective (R := AlgebraicClosure K')
      calc
        (Module.finrank K' ρ : AlgebraicClosure K') =
            ∑ i, (d i : AlgebraicClosure K') *
              Module.finrank (AlgebraicClosure K') (ψ i) := hdegree_cast
        _ = ((∑ i, d i * Module.finrank (AlgebraicClosure K') (ψ i) : ℕ) :
            AlgebraicClosure K') := by
              simp
    calc
      Module.finrank K' ρ =
          ∑ i, d i * Module.finrank (AlgebraicClosure K') (ψ i) := hnat
      _ = ∑ _i : ι, (n : ℕ) * r := by
              refine Finset.sum_congr rfl ?_
              intro i _
              simp [hd_eq i, hdeg_eq i]
      _ = Fintype.card ι * ((n : ℕ) * r) := by
              simp
  have hdvd_end_source :
      Module.finrank K' (Representation.IntertwiningMap ρ.ρ ρ.ρ) ∣
        Module.finrank K' ρ :=
    sourceIntertwining_finrank_dvd_finrank_local (G := G) ρ
  have hdvd :
      Fintype.card ι * ((n : ℕ) * (n : ℕ)) ∣
        Fintype.card ι * ((n : ℕ) * r) := by
    simpa [hend_eq, hsource_eq] using hdvd_end_source
  have hcard_pos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i0⟩
  have hcancel_card :
      (n : ℕ) * (n : ℕ) ∣ (n : ℕ) * r :=
    Nat.dvd_of_mul_dvd_mul_left hcard_pos hdvd
  have hcancel_n : (n : ℕ) ∣ r :=
    Nat.dvd_of_mul_dvd_mul_left n.pos hcancel_card
  simpa [r] using hcancel_n

/-- Helper for Exercise 12-12.2-6: after the quotient coefficients collapse to `1`, descending a
single isotypic block to the stabilizer fixed field should force each constituent degree to be a
multiple of the canonical denominator. -/
private theorem visible_packet_multiplicity_eq_denominator_of_coeffOne_block_local
    (n : ℕ+)
    {ι : Type*}
    (d e : ι → ℕ)
    (he : ∀ i, d i = (n : ℕ) * e i)
    (hcoeff_one : ∀ i, e i = 1) :
    ∀ i, d i = (n : ℕ) := by
  intro i
  -- Once the quotient coefficient is `1`, the visible multiplicity is exactly the denominator.
  calc
    d i = (n : ℕ) * e i := he i
    _ = (n : ℕ) * 1 := by rw [hcoeff_one i]
    _ = (n : ℕ) := by simp

/-- Helper for Exercise 12-12.2-6: after the quotient coefficients collapse to `1`, the visible
packet multiplicities are automatically positive. -/
private theorem visible_packet_multiplicity_pos_of_coeffOne_block_local
    (n : ℕ+)
    {ι : Type*}
    (d e : ι → ℕ)
    (he : ∀ i, d i = (n : ℕ) * e i)
    (hcoeff_one : ∀ i, e i = 1) :
    ∀ i, 0 < d i := by
  intro i
  -- Replace `d i` by the canonical denominator itself and read off positivity from `n`.
  have hdi :
      d i = (n : ℕ) :=
    visible_packet_multiplicity_eq_denominator_of_coeffOne_block_local
      (n := n) (d := d) (e := e) he hcoeff_one i
  simpa [hdi] using n.pos

/-- Helper for Exercise 12-12.2-6: after the quotient coefficients collapse to `1`, the honest
fiber of a chosen visible constituent is nonempty and its total degree is exactly
`n * dim ψᵢ₀`. -/
private theorem selectedVisibleConstituentFiberDegreeSetup_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [FiniteDimensional K' ρ]
    (n : ℕ+)
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
    (hcoeff_one : ∀ i, e i = 1)
    (i0 : ι) :
    ∃ (a : ℕ) (σ : Fin a → Subrepresentation
        (Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ))
      (S : ι → Finset (Fin a)) (j0 : Fin a),
      j0 ∈ S i0 ∧
      (∀ i j, j ∈ S i ↔ Nonempty (((σ j).toRepresentation).Equiv (ψ i).ρ)) ∧
      Finset.sum (S i0)
          (fun j ↦ Module.finrank (AlgebraicClosure K') ↥((σ j).toSubmodule)) =
        (n : ℕ) * Module.finrank (AlgebraicClosure K') (ψ i0) := by
  obtain ⟨a, σ, S, _hinternal, _hσchar, _hσirr, hS, hS_nonempty, _hcanonical_fiber, hcard⟩ :=
    canonicalMultipleHonestFiberCardSetup_local
      (G := G) (ρ := ρ) (n := n) (ψ := ψ) (d := d) (e := e)
      hψ_fd hψ_pairwise hψ_irr hpacket he hcoeff_one
  obtain ⟨j0, hj0_mem⟩ := hS_nonempty i0
  refine ⟨a, σ, S, j0, hj0_mem, hS, ?_⟩
  -- Every summand in the chosen honest fiber has the same degree as `ψ i0`, and the fiber has
  -- exactly `n` summands.
  calc
    Finset.sum (S i0)
        (fun j ↦ Module.finrank (AlgebraicClosure K') ↥((σ j).toSubmodule)) =
      (S i0).card * Module.finrank (AlgebraicClosure K') (ψ i0) := by
        exact
          honestFiber_finrank_sum_eq_card_mul_constituent_local
            (G := G) (ρ := ρ) (ψ := ψ) (σ := σ) (S := S) hS i0
    _ = (n : ℕ) * Module.finrank (AlgebraicClosure K') (ψ i0) := by
        simp [hcard i0]

/-- Helper for Exercise 12-12.2-6: after the quotient coefficients collapse to `1`, Serre's
division-algebra degree comparison forces the canonical denominator to divide a selected visible
constituent degree. -/
private theorem selectedVisibleConstituentDenominatorDvdDegree_local
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
    (hcoeff_one : ∀ i, e i = 1)
    (i0 : ι) :
    (n : ℕ) ∣ Module.finrank (AlgebraicClosure K') (ψ i0) := by
  have hd_pos : ∀ i, 0 < d i := by
    exact
      visible_packet_multiplicity_pos_of_coeffOne_block_local
        (n := n) (d := d) (e := e) he hcoeff_one
  obtain ⟨iBase, hcoverBase⟩ :=
    full_transport_cover_of_irreducible_source_local
      (G := G) (ρ := ρ) (n := n) hcanon hmax
      (ψ := ψ) (d := d) (e := e)
      hd_pos hψ_fd hψ_pairwise hψ_irr hpacket he hscaled_packet
  have hdeg_eq :
      Module.finrank (AlgebraicClosure K') (ψ i0) =
        Module.finrank (AlgebraicClosure K') (ψ iBase) :=
    visible_degrees_eq_of_full_transport_cover_local
      (G := G) (ψ := ψ) hψ_fd iBase hcoverBase i0
  have hn_dvd_base :
      (n : ℕ) ∣ Module.finrank (AlgebraicClosure K') (ψ iBase) :=
    canonical_denominator_dvd_visible_degree_of_full_transport_cover_local
      (G := G) (ρ := ρ) (n := n)
      (ψ := ψ) (d := d) (e := e)
      hψ_fd hψ_pairwise hψ_irr hpacket he hcoeff_one iBase hcoverBase
  simpa [hdeg_eq] using hn_dvd_base

/-- Helper for Exercise 12-12.2-6: after the quotient coefficients collapse to `1`, the canonical
denominator divides every visible constituent degree. -/
theorem isotypicBlockProjectorDescendsToStabilizer_forcesDenominatorDegree_local
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
  intro i
  exact
    selectedVisibleConstituentDenominatorDvdDegree_local
      (G := G) (ρ := ρ) (n := n) hcanon hmax
      (ψ := ψ) (d := d) (e := e)
      hψ_fd hψ_pairwise hψ_irr hpacket he hscaled_packet hcoeff_one i

end FieldPart

end Exercise_12_12_2_6

end Representation
