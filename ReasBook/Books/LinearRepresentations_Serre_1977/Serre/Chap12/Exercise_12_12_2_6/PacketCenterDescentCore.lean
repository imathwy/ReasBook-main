import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap02.Proposition_2_2_2_1
import LinearRepresentations_Serre_1977.Serre.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Serre.Chap06.Corollary_6_6_5_4
import LinearRepresentations_Serre_1977.Serre.Chap06.Proposition_6_6_5_5
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_3.API
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.CharacterBasisCoefficients
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.ComplexMinimalRealization
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.FieldDenominatorDescent
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.FieldTensorCenterBridge
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.ScalarExtensionConstituents
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.ScalarExtensionPackets
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.ScalarExtensionPairing
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_2_1

noncomputable section

open scoped BigOperators
open scoped Representation
open scoped Representation.ExternalTensor
open scoped SubgroupInduction

universe u v w

namespace Representation

open CategoryTheory
open Exercise_12_12_2_6

attribute [local instance] ULift.algebra'

section FieldPart

variable {K : Type u} [Field K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]

local instance instFintypeGExercise_12_12_2_6_packet_center_core : Fintype G := Fintype.ofFinite G

/-- Helper for Exercise 12-12.2-6: the coefficient of the primitive central idempotent attached
to one algebraic-closure constituent is the degree-weighted inverse-character value appearing in
Serre's projector formula. -/
def primitive_central_idempotent_coefficient_packet_local
    {K' : Type v} [Field K'] [CharZero K']
    (V : Rep.{max u v} (AlgebraicClosure K') G)
    [FiniteDimensional (AlgebraicClosure K') V] :
    G → AlgebraicClosure K' :=
  fun g ↦
    ((Module.finrank (AlgebraicClosure K') V : AlgebraicClosure K') / Nat.card G) *
      V.ρ.character g⁻¹

/-- Helper for Exercise 12-12.2-6: a packet permutation that transports constituent characters
also transports the explicit primitive-central-idempotent coefficient formula. -/
theorem
    primitive_central_idempotent_coefficient_packet_aut_eq_of_character_transport_local
    {K' : Type v} [Field K'] [CharZero K']
    {ι : Type*}
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i))
    (σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K'))
    (τ : Equiv.Perm ι)
    (hchar : ∀ i : ι, ∀ g : G, σ ((ψ i).ρ.character g) = (ψ (τ i)).ρ.character g) :
    ∀ i : ι, ∀ g : G,
      σ (primitive_central_idempotent_coefficient_packet_local (G := G) (V := ψ i) g) =
        primitive_central_idempotent_coefficient_packet_local (G := G) (V := ψ (τ i)) g := by
  intro i g
  letI : FiniteDimensional (AlgebraicClosure K') (ψ i) := hψ_fd i
  letI : FiniteDimensional (AlgebraicClosure K') (ψ (τ i)) := hψ_fd (τ i)
  have hdim_cast :
      ((Module.finrank (AlgebraicClosure K') (ψ i) : ℕ) : AlgebraicClosure K') =
        (Module.finrank (AlgebraicClosure K') (ψ (τ i)) : ℕ) := by
    -- Evaluate the transported character at `1` to identify the two constituent degrees.
    simpa [Representation.char_one] using hchar i 1
  have hdim :
      Module.finrank (AlgebraicClosure K') (ψ i) =
        Module.finrank (AlgebraicClosure K') (ψ (τ i)) := by
    exact_mod_cast hdim_cast
  have hchar_inv := hchar i g⁻¹
  -- Apply the automorphism to Serre's explicit coefficient formula and rewrite both factors.
  dsimp [primitive_central_idempotent_coefficient_packet_local]
  calc
    σ
        (((Module.finrank (AlgebraicClosure K') (ψ i) : AlgebraicClosure K') / Nat.card G) *
          (ψ i).ρ.character g⁻¹)
        =
          σ ((Module.finrank (AlgebraicClosure K') (ψ i) : AlgebraicClosure K') / Nat.card G) *
            σ ((ψ i).ρ.character g⁻¹) := by
              simp [map_mul]
    _ =
          (((Module.finrank (AlgebraicClosure K') (ψ (τ i)) : AlgebraicClosure K') /
              Nat.card G) *
            (ψ (τ i)).ρ.character g⁻¹) := by
              simp [hchar_inv, hdim]

/-- Helper for Exercise 12-12.2-6: if the honest packet permutation fixes a chosen constituent
for every automorphism in a stabilizer, then the corresponding primitive-central-idempotent
descends coefficientwise to the stabilizer fixed field. -/
theorem
    primitive_central_idempotent_descends_to_fixedField_of_packet_transport_fix_local
    {K' : Type v} [Field K'] [CharZero K']
    {ι : Type*}
    (H : Subgroup ((AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')))
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i))
    (perm :
      ∀ σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K'), σ ∈ H → Equiv.Perm ι)
    (hchar :
      ∀ (σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')) (hσ : σ ∈ H)
        (i : ι) (g : G),
          σ ((ψ i).ρ.character g) = (ψ (perm σ hσ i)).ρ.character g)
    (i : ι)
    (hfix :
      ∀ (σ : (AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K')) (hσ : σ ∈ H),
        perm σ hσ i = i) :
    ∃ p0 : MonoidAlgebra (IntermediateField.fixedField H) G,
      ∀ g : G,
        ((p0 g : IntermediateField.fixedField H) : AlgebraicClosure K') =
          primitive_central_idempotent_coefficient_packet_local (G := G) (V := ψ i) g := by
  -- Route correction: this projector-descent API must be available before the owner file, so we
  -- descend the single constituent directly from the packet transport data in the shared core.
  have hcoeff_fixed :
      ∀ σ ∈ H, ∀ g : G,
        σ (primitive_central_idempotent_coefficient_packet_local (G := G) (V := ψ i) g) =
          primitive_central_idempotent_coefficient_packet_local (G := G) (V := ψ i) g := by
    intro σ hσ g
    -- The stabilizer hypothesis turns the transported packet constituent back into the original
    -- one, so the explicit primitive-central-idempotent coefficient is fixed.
    simpa [hfix σ hσ] using
      primitive_central_idempotent_coefficient_packet_aut_eq_of_character_transport_local
        (G := G) (ψ := ψ) (hψ_fd := hψ_fd) (σ := σ) (τ := perm σ hσ)
        (hchar := fun j g' ↦ hchar σ hσ j g') i g
  have hcoeff_mem :
      ∀ g : G,
        primitive_central_idempotent_coefficient_packet_local (G := G) (V := ψ i) g ∈
          IntermediateField.fixedField H := by
    intro g
    -- Fixed-field membership is exactly coefficientwise invariance under the stabilizer.
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    exact hcoeff_fixed σ hσ g
  let p0 : MonoidAlgebra (IntermediateField.fixedField H) G :=
    Finsupp.equivFunOnFinite.symm
      (fun g : G ↦
        ⟨primitive_central_idempotent_coefficient_packet_local (G := G) (V := ψ i) g,
          hcoeff_mem g⟩)
  -- The descended group-algebra element has exactly the same coefficients after coercion.
  refine ⟨p0, ?_⟩
  intro g
  rfl

/-- Helper for Exercise 12-12.2-6: comparing the visible packet with an honest internal
decomposition of `Representation.scalarExtension ρ` identifies each visible multiplicity block as
the sum of the internal irreducible constituents in that isomorphism class. -/
theorem actual_scalar_extension_isotypic_fiber_character_core_local
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
    ∃ (a : ℕ) (σ : Fin a → Subrepresentation (Representation.scalarExtension
        (k := AlgebraicClosure K') ρ.ρ)) (S : ι → Finset (Fin a)),
      DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule) ∧
      (Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ).character =
        ∑ j, ((σ j).toRepresentation).character ∧
      (∀ j, ((σ j).toRepresentation).IsIrreducible) ∧
      (∀ i j, j ∈ S i ↔ Nonempty (((σ j).toRepresentation).Equiv (ψ i).ρ)) ∧
      ∀ i,
        Finset.sum
            (S i)
            (fun j ↦ ((σ j).toRepresentation).character) =
            (d i : AlgebraicClosure K') • (ψ i).ρ.character := by
  classical
  obtain ⟨a, σ, hinternal, hσchar, hσirr⟩ :=
    Exercise_12_12_2_6.scalar_extension_internal_irreducible_subrepresentations_fin_local
      (G := G) (K := K') (L := AlgebraicClosure K') ρ
  let S : ι → Finset (Fin a) := fun i ↦ Finset.univ.filter fun j ↦
    Nonempty (((σ j).toRepresentation).Equiv (ψ i).ρ)
  have hcard_ne : (Nat.card G : AlgebraicClosure K') ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : AlgebraicClosure K') := invertibleOfNonzero hcard_ne
  refine ⟨a, σ, S, hinternal, hσchar, hσirr, ?_, ?_⟩
  · intro i j
    dsimp [S]
    simp
  intro i
  let Si : Finset (Fin a) := S i
  letI : FiniteDimensional (AlgebraicClosure K') (ψ i) := hψ_fd i
  letI : (ψ i).ρ.IsIrreducible := hψ_irr i
  have hself_pair :
      ⟪(ψ i).ρ.character, (ψ i).ρ.character⟫ = (1 : AlgebraicClosure K') := by
    have hfinrank :
        Module.finrank (AlgebraicClosure K')
            (Representation.IntertwiningMap (ψ i).ρ (ψ i).ρ) = 1 := by
      -- Over an algebraically closed field, Schur's lemma makes the self-intertwining space
      -- one-dimensional.
      simpa using
        Representation.IsIrreducible.finrank_intertwiningMap_self (ρ := (ψ i).ρ)
    simpa [hfinrank] using
      (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
        (K := AlgebraicClosure K') (G := G) (ρ := (ψ i).ρ) (σ := (ψ i).ρ))
  have hpair_visible :
      ⟪(Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ).character,
          (ψ i).ρ.character⟫ = (d i : AlgebraicClosure K') := by
    -- First rewrite the actual scalar-extension character to the visible packet character.
    calc
      ⟪(Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ).character,
          (ψ i).ρ.character⟫
          =
            ⟪((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character,
              (ψ i).ρ.character⟫ := by
                rw [scalarExtension_character_eq_map_algClosure_local (G := G) (ρ := ρ)]
      _ = (d i : AlgebraicClosure K') := by
            exact
              packet_constituent_pairing_eq_multiplicity_universe_local
                (G := G) (ρ := ρ) (ψ := ψ) (d := d)
                hψ_fd hψ_pairwise hψ_irr hpacket i
  have hpair_internal :
      ⟪(Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ).character,
          (ψ i).ρ.character⟫ = (Si.card : AlgebraicClosure K') := by
    -- Pairing the honest internal decomposition with `ψ i` keeps only the summands isomorphic
    -- to `ψ i`, each contributing exactly `1`.
    calc
      ⟪(Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ).character,
          (ψ i).ρ.character⟫
          = ⟪∑ j, ((σ j).toRepresentation).character, (ψ i).ρ.character⟫ := by
              rw [hσchar]
      _ = ∑ j, ⟪((σ j).toRepresentation).character, (ψ i).ρ.character⟫ := by
            simpa using
              groupFunctionPairing_sum_field_smul_left_universe_local
                (K' := K') (G := G) (s := Finset.univ)
                (a := fun _ : Fin a ↦ (1 : AlgebraicClosure K'))
                (χ := fun j ↦ ((σ j).toRepresentation).character)
                ((ψ i).ρ.character)
      _ = ∑ j, if Nonempty (((σ j).toRepresentation).Equiv (ψ i).ρ)
            then (1 : AlgebraicClosure K') else 0 := by
            refine Finset.sum_congr rfl ?_
            intro j _
            letI : ((σ j).toRepresentation).IsIrreducible := hσirr j
            letI : FiniteDimensional (AlgebraicClosure K') ↥((σ j).toSubmodule) :=
              Representation.IsIrreducible.finiteDimensional_of_finite
                (ρ := (σ j).toRepresentation)
            by_cases hIso : Nonempty (((σ j).toRepresentation).Equiv (ψ i).ρ)
            · have hIso' : Nonempty (((σ j).toRepresentation).Equiv (ψ i).ρ) := hIso
              rcases hIso' with ⟨e⟩
              have hpair_eq_one :
                  ⟪((σ j).toRepresentation).character, (ψ i).ρ.character⟫ =
                    (1 : AlgebraicClosure K') := by
                calc
                  ⟪((σ j).toRepresentation).character, (ψ i).ρ.character⟫
                      = ⟪(ψ i).ρ.character, (ψ i).ρ.character⟫ := by
                          simpa [Representation.char_iso e]
                  _ = (1 : AlgebraicClosure K') := hself_pair
              simp [hIso, hpair_eq_one]
            · have hpair_zero :
                  ⟪((σ j).toRepresentation).character, (ψ i).ρ.character⟫ =
                    (0 : AlgebraicClosure K') := by
                exact
                  Representation.groupFunctionPairingOverField_character_eq_zero_of_not_isomorphic
                    (K := AlgebraicClosure K') (G := G)
                    (ρ := (σ j).toRepresentation) (σ := (ψ i).ρ) hIso
              simp [hIso, hpair_zero]
      _ = (Si.card : AlgebraicClosure K') := by
            simp [Si, S]
  have hcount : d i = Si.card := by
    have hcount_cast : (d i : AlgebraicClosure K') = (Si.card : AlgebraicClosure K') := by
      exact hpair_visible.symm.trans hpair_internal
    exact Nat.cast_injective hcount_cast
  -- Replace the visible multiplicity by the cardinality of the actual fiber and then collapse the
  -- fiber sum to a constant character over that isomorphism class.
  ext g
  calc
    (Finset.sum Si fun j ↦ ((σ j).toRepresentation).character) g
        = Finset.sum Si (fun j ↦ ((σ j).toRepresentation).character g) := by
            simp
    _ = Finset.sum Si (fun _j ↦ (ψ i).ρ.character g) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hj_iso : Nonempty (((σ j).toRepresentation).Equiv (ψ i).ρ) := by
            simpa [Si, S] using hj
          rcases hj_iso with ⟨e⟩
          simpa using congrArg (fun χ : G → AlgebraicClosure K' ↦ χ g)
            (Representation.char_iso e)
    _ = (Si.card : AlgebraicClosure K') * (ψ i).ρ.character g := by
          simp
    _ = (d i : AlgebraicClosure K') * (ψ i).ρ.character g := by
          simp [hcount]
    _ = ((d i : AlgebraicClosure K') • (ψ i).ρ.character) g := by
          simp [smul_eq_mul]

/-- Helper for Exercise 12-12.2-6: expose the verified honest scalar-extension fiber
decomposition under the theorem-local namespace, so later block-descent arguments can reuse the
same source-faithful packet skeleton without depending on a target-private declaration. -/
theorem Exercise_12_12_2_6.actual_scalar_extension_isotypic_fiber_character_local
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
    ∃ (a : ℕ) (σ : Fin a → Subrepresentation (Representation.scalarExtension
        (k := AlgebraicClosure K') ρ.ρ)) (S : ι → Finset (Fin a)),
      DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule) ∧
      (Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ).character =
        ∑ j, ((σ j).toRepresentation).character ∧
      (∀ j, ((σ j).toRepresentation).IsIrreducible) ∧
      (∀ i j, j ∈ S i ↔ Nonempty (((σ j).toRepresentation).Equiv (ψ i).ρ)) ∧
      ∀ i,
        Finset.sum
            (S i)
            (fun j ↦ ((σ j).toRepresentation).character) =
            (d i : AlgebraicClosure K') • (ψ i).ρ.character := by
  -- Route correction: the honest-fiber decomposition is no longer target-private API.
  -- Re-export the already verified proof under the helper namespace expected by the descent layer.
  exact
    actual_scalar_extension_isotypic_fiber_character_core_local
      (ρ := ρ) (ψ := ψ) (d := d)
      hψ_fd hψ_pairwise hψ_irr hpacket

/-- Helper for Exercise 12-12.2-6: once a scalar-extension representation is already known to be
realizable over the source field, we can unpack explicit source-model data and a scalar-extension
equivalence. -/
theorem exists_source_model_of_isRealizableOver_local
    {K₀ : Type v} [Field K₀]
    {L : Type*} [Field L] [CharZero L] [Algebra K₀ L]
    {V : Type w} [AddCommGroup V] [Module L V]
    (σ : Representation L G V)
    (hσ : Representation.IsRealizableOver K₀ σ) :
    ∃ (W : Type w) (_ : AddCommGroup W) (_ : Module K₀ W) (_ : FiniteDimensional K₀ W)
      (τ : Representation K₀ G W),
      Nonempty ((Representation.scalarExtension (k := L) τ).Equiv σ) := by
  -- This is just the realizability witness from the definition, exposed under a dedicated name
  -- for the later block-descent arguments.
  rcases hσ with ⟨W, hWAdd, hWModule, hWfd, τ, hτ⟩
  exact ⟨W, hWAdd, hWModule, hWfd, τ, hτ⟩

/-- Helper for Exercise 12-12.2-6: after the quotient coefficients collapse to `1`, the honest
internal scalar-extension fibers already have character `n • χ_(ψ i)`. -/
theorem actual_scalar_extension_isotypic_fiber_character_eq_canonical_multiple_core_local
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
    ∃ (a : ℕ) (σ : Fin a → Subrepresentation (Representation.scalarExtension
        (k := AlgebraicClosure K') ρ.ρ)) (S : ι → Finset (Fin a)),
      DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule) ∧
      (Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ).character =
        ∑ j, ((σ j).toRepresentation).character ∧
      (∀ j, ((σ j).toRepresentation).IsIrreducible) ∧
      (∀ i j, j ∈ S i ↔ Nonempty (((σ j).toRepresentation).Equiv (ψ i).ρ)) ∧
      ∀ i,
        Finset.sum
            (S i)
            (fun j ↦ ((σ j).toRepresentation).character) =
          (n : AlgebraicClosure K') • (ψ i).ρ.character := by
  obtain ⟨a, σ, S, hinternal, hσchar, hσirr, hS, hfiber_char⟩ :=
    Exercise_12_12_2_6.actual_scalar_extension_isotypic_fiber_character_local
      (ρ := ρ) (ψ := ψ) (d := d)
      hψ_fd hψ_pairwise hψ_irr hpacket
  refine ⟨a, σ, S, hinternal, hσchar, hσirr, hS, ?_⟩
  intro i
  have hdi : d i = (n : ℕ) := by
    -- Replace the raw multiplicity `d i` by the canonical denominator using `e i = 1`.
    calc
      d i = (n : ℕ) * e i := he i
      _ = (n : ℕ) * 1 := by rw [hcoeff_one i]
      _ = (n : ℕ) := by simp
  -- The honest fiber formula from `actual_scalar_extension_isotypic_fiber_character_local`
  -- now simplifies to the common-coefficient form needed for the stabilizer-field step.
  calc
    Finset.sum
        (S i)
        (fun j ↦ ((σ j).toRepresentation).character)
        = (d i : AlgebraicClosure K') • (ψ i).ρ.character := hfiber_char i
    _ = (n : AlgebraicClosure K') • (ψ i).ρ.character := by
          simp [hdi]

/-- Helper for Exercise 12-12.2-6: once the quotient coefficients have collapsed to `1`, expose
the verified canonical-multiple honest-fiber identity under the theorem-local namespace expected
by the remaining stabilizer descent step. -/
theorem Exercise_12_12_2_6.actual_scalar_extension_isotypic_fiber_character_eq_canonical_multiple_local
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
    ∃ (a : ℕ) (σ : Fin a → Subrepresentation (Representation.scalarExtension
        (k := AlgebraicClosure K') ρ.ρ)) (S : ι → Finset (Fin a)),
      DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule) ∧
      (Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ).character =
        ∑ j, ((σ j).toRepresentation).character ∧
      (∀ j, ((σ j).toRepresentation).IsIrreducible) ∧
      (∀ i j, j ∈ S i ↔ Nonempty (((σ j).toRepresentation).Equiv (ψ i).ρ)) ∧
      ∀ i,
        Finset.sum
            (S i)
            (fun j ↦ ((σ j).toRepresentation).character) =
          (n : AlgebraicClosure K') • (ψ i).ρ.character := by
  -- Route correction: the canonical-multiple fiber identity should be reusable as theorem-local
  -- support data rather than reconstructed ad hoc inside the remaining block-projector proof.
  exact
    actual_scalar_extension_isotypic_fiber_character_eq_canonical_multiple_core_local
      (ρ := ρ) (n := n) (ψ := ψ) (d := d) (e := e)
      hψ_fd hψ_pairwise hψ_irr hpacket he hcoeff_one

end FieldPart

end Representation
