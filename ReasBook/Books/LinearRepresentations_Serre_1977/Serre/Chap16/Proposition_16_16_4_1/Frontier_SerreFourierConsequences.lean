import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.Index
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.CanonicalPacketFrontier
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.Frontier_PacketReindex
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.Frontier_CharZeroSupportedFamily
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.Frontier_AsAlgebraHomTransport
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.Frontier_FiberInternalCoordinate
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.Frontier_FourierOrthogonality
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.Frontier_IntegralFourier

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

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the only missing source
step is the ambient `K`-linear Fourier inversion identity for the simple representation `ρ`
itself. Once this is known, the algebraic-closure statement is the formal scalar-extension wrapper
just above. -/
lemma equalChar_hambient_local
    [CharP K p] [CharZero K]
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule) :
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A K) (L.serre_fourier_element hdefect φ)) =
      (L.toSubmodule_subtype_isBaseChange).endHom φ := by
  -- Route correction: reduce the ambient self-action theorem to the basis-unit owner from the
  -- source Proposition `11`, instead of leaving the whole arbitrary-`φ` statement as one block.
  exact L.integral_fourier_self_action_local (p := p) (ρ := ρ) hdefect φ

/-- Helper for Proposition 16-16.4-1: the equal-characteristic branch of the remaining Fourier
packet argument. The local distinguished-block computation should first identify the ambient
`K`-action of Serre's Fourier element; this lemma then lifts that identity to
`AlgebraicClosure K`. -/
lemma equalChar_algClosure_fourier_action_eq_baseChange
    [CharP K p] [CharZero K]
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule) :
    (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K))
          (L.serre_fourier_element hdefect φ)) =
      LinearMap.baseChange (AlgebraicClosure K)
        ((L.toSubmodule_subtype_isBaseChange).endHom φ) := by
  -- Route correction: the scalar-extension step is formal once the ambient `K`-action equality is
  -- known, so this theorem only consumes the dedicated ambient owner.
  exact
    L.algClosure_fourier_action_eq_baseChange_of_ambient_action_local
      (p := p) (ρ := ρ) hdefect φ
      (L.equalChar_hambient_local (p := p) (ρ := ρ) hdefect φ)

/-- Helper for Proposition 16-16.4-1: the equal-characteristic branch of the remaining Fourier
packet argument. The local distinguished-block computation already identifies the scalar-extended
action of Serre's Fourier element, so this wrapper only performs the descent back to `K` and
reuses the corresponding projector-annihilator statement. -/
lemma equalChar_ambient_action_eq_of_projector_bridge
    [CharP K p] [CharZero K]
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule) :
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A K) (L.serre_fourier_element hdefect φ)) =
      (L.toSubmodule_subtype_isBaseChange).endHom φ := by
  -- Descend the scalar-extension identity from the dedicated equal-characteristic packet theorem.
  exact
    StableLattice.ambient_action_eq_of_algClosure_baseChange_eq_local
      (ρ := ρ)
      (u := L.serre_fourier_element hdefect φ)
      (f := (L.toSubmodule_subtype_isBaseChange).endHom φ)
      (by
        simpa using
          L.equalChar_algClosure_fourier_action_eq_baseChange
            (p := p) (ρ := ρ) hdefect φ)

/-- Helper for Proposition 16-16.4-1: the equal-characteristic branch of the remaining Fourier
packet argument. The local distinguished-block computation already identifies the scalar-extended
action of Serre's Fourier element, so this wrapper only performs the descent back to `K`. -/
lemma equalChar_packet_block_action_eq_transport
    [CharP K p] [CharZero K]
    (hdefect : ρ.HasDefectZero p) :
    ∀ φ : Module.End A L.toSubmodule,
      ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K) (L.serre_fourier_element hdefect φ)) =
        (L.toSubmodule_subtype_isBaseChange).endHom φ := by
  intro φ
  -- Consume the dedicated target-local descent wrapper so the branch theorem only records the
  -- source-level ambient action computation.
  exact
    L.equalChar_ambient_action_eq_of_projector_bridge
      (p := p) (ρ := ρ) hdefect φ

/-- Helper for Proposition 16-16.4-1: the sole remaining source-faithful Fourier inversion step
over `AlgebraicClosure K` identifies the ambient action of the integral Fourier section `u_φ`.
The later kernel and idempotence consequences are now derived formally from this single bridge. -/
lemma algClosure_complete_family_fourier_consequences
    [CharZero K]
    [(@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).IsIrreducible]
    (hdefect : ρ.HasDefectZero p) :
    ∀ φ : Module.End A L.toSubmodule,
      ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K) (L.serre_fourier_element hdefect φ)) =
        (L.toSubmodule_subtype_isBaseChange).endHom φ := by
  have hcharSplit : CharZero K ∨ CharP K p :=
    L.charZero_or_charP_fraction_field (p := p)
  -- Route correction: the remaining source step is now explicitly split by the verified
  -- characteristic dichotomy of the fraction field, rather than hidden behind one undifferentiated
  -- algebraic-closure packet goal.
  rcases hcharSplit with hchar0 | hcharp
  · letI : CharZero K := hchar0
    -- Dispatch the semisimple branch to the target-local Fourier workbench.
    exact L.charZero_fourier_branch_consequences (p := p) (ρ := ρ) hdefect
  · letI : CharP K p := hcharp
    -- Dispatch the equal-characteristic branch to the target-local packet-block workbench.
    exact L.equalChar_packet_block_action_eq_transport (p := p) (ρ := ρ) hdefect

/-- Helper for Proposition 16-16.4-1: Serre's explicit integral Fourier element `u_φ`
acts on the stable lattice as the prescribed `A`-linear endomorphism `φ`. -/
lemma serre_fourier_action_eq_endHom
    [CharZero K]
    [(@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).IsIrreducible]
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule) :
    L.toRepresentation.asAlgebraHom (L.serre_fourier_element hdefect φ) = φ := by
  -- Route correction: the only remaining source step now lives in the single theorem just above as
  -- one ambient complete-family Fourier bridge, so this consumer only performs the previously
  -- isolated descent from ambient action to the lattice.
  apply L.serre_fourier_action_eq_endHom_of_ambient (hdefect := hdefect) (φ := φ)
  exact L.algClosure_complete_family_fourier_consequences (p := p) (ρ := ρ) hdefect φ
/-- Helper for Proposition 16-16.4-1: Serre's special Fourier element
`u_{LinearMap.id}` acts on the stable lattice as the identity endomorphism. This is the
`φ = LinearMap.id` specialization of the integral Fourier lift. -/
lemma serre_fourier_id_action_eq_id
    [CharZero K]
    [(@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).IsIrreducible]
    (hdefect : ρ.HasDefectZero p) :
    L.toRepresentation.asAlgebraHom
        (L.serre_fourier_element hdefect
          (LinearMap.id : Module.End A L.toSubmodule)) =
      (LinearMap.id : Module.End A L.toSubmodule) := by
  -- Specialize the already isolated Fourier action identity at `φ = id`.
  simpa using
    (L.serre_fourier_action_eq_endHom hdefect
      (LinearMap.id : Module.End A L.toSubmodule))

/-- Helper for Proposition 16-16.4-1: under the defect-zero hypothesis, the source proof's
integral Fourier projector should realize every `A`-linear endomorphism of the stable lattice as
the action of an element of `A[G]`. -/
lemma exists_groupAlgebra_preimage_of_endomorphism
    [CharZero K]
    [(@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).IsIrreducible]
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule) :
    ∃ u : A[G], L.toRepresentation.asAlgebraHom u = φ := by
  -- Lock in Serre's concrete integral Fourier element, then invoke the isolated action packet.
  refine ⟨L.serre_fourier_element hdefect φ, ?_⟩
  exact L.serre_fourier_action_eq_endHom hdefect φ

/-- Helper for Proposition 16-16.4-1: for Serre's special Fourier element
`e = u_{LinearMap.id}`, the implication `e * u = 0 → ρ_P(u) = 0` is already forced by the
established identity `ρ_P(e) = id`. This isolates the easy half of the kernel criterion, so the
remaining source-faithful projector work only has to prove the converse implication and
idempotence of `e`. -/
lemma serre_fourier_id_action_zero_of_left_mul_zero
    [CharZero K]
    [(@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).IsIrreducible]
    (hdefect : ρ.HasDefectZero p) (u : A[G])
    (hu : L.serre_fourier_element hdefect LinearMap.id * u = 0) :
    L.toRepresentation.asAlgebraHom u = 0 := by
  let e := L.serre_fourier_element hdefect LinearMap.id
  have he :
      L.toRepresentation.asAlgebraHom e =
        (LinearMap.id : Module.End A L.toSubmodule) := by
    -- Reuse the dedicated `φ = id` specialization so the kernel calculation stays flat.
    simpa [e] using L.serre_fourier_id_action_eq_id hdefect
  -- Apply the action map to `e * u = 0`; since `e` acts as the identity, the remaining factor is
  -- exactly the action of `u`.
  calc
    L.toRepresentation.asAlgebraHom u =
        (LinearMap.id : Module.End A L.toSubmodule) * L.toRepresentation.asAlgebraHom u := by
          symm
          exact one_mul (L.toRepresentation.asAlgebraHom u)
    _ = L.toRepresentation.asAlgebraHom e * L.toRepresentation.asAlgebraHom u := by
          rw [he]
    _ = L.toRepresentation.asAlgebraHom (e * u) := by
          symm
          simpa using L.toRepresentation.asAlgebraHom.map_mul e u
    _ = 0 := by
          rw [hu]
          simp

/-- Helper for Proposition 16-16.4-1: Serre's special Fourier element `u_{LinearMap.id}` cuts
out exactly the kernel of the lattice action map by left multiplication. This packages the two
directions of the kernel criterion that are proved separately around the remaining ambient packet
bridge. -/
lemma serre_fourier_id_action_zero_iff_left_mul_zero
    [CharZero K]
    [(@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).IsIrreducible]
    (hdefect : ρ.HasDefectZero p) (u : A[G]) :
    L.toRepresentation.asAlgebraHom u = 0 ↔
      L.serre_fourier_element hdefect
        (LinearMap.id : Module.End A L.toSubmodule) * u = 0 := by
  constructor
  · -- The forward implication is the isolated ambient-packet consequence specialized at `φ = id`.
    intro hu
    simpa using L.serre_fourier_id_left_mul_zero_of_action_zero hdefect u hu
  · -- The reverse implication follows because `u_id` acts as the identity on the lattice.
    intro hu
    simpa using L.serre_fourier_id_action_zero_of_left_mul_zero hdefect u hu

/-- Helper for Proposition 16-16.4-1: the special Fourier element attached to `LinearMap.id`
should simultaneously produce the averaging endomorphism used for projectivity and the
complementary two-sided ideal used for the kernel splitting. -/
lemma serre_fourier_id_consequences
    [CharZero K]
    [(@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).IsIrreducible]
    (hdefect : ρ.HasDefectZero p) :
    letI : Fintype G := Fintype.ofFinite G
    letI : Module A[G] L.toSubmodule := by
      change Module A[G] L.toRepresentation.asModule
      infer_instance
    letI : IsScalarTower A A[G] L.toSubmodule := by
      change IsScalarTower A A[G] L.toRepresentation.asModule
      infer_instance
    (∃ u : Module.End A L.toSubmodule, u.sumOfConjugates G = LinearMap.id) ∧
      ∃ I : TwoSidedIdeal A[G],
        IsCompl (TwoSidedIdeal.ker L.toRepresentation.asAlgebraHom) I := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Module A[G] L.toSubmodule := by
    change Module A[G] L.toRepresentation.asModule
    infer_instance
  letI : IsScalarTower A A[G] L.toSubmodule := by
    change IsScalarTower A A[G] L.toRepresentation.asModule
    infer_instance
  -- Route correction: specialize Serre's Fourier element at `φ = LinearMap.id` before consuming
  -- it. The same block projector should supply both the Chapter `14` averaging operator and the
  -- direct-factor description of the kernel ideal.
  let e := L.serre_fourier_element hdefect LinearMap.id
  have hkernel_criterion :
      ∀ u : A[G], L.toRepresentation.asAlgebraHom u = 0 ↔ e * u = 0 := by
    -- Reuse the dedicated `u_id` kernel criterion instead of reproving its two directions inline.
    intro u
    simpa [e] using L.serre_fourier_id_action_zero_iff_left_mul_zero hdefect u
  have hsurj :
      Function.Surjective L.toRepresentation.asAlgebraHom := by
    intro φ
    exact L.exists_groupAlgebra_preimage_of_endomorphism hdefect φ
  have hkernel_split :
      ∃ I : TwoSidedIdeal A[G],
        IsCompl (TwoSidedIdeal.ker L.toRepresentation.asAlgebraHom) I := by
    have he_action :
        L.toRepresentation.asAlgebraHom e =
          (LinearMap.id : Module.End A L.toSubmodule) := by
      -- Reuse the dedicated `φ = id` specialization of the Fourier lift.
      simpa [e] using L.serre_fourier_id_action_eq_id hdefect
    have he_idem : IsIdempotentElem e := by
      have he_minus_one :
          L.toRepresentation.asAlgebraHom (e - 1) = 0 := by
        -- Since `e` acts as the identity, `e - 1` lies in the action kernel.
        rw [map_sub, he_action, map_one]
        change (LinearMap.id : Module.End A L.toSubmodule) - LinearMap.id = 0
        simp
      have hmul_zero : e * (e - 1) = 0 := (hkernel_criterion (e - 1)).mp he_minus_one
      have hsub : e * e - e = 0 := by
        -- Expanding `e * (e - 1)` turns the forward annihilator into the idempotence equation.
        simpa [sub_eq_add_neg, mul_add, mul_one, add_comm, add_left_comm, add_assoc] using
          hmul_zero
      exact sub_eq_zero.mp hsub
    -- Combine centrality, idempotence, and the two annihilator implications to split the kernel.
    exact
      L.isCompl_ker_of_central_idempotent_annihilator
        (e := e)
        (he_center := by simpa [e] using L.serre_fourier_id_mem_center hdefect)
        (he_idem := he_idem)
        (hker := hkernel_criterion)
  letI : Nontrivial E :=
    StableLattice.carrier_nontrivial_of_defect_zero (K := K) (G := G) (E := E)
      (p := p) (ρ := ρ) hdefect
  letI : Nontrivial L.toSubmodule := L.toSubmodule_nontrivial
  have hproj :
      Module.Projective A[G] L.toRepresentation.asModule := by
    -- Once the action map is surjective with split kernel, Serre's part `(a)` is formal.
    exact L.projective_of_action_hom_surjective_and_ker_isCompl hsurj hkernel_split
  have havg :
      ∃ u : Module.End A L.toSubmodule, u.sumOfConjugates G = LinearMap.id := by
    let hprojSubmodule : Module.Projective A[G] L.toSubmodule := by
      simpa using hproj
    have hcriterion :=
      (projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism
        (Λ := A) (G := G) (P := L.toSubmodule)).mp hprojSubmodule
    exact hcriterion.2
  exact ⟨havg, hkernel_split⟩


end DefectZero

end StableLattice

end
