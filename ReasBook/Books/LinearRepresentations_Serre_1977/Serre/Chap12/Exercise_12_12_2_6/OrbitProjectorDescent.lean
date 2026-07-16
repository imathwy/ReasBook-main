import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.PacketTransportOrbit

noncomputable section

open scoped BigOperators
open scoped Representation
open scoped Representation.ExternalTensor
open scoped SubgroupInduction

universe u v

namespace Representation

open CategoryTheory
open Exercise_12_12_2_6

attribute [local instance] ULift.algebra'

section FieldPart

variable {G : Type u} [Group G] [Finite G]

local instance instFintypeGExercise_12_12_2_6_orbit_projector_descent : Fintype G :=
  Fintype.ofFinite G

/-- Helper for Exercise 12-12.2-6: the transport orbit of a chosen constituent is stable under
every further packet transport. -/
theorem packet_transport_orbit_stable_of_transport_local
    {K1 : Type v} [Field K1] [CharZero K1]
    {ι : Type*}
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K1) G)
    (i0 : ι)
    (O : Finset ι)
    (hmem_O :
      ∀ j : ι,
        j ∈ O ↔
          ∃ (σ : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1)) (τ : Equiv.Perm ι),
            (∀ k : ι, ∀ g : G, σ ((ψ k).ρ.character g) = (ψ (τ k)).ρ.character g) ∧
            τ i0 = j)
    {σ : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1)}
    {τ : Equiv.Perm ι}
    (hchar : ∀ k : ι, ∀ g : G, σ ((ψ k).ρ.character g) = (ψ (τ k)).ρ.character g) :
    ∀ j : ι, j ∈ O ↔ τ j ∈ O := by
  intro j
  constructor
  · intro hj
    have hreach_j :
        ∃ (σ' : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1)) (τ' : Equiv.Perm ι),
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
        ∃ (σ' : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1)) (τ' : Equiv.Perm ι),
          (∀ k : ι, ∀ g : G, σ' ((ψ k).ρ.character g) = (ψ (τ' k)).ρ.character g) ∧
          τ' i0 = τ j := (hmem_O (τ j)).mp hτj
    have hback :
        ∃ (σ' : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1)) (τ' : Equiv.Perm ι),
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

/-- Helper for Exercise 12-12.2-6: a transport-stable orbit sum of primitive central idempotents
descends coefficientwise to the corresponding fixed field. -/
theorem transport_orbit_projector_descends_local
    {K1 : Type v} [Field K1] [CharZero K1]
    {ι : Type*} [Fintype ι]
    (H : Subgroup ((AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1)))
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K1) G)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K1) (ψ i))
    (perm :
      ∀ σ : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1), σ ∈ H → Equiv.Perm ι)
    (hchar :
      ∀ (σ : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1)) (hσ : σ ∈ H)
        (i : ι) (g : G),
          σ ((ψ i).ρ.character g) = (ψ (perm σ hσ i)).ρ.character g)
    (O : Finset ι)
    (hstable :
      ∀ (σ : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1)) (hσ : σ ∈ H) (i : ι),
        i ∈ O ↔ perm σ hσ i ∈ O) :
    ∃ p0 : MonoidAlgebra (IntermediateField.fixedField H) G,
      ∀ g : G,
        ((p0 g : IntermediateField.fixedField H) : AlgebraicClosure K1) =
          Finset.sum O
            (fun i ↦
              primitive_central_idempotent_coefficient_packet_local (G := G) (V := ψ i) g) := by
  classical
  have hcoeff_fixed :
      ∀ (σ : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1)) (hσ : σ ∈ H) (g : G),
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
    -- Transport each primitive-idempotent coefficient and then reindex along the stable orbit.
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
    -- Fixed-field membership is exactly coefficientwise invariance under the subgroup `H`.
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
  -- The descended group-algebra element recovers the orbit-sum coefficients after coercion.
  refine ⟨p0, ?_⟩
  intro g
  rfl

/-- Helper for Exercise 12-12.2-6: the explicit packet coefficient is exactly the coefficient of
Serre's Chapter 6 central primitive idempotent. -/
theorem primitive_central_idempotent_coefficient_eq_characterCentralElement_coeff_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (V : Rep.{max u v} (AlgebraicClosure K1) G)
    [FiniteDimensional (AlgebraicClosure K1) V]
    (g : G) :
    (((((Module.finrank (AlgebraicClosure K1) V : AlgebraicClosure K1) / Nat.card G) •
        ∑ s : G, V.ρ.character s⁻¹ • MonoidAlgebra.of (AlgebraicClosure K1) G s) :
        MonoidAlgebra (AlgebraicClosure K1) G) g) =
      primitive_central_idempotent_coefficient_packet_local (G := G) (V := V) g := by
  have hcoeff :
      ((∑ s : G, V.ρ.character s⁻¹ • MonoidAlgebra.of (AlgebraicClosure K1) G s :
          MonoidAlgebra (AlgebraicClosure K1) G) g) =
        V.ρ.character g⁻¹ := by
    classical
    -- Evaluate the coefficient of the group-algebra basis expansion at the chosen group element.
    calc
      ((∑ s : G, V.ρ.character s⁻¹ • MonoidAlgebra.of (AlgebraicClosure K1) G s :
          MonoidAlgebra (AlgebraicClosure K1) G) g)
          =
        ∑ s : G,
          ((V.ρ.character s⁻¹ • MonoidAlgebra.of (AlgebraicClosure K1) G s :
              MonoidAlgebra (AlgebraicClosure K1) G) g) := by
            exact
              Finsupp.finset_sum_apply Finset.univ
                (fun s : G ↦
                  V.ρ.character s⁻¹ • MonoidAlgebra.of (AlgebraicClosure K1) G s) g
      _ = V.ρ.character g⁻¹ := by
            rw [Finset.sum_eq_single g]
            · simp [MonoidAlgebra.of]
            · intro s _ hsg
              simp [MonoidAlgebra.of, hsg]
            · intro hg
              simp at hg
  -- Rewrite the coefficient of the Chapter 6 element and match it with the local packet formula.
  calc
    (((((Module.finrank (AlgebraicClosure K1) V : AlgebraicClosure K1) / Nat.card G) •
        ∑ s : G, V.ρ.character s⁻¹ • MonoidAlgebra.of (AlgebraicClosure K1) G s) :
        MonoidAlgebra (AlgebraicClosure K1) G) g)
        =
      (((Module.finrank (AlgebraicClosure K1) V : AlgebraicClosure K1) / Nat.card G) :
          AlgebraicClosure K1) *
        ((∑ s : G, V.ρ.character s⁻¹ • MonoidAlgebra.of (AlgebraicClosure K1) G s :
            MonoidAlgebra (AlgebraicClosure K1) G) g) := by
          simp
    _ =
      (((Module.finrank (AlgebraicClosure K1) V : AlgebraicClosure K1) / Nat.card G) :
          AlgebraicClosure K1) *
        V.ρ.character g⁻¹ := by
          rw [hcoeff]
    _ = primitive_central_idempotent_coefficient_packet_local (G := G) (V := V) g := by
          rfl

/-- Helper for Exercise 12-12.2-6: scalar extension carries the source group-algebra action to
the coefficientwise image of that action over the algebraic closure. -/
theorem scalarExtension_asAlgebraHom_mapRingHom_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    (x : MonoidAlgebra K1 G) :
    (Representation.scalarExtension (k := AlgebraicClosure K1) ρ.ρ).asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap K1 (AlgebraicClosure K1)) x) =
      LinearMap.baseChange (AlgebraicClosure K1) (ρ.ρ.asAlgebraHom x) := by
  -- Route correction: compare the two actions on monoid-algebra generators and then extend
  -- linearly, rather than repeatedly unfolding scalar extension inside the seam proof.
  refine MonoidAlgebra.induction_on
    (p := fun y : MonoidAlgebra K1 G ↦
      (Representation.scalarExtension (k := AlgebraicClosure K1) ρ.ρ).asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap K1 (AlgebraicClosure K1)) y) =
        LinearMap.baseChange (AlgebraicClosure K1) (ρ.ρ.asAlgebraHom y))
    x ?_ ?_ ?_
  · intro g
    -- On basis elements, scalar extension is definitionally the base-changed group action.
    simp [MonoidAlgebra.of, Representation.scalarExtension]
    rfl
  · intro a b ha hb
    -- Both constructions are additive in the group-algebra input.
    simp [ha, hb]
  · intro r a ha
    -- Scalar coefficients commute with both `mapRingHom` and `LinearMap.baseChange`.
    have hmap :
        MonoidAlgebra.mapRingHom G (algebraMap K1 (AlgebraicClosure K1)) (r • a) =
          (algebraMap K1 (AlgebraicClosure K1)) r •
            MonoidAlgebra.mapRingHom G (algebraMap K1 (AlgebraicClosure K1)) a := by
      ext g
      simp [MonoidAlgebra.mapRingHom_apply, Algebra.smul_def]
    rw [hmap, AlgHom.map_smul_of_tower, ha]
    simpa using
      (LinearMap.baseChange_smul
        (S := AlgebraicClosure K1) (f := ρ.ρ.asAlgebraHom a) r).symm

/-- Helper for Exercise 12-12.2-6: on a subrepresentation, the restricted group-algebra action is
just the ambient action evaluated on the underlying vector. -/
theorem subrepresentation_asAlgebraHom_apply_local
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
theorem subrepresentation_action_zero_of_ambient_zero_local
    {L : Type*} [Field L]
    {G' : Type*} [Group G']
    {V : Type*} [AddCommGroup V] [Module L V]
    (ρ : Representation L G' V) (σ : Subrepresentation ρ)
    (u : MonoidAlgebra L G') (hu : ρ.asAlgebraHom u = 0) :
    σ.toRepresentation.asAlgebraHom u = 0 := by
  ext x
  -- Evaluate the ambient vanishing on the underlying vector and then restrict back.
  have hx := congrArg (fun T : Module.End L V ↦ T (x : V)) hu
  simpa [subrepresentation_asAlgebraHom_apply_local ρ σ u x] using hx

/-- Helper for Exercise 12-12.2-6: if a group-algebra element acts as the identity on the ambient
representation, then it acts as the identity on every subrepresentation. -/
theorem subrepresentation_action_id_of_ambient_id_local
    {L : Type*} [Field L]
    {G' : Type*} [Group G']
    {V : Type*} [AddCommGroup V] [Module L V]
    (ρ : Representation L G' V) (σ : Subrepresentation ρ)
    (u : MonoidAlgebra L G') (hu : ρ.asAlgebraHom u = LinearMap.id) :
    σ.toRepresentation.asAlgebraHom u = LinearMap.id := by
  ext x
  -- Evaluate the ambient identity on the underlying vector and then restrict back.
  have hx := congrArg (fun T : Module.End L V ↦ T (x : V)) hu
  simpa [subrepresentation_asAlgebraHom_apply_local ρ σ u x] using hx

/-- Helper for Exercise 12-12.2-6: a central group-algebra element acts equivariantly on the
source representation. -/
theorem asAlgebraHom_isIntertwining_of_mem_center_local
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
theorem idempotent_intertwining_eq_zero_or_one_local
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

/-- Helper for Exercise 12-12.2-6: once a descended central group-algebra element is idempotent,
its action on the irreducible source representation is forced to be `0` or `1`. -/
theorem central_idempotent_source_action_eq_zero_or_one_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    [ρ.ρ.IsIrreducible]
    (u : Subalgebra.center K1 (MonoidAlgebra K1 G))
    (hidem : (u : MonoidAlgebra K1 G) * u = u) :
    ρ.ρ.asAlgebraHom u = 0 ∨ ρ.ρ.asAlgebraHom u = 1 := by
  let f : ρ.ρ.IntertwiningMap ρ.ρ :=
    (ρ.ρ.asAlgebraHom u).intertwiningMap_of_isIntertwiningMap ρ.ρ ρ.ρ
      (asAlgebraHom_isIntertwining_of_mem_center_local (G := G) (ρ := ρ) u).isIntertwining
  have hfidem : f * f = f := by
    ext x
    -- Map the source idempotence relation through the representation algebra homomorphism.
    have hmap :
        ρ.ρ.asAlgebraHom ((u : MonoidAlgebra K1 G) * u) = ρ.ρ.asAlgebraHom u :=
      congrArg ρ.ρ.asAlgebraHom hidem
    simpa [f, Module.End.mul_apply] using LinearMap.congr_fun hmap x
  -- Apply the irreducible idempotent dichotomy to the associated intertwining endomorphism.
  rcases idempotent_intertwining_eq_zero_or_one_local (G := G) (ρ := ρ) f hfidem with hf0 | hf1
  · left
    ext x
    simpa [f] using congrArg (fun T : ρ.ρ.IntertwiningMap ρ.ρ ↦ T x) hf0
  · right
    ext x
    simpa [f] using congrArg (fun T : ρ.ρ.IntertwiningMap ρ.ρ ↦ T x) hf1

end FieldPart

end Representation
