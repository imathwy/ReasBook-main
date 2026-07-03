import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.PacketCenterDescentCore
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.ScalarExtensionPackets
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.ReductionBridge

noncomputable section

open scoped MonoidAlgebra
open Representation

universe u v w x

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type w} [Group G]
variable {E : Type x} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]

local notation "k" => IsLocalRing.ResidueField A

namespace Representation

/-- Helper for Proposition 16-16.4-1: scalar extension carries the group-algebra action of a
finite-dimensional representation to the coefficientwise image in the scalar-extended
representation. -/
lemma scalarExtension_asAlgebraHom_mapRingHom
    {F : Type*} [Field F] [Algebra K F]
    (ρ : Representation K G E) (u : K[G]) :
    (@Representation.scalarExtension F _ K _ inferInstance G _ E _ _ ρ).asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap K F) u) =
      LinearMap.baseChange F (ρ.asAlgebraHom u) := by
  -- Compare the scalar-extended action with base change on group-algebra generators and then
  -- extend linearly across `K[G]`.
  refine MonoidAlgebra.induction_on
    (p := fun v : K[G] =>
      (@Representation.scalarExtension F _ K _ inferInstance G _ E _ _ ρ).asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap K F) v) =
        LinearMap.baseChange F (ρ.asAlgebraHom v)) u
    ?_ ?_ ?_
  · intro g
    -- On a group element, scalar extension is definitionally the base-changed action.
    simp [MonoidAlgebra.of, Representation.scalarExtension]
    rfl
  · intro a b ha hb
    -- Both sides are additive in the group-algebra variable.
    simp [ha, hb]
  · intro r a ha
    -- Coefficient scalars commute with both `mapRingHom` and `LinearMap.baseChange`.
    have hmap :
        MonoidAlgebra.mapRingHom G (algebraMap K F) (r • a) =
          (algebraMap K F r) • MonoidAlgebra.mapRingHom G (algebraMap K F) a := by
      ext g
      simp [MonoidAlgebra.mapRingHom_apply, Algebra.smul_def]
    rw [hmap, AlgHom.map_smul_of_tower, ha]
    calc
      (algebraMap K F r) • LinearMap.baseChange F (ρ.asAlgebraHom a) =
          LinearMap.baseChange F (r • ρ.asAlgebraHom a) := by
            simpa using (LinearMap.baseChange_smul (S := F) (f := ρ.asAlgebraHom a) r).symm
      _ = LinearMap.baseChange F (ρ.asAlgebraHom (r • a)) := by
            simp

end Representation

namespace StableLattice

section DefectZero

variable [Finite G] [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
variable {ρ : Representation K G E} [FiniteDimensional K E]
variable (L : StableLattice A ρ)

/-- Helper for Proposition 16-16.4-1: the prime-to-`p` factor `ordCompl[p](|G|)` is a unit in
the discrete valuation ring `A`. -/
lemma ordCompl_card_isUnit (L : StableLattice A ρ) :
    IsUnit ((ordCompl[p] (Nat.card G)) : A) := by
  let m : ℕ := ordCompl[p] (Nat.card G)
  have hm_not_dvd : ¬ p ∣ m := by
    -- The prime-to-`p` factor of `|G|` is, by definition, not divisible by `p`.
    simpa [m] using
      (Nat.not_dvd_ordCompl (p := p) (Fact.out : Nat.Prime p)
        (n := Nat.card G) Nat.card_pos.ne')
  let _ : NeZero (m : k) := NeZero.of_not_dvd k hm_not_dvd
  have hresidue_ne_zero : IsLocalRing.residue A (m : A) ≠ 0 := by
    -- In the residue field of characteristic `p`, a prime-to-`p` natural number stays nonzero.
    rw [← IsLocalRing.ResidueField.algebraMap_eq]
    exact NeZero.ne (m : k)
  -- Local-ring theory upgrades nonvanishing modulo `𝔪_A` to invertibility in `A`.
  exact (IsLocalRing.residue_ne_zero_iff_isUnit (m : A)).mp hresidue_ne_zero

/-- Helper for Proposition 16-16.4-1: the source scalar `N / |G|` attached to the defect-zero
representation, viewed in the discrete valuation ring `A`. -/
noncomputable def defect_zero_dim_ratio
    (L : StableLattice A ρ) (hdefect : ρ.HasDefectZero p) : A :=
  let n := Nat.factorization (Nat.card G) p
  let q := Module.finrank K ρ.asModule / p ^ n
  -- Route correction: define the integral scalar by dividing only by the prime-to-`p` factor,
  -- which is already a unit in `A`.
  (q : A) * ↑((L.ordCompl_card_isUnit (p := p)).unit⁻¹ : Aˣ)

/-- Helper for Proposition 16-16.4-1: the chosen scalar `N / |G|` maps to the expected fraction in
the fraction field `K`. -/
lemma algebraMap_defect_zero_dim_ratio
    [Invertible (Nat.card G : K)]
    (hdefect : ρ.HasDefectZero p) :
    algebraMap A K (L.defect_zero_dim_ratio hdefect) =
      (Module.finrank K ρ.asModule : K) / Nat.card G := by
  -- Route correction: isolate the denominator-clearing scalar before comparing coefficients of
  -- LinearRepresentations_Serre_1977's Fourier element with the Chapter `6` inverse-Wedderburn preimage over `K[G]`.
  let n := Nat.factorization (Nat.card G) p
  let m := ordCompl[p] (Nat.card G)
  let q := Module.finrank K ρ.asModule / p ^ n
  have hcard : Nat.card G = p ^ n * m := by
    -- Rewrite `|G|` into its `p`-part times the prime-to-`p` complement.
    dsimp [n, m]
    simpa using (Nat.ordProj_mul_ordCompl_eq_self (Nat.card G) p).symm
  have hcardK : (Nat.card G : K) = (p : K) ^ n * (m : K) := by
    -- Move the canonical factorization of `|G|` into the fraction field.
    simpa using congrArg (fun t : ℕ => (t : K)) hcard
  have hfinrank : Module.finrank K ρ.asModule = p ^ n * q := by
    -- The defect-zero hypothesis exactly says that the `p`-part of `|G|` divides the dimension.
    dsimp [q]
    exact (Nat.mul_div_cancel' hdefect.dvd_finrank).symm
  have hfinrankK : (Module.finrank K ρ.asModule : K) = (p : K) ^ n * (q : K) := by
    -- Transport the dimension factorization to `K`.
    simpa using congrArg (fun t : ℕ => (t : K)) hfinrank
  have hmK_inv :
      algebraMap A K (↑((L.ordCompl_card_isUnit (p := p)).unit⁻¹ : Aˣ) : A) = (m : K)⁻¹ := by
    -- The prime-to-`p` denominator is already a unit in `A`, so its image in `K` is inverted
    -- coefficientwise.
    calc
      algebraMap A K (↑((L.ordCompl_card_isUnit (p := p)).unit⁻¹ : Aˣ) : A) =
          (algebraMap A K (((L.ordCompl_card_isUnit (p := p)).unit : Aˣ) : A))⁻¹ := by
            simp
      _ = (m : K)⁻¹ := by
            simp [m]
  have hcardG_ne_zero : (Nat.card G : K) ≠ 0 := by
    -- This is the field-side invertibility hypothesis required by the Chapter `6` comparison.
    exact (isUnit_iff_ne_zero).mp (isUnit_of_invertible (Nat.card G : K))
  have hpn_ne_zero : (p : K) ^ n ≠ 0 := by
    -- Since the complementary factor maps to a unit, vanishing of the `p`-part would force
    -- vanishing of `|G|`, contradicting invertibility.
    intro hpn0
    apply hcardG_ne_zero
    rw [hcardK, hpn0]
    simp
  calc
    algebraMap A K (L.defect_zero_dim_ratio hdefect) = (q : K) * (m : K)⁻¹ := by
      -- Unfold LinearRepresentations_Serre_1977's integral scalar and map the chosen unit inverse into `K`.
      dsimp [StableLattice.defect_zero_dim_ratio, n, q]
      rw [map_mul, hmK_inv]
      simp
    _ = ((p : K) ^ n * q) / ((p : K) ^ n * m) := by
      -- Cancel the common `p`-part after moving the denominator to the field side.
      field_simp [hpn_ne_zero]
    _ = (Module.finrank K ρ.asModule : K) / Nat.card G := by
      -- Replace the numerator and denominator by the factorizations recorded above.
      rw [← hfinrankK, ← hcardK]

/-- Helper for Proposition 16-16.4-1: LinearRepresentations_Serre_1977's explicit integral Fourier element attached to an
`A`-linear endomorphism `φ` of the stable lattice. -/
noncomputable def serre_fourier_element
    (L : StableLattice A ρ) (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule) :
    A[G] :=
  letI : Fintype G := Fintype.ofFinite G
  ∑ s : G,
    (L.defect_zero_dim_ratio hdefect *
        LinearMap.trace A L.toSubmodule ((L.toRepresentation s⁻¹).comp φ)) •
      MonoidAlgebra.of A G s

/-- Helper for Proposition 16-16.4-1: the coefficient of LinearRepresentations_Serre_1977's explicit integral Fourier element
is exactly the source trace formula. -/
lemma serre_fourier_element_apply
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule) (s : G) :
    L.serre_fourier_element hdefect φ s =
      L.defect_zero_dim_ratio hdefect *
        LinearMap.trace A L.toSubmodule ((L.toRepresentation s⁻¹).comp φ) := by
  -- Read the coefficient of the finite sum at the basis vector `[s]`.
  letI : Fintype G := Fintype.ofFinite G
  classical
  rw [show L.serre_fourier_element hdefect φ =
      ∑ t : G,
        MonoidAlgebra.single t
          (L.defect_zero_dim_ratio hdefect *
            LinearMap.trace A L.toSubmodule ((L.toRepresentation t⁻¹).comp φ)) by
      simp [serre_fourier_element, MonoidAlgebra.of_apply]]
  let f : G →₀ A :=
    Finsupp.equivFunOnFinite.symm fun t : G ↦
      L.defect_zero_dim_ratio hdefect *
        LinearMap.trace A L.toSubmodule ((L.toRepresentation t⁻¹).comp φ)
  have hf :
      (∑ t : G,
          MonoidAlgebra.single t
            (L.defect_zero_dim_ratio hdefect *
              LinearMap.trace A L.toSubmodule ((L.toRepresentation t⁻¹).comp φ)) : A[G]) = f := by
    simpa [f] using (Finsupp.univ_sum_single f)
  exact congrArg (fun g : G →₀ A => g s) hf

/-- Helper for Proposition 16-16.4-1: the inclusion of the lattice into the ambient
representation is the canonical base change from `A` to its fraction field `K`. -/
lemma toSubmodule_subtype_isBaseChange :
    IsBaseChange K (L.toSubmodule.subtype : L.toSubmodule →ₗ[A] E) := by
  let ι := Module.Free.ChooseBasisIndex A L.toSubmodule
  let b : Module.Basis ι A L.toSubmodule := Module.Free.chooseBasis A L.toSubmodule
  let e : Module.Basis ι K E := b.extendOfIsLattice K
  let ibc : IsBaseChange K (Finsupp.linearCombination A e) := IsBaseChange.of_basis A e
  -- Route correction: package the lattice spanning property as a genuine base-change owner instead
  -- of repeating matrix-by-matrix transport in each downstream Fourier coefficient comparison.
  refine IsBaseChange.of_equiv ((b.repr.baseChange A K _ _).trans ibc.equiv) ?_
  intro x
  suffices
      Finsupp.linearCombination A e (b.repr x) = ((x : L.toSubmodule) : E) by
    simpa only [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul, IsBaseChange.equiv_tmul,
      one_smul, Submodule.subtype_apply] using this
  -- Expand the basis reconstruction of `x` in the lattice basis and then coerce to `E`.
  calc
    Finsupp.linearCombination A e (b.repr x) = (b.repr x).sum fun i a ↦ a • e i := by
      simp [Finsupp.linearCombination_apply]
    _ = ∑ i, (b.repr x i : A) • e i := by
      exact Finsupp.sum_fintype (b.repr x) (fun i a ↦ a • e i) (fun i ↦ zero_smul A (e i))
    _ = ∑ i, (b.repr x i : A) • ((b i : L.toSubmodule) : E) := by
      simp [e, Module.Basis.extendOfIsLattice_apply]
    _ = ((((∑ i, (b.repr x i : A) • b i : L.toSubmodule)) : L.toSubmodule) : E) := by
      symm
      simpa [Submodule.coe_smul_of_tower] using
        (Submodule.coe_sum (p := L.toSubmodule) (s := Finset.univ)
          (x := fun i ↦ ((b.repr x i : A) • b i : L.toSubmodule)))
    _ = ((x : L.toSubmodule) : E) := by
      exact congrArg Subtype.val (b.sum_repr x)

/-- Helper for Proposition 16-16.4-1: traces of lattice endomorphisms commute with scalar
extension from `A` to `K`. -/
lemma algebraMap_trace_eq_trace_endHom
    (φ : Module.End A L.toSubmodule) :
    algebraMap A K (LinearMap.trace A L.toSubmodule φ) =
      LinearMap.trace K E ((L.toSubmodule_subtype_isBaseChange).endHom φ) := by
  let b : Module.Basis (Module.Free.ChooseBasisIndex A L.toSubmodule) A L.toSubmodule :=
    Module.Free.chooseBasis A L.toSubmodule
  let hf : IsBaseChange K (L.toSubmodule.subtype : L.toSubmodule →ₗ[A] E) :=
    L.toSubmodule_subtype_isBaseChange
  -- Compare traces through the compatible lattice/ambient bases provided by the base-change owner.
  rw [LinearMap.trace_eq_matrix_trace A b, LinearMap.trace_eq_matrix_trace K (hf.basis b)]
  rw [IsBaseChange.endHom_toMatrix (ibcM := hf) (b := b) (f := φ)]
  simp [Matrix.trace]

/-- Helper for Proposition 16-16.4-1: the trace of a lattice endomorphism maps to the trace of
its ambient `K`-linear action on the simple representation. -/
lemma algebraMap_trace_toRepresentation_eq_character
    (s : G) :
    algebraMap A K (LinearMap.trace A L.toSubmodule (L.toRepresentation s)) =
      ρ.character s := by
  letI : Module.Free A L.toSubmodule := Submodule.IsLattice.free (K := K) L.toSubmodule
  letI : Module.Finite A L.toSubmodule :=
    Module.Finite.of_fg (Submodule.IsLattice.fg (A := K) (M := L.toSubmodule))
  let ι := Module.Free.ChooseBasisIndex A L.toSubmodule
  letI : Fintype ι := Fintype.ofFinite ι
  let b : Module.Basis ι A L.toSubmodule := Module.Free.chooseBasis A L.toSubmodule
  let e : Module.Basis ι K E := b.extendOfIsLattice K
  have hmatrix :
      LinearMap.toMatrix e e (ρ s) =
        (LinearMap.toMatrix b b (L.toRepresentation s)).map (algebraMap A K) := by
    -- The ambient matrix is obtained by extending the lattice matrix coefficientwise.
    ext i j
    rw [LinearMap.toMatrix_apply]
    calc
      e.repr (ρ s (e j)) i =
          e.repr
            (Finsupp.linearCombination K e
              (Finsupp.mapRange.linearMap (Algebra.linearMap A K)
                (b.repr (L.toRepresentation s (b j))))) i := by
            have hsum₁ :
                ρ s (e j) =
                  ∑ m, (b.repr (L.toRepresentation s (b j)) m : A) • (b m : E) := by
              have hej : e j = ((b j : L.toSubmodule) : E) := by
                simp [e, Module.Basis.extendOfIsLattice_apply]
              have hsum_sub :
                  L.toRepresentation s (b j) =
                    ∑ m, (b.repr (L.toRepresentation s (b j)) m : A) • b m := by
                exact (b.sum_repr (L.toRepresentation s (b j))).symm
              have hsum_val :
                  (((L.toRepresentation s (b j) : L.toSubmodule) : E)) =
                    ∑ m, (b.repr (L.toRepresentation s (b j)) m : A) • (b m : E) := by
                calc
                  (((L.toRepresentation s (b j) : L.toSubmodule) : E)) =
                      ↑(∑ m, (b.repr (L.toRepresentation s (b j)) m : A) • b m) := by
                        exact congrArg Subtype.val hsum_sub
                  _ = ∑ m, (b.repr (L.toRepresentation s (b j)) m : A) • (b m : E) := by
                        simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
              rw [hej]
              change (((L.toRepresentation s (b j) : L.toSubmodule) : E)) =
                  ∑ m, (b.repr (L.toRepresentation s (b j)) m : A) • (b m : E)
              exact hsum_val
            have hsum₂ :
                (∑ m, (b.repr (L.toRepresentation s (b j)) m : A) • (b m : E)) =
                  ∑ m, algebraMap A K (b.repr (L.toRepresentation s (b j)) m) • (b m : E) := by
              simp only [IsScalarTower.algebraMap_smul]
            have hsum₃ :
                (∑ m, algebraMap A K (b.repr (L.toRepresentation s (b j)) m) • (b m : E)) =
                  Finsupp.linearCombination K e
                    (Finsupp.mapRange.linearMap (Algebra.linearMap A K)
                      (b.repr (L.toRepresentation s (b j)))) := by
              rw [Finsupp.linearCombination_apply]
              rw [Finsupp.sum_fintype _ _ (fun m => zero_smul K (e m))]
              simp [Finsupp.mapRange.linearMap_apply, e, Module.Basis.extendOfIsLattice_apply]
            have hvector :
                ρ s (e j) =
                  Finsupp.linearCombination K e
                    (Finsupp.mapRange.linearMap (Algebra.linearMap A K)
                      (b.repr (L.toRepresentation s (b j)))) := by
              calc
                ρ s (e j) = ∑ m, (b.repr (L.toRepresentation s (b j)) m : A) • (b m : E) :=
                  hsum₁
                _ = ∑ m, algebraMap A K (b.repr (L.toRepresentation s (b j)) m) • (b m : E) :=
                  hsum₂
                _ = Finsupp.linearCombination K e
                      (Finsupp.mapRange.linearMap (Algebra.linearMap A K)
                        (b.repr (L.toRepresentation s (b j)))) := hsum₃
            exact congrArg (fun y : E ↦ e.repr y i) hvector
      _ = (Finsupp.mapRange.linearMap (Algebra.linearMap A K)
            (b.repr (L.toRepresentation s (b j)))) i := by
            simp
      _ = algebraMap A K ((LinearMap.toMatrix b b (L.toRepresentation s)) i j) := by
            simp [LinearMap.toMatrix_apply]
  -- Read both traces in the compatible lattice/ambient bases.
  rw [Representation.character]
  calc
    algebraMap A K (LinearMap.trace A L.toSubmodule (L.toRepresentation s)) =
        algebraMap A K (Matrix.trace (LinearMap.toMatrix b b (L.toRepresentation s))) := by
          rw [LinearMap.trace_eq_matrix_trace A b]
    _ = Matrix.trace ((LinearMap.toMatrix b b (L.toRepresentation s)).map (algebraMap A K)) := by
          simp [Matrix.trace]
    _ = Matrix.trace (LinearMap.toMatrix e e (ρ s)) := by
          rw [hmatrix]
    _ = LinearMap.trace K E (ρ s) := by
          rw [LinearMap.trace_eq_matrix_trace K e]

/-- Helper for Proposition 16-16.4-1: after mapping coefficients to the fraction field, LinearRepresentations_Serre_1977's
special Fourier element for `φ = LinearMap.id` matches the explicit character-theoretic central
element formula from Chapter `6`. -/
lemma map_serre_fourier_element_id_eq_character_formula
    [Invertible (Nat.card G : K)]
    (hdefect : ρ.HasDefectZero p) :
    letI : Fintype G := Fintype.ofFinite G
    MonoidAlgebra.mapRingHom G (algebraMap A K)
        (L.serre_fourier_element hdefect LinearMap.id) =
      (((Module.finrank K ρ.asModule : K) / Nat.card G) •
        ∑ t : G, ρ.character t⁻¹ • MonoidAlgebra.of K G t : K[G]) := by
  letI : Fintype G := Fintype.ofFinite G
  ext s
  -- Compare coefficients using the trace/character identity and the defect-zero scalar formula.
  calc
    MonoidAlgebra.mapRingHom G (algebraMap A K)
        (L.serre_fourier_element hdefect LinearMap.id) s =
      algebraMap A K
        (L.defect_zero_dim_ratio hdefect *
          LinearMap.trace A L.toSubmodule ((L.toRepresentation s⁻¹).comp LinearMap.id)) := by
            simp [StableLattice.serre_fourier_element_apply]
    _ = algebraMap A K (L.defect_zero_dim_ratio hdefect) *
          algebraMap A K (LinearMap.trace A L.toSubmodule (L.toRepresentation s⁻¹)) := by
            simp
    _ = ((Module.finrank K ρ.asModule : K) / Nat.card G) * ρ.character s⁻¹ := by
          rw [L.algebraMap_defect_zero_dim_ratio (p := p) hdefect,
            L.algebraMap_trace_toRepresentation_eq_character (s := s⁻¹)]
    _ = ((((Module.finrank K ρ.asModule : K) / Nat.card G) •
          ∑ t : G, ρ.character t⁻¹ • MonoidAlgebra.of K G t : K[G]) : K[G]) s := by
          have hsingle :
              (∑ t : G, (ρ.character t⁻¹ • MonoidAlgebra.of K G t : K[G])) s =
                ρ.character s⁻¹ := by
            have hsum :
                (∑ t : G, (ρ.character t⁻¹ • MonoidAlgebra.of K G t : K[G])) =
                  Finsupp.equivFunOnFinite.symm (fun t : G ↦ ρ.character t⁻¹) := by
              simpa [MonoidAlgebra.of] using
                (Finsupp.equivFunOnFinite_symm_eq_sum (fun t : G ↦ ρ.character t⁻¹)).symm
            simpa using congrArg (fun z : K[G] => z s) hsum
          symm
          calc
            ((((Module.finrank K ρ.asModule : K) / Nat.card G) •
                ∑ t : G, ρ.character t⁻¹ • MonoidAlgebra.of K G t : K[G]) : K[G]) s =
                  ((Module.finrank K ρ.asModule : K) / Nat.card G) *
                    (∑ t : G, (ρ.character t⁻¹ • MonoidAlgebra.of K G t : K[G])) s := by
                      rfl
            _ = ((Module.finrank K ρ.asModule : K) / Nat.card G) * ρ.character s⁻¹ := by
                  rw [hsingle]

/-- Helper for Proposition 16-16.4-1: after scalar extension to `K`, the special Fourier element
for `φ = LinearMap.id` is the class-function packet attached to the inverse character
`s ↦ χ(s⁻¹)`. -/
lemma map_serre_fourier_element_id_eq_classFunction_packet
    [Invertible (Nat.card G : K)]
    (hdefect : ρ.HasDefectZero p) :
    letI : Fintype G := Fintype.ofFinite G
    ∃ f : classFunctionSubmodule K G,
      MonoidAlgebra.mapRingHom G (algebraMap A K)
          (L.serre_fourier_element hdefect LinearMap.id) =
        Finsupp.equivFunOnFinite.symm (f : G → K) := by
  letI : Fintype G := Fintype.ofFinite G
  let f : classFunctionSubmodule K G :=
    ⟨fun s ↦ ρ.character s⁻¹, inverse_character_mem_classFunctionSubmodule ρ⟩
  let f' : classFunctionSubmodule K G := ((Module.finrank K ρ.asModule : K) / Nat.card G) • f
  refine ⟨f', ?_⟩
  -- Route correction: expose the mapped Fourier projector as a genuine class function once, so
  -- later centrality arguments can use the Chapter `6` center API directly.
  calc
    MonoidAlgebra.mapRingHom G (algebraMap A K)
        (L.serre_fourier_element hdefect LinearMap.id) =
      (((Module.finrank K ρ.asModule : K) / Nat.card G) •
        ∑ t : G, ρ.character t⁻¹ • MonoidAlgebra.of K G t : K[G]) := by
          exact L.map_serre_fourier_element_id_eq_character_formula (p := p) hdefect
    _ = Finsupp.equivFunOnFinite.symm (f' : G → K) := by
      symm
      calc
        Finsupp.equivFunOnFinite.symm (f' : G → K) =
            ∑ t : G, (f' : G → K) t • MonoidAlgebra.of K G t := by
              simpa [MonoidAlgebra.of] using
                (Finsupp.equivFunOnFinite_symm_eq_sum (f' : G → K))
        _ = (((Module.finrank K ρ.asModule : K) / Nat.card G) •
              ∑ t : G, ρ.character t⁻¹ • MonoidAlgebra.of K G t : K[G]) := by
              simp [f, f', Finset.smul_sum]

/-- Helper for Proposition 16-16.4-1: the mapped Fourier projector for `φ = LinearMap.id` is
central in `K[G]`, exactly as in LinearRepresentations_Serre_1977's character-central-element packet. -/
lemma map_serre_fourier_element_id_mem_center
    [Invertible (Nat.card G : K)]
    (hdefect : ρ.HasDefectZero p) :
    letI : Fintype G := Fintype.ofFinite G
    MonoidAlgebra.mapRingHom G (algebraMap A K)
        (L.serre_fourier_element hdefect LinearMap.id) ∈
      Subalgebra.center K (K[G]) := by
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨f, hf⟩ := L.map_serre_fourier_element_id_eq_classFunction_packet (p := p) hdefect
  -- Route correction: centrality now comes from the class-function presentation rather than from
  -- a bundled `Rep` transport.
  rw [hf]
  exact mem_center_of_classFunction K f

/-- Helper for Proposition 16-16.4-1: coefficient extension from `A[G]` to
`(AlgebraicClosure K)[G]` factors through the fraction field. This packages the repeated
coefficient-map normalization used in the remaining packet/projector calculations. -/
lemma mapRingHom_to_algClosure_eq_two_step_local
    (u : A[G]) :
    MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u =
      MonoidAlgebra.mapRingHom G (algebraMap K (AlgebraicClosure K))
        (MonoidAlgebra.mapRingHom G (algebraMap A K) u) := by
  ext s
  simp [MonoidAlgebra.mapRingHom_apply,
    IsScalarTower.algebraMap_eq A K (AlgebraicClosure K)]

/-- Helper for Proposition 16-16.4-1: after mapping LinearRepresentations_Serre_1977's special Fourier projector
`u_{LinearMap.id}` to `AlgebraicClosure K`, the same source coefficient formula remains valid with
all coefficients transported to the algebraic closure. This is the concrete group-algebra element
whose packet coordinates still have to be identified. -/
lemma algClosure_map_serre_fourier_element_id_eq_character_formula_local
    [Invertible (Nat.card G : K)]
    (hdefect : ρ.HasDefectZero p) :
    letI : Fintype G := Fintype.ofFinite G
    MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K))
        (L.serre_fourier_element hdefect LinearMap.id) =
      (((Module.finrank K ρ.asModule : AlgebraicClosure K) / Nat.card G) •
        ∑ t : G,
          algebraMap K (AlgebraicClosure K) (ρ.character t⁻¹) •
            MonoidAlgebra.of (AlgebraicClosure K) G t : (AlgebraicClosure K)[G]) := by
  letI : Fintype G := Fintype.ofFinite G
  calc
    MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K))
        (L.serre_fourier_element hdefect LinearMap.id) =
      MonoidAlgebra.mapRingHom G (algebraMap K (AlgebraicClosure K))
        ((((Module.finrank K ρ.asModule : K) / Nat.card G) •
          ∑ t : G, ρ.character t⁻¹ • MonoidAlgebra.of K G t : K[G])) := by
            rw [StableLattice.mapRingHom_to_algClosure_eq_two_step_local
                  (A := A) (K := K) (G := G)
                  (u := L.serre_fourier_element hdefect LinearMap.id),
              L.map_serre_fourier_element_id_eq_character_formula (p := p) hdefect]
    _ =
      (((Module.finrank K ρ.asModule : AlgebraicClosure K) / Nat.card G) •
        ∑ t : G,
          algebraMap K (AlgebraicClosure K) (ρ.character t⁻¹) •
            MonoidAlgebra.of (AlgebraicClosure K) G t : (AlgebraicClosure K)[G]) := by
            ext s
            have hsingleK :
                (∑ t : G, (ρ.character t⁻¹ • MonoidAlgebra.of K G t : K[G])) s =
                  ρ.character s⁻¹ := by
              have hsum :
                  (∑ t : G, (ρ.character t⁻¹ • MonoidAlgebra.of K G t : K[G])) =
                    Finsupp.equivFunOnFinite.symm (fun t : G ↦ ρ.character t⁻¹) := by
                simpa [MonoidAlgebra.of] using
                  (Finsupp.equivFunOnFinite_symm_eq_sum (fun t : G ↦ ρ.character t⁻¹)).symm
              simpa using congrArg (fun z : K[G] ↦ z s) hsum
            have hsingleAlg :
                (∑ t : G,
                    (algebraMap K (AlgebraicClosure K) (ρ.character t⁻¹) •
                      MonoidAlgebra.of (AlgebraicClosure K) G t :
                        (AlgebraicClosure K)[G])) s =
                  algebraMap K (AlgebraicClosure K) (ρ.character s⁻¹) := by
              have hmapSum :
                  (∑ t : G,
                      (algebraMap K (AlgebraicClosure K) (ρ.character t⁻¹) •
                        MonoidAlgebra.of (AlgebraicClosure K) G t :
                          (AlgebraicClosure K)[G])) =
                    MonoidAlgebra.mapRingHom G (algebraMap K (AlgebraicClosure K))
                      (∑ t : G, ρ.character t⁻¹ • MonoidAlgebra.of K G t : K[G]) := by
                ext t
                simp [MonoidAlgebra.of, Algebra.smul_def]
              rw [hmapSum, MonoidAlgebra.mapRingHom_apply]
              exact congrArg (algebraMap K (AlgebraicClosure K)) hsingleK
            have hcoeffK :
                ((((Module.finrank K ρ.asModule : K) / Nat.card G) •
                    ∑ t : G, ρ.character t⁻¹ • MonoidAlgebra.of K G t : K[G])) s =
                  ((Module.finrank K ρ.asModule : K) / Nat.card G) * ρ.character s⁻¹ := by
              calc
                ((((Module.finrank K ρ.asModule : K) / Nat.card G) •
                    ∑ t : G, ρ.character t⁻¹ • MonoidAlgebra.of K G t : K[G])) s =
                  ((Module.finrank K ρ.asModule : K) / Nat.card G) *
                    ((∑ t : G, ρ.character t⁻¹ • MonoidAlgebra.of K G t : K[G]) s) := by
                      rfl
                _ = ((Module.finrank K ρ.asModule : K) / Nat.card G) * ρ.character s⁻¹ := by
                      rw [hsingleK]
            have hcoeffAlg :
                ((((Module.finrank K ρ.asModule : AlgebraicClosure K) / Nat.card G) •
                    ∑ t : G,
                      algebraMap K (AlgebraicClosure K) (ρ.character t⁻¹) •
                        MonoidAlgebra.of (AlgebraicClosure K) G t :
                          (AlgebraicClosure K)[G])) s =
                  ((Module.finrank K ρ.asModule : AlgebraicClosure K) / Nat.card G) *
                    algebraMap K (AlgebraicClosure K) (ρ.character s⁻¹) := by
              calc
                ((((Module.finrank K ρ.asModule : AlgebraicClosure K) / Nat.card G) •
                    ∑ t : G,
                      algebraMap K (AlgebraicClosure K) (ρ.character t⁻¹) •
                        MonoidAlgebra.of (AlgebraicClosure K) G t :
                          (AlgebraicClosure K)[G])) s =
                  ((Module.finrank K ρ.asModule : AlgebraicClosure K) / Nat.card G) *
                    ((∑ t : G,
                        algebraMap K (AlgebraicClosure K) (ρ.character t⁻¹) •
                          MonoidAlgebra.of (AlgebraicClosure K) G t :
                            (AlgebraicClosure K)[G]) s) := by
                      rfl
                _ = ((Module.finrank K ρ.asModule : AlgebraicClosure K) / Nat.card G) *
                    algebraMap K (AlgebraicClosure K) (ρ.character s⁻¹) := by
                      rw [hsingleAlg]
            calc
              (MonoidAlgebra.mapRingHom G (algebraMap K (AlgebraicClosure K))
                  ((((Module.finrank K ρ.asModule : K) / Nat.card G) •
                    ∑ t : G, ρ.character t⁻¹ • MonoidAlgebra.of K G t : K[G]))) s =
                algebraMap K (AlgebraicClosure K)
                  (((Module.finrank K ρ.asModule : K) / Nat.card G) * ρ.character s⁻¹) := by
                    rw [MonoidAlgebra.mapRingHom_apply, hcoeffK]
              _ =
                ((((Module.finrank K ρ.asModule : AlgebraicClosure K) / Nat.card G) •
                    ∑ t : G,
                      algebraMap K (AlgebraicClosure K) (ρ.character t⁻¹) •
                        MonoidAlgebra.of (AlgebraicClosure K) G t :
                          (AlgebraicClosure K)[G]) : (AlgebraicClosure K)[G]) s := by
                    rw [hcoeffAlg]
                    simpa [mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Proposition 16-16.4-1: scalar extension of the `A[G]`-action on the lattice agrees
with the ambient `K[G]`-action on `E`. -/
lemma ambient_action_map_eq_endHom
    (u : A[G]) :
    ρ.asAlgebraHom (MonoidAlgebra.mapRingHom G (algebraMap A K) u) =
      (L.toSubmodule_subtype_isBaseChange).endHom (L.toRepresentation.asAlgebraHom u) := by
  letI : Fintype G := Fintype.ofFinite G
  let hf : IsBaseChange K (L.toSubmodule.subtype : L.toSubmodule →ₗ[A] E) :=
    L.toSubmodule_subtype_isBaseChange
  -- Compare both `K`-linear endomorphisms on the image of the lattice, which generates `E`
  -- through the base-change owner.
  apply hf.algHom_ext
  intro x
  have hu :
      u = ∑ g : G, u g • MonoidAlgebra.of A G g := by
    have hu' : u = ∑ g : G, MonoidAlgebra.single g (u g) :=
      (Finsupp.univ_sum_single u).symm
    simpa [MonoidAlgebra.of] using hu'
  calc
    ρ.asAlgebraHom (MonoidAlgebra.mapRingHom G (algebraMap A K) u) (((x : L.toSubmodule) : E)) =
        (((L.toRepresentation.asAlgebraHom u) x : L.toSubmodule) : E) := by
          -- Expand `u` in the delta basis of `A[G]`, then compare the two resulting finite sums
          -- termwise.
          rw [hu]
          simp [map_sum]
    _ = hf.endHom (L.toRepresentation.asAlgebraHom u) (((x : L.toSubmodule) : E)) := by
          symm
          simpa using hf.endHom_comp_apply (L.toRepresentation.asAlgebraHom u) x

/-- Helper for Proposition 16-16.4-1: if an element of `A[G]` acts trivially on the stable
lattice, then its coefficientwise image in `(AlgebraicClosure K)[G]` acts trivially on the scalar
extension of the ambient representation. -/
lemma algClosure_ambient_action_zero_of_action_zero
    (u : A[G]) (hu : L.toRepresentation.asAlgebraHom u = 0) :
    (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u) = 0 := by
  have hmap :
      MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u =
        MonoidAlgebra.mapRingHom G (algebraMap K (AlgebraicClosure K))
          (MonoidAlgebra.mapRingHom G (algebraMap A K) u) := by
    ext g
    simp [MonoidAlgebra.mapRingHom_apply, IsScalarTower.algebraMap_eq A K (AlgebraicClosure K)]
  -- First rewrite the mapped coefficient ring in two steps `A → K → AlgebraicClosure K`, then
  -- transport the ambient action through scalar extension.
  rw [hmap, Representation.scalarExtension_asAlgebraHom_mapRingHom (ρ := ρ)]
  rw [L.ambient_action_map_eq_endHom (u := u), hu]
  simp

/-- Helper for Proposition 16-16.4-1: conjugation by a representation equivalence carries
products of endomorphisms to products of the conjugated endomorphisms. -/
lemma conj_mul_eq
    {W : Type*} [AddCommGroup W] [Module K W]
    (σ : Representation K G W) (e : ρ.Equiv σ)
    (f g : Module.End K E) :
    e.toLinearEquiv.conj (f * g) = e.toLinearEquiv.conj f * e.toLinearEquiv.conj g := by
  -- This isolates the purely transport-level compatibility of `conj` with composition.
  ext x
  simp [LinearEquiv.conj_apply, Module.End.mul_apply]
  exact congrArg f (e.left_inv (g (e.invFun x))).symm

/-- Helper for Proposition 16-16.4-1: after transporting an endomorphism to an equivalent
representation, the Fourier trace term `Tr(ρ(s⁻¹) ∘ f)` is unchanged. -/
lemma trace_action_conj_eq
    {W : Type*} [AddCommGroup W] [Module K W]
    (σ : Representation K G W) (e : ρ.Equiv σ)
    (f : Module.End K E) (s : G) :
    LinearMap.trace K W (σ s⁻¹ * e.toLinearEquiv.conj f) =
      LinearMap.trace K E (ρ s⁻¹ * f) := by
  -- Route correction: separate the transport/conjugation step from the remaining coefficient
  -- comparison with LinearRepresentations_Serre_1977's explicit lattice trace formula.
  calc
    LinearMap.trace K W (σ s⁻¹ * e.toLinearEquiv.conj f) =
        LinearMap.trace K W (e.toLinearEquiv.conj (ρ s⁻¹) * e.toLinearEquiv.conj f) := by
          have heq :=
            Representation.equiv_conj_asAlgebraHom ρ σ e (MonoidAlgebra.of K G s⁻¹)
          simpa using
            congrArg (LinearMap.trace K W)
              (congrArg (fun T : Module.End K W => T * e.toLinearEquiv.conj f) heq.symm)
    _ = LinearMap.trace K W (e.toLinearEquiv.conj (ρ s⁻¹ * f)) := by
          symm
          congr 1
          exact conj_mul_eq (ρ := ρ) (σ := σ) e (ρ s⁻¹) f
    _ = LinearMap.trace K E (ρ s⁻¹ * f) := by
          exact LinearMap.trace_conj' _ e.toLinearEquiv

/-- Helper for Proposition 16-16.4-1: in characteristic zero, the Chapter `12` packet API already
packages the honest internal decomposition of `Representation.scalarExtension ρ.ρ` into its
irreducible packet fibers over `AlgebraicClosure K`. This isolates the source-faithful packet
owner that the remaining Fourier comparison still has to target. -/
lemma algClosure_packet_block_data
    [CharZero K] :
    ∃ (ι : Type) (_ : Fintype ι)
      (ψ : ι → Rep.{max w v} (AlgebraicClosure K) G)
      (d : ι → ℕ)
      (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K) (ψ i))
      (hψ_pairwise : CategoryTheory.PairwiseNonisomorphic ψ)
      (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
      (a : ℕ)
      (σ : Fin a →
        Subrepresentation
          (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ))
      (S : ι → Finset (Fin a)),
      DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule) ∧
      (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).character =
        ∑ j, ((σ j).toRepresentation).character ∧
      (∀ j, ((σ j).toRepresentation).IsIrreducible) ∧
      (∀ i j, j ∈ S i ↔ Nonempty (((σ j).toRepresentation).Equiv (ψ i).ρ)) ∧
      ∀ i,
        Finset.sum
            (S i)
            (fun j ↦ ((σ j).toRepresentation).character) =
          (d i : AlgebraicClosure K) • (ψ i).ρ.character := by
  -- Route correction: reuse the Chapter `12` visible packet and honest-fiber decomposition
  -- directly instead of rebuilding a same-universe scalar-extension owner locally.
  obtain ⟨ι, _, ψ, d, _hd_pos, hψ_fd, hψ_pairwise, hψ_irr, hpacket⟩ :=
    Representation.scalar_extension_public_packet_visible_adapter_local
      (G := G) (K' := K) (ρ := Rep.of ρ)
  obtain ⟨a, σ, S, hinternal, hσchar, hσirr, hS, hfiber⟩ :=
    Representation.Exercise_12_12_2_6.actual_scalar_extension_isotypic_fiber_character_local
      (G := G) (K' := K) (ρ := Rep.of ρ) (ψ := ψ) (d := d)
      hψ_fd hψ_pairwise hψ_irr hpacket
  exact ⟨ι, inferInstance, ψ, d, hψ_fd, hψ_pairwise, hψ_irr,
    a, σ, S, hinternal, hσchar, hσirr, hS, hfiber⟩

/-- Helper for Proposition 16-16.4-1: base change from `K` to `AlgebraicClosure K` is injective
on ambient endomorphisms. This is the faithful-descent step used to recover a `K`-linear action
identity from its scalar-extension to the algebraic closure. -/
lemma algClosure_baseChange_end_injective_local :
    Function.Injective
      (LinearMap.baseChange (AlgebraicClosure K) :
        Module.End K E →
          Module.End (AlgebraicClosure K) (TensorProduct K (AlgebraicClosure K) E)) := by
  intro f g hfg
  ext x
  have hx := congrArg (fun T ↦ T (1 ⊗ₜ[K] x)) hfg
  change (1 : AlgebraicClosure K) ⊗ₜ[K] f x = (1 : AlgebraicClosure K) ⊗ₜ[K] g x at hx
  exact
    Module.FaithfullyFlat.tensorProduct_mk_injective
      (A := K) (B := AlgebraicClosure K) E hx

/-- Helper for Proposition 16-16.4-1: an ambient action identity proved after scalar extension to
`AlgebraicClosure K` descends to the original `K`-linear ambient representation. -/
lemma ambient_action_eq_of_algClosure_baseChange_eq_local
    (u : A[G]) (f : Module.End K E)
    (hbar :
      (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u) =
        LinearMap.baseChange (AlgebraicClosure K) f) :
    ρ.asAlgebraHom (MonoidAlgebra.mapRingHom G (algebraMap A K) u) = f := by
  have hmap :
      MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u =
        MonoidAlgebra.mapRingHom G (algebraMap K (AlgebraicClosure K))
          (MonoidAlgebra.mapRingHom G (algebraMap A K) u) := by
    ext g
    simp [MonoidAlgebra.mapRingHom_apply, IsScalarTower.algebraMap_eq A K (AlgebraicClosure K)]
  -- Compare the scalar-extended ambient action with the base change of the `K`-linear action,
  -- then descend the equality through the faithful tensor functor.
  apply StableLattice.algClosure_baseChange_end_injective_local
  rw [hmap] at hbar
  rw [Representation.scalarExtension_asAlgebraHom_mapRingHom (ρ := ρ)] at hbar
  exact hbar

/-- Helper for Proposition 16-16.4-1: any ambient action identity over the fraction field lifts
coefficientwise to the scalar-extended action over `AlgebraicClosure K`. This isolates the
forward base-change step from the packet comparison that still remains in each characteristic
branch. -/
lemma algClosure_ambient_action_eq_of_local_action_eq
    (u : A[G]) (f : Module.End K E)
    (hlocal :
      ρ.asAlgebraHom (MonoidAlgebra.mapRingHom G (algebraMap A K) u) = f) :
    (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u) =
      LinearMap.baseChange (AlgebraicClosure K) f := by
  have hmap :
      MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u =
        MonoidAlgebra.mapRingHom G (algebraMap K (AlgebraicClosure K))
          (MonoidAlgebra.mapRingHom G (algebraMap A K) u) := by
    ext g
    simp [MonoidAlgebra.mapRingHom_apply, IsScalarTower.algebraMap_eq A K (AlgebraicClosure K)]
  -- Transport the coefficient map through scalar extension and then substitute the known ambient
  -- `K`-linear action identity.
  rw [hmap, Representation.scalarExtension_asAlgebraHom_mapRingHom (ρ := ρ), hlocal]

/-- Helper for Proposition 16-16.4-1: once an injective target sees LinearRepresentations_Serre_1977's special Fourier
projector as the identity, the forward annihilator implication `ρ(u) = 0 → e * u = 0` reduces to
a single multiplicative calculation in that target. This is the pure algebra step shared by the
remaining characteristic-zero and equal-characteristic packet arguments. -/
lemma mapped_serre_fourier_id_mul_eq_zero_of_injective_target
    {R : Type*} [Semiring R]
    (hdefect : ρ.HasDefectZero p)
    (σ : (AlgebraicClosure K)[G] →+* R)
    (hσ_inj : Function.Injective σ)
    (hσ_id :
      σ (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K))
        (L.serre_fourier_element hdefect
          (LinearMap.id : Module.End A L.toSubmodule))) = 1)
    (u : A[G])
    (hu :
      σ (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u) = 0) :
    MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K))
      (L.serre_fourier_element hdefect
        (LinearMap.id : Module.End A L.toSubmodule) * u) = 0 := by
  apply hσ_inj
  -- Expand the mapped product and use that the mapped projector acts as `1` in the chosen
  -- injective target.
  calc
    σ (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K))
        (L.serre_fourier_element hdefect
          (LinearMap.id : Module.End A L.toSubmodule) * u)) =
      σ (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K))
          (L.serre_fourier_element hdefect
            (LinearMap.id : Module.End A L.toSubmodule))) *
        σ (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u) := by
          simp
    _ = 1 * 0 := by rw [hσ_id, hu]
    _ = σ 0 := by simp

/-- Helper for Proposition 16-16.4-1: if an injective target sends LinearRepresentations_Serre_1977's special element
`u_id` to the projector which is the identity on the packet support `T` and `0` off `T`, then
the forward annihilator statement follows by a coordinatewise multiplication check. This is the
pure algebraic step behind both remaining branch goals; only the source-faithful construction of
such an injective target is still missing. -/
lemma mapped_serre_fourier_id_mul_eq_zero_of_injective_product_projector
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module (AlgebraicClosure K) (V i)]
    (hdefect : ρ.HasDefectZero p)
    (σ : (AlgebraicClosure K)[G] →+* ∀ i, Module.End (AlgebraicClosure K) (V i))
    (hσ_inj : Function.Injective σ)
    (T : Finset ι)
    (hprojector :
      σ (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K))
        (L.serre_fourier_element hdefect
          (LinearMap.id : Module.End A L.toSubmodule))) =
        fun i ↦ if i ∈ T then (LinearMap.id : Module.End (AlgebraicClosure K) (V i)) else 0)
    (u : A[G])
    (hu_packet :
      ∀ i ∈ T,
        σ (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u) i = 0) :
    MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K))
      (L.serre_fourier_element hdefect
        (LinearMap.id : Module.End A L.toSubmodule) * u) = 0 := by
  -- Compare the mapped product in every irreducible coordinate and then use complete-family
  -- injectivity to descend back to the group algebra.
  apply hσ_inj
  ext i x
  have hprojector_i := congrArg (fun f ↦ f i) hprojector
  by_cases hi : i ∈ T
  · -- On the packet support, `u_id` acts as the identity while `u` already acts by `0`.
    have hu_i : σ (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u) i = 0 :=
      hu_packet i hi
    calc
      σ (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K))
          (L.serre_fourier_element hdefect
            (LinearMap.id : Module.End A L.toSubmodule) * u)) i x =
        (σ (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K))
            (L.serre_fourier_element hdefect
              (LinearMap.id : Module.End A L.toSubmodule))) i *
          (σ (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u) i)) x := by
            simp [Module.End.mul_apply]
      _ = ((LinearMap.id : Module.End (AlgebraicClosure K) (V i)) *
            (σ (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u) i)) x := by
            simp [hprojector_i, hi, Module.End.mul_apply]
      _ = 0 := by
            simp [hu_i, Module.End.mul_apply]
      _ = (σ 0 i) x := by
            simp
  · -- Off the packet support, the projector coordinate is already `0`.
    calc
      σ (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K))
          (L.serre_fourier_element hdefect
            (LinearMap.id : Module.End A L.toSubmodule) * u)) i x =
        (σ (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K))
            (L.serre_fourier_element hdefect
              (LinearMap.id : Module.End A L.toSubmodule))) i *
          (σ (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u) i)) x := by
            simp [Module.End.mul_apply]
      _ = 0 := by
            simp [hprojector_i, hi, Module.End.mul_apply]
      _ = (σ 0 i) x := by
            simp

end DefectZero

end StableLattice

end
