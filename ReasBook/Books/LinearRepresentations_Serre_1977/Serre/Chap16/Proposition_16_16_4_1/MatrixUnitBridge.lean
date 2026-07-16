import LinearRepresentations_Serre_1977.Serre.Chap16.Proposition_16_16_4_1.PacketBridge

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

namespace StableLattice

section DefectZero

variable [Finite G] [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
variable {ρ : Representation K G E} [FiniteDimensional K E]
variable (L : StableLattice A ρ)

local instance instFintypeGDefectZeroMatrixUnit : Fintype G := Fintype.ofFinite G

/-- Helper for Proposition 16-16.4-1: the equal-characteristic branch of the remaining Fourier
packet argument. The local distinguished-block computation already identifies the scalar-extended
action of Serre's Fourier element, so this wrapper only performs the descent back to `K` and
reuses the corresponding projector-annihilator statement. -/
lemma algClosure_fourier_action_eq_baseChange_of_ambient_action_local
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule)
    (hambient :
      ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K) (L.serre_fourier_element hdefect φ)) =
        (L.toSubmodule_subtype_isBaseChange).endHom φ) :
    (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K))
          (L.serre_fourier_element hdefect φ)) =
      LinearMap.baseChange (AlgebraicClosure K)
        ((L.toSubmodule_subtype_isBaseChange).endHom φ) := by
  -- Lift the ambient `K`-action identity through scalar extension to the algebraic closure.
  exact
    StableLattice.algClosure_ambient_action_eq_of_local_action_eq
      (ρ := ρ)
      (u := L.serre_fourier_element hdefect φ)
      (f := (L.toSubmodule_subtype_isBaseChange).endHom φ)
      hambient

/-- Helper for Proposition 16-16.4-1: once the mapped Serre Fourier element is known to act on
the original simple representation `ρ`, any isomorphic simple representation sees the same action
after conjugation. This isolates the purely formal transport half of the source Proposition `11`
package, so the remaining equal-characteristic blocker is only the self-action identity on `ρ`. -/
lemma mapped_serre_fourier_isomorphic_action_of_ambient_local
    {F : Type*} [AddCommGroup F] [Module K F]
    {τ : Representation K G F} [FiniteDimensional K F]
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule)
    (e : ρ.Equiv τ)
    (hambient :
      ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K) (L.serre_fourier_element hdefect φ)) =
        (L.toSubmodule_subtype_isBaseChange).endHom φ) :
    τ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A K) (L.serre_fourier_element hdefect φ)) =
      e.toLinearEquiv.conj ((L.toSubmodule_subtype_isBaseChange).endHom φ) := by
  -- First transport the group-algebra action across the representation equivalence.
  calc
    τ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A K) (L.serre_fourier_element hdefect φ)) =
      e.toLinearEquiv.conj
        (ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K) (L.serre_fourier_element hdefect φ))) := by
            simpa using
              (Representation.equiv_conj_asAlgebraHom
                ρ τ e
                (MonoidAlgebra.mapRingHom G (algebraMap A K)
                  (L.serre_fourier_element hdefect φ))).symm
    _ = e.toLinearEquiv.conj ((L.toSubmodule_subtype_isBaseChange).endHom φ) := by
      rw [hambient]

/-- Helper for Proposition 16-16.4-1: with respect to a finite `A`-basis of the stable lattice,
every lattice endomorphism is the sum of its matrix coefficients times the corresponding rank-one
basis endomorphisms. This is the source-faithful linear-algebra normalization used before proving
the equal-characteristic Fourier identity on one matrix unit at a time. -/
lemma endHom_eq_sum_matrix_units_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (φ : Module.End A L.toSubmodule) :
    φ =
      ∑ i : ι, ∑ j : ι,
        (LinearMap.toMatrix b b φ j i) • ((b.coord i).smulRight (b j)) := by
  -- Evaluate both endomorphisms on each basis vector and collapse the rank-one terms by the
  -- coordinate identities of `b`.
  have hbasis :
      ∀ i0 : ι,
        φ (b i0) =
          (∑ i : ι, ∑ j : ι,
            (LinearMap.toMatrix b b φ j i) • ((b.coord i).smulRight (b j))) (b i0) := by
    intro i0
    have hφk :
        φ (b i0) = ∑ j : ι, (LinearMap.toMatrix b b φ j i0) • b j := by
      simpa using
        (Matrix.toLin_self (v₁ := b) (v₂ := b)
          (M := LinearMap.toMatrix b b φ) i0)
    calc
      φ (b i0) = ∑ j : ι, (LinearMap.toMatrix b b φ j i0) • b j := hφk
      _ = (∑ i : ι, ∑ j : ι,
            (LinearMap.toMatrix b b φ j i) • ((b.coord i).smulRight (b j))) (b i0) := by
            symm
            calc
              (∑ i : ι, ∑ j : ι,
                  (LinearMap.toMatrix b b φ j i) • ((b.coord i).smulRight (b j))) (b i0) =
                  ∑ i : ι, ∑ j : ι,
                    (LinearMap.toMatrix b b φ j i) • (((b.coord i).smulRight (b j)) (b i0)) := by
                      simp
              _ = ∑ i : ι, if i = i0 then ∑ j : ι, (LinearMap.toMatrix b b φ j i) • b j else 0 := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      by_cases hik : i = i0
                      · subst hik
                        simp [LinearMap.smulRight_apply, Module.Basis.coord_apply]
                      · simp [LinearMap.smulRight_apply, Module.Basis.coord_apply, hik]
              _ = ∑ j : ι, (LinearMap.toMatrix b b φ j i0) • b j := by
                      simp
  exact Module.Basis.ext b hbasis

/-- Helper for Proposition 16-16.4-1: the rank-one endomorphism built from `b.coord i` and `b j`
is exactly the `(j,i)` standard basis endomorphism attached to `b`. This is the bridge from the
source proof's basis-unit language to mathlib's `b.end`. -/
lemma basis_unit_eq_end_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j : ι) :
    ((b.coord i).smulRight (b j)) = b.end (j, i) := by
  -- Compare the two endomorphisms on basis vectors; both send `b i` to `b j` and kill the other
  -- basis vectors.
  apply b.ext
  intro a
  by_cases hk : i = a
  · subst hk
    simp [Module.Basis.end_apply_apply, Module.Basis.coord_apply]
  · have hki : a ≠ i := by
      simpa [eq_comm] using hk
    simp [Module.Basis.end_apply_apply, Module.Basis.coord_apply, hk, hki]

/-- Helper for Proposition 16-16.4-1: after scalar extension to the ambient representation, the
rank-one lattice endomorphism attached to `b i` and `b j` is still the standard matrix unit in
the extended basis. -/
lemma basis_unit_endHom_toMatrix_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j : ι) :
    LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K)
      ((L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j))) =
        Matrix.stdBasis K ι ι (j, i) :=
  by
  let hf : IsBaseChange K (L.toSubmodule.subtype : L.toSubmodule →ₗ[A] E) :=
    L.toSubmodule_subtype_isBaseChange
  have hbasis : hf.basis b = b.extendOfIsLattice K := by
    ext a
    simp [IsBaseChange.basis_apply, Module.Basis.extendOfIsLattice_apply]
  -- First compute the lattice matrix of the rank-one operator, then transport it coefficientwise
  -- to the ambient basis provided by base change.
  calc
    LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K)
        ((L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j))) =
      LinearMap.toMatrix (hf.basis b) (hf.basis b)
        (hf.endHom ((b.coord i).smulRight (b j))) := by
          rw [hbasis]
    _ =
      (LinearMap.toMatrix b b (((b.coord i).smulRight (b j)))).map (algebraMap A K) := by
        simpa using
          (IsBaseChange.endHom_toMatrix (ibcM := hf) (b := b)
            (f := ((b.coord i).smulRight (b j))))
    _ = (LinearMap.toMatrix b b (b.end (j, i))).map (algebraMap A K) := by
      rw [L.basis_unit_eq_end_local (b := b) i j]
    _ = (Matrix.stdBasis A ι ι (j, i)).map (algebraMap A K) := by
      rw [Module.Basis.end_apply, LinearMap.toMatrix_toLin]
    _ = Matrix.stdBasis K ι ι (j, i) := by
      ext a m
      by_cases hja : j = a
      · by_cases him : i = m
        · subst hja
          subst him
          simp [Matrix.stdBasis_eq_single, Matrix.map_apply]
        · have hmi : ¬m = i := by simpa [eq_comm] using him
          simp [Matrix.stdBasis_eq_single, Matrix.map_apply, hja, him, hmi]
      · by_cases him : i = m
        · have hne : ¬a = j := by simpa [eq_comm] using hja
          simp [Matrix.stdBasis_eq_single, Matrix.map_apply, hja, hne, him]
        · have hne : ¬a = j := by simpa [eq_comm] using hja
          have hmi : ¬m = i := by simpa [eq_comm] using him
          simp [Matrix.stdBasis_eq_single, Matrix.map_apply, hja, hne, him, hmi]

/-- Helper for Proposition 16-16.4-1: the `(a,m)` entry of the scalar-extended basis unit is the
corresponding entry of the standard matrix unit. This packages the target side of the remaining
equal-characteristic matrix-coefficient comparison into a direct rewrite lemma. -/
lemma basis_unit_endHom_toMatrix_entry_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j a m : ι) :
    LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K)
      ((L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j))) a m =
        (Matrix.stdBasis K ι ι (j, i)) a m := by
  -- Read the established matrix-unit identity at the chosen `(a,m)` entry.
  exact congrArg (fun M : Matrix ι ι K ↦ M a m)
    (L.basis_unit_endHom_toMatrix_local (ρ := ρ) (b := b) i j)

/-- Helper for Proposition 16-16.4-1: the trace coefficient appearing in Serre's integral Fourier
formula for a basis matrix unit is exactly the corresponding ambient matrix entry of `ρ s⁻¹`. -/
lemma trace_comp_basis_unit_eq_matrix_entry_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (s : G) (i j : ι) :
    algebraMap A K
        (LinearMap.trace A L.toSubmodule
          ((L.toRepresentation s⁻¹).comp ((b.coord i).smulRight (b j)))) =
      LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j :=
  by
  let e : Module.Basis ι K E := b.extendOfIsLattice K
  let hf : IsBaseChange K (L.toSubmodule.subtype : L.toSubmodule →ₗ[A] E) :=
    L.toSubmodule_subtype_isBaseChange
  have hbasis : hf.basis b = e := by
    ext a
    simp [e, IsBaseChange.basis_apply, Module.Basis.extendOfIsLattice_apply]
  have htrace :
      LinearMap.trace A L.toSubmodule
          ((L.toRepresentation s⁻¹).comp ((b.coord i).smulRight (b j))) =
        LinearMap.toMatrix b b (L.toRepresentation s⁻¹) i j := by
    -- Rewrite the basis unit as `b.end (j,i)` and compute the trace on matrices by multiplying by
    -- a single-entry matrix.
    calc
      LinearMap.trace A L.toSubmodule
          ((L.toRepresentation s⁻¹).comp ((b.coord i).smulRight (b j))) =
        LinearMap.trace A L.toSubmodule
          ((L.toRepresentation s⁻¹).comp (b.end (j, i))) := by
            rw [L.basis_unit_eq_end_local (b := b) i j]
      _ = Matrix.trace
            (LinearMap.toMatrix b b ((L.toRepresentation s⁻¹).comp (b.end (j, i)))) := by
            rw [LinearMap.trace_eq_matrix_trace A b]
      _ = Matrix.trace
            (LinearMap.toMatrix b b (L.toRepresentation s⁻¹) *
              Matrix.stdBasis A ι ι (j, i)) := by
            change Matrix.trace
                (LinearMap.toMatrix b b (L.toRepresentation s⁻¹ * b.end (j, i))) =
              Matrix.trace
                (LinearMap.toMatrix b b (L.toRepresentation s⁻¹) *
                  Matrix.stdBasis A ι ι (j, i))
            rw [LinearMap.toMatrix_mul, Module.Basis.end_apply, LinearMap.toMatrix_toLin]
      _ = LinearMap.toMatrix b b (L.toRepresentation s⁻¹) i j := by
            rw [Matrix.stdBasis_eq_single, Matrix.trace_mul_single]
            simp
  have hmatrix :
      LinearMap.toMatrix e e (ρ s⁻¹) =
        (LinearMap.toMatrix b b (L.toRepresentation s⁻¹)).map (algebraMap A K) := by
    -- Base change identifies the ambient action matrix with the coefficientwise image of the
    -- lattice action matrix.
    calc
      LinearMap.toMatrix e e (ρ s⁻¹) =
        LinearMap.toMatrix e e (hf.endHom (L.toRepresentation s⁻¹)) := by
          rw [L.endHom_toRepresentation_eq_ambient_action (ρ := ρ) (s := s⁻¹)]
      _ = LinearMap.toMatrix (hf.basis b) (hf.basis b) (hf.endHom (L.toRepresentation s⁻¹)) := by
          rw [hbasis]
      _ = (LinearMap.toMatrix b b (L.toRepresentation s⁻¹)).map (algebraMap A K) := by
          simpa using
            (IsBaseChange.endHom_toMatrix (ibcM := hf) (b := b) (f := L.toRepresentation s⁻¹))
  calc
    algebraMap A K
        (LinearMap.trace A L.toSubmodule
          ((L.toRepresentation s⁻¹).comp ((b.coord i).smulRight (b j)))) =
      algebraMap A K (LinearMap.toMatrix b b (L.toRepresentation s⁻¹) i j) := by
        rw [htrace]
    _ = ((LinearMap.toMatrix b b (L.toRepresentation s⁻¹)).map (algebraMap A K)) i j := by
        rfl
    _ = LinearMap.toMatrix e e (ρ s⁻¹) i j := by
        simpa [Matrix.map_apply] using congrArg (fun M : Matrix ι ι K ↦ M i j) hmatrix.symm


end DefectZero

end StableLattice

end section
