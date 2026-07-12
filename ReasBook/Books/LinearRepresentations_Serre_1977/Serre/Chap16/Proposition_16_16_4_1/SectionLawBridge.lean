import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.PacketBridge
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.CentralProjectorBridge

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

/-- Helper for Proposition 16-16.4-1: right multiplication of Serre's Fourier element by the basis
monomial `[g]` rotates the lifted endomorphism by the lattice action of `g`. This is the
coefficientwise trace computation at the heart of Serre's section law. -/
-- TODO: rewrite the trace calculation using the composition-friendly `LinearMap.trace_mul_comm`
-- and `LinearMap.trace_mul_cycle` API at the ambient endomorphism level.
lemma serre_fourier_mul_single_one_eq_action_local
    (hdefect : ρ.HasDefectZero p)
    (φ : Module.End A L.toSubmodule) (g : G) :
    L.serre_fourier_element hdefect φ * MonoidAlgebra.single g (1 : A) =
      L.serre_fourier_element hdefect (φ * L.toRepresentation g) :=
  by
  ext h
  have htrace :
      LinearMap.trace A L.toSubmodule
          ((L.toRepresentation ((h * g⁻¹)⁻¹)).comp φ) =
        LinearMap.trace A L.toSubmodule
          ((L.toRepresentation h⁻¹).comp (φ * L.toRepresentation g)) := by
    -- Rotate the threefold product inside the trace so the right multiplication by `g` lands on
    -- the lifted endomorphism `φ`, exactly as in the source section-law computation.
    calc
      LinearMap.trace A L.toSubmodule
          ((L.toRepresentation ((h * g⁻¹)⁻¹)).comp φ) =
        LinearMap.trace A L.toSubmodule
          (((L.toRepresentation g) * (L.toRepresentation h⁻¹)) * φ) := by
            congr 1
            ext x
            simp [mul_assoc]
      _ = LinearMap.trace A L.toSubmodule
            (φ * ((L.toRepresentation g) * (L.toRepresentation h⁻¹))) := by
            rw [LinearMap.trace_mul_comm]
      _ = LinearMap.trace A L.toSubmodule
            ((φ * L.toRepresentation g) * L.toRepresentation h⁻¹) := by
            simp [mul_assoc]
      _ = LinearMap.trace A L.toSubmodule
            (L.toRepresentation h⁻¹ * (φ * L.toRepresentation g)) := by
            rw [LinearMap.trace_mul_comm]
      _ = LinearMap.trace A L.toSubmodule
            ((L.toRepresentation h⁻¹).comp (φ * L.toRepresentation g)) := by
            rfl
  -- Read both coefficients from Serre's explicit trace formula and use the trace rotation above.
  calc
    (L.serre_fourier_element hdefect φ * MonoidAlgebra.single g (1 : A)) h =
      L.serre_fourier_element hdefect φ (h * g⁻¹) := by
        simp [MonoidAlgebra.mul_single_apply]
    _ = L.defect_zero_dim_ratio hdefect *
          LinearMap.trace A L.toSubmodule
            ((L.toRepresentation ((h * g⁻¹)⁻¹)).comp φ) := by
          simp [StableLattice.serre_fourier_element_apply]
    _ = L.defect_zero_dim_ratio hdefect *
          LinearMap.trace A L.toSubmodule
            ((L.toRepresentation h⁻¹).comp (φ * L.toRepresentation g)) := by
          rw [htrace]
    _ = L.serre_fourier_element hdefect (φ * L.toRepresentation g) h := by
          simp [StableLattice.serre_fourier_element_apply]

/-- Helper for Proposition 16-16.4-1: Serre's integral Fourier section intertwines right
multiplication in `A[G]` with postcomposition by the lattice action. This is the formal section law
used later to derive the kernel criterion and the idempotence of `u_{LinearMap.id}`. -/
-- TODO: prove the section law by induction on `u`, reducing the basis step to the repaired
-- `serre_fourier_mul_single_one_eq_action_local`.
lemma serre_fourier_mul_eq_action_local
    (hdefect : ρ.HasDefectZero p)
    (φ : Module.End A L.toSubmodule) (u : A[G]) :
    L.serre_fourier_element hdefect φ * u =
      L.serre_fourier_element hdefect (φ * L.toRepresentation.asAlgebraHom u) :=
  by
  induction u using MonoidAlgebra.induction_linear with
  | zero =>
      -- The section law is trivial on the zero group-algebra element.
      simp [L.serre_fourier_zero_local hdefect]
  | add u v hu hv =>
      -- Extend the monomial identity additively across the group algebra.
      calc
        L.serre_fourier_element hdefect φ * (u + v) =
          L.serre_fourier_element hdefect φ * u +
            L.serre_fourier_element hdefect φ * v := by
              rw [mul_add]
        _ =
          L.serre_fourier_element hdefect (φ * L.toRepresentation.asAlgebraHom u) +
            L.serre_fourier_element hdefect (φ * L.toRepresentation.asAlgebraHom v) := by
              rw [hu, hv]
        _ =
          L.serre_fourier_element hdefect
            ((φ * L.toRepresentation.asAlgebraHom u) +
              (φ * L.toRepresentation.asAlgebraHom v)) := by
                rw [← L.serre_fourier_add_local hdefect
                  (φ * L.toRepresentation.asAlgebraHom u)
                  (φ * L.toRepresentation.asAlgebraHom v)]
        _ = L.serre_fourier_element hdefect
              (φ * L.toRepresentation.asAlgebraHom (u + v)) := by
                simp [mul_add, map_add]
  | single g r =>
      have hmul_smul :
          φ * (r • L.toRepresentation g) =
            r • (φ * L.toRepresentation g) := by
        ext x
        simp [Module.End.mul_apply]
      -- Reduce the arbitrary coefficient to the coefficient-`1` basis step by `A`-linearity.
      calc
        L.serre_fourier_element hdefect φ * MonoidAlgebra.single g r =
          r • (L.serre_fourier_element hdefect φ * MonoidAlgebra.single g (1 : A)) := by
            apply Finsupp.ext
            intro h
            simp [MonoidAlgebra.mul_single_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
        _ = r • L.serre_fourier_element hdefect (φ * L.toRepresentation g) := by
            rw [L.serre_fourier_mul_single_one_eq_action_local hdefect φ g]
        _ = L.serre_fourier_element hdefect (r • (φ * L.toRepresentation g)) := by
            rw [← L.serre_fourier_smul_local hdefect r (φ * L.toRepresentation g)]
        _ = L.serre_fourier_element hdefect (φ * (r • L.toRepresentation g)) := by
            rw [hmul_smul]
        _ = L.serre_fourier_element hdefect
              (φ * L.toRepresentation.asAlgebraHom (MonoidAlgebra.single g r)) := by
                simp [Representation.asAlgebraHom_single]

/-- Helper for Proposition 16-16.4-1: the remaining source-faithful `φ = LinearMap.id` packet
step is the forward annihilator implication. Once this is known, applying it to `e - 1` yields
the idempotence of Serre's projector `e = u_{LinearMap.id}`. -/
lemma serre_fourier_id_left_mul_zero_of_action_zero
    (hdefect : ρ.HasDefectZero p) (u : A[G])
    (hu : L.toRepresentation.asAlgebraHom u = 0) :
    L.serre_fourier_element hdefect LinearMap.id * u = 0 := by
  -- Route correction: Serre's source proof gets the annihilator implication from the section law
  -- `u_φ * u = u_{φ * ρ_P(u)}`, not from a second independent packet theorem.
  calc
    L.serre_fourier_element hdefect LinearMap.id * u =
      L.serre_fourier_element hdefect
        ((LinearMap.id : Module.End A L.toSubmodule) * L.toRepresentation.asAlgebraHom u) := by
          simpa using
            L.serre_fourier_mul_eq_action_local
              hdefect (LinearMap.id : Module.End A L.toSubmodule) u
    _ = L.serre_fourier_element hdefect (0 : Module.End A L.toSubmodule) := by
          rw [hu]
          simp
    _ = 0 := L.serre_fourier_zero_local hdefect

/-- Helper for Proposition 16-16.4-1: once the scalar-extended ambient action of `u` is already
zero, the source-faithful route descends that vanishing to the lattice action and then applies the
formal section law for `u_{LinearMap.id}`. -/
lemma serre_fourier_id_left_mul_zero_of_algClosure_action_zero
    (hdefect : ρ.HasDefectZero p) (u : A[G])
    (hu :
      (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u) = 0) :
    L.serre_fourier_element hdefect LinearMap.id * u = 0 := by
  -- First descend the ambient zero action to `K`, then apply the already isolated section law.
  have hlocal :
      ρ.asAlgebraHom (MonoidAlgebra.mapRingHom G (algebraMap A K) u) = 0 :=
    StableLattice.ambient_action_zero_of_algClosure_action_zero_local (ρ := ρ) (u := u) hu
  have hlattice : L.toRepresentation.asAlgebraHom u = 0 := by
    apply L.toSubmodule_endHom_injective
    rw [← L.ambient_action_map_eq_endHom (u := u), map_zero]
    simpa using hlocal
  simpa using L.serre_fourier_id_left_mul_zero_of_action_zero hdefect u hlattice

end DefectZero

end StableLattice

end section
