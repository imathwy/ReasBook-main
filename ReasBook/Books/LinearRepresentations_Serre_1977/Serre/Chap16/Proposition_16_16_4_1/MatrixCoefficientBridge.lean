import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.MatrixUnitBridge

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

local instance instFintypeGDefectZeroMatrixCoefficient : Fintype G := Fintype.ofFinite G

/-- Helper for Proposition 16-16.4-1: after mapping coefficients to `K`, Serre's Fourier
coefficient attached to the basis unit `((b.coord i).smulRight (b j))` is exactly the defect-zero
ratio times the `(i,j)` matrix entry of `ρ s⁻¹`. This isolates the source coefficient rewrite
used repeatedly in the remaining equal-characteristic matrix calculations. -/
lemma algebraMap_serre_fourier_basis_unit_coeff_eq_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j : ι)
    (hdefect : ρ.HasDefectZero p) (s : G) :
    algebraMap A K
        (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j)) s) =
      algebraMap A K (L.defect_zero_dim_ratio hdefect) *
        LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j := by
  -- Expand Serre's coefficient formula on the chosen basis unit, then rewrite the trace term as
  -- the corresponding ambient matrix entry.
  rw [L.serre_fourier_element_apply (p := p) (ρ := ρ)
    (φ := ((b.coord i).smulRight (b j))) (s := s)]
  rw [map_mul, L.trace_comp_basis_unit_eq_matrix_entry_local
    (ρ := ρ) (b := b) (s := s) (i := i) (j := j)]

/-- Helper for Proposition 16-16.4-1: the `(a,m)` matrix entry of the group-algebra action on the
ambient representation is the coefficientwise sum of the matrix entries of the group operators.
This isolates the linear-expansion step before substituting Serre's explicit Fourier
coefficients. -/
lemma toMatrix_asAlgebraHom_entry_eq_sum_coeff_mul_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Module.Basis ι K E) (u : K[G]) (a m : ι) :
    LinearMap.toMatrix e e (ρ.asAlgebraHom u) a m =
      ∑ s : G, u s * LinearMap.toMatrix e e (ρ s) a m := by
  classical
  -- Expand the group-algebra action by linearity from the basis vectors `[s]`.
  induction u using MonoidAlgebra.induction_linear with
  | zero =>
      rw [map_zero]
      have hsum :
          ∑ s : G, (0 : K[G]) s * LinearMap.toMatrix e e (ρ s) a m = 0 := by
        refine Finset.sum_eq_zero ?_
        intro s hs
        have hcoeff : (0 : K[G]) s = 0 := by
          rfl
        rw [hcoeff]
        simp
      simpa using hsum.symm
  | add u v hu hv =>
      -- Matrix entries are additive in the acted-upon group-algebra element.
      simp [map_add, hu, hv, add_mul, Finset.sum_add_distrib]
  | single s c =>
      -- On one basis vector `[s]`, the action is just `c • ρ(s)`.
      calc
        LinearMap.toMatrix e e (ρ.asAlgebraHom (MonoidAlgebra.single s c)) a m =
          LinearMap.toMatrix e e (c • ρ s) a m := by
            simp [Representation.asAlgebraHom_single]
        _ = c * LinearMap.toMatrix e e (ρ s) a m := by
            simp [LinearMap.toMatrix_apply, smul_eq_mul]
        _ = ∑ t : G, (MonoidAlgebra.single s c : K[G]) t * LinearMap.toMatrix e e (ρ t) a m := by
            symm
            simpa [MonoidAlgebra.single_apply] using
              (Finset.sum_eq_single s
                (fun t _ hts ↦ by simp [MonoidAlgebra.single_apply, hts])
                (fun hs ↦ (hs (Finset.mem_univ s)).elim) :
                ∑ t : G, (MonoidAlgebra.single s c : K[G]) t *
                    LinearMap.toMatrix e e (ρ t) a m =
                  (MonoidAlgebra.single s c : K[G]) s *
                    LinearMap.toMatrix e e (ρ s) a m)

/-- Helper for Proposition 16-16.4-1: the `(a,m)` matrix entry of the ambient action of Serre's
integral Fourier element attached to one basis matrix unit is exactly the explicit defect-zero
coefficient sum appearing in the source orthogonality formula. -/
lemma integral_fourier_matrix_unit_action_entry_eq_sum_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j a m : ι)
    (hdefect : ρ.HasDefectZero p) :
    LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K)
        (ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K)
            (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j))))) a m =
      ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
        (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j) *
        (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s) a m) := by
  let e : Module.Basis ι K E := b.extendOfIsLattice K
  -- Route correction: expand the mapped Fourier element entrywise as a sum over group elements,
  -- then rewrite each coefficient by Serre's explicit trace formula for the chosen basis unit.
  calc
    LinearMap.toMatrix e e
        (ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K)
            (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j))))) a m =
      ∑ s : G,
        (MonoidAlgebra.mapRingHom G (algebraMap A K)
          (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j))) : K[G]) s *
          LinearMap.toMatrix e e (ρ s) a m := by
            simpa [e] using
              toMatrix_asAlgebraHom_entry_eq_sum_coeff_mul_local
                (ρ := ρ) (e := e)
                (u := MonoidAlgebra.mapRingHom G (algebraMap A K)
                  (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j))))
                (a := a) (m := m)
    _ = ∑ s : G,
        algebraMap A K
          (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j)) s) *
          LinearMap.toMatrix e e (ρ s) a m := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            simp [MonoidAlgebra.mapRingHom_apply]
    _ = ∑ s : G,
        algebraMap A K
          (L.defect_zero_dim_ratio hdefect *
            LinearMap.trace A L.toSubmodule
              ((L.toRepresentation s⁻¹).comp ((b.coord i).smulRight (b j)))) *
          LinearMap.toMatrix e e (ρ s) a m := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            rw [L.serre_fourier_element_apply (p := p) (ρ := ρ)
              (φ := ((b.coord i).smulRight (b j))) (s := s)]
    _ = ∑ s : G,
        (algebraMap A K (L.defect_zero_dim_ratio hdefect) *
          LinearMap.toMatrix e e (ρ s⁻¹) i j) *
          LinearMap.toMatrix e e (ρ s) a m := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            rw [map_mul,
              L.trace_comp_basis_unit_eq_matrix_entry_local
                (ρ := ρ) (b := b) (s := s) (i := i) (j := j)]
    _ = ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
        (LinearMap.toMatrix e e (ρ s⁻¹) i j) *
        (LinearMap.toMatrix e e (ρ s) a m) := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            ring

/-- Helper for Proposition 16-16.4-1: once the source coefficient sum for one basis matrix unit is
identified entrywise with the standard matrix unit, matrix extensionality upgrades that
coefficient formula to the full ambient operator identity. This isolates the formal matrix
reassembly from the remaining equal-characteristic coefficient computation. -/
lemma basis_unit_action_eq_of_matrix_entry_formula_local
    [CharP K p]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j : ι)
    (hdefect : ρ.HasDefectZero p)
    (hentry :
      ∀ a m : ι,
        ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
          (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j) *
          (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s) a m) =
            (Matrix.stdBasis K ι ι (j, i)) a m) :
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A K)
          (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j)))) =
      (L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j)) := by
  let e : Module.Basis ι K E := b.extendOfIsLattice K
  apply (LinearMap.toMatrix e e).injective
  ext a m
  -- Read the source action entrywise, substitute the coefficient formula, and then rewrite the
  -- target basis unit as the same standard matrix unit.
  calc
    LinearMap.toMatrix e e
        (ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K)
            (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j))))) a m =
      ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
        (LinearMap.toMatrix e e (ρ s⁻¹) i j) *
        (LinearMap.toMatrix e e (ρ s) a m) := by
          exact
            L.integral_fourier_matrix_unit_action_entry_eq_sum_local
              (ρ := ρ) (b := b) i j a m hdefect
    _ = (Matrix.stdBasis K ι ι (j, i)) a m := hentry a m
    _ =
      LinearMap.toMatrix e e
        ((L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j))) a m := by
          symm
          exact L.basis_unit_endHom_toMatrix_entry_local (ρ := ρ) (b := b) i j a m

/-- Helper for Proposition 16-16.4-1: once the basis-unit Fourier action is known as an ambient
operator identity, reading the `(a,m)` matrix entry recovers the corresponding source
orthogonality coefficient formula. This isolates the formal entry-extraction step from the
remaining basis-unit action blocker. -/
lemma defect_zero_basis_unit_entry_sum_eq_stdBasis_of_action_eq_local
    [CharP K p]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j a m : ι)
    (hdefect : ρ.HasDefectZero p)
    (hact :
      ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K)
            (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j)))) =
        (L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j))) :
    ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s) a m) =
        (Matrix.stdBasis K ι ι (j, i)) a m := by
  let e : Module.Basis ι K E := b.extendOfIsLattice K
  -- Read the source coefficient sum as the `(a,m)` entry of the Fourier action operator.
  calc
    ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
      (LinearMap.toMatrix e e (ρ s⁻¹) i j) *
      (LinearMap.toMatrix e e (ρ s) a m) =
      LinearMap.toMatrix e e
        (ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K)
            (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j))))) a m := by
          symm
          exact
            L.integral_fourier_matrix_unit_action_entry_eq_sum_local
              (ρ := ρ) (b := b) i j a m hdefect
    _ =
      LinearMap.toMatrix e e
        ((L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j))) a m := by
          -- Apply `toMatrix` to the assumed primitive basis-unit action identity.
          exact congrArg (fun M : Matrix ι ι K ↦ M a m)
            (congrArg (LinearMap.toMatrix e e) hact)
    _ = (Matrix.stdBasis K ι ι (j, i)) a m := by
          exact
            L.basis_unit_endHom_toMatrix_entry_local
              (ρ := ρ) (b := b) i j a m

/-- Helper for Proposition 16-16.4-1: before the later public linearity API is reached, the
integral Fourier section already sends the zero endomorphism to zero. This keeps the equal-
characteristic matrix-unit expansion dependency-closed. -/
lemma serre_fourier_zero_pre_local
    (hdefect : ρ.HasDefectZero p) :
    L.serre_fourier_element hdefect (0 : Module.End A L.toSubmodule) = 0 := by
  apply Finsupp.ext
  intro s
  -- Evaluate the coefficient formula at `s` and simplify the trace of the zero map.
  rw [StableLattice.serre_fourier_element_apply, LinearMap.comp_zero]
  change L.defect_zero_dim_ratio hdefect * LinearMap.trace A L.toSubmodule 0 = 0
  simp

/-- Helper for Proposition 16-16.4-1: before the later public linearity API is reached, the
integral Fourier section is already additive in the lifted endomorphism. This is the coefficient-
wise trace linearity used in the basis-unit expansion. -/
lemma serre_fourier_add_pre_local
    (hdefect : ρ.HasDefectZero p)
    (φ ψ : Module.End A L.toSubmodule) :
    L.serre_fourier_element hdefect (φ + ψ) =
      L.serre_fourier_element hdefect φ + L.serre_fourier_element hdefect ψ := by
  ext s
  -- Compare coefficients and use additivity of composition and trace.
  calc
    L.serre_fourier_element hdefect (φ + ψ) s =
        L.defect_zero_dim_ratio hdefect *
          LinearMap.trace A L.toSubmodule
            ((L.toRepresentation s⁻¹).comp (φ + ψ)) := by
          simp [StableLattice.serre_fourier_element_apply]
    _ = L.defect_zero_dim_ratio hdefect *
          LinearMap.trace A L.toSubmodule
            ((L.toRepresentation s⁻¹).comp φ + (L.toRepresentation s⁻¹).comp ψ) := by
          rw [LinearMap.comp_add]
    _ = L.defect_zero_dim_ratio hdefect *
          (LinearMap.trace A L.toSubmodule ((L.toRepresentation s⁻¹).comp φ) +
            LinearMap.trace A L.toSubmodule ((L.toRepresentation s⁻¹).comp ψ)) := by
          rw [(LinearMap.trace A L.toSubmodule).map_add]
    _ = (L.serre_fourier_element hdefect φ + L.serre_fourier_element hdefect ψ) s := by
          simp [StableLattice.serre_fourier_element_apply, mul_add]

/-- Helper for Proposition 16-16.4-1: before the later public linearity API is reached, the
integral Fourier section is already `A`-linear in the lifted endomorphism. This keeps scalar
coefficients outside the basis-unit expansion in the equal-characteristic branch. -/
lemma serre_fourier_smul_pre_local
    (hdefect : ρ.HasDefectZero p)
    (a : A) (φ : Module.End A L.toSubmodule) :
    L.serre_fourier_element hdefect (a • φ) =
      a • L.serre_fourier_element hdefect φ := by
  ext s
  -- Compare coefficients and move the scalar through composition and trace.
  calc
    L.serre_fourier_element hdefect (a • φ) s =
        L.defect_zero_dim_ratio hdefect *
          LinearMap.trace A L.toSubmodule
            ((L.toRepresentation s⁻¹).comp (a • φ)) := by
          simp [StableLattice.serre_fourier_element_apply]
    _ = L.defect_zero_dim_ratio hdefect *
          LinearMap.trace A L.toSubmodule
            (a • ((L.toRepresentation s⁻¹).comp φ)) := by
          rw [LinearMap.comp_smul]
    _ = L.defect_zero_dim_ratio hdefect *
          (a * LinearMap.trace A L.toSubmodule ((L.toRepresentation s⁻¹).comp φ)) := by
          rw [(LinearMap.trace A L.toSubmodule).map_smul]
          simp [smul_eq_mul]
    _ = (a • L.serre_fourier_element hdefect φ) s := by
          simp [StableLattice.serre_fourier_element_apply, smul_eq_mul, mul_assoc, mul_left_comm,
            mul_comm]

end DefectZero

end StableLattice

end section
