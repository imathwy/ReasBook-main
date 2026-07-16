import LinearRepresentations_Serre_1977.Serre.Chap13.Exercise_13_13_1_14.IntertwinerCubicPlane

noncomputable section

open scoped Representation
open scoped Quaternion

namespace Representation

section

local notation "Q8" => QuaternionGroup 2
local notation "C3" => Multiplicative (ZMod 3)
local notation "G0" => Q8 × C3

local instance anonInst_ModuleEndMatrix_1 : Fintype Q8 := inferInstance
local instance anonInst_ModuleEndMatrix_2 : Fintype C3 := inferInstance
local instance anonInst_ModuleEndMatrix_3 : DecidableEq Q8 := inferInstance
local instance anonInst_ModuleEndMatrix_4 : DecidableEq C3 := inferInstance
local instance anonInst_ModuleEndMatrix_5 : Finite G0 := inferInstance
local instance anonInst_ModuleEndMatrix_6 : Fintype G0 := inferInstance
local instance anonInst_ModuleEndMatrix_7 : DecidableEq G0 := inferInstance
local instance anonInst_ModuleEndMatrix_8 : DecidableEq ℍ[ℚ] := by
  intro a b
  by_cases hre : a.re = b.re
  · by_cases himI : a.imI = b.imI
    · by_cases himJ : a.imJ = b.imJ
      · by_cases himK : a.imK = b.imK
        · exact isTrue (by ext <;> assumption)
        · exact isFalse (by
            intro h
            exact himK (congrArg QuaternionAlgebra.imK h))
      · exact isFalse (by
          intro h
          exact himJ (congrArg QuaternionAlgebra.imJ h))
    · exact isFalse (by
        intro h
        exact himI (congrArg QuaternionAlgebra.imI h))
  · exact isFalse (by
      intro h
      exact hre (congrArg QuaternionAlgebra.re h))

/-- Helper for Exercise 13-13.1-14: Serre's double-centralizer step identifies the image algebra
with the endomorphism algebra over the cubic coefficient field. -/
theorem quaternion_cyclic_imageSubalgebra_algEquiv_moduleEnd_cubic_subfield_exists :
    Nonempty
      (quaternion_cyclic_imageSubalgebra ≃ₐ[ℚ]
        Module.End ↥quaternion_cubic_subfield ℍ[ℚ]) := by
  -- Route correction: avoid the abstract transport equivalence and follow Serre's concrete
  -- double-centralizer route. We send each image-algebra element to the same underlying map,
  -- now viewed as `quaternion_cubic_subfield`-linear because the two actions commute.
  let actionHom :
      quaternion_cyclic_imageSubalgebra →ₐ[ℚ]
        Module.End ↥quaternion_cubic_subfield ℍ[ℚ] :=
    AlgHom.mk'
      { toFun := fun a =>
          { toFun := fun y ↦ (a : Module.End ℚ ℍ[ℚ]) y
            map_add' := by
              intro x y
              exact map_add (a : Module.End ℚ ℍ[ℚ]) x y
            map_smul' := by
              intro x y
              exact
                quaternion_cyclic_imageSubalgebra_smulCommClass_cubic_subfield.smul_comm a x y }
        map_one' := by
          apply LinearMap.ext
          intro y
          rfl
        map_mul' := by
          intro a b
          apply LinearMap.ext
          intro y
          rfl
        map_zero' := by
          apply LinearMap.ext
          intro y
          rfl
        map_add' := by
          intro a b
          apply LinearMap.ext
          intro y
          rfl }
      (by
        intro q a
        apply LinearMap.ext
        intro y
        rfl)
  letI : IsSimpleModule quaternion_cyclic_imageSubalgebra ℍ[ℚ] :=
    quaternion_cyclic_imageSubalgebra_isSimpleModule
  refine ⟨AlgEquiv.ofBijective actionHom ?_⟩
  constructor
  · intro a b hab
    -- Injectivity is pointwise faithfulness of the original image algebra inside `Endℚ(ℍ[ℚ])`.
    apply Subtype.ext
    apply LinearMap.ext
    intro y
    exact LinearMap.congr_fun hab y
  · intro f
    let s : Finset ℍ[ℚ] := {(1 : ℍ[ℚ]), rational_quaternion_basis.j}
    obtain ⟨a, ha⟩ :=
      jacobson_density (quaternion_cyclic_cubic_linear_to_end_linear f) s
    refine ⟨a, ?_⟩
    apply LinearMap.ext
    intro x
    -- The source proof uses that `1` and `j` form a basis over the cubic coefficient field.
    have hx :
        x ∈ Submodule.span ↥quaternion_cubic_subfield
          ({(1 : ℍ[ℚ]), rational_quaternion_basis.j} : Set ℍ[ℚ]) := by
      rw [quaternion_cubic_subfield_span_one_j]
      simp
    rw [Submodule.mem_span_pair] at hx
    rcases hx with ⟨u, v, rfl⟩
    have h1 : f (1 : ℍ[ℚ]) = actionHom a (1 : ℍ[ℚ]) := by
      -- Density matches `f` and the image-algebra action on the first basis vector.
      have h := ha 1 (by simp [s])
      simpa [actionHom, quaternion_cyclic_cubic_linear_to_end_linear, s] using h
    have hj :
        f rational_quaternion_basis.j =
          actionHom a rational_quaternion_basis.j := by
      -- The same comparison on `j` is enough because `{1, j}` spans `ℍ[ℚ]` over `K`.
      have h := ha rational_quaternion_basis.j (by simp [s])
      simpa [actionHom, quaternion_cyclic_cubic_linear_to_end_linear, s] using h
    calc
      actionHom a (u • (1 : ℍ[ℚ]) + v • rational_quaternion_basis.j)
          = u • actionHom a (1 : ℍ[ℚ]) +
              v • actionHom a rational_quaternion_basis.j := by
              simp
      _ = u • f (1 : ℍ[ℚ]) + v • f rational_quaternion_basis.j := by
            rw [← h1, ← hj]
      _ = f (u • (1 : ℍ[ℚ]) + v • rational_quaternion_basis.j) := by
            simp

/-- Helper for Exercise 13-13.1-14: a chosen algebra equivalence realizing Serre's
double-centralizer step. -/
noncomputable def quaternion_cyclic_imageSubalgebra_algEquiv_moduleEnd_cubic_subfield :
    quaternion_cyclic_imageSubalgebra ≃ₐ[ℚ]
      Module.End ↥quaternion_cubic_subfield ℍ[ℚ] :=
  Classical.choice quaternion_cyclic_imageSubalgebra_algEquiv_moduleEnd_cubic_subfield_exists

/-- Helper for Exercise 13-13.1-14: the standard function-space endomorphism ring carries the
expected cubic-subfield algebra structure explicitly. -/
local instance quaternion_cubic_subfield_fun_end_algebra :
    Algebra ↥quaternion_cubic_subfield
      ((Fin 2 → ↥quaternion_cubic_subfield) →ₗ[↥quaternion_cubic_subfield]
        Fin 2 → ↥quaternion_cubic_subfield) :=
  Module.End.instAlgebra
    ↥quaternion_cubic_subfield ↥quaternion_cubic_subfield
    (Fin 2 → ↥quaternion_cubic_subfield)

/-- Helper for Exercise 13-13.1-14: Serre's `{1, j}` basis identifies `End_K(ℍ[ℚ])` with
`M₂(K)`, viewed as a `ℚ`-algebra equivalence by restriction of scalars. -/
noncomputable def quaternion_cubic_subfield_moduleEnd_algEquiv_matrix_over_Q :
    Module.End ↥quaternion_cubic_subfield ℍ[ℚ] ≃ₐ[ℚ]
      Matrix (Fin 2) (Fin 2) ↥quaternion_cubic_subfield :=
  -- Conjugate to the standard function-space model before applying the matrix equivalence.
  (quaternion_cubic_subfield_basis_one_j.equivFun.conjAlgEquiv ℚ).trans
    ((algEquivMatrix' (R := ↥quaternion_cubic_subfield) (n := Fin 2)).restrictScalars ℚ)

/-- Helper for Exercise 13-13.1-14: the image algebra is already Serre's `M₂(K)` once the
double-centralizer step is followed by the `{1, j}` matrix model. -/
noncomputable def quaternion_cyclic_imageSubalgebra_algEquiv_matrix_over_cubic_subfield :
    quaternion_cyclic_imageSubalgebra ≃ₐ[ℚ]
      Matrix (Fin 2) (Fin 2) ↥quaternion_cubic_subfield :=
  quaternion_cyclic_imageSubalgebra_algEquiv_moduleEnd_cubic_subfield.trans
    quaternion_cubic_subfield_moduleEnd_algEquiv_matrix_over_Q

end

end Representation
