import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Tactic
import StacksProject_2024.stacks_project.Chap22.Definition_22_4_3
import StacksProject_2024.stacks_project.Chap22.Lemma_22_13_3
import StacksProject_2024.stacks_project.Chap22.Example_22_26_8_Differential_graded_category_of_differential_graded_modules

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]

local notation "DGA" => CochainDGAlgebra R
local notation "Mod_(" A ")" => DifferentialGradedModule A

-- Semantic recall note: `lean_leansearch` only surfaced generic cochain-complex owners, so this
-- repair follows the checked Chapter 22 DG-module owners from
-- `Definition_22_4_3` and `Example_22_26_8_Differential_graded_category_of_differential_graded_modules`.

namespace DifferentialGradedModule

/-- Helper for Lemma 22.16.2: transport across a degree equality commutes with scalar
multiplication on homogeneous pieces of `A`. -/
private theorem castX_smul (A : DGA) {i i' : ℤ} (h : i = i') (r : R) (x : A.X i) :
    cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) h) (r • x) =
      r • cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) h) x := by
  -- Transport on a homogeneous component is definitionally compatible with the `R`-module
  -- structure once the degree equality is reduced to `rfl`.
  cases h
  rfl

/-- Helper for Lemma 22.16.2: the two `add_comm` transports on `A.X` cancel each other. -/
private theorem castX_addComm_cancel (A : DGA) (i j : ℤ) (x : A.X (i + j)) :
    cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) (add_comm j i))
      (cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) (add_comm i j)) x) = x := by
  -- This is the specific cast normalization needed when the opposite-action formula is expanded
  -- and immediately transported back to the source-facing right action.
  rw [cast_cast]
  simp

/-- Helper for Lemma 22.16.2: the differential of a cochain differential graded algebra squares
to zero on homogeneous elements. -/
theorem CochainDGAlgebra.d_sq_apply (A : DGA) (n : ℤ) (x : A.X n) :
    A.d (n + 1) (A.d n x) = 0 := by
  -- Evaluate the cochain-complex identity `d ≫ d = 0` at the homogeneous element `x`.
  have hsq :
      (A.toCochainComplex.d n (n + 1) ≫ A.toCochainComplex.d (n + 1) ((n + 1) + 1)).hom x = 0 := by
    exact
      LinearMap.congr_fun
        (ModuleCat.hom_ext_iff.mp
          (A.toCochainComplex.d_comp_d n (n + 1) ((n + 1) + 1)))
        x
  have hsq' := hsq
  change
    (A.toCochainComplex.d (n + 1) ((n + 1) + 1)).hom
        ((A.toCochainComplex.d n (n + 1)).hom x) = 0 at hsq'
  change (A.d (n + 1)).hom ((A.d n).hom x) = 0
  simpa [CochainDGAlgebra.d_eq_toCochainComplex_d] using hsq'

/-- Helper for Lemma 22.16.2: the direct regular action sends `r • 1` to `r • x` in the exact
normal form required by `DifferentialGradedModule.smul_one`. -/
private theorem regular_smul_one (A : DGA) (r : R) (p : ℤ) (x : A.X p) :
    A.mul p 0 x (r • A.one) = cast (rightDGModuleZeroTargetEq p) (r • x) :=
  -- TODO: normalize `A.mul p 0 x (r • A.one)` by `LinearMap.map_smul`, transport the right unit
  -- law `A.mul_one_apply p x` across `rightDGModuleZeroTargetEq p`, and finish with one cast/smul
  -- commutation step.
  sorry

/-- Helper for Lemma 22.16.2: the direct regular action satisfies the Leibniz rule in the exact
field-shaped normal form required by `DifferentialGradedModule.comm_d`. -/
private theorem regular_comm_d (A : DGA) (p i : ℤ) (x : A.X p) (a : A.X i) :
    A.d (p + i) (A.mul p i x a) =
      cast (rightDGModuleDLeftTargetEq p i) (A.mul (p + 1) i (A.d p x) a) +
        (p.negOnePow : R) •
          cast (rightDGModuleDRightTargetEq p i) (A.mul p (i + 1) x (A.d i a)) := by
  -- The direct regular module uses the cochain Leibniz rule without any extra transport layer.
  simpa [Units.smul_def, ← Int.cast_smul_eq_zsmul R] using A.leibniz_apply p i x a

/-- Helper for Lemma 22.16.2: the unit of a cochain differential graded algebra is a cycle in
degree `0`. -/
theorem CochainDGAlgebra.d_one_eq_zero (A : DGA) : A.d 0 A.one = 0 :=
  -- TODO: rewrite `A.leibniz_apply 0 0 A.one A.one` to
  -- `A.d 0 A.one = A.d 0 A.one + A.d 0 A.one` using `A.one_mul_apply` and `A.mul_one_apply`, then
  -- cancel one copy in the additive group `A.X 1`.
  sorry

/-- The regular right differential graded module of a cochain differential graded algebra. -/
noncomputable def regular (A : DGA) : Mod_(A) where
  X := A.X
  d := fun n ↦ ModuleCat.Hom.hom (A.d n)
  smul := A.mul
  d_sq := by
    intro n x
    -- The regular differential is the algebra differential on the underlying complex.
    simpa using CochainDGAlgebra.d_sq_apply A n x
  smul_one := by
    intro r p x
    -- The direct source-facing regular action reduces the unit law to the algebra unit law.
    exact regular_smul_one A r p x
  smul_mul := by
    intro p i j x a b
    -- Associativity is exactly the algebra multiplication law on homogeneous pieces.
    simpa using (A.mul_assoc_apply p i j x a b).symm
  comm_d := by
    intro p i x a
    -- The direct regular action packages the cochain Leibniz rule with the canonical target
    -- reassociation casts used by the DG-module owner.
    exact regular_comm_d A p i x a

/-- Helper for Lemma 22.16.2: the source-facing regular action is ordinary multiplication. -/
@[simp] theorem regular_smul_apply (A : DGA) (p i : ℤ) (x : A.X p) (a : A.X i) :
    (regular A).smul p i x a = A.mul p i x a := by
  -- The direct regular module uses the multiplication map of `A` definitionally.
  rfl

/-- The underlying cochain complex of a differential graded module. -/
noncomputable def toCochainComplex {A : DGA} (M : Mod_(A)) : CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.of M.X (fun n ↦ ModuleCat.ofHom (M.d n)) (fun n ↦ by
    ext x
    exact M.d_sq n x)

/-- The underlying cochain complex of a differential graded module has homology in every degree. -/
noncomputable instance instHasHomology {A : DGA} (M : Mod_(A)) (n : ℤ) :
    M.toCochainComplex.HasHomology n := by
  exact ⟨⟨ShortComplex.HomologyData.ofAbelian (M.toCochainComplex.sc n)⟩⟩

/-- The cycles object of a differential graded module in degree `n`. -/
noncomputable abbrev cycles {A : DGA} (M : Mod_(A)) (n : ℤ) :=
  M.toCochainComplex.cycles n

/-- The canonical inclusion of cycles into the degree-`n` term. -/
noncomputable abbrev iCycles {A : DGA} (M : Mod_(A)) (n : ℤ) : M.cycles n ⟶ M.X n :=
  M.toCochainComplex.iCycles n

/-- The homology object of a differential graded module in degree `n`. -/
noncomputable abbrev homology {A : DGA} (M : Mod_(A)) (n : ℤ) :=
  M.toCochainComplex.homology n

/-- The canonical projection from cycles to homology in degree `n`. -/
noncomputable abbrev homologyπ {A : DGA} (M : Mod_(A)) (n : ℤ) :
    M.cycles n ⟶ M.homology n :=
  M.toCochainComplex.homologyπ n

end DifferentialGradedModule

namespace DifferentialGradedCategory.CompHom

/-- A convenient notation for the Chapter 22 source object `A[k]` in `Comp(Mod_(A,d))`. -/
private abbrev regularShiftComp (A : DGA) (k : ℤ) : Comp R (Mod_(A)) :=
  ⟨(DifferentialGradedModule.regular A)[k]⟩

/-- A convenient notation for the Chapter 22 source object `A[k]` in `K(Mod_(A,d))`. -/
private abbrev regularShiftK (A : DGA) (k : ℤ) : K R (Mod_(A)) :=
  ⟨(DifferentialGradedModule.regular A)[k]⟩

/-- Helper for Lemma 22.16.2: the shifted regular module is generated by the shifted unit in
degree `-k`. -/
private def shiftedOne (A : DGA) (k : ℤ) : ((DifferentialGradedModule.regular A)[k]).X (-k) := by
  change A.toCochainComplex.X (-k + k)
  exact
    cast
      (congrArg (fun n : ℤ ↦ (A.toCochainComplex.X n : Type u))
        (by omega : (0 : ℤ) = -k + k))
      A.one

/-- Helper for Lemma 22.16.2: the shifted unit generator is closed. -/
private theorem shiftedOne_closed (A : DGA) (k : ℤ) :
    ((DifferentialGradedModule.regular A)[k]).d (-k) (shiftedOne A k) = 0 := by
  -- Rewrite the shifted differential to `d_A(1)` and use that the unit is a cycle.
  -- TODO: after expanding `shift_d`, normalize the two arithmetic casts back to degree `0`, then
  -- rewrite the resulting differential by `DifferentialGradedModule.CochainDGAlgebra.d_one_eq_zero`.
  sorry

/-- Helper for Lemma 22.16.2: every homogeneous element of the shifted regular module is the
shifted unit acted on by that element. -/
private theorem shiftedOne_smul (A : DGA) (k n : ℤ) (x : A.X (n + k)) :
    cast
      (congrArg (fun m : ℤ ↦ (A.X m : Type u))
        (by omega : ((-k : ℤ) + (n + k)) + k = n + k))
      (((DifferentialGradedModule.regular A)[k]).smul (-k) (n + k) (shiftedOne A k) x) = x := by
  -- Rewrite the shifted source action to ordinary multiplication by `1`.
  -- TODO: expand `shift_smul`, transport the shifted unit back to degree `0`, and finish with
  -- `A.one_mul_apply (n + k) x` in the direct regular-module spelling.
  sorry

/-- Lemma 22.16.2 (1): for a cochain differential graded algebra `A` and a differential graded
right `A`-module `M`, the morphisms in `Mod_(A,d)` from the shifted regular module `A[k]` to `M`
are in canonical bijection with the cycles `Ker(d : M^{-k} → M^{-k + 1})`. In the Chapter 22
owners used here, `Mod_(A,d)` is `Comp R (DifferentialGradedModule A)`, `A` is the regular right
differential graded module `DifferentialGradedModule.regular A`, and `A[k]` uses the shift API
of Definition `22.4.3`. -/
@[stacks 09K1]
noncomputable def freeModuleShiftHomToCyclesEquiv
    (A : DGA) (M : Mod_(A)) (k : ℤ) :
    (regularShiftComp A k ⟶ ⟨M⟩) ≃ M.cycles (-k) where
  toFun φ :=
    let shiftedOne : ((DifferentialGradedModule.regular A)[k]).X (-k) := shiftedOne A k
    let f : ((DifferentialGradedModule.regular A)[k]) ⟶[0] M := φ.1
    by
      simpa using
        (ModuleCat.homEquiv
          (M.toCochainComplex.liftCycles
            (ModuleCat.ofHom ((LinearMap.id : R →ₗ[R] R).smulRight (f.1 (-k) shiftedOne)))
            ((-k) + 1)
            (by simp)
            (by
              -- TODO: evaluate the closedness equation `φ.closed` at the shifted unit generator and
              -- rewrite the source differential with `shiftedOne_closed`.
              sorry)) 1)
  invFun z :=
    let z0 : M.X (-k) := (ModuleCat.Hom.hom (M.iCycles (-k))) z
    ⟨⟨fun n ↦
          castLinearMap
            (congrArg M.X (by omega : (-k : ℤ) + (n + k) = n + 0))
            (M.smul (-k) (n + k) z0),
        by
          intro n m x a
          -- TODO: rewrite both sides with `M.smul_mul` and the shift-source generator indexing.
          sorry⟩,
      by
        -- TODO: prove the differential condition using that `z0` is a cycle and the shifted
        -- source differential is `(-1)^k d_A`.
        sorry⟩
  left_inv := by
    intro φ
    -- TODO: use right `A`-linearity and the shifted unit generator to prove that a morphism is
    -- determined by the image of `1 ∈ A^0`.
    sorry
  right_inv := by
    intro z
    -- TODO: show the inverse sends a cycle back to the same cycle after evaluating at the shifted
    -- unit generator.
    sorry

/-- The source-facing cycles comparison is bijective. -/
theorem freeModuleShiftHomToCycles_bijective
    (A : DGA) (M : Mod_(A)) (k : ℤ) :
    Function.Bijective (freeModuleShiftHomToCyclesEquiv A M k) :=
  (freeModuleShiftHomToCyclesEquiv A M k).bijective

/-- The canonical comparison from morphisms in `K(Mod_(A,d))` out of `A[k]` to cohomology in
degree `-k`, defined by sending a represented morphism to the corresponding cycle class. -/
noncomputable def freeModuleShiftHomotopyToHomologyFun
    (A : DGA) (M : Mod_(A)) (k : ℤ) :
    (regularShiftK A k ⟶ ⟨M⟩) → M.homology (-k) :=
  Quotient.lift
    (fun φ : regularShiftComp A k ⟶ ⟨M⟩ ↦
      (ModuleCat.Hom.hom (M.homologyπ (-k)))
        (freeModuleShiftHomToCyclesEquiv A M k φ))
    (by
      intro φ ψ hφψ
      -- TODO: turn `hφψ` into a degree `-1` witness via `CompHom.homotopic_zero_iff` and show
      -- the two cycle representatives differ by a boundary.
      sorry)

/-- On a represented morphism in `Comp(Mod_(A,d))`, the homotopy-category comparison is the
homology class of the corresponding cycle. -/
theorem freeModuleShiftHomotopyToHomology_eq_homologyπ
    (A : DGA) (M : Mod_(A)) (k : ℤ) (φ : regularShiftComp A k ⟶ ⟨M⟩) :
    freeModuleShiftHomotopyToHomologyFun A M k φ.inK =
      (ModuleCat.Hom.hom (M.homologyπ (-k)))
        (freeModuleShiftHomToCyclesEquiv A M k φ) := by
  rfl

/-- Lemma 22.16.2 (2): for a cochain differential graded algebra `A` and a differential graded
right `A`-module `M`, the morphisms in `K(Mod_(A,d))` from the shifted regular module `A[k]` to
`M` are in canonical bijection with the cohomology group `H^{-k}(M)`. -/
@[stacks 09K1]
noncomputable def freeModuleShiftHomotopyToHomology
    (A : DGA) (M : Mod_(A)) (k : ℤ) :
    (regularShiftK A k ⟶ ⟨M⟩) ≃ M.homology (-k) where
  toFun := freeModuleShiftHomotopyToHomologyFun A M k
  invFun x :=
    let q : ModuleCat.of R R ⟶ M.homology (-k) :=
      ModuleCat.ofHom ((LinearMap.id : R →ₗ[R] R).smulRight x)
    let z : ModuleCat.of R R ⟶ M.cycles (-k) :=
      letI : Projective (ModuleCat.of R R) := by infer_instance
      Projective.factorThru q (M.homologyπ (-k))
    ((freeModuleShiftHomToCyclesEquiv A M k).symm ((ModuleCat.homEquiv z) 1)).inK
  left_inv := by
    intro φ
    -- TODO: compare the constructed preimage with `φ` by applying `freeModuleShiftHomotopyToHomologyFun`
    -- and using `CompHom.toHomotopyClass_eq_of_homotopic`.
    sorry
  right_inv := by
    intro x
    -- TODO: use `Projective.factorThru_comp` to show the chosen cycle lifts back to the original
    -- homology class `x`.
    sorry

/-- The source-facing homotopy-category comparison is bijective. -/
theorem freeModuleShiftHomotopyToHomology_bijective
    (A : DGA) (M : Mod_(A)) (k : ℤ) :
    Function.Bijective (freeModuleShiftHomotopyToHomology A M k) :=
  (freeModuleShiftHomotopyToHomology A M k).bijective

end DifferentialGradedCategory.CompHom

end
