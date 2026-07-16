import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.RealizableOver
import LinearRepresentations_Serre_1977.Serre.Chap18.Corollary_18_18_2_3
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_6_3.SourceCharacters
import LinearRepresentations_Serre_1977.Serre.Chap14.Remark_14_14_5_1.Modular.GaloisDescent

noncomputable section

open CategoryTheory
open Representation
open AlternatingGroupFive

local notation "A5" => alternatingGroup (Fin 5)
local notation "𝔽₄" => FiniteField.Extension (ZMod 2) 2 2

namespace Representation

/-- Helper for Exercise 18-18.6-3: use the canonical inclusion of prime-to-`2` roots of unity in
`𝔽₄ˣ` when evaluating Brauer characters on `PRegularConjClass A₅ 2`. -/
abbrev a5_modTwo_unitsLift_f4 : PrimeToPRoot 2 𝔽₄ →* 𝔽₄ˣ :=
  (primeToPRoots 2 𝔽₄).subtype

/-- Helper for Exercise 18-18.6-3: the algebraic closure of `𝔽₄`, used as the splitting field over
which the modular (Brauer) characters of `A₅` in characteristic `2` are defined. The owner
`Representation.modularCharacter` requires an algebraically closed field of coefficients, so the
nonisomorphism criterion below is phrased over `AlgebraicClosure 𝔽₄`. -/
abbrev F4bar := AlgebraicClosure 𝔽₄

/-- Helper for Exercise 18-18.6-3: the canonical inclusion of prime-to-`2` roots of unity in
`(AlgebraicClosure 𝔽₄)ˣ`, used when evaluating Brauer characters on `PRegularConjClass A₅ 2`. -/
abbrev a5_modTwo_unitsLift_f4bar : PrimeToPRoot 2 F4bar →* F4barˣ :=
  (primeToPRoots 2 F4bar).subtype

/-- Helper for Exercise 18-18.6-3: pointwise equality of `𝔽₄`-valued functions on the
`2`-regular classes of `A₅` may be pulled back from any extension field of `𝔽₄` by injectivity of
the scalar map. -/
theorem a5_pregular_class_function_eq_of_map_eq
    {K : Type*} [Field K] [Algebra 𝔽₄ K]
    {f g : PRegularConjClass A5 2 → 𝔽₄}
    (hfg : (fun c ↦ algebraMap 𝔽₄ K (f c)) = fun c ↦ algebraMap 𝔽₄ K (g c)) :
    f = g := by
  -- Compare the two class functions pointwise and cancel the injective coefficient map.
  funext c
  exact (algebraMap 𝔽₄ K).injective (congrFun hfg c)

/-- Helper for Exercise 18-18.6-3: Serre's two source degree-`2` Brauer rows remain distinct on
the explicit `2`-regular classes of `A₅`. This records that the remaining gap is the owner-level
construction, not ambiguity in the target character functions. -/
theorem a5_source_degree_two_character_functions_ne_modTwo :
    (fun c : PRegularConjClass A5 2 ↦
      (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi3_phi_psi : 𝔽₄) -
        (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi1 : 𝔽₄)) ≠
      (fun c : PRegularConjClass A5 2 ↦
        (alternating_group_five_decomposition_matrix_mod_two
            (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
            OrdinaryIrreducible.chi3_psi_phi : 𝔽₄) -
          (alternating_group_five_decomposition_matrix_mod_two
            (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
            OrdinaryIrreducible.chi1 : 𝔽₄)) := by
  intro hEq
  let cφ : PRegularConjClass A5 2 :=
    alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
      BrauerProjectiveModTwo.degreeTwo_from_chi3_phi_psi
  have hphi := congrFun a5_source_degree_two_character_function_phi_modTwo cφ
  have hpsi := congrFun a5_source_degree_two_character_function_psi_modTwo cφ
  have hvalue : ((1 : 𝔽₄) = 0) := by
    -- Evaluate both source rows on the split `5`-cycle class labeled by `φ`.
    have heval := congrFun hEq cφ
    simpa [cφ] using hphi.symm.trans (heval.trans hpsi)
  exact one_ne_zero hvalue

/-- Helper for Exercise 18-18.6-3: the reduced row `χ₃,φ,ψ - χ₁` is not the trivial Brauer
character. This is the source-faithful obstruction to a degree-`1` simple quotient in the
`φ`-branch. -/
theorem a5_source_degree_two_character_function_phi_ne_trivial_modTwo :
    (fun c : PRegularConjClass A5 2 ↦
      (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi3_phi_psi : 𝔽₄) -
        (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi1 : 𝔽₄)) ≠
      fun _ : PRegularConjClass A5 2 ↦ (1 : 𝔽₄) := by
  intro hEq
  let c1 : PRegularConjClass A5 2 :=
    alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
      BrauerProjectiveModTwo.trivial
  have hphi := congrFun a5_source_degree_two_character_function_phi_modTwo c1
  have hvalue : (0 : 𝔽₄) = 1 := by
    -- Evaluate the reduced row at the identity class, where Serre's source function vanishes.
    have heval := congrFun hEq c1
    simpa [c1] using hphi.symm.trans heval
  exact zero_ne_one hvalue

/-- Helper for Exercise 18-18.6-3: the reduced row `χ₃,ψ,φ - χ₁` is not the trivial Brauer
character. This is the symmetric degree-`1` exclusion needed in the `ψ`-branch. -/
theorem a5_source_degree_two_character_function_psi_ne_trivial_modTwo :
    (fun c : PRegularConjClass A5 2 ↦
      (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi3_psi_phi : 𝔽₄) -
        (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi1 : 𝔽₄)) ≠
      fun _ : PRegularConjClass A5 2 ↦ (1 : 𝔽₄) := by
  intro hEq
  let c1 : PRegularConjClass A5 2 :=
    alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
      BrauerProjectiveModTwo.trivial
  have hpsi := congrFun a5_source_degree_two_character_function_psi_modTwo c1
  have hvalue : (0 : 𝔽₄) = 1 := by
    -- The companion reduced row also vanishes on the identity class.
    have heval := congrFun hEq c1
    simpa [c1] using hpsi.symm.trans heval
  exact zero_ne_one hvalue

/-- Helper for Exercise 18-18.6-3: the reduced row `χ₃,φ,ψ - χ₁` is genuinely nonzero on the
explicit `φ`-labeled `5`-cycle class. This isolates the future quotient argument from any
ambiguity about whether the target Brauer row could vanish. -/
theorem a5_source_degree_two_character_function_phi_ne_zero_modTwo :
    (fun c : PRegularConjClass A5 2 ↦
      (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi3_phi_psi : 𝔽₄) -
        (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi1 : 𝔽₄)) ≠
      0 := by
  intro hEq
  let cφ : PRegularConjClass A5 2 :=
    alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
      BrauerProjectiveModTwo.degreeTwo_from_chi3_phi_psi
  have hphi := congrFun a5_source_degree_two_character_function_phi_modTwo cφ
  have hvalue : (1 : 𝔽₄) = 0 := by
    -- Evaluate at the split `5`-cycle class where the `φ`-row takes the value `1`.
    have heval := congrFun hEq cφ
    simpa [Pi.zero_apply, cφ] using hphi.symm.trans heval
  exact one_ne_zero hvalue

/-- Helper for Exercise 18-18.6-3: the companion reduced row `χ₃,ψ,φ - χ₁` is also genuinely
nonzero, now detected on the `ψ`-labeled `5`-cycle class. -/
theorem a5_source_degree_two_character_function_psi_ne_zero_modTwo :
    (fun c : PRegularConjClass A5 2 ↦
      (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi3_psi_phi : 𝔽₄) -
        (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi1 : 𝔽₄)) ≠
      0 := by
  intro hEq
  let cψ : PRegularConjClass A5 2 :=
    alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
      BrauerProjectiveModTwo.degreeTwo_from_chi3_psi_phi
  have hpsi := congrFun a5_source_degree_two_character_function_psi_modTwo cψ
  have hvalue : (1 : 𝔽₄) = 0 := by
    -- Evaluate at the other split `5`-cycle class where the `ψ`-row takes the value `1`.
    have heval := congrFun hEq cψ
    simpa [Pi.zero_apply, cψ] using hpsi.symm.trans heval
  exact one_ne_zero hvalue

/-- Helper for Exercise 18-18.6-3: the unreduced source row `χ₃,φ,ψ` is the explicit
`(1, 1, 0, 0)` Brauer function on Serre's four `2`-regular labels. This is the owner-level row
supplied by the theorem-local degree-`3` reduction package. -/
theorem a5_source_degree_three_character_function_phi_modTwo :
    (fun c : PRegularConjClass A5 2 ↦
      (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi3_phi_psi : 𝔽₄)) =
      fun c ↦
        match alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c with
        | .trivial => 1
        | .degreeTwo_from_chi3_phi_psi => 1
        | .degreeTwo_from_chi3_psi_phi => 0
        | .degreeFour => 0 := by
  -- Read the `χ₃,φ,ψ` column of Serre's decomposition matrix after the explicit class labeling.
  ext c
  cases hφ : alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c <;>
    simp [hφ, alternating_group_five_decomposition_matrix_mod_two]

/-- Helper for Exercise 18-18.6-3: the unreduced source row `χ₃,ψ,φ` is the explicit
`(1, 0, 1, 0)` Brauer function on the same four labels. This is the symmetric owner-level row
behind the second theorem-local degree-`3` reduction package. -/
theorem a5_source_degree_three_character_function_psi_modTwo :
    (fun c : PRegularConjClass A5 2 ↦
      (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi3_psi_phi : 𝔽₄)) =
      fun c ↦
        match alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c with
        | .trivial => 1
        | .degreeTwo_from_chi3_phi_psi => 0
        | .degreeTwo_from_chi3_psi_phi => 1
        | .degreeFour => 0 := by
  -- The companion `χ₃,ψ,φ` column swaps the two split `5`-cycle labels and keeps the same
  -- trivial/degree-`4` values.
  ext c
  cases hφ : alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c <;>
    simp [hφ, alternating_group_five_decomposition_matrix_mod_two]

/-- Helper for Exercise 18-18.6-3: Serre's reduced `φ`-row vanishes on the trivial Brauer label.
This is the concrete value that later forces the corrected owner statement to split off a trivial
constituent before reaching the degree-`2` source slot. -/
theorem a5_source_degree_two_character_function_phi_value_at_trivial_label :
    (fun c : PRegularConjClass A5 2 ↦
      (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi3_phi_psi : 𝔽₄) -
        (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi1 : 𝔽₄))
      (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
        BrauerProjectiveModTwo.trivial) = 0 := by
  let c1 : PRegularConjClass A5 2 :=
    alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
      BrauerProjectiveModTwo.trivial
  -- Evaluate the explicit source row on the class singled out by the trivial Brauer label.
  have hphi := congrFun a5_source_degree_two_character_function_phi_modTwo c1
  simpa [c1] using hphi

/-- Helper for Exercise 18-18.6-3: the companion reduced `ψ`-row also vanishes on the trivial
Brauer label. This is the same obstruction to identifying a `3`-dimensional owner directly with
the reduced source row. -/
theorem a5_source_degree_two_character_function_psi_value_at_trivial_label :
    (fun c : PRegularConjClass A5 2 ↦
      (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi3_psi_phi : 𝔽₄) -
        (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi1 : 𝔽₄))
      (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
        BrauerProjectiveModTwo.trivial) = 0 := by
  let c1 : PRegularConjClass A5 2 :=
    alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
      BrauerProjectiveModTwo.trivial
  -- The same explicit table computation applies to the second source row.
  have hpsi := congrFun a5_source_degree_two_character_function_psi_modTwo c1
  simpa [c1] using hpsi

/-- Helper for Exercise 18-18.6-3: Serre's reduced `φ`-row takes the value `1` on the
`φ`-labeled split `5`-cycle class. -/
theorem a5_source_degree_two_character_function_phi_value_at_phi_label :
    (fun c : PRegularConjClass A5 2 ↦
      (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi3_phi_psi : 𝔽₄) -
        (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi1 : 𝔽₄))
      (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
        BrauerProjectiveModTwo.degreeTwo_from_chi3_phi_psi) = 1 := by
  let cφ : PRegularConjClass A5 2 :=
    alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
      BrauerProjectiveModTwo.degreeTwo_from_chi3_phi_psi
  -- On the `φ`-labeled split `5`-cycle class, the table isolates the first degree-`2` row.
  have hphi := congrFun a5_source_degree_two_character_function_phi_modTwo cφ
  simpa [cφ] using hphi

/-- Helper for Exercise 18-18.6-3: Serre's reduced `ψ`-row takes the value `1` on the
`ψ`-labeled split `5`-cycle class. -/
theorem a5_source_degree_two_character_function_psi_value_at_psi_label :
    (fun c : PRegularConjClass A5 2 ↦
      (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi3_psi_phi : 𝔽₄) -
        (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi1 : 𝔽₄))
      (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
        BrauerProjectiveModTwo.degreeTwo_from_chi3_psi_phi) = 1 := by
  let cψ : PRegularConjClass A5 2 :=
    alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
      BrauerProjectiveModTwo.degreeTwo_from_chi3_psi_phi
  -- The companion split `5`-cycle class isolates the second degree-`2` row.
  have hpsi := congrFun a5_source_degree_two_character_function_psi_modTwo cψ
  simpa [cψ] using hpsi

/-- Helper for Exercise 18-18.6-3: any two simple `(AlgebraicClosure 𝔽₄)[A₅]`-slots with Serre's
two distinct degree-`2` source Brauer rows (transported to the splitting field) are automatically
nonisomorphic.

The modular-character owner `Representation.modularCharacter` is only defined over an algebraically
closed field of coefficients, so this nonisomorphism criterion is phrased over `AlgebraicClosure 𝔽₄`,
with the explicit `𝔽₄`-valued source rows pushed forward by `algebraMap 𝔽₄ (AlgebraicClosure 𝔽₄)`.
-/
theorem a5_source_degree_two_slots_nonisomorphic_of_character_eq
    {Eφ Eψ : FDRep F4bar A5}
    (hEφ_char :
      FDRep.modularCharacterOnPRegularConjClass (p := 2) Eφ
          (PrimeToPRoot.toFieldLift a5_modTwo_unitsLift_f4bar) =
        (fun c : PRegularConjClass A5 2 ↦
          algebraMap 𝔽₄ F4bar
            ((alternating_group_five_decomposition_matrix_mod_two
                (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
                OrdinaryIrreducible.chi3_phi_psi : 𝔽₄) -
              (alternating_group_five_decomposition_matrix_mod_two
                (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
                OrdinaryIrreducible.chi1 : 𝔽₄))))
    (hEψ_char :
      FDRep.modularCharacterOnPRegularConjClass (p := 2) Eψ
          (PrimeToPRoot.toFieldLift a5_modTwo_unitsLift_f4bar) =
        (fun c : PRegularConjClass A5 2 ↦
          algebraMap 𝔽₄ F4bar
            ((alternating_group_five_decomposition_matrix_mod_two
                (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
                OrdinaryIrreducible.chi3_psi_phi : 𝔽₄) -
              (alternating_group_five_decomposition_matrix_mod_two
                (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
                OrdinaryIrreducible.chi1 : 𝔽₄)))) :
    ¬ Nonempty (Eφ ≅ Eψ) := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hF4Char : CharP 𝔽₄ 2 := by
    rw [← Algebra.charP_iff (ZMod 2) 𝔽₄ 2]
    exact ZMod.charP 2
  letI : CharP 𝔽₄ 2 := hF4Char
  intro hIso
  have hchar_eq :
      FDRep.modularCharacterOnPRegularConjClass (p := 2) Eφ
          (PrimeToPRoot.toFieldLift a5_modTwo_unitsLift_f4bar) =
        FDRep.modularCharacterOnPRegularConjClass (p := 2) Eψ
          (PrimeToPRoot.toFieldLift a5_modTwo_unitsLift_f4bar) :=
    modularCharacterOnPRegularConjClass_eq_of_nonempty_iso
      (k := 𝔽₄) (p := 2)
      (lift := PrimeToPRoot.toFieldLift a5_modTwo_unitsLift_f4bar) hIso
  have hmap_eq :
      (fun c : PRegularConjClass A5 2 ↦
        algebraMap 𝔽₄ F4bar
          ((alternating_group_five_decomposition_matrix_mod_two
              (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
              OrdinaryIrreducible.chi3_phi_psi : 𝔽₄) -
            (alternating_group_five_decomposition_matrix_mod_two
              (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
              OrdinaryIrreducible.chi1 : 𝔽₄))) =
        (fun c : PRegularConjClass A5 2 ↦
          algebraMap 𝔽₄ F4bar
            ((alternating_group_five_decomposition_matrix_mod_two
                (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
                OrdinaryIrreducible.chi3_psi_phi : 𝔽₄) -
              (alternating_group_five_decomposition_matrix_mod_two
                (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
                OrdinaryIrreducible.chi1 : 𝔽₄))) := by
    -- The public iso-invariance theorem transfers equality of the two descended Brauer characters
    -- to equality of the two mapped explicit source rows.
    calc
      (fun c : PRegularConjClass A5 2 ↦
        algebraMap 𝔽₄ F4bar
          ((alternating_group_five_decomposition_matrix_mod_two
              (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
              OrdinaryIrreducible.chi3_phi_psi : 𝔽₄) -
            (alternating_group_five_decomposition_matrix_mod_two
              (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
              OrdinaryIrreducible.chi1 : 𝔽₄))) =
          FDRep.modularCharacterOnPRegularConjClass (p := 2) Eφ
            (PrimeToPRoot.toFieldLift a5_modTwo_unitsLift_f4bar) := by
              symm
              exact hEφ_char
      _ =
          FDRep.modularCharacterOnPRegularConjClass (p := 2) Eψ
            (PrimeToPRoot.toFieldLift a5_modTwo_unitsLift_f4bar) := hchar_eq
      _ =
          (fun c : PRegularConjClass A5 2 ↦
            algebraMap 𝔽₄ F4bar
              ((alternating_group_five_decomposition_matrix_mod_two
                  (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
                  OrdinaryIrreducible.chi3_psi_phi : 𝔽₄) -
                (alternating_group_five_decomposition_matrix_mod_two
                  (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
                  OrdinaryIrreducible.chi1 : 𝔽₄))) := by
            exact hEψ_char
  have hbase_eq :
      (fun c : PRegularConjClass A5 2 ↦
        (alternating_group_five_decomposition_matrix_mod_two
            (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
            OrdinaryIrreducible.chi3_phi_psi : 𝔽₄) -
          (alternating_group_five_decomposition_matrix_mod_two
            (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
            OrdinaryIrreducible.chi1 : 𝔽₄)) =
        (fun c : PRegularConjClass A5 2 ↦
          (alternating_group_five_decomposition_matrix_mod_two
              (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
              OrdinaryIrreducible.chi3_psi_phi : 𝔽₄) -
            (alternating_group_five_decomposition_matrix_mod_two
              (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
              OrdinaryIrreducible.chi1 : 𝔽₄)) :=
    a5_pregular_class_function_eq_of_map_eq (K := F4bar) hmap_eq
  exact a5_source_degree_two_character_functions_ne_modTwo hbase_eq

end Representation
