import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Equiv.Perm Matrix
open scoped goldenRatio

namespace AlternatingGroupFive

/-- The ordinary irreducible characters used in Serre's `A₅` example. The two degree-`3`
characters are distinguished by their values `(φ, ψ)` and `(ψ, φ)` on the two `5`-cycle
classes. -/
inductive OrdinaryIrreducible
  | chi1
  | chi3_phi_psi
  | chi3_psi_phi
  | chi4
  | chi5
  deriving DecidableEq, Fintype

/-- The conjugacy-class labels for Serre's ordinary character table of `A₅`. The two `5`-cycle
classes are ordered so that `OrdinaryIrreducible.chi3_phi_psi` takes the values `φ` and `ψ` on
`fiveCycle_phi` and `fiveCycle_psi`, respectively. -/
inductive ConjugacyClass
  | identity
  | doubleTransposition
  | threeCycle
  | fiveCycle_phi
  | fiveCycle_psi
  deriving DecidableEq, Fintype

/-- The common ordered labels for the `p = 2` irreducible Brauer characters of `A₅` and the
corresponding indecomposable projective classes. This is the row index of the `p = 2`
decomposition matrix and, in the chapter's `cartanMatrix` convention, both the row and column
index of the `p = 2` Cartan matrix. The two degree-`2` labels are distinguished by which
degree-`3` ordinary character appears in their decomposition row. -/
inductive BrauerProjectiveModTwo
  | trivial
  | degreeTwo_from_chi3_phi_psi
  | degreeTwo_from_chi3_psi_phi
  | degreeFour
  deriving DecidableEq, Fintype

/-- The common ordered labels for the `p = 3` irreducible Brauer characters of `A₅` and the
corresponding indecomposable projective classes. This is the row index of the `p = 3`
decomposition matrix and, in the chapter's `cartanMatrix` convention, both the row and column
index of the `p = 3` Cartan matrix. The two degree-`3` labels are distinguished by the matching
ordinary degree-`3` character. -/
inductive BrauerProjectiveModThree
  | trivial
  | degreeThree_from_chi3_phi_psi
  | degreeThree_from_chi3_psi_phi
  | degreeFour
  deriving DecidableEq, Fintype

/-- The common ordered labels for the `p = 5` irreducible Brauer characters of `A₅` and the
corresponding indecomposable projective classes. This is the row index of the `p = 5`
decomposition matrix and, in the chapter's `cartanMatrix` convention, both the row and column
index of the `p = 5` Cartan matrix. -/
inductive BrauerProjectiveModFive
  | trivial
  | degreeThree
  | degreeFive
  deriving DecidableEq, Fintype

end AlternatingGroupFive

open AlternatingGroupFive

local notation "A5" => alternatingGroup (Fin 5)

/- Domain-style sampling for this remark:
* primary domain: modular representation theory of finite groups, specialized here to Serre's
  explicit `A₅` ordinary-character, decomposition, and Cartan tables;
* relevant owner declarations inspected upstream in the chapter/project:
  `Representation.decompositionHom`,
  `Representation.cartanHom`,
  `Representation.cartanMatrix`,
  `Representation.decompositionHom_toMatrix_eq_one_of_order_prime_to_p`;
* best owner abstraction for this file: Serre's tables are source-facing matrix data, but their
  indices should be the chapter's ordinary-simple and Brauer/projective basis labels rather than
  anonymous `Fin` coordinates;
* source/core/bridge triage:
  source-facing: these explicit `A₅` tables with Serre's chosen basis orderings;
  core/canonical: the chapter-level decomposition and Cartan owners determining the orientation of
    those basis labels;
  bridge/view: this file stays at the explicit table layer, so the Cartan matrices remain derived
    matrix companions `D * Dᵀ` of the recorded decomposition matrices.

Primitive data vs derived API:
* primitive data: the labeled ordinary irreducible character table and the three labeled
  decomposition matrices;
* derived API: the source-facing bridge from those labels to actual class functions on `A₅`,
  together with the three Cartan matrices and their explicit-value and determinant lemmas.
-/

/-- Remark 18-18.6-1: the ordinary irreducible character table of `A₅` in Serre's example, with
rows indexed by the labeled ordinary irreducible characters and columns indexed by the labeled
conjugacy classes. -/
def alternating_group_five_ordinary_irreducible_character_table :
    Matrix OrdinaryIrreducible ConjugacyClass ℝ
  | .chi1, .identity => 1
  | .chi1, .doubleTransposition => 1
  | .chi1, .threeCycle => 1
  | .chi1, .fiveCycle_phi => 1
  | .chi1, .fiveCycle_psi => 1
  | .chi3_phi_psi, .identity => 3
  | .chi3_phi_psi, .doubleTransposition => -1
  | .chi3_phi_psi, .threeCycle => 0
  | .chi3_phi_psi, .fiveCycle_phi => φ
  | .chi3_phi_psi, .fiveCycle_psi => ψ
  | .chi3_psi_phi, .identity => 3
  | .chi3_psi_phi, .doubleTransposition => -1
  | .chi3_psi_phi, .threeCycle => 0
  | .chi3_psi_phi, .fiveCycle_phi => ψ
  | .chi3_psi_phi, .fiveCycle_psi => φ
  | .chi4, .identity => 4
  | .chi4, .doubleTransposition => 0
  | .chi4, .threeCycle => 1
  | .chi4, .fiveCycle_phi => -1
  | .chi4, .fiveCycle_psi => -1
  | .chi5, .identity => 5
  | .chi5, .doubleTransposition => 1
  | .chi5, .threeCycle => -1
  | .chi5, .fiveCycle_phi => 0
  | .chi5, .fiveCycle_psi => 0

/-- A fixed representative of the `fiveCycle_phi` column in Serre's split `5`-cycle ordering for
the ordinary character table of `A₅`. -/
private def fiveCyclePhiRepresentative : A5 :=
  ⟨finRotate 5, by
    have h : finRotate (2 * 2 + 1) ∈ alternatingGroup (Fin (2 * 2 + 1)) :=
      finRotate_bit1_mem_alternatingGroup
    simpa using h⟩

/-- The labeled conjugacy class of an element of `A₅` in Serre's ordinary character table. The
two split `5`-cycle classes are ordered so that `OrdinaryIrreducible.chi3_phi_psi` has values
`(φ, ψ)` on `fiveCycle_phi` and `fiveCycle_psi`. -/
def conjugacyClass (g : A5) : ConjugacyClass :=
  if orderOf g = 1 then .identity
  else if orderOf g = 2 then .doubleTransposition
  else if orderOf g = 3 then .threeCycle
  else if IsConj g fiveCyclePhiRepresentative then .fiveCycle_phi
  else .fiveCycle_psi

namespace OrdinaryIrreducible

/-- The ordinary complex character of `A₅` attached to one of Serre's labeled rows in the
ordinary character table from `Remark 18-18.6-1`. -/
def character (χ : OrdinaryIrreducible) : A5 → ℂ :=
  fun g ↦ (alternating_group_five_ordinary_irreducible_character_table χ (conjugacyClass g) : ℂ)

@[simp] theorem character_apply (χ : OrdinaryIrreducible) (g : A5) :
    character χ g =
      (alternating_group_five_ordinary_irreducible_character_table χ (conjugacyClass g) : ℂ) :=
  rfl

end OrdinaryIrreducible

/-- Remark 18-18.6-1: the `p = 2` decomposition matrix in Serre's modular-character example for
`A₅`, with rows indexed by the ordered `p = 2` Brauer/projective labels and columns indexed by
the ordered ordinary irreducible labels. -/
def alternating_group_five_decomposition_matrix_mod_two :
    Matrix BrauerProjectiveModTwo OrdinaryIrreducible ℤ
  | .trivial, .chi1 => 1
  | .trivial, .chi3_phi_psi => 1
  | .trivial, .chi3_psi_phi => 1
  | .trivial, .chi4 => 0
  | .trivial, .chi5 => 1
  | .degreeTwo_from_chi3_phi_psi, .chi1 => 0
  | .degreeTwo_from_chi3_phi_psi, .chi3_phi_psi => 1
  | .degreeTwo_from_chi3_phi_psi, .chi3_psi_phi => 0
  | .degreeTwo_from_chi3_phi_psi, .chi4 => 0
  | .degreeTwo_from_chi3_phi_psi, .chi5 => 1
  | .degreeTwo_from_chi3_psi_phi, .chi1 => 0
  | .degreeTwo_from_chi3_psi_phi, .chi3_phi_psi => 0
  | .degreeTwo_from_chi3_psi_phi, .chi3_psi_phi => 1
  | .degreeTwo_from_chi3_psi_phi, .chi4 => 0
  | .degreeTwo_from_chi3_psi_phi, .chi5 => 1
  | .degreeFour, .chi1 => 0
  | .degreeFour, .chi3_phi_psi => 0
  | .degreeFour, .chi3_psi_phi => 0
  | .degreeFour, .chi4 => 1
  | .degreeFour, .chi5 => 0

/-- The `p = 2` Cartan matrix in Serre's modular-character example for `A₅`. Its rows are indexed
by the chosen `p = 2` Brauer-character labels, and its columns by the corresponding projective
indecomposable labels in the same order. -/
def alternating_group_five_cartan_matrix_mod_two :
    Matrix BrauerProjectiveModTwo BrauerProjectiveModTwo ℤ :=
  alternating_group_five_decomposition_matrix_mod_two *
    alternating_group_five_decomposition_matrix_mod_twoᵀ

/-- The `p = 2` Cartan matrix for `A₅` is the Gram matrix of the recorded decomposition matrix in
the chosen Brauer/projective basis order. -/
theorem alternating_group_five_cartan_matrix_mod_two_eq :
    alternating_group_five_cartan_matrix_mod_two =
      fun i j ↦
        match i, j with
        | .trivial, .trivial => 4
        | .trivial, .degreeTwo_from_chi3_phi_psi => 2
        | .trivial, .degreeTwo_from_chi3_psi_phi => 2
        | .trivial, .degreeFour => 0
        | .degreeTwo_from_chi3_phi_psi, .trivial => 2
        | .degreeTwo_from_chi3_phi_psi, .degreeTwo_from_chi3_phi_psi => 2
        | .degreeTwo_from_chi3_phi_psi, .degreeTwo_from_chi3_psi_phi => 1
        | .degreeTwo_from_chi3_phi_psi, .degreeFour => 0
        | .degreeTwo_from_chi3_psi_phi, .trivial => 2
        | .degreeTwo_from_chi3_psi_phi, .degreeTwo_from_chi3_phi_psi => 1
        | .degreeTwo_from_chi3_psi_phi, .degreeTwo_from_chi3_psi_phi => 2
        | .degreeTwo_from_chi3_psi_phi, .degreeFour => 0
        | .degreeFour, .trivial => 0
        | .degreeFour, .degreeTwo_from_chi3_phi_psi => 0
        | .degreeFour, .degreeTwo_from_chi3_psi_phi => 0
        | .degreeFour, .degreeFour => 1 := by
  decide

/-- The determinant of Serre's `p = 2` Cartan matrix for `A₅` is `4`. -/
theorem alternating_group_five_cartan_matrix_mod_two_det :
    det alternating_group_five_cartan_matrix_mod_two = 4 := by
  decide

/-- Remark 18-18.6-1: the `p = 3` decomposition matrix in Serre's modular-character example for
`A₅`, with rows indexed by the ordered `p = 3` Brauer/projective labels and columns indexed by
the ordered ordinary irreducible labels. -/
def alternating_group_five_decomposition_matrix_mod_three :
    Matrix BrauerProjectiveModThree OrdinaryIrreducible ℤ
  | .trivial, .chi1 => 1
  | .trivial, .chi3_phi_psi => 0
  | .trivial, .chi3_psi_phi => 0
  | .trivial, .chi4 => 0
  | .trivial, .chi5 => 1
  | .degreeThree_from_chi3_phi_psi, .chi1 => 0
  | .degreeThree_from_chi3_phi_psi, .chi3_phi_psi => 1
  | .degreeThree_from_chi3_phi_psi, .chi3_psi_phi => 0
  | .degreeThree_from_chi3_phi_psi, .chi4 => 0
  | .degreeThree_from_chi3_phi_psi, .chi5 => 0
  | .degreeThree_from_chi3_psi_phi, .chi1 => 0
  | .degreeThree_from_chi3_psi_phi, .chi3_phi_psi => 0
  | .degreeThree_from_chi3_psi_phi, .chi3_psi_phi => 1
  | .degreeThree_from_chi3_psi_phi, .chi4 => 0
  | .degreeThree_from_chi3_psi_phi, .chi5 => 0
  | .degreeFour, .chi1 => 0
  | .degreeFour, .chi3_phi_psi => 0
  | .degreeFour, .chi3_psi_phi => 0
  | .degreeFour, .chi4 => 1
  | .degreeFour, .chi5 => 1

/-- The `p = 3` Cartan matrix in Serre's modular-character example for `A₅`. Its rows are indexed
by the chosen `p = 3` Brauer-character labels, and its columns by the corresponding projective
indecomposable labels in the same order. -/
def alternating_group_five_cartan_matrix_mod_three :
    Matrix BrauerProjectiveModThree BrauerProjectiveModThree ℤ :=
  alternating_group_five_decomposition_matrix_mod_three *
    alternating_group_five_decomposition_matrix_mod_threeᵀ

/-- The `p = 3` Cartan matrix for `A₅` is the Gram matrix of the recorded decomposition matrix in
the chosen Brauer/projective basis order. -/
theorem alternating_group_five_cartan_matrix_mod_three_eq :
    alternating_group_five_cartan_matrix_mod_three =
      fun i j ↦
        match i, j with
        | .trivial, .trivial => 2
        | .trivial, .degreeThree_from_chi3_phi_psi => 0
        | .trivial, .degreeThree_from_chi3_psi_phi => 0
        | .trivial, .degreeFour => 1
        | .degreeThree_from_chi3_phi_psi, .trivial => 0
        | .degreeThree_from_chi3_phi_psi, .degreeThree_from_chi3_phi_psi => 1
        | .degreeThree_from_chi3_phi_psi, .degreeThree_from_chi3_psi_phi => 0
        | .degreeThree_from_chi3_phi_psi, .degreeFour => 0
        | .degreeThree_from_chi3_psi_phi, .trivial => 0
        | .degreeThree_from_chi3_psi_phi, .degreeThree_from_chi3_phi_psi => 0
        | .degreeThree_from_chi3_psi_phi, .degreeThree_from_chi3_psi_phi => 1
        | .degreeThree_from_chi3_psi_phi, .degreeFour => 0
        | .degreeFour, .trivial => 1
        | .degreeFour, .degreeThree_from_chi3_phi_psi => 0
        | .degreeFour, .degreeThree_from_chi3_psi_phi => 0
        | .degreeFour, .degreeFour => 2 := by
  decide

/-- The determinant of Serre's `p = 3` Cartan matrix for `A₅` is `3`. -/
theorem alternating_group_five_cartan_matrix_mod_three_det :
    det alternating_group_five_cartan_matrix_mod_three = 3 := by
  decide

/-- Remark 18-18.6-1: the `p = 5` decomposition matrix in Serre's modular-character example for
`A₅`, with rows indexed by the ordered `p = 5` Brauer/projective labels and columns indexed by
the ordered ordinary irreducible labels. -/
def alternating_group_five_decomposition_matrix_mod_five :
    Matrix BrauerProjectiveModFive OrdinaryIrreducible ℤ
  | .trivial, .chi1 => 1
  | .trivial, .chi3_phi_psi => 0
  | .trivial, .chi3_psi_phi => 0
  | .trivial, .chi4 => 1
  | .trivial, .chi5 => 0
  | .degreeThree, .chi1 => 0
  | .degreeThree, .chi3_phi_psi => 1
  | .degreeThree, .chi3_psi_phi => 1
  | .degreeThree, .chi4 => 1
  | .degreeThree, .chi5 => 0
  | .degreeFive, .chi1 => 0
  | .degreeFive, .chi3_phi_psi => 0
  | .degreeFive, .chi3_psi_phi => 0
  | .degreeFive, .chi4 => 0
  | .degreeFive, .chi5 => 1

/-- The `p = 5` Cartan matrix in Serre's modular-character example for `A₅`. Its rows are indexed
by the chosen `p = 5` Brauer-character labels, and its columns by the corresponding projective
indecomposable labels in the same order. -/
def alternating_group_five_cartan_matrix_mod_five :
    Matrix BrauerProjectiveModFive BrauerProjectiveModFive ℤ :=
  alternating_group_five_decomposition_matrix_mod_five *
    alternating_group_five_decomposition_matrix_mod_fiveᵀ

/-- The `p = 5` Cartan matrix for `A₅` is the Gram matrix of the recorded decomposition matrix in
the chosen Brauer/projective basis order. -/
theorem alternating_group_five_cartan_matrix_mod_five_eq :
    alternating_group_five_cartan_matrix_mod_five =
      fun i j ↦
        match i, j with
        | .trivial, .trivial => 2
        | .trivial, .degreeThree => 1
        | .trivial, .degreeFive => 0
        | .degreeThree, .trivial => 1
        | .degreeThree, .degreeThree => 3
        | .degreeThree, .degreeFive => 0
        | .degreeFive, .trivial => 0
        | .degreeFive, .degreeThree => 0
        | .degreeFive, .degreeFive => 1 := by
  decide

/-- The determinant of Serre's `p = 5` Cartan matrix for `A₅` is `5`. -/
theorem alternating_group_five_cartan_matrix_mod_five_det :
    det alternating_group_five_cartan_matrix_mod_five = 5 := by
  decide

/- Remark 18-18.6-1 records Serre's `A₅` example: the labeled ordinary irreducible character
table and, for `p = 2`, `3`, and `5`, the labeled decomposition matrices together with the
corresponding Cartan matrices, defined canonically as `D * Dᵀ` in the chapter's
Brauer/projective basis conventions. -/
