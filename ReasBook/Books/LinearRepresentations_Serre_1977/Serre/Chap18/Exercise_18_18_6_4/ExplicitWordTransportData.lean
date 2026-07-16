import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_6_4.ExplicitGeneratorsAndRegularClasses

noncomputable section

open scoped MatrixGroups

local notation "A5" => alternatingGroup (Fin 5)

/-- Helper for Exercise 18-18.6-4: evaluate a word in Serre's chosen `A₅` generators, with
`false` standing for the order-`5` generator and `true` for the order-`2` generator. -/
def alternating_group_fin5_word_eval_a5 : List Bool → A5
  | [] => 1
  | false :: w => a5_generator_five * alternating_group_fin5_word_eval_a5 w
  | true :: w => a5_generator_two * alternating_group_fin5_word_eval_a5 w

/-- Helper for Exercise 18-18.6-4: the finite word list used to enumerate all `60` elements of
`A₅` from Serre's two explicit generators. -/
def alternating_group_fin5_word_table : List (List Bool) :=
  [[],
    [false],
    [true],
    [false, false],
    [false, true],
    [true, false],
    [false, false, false],
    [false, false, true],
    [false, true, false],
    [true, false, false],
    [true, false, true],
    [false, false, false, false],
    [false, false, false, true],
    [false, false, true, false],
    [false, true, false, false],
    [false, true, false, true],
    [true, false, false, false],
    [true, false, false, true],
    [true, false, true, false],
    [false, false, false, true, false],
    [false, false, true, false, false],
    [false, false, true, false, true],
    [false, true, false, false, false],
    [false, true, false, false, true],
    [true, false, false, false, true],
    [true, false, false, true, false],
    [true, false, true, false, false],
    [false, false, false, true, false, false],
    [false, false, false, true, false, true],
    [false, false, true, false, false, false],
    [false, false, true, false, false, true],
    [false, true, false, false, false, true],
    [true, false, false, false, true, false],
    [true, false, false, true, false, false],
    [true, false, false, true, false, true],
    [true, false, true, false, false, false],
    [true, false, true, false, false, true],
    [false, false, false, true, false, false, false],
    [false, false, false, true, false, false, true],
    [false, false, true, false, false, false, true],
    [false, true, false, false, false, true, false],
    [true, false, false, false, true, false, false],
    [true, false, false, false, true, false, true],
    [true, false, false, true, false, false, false],
    [true, false, false, true, false, false, true],
    [true, false, true, false, false, false, true],
    [false, false, false, true, false, false, false, true],
    [false, false, true, false, false, false, true, false],
    [false, true, false, false, false, true, false, false],
    [false, true, false, false, false, true, false, true],
    [true, false, false, false, true, false, false, true],
    [true, false, false, true, false, false, false, true],
    [false, false, false, true, false, false, false, true, false],
    [false, false, true, false, false, false, true, false, false],
    [false, false, true, false, false, false, true, false, true],
    [false, true, false, false, false, true, false, false, true],
    [true, false, false, true, false, false, false, true, false],
    [false, false, false, true, false, false, false, true, false, false],
    [false, false, false, true, false, false, false, true, false, true],
    [false, false, true, false, false, false, true, false, false, true]]

/-- Helper for Exercise 18-18.6-4: the explicit `SL₂(𝔽₅)` matrices attached to the word table
above, computed once and stored as literal transport data. -/
def alternating_group_fin5_sl_matrix_table : List (Matrix (Fin 2) (Fin 2) (ZMod 5)) :=
  [
    !![(1 : ZMod 5), 0; 0, 1],
    !![(1 : ZMod 5), 1; 0, 1],
    !![(0 : ZMod 5), 4; 1, 0],
    !![(1 : ZMod 5), 2; 0, 1],
    !![(1 : ZMod 5), 4; 1, 0],
    !![(0 : ZMod 5), 4; 1, 1],
    !![(1 : ZMod 5), 3; 0, 1],
    !![(2 : ZMod 5), 4; 1, 0],
    !![(1 : ZMod 5), 0; 1, 1],
    !![(0 : ZMod 5), 4; 1, 2],
    !![(4 : ZMod 5), 0; 1, 4],
    !![(1 : ZMod 5), 4; 0, 1],
    !![(3 : ZMod 5), 4; 1, 0],
    !![(2 : ZMod 5), 1; 1, 1],
    !![(1 : ZMod 5), 1; 1, 2],
    !![(0 : ZMod 5), 4; 1, 4],
    !![(0 : ZMod 5), 4; 1, 3],
    !![(4 : ZMod 5), 0; 2, 4],
    !![(4 : ZMod 5), 4; 1, 0],
    !![(3 : ZMod 5), 2; 1, 1],
    !![(2 : ZMod 5), 3; 1, 2],
    !![(1 : ZMod 5), 3; 1, 4],
    !![(1 : ZMod 5), 2; 1, 3],
    !![(1 : ZMod 5), 4; 2, 4],
    !![(4 : ZMod 5), 0; 3, 4],
    !![(4 : ZMod 5), 4; 2, 1],
    !![(4 : ZMod 5), 3; 1, 1],
    !![(3 : ZMod 5), 0; 1, 2],
    !![(2 : ZMod 5), 2; 1, 4],
    !![(2 : ZMod 5), 0; 1, 3],
    !![(3 : ZMod 5), 3; 2, 4],
    !![(2 : ZMod 5), 4; 3, 4],
    !![(4 : ZMod 5), 4; 3, 2],
    !![(4 : ZMod 5), 3; 2, 3],
    !![(4 : ZMod 5), 1; 1, 3],
    !![(4 : ZMod 5), 2; 1, 2],
    !![(3 : ZMod 5), 1; 1, 4],
    !![(3 : ZMod 5), 3; 1, 3],
    !![(0 : ZMod 5), 2; 2, 4],
    !![(0 : ZMod 5), 3; 3, 4],
    !![(2 : ZMod 5), 1; 3, 2],
    !![(4 : ZMod 5), 3; 3, 0],
    !![(4 : ZMod 5), 1; 2, 2],
    !![(4 : ZMod 5), 2; 2, 0],
    !![(3 : ZMod 5), 1; 3, 3],
    !![(2 : ZMod 5), 1; 2, 4],
    !![(3 : ZMod 5), 2; 3, 4],
    !![(0 : ZMod 5), 3; 3, 2],
    !![(2 : ZMod 5), 3; 3, 0],
    !![(1 : ZMod 5), 3; 2, 2],
    !![(3 : ZMod 5), 1; 0, 2],
    !![(2 : ZMod 5), 1; 0, 3],
    !![(3 : ZMod 5), 0; 3, 2],
    !![(0 : ZMod 5), 3; 3, 0],
    !![(3 : ZMod 5), 0; 2, 2],
    !![(3 : ZMod 5), 3; 0, 2],
    !![(2 : ZMod 5), 3; 0, 3],
    !![(3 : ZMod 5), 3; 3, 0],
    !![(0 : ZMod 5), 2; 2, 2],
    !![(3 : ZMod 5), 0; 0, 2]
  ]

/-- Helper for Exercise 18-18.6-4: pair each word-generated `A₅` element with its precomputed
`SL₂(𝔽₅)` lift. -/
def alternating_group_fin5_transport_table :
    List (A5 × Matrix (Fin 2) (Fin 2) (ZMod 5)) :=
  List.zip
    (alternating_group_fin5_word_table.map alternating_group_fin5_word_eval_a5)
    alternating_group_fin5_sl_matrix_table

/-- Helper for Exercise 18-18.6-4: recover the stored `SL₂(𝔽₅)` matrix assigned to an `A₅`
element by the finite transport table. -/
def alternating_group_fin5_to_sl_matrix_lookup (g : A5) :
    Matrix (Fin 2) (Fin 2) (ZMod 5) :=
  (alternating_group_fin5_transport_table.find? fun p ↦ p.1 = g).map Prod.snd |>.getD 1

/-- Helper for Exercise 18-18.6-4: every stored transport matrix has determinant `1`, so it
really lies in `SL₂(𝔽₅)`. -/
theorem alternating_group_fin5_to_sl_matrix_lookup_det (g : A5) :
    Matrix.det (alternating_group_fin5_to_sl_matrix_lookup g) = 1 := by
  revert g
  native_decide
