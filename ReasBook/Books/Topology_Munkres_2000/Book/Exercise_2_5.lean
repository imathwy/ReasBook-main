module

public import Topology_Munkres_2000.Book.Lemma_2_1

public section

-- Exercise 2.5 (1): The identity function, left inverses, and right inverses are
-- represented by the canonical function API; the final two checks recover the
-- textbook composition equations.
#check id
#check Function.LeftInverse
#check Function.RightInverse
#check Function.leftInverse_iff_comp
#check Function.rightInverse_iff_comp

-- Exercise 2.5 (2): A function with a left inverse is injective.
#check Function.LeftInverse.injective

-- Exercise 2.5 (3): A function with a right inverse is surjective.
#check Function.RightInverse.surjective

/-- Exercise 2.5 (1): The successor function on `Nat` has the explicit left inverse
`Nat.pred`. -/
theorem succ_leftInverse : Function.LeftInverse Nat.pred Nat.succ := sorry

/-- Exercise 2.5 (2): The successor function on `Nat` has no right inverse. -/
theorem succ_noRightInverse : ¬ Function.HasRightInverse Nat.succ := sorry

/-- Exercise 2.5 (3): Selecting `false` gives a right inverse of the constant
function from `Bool` to `Unit`. -/
theorem boolToUnit_rightInverseFalse :
    Function.RightInverse (fun _ : Unit ↦ false) (fun _ : Bool ↦ ()) := sorry

/-- Exercise 2.5 (4): The constant function from `Bool` to `Unit` has no left
inverse. -/
theorem boolToUnit_noLeftInverse :
    ¬ Function.HasLeftInverse (fun _ : Bool ↦ ()) := sorry

/-- Exercise 2.5 (5): The function sending `none` to `false` and `some b` to `b`
is a left inverse of `Option.some : Bool → Option Bool`. -/
theorem some_leftInverseFalse :
    Function.LeftInverse
      (fun x : Option Bool ↦ match x with | none => false | some b => b) Option.some := sorry

/-- Exercise 2.5 (6): The function sending `none` to `true` and `some b` to `b`
is a left inverse of `Option.some : Bool → Option Bool`. -/
theorem some_leftInverseTrue :
    Function.LeftInverse
      (fun x : Option Bool ↦ match x with | none => true | some b => b) Option.some := sorry

/-- Exercise 2.5 (7): The two displayed left inverses of
`Option.some : Bool → Option Bool` are distinct. -/
theorem some_leftInverses_ne :
    (fun x : Option Bool ↦ match x with | none => false | some b => b) ≠
      (fun x : Option Bool ↦ match x with | none => true | some b => b) := sorry

/-- Exercise 2.5 (8): Selecting `true` gives another right inverse of the constant
function from `Bool` to `Unit`. -/
theorem boolToUnit_rightInverseTrue :
    Function.RightInverse (fun _ : Unit ↦ true) (fun _ : Bool ↦ ()) := sorry

/-- Exercise 2.5 (9): The two displayed right inverses of the constant function from
`Bool` to `Unit` are distinct. -/
theorem boolToUnit_rightInverses_ne :
    (fun _ : Unit ↦ false) ≠ (fun _ : Unit ↦ true) := sorry

-- Exercise 2.5 (13): A function with both a left inverse and a right inverse is
-- bijective.
#check Function.Bijective.of_leftInverse_of_rightInverse

-- Exercise 2.5 (14): A left inverse and a right inverse of the same function
-- coincide, giving the common inverse denoted informally by `f⁻¹`.
#check Function.LeftInverse.eq_rightInverse
