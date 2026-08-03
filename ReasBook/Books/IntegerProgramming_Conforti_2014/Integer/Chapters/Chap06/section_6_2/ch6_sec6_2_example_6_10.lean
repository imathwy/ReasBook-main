import Integer.Chapters.Chap05.section_5_1_4.ch5_sec5_1_4_definition_5_1_4_extra_1
import Integer.Chapters.Chap06.section_6_2.ch6_sec6_2_theorem_6_5

open scoped BigOperators

open IntersectionCut

-- This source-facing file keeps the tableau-row data from Example 6.10 explicit, while reusing
-- the Section 6.2 intersection-cut owner and the Chapter 5 mixed-integer-cut owner.

noncomputable section

section Example610

variable {n p : ℕ}

/-- The fractional part `f = b - floor b` of the tableau right-hand side. -/
def gomory_row_fraction
    (b : ℝ) : ℝ :=
  Int.fract b

/-- `gomory_row_fraction b` is the fractional part of `b`. -/
theorem gomory_row_fraction_def
    (b : ℝ) :
    gomory_row_fraction b = Int.fract b :=
  rfl

/-- The integral split normal `π` from (6.13), attached to one tableau row
`x_i = b - ∑ j, a j * x j`. The coefficient vector `a` is understood to be extended by zero
outside the nonbasic index set. -/
def gomory_tableau_split_normal
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ) : Fin n → ℤ :=
  fun j ↦
    if j = Fin.castLE hpn i then
      1
    else if j.1 < p then
      if Int.fract (a j) ≤ gomory_row_fraction b then
        Int.floor (a j)
      else
        Int.ceil (a j)
    else
      0

/-- The split normal from Example 6.10 is given by the displayed case distinction (6.13). -/
theorem gomory_tableau_split_normal_apply
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ)
    (j : Fin n) :
    gomory_tableau_split_normal hpn a i b j =
      if j = Fin.castLE hpn i then
        1
      else if j.1 < p then
        if Int.fract (a j) ≤ gomory_row_fraction b then
          Int.floor (a j)
        else
          Int.ceil (a j)
      else
        0 :=
  rfl

/-- The split set `C = {x : R^n | pi0 <= pi x <= pi0 + 1}` determined by the tableau row
of Example 6.10. -/
def gomory_tableau_split_set
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ) : Set (Fin n → ℝ) :=
  {x |
    (Int.floor b : ℝ) ≤
        ∑ h : Fin n, (gomory_tableau_split_normal hpn a i b h : ℝ) * x h ∧
      (∑ h : Fin n, (gomory_tableau_split_normal hpn a i b h : ℝ) * x h) ≤
        (Int.floor b : ℝ) + 1}

/-- Membership in `gomory_tableau_split_set hpn a i b` is exactly the displayed split
inequality `pi0 <= pi x <= pi0 + 1`. -/
theorem mem_gomory_tableau_split_set_iff
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ)
    (x : Fin n → ℝ) :
    x ∈ gomory_tableau_split_set hpn a i b ↔
      (Int.floor b : ℝ) ≤
          ∑ h : Fin n, (gomory_tableau_split_normal hpn a i b h : ℝ) * x h ∧
        (∑ h : Fin n, (gomory_tableau_split_normal hpn a i b h : ℝ) * x h) ≤
          (Int.floor b : ℝ) + 1 :=
  Iff.rfl

/-- The basic feasible point attached to the tableau row `x_i = b - ∑ j, a_j x_j`, with
basic coordinate `x_i = b` and all other coordinates equal to `0`. -/
def gomory_tableau_row_vertex
    (hpn : p ≤ n)
    (i : Fin p)
    (b : ℝ) : Fin n → ℝ :=
  fun h ↦
    if h = Fin.castLE hpn i then
      b
    else
      0

/-- The tableau-row vertex from Example 6.10 has `b` in the basic coordinate `i` and `0`
elsewhere. -/
theorem gomory_tableau_row_vertex_apply
    (hpn : p ≤ n)
    (i : Fin p)
    (b : ℝ)
    (h : Fin n) :
    gomory_tableau_row_vertex hpn i b h =
      if h = Fin.castLE hpn i then
        b
      else
        0 :=
  rfl

/-- The tableau ray `r^j` used in Example 6.10: the `j`th nonbasic variable increases by one,
and the basic variable `x_i` changes by `-a_j`. -/
def gomory_tableau_row_ray
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (j : Fin n) : Fin n → ℝ :=
  fun h ↦
    if h = j then
      1
    else if h = Fin.castLE hpn i then
      -a j
    else
      0

/-- The tableau ray from Example 6.10 has unit `j`th coordinate, `-a_j` in the basic
coordinate `i`, and zero elsewhere. -/
theorem gomory_tableau_row_ray_apply
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (j h : Fin n) :
    gomory_tableau_row_ray hpn a i j h =
      if h = j then
        1
      else if h = Fin.castLE hpn i then
        -a j
      else
        0 :=
  rfl

/-- The value `pi r^j` of the split normal on the tableau ray indexed by `j`. -/
def gomory_tableau_split_direction_value
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ)
    (j : Fin n) : ℝ :=
  ∑ h : Fin n, (gomory_tableau_split_normal hpn a i b h : ℝ) * gomory_tableau_row_ray hpn a i j h

/-- The ray-intersection parameter `alpha_j` computed in Example 6.10 from the split set of the
tableau row. -/
def gomory_tableau_split_ray_parameter
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ)
    (j : Fin n) : ENNReal :=
  ray_intersection_parameter
    (gomory_tableau_split_set hpn a i b)
    (gomory_tableau_row_vertex hpn i b)
    (gomory_tableau_row_ray hpn a i)
    j

/-- The split-intersection-cut coefficient `1 / alpha_j` obtained from Example 6.10. -/
def gomory_tableau_split_intersection_coefficient
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ)
    (j : Fin n) : ℝ :=
  intersection_cut_coeff
    (gomory_tableau_split_set hpn a i b)
    (gomory_tableau_row_vertex hpn i b)
    (gomory_tableau_row_ray hpn a i)
    j

/-- The split-intersection cut attached to the split set from Example 6.10. -/
def gomory_tableau_split_intersection_cut
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ) : Set (Fin n → ℝ) :=
  {x | 1 ≤ ∑ j : Fin n, gomory_tableau_split_intersection_coefficient hpn a i b j * x j}

/-- Membership in `gomory_tableau_split_intersection_cut hpn a i b` is exactly the normalized
intersection-cut inequality generated from the split set of Example 6.10. -/
theorem mem_gomory_tableau_split_intersection_cut_iff
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ)
    (x : Fin n → ℝ) :
    x ∈ gomory_tableau_split_intersection_cut hpn a i b ↔
      1 ≤ ∑ j : Fin n, gomory_tableau_split_intersection_coefficient hpn a i b j * x j :=
  Iff.rfl

/-- The direct Gomory mixed-integer coefficient from the tableau row formula (6.15), again with
`a` extended by zero outside the nonbasic index set. -/
def gomory_mixed_integer_cut_coefficient
    (p : ℕ)
    (a : Fin n → ℝ)
    (b : ℝ)
    (hfrac : 0 < gomory_row_fraction b)
    (j : Fin n) : ℝ :=
  gomory_mixed_integer_inequality_coefficient
    (Finset.univ.filter fun h : Fin n ↦ h.1 < p)
    a
    b
    hfrac
    j

/-- The Gomory mixed-integer cut generated by the tableau row. -/
def gomory_mixed_integer_cut
    (p : ℕ)
    (a : Fin n → ℝ)
    (b : ℝ)
    (hfrac : 0 < gomory_row_fraction b) : Set (Fin n → ℝ) :=
  gomory_mixed_integer_inequality
    (Finset.univ.filter fun j : Fin n ↦ j.1 < p)
    a
    b
    hfrac

/-- Membership in `gomory_mixed_integer_cut p a b` is exactly the normalized Gomory mixed
integer inequality of (6.15). -/
theorem mem_gomory_mixed_integer_cut_iff
    (p : ℕ)
    (a : Fin n → ℝ)
    (b : ℝ)
    (hfrac : 0 < gomory_row_fraction b)
    (x : Fin n → ℝ) :
    x ∈ gomory_mixed_integer_cut p a b hfrac ↔
      1 ≤ ∑ j : Fin n, gomory_mixed_integer_cut_coefficient p a b hfrac j * x j := by
  rw [gomory_mixed_integer_cut, mem_gomory_mixed_integer_inequality_iff]
  rfl

/-- The integer-variable coefficient function `pi` from (6.16). -/
def gomory_integer_function
    (f : ℝ)
    (r : ℝ) : ℝ :=
  min
    ((r - (Int.floor r : ℝ)) / (1 - f))
    ((((Int.floor r : ℝ) + 1) - r) / f)

/-- `gomory_integer_function f r` is the minimum of the two affine expressions from (6.16). -/
theorem gomory_integer_function_def
    (f : ℝ)
    (r : ℝ) :
    gomory_integer_function f r =
      min
        ((r - (Int.floor r : ℝ)) / (1 - f))
        ((((Int.floor r : ℝ) + 1) - r) / f) :=
  rfl

/-- The continuous-variable coefficient function `psi` from (6.16). -/
def gomory_continuous_function
    (f : ℝ)
    (r : ℝ) : ℝ :=
  max (r / (1 - f)) ((-r) / f)

/-- `gomory_continuous_function f r` is the maximum of the two affine expressions from (6.16). -/
theorem gomory_continuous_function_def
    (f : ℝ)
    (r : ℝ) :
    gomory_continuous_function f r = max (r / (1 - f)) ((-r) / f) :=
  rfl

/-- Example 6.10 (1). For a tableau row
`x_i = b - ∑ j, a j * x j` with `a` extended by zero outside the nonbasic indices, the split
normal (6.13) evaluates on the tableau ray `r^j` by the displayed formula (6.14). -/
theorem example_6_10_split_direction_value_eq_piecewise
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ)
    (j : Fin n)
    (hj : j ≠ Fin.castLE hpn i) :
    gomory_tableau_split_direction_value hpn a i b j =
      if j.1 < p then
        if Int.fract (a j) ≤ gomory_row_fraction b then
          -Int.fract (a j)
        else
          1 - Int.fract (a j)
      else
        -a j := sorry

/-- Example 6.10 (2). If the tableau right-hand side `b` is fractional, then the coefficient
`1 / alpha_j` of the split-intersection cut derived from the split set equals the corresponding
coefficient of Gomory's mixed integer cut. -/
theorem example_6_10_split_intersection_coefficient_eq_gomory_coefficient
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ)
    (hfrac : 0 < gomory_row_fraction b ∧ gomory_row_fraction b < 1)
    (j : Fin n) :
    gomory_tableau_split_intersection_coefficient hpn a i b j =
      gomory_mixed_integer_cut_coefficient p a b hfrac.1 j := sorry

/-- Example 6.10 (3). The intersection cut derived from the split set defined by (6.13) is
exactly the Gomory mixed integer cut generated by the same tableau row. -/
theorem example_6_10_split_intersection_cut_eq_gomory_mixed_integer_cut
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ)
    (hfrac : 0 < gomory_row_fraction b ∧ gomory_row_fraction b < 1) :
    gomory_tableau_split_intersection_cut hpn a i b =
      gomory_mixed_integer_cut p a b hfrac.1 := sorry

/-- Example 6.10 (4). The Gomory mixed integer cut coefficients may equivalently be written with
the two functions `pi` and `psi` from (6.16), applied to `-a_j` on the integer and continuous
blocks respectively. -/
theorem example_6_10_gomory_coefficient_eq_function_form
    (a : Fin n → ℝ)
    (b : ℝ)
    (hfrac : 0 < gomory_row_fraction b ∧ gomory_row_fraction b < 1)
    (j : Fin n) :
    gomory_mixed_integer_cut_coefficient p a b hfrac.1 j =
      if j.1 < p then
        gomory_integer_function (gomory_row_fraction b) (-a j)
      else
        gomory_continuous_function (gomory_row_fraction b) (-a j) := sorry

end Example610
