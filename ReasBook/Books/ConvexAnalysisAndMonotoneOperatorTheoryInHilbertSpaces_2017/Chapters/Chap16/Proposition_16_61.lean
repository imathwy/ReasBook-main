import Mathlib
import BauschkeLean.Chap12.Definition_12_1
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap16.Proposition_16_59

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section SubdifferentialCalculus

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

variable (f g : H → Set.Ioi (⊥ : EReal)) (x y : H)

local notation:70 f " □ₑ " g =>
  ERealFunction.infimalConvolution (fun z ↦ (f z : EReal)) (fun z ↦ (g z : EReal))

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 16.61: if `x ∈ dom (f □ g)` and the infimal convolution value at `x`
is realized by `y`, then both summands `f y` and `g (x - y)` are finite. -/
private lemma summands_lt_top_of_infimalConvolution_value_eq
    (hx : x ∈ dom (f □ g))
    (hEq : (f □ g) x = (f y : EReal) + (g (x - y) : EReal)) :
    (f y : EReal) < ⊤ ∧ (g (x - y) : EReal) < ⊤ := by
  -- The exact value is finite because `x` lies in the domain of `f □ g`.
  have hsum_top : ((f y : EReal) + (g (x - y) : EReal)) ≠ ⊤ := by
    rw [← hEq]
    exact ne_of_lt ((mem_dom_iff (f □ g) x).mp hx)
  have hfy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
  have hgy_bot : (g (x - y) : EReal) ≠ ⊥ := ne_of_gt (g (x - y)).2
  -- Split finiteness of the sum into finiteness of each summand.
  have hparts := (EReal.add_ne_top_iff_ne_top₂ hfy_bot hgy_bot).1 hsum_top
  exact ⟨lt_of_le_of_ne le_top hparts.1, lt_of_le_of_ne le_top hparts.2⟩

omit [CompleteSpace H] in
/-- Helper for Proposition 16.61: a common subgradient at `y` and `x - y` forces the split
`x = y + (x - y)` to attain the infimal convolution. -/
private lemma infimalConvolution_eq_add_of_mem_subdifferential_inter
    {u : H}
    (hu : u ∈ (∂ f) y ∩ (∂ g) (x - y)) :
    (f □ g) x = (f y : EReal) + (g (x - y) : EReal) := by
  rcases hu with ⟨hu_f, hu_g⟩
  rw [mem_subdifferential_iff] at hu_f hu_g
  apply le_antisymm
  · -- The candidate decomposition `x = y + (x - y)` gives the standard upper bound.
    rw [infimalConvolution_apply]
    exact iInf_le (fun z : H ↦ (f z : EReal) + (g (x - z) : EReal)) y
  · -- Every other decomposition has value at least the active one by adding the two
    -- subgradient inequalities.
    rw [infimalConvolution_apply]
    refine le_iInf ?_
    intro a
    have hfa : (⟪a - y, u⟫_ℝ : EReal) + (f y : EReal) ≤ (f a : EReal) := hu_f a
    have hga :
        (⟪(x - a) - (x - y), u⟫_ℝ : EReal) + (g (x - y) : EReal) ≤ (g (x - a) : EReal) :=
      hu_g (x - a)
    have hsum := add_le_add hfa hga
    have hsum' :
        (f y : EReal) + ((g (x - y) : EReal) +
            ((⟪y - a, u⟫_ℝ : EReal) + (⟪a - y, u⟫_ℝ : EReal))) ≤
          (f a : EReal) + (g (x - a) : EReal) := by
      simpa [add_assoc, add_left_comm, add_comm] using hsum
    have hinner_real :
        ⟪y - a, u⟫_ℝ + ⟪a - y, u⟫_ℝ = 0 := by
      calc
        ⟪y - a, u⟫_ℝ + ⟪a - y, u⟫_ℝ
            = ⟪(y - a) + (a - y), u⟫_ℝ := by
                rw [← inner_add_left]
        _ = ⟪(0 : H), u⟫_ℝ := by
              congr 1
              abel
        _ = 0 := by simp
    have hinner :
        (⟪y - a, u⟫_ℝ : EReal) + (⟪a - y, u⟫_ℝ : EReal) = 0 := by
      exact_mod_cast hinner_real
    simpa [hinner, add_assoc] using hsum'

omit [CompleteSpace H] in
/-- Proposition 16.61 (1): if `f, g ∈ Γ₀(H)`, `x ∈ dom (f □ g)`, and
`(f □ g) x = f y + g (x - y)`, then
`∂ (f □ g) x = ∂ f y ∩ ∂ g (x - y)`. -/
theorem subdifferential_infimalConvolution_eq_inter_of_value_eq
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hx : x ∈ dom (f □ g))
    (hEq : (f □ g) x = (f y : EReal) + (g (x - y) : EReal)) :
    (∂ (f □ g)) x = (∂ f) y ∩ (∂ g) (x - y) := by
  let _ := hf
  let _ := hg
  have hfinite :=
    summands_lt_top_of_infimalConvolution_value_eq
      (f := f) (g := g) (x := x) (y := y) hx hEq
  have hfy_top : (f y : EReal) ≠ ⊤ := ne_of_lt hfinite.1
  have hgy_top : (g (x - y) : EReal) ≠ ⊤ := ne_of_lt hfinite.2
  have hfy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
  have hgy_bot : (g (x - y) : EReal) ≠ ⊥ := ne_of_gt (g (x - y)).2
  ext u
  rw [Set.mem_inter_iff]
  constructor
  · intro hu
    rw [mem_subdifferential_iff] at hu
    constructor
    · rw [mem_subdifferential_iff]
      intro a
      -- Freeze the `g`-summand and translate the global subgradient inequality to the first
      -- coordinate.
      have htranslate : a + (x - y) - x = a - y := by
        abel
      have hu_shift :
          (⟪a + (x - y) - x, u⟫_ℝ : EReal) + (f □ g) x ≤ (f □ g) (a + (x - y)) :=
        hu (a + (x - y))
      have hupper :
          (f □ g) (a + (x - y)) ≤ (f a : EReal) + (g (x - y) : EReal) := by
        have hfreeze : a + (x - y) - a = x - y := by
          abel
        rw [infimalConvolution_apply]
        simpa [hfreeze] using
          (iInf_le (fun z : H ↦ (f z : EReal) + (g (a + (x - y) - z) : EReal)) a)
      have hraw :
          (⟪a - y, u⟫_ℝ : EReal) + ((f y : EReal) + (g (x - y) : EReal)) ≤
            (f a : EReal) + (g (x - y) : EReal) := by
        have hle := le_trans hu_shift hupper
        simpa [hEq, htranslate, add_assoc, add_left_comm, add_comm] using hle
      rw [← EReal.coe_toReal hgy_top hgy_bot] at hraw
      have hshift :
          ((⟪a - y, u⟫_ℝ : EReal) + (f y : EReal)) +
              (((g (x - y) : EReal).toReal : ℝ) : EReal) ≤
            (f a : EReal) + (((g (x - y) : EReal).toReal : ℝ) : EReal) := by
        simpa [add_assoc] using hraw
      exact
        (EReal.addLECancellable_coe ((g (x - y) : EReal).toReal)).add_le_add_iff_right.mp hshift
    · rw [mem_subdifferential_iff]
      intro b
      -- Freeze the `f`-summand and translate the global subgradient inequality to the second
      -- coordinate.
      have htranslate : y + b - x = b - (x - y) := by
        abel
      have hu_shift :
          (⟪y + b - x, u⟫_ℝ : EReal) + (f □ g) x ≤ (f □ g) (y + b) :=
        hu (y + b)
      have hupper :
          (f □ g) (y + b) ≤ (f y : EReal) + (g b : EReal) := by
        have hfreeze : y + b - y = b := by
          abel
        rw [infimalConvolution_apply]
        simpa [hfreeze] using
          (iInf_le (fun z : H ↦ (f z : EReal) + (g (y + b - z) : EReal)) y)
      have hraw :
          (⟪b - (x - y), u⟫_ℝ : EReal) + ((f y : EReal) + (g (x - y) : EReal)) ≤
            (f y : EReal) + (g b : EReal) := by
        have hle := le_trans hu_shift hupper
        simpa [hEq, htranslate, add_assoc, add_left_comm, add_comm] using hle
      rw [← EReal.coe_toReal hfy_top hfy_bot] at hraw
      have hshift :
          ((⟪b - (x - y), u⟫_ℝ : EReal) + (g (x - y) : EReal)) +
              (((f y : EReal).toReal : ℝ) : EReal) ≤
            (g b : EReal) + (((f y : EReal).toReal : ℝ) : EReal) := by
        simpa [add_assoc, add_left_comm, add_comm] using hraw
      exact
        (EReal.addLECancellable_coe ((f y : EReal).toReal)).add_le_add_iff_right.mp hshift
  · intro hu
    rw [mem_subdifferential_iff]
    rw [mem_subdifferential_iff] at hu
    have hvalue :=
      infimalConvolution_eq_add_of_mem_subdifferential_inter
        (f := f) (g := g) (x := x) (y := y) hu
    intro z
    -- Add the component subgradient inequalities along an arbitrary decomposition `z = a + (z-a)`.
    rw [hvalue, infimalConvolution_apply]
    refine le_iInf ?_
    intro a
    have hfa : (⟪a - y, u⟫_ℝ : EReal) + (f y : EReal) ≤ (f a : EReal) := hu.1 a
    have hga :
        (⟪(z - a) - (x - y), u⟫_ℝ : EReal) + (g (x - y) : EReal) ≤ (g (z - a) : EReal) :=
      hu.2 (z - a)
    have hsum := add_le_add hfa hga
    have hinner_real :
        ⟪a - y, u⟫_ℝ + ⟪(z - a) - (x - y), u⟫_ℝ = ⟪z - x, u⟫_ℝ := by
      calc
        ⟪a - y, u⟫_ℝ + ⟪(z - a) - (x - y), u⟫_ℝ
            = ⟪(a - y) + ((z - a) - (x - y)), u⟫_ℝ := by
                rw [← inner_add_left]
        _ = ⟪z - x, u⟫_ℝ := by
              congr 1
              abel
    have hinner :
        (⟪a - y, u⟫_ℝ : EReal) + (⟪(z - a) - (x - y), u⟫_ℝ : EReal) =
          (⟪z - x, u⟫_ℝ : EReal) := by
      exact_mod_cast hinner_real
    have hsum' :
        (f y : EReal) + ((g (x - y) : EReal) + (⟪z - x, u⟫_ℝ : EReal)) ≤
          (f a : EReal) + (g (z - a) : EReal) := by
      simpa [hinner, add_assoc, add_left_comm, add_comm] using hsum
    have hbound :
        ((f y : EReal) + (g (x - y) : EReal)) + (⟪z - x, u⟫_ℝ : EReal) ≤
          (f a : EReal) + (g (z - a) : EReal) := by
      simpa [add_assoc] using hsum'
    calc
      (⟪z - x, u⟫_ℝ : EReal) + ((f y : EReal) + (g (x - y) : EReal))
          = ((f y : EReal) + (g (x - y) : EReal)) + (⟪z - x, u⟫_ℝ : EReal) := by
              simp [add_assoc, add_comm]
      _ ≤ (f a : EReal) + (g (z - a) : EReal) := hbound

omit [CompleteSpace H] in
/-- Companion exactness form of Proposition 16.61 (2): a common subgradient at `y` and `x - y`
forces the infimal convolution `f □ g` to be exact at `x`. -/
theorem infimalConvolution_exactAt_of_subdifferential_inter_nonempty
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hinter : ((∂ f) y ∩ (∂ g) (x - y)).Nonempty) :
    infimalConvolution.ExactAt f g x := by
  let _ := hf
  let _ := hg
  rcases hinter with ⟨u, hu⟩
  -- The witness `u` provides the exact minimizing split through the value identity above.
  have hvalue :=
    infimalConvolution_eq_add_of_mem_subdifferential_inter
      (f := f) (g := g) (x := x) (y := y) hu
  exact ⟨y, hvalue⟩

omit [CompleteSpace H] in
/-- Proposition 16.61 (2): if `x ∈ dom (f □ g)` and `∂ f(y) ∩ ∂ g(x - y)` is nonempty, then
`(f □ g) x = f y + g (x - y)`. -/
theorem infimalConvolution_eq_add_of_subdifferential_inter_nonempty
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hx : x ∈ dom (f □ g))
    (hinter : ((∂ f) y ∩ (∂ g) (x - y)).Nonempty) :
    (f □ g) x = (f y : EReal) + (g (x - y) : EReal) := by
  let _ := hf
  let _ := hg
  let _ := hx
  rcases hinter with ⟨u, hu⟩
  -- The nonempty intersection reduces the displayed equality to the witness-level helper.
  exact
    infimalConvolution_eq_add_of_mem_subdifferential_inter
      (f := f) (g := g) (x := x) (y := y) hu

end SubdifferentialCalculus

end

end ERealFunction
