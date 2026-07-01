import Mathlib
import FirstOrderMethodsinOptimization.Chap11.Definition_11_4

-- Declarations for this item will be appended below by the statement pipeline.

/- Algorithm 11.3 is `source-facing`, but its one-block update is already owned by the Chapter 11
block replacement map `block_coordinate_update`; the prox point `T[Li i; hproblem] x i` is only
the source-facing displacement choice for that owner.

Domain sampling in this block-coordinate proximal-gradient layer is:
- `source-facing`: the textbook update replacing block `i` by `T_{L_i}^i(x)`;
- `core/canonical`: `block_coordinate_update`;
- `bridge/view`: the Chapter 11 prox-point notation `T[Li i; hproblem]`.

The primitive data are just the ambient point, the selected block, and the inserted displacement.
Coordinate formulas away from the updated block and the identity
`block_coordinate_update x i d = x + 𝒰[i] d` are already derived API of the owner and should not
survive as parallel algorithm-local wrappers. -/

noncomputable section

universe u v

open scoped Gradient

section

variable {ι : Type u} {Ei : ι → Type v}
variable [Fintype ι]
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, ProperSpace (Ei i)]

variable {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
variable {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
variable {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
variable {Lf : NNReal} {Li : (i : ι) → PosReal}

-- Semantic recall note: the semantic search tool `lean_leansearch` was unavailable in this
-- environment, so the owner check was verified locally against `Definition_11_4` and nearby
-- Chapter 11 algorithm files using `block_coordinate_update`, `𝒰[i]`, and `T[...]`.

section

variable (hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)

/- Algorithm 11.3 (1) and (3) are direct recall of the Chapter 11 block-update owner:
away from the selected block the update is unchanged by `block_coordinate_update_apply_ne`, and
the update itself is definitionally `x + 𝒰[i](T[Li i; hproblem] x i - x i)` by
`block_coordinate_update`. -/
recall block_coordinate_update
recall block_coordinate_update_apply_ne

/-- Algorithm 11.3 (2): at the selected block `i`, the one-block proximal-gradient update replaces
`x_i` by `T_{L_i}^i(x)`. -/
theorem block_proximal_gradient_update_apply_eq
    (x : (j : ι) → Ei j) (i : ι) :
    block_coordinate_update x i (hproblem.prox_point (Li i) i x - x i) i =
      hproblem.prox_point (Li i) i x := by
  simpa [sub_eq_add_neg] using
    (block_coordinate_update_apply_same
      x
      i
      (hproblem.prox_point (Li i) i x - x i))

end

end
