import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

attribute [local instance] Classical.propDecidable

/- Theorem 6.18 is `source-facing` in the Chapter 6 proximal-operator API. Domain sampling against
the owner `prox[...]` from Definition 6.1, the scalar properness owner
`IsProperExtendedRealFunction` from Definition 2.5, and the chapter's norm-radial examples shows
that the public statement should stay on the canonical proximal owner, with the scalar-to-radial
passage recorded only as a `bridge/view`.

The primitive data are the scalar profile `g`, its canonical properness owner `hproper`, the
negative-ray bridge `hdom`, and the base point `x`. The nonnegative `≠ ⊥` branch and the finite
witness on `[0, ∞)` are derived from `hproper` together with `hdom`, so they should not remain as
parallel primitive hypotheses. -/

-- Proof sketch: for fixed `x`, write the proximal objective for `u ↦ g ‖u‖` in polar form using
-- `r = ‖u‖`. Expanding `‖u - x‖²` shows that, for each fixed radius `r`, minimizing over the
-- sphere `‖u‖ = r` is equivalent to maximizing `⟪u, x⟫`; by Cauchy-Schwarz, this forces the
-- unique optimizer `u = (r / ‖x‖) • x` when `x ≠ 0`, while for `x = 0` every vector of radius
-- `r` is optimal. The scalar objective is exactly the proximal objective of `g` at `‖x‖`. The
-- properness rules out the degenerate `⊥` and everywhere-`⊤` branches, while `hdom` forces the
-- effective-domain witness to lie on `[0, ∞)` and excludes negative radii from the minimizing
-- scalar profile.
/-- Theorem 6.18: norm composition. For the radial function `f = g ∘ norm`, the proximal set at
`x` is the radial image of the scalar proximal set at `‖x‖` when `x ≠ 0`, and at the origin it is
the set of vectors whose norm belongs to the scalar proximal set at `0`, provided `g` is proper,
closed, convex, and has effective domain contained in `[0, ∞)`.

The nontriviality hypothesis records the Euclidean-space assumption used in the textbook proof:
at `x = 0`, every nonnegative optimal scalar radius must be realized as the norm of some vector.
Without this, the statement is false in the zero-dimensional space. -/
theorem prox_norm_composition_eq_piecewise
    [Nontrivial E]
    (g : ℝ → EReal) (hproper : IsProperExtendedRealFunction g)
    (hclosed : LowerSemicontinuous g) (hconvex : is_convex_function g)
    (hdom : ∀ t : ℝ, t < 0 → g t = ⊤) (x : E) :
    prox[g ∘ norm] x =
      if x = 0 then
        {u : E | ‖u‖ ∈ prox[g] 0}
      else
        (fun t : ℝ ↦ (t / ‖x‖) • x) '' prox[g] ‖x‖ := sorry

-- Proof sketch: specialize `prox_norm_composition_eq_piecewise` to the origin, where the `if`
-- branch reduces definitionally to the radius-membership description.
/-- At the origin, the proximal set of the radial function `g ∘ norm` consists exactly of the
vectors whose norm belongs to the scalar proximal set of `g` at `0`. -/
@[simp] theorem prox_norm_composition_at_zero
    [Nontrivial E]
    (g : ℝ → EReal) (hproper : IsProperExtendedRealFunction g)
    (hclosed : LowerSemicontinuous g) (hconvex : is_convex_function g)
    (hdom : ∀ t : ℝ, t < 0 → g t = ⊤) :
    prox[g ∘ norm] (0 : E) = {u : E | ‖u‖ ∈ prox[g] 0} := by
  simpa using prox_norm_composition_eq_piecewise g hproper hclosed hconvex hdom (0 : E)

-- Proof sketch: specialize `prox_norm_composition_eq_piecewise` away from the origin, where the
-- nonzero hypothesis selects the radial-image branch of the piecewise formula.
/-- Away from the origin, the proximal set of `g ∘ norm` is the radial image of the scalar
proximal set of `g` at `‖x‖`. -/
theorem prox_norm_composition_of_ne_zero
    [Nontrivial E]
    (g : ℝ → EReal) (hproper : IsProperExtendedRealFunction g)
    (hclosed : LowerSemicontinuous g) (hconvex : is_convex_function g)
    (hdom : ∀ t : ℝ, t < 0 → g t = ⊤) {x : E} (hx : x ≠ 0) :
    prox[g ∘ norm] x = (fun t : ℝ ↦ (t / ‖x‖) • x) '' prox[g] ‖x‖ := by
  simpa [hx] using prox_norm_composition_eq_piecewise g hproper hclosed hconvex hdom x

end
