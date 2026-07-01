import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_2_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_22

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped BigOperators Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.23 computes the conjugate of the concrete function
  `x ↦ (1 / p) * ∑ i, ‖x i‖ ^ p` on a finite coordinate family `ι → X`; the textbook scalar
  coordinate model is recovered by `X = ℝ` and `ι = Fin n`.
- `core/canonical`: the owner abstraction is the project's Fenchel conjugate `convexConjugate` on
  `WithBotTop ℝ`-valued functions on finite coordinate families.
- `bridge/view`: the source-facing function owner is `lpCoordinatePower` from
  Text 15.0.22, while the conjugate-exponent relation is expressed by the canonical predicate
  `p.HolderConjugate q`; the codomain lift is the canonical bridge `Function.toWithBotTop`.

Domain-style sampling used here:
- the owner `convexConjugate` from Defn 12.2;
- direct unfolding of the owner `convexConjugate`;
- the source-facing function `lpCoordinatePower` from Text 15.0.22;
- the canonical real inner-product pairing owner from Chapter 1;
- mathlib's `Real.HolderConjugate` as the canonical exponent relation.

Primitive data vs derived API:
- primitive inputs: the exponents `p q : ℝ` with `p.HolderConjugate q`;
- primitive ambient data: a real inner-product coordinate value type `X` and a finite index type
  `ι`, since the source formula is coordinatewise and uses no order or arithmetic on indices;
- derived API: the conjugate identity between the canonical source-facing owners
  `lpCoordinatePower X ι p` and `lpCoordinatePower X ι q`, viewed
  as `WithBotTop ℝ`-valued by the canonical codomain lift.

Layer target: `source-facing`; the item is stated directly through the canonical conjugate owner
applied to the source-facing `ℓ_p` power-sum function, on the intrinsic inner-product coordinate
layer instead of only scalar coordinates. The scalar remains `ℝ` because the exponent owner is
`Real.rpow` and the dual-exponent owner is `Real.HolderConjugate`.
-/

variable {ι : Type*} [Fintype ι]
variable {X : Type*} [SeminormedAddCommGroup X] [InnerProductSpace ℝ X]

-- Proof sketch: unfold `convexConjugate`; by symmetry of the real inner product on `ι → X`,
-- separate the Fenchel supremum into independent coordinates. Apply the degree-`p`/degree-`q`
-- conjugacy formula for `x ↦ (1 / p) * ‖x‖ ^ p` on each coordinate space `X`, then reassemble the
-- resulting sum as `lpCoordinatePower X ι q`.
/-- Text 15.0.23: if `p` and `q` are Hölder-conjugate exponents, then the Fenchel conjugate of
`x ↦ (1 / p) * ∑ i, ‖x i‖ ^ p`, viewed as `WithBotTop ℝ`-valued by coercion, is the canonical
codomain lift of `xStar ↦ (1 / q) * ∑ i, ‖xStar i‖ ^ q`. -/
theorem lpCoordinatePower_convexConjugate_eq
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    ((lpCoordinatePower X ι p).toWithBotTop)⋆ =
      (lpCoordinatePower X ι q).toWithBotTop := sorry

end
