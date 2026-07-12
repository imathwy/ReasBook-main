import Mathlib.Analysis.InnerProductSpace.PiL2
import SmoothManifolds_Lee_2012.Chap03.Sec03_13.Definition_3_13_extra_1
import SmoothManifolds_Lee_2012.Chap03.Sec03_13.Definition_3_13_extra_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ContDiff Manifold

-- Semantic search note: the `lean_leansearch` MCP tool was unavailable in this session, so this
-- file uses local repository precedent plus mathlib inspection of `PointDerivation`,
-- `Derivation.mk'`, and `EuclideanSpace.projₗ`.

variable {n : ℕ}

local notation "R^n" => EuclideanSpace ℝ (Fin n)
local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "SmoothRn" => C^∞⟮I, EuclideanSpace ℝ (Fin n); ℝ⟯

/-- The `i`-th coordinate function on `ℝ^n`, viewed as a smooth real-valued map. -/
def coordinate_cont_mdiff_map (i : Fin n) : SmoothRn :=
  (EuclideanSpace.proj i : R^n →L[ℝ] ℝ)

/-- Applying the smooth coordinate projection returns the corresponding coordinate. -/
theorem coordinate_cont_mdiff_map_apply (i : Fin n) (x : R^n) :
    coordinate_cont_mdiff_map i x = x i := sorry

/-- The directional derivative at `a` is additive in the smooth function argument. -/
theorem directional_fderiv_map_add (a : R^n) (v : geometric_tangent_space a)
    (f g : SmoothRn) :
    fderiv ℝ (f + g) a v = fderiv ℝ f a v + fderiv ℝ g a v := sorry

/-- The directional derivative at `a` is `ℝ`-linear in the smooth function argument. -/
theorem directional_fderiv_map_smul (a : R^n) (v : geometric_tangent_space a)
    (c : ℝ) (f : SmoothRn) :
    fderiv ℝ (c • f) a v = c * fderiv ℝ f a v := sorry

/-- The directional derivative at `a` satisfies the Leibniz rule on smooth real-valued functions
on `ℝ^n`. -/
theorem directional_fderiv_leibniz_formula (a : R^n) (v : geometric_tangent_space a)
    (f g : SmoothRn) :
    fderiv ℝ (f * g) a v = f a * fderiv ℝ g a v + g a * fderiv ℝ f a v := sorry

/-- The directional derivative at `a` along the based vector `v` packaged as a point derivation. -/
def directional_point_derivation (a : R^n) (v : geometric_tangent_space a) :
    PointDerivation I a :=
  Derivation.mk'
    { toFun := fun f ↦ fderiv ℝ f a v
      map_add' := fun f g ↦ directional_fderiv_map_add a v f g
      map_smul' := fun c f ↦ directional_fderiv_map_smul a v c f }
    (fun f g ↦ directional_fderiv_leibniz_formula a v f g)

/-- Evaluating `directional_point_derivation` is evaluation of the Fréchet derivative in the
direction `v`. -/
theorem directional_point_derivation_apply (a : R^n) (v : geometric_tangent_space a)
    (f : SmoothRn) :
    directional_point_derivation a v f = fderiv ℝ f a v := sorry

/-- Proposition 3.2 (1): for each geometric tangent vector `v ∈ ℝ_a^n`, the associated map
`Dᵥ|ₐ` is a derivation at `a` on smooth real-valued functions on `ℝ^n`. -/
theorem directional_point_derivation_leibniz (a : R^n) (v : geometric_tangent_space a)
    (f g : SmoothRn) :
    directional_point_derivation a v (f * g) =
      f a * directional_point_derivation a v g +
        g a * directional_point_derivation a v f := sorry

/-- The assignment `v ↦ Dᵥ|ₐ` is additive in the geometric tangent vector. -/
theorem geometric_to_point_derivation_map_add (a : R^n)
    (v w : geometric_tangent_space a) :
    directional_point_derivation a (v + w) =
      directional_point_derivation a v +
        directional_point_derivation a w := sorry

/-- The assignment `v ↦ Dᵥ|ₐ` is `ℝ`-linear in the geometric tangent vector. -/
theorem geometric_to_point_derivation_map_smul (a : R^n) (c : ℝ)
    (v : geometric_tangent_space a) :
    directional_point_derivation a (c • v) =
      c • directional_point_derivation a v := sorry

/-- The map sending a geometric tangent vector at `a` to its associated point derivation. -/
def geometric_to_point_derivation (a : R^n) :
    geometric_tangent_space a →ₗ[ℝ] PointDerivation I a where
  toFun := directional_point_derivation a
  map_add' := fun v w ↦ geometric_to_point_derivation_map_add a v w
  map_smul' := fun c v ↦ geometric_to_point_derivation_map_smul a c v

/-- Applying `geometric_to_point_derivation` sends `v` to the directional point derivation
`Dᵥ|ₐ`. -/
theorem geometric_to_point_derivation_apply (a : R^n) (v : geometric_tangent_space a) :
    geometric_to_point_derivation a v =
      directional_point_derivation a v := sorry

/-- The coordinate-evaluation recipe recovers a geometric tangent vector from a point derivation. -/
theorem point_derivation_to_geometric_map_add_formula (a : R^n)
    (w₁ w₂ : PointDerivation I a) :
    (∑ i, (w₁ + w₂) (coordinate_cont_mdiff_map i) •
        EuclideanSpace.basisFun (Fin n) ℝ i) =
      (∑ i, w₁ (coordinate_cont_mdiff_map i) • EuclideanSpace.basisFun (Fin n) ℝ i) +
        ∑ i,
          w₂ (coordinate_cont_mdiff_map i) • EuclideanSpace.basisFun (Fin n) ℝ i := sorry

/-- The coordinate-evaluation recipe is `ℝ`-linear in the point derivation. -/
theorem point_derivation_to_geometric_map_smul_formula (a : R^n) (c : ℝ)
    (w : PointDerivation I a) :
    (∑ i, (c • w) (coordinate_cont_mdiff_map i) •
        EuclideanSpace.basisFun (Fin n) ℝ i) =
      c • ∑ i,
        w (coordinate_cont_mdiff_map i) • EuclideanSpace.basisFun (Fin n) ℝ i := sorry

/-- Recover a geometric tangent vector from a point derivation by evaluating it on the coordinate
functions. -/
def point_derivation_to_geometric (a : R^n) :
    PointDerivation I a →ₗ[ℝ] geometric_tangent_space a where
  toFun := fun w ↦
    ∑ i, w (coordinate_cont_mdiff_map i) • EuclideanSpace.basisFun (Fin n) ℝ i
  map_add' := fun w₁ w₂ ↦ point_derivation_to_geometric_map_add_formula a w₁ w₂
  map_smul' := fun c w ↦ point_derivation_to_geometric_map_smul_formula a c w

/-- Projecting `point_derivation_to_geometric` to coordinate `i` recovers the derivation applied
to the `i`-th coordinate function. -/
theorem point_derivation_to_geometric_proj (a : R^n) (w : PointDerivation I a) (i : Fin n) :
    EuclideanSpace.proj i (point_derivation_to_geometric a w) =
      w (coordinate_cont_mdiff_map i) := sorry

/-- Applying `point_derivation_to_geometric` after `directional_point_derivation` recovers the
original geometric tangent vector. -/
theorem geometric_to_point_derivation_left_inv (a : R^n) (v : geometric_tangent_space a) :
    point_derivation_to_geometric a (directional_point_derivation a v) = v := sorry

/-- Applying `directional_point_derivation` after `point_derivation_to_geometric` recovers the
original point derivation. -/
theorem geometric_to_point_derivation_right_inv (a : R^n) (w : PointDerivation I a) :
    directional_point_derivation a (point_derivation_to_geometric a w) = w := sorry

/-- Proposition 3.2 (2): the map `v ↦ Dᵥ|ₐ` is a linear isomorphism from the geometric tangent
space `ℝ_a^n` onto the point-derivation tangent space `T_aℝ^n`. -/
def geometric_to_point_derivation_linear_equiv (a : R^n) :
    geometric_tangent_space a ≃ₗ[ℝ] PointDerivation I a where
  toLinearMap := geometric_to_point_derivation a
  invFun := point_derivation_to_geometric a
  left_inv := geometric_to_point_derivation_left_inv a
  right_inv := geometric_to_point_derivation_right_inv a

/-- The forward direction of `geometric_to_point_derivation_linear_equiv` is the map
`v ↦ Dᵥ|ₐ`. -/
theorem geometric_to_point_derivation_linear_equiv_apply (a : R^n)
    (v : geometric_tangent_space a) :
    geometric_to_point_derivation_linear_equiv a v =
      directional_point_derivation a v := sorry
