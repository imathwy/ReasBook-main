import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_15_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_29_1

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (X S : OrderDual I ⥤ Scheme.{u}) (φ : X ⟶ S)
variable (cX : Cone X) (hcX : IsLimit cX) (cS : Cone S) (hcS : IsLimit cS)
variable [∀ i : I, CompactSpace ↥(S.obj i)]
variable [∀ i : I, QuasiSeparatedSpace ↥(S.obj i)]
variable [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (S.map (homOfLE hii'))]
variable [∀ i : I, Scheme.Hom.FiniteType (φ.app i)]
variable [∀ {i i' : I} (hii' : i ≤ i'), IsClosedImmersion
  (pullback.lift (X.map (homOfLE hii')) (φ.app i') (φ.naturality (homOfLE hii')))]
variable (f : cX.pt ⟶ cS.pt)
variable (hf : ∀ i : I, cX.π.app i ≫ φ.app i = f ≫ cS.π.app i)

-- Semantic recall / analogue check:
-- - `lean_leansearch` recalled the canonical scheme-side fibre owner `Scheme.Hom.fiber` and the
--   project owner `Scheme.Hom.RelativeDimensionLE`;
-- - local Chapter 29 precedent records the pointwise fibre-dimension condition through
--   `Scheme.Hom.fiberDimensionAt` and the stagewise conclusion through `RelativeDimensionLE`;
-- - local Chapter 32 precedent states inverse-limit approximation results using explicit diagrams,
--   chosen limit cones, and explicit comparison morphisms rather than a wrapper around the system.

/-- Lemma 32.18.1: for a directed inverse system of finite type morphisms of schemes
`f_i : X_i ⟶ S_i` with affine base transition maps, quasi-compact quasi-separated bases, and closed
immersion comparison maps `X_{i'} ⟶ X_i ×_{S_i} S_{i'}`, if the limit morphism has fibre dimension
at most `d` at every point, then some stage morphism has relative dimension at most `d`. -/
@[stacks 05M5]
theorem exists_relativeDimensionLE_stage_of_limit_fiberDimensionLE (d : ℕ)
    (hfdim : ∀ x : cX.pt, f.fiberDimensionAt x ≤ (d : WithBot ℕ∞)) :
    ∃ i : I, Scheme.Hom.RelativeDimensionLE (φ.app i) d := sorry

end

end AlgebraicGeometry
