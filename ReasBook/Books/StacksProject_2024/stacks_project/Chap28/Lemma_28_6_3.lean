import Mathlib
import StacksProject_2024.stacks_project.Chap28.Definition_28_4_2
import StacksProject_2024.stacks_project.Chap28.Lemma_28_4_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local analogue check:
-- - `lean_leansearch` returned the canonical open-cover owner theorem
--   `TopologicalSpace.IsOpenCover.jacobsonSpace_iff`;
-- - local Chapter 28 files already fix the project surfaces `Scheme.HasRingPropertyLocally` and
--   `jacobsonSpace_spec_iff_isJacobsonRing`;
-- - nearby locality files such as `Lemma_28_7_2` and `Lemma_28_13_5` use the same affine/open-cover
--   split, so this item is formalized as the Jacobson specialization of that pattern.

variable (X : Scheme.{u})

/-- Lemma 28.6.3 (1): a scheme `X` is Jacobson if and only if it is locally Jacobson in the sense
of Definition 28.4.2, i.e. iff `X.HasRingPropertyLocally (fun R ↦ IsJacobsonRing R)`. -/
@[stacks 01P4]
theorem jacobsonSpace_iff_hasRingPropertyLocally_isJacobsonRing :
    JacobsonSpace X ↔ X.HasRingPropertyLocally (fun R ↦ IsJacobsonRing R) := sorry

/-- Lemma 28.6.3 (2): a scheme `X` is Jacobson if and only if for every affine open `U ⊆ X`, the
ring of sections `Γ(X, U)` is Jacobson. -/
@[stacks 01P4]
theorem jacobsonSpace_iff_forall_affineOpen_sectionsRing_isJacobsonRing :
    JacobsonSpace X ↔
      ∀ U : X.affineOpens, IsJacobsonRing (Γ(X, (U : X.Opens))) := sorry

/-- Lemma 28.6.3 (3): a scheme `X` is Jacobson if and only if it admits an affine open covering
whose section rings are Jacobson. -/
@[stacks 01P4]
theorem jacobsonSpace_iff_exists_affineOpenCover_sectionsRing_isJacobsonRing :
    JacobsonSpace X ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, IsJacobsonRing (Γ(X, (𝒰.openCover.f i).opensRange)) := sorry

/-- Lemma 28.6.3 (4): a scheme `X` is Jacobson if and only if it admits an open covering by
Jacobson open subschemes. -/
@[stacks 01P4]
theorem jacobsonSpace_iff_exists_openCover_by_jacobsonOpens :
    JacobsonSpace X ↔
      ∃ 𝒰 : X.OpenCover, ∀ i : 𝒰.I₀, JacobsonSpace ((𝒰.f i).opensRange).toScheme := sorry

/-- Lemma 28.6.3 (5): if a scheme `X` is Jacobson, then every open subscheme of `X` is Jacobson. -/
@[stacks 01P4]
theorem jacobsonSpace_toScheme (hX : JacobsonSpace X) (U : X.Opens) :
    JacobsonSpace U.toScheme := sorry

end AlgebraicGeometry.Scheme
