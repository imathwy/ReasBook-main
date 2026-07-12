import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

-- Semantic recall: `lean_leansearch` returned the canonical scheme-theoretic-image owner
-- `Scheme.Hom.image`, its ideal-sheaf datum `Scheme.Hom.ker`, the open-restriction kernel formula
-- `Scheme.ker_morphismRestrict_ideal`, and the dominant morphism predicate `IsDominant`.
-- The Stacks tag evidence is consistent: item tag `01R8` matches the source URL `/tag/01R8`.

/-- Lemma 29.6.3 (1): for a quasi-compact morphism of schemes `f : X \to Y`, the kernel ideal
sheaf defining the scheme-theoretic image is represented on affine opens by the kernel of the
restriction map on sections. This is the current `IdealSheafData` form of the source
quasi-coherence assertion for `Ker(\mathcal O_Y \to f_* \mathcal O_X)`. -/
@[stacks 01R8]
theorem schemeTheoreticImage_kernelIdeal_eq_kernel
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (U : Y.affineOpens) :
    f.ker.ideal U = RingHom.ker (f.app U).hom := sorry

/-- Lemma 29.6.3 (2): the scheme-theoretic image of `f : X \to Y` is the closed subscheme of
`Y` cut out by the kernel ideal sheaf `f.ker`. -/
@[stacks 01R8]
theorem schemeTheoreticImage_eq_kernelSubscheme
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] :
    Scheme.Hom.image f = f.ker.subscheme := sorry

/-- Lemma 29.6.3 (3): for any open subscheme `U \subset Y`, the kernel ideal sheaf defining the
scheme-theoretic image of the restricted morphism `f|_{f^{-1}(U)} : f^{-1}(U) \to U` is the
restriction of the kernel ideal sheaf defining the scheme-theoretic image of `f`. Equivalently,
the scheme-theoretic image restricts to the scheme-theoretic intersection with `U`. -/
@[stacks 01R8]
theorem schemeTheoreticImage_restrictOpen_ker_eq_comap
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (U : Y.Opens) :
    (f ∣_ U).ker = f.ker.comap U.ι := sorry

/-- Lemma 29.6.3 (4): for a quasi-compact morphism `f : X \to Y`, the induced morphism from `X`
to its scheme-theoretic image has dense image, i.e. it is dominant. -/
@[stacks 01R8]
theorem schemeTheoreticImage_toImage_isDominant
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] :
    IsDominant (Scheme.Hom.toImage f) := sorry

end

end AlgebraicGeometry
