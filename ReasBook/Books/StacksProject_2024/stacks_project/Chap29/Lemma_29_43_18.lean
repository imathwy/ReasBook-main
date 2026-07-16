import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_37_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}

/- Semantic recall:
`lean_leansearch` recalled the canonical scheme-morphism predicates `UniversallyClosed` and
`IsAffineHom`. Local Chapter 29 precedent uses `RelativelyAmple f L` for `f`-ample invertible
modules and states section nonvanishing loci by the explicit stalkwise formula below. The Stacks
tag evidence is consistent: item tag `0EKE` agrees with the source URL ending in `/tag/0EKE`.
-/

/-- Lemma 29.43.18: if `f : X ⟶ S` is universally closed and `L` is an `f`-ample
invertible `\mathcal O_X`-module, then for every section `s ∈ Γ(X, L)` the nonvanishing open
`X_s`, viewed as an open subscheme of `X`, is affine over `S`. -/
@[stacks 0EKE]
theorem sectionNonvanishing_toBase_isAffineHom
    [Scheme.Modules.Invertible L] [RelativelyAmple f L]
    (hf : UniversallyClosed f)
    (s : L.sections) (U : X.Opens)
    (hU : (U : Set X) =
      {x | TopCat.Presheaf.Γgerm L.val.presheaf x (s.1 (op ⊤)) ∉
        ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
          (⊤ : Submodule (X.presheaf.stalk x)
            (RingedSpace.stalkModuleCat L x)))}) :
    IsAffineHom (U.ι ≫ f) := sorry

end

end AlgebraicGeometry
