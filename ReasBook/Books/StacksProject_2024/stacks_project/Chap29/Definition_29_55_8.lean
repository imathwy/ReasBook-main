import StacksProject_2024.stacks_project.Chap29.Definition_29_45_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_47_3
import StacksProject_2024.stacks_project.Chap29.Definition_29_54_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `Scheme.normalization` and `Scheme.normalizationTo` from Definition 29.54.1
-- already provide the canonical normalization data. The source item adds the weak-normalization
-- conditions and initiality clause on an intermediate factorization of `X.normalizationTo`, so
-- the source-facing owner records that structure directly.

/-- Definition 29.55.8: the weak normalization `X^{wn}` of a scheme `X` is the weak
normalization of `X` in its normalization `X^ν`. Concretely, it is an intermediate factorization
`X.normalization ⟶ X^{wn} ⟶ X` of the normalization morphism such that `X^{wn} ⟶ X` is a
universal homeomorphism, `X^{wn}` is absolutely weakly normal, and the factorization is initial
among all factorizations of `X.normalizationTo` whose second map is a universal homeomorphism.
This formalizes the source formula `X^{wn} = X^{X^ν /wn}` by keeping the source-facing
weak-normalization owner while reusing the canonical factorization core of `X.normalizationTo`. -/
@[stacks 0H3R]
structure WeakNormalization (X : Scheme.{u})
    [QuasiCompact (genericPointSpectrumCoproductTo X)]
    [QuasiSeparated (genericPointSpectrumCoproductTo X)]
    extends CategoryTheory.Factorisation X.normalizationTo where
  /-- The weak-normalization morphism to `X` is a universal homeomorphism. -/
  isUniversalHomeomorphism_π : UniversalHomeomorphism π
  /-- The intermediate scheme is absolutely weakly normal. -/
  absolutelyWeaklyNormal_mid : AbsolutelyWeaklyNormal mid
  /-- The weak normalization is initial among factorizations of `X.normalizationTo` whose second
  map is a universal homeomorphism. -/
  desc :
    ∀ {Z : Scheme.{u}} (g : X.normalization ⟶ Z) (π' : Z ⟶ X),
      UniversalHomeomorphism π' →
      g ≫ π' = X.normalizationTo →
      ∃! h : mid ⟶ Z, ι ≫ h = g ∧ h ≫ π' = π

namespace WeakNormalization

variable {X : Scheme.{u}}
variable [QuasiCompact (genericPointSpectrumCoproductTo X)]
variable [QuasiSeparated (genericPointSpectrumCoproductTo X)]

/-- The underlying scheme `X^{wn}` of a weak normalization. -/
abbrev obj (W : WeakNormalization X) : Scheme.{u} :=
  W.mid

/-- The weak-normalization morphism `X^{wn} ⟶ X`. -/
abbrev toScheme (W : WeakNormalization X) : W.obj ⟶ X :=
  W.π

/-- The factorization map from the normalization `X^ν` to `X^{wn}`. -/
abbrev fromNormalization (W : WeakNormalization X) : X.normalization ⟶ W.obj :=
  W.ι

/-- The normalization morphism factors through the weak normalization. -/
theorem fromNormalization_comp_toScheme (W : WeakNormalization X) :
    W.fromNormalization ≫ W.toScheme = X.normalizationTo :=
  W.ι_π

end WeakNormalization

/-- A weak normalization carries a universal-homeomorphism structure on its map to `X`. -/
@[stacks 0H3R]
instance instUniversalHomeomorphismToScheme (X : Scheme.{u})
    [QuasiCompact (genericPointSpectrumCoproductTo X)]
    [QuasiSeparated (genericPointSpectrumCoproductTo X)]
    (W : WeakNormalization X) :
    UniversalHomeomorphism W.toScheme :=
  W.isUniversalHomeomorphism_π

/-- The underlying scheme of a weak normalization is absolutely weakly normal. -/
@[stacks 0H3R]
instance instAbsolutelyWeaklyNormalObj (X : Scheme.{u})
    [QuasiCompact (genericPointSpectrumCoproductTo X)]
    [QuasiSeparated (genericPointSpectrumCoproductTo X)]
    (W : WeakNormalization X) :
    AbsolutelyWeaklyNormal W.obj :=
  W.absolutelyWeaklyNormal_mid

end AlgebraicGeometry.Scheme
