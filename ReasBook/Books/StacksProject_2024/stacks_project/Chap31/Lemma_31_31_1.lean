import Mathlib
import StacksProject_2024.Chap29.RelativeProjPresentation

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {S X Z : Scheme.{u}} {p : X ⟶ S}

namespace RelativeProjPresentation

/-- The `d`-th twist on a closed subscheme of a relative `Proj`, obtained by restricting the
ambient twist `\mathcal O_X(d)` along the closed immersion. -/
abbrev closedSubschemeTwist
    (P : RelativeProjPresentation p) (i : Z ⟶ X) (d : ℤ) : Z.Modules :=
  (Scheme.Modules.pullback i).obj (P.twist d)

/-- The `d`-th graded piece of the quotient presentation attached to a closed subscheme of a
relative `Proj`, expressed as the pushforward of the restricted twist along the induced map
`Z ⟶ S`. This is the degreewise owner corresponding to
`p_*((i_* \mathcal O_Z)(d))` in the source statement. -/
abbrev closedSubschemeDegreePiece
    (P : RelativeProjPresentation p) (i : Z ⟶ X) (d : ℕ) : S.Modules :=
  (Scheme.Modules.pushforward (i ≫ p)).obj (P.closedSubschemeTwist i (d : ℤ))

/-- For a degreewise quotient map from the ambient relative-`Proj` presentation to a closed
subscheme presentation, the degree-`d` kernel subobject is the `d`-th piece of the source kernel
ideal sheaf. -/
abbrev closedSubschemeKernelDegreePiece
    (P : RelativeProjPresentation p) (i : Z ⟶ X) (Q : RelativeProjPresentation (i ≫ p))
    (q : ∀ d : ℕ, P.degreePiece d ⟶ Q.degreePiece d) (d : ℕ) :
    Subobject (P.degreePiece d) :=
  kernelSubobject (q d)

/-- Lemma 31.31.1: let `S` be a scheme, let `p : X = \underline{\mathrm{Proj}}_S(\mathcal A) \to
S` be a relative `Proj` presented by `P`, and let `i : Z \to X` be a closed subscheme. If `p` is
quasi-compact, then `Z` is the relative `Proj` of the quotient by the kernel ideal sheaf of the
canonical map
`\mathcal A \to \bigoplus_{d \ge 0} p_*((i_* \mathcal O_Z)(d))`.

In the current repository, the source quotient-relative-`Proj` statement is recorded as the
existence of a relative `Proj` presentation `Q` for `i ≫ p` whose twists are the pullbacks of the
ambient twists and whose nonnegative degree pieces are the pushforwards of those restricted
twists. The degreewise quotient maps `q d : P.degreePiece d ⟶ Q.degreePiece d` encode the source
kernel ideal through `P.closedSubschemeKernelDegreePiece i Q q d = kernelSubobject (q d)`. -/
@[stacks 0801]
theorem exists_closedSubscheme_quotientPresentation
    (P : RelativeProjPresentation p) (i : Z ⟶ X) [IsClosedImmersion i] [QuasiCompact p] :
    ∃ (Q : RelativeProjPresentation (i ≫ p))
      (q : ∀ d : ℕ, P.degreePiece d ⟶ Q.degreePiece d),
      (∀ d : ℕ, Epi (q d)) ∧
        (∀ d : ℕ, Q.degreePiece d = P.closedSubschemeDegreePiece i d) ∧
        (∀ d : ℤ, Q.twist d = P.closedSubschemeTwist i d) := sorry

end RelativeProjPresentation

end AlgebraicGeometry.Scheme.Hom
