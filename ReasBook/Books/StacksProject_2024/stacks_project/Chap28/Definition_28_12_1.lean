import Mathlib.AlgebraicGeometry.Noetherian
import StacksProject_2024.Chap10.Definition_10_157_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A local Noetherian ring satisfying `(R_k)` is regular whenever its Krull dimension is at most
`k`. -/
private theorem isRegularLocalRing_of_serreConditionR
    (A : Type u) [CommRing A] [IsLocalRing A] {k : ℕ} [SerreConditionR A k]
    (hk : ringKrullDim A ≤ k) :
    IsRegularLocalRing A := by
  sorry

/- Semantic recall:
- Definition 28.12.1(1) is owned here as the source-facing Chapter 28 scheme predicate for
  `(R_k)`.
- Definition 28.12.1(2) is the later Chapter 30 scheme owner `satisfiesSerreConditionS`; this
  file therefore keeps only the Chapter 28 `(R_k)` owner, without introducing a duplicate
  scheme-side `(S_k)` wrapper.
-/

variable (X : Scheme.{u})

/-- Definition 28.12.1 (1): a scheme `X` is regular in codimension `k`, or has property `(R_k)`,
if every point `x` with `dim(\mathcal O_{X, x}) ≤ k` has regular local ring
`\mathcal O_{X, x}`. The source states this in the locally Noetherian setting, but the stalkwise
condition itself does not use that ambient hypothesis. -/
@[stacks 033Q]
def satisfiesSerreConditionR (k : ℕ) : Prop :=
  ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ k → IsRegularLocalRing (X.presheaf.stalk x)

/-- Unfold the stalkwise `(R_k)` condition for a scheme. -/
@[simp] theorem satisfiesSerreConditionR_iff (k : ℕ) :
    satisfiesSerreConditionR X k ↔
      ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ k → IsRegularLocalRing (X.presheaf.stalk x) :=
  Iff.rfl

/-- If a scheme `X` satisfies `(R_k)`, then each stalk of Krull dimension at
most `k` is a regular local ring. -/
theorem satisfiesSerreConditionR.isRegularLocalRing_stalk {k : ℕ}
    (hX : satisfiesSerreConditionR X k) (x : X)
    (hx : ringKrullDim (X.presheaf.stalk x) ≤ k) :
    IsRegularLocalRing (X.presheaf.stalk x) :=
  hX x hx

/-- On a locally Noetherian scheme, the source-facing scheme condition `(R_k)` implies the
ring-level Serre condition `(R_k)` on every stalk. -/
theorem satisfiesSerreConditionR.serreConditionR_stalk {k : ℕ}
    [IsLocallyNoetherian X]
    (hX : satisfiesSerreConditionR X k) (x : X) :
    SerreConditionR (X.presheaf.stalk x) k := by
  sorry

/-- On a locally Noetherian scheme, stalkwise ring-level Serre condition `(R_k)` implies the
source-facing scheme condition `(R_k)`. -/
theorem satisfiesSerreConditionR.of_stalkwise_serreConditionR {k : ℕ}
    [IsLocallyNoetherian X]
    (hX : ∀ x : X, SerreConditionR (X.presheaf.stalk x) k) :
    satisfiesSerreConditionR X k := by
  intro x hx
  let A := X.presheaf.stalk x
  letI : SerreConditionR A k := hX x
  exact isRegularLocalRing_of_serreConditionR A hx

/-- On a locally Noetherian scheme, the source-facing scheme condition `(R_k)` is equivalent to
requiring each stalk to satisfy the ring-level Serre condition `(R_k)`. -/
theorem satisfiesSerreConditionR_iff_stalkwise_serreConditionR
    [IsLocallyNoetherian X] (k : ℕ) :
    satisfiesSerreConditionR X k ↔ ∀ x : X, SerreConditionR (X.presheaf.stalk x) k := by
  constructor
  · intro hX x
    exact satisfiesSerreConditionR.serreConditionR_stalk X hX x
  · intro hX
    exact satisfiesSerreConditionR.of_stalkwise_serreConditionR X hX

end AlgebraicGeometry.Scheme
