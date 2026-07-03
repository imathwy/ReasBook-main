import Mathlib
import StacksProject_2024.Chap15.Definition_15_67_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Pretriangulated

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable {a b : ℤ}

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for Lemma 15.67.5:
- primary domain: tor-amplitude in the derived category `D(R)` and its behavior with respect to
  shifts and distinguished triangles;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `Triangle.rotate`,
  `Triangle.invRotate`,
  `rot_of_distTriang`,
  `inv_rot_of_distTriang`;
- best owner abstraction: the source-facing owner is `HasTorAmplitudeIn K a b`; distinguished
  triangle closure is derived API built from the canonical triangulated operations `rotate` and
  `invRotate`, together with the shift behavior of tor-amplitude;
- primitive vs. derived:
  primitive data are the tor-amplitude predicate from Definition `15.67.1` and its canonical
  shift transport;
  derived API are the three `obj₁`/`obj₂`/`obj₃` closure statements for distinguished triangles;
- source/core/bridge triage:
  `source-facing`: the three numbered closure statements below;
  `core/canonical`: the owner predicate `HasTorAmplitudeIn`;
  `bridge/view`: the owner-level shift theorem below and the use of `Triangle.rotate` /
    `Triangle.invRotate`
    to move between the three source-facing clauses.

This file keeps the textbook statements as the public surface, but treats clause `(1)` as the
primitive distinguished-triangle propagation statement. Clauses `(2)` and `(3)` are then expressed
as derived consequences via the canonical shift theorem and rotation operators rather than as
independent peer API. -/

-- Proof sketch: compare the homology of `K⟦1⟧ ⊗[R]^L M[0]` with the shifted homology of
-- `K ⊗[R]^L M[0]` using the standard shift isomorphism on the homology functors.
/-- Tor-amplitude shifts with the derived-category translation functor: shifting `K` by `n`
translates the tor-amplitude interval by the same amount. -/
theorem hasTorAmplitudeIn_shift_iff (K : DMod) (n a b : ℤ) :
    HasTorAmplitudeIn (K⟦n⟧) a b ↔ HasTorAmplitudeIn K (a + n) (b + n) := by
  sorry

-- Proof sketch: choose a tor-amplitude interval for `K`, translate it by `n` using
-- `hasTorAmplitudeIn_shift_iff`, and conversely shift the interval back by `-n`.
/-- Finite tor dimension is invariant under shifts in the derived category. -/
theorem hasFiniteTorDimension_shift_iff (K : DMod) (n : ℤ) :
    HasFiniteTorDimension (K⟦n⟧) ↔ HasFiniteTorDimension K := by
  sorry

-- Proof sketch: apply `- ⊗[R]^L N[0]` to the distinguished triangle, use that derived tensor
-- preserves distinguished triangles, and read off the vanishing range for the third term from the
-- associated long exact homology sequence.
/-- Lemma 15.67.5 (1): in a distinguished triangle in `D(R)`, if the first term has
tor-amplitude in `[a + 1, b + 1]` and the second term has tor-amplitude in `[a, b]`, then the
third term has tor-amplitude in `[a, b]`. -/
theorem hasTorAmplitudeIn_obj₃_of_distinguishedTriangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : HasTorAmplitudeIn T.obj₁ (a + 1) (b + 1))
    (h₂ : HasTorAmplitudeIn T.obj₂ a b) :
    HasTorAmplitudeIn T.obj₃ a b := sorry

-- Proof sketch: tensor with an arbitrary module placed in degree `0`, use the long exact
-- homology sequence of the distinguished triangle, and apply two-out-of-three for vanishing in
-- degrees outside `[a, b]`.
/-- Lemma 15.67.5 (2): in a distinguished triangle in `D(R)`, if the first and third terms have
tor-amplitude in `[a, b]`, then the second term has tor-amplitude in `[a, b]`. -/
theorem hasTorAmplitudeIn_obj₂_of_distinguishedTriangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : HasTorAmplitudeIn T.obj₁ a b)
    (h₃ : HasTorAmplitudeIn T.obj₃ a b) :
    HasTorAmplitudeIn T.obj₂ a b := by
  -- Apply part `(1)` to the inverse-rotated triangle
  -- `T.obj₃⟦-1⟧ ⟶ T.obj₁ ⟶ T.obj₂ ⟶ T.obj₃`.
  have h₃' : HasTorAmplitudeIn (T.obj₃⟦(-1 : ℤ)⟧) (a + 1) (b + 1) := by
    have h₃'' : HasTorAmplitudeIn T.obj₃ ((a + 1) + (-1)) ((b + 1) + (-1)) := by
      simpa [add_assoc] using h₃
    exact (hasTorAmplitudeIn_shift_iff T.obj₃ (-1) (a + 1) (b + 1)).2 h₃''
  exact
    hasTorAmplitudeIn_obj₃_of_distinguishedTriangle T.invRotate
      (inv_rot_of_distTriang T hT) h₃' h₁

-- Proof sketch: rotate the distinguished triangle and reduce to the first closure statement,
-- which shifts the tor-amplitude bounds by one on the first vertex exactly as required.
/-- Lemma 15.67.5 (3): in a distinguished triangle in `D(R)`, if the second term has
tor-amplitude in `[a + 1, b + 1]` and the third term has tor-amplitude in `[a, b]`, then the
first term has tor-amplitude in `[a + 1, b + 1]`. -/
theorem hasTorAmplitudeIn_obj₁_of_distinguishedTriangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₂ : HasTorAmplitudeIn T.obj₂ (a + 1) (b + 1))
    (h₃ : HasTorAmplitudeIn T.obj₃ a b) :
    HasTorAmplitudeIn T.obj₁ (a + 1) (b + 1) := by
  -- Apply part `(1)` to the rotated triangle
  -- `T.obj₂ ⟶ T.obj₃ ⟶ T.obj₁⟦1⟧ ⟶ T.obj₂⟦1⟧`,
  -- then shift back.
  have hshift :
      HasTorAmplitudeIn (T.obj₁⟦(1 : ℤ)⟧) a b :=
    hasTorAmplitudeIn_obj₃_of_distinguishedTriangle T.rotate
      (rot_of_distTriang T hT) h₂ h₃
  exact (hasTorAmplitudeIn_shift_iff T.obj₁ 1 a b).1 hshift

end

end CategoryTheory
