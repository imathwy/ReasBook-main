import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap15.Lemma_15_75_15

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "RHomPkg" => MonoidalClosed DMod

/-
Domain-style sampling for Lemma 15.127.3:
- primary domain: rigid duality for perfect objects in the monoidal derived category `D(R)`;
- sampled owner declarations:
  `ExactPairing`,
  `HasLeftDual`,
  `derivedDualExactPairing`,
  `leftDualIso`,
  `DerivedCategory.IsPerfect`;
- best owner abstraction:
  `source-facing`: the existence theorem that `M` admits a duality datum exactly when `M` is
    perfect, together with the identification of any chosen dual object with the canonical derived
    dual `Mᵛ⟮H⟯ = R\mathrm{Hom}_R(M, R[0])`;
  `core/canonical`: an arbitrary exact pairing `ExactPairing N M` and the chapter owner
    `DerivedCategory.IsPerfect`;
  `bridge/view`: the canonical pairing `derivedDualExactPairing` attached to a perfect object and
    the uniqueness isomorphism `leftDualIso` comparing any other left dual with it.

Primitive data are only the chosen derived-internal-Hom package `H`, the object `M`, and an
arbitrary exact pairing `ExactPairing N M`. The canonical dual `Mᵛ⟮H⟯` and the comparison from a
chosen dual object are derived API, so this file should recall `derivedDualExactPairing` for the
forward half, state the converse for arbitrary dual data, and keep the uniqueness isomorphism only
as a bridge to the canonical derived dual.
-/

variable (H : RHomPkg)

/- Lemma 15.127.3 (forward direction): for a perfect object of `D(R)`, the derived dual
`Mᵛ⟮H⟯ = R\mathrm{Hom}_R(M, R[0])` is canonically a left dual via the owner declaration
`derivedDualExactPairing`. -/
recall derivedDualExactPairing
    (H : RHomPkg) {M : DMod}
    (hM : DerivedCategory.IsPerfect M) :
    ExactPairing Mᵛ⟮H⟯ M

-- Proof sketch: choose the coevaluation from the assumed exact pairing `ExactPairing N M`, factor it
-- through a bounded finite free subcomplex by Lemma `15.127.2`, and apply the triangle identity
-- to show that `𝟙_M` factors through a perfect object. Since perfect objects are closed under
-- retracts, `M` itself is perfect.
/-- Lemma 15.127.3 (converse): if `M` admits a duality datum in the monoidal category `D(R)`,
then `M` is perfect. -/
theorem exactPairing_isPerfect
    {M N : DMod} (hpair : ExactPairing N M) :
    DerivedCategory.IsPerfect M := by
  sorry

/- Bridge/view for Lemma `15.127.3`: uniqueness of left duals is already owned by
`leftDualIso`. For a chosen pairing `hpair : ExactPairing N M`, the textbook comparison
`N ≅ Mᵛ⟮H⟯` is obtained directly as
`leftDualIso hpair (derivedDualExactPairing H (exactPairing_isPerfect hpair))`,
so this file should not introduce a second wrapper around that owner declaration. -/
recall leftDualIso
    {C : Type _} [Category C] [MonoidalCategory C]
    {X₁ X₂ Y : C} (p₁ : ExactPairing X₁ Y) (p₂ : ExactPairing X₂ Y) :
    X₁ ≅ X₂

end

end CategoryTheory
