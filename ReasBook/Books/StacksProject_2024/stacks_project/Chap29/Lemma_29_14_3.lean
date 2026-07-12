import Mathlib
import StacksProject_2024.Chap29.Definition_29_14_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}
variable
  (P : {R T : Type u} → [CommRing R] → [CommRing T] → (R →+* T) → Prop)

/- Semantic recall / analogue check:
- `AlgebraicGeometry.affineLocally_iff_affineOpens_le` is the canonical affine-open scheme
  surface for local ring-hom properties;
- `Definition_29_14_2.lean` records the source hypothesis “locally of type `P`” by the
  project-local owner `LocallyOfType P f`, so this file keeps that owner, adds the canonical
  `affineOpens` companion, and exposes the source-facing affine-open consequence on the standard
  `IsAffineOpen` API.
-/

/-- Canonical affine-open companion to `LocallyOfType`: under a local property hypothesis on `P`,
every affine open `U ⊆ X` mapping into an affine open `V ⊆ S` induces a ring map with property
`P`. -/
theorem locallyOfType_affineOpens_appLE
    (hf : LocallyOfType P f) (hP : RingHom.PropertyIsLocal P)
    (U : X.affineOpens) (V : S.affineOpens) (e : U ≤ f ⁻¹ᵁ V) :
    P (CommRingCat.Hom.hom (f.appLE V U e)) := by
  rw [locallyOfType_iff_affineLocally P f hP] at hf
  exact (affineLocally_iff_affineOpens_le P f).mp hf V U e

/-- Lemma 29.14.3: if `f : X ⟶ S` is locally of type `P` and `P` is a local property of ring
maps, then for every affine open `U ⊆ X` and affine open `V ⊆ S` with `f(U) ⊆ V`, the induced
ring map `\Gamma(S, V) \to \Gamma(X, U)` has property `P`. -/
@[stacks 01ST]
theorem locallyOfType_affineOpen_appLE
    (hf : LocallyOfType P f) (hP : RingHom.PropertyIsLocal P)
    {U : X.Opens} (hU : IsAffineOpen U)
    {V : S.Opens} (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V) :
    P (CommRingCat.Hom.hom (f.appLE V U e)) := by
  simpa using locallyOfType_affineOpens_appLE P hf hP ⟨U, hU⟩ ⟨V, hV⟩ e

end AlgebraicGeometry
