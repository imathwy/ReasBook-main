import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap17.Lemma_17_10_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-
Domain-style sampling for Definition 17.10.6:
- primary domain: associated `\mathcal O_X`-modules on a ringed space, attached to modules over
  the global-sections ring;
- inspected owner declarations:
  `globalSectionsModuleFunctor`,
  `associatedModuleSheaf`,
  `associatedModuleSheafFromPresheafIso`,
  `associatedModuleSheafFromPresentationIso`;
- best owner abstraction: the canonical owner is `associatedModuleSheaf α M : X.Modules`;
- primitive data: a ringed space `X`, a commutative ring `R`, a ring map
  `α : R → Γ(X, \mathcal O_X)`, and an `R`-module `M`;
- derived API: the source-facing notation `𝓕[α]_M` for that owner, its identity specialization
  `𝓕_ M` as the Lean surface for the textbook `𝓕_M`, together with the proposition that a given
  `X.Modules` object is isomorphic to the corresponding associated sheaf.

Source/core/bridge triage:
- `source-facing`: the proposition that an `\mathcal O_X`-module `ℱ` is associated to `M`;
- `core/canonical`: the owner object `associatedModuleSheaf α M`;
- `bridge/view`: the presheaf and presentation realizations already identified upstream by
  `associatedModuleSheafFromPresheafIso` and `associatedModuleSheafFromPresentationIso`.

Definition 17.10.6 does not introduce a second owner; it only refers back to the canonical module
sheaf from Lemma 17.10.5. The file therefore keeps the public surface at that owner and expresses
"being associated to `M`" directly as isomorphism to it.
-/
variable {X : RingedSpace.{u}} {R : Type u} [CommRing R]
variable (α : R →+* X.presheaf.obj (op ⊤)) (M : ModuleCat R) (ℱ : X.Modules)
variable (MΓ : ModuleCat (X.presheaf.obj (op ⊤)))

/- Core owner recall behind the source-facing notation for Definition 17.10.6. -/
recall associatedModuleSheaf

/- Definition 17.10.6: write the `\mathcal O_X`-module associated to `M` through
`α : R → Γ(X, \mathcal O_X)` as `𝓕[α]_M`. The notation keeps the source-facing `\mathcal F_M`
surface while leaving the ambient ring map explicit when Lean cannot infer it. -/
scoped notation:max "𝓕[" α "]_" M:max => associatedModuleSheaf α M

/- Source-facing identity specialization: when `R = Γ(X, \mathcal O_X)` and `α = RingHom.id _`,
write the associated module sheaf as `𝓕_ M`, the Lean surface corresponding to the textbook
notation `\mathcal F_M`. -/
scoped notation:max "𝓕_" M:max => associatedModuleSheaf (RingHom.id _) M

/- Source-facing owner surface for Definition 17.10.6. -/
#check 𝓕[α]_M
#check 𝓕_ MΓ

/- Source-facing specialization: an `\mathcal O_X`-module `ℱ` is associated to `M` exactly when
it is isomorphic to `𝓕[α]_M`. -/
#check Nonempty (ℱ ≅ 𝓕[α]_M)
#check Nonempty (ℱ ≅ 𝓕_ MΓ)

end AlgebraicGeometry
