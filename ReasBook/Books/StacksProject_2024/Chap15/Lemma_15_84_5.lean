import Mathlib
import stacks_project.Chap15.«15_60_1_1»
import stacks_project.Chap15.Definition_15_84_1

noncomputable section

open CategoryTheory
open scoped TensorProduct DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace CategoryTheory

section

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']

local notation "Aprime" => A ⊗[R] R'
local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.84.5:
- primary domain: base change for relative perfect objects in derived categories of module
  categories;
- sampled owner declarations:
  `DerivedCategory.IsPerfectOver`,
  `derivedTensorWithAlgebra_isPseudoCoherent`,
  `derivedTensorBaseChangeIso`,
  `hasTorAmplitudeIn_derivedTensorWithAlgebra`;
- best owner abstraction: this theorem is `source-facing` on the chapter owner
  `DerivedCategory.IsPerfectOver`, while the core/canonical owners are the derived scalar
  extension `K ⊗[A]^L[Aprime]`, the canonical base-change comparison `derivedTensorBaseChangeIso`,
  and the tor-amplitude base-change theorem;
- primitive vs. derived:
  primitive data are the algebra maps `R → A` and `R → R'`, the base change ring
  `Aprime = A ⊗[R] R'`, and the hypothesis that `K` is perfect over `R`;
  the base-changed object `K ⊗[A]^L[Aprime]` and its relative-perfectness conclusion are derived
  API over those owners;
- source/core/bridge triage:
  `source-facing`: preservation of `DerivedCategory.IsPerfectOver` under base change in the base
    ring;
  `core/canonical`: `DerivedCategory.IsPerfectOver`, `derivedTensorWithAlgebra`,
    `derivedTensorBaseChangeIso`, and `HasFiniteTorDimension`;
  `bridge/view`: the notation `K ⊗[A]^L[Aprime]` for the scalar-extension owner applied to `K`. -/

-- Proof sketch: use Lemma `15.82.12` to preserve pseudo-coherence relative to the base under the
-- derived scalar extension `A → Aprime`. Then identify the restricted derived base change with
-- `K ⊗_R^L R'` using Lemma `15.61.2`, and apply Lemma `15.67.13` together with finite tor
-- dimension over `R` to conclude finite tor dimension over `R'`. The source phrases this lemma
-- under additional flatness and finite-presentation assumptions on `R → A`, but those hypotheses
-- are redundant for the canonical owner decomposition used here.
/-- Lemma 15.84.5: let `R → A` and `R → R'` be ring maps, and set `A' = A ⊗[R] R'`. If an object
of `D(A)` is perfect relative to `R`, then its derived base change to `A'` is perfect relative
to `R'`. The flatness and finite-presentation assumptions on `R → A` appearing in the source are
redundant for this conclusion. -/
theorem derivedTensorWithAlgebra_isPerfectOver_of_baseChange
    {K : DModA}
    (hK : DerivedCategory.IsPerfectOver R K) :
    DerivedCategory.IsPerfectOver R' (K ⊗[A]^L[Aprime]) :=
  sorry

end

end CategoryTheory
