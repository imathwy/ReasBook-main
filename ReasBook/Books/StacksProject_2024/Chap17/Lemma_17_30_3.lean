import Mathlib
import StacksProject_2024.Chap17.Definition_17_29_1
import StacksProject_2024.Chap17.Definition_17_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open TopCat.Sheaf

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable {O₁ O₂ : TopCat.Sheaf CommRingCat.{u} X}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]

/- Domain-style sampling for Lemma 17.30.3:
- primary domain: relative de Rham differentials for a morphism of sheaves of rings on a fixed
  topological space;
- sampled owner declarations:
  `TopCat.Sheaf.deRhamComplex`,
  `TopCat.Sheaf.IsDifferentialOperatorOfOrder`,
  `de_rham_differentials_are_order_one_differential_operators`;
- best owner abstraction: the canonical degree-`p` differential
  `(deRhamComplex φ).d p (p + 1)` in the source-facing owner `TopCat.Sheaf.deRhamComplex φ`;
- primitive data: only the morphism `φ : O₁ ⟶ O₂` and the degree `p`;
- derived API: the order-one differential-operator property of that canonical differential.

Source/core/bridge triage:
- `source-facing`: the order-one statement for the actual de Rham differential
  `d : \Omega^p_{O₂/O₁} \to \Omega^{p + 1}_{O₂/O₁}`;
- `core/canonical`: `TopCat.Sheaf.deRhamComplex φ` together with
  `TopCat.Sheaf.IsDifferentialOperatorOfOrder`;
- `bridge/view`: evaluation on opens inside the ringed-site owner. -/

/-- Lemma 17.30.3: for a morphism of sheaves of rings `φ : O₁ ⟶ O₂`, each differential
`d : \Omega^p_{O₂/O₁} \to \Omega^{p + 1}_{O₂/O₁}` in the canonical de Rham complex is a
differential operator of order `1` relative to `φ`. -/
-- Proof sketch: evaluate the canonical de Rham differential on each open set, identify it with
-- the sectionwise algebraic de Rham differential, and apply the algebraic order-one result of
-- Lemma `10.133.10`.
theorem deRhamDifferential_isDifferentialOperatorOfOrder
    (φ : O₁ ⟶ O₂) (p : ℕ) :
    IsDifferentialOperatorOfOrder φ ((deRhamComplex φ).d p (p + 1)) 1 := by
  sorry

end TopCat.Sheaf
