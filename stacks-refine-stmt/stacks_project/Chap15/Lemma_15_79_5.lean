import Mathlib
import stacks_project.Chap15.Definition_15_65_1
import stacks_project.Chap15.Definition_15_75_1
import stacks_project.Chap15.«15_60_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] (I J : Ideal R)

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for Lemma 15.79.5:
- primary domain: perfect complexes in quotient derived categories under derived scalar extension
  along compatible quotient maps `R → R ⧸ I`, `R → R ⧸ J`, and `R → R ⧸ (I * J)`;
- sampled owner declarations:
  `derivedTensorWithAlgebra`,
  `K ⊗[R]^L[(R ⧸ I)]`,
  `DerivedCategory.IsPerfect`,
  `isPerfect_of_derivedTensorWithAlgebra_quotient_isPerfect_of_isNilpotent`;
- best owner abstraction:
  the source-facing statement is the perfectness of the quotient-ring base changes
  `K ⊗[R]^L[(R ⧸ I)]`, `K ⊗[R]^L[(R ⧸ J)]`, and `K ⊗[R]^L[(R ⧸ (I * J))]`, so the public
  theorem should use the chapter's canonical owner `derivedTensorWithAlgebra` rather than the
  stronger restriction-of-scalars presentation in `D(R)`;
- primitive vs. derived:
  primitive data are the commutative ring `R`, the ideals `I`, `J`, and the object `K : D(R)`;
  the three perfectness predicates live on the already-owned quotient derived objects
  `K ⊗[R]^L[(R ⧸ I)]`, `K ⊗[R]^L[(R ⧸ J)]`, and `K ⊗[R]^L[(R ⧸ (I * J))]`, so no extra degree-zero
  quotient-module packaging belongs in the public API;
- source/core/bridge triage:
  `source-facing`: perfectness of the quotient-derived objects over `R ⧸ I` and `R ⧸ J` implies
    perfectness over `R ⧸ (I * J)`;
  `core/canonical`: `derivedTensorWithAlgebra` and `DerivedCategory.IsPerfect`;
  `bridge/view`: any later restriction-of-scalars identification back in `D(R)` is only a bridge,
    not the main statement here.
-/

-- Proof sketch: first replace `R` by `R ⧸ (I * J)` and `K` by its reduction modulo `I * J`.
-- The induced map `R ⧸ (I * J) → R ⧸ (I ⊓ J)` has square-zero kernel, so Lemma `15.79.4`
-- reduces the claim to the case `I ⊓ J = 0`. In that case, represent `K` by a K-flat complex,
-- use the short exact sequence relating reduction modulo `I`, `J`, and `I + J`, deduce bounded
-- cohomology, and then apply the compactness criterion of Proposition `15.79.3` via the five
-- lemma on direct-sum comparison maps.
/-- Lemma 15.79.5: if the quotient-derived base changes
`K \otimes_R^{\mathbf L} (R / I)` and `K \otimes_R^{\mathbf L} (R / J)` are perfect in
`D(R / I)` and `D(R / J)`, then `K \otimes_R^{\mathbf L} (R / IJ)` is perfect in
`D(R / IJ)`. -/
theorem isPerfect_derivedTensorWithAlgebra_quotient_mul_of_isPerfect_quotient_left_right
    (K : DMod)
    (hI : (K ⊗[R]^L[(R ⧸ I)]).IsPerfect)
    (hJ : (K ⊗[R]^L[(R ⧸ J)]).IsPerfect) :
    (K ⊗[R]^L[(R ⧸ (I * J))]).IsPerfect := sorry

end

end CategoryTheory
