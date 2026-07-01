import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import stacks_project.Chap13.Lemma_13_11_6
import stacks_project.Chap15.Definition_15_65_1
import stacks_project.Chap15.Definition_15_59_13
import stacks_project.Chap15.Definition_15_89_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] (I : Ideal R)

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "DbMod" => boundedDerivedCategory (ModuleCat R)
local notation "Hb" => boundedDerivedHomologyFunctor (ModuleCat R)
local notation "RmodI" =>
  ModuleCat.single0Functor.obj (ModuleCat.of R (R ⧸ I))

/- Domain-style sampling for derived tensor bounds with ideal-power torsion coefficients:
- primary domain: canonical t-structure bounds `DerivedCategory.IsLE 0` on derived tensor
  products in `D(R)`;
- same-domain declarations inspected:
  `DerivedCategory.IsLE`,
  `boundedDerivedHomologyFunctor`,
  `ModuleCat.single0Functor`,
  `DerivedCategory.isLE_iff`,
  `Module.IsIdealPowerTorsion`;
- best owner abstraction: the bound `(K ⊗[R]^L M).IsLE 0` in the canonical derived-category
  t-structure;
- primitive data: the bounded object `M`, the source-facing nonpositive bound `M.obj.IsLE 0`,
  and the torsion hypotheses on the genuinely possibly nonzero cohomology objects `H^i(M)` for
  `i ≤ 0`;
- derived API: vanishing of the positive cohomology objects of `M` is already supplied by
  `DerivedCategory.isLE_iff` / `DerivedCategory.isZero_of_isLE`, so torsion in positive degrees
  is redundant and should not remain primitive input.

Layer triage:
- `source-facing`: the tensor-vanishing statement for bounded complexes with ideal-power torsion
  cohomology;
- `core/canonical`: the owner predicate `DerivedCategory.IsLE 0` on the derived tensor product;
- `bridge/view`: `ModuleCat.single0Functor` for modules concentrated in degree `0` and
  `boundedDerivedHomologyFunctor` for the cohomology objects of `M`.

Within this file, the quotient clause `(1)` is derived API: after identifying `R ⧸ I^n` as an
`I`-power torsion module through `Module.isIdealPowerTorsion_quotient_pow`, it is a specialization
of the module clause `(2)` rather than a second primitive owner.
-/

-- Proof sketch: write an `I`-power torsion module `N` as the filtered colimit of its submodules
-- annihilated by powers of `I`, reduce to the case where some `I^n` kills `N`, and then apply
-- the quotient case `R ⧸ I^n` after passing to the square-zero extension `R ⧸ I^n ⊕ N` as in the
-- textbook proof.
/-- Lemma 15.89.7 (2): if `K ⊗_R^{\mathbf L} (R ⧸ I)[0]` has no positive cohomology, then
`K ⊗_R^{\mathbf L} N[0]` has no positive cohomology for every `I`-power torsion `R`-module
`N`. -/
theorem derivedTensorProduct_idealPowerTorsionModule_isLE_zero_of_modIdeal
    (K : DMod)
    (hKI : (K ⊗[R]^L RmodI).IsLE 0)
    (N : ModuleCat R) (hN : Module.IsIdealPowerTorsion I N) :
    (K ⊗[R]^L ModuleCat.single0Functor.obj N).IsLE 0 := sorry

-- Proof sketch: this is the module case `(2)` specialized to the `I`-power torsion module
-- `R ⧸ I^n`, using `Module.isIdealPowerTorsion_quotient_pow`.
/-- Lemma 15.89.7 (1): if `K ⊗_R^{\mathbf L} (R ⧸ I)[0]` has no positive cohomology, then
`K ⊗_R^{\mathbf L} (R ⧸ I^n)[0]` has no positive cohomology for every positive `n`. -/
theorem derivedTensorProduct_idealPowQuotient_isLE_zero_of_modIdeal
    (K : DMod)
    (hKI : (K ⊗[R]^L RmodI).IsLE 0)
    (n : ℕ+) :
    (K ⊗[R]^L ModuleCat.single0Functor.obj (ModuleCat.of R (R ⧸ I ^ (n : ℕ)))).IsLE 0 := by
  simpa using
    derivedTensorProduct_idealPowerTorsionModule_isLE_zero_of_modIdeal
      I K hKI (ModuleCat.of R (R ⧸ I ^ (n : ℕ)))
      (Module.isIdealPowerTorsion_quotient_pow I (n : ℕ))

-- Proof sketch: use part `(2)` for each possibly nonzero cohomology object `H^i(M)` with `i ≤ 0`,
-- since `hMle` already forces `H^i(M) = 0` for `i > 0`; then induct on the number of nonzero
-- cohomology objects of the bounded complex `M` via the truncation distinguished triangles from
-- Remark `13.12.4`.
/-- Lemma 15.89.7 (3): if `M` is a bounded derived `R`-complex whose nonpositive cohomology
modules are `I`-power torsion and which has no positive cohomology, then
`K ⊗_R^{\mathbf L} M` has no positive cohomology whenever
`K ⊗_R^{\mathbf L} (R ⧸ I)[0]` has none. -/
theorem derivedTensorProduct_boundedIdealPowerTorsion_isLE_zero_of_modIdeal
    (K : DMod)
    (hKI : (K ⊗[R]^L RmodI).IsLE 0)
    (M : DbMod)
    (hMtors : ∀ i ≤ 0, Module.IsIdealPowerTorsion I ((Hb i).obj M))
    (hMle : M.obj.IsLE 0) :
    (K ⊗[R]^L M.obj).IsLE 0 := sorry

end

end CategoryTheory
