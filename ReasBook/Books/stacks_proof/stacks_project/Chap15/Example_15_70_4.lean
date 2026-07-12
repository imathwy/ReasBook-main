import Mathlib
import StacksProject_2024.Chap15.Example_15_69_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CochainComplex.HomComplex.Cocycle
open TrivSqZeroExt
open scoped DualNumber

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable (k : Type u) [CommRing k]

local notation "Rε" => DualNumber k
local notation "ModRε" => ModuleCat Rε

/-- The bi-infinite `ε`-periodic cochain complex `⋯ ⟶ R ⟶ R ⟶ R ⟶ ⋯` over the dual numbers,
with every differential given by multiplication by `ε`. -/
def dualNumbersBiInfinitePeriodicComplex : CochainComplex ModRε ℤ :=
  CochainComplex.of
    (fun _ : ℤ ↦ ModuleCat.of Rε Rε)
    (fun _ : ℤ ↦ dualNumbersPeriodicDifferential k)
    (fun _ : ℤ ↦ dualNumbersPeriodicDifferential_sq k)

-- Proof sketch: `dualNumbersBiInfinitePeriodicComplex` is defined using `CochainComplex.of` with
-- the same differential in every degree, so the degree-`n` differential is definitionally left
-- multiplication by `ε`.
/-- Every differential in the bi-infinite dual-numbers complex is multiplication by `ε`. -/
theorem dualNumbersBiInfinitePeriodicComplex_d (n : ℤ) :
    (dualNumbersBiInfinitePeriodicComplex k).d n (n + 1) =
      dualNumbersPeriodicDifferential k := sorry

end

section

variable (k : Type u) [CommRing k]

local notation "Rε" => DualNumber k
local notation "ModRε" => ModuleCat Rε
local notation "single0" => DerivedCategory.singleFunctor ModRε (0 : ℤ)

/- Domain-style sampling:
- primary domain: explicit cochain-complex representatives of degree-zero modules in
  `DerivedCategory (ModuleCat Rε)`;
- inspected owner declarations: `Ideal.Quotient.mkₐ`,
  `CochainComplex.HomComplex.Cocycle.toSingleMk`, `DerivedCategory.Q`,
  `DerivedCategory.singleFunctor`, and `DerivedCategory.singleFunctorIsoCompQ`;
- best owner abstraction: the source-facing owner here is the concrete complex
  `dualNumbersBiInfinitePeriodicComplex k`, not an existential wrapper around it;
- source/core/bridge triage: `dualNumbersBiInfinitePeriodicAugmentation` is the
  `source-facing` map, `DerivedCategory.Q` together with `single0` is the
  `core/canonical` owner layer, and termwise injectivity is a separate `bridge/view` property;
- primitive data: the explicit augmentation
  `dualNumbersBiInfinitePeriodicAugmentation k :
    dualNumbersBiInfinitePeriodicComplex k ⟶
      (CochainComplex.singleFunctor ModRε (0 : ℤ)).obj (dualNumbersResidueModule k)`;
- derived API: the induced isomorphism
  `DerivedCategory.Q.obj (dualNumbersBiInfinitePeriodicComplex k) ≅
    (single0).obj (dualNumbersResidueModule k)`;
  the extra field hypothesis belongs only to the separate termwise-injectivity theorem below. -/

-- Proof sketch: as for the one-sided periodic complex, a cochain map to the degree-zero complex
-- is determined by its degree-zero component, here the quotient map `Rε → Rε/(ε)`.
/-- The canonical augmentation from the bi-infinite dual-numbers periodic complex to the residue
module in degree `0`. -/
def dualNumbersBiInfinitePeriodicAugmentation :
    dualNumbersBiInfinitePeriodicComplex k ⟶
      (CochainComplex.singleFunctor ModRε (0 : ℤ)).obj (dualNumbersResidueModule k) :=
  let π : (dualNumbersBiInfinitePeriodicComplex k).X 0 ⟶ dualNumbersResidueModule k :=
    ModuleCat.ofHom (Ideal.Quotient.mkₐ Rε (kerIdeal k k)).toLinearMap
  (toSingleMk π (by simp) (-1) (by simp) (by
      have hd :
          (dualNumbersBiInfinitePeriodicComplex k).d (-1) 0 =
            dualNumbersPeriodicDifferential k := by
        simpa using dualNumbersBiInfinitePeriodicComplex_d k (-1)
      rw [hd]
      apply ModuleCat.hom_ext
      ext
      change (Ideal.Quotient.mk (kerIdeal k k))
          ((LinearMap.mulLeft Rε (ε : Rε)) 1) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      rw [mem_kerIdeal_iff_inr]
      ext <;> simp [LinearMap.mulLeft_apply])).homOf

-- Proof sketch: compute cohomology exactly as for the one-sided periodic resolution; the
-- bi-infinite complex is exact away from degree `0`, and its degree-zero cohomology is
-- `Rε / (ε)`.
/-- The canonical augmentation from the bi-infinite periodic dual-numbers complex to the residue
module in degree `0` is a quasi-isomorphism. -/
theorem dualNumbersBiInfinitePeriodicAugmentation_quasiIso :
    QuasiIso (dualNumbersBiInfinitePeriodicAugmentation k) := sorry

-- Proof sketch: use the standard two-sided periodic injective resolution of `R / (ε)` over the
-- dual numbers. The complex is exact away from degree `0`, and its degree-`0` cohomology is the
-- quotient by `(ε)`.
/-- Example 15.70.4: for the dual numbers `R = k[ε]/(ε^2)` over a commutative ring `k` and
`M = R / (ε)`, the explicit bi-infinite periodic complex `⋯ ⟶ R ⟶ R ⟶ R ⟶ ⋯` with differential
given by multiplication by `ε` represents `M[0]` in `D(R)`. Over a field, the separate theorem
`dualNumbersBiInfinitePeriodicComplex_term_injective` upgrades this representative to an injective
one. Lean reuses the canonical chapter owner `DualNumber k`, definitionally `TrivSqZeroExt k k`.
-/
@[stacks 0A5U]
noncomputable def dualNumbersBiInfinitePeriodicComplex_iso_single0ResidueModule :
    DerivedCategory.Q.obj (dualNumbersBiInfinitePeriodicComplex k) ≅
      (single0).obj (dualNumbersResidueModule k) :=
  letI : QuasiIso (dualNumbersBiInfinitePeriodicAugmentation k) :=
    dualNumbersBiInfinitePeriodicAugmentation_quasiIso k
  asIso (DerivedCategory.Q.map (dualNumbersBiInfinitePeriodicAugmentation k)) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ ModRε (0 : ℤ)).app
      (dualNumbersResidueModule k)).symm

end

section

variable (k : Type u) [Field k]

local notation "Rε" => DualNumber k

-- Proof sketch: the dual numbers `k[ε]/(ε^2)` form a self-injective Frobenius algebra over the
-- field `k`, so the regular module is injective.
/-- The dual numbers over a field are injective as a module over themselves. -/
theorem dualNumbers_self_injective :
    Module.Injective Rε Rε := sorry

-- Proof sketch: every term of `dualNumbersBiInfinitePeriodicComplex` is the regular module `R`,
-- and `dualNumbers_self_injective` identifies that regular module as injective; translate to
-- `ModuleCat` using `Module.injective_iff_injective_object`.
/-- Every term of the bi-infinite dual-numbers periodic complex is injective. -/
theorem dualNumbersBiInfinitePeriodicComplex_term_injective (n : ℤ) :
    Injective ((dualNumbersBiInfinitePeriodicComplex k).X n) := sorry

end
