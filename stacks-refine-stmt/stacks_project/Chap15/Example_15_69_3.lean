import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open TrivSqZeroExt
open scoped DualNumber

section

variable (k : Type u) [CommRing k]

local notation "Rε" => DualNumber k
local notation "ModRε" => ModuleCat Rε

/- Domain-style sampling:
- primary domain: dual numbers as a trivial square-zero extension, together with the explicit
  `ε`-periodic cochain complex in `ModuleCat Rε`;
- inspected owner declarations:
  `TrivSqZeroExt.kerIdeal`,
  `Ideal.Quotient.mkₐ`,
  `Ideal.Quotient.mkₐ_eq_mk`,
  `DualNumber.eps_mul_eps`,
  `CochainComplex.of`;
- best owner abstraction:
  `source-facing`: the residue module `R / (ε)` and the explicit periodic complex
    `R --ε→ R --ε→ ⋯`;
  `core/canonical`: `TrivSqZeroExt.kerIdeal` for the ideal `(ε)` and `CochainComplex.of` for the
    complex, with `Ideal.Quotient.mkₐ` for the quotient algebra map;
  `bridge/view`: the quotient presentation of `R / (ε)` by the kernel ideal of
    `TrivSqZeroExt.fstHom`;
- primitive data: the dual-number ring `Rε` and multiplication by `ε`;
- derived API: the residue module, quotient map, periodic complex, augmentation, and the
  projective-dimension statements below. -/

/-- The residue module `R / (ε)` for the dual numbers `R`, realized via the canonical kernel ideal
of `TrivSqZeroExt.fstHom`. -/
abbrev dualNumbersResidueModule : ModRε :=
  ModuleCat.of Rε (Rε ⧸ kerIdeal k k)

/-- Multiplication by `ε` on the dual numbers, viewed as an endomorphism of the free rank-one
module `R`. -/
def dualNumbersPeriodicDifferential : ModuleCat.of Rε Rε ⟶ ModuleCat.of Rε Rε :=
  ModuleCat.ofHom (LinearMap.mulLeft Rε (ε : Rε))

-- Proof sketch: `ε` is square-zero in the trivial square-zero extension, so composing left
-- multiplication by `ε` with itself is left multiplication by `ε^2 = 0`.
/-- Left multiplication by `ε` squares to zero on the dual numbers. -/
theorem dualNumbersPeriodicDifferential_sq :
    dualNumbersPeriodicDifferential k ≫ dualNumbersPeriodicDifferential k = 0 := sorry

/-- The infinite `ε`-periodic cochain complex `R --ε→ R --ε→ R --ε→ ⋯` over the dual numbers. -/
def dualNumbersPeriodicComplex : CochainComplex ModRε ℕ :=
  CochainComplex.of
    (fun _ ↦ ModuleCat.of Rε Rε)
    (fun _ ↦ dualNumbersPeriodicDifferential k)
    (fun _ ↦ dualNumbersPeriodicDifferential_sq k)

/-- The canonical augmentation from the periodic `ε`-complex to the module `R / (ε)` concentrated
in degree `0`. -/
def dualNumbersPeriodicAugmentation :
    dualNumbersPeriodicComplex k ⟶
      (CochainComplex.single₀ ModRε).obj (dualNumbersResidueModule k) :=
  (CochainComplex.toSingle₀Equiv
      (dualNumbersPeriodicComplex k)
      (dualNumbersResidueModule k)).symm
    (ModuleCat.ofHom (Ideal.Quotient.mkₐ Rε (kerIdeal k k)).toLinearMap)

-- Proof sketch: every term of `dualNumbersPeriodicComplex` is the free rank-one module `R`, hence
-- projective in `ModuleCat R`.
/-- Each term of the periodic dual-numbers complex is projective. -/
theorem dualNumbersPeriodicComplex_projective (n : ℕ) :
    Projective ((dualNumbersPeriodicComplex k).X n) := sorry

-- Proof sketch: identify the degree-zero homology of the periodic `ε`-complex with `R / (ε)` and
-- check that the higher homology vanishes because consecutive differentials are both multiplication
-- by the square-zero element `ε`.
/-- Example 15.69.3: for the dual numbers `R = k[ε]/(ε^2)` over a commutative ring `k` and
`M = R / (ε)`, the canonical
augmentation from the infinite `ε`-periodic cochain complex `R --ε→ R --ε→ R --ε→ ⋯` to the
degree-zero complex `M[0]` is a quasi-isomorphism. Lean uses the canonical owner
`DualNumber k` for `R`, definitionally `TrivSqZeroExt k k`. -/
theorem dualNumbersResidueModule_quasiIso_periodicComplex :
    QuasiIso (dualNumbersPeriodicAugmentation k) := sorry

end

section

variable (k : Type u) [CommRing k] [Nontrivial k]

-- Proof sketch: if `R / (ε)` had finite projective dimension, some finite truncation of the
-- periodic projective resolution would force a projective syzygy. For the dual numbers this never
-- happens, because every syzygy is again isomorphic to `R / (ε)`.
/-- Over a nontrivial commutative ring, the residue module over the dual numbers does not have
finite projective dimension. -/
theorem dualNumbersResidueModule_projectiveDimension_eq_top :
    projectiveDimension (dualNumbersResidueModule k) = ⊤ := sorry

end
