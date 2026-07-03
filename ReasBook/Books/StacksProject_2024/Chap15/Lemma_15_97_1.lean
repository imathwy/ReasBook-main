import StacksProject_2024.Chap15.Definition_15_8_3
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.PrincipalIdeal
import Mathlib.Data.Int.Range

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped BigOperators
open scoped FittingIdeal

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "Q" => (DerivedCategory.Q : CpxA ⥤ DModA)

/- Domain-style sampling:
- primary domain: determinantal ideals of bounded finite-free cochain complexes, expressed through
  the intrinsic Fitting ideal of the degree-`i` presentation map `(f, d^i)`;
- sampled owner declarations:
  `fittingIdeal`,
  `fittingIdeal_eq_of_linearEquiv`,
  `fittingIdeal_baseChange`,
  `CochainComplex.IsTermwiseFiniteFree`,
  `CategoryTheory.IsIsomorphic`;
- best owner abstraction:
  `source-facing`: `etaDeterminantalIdeal`, the degree-`i` ideal attached to `(f, d^i)`;
  `core/canonical`: the chapter Fitting-ideal owner `fittingIdeal`;
  `bridge/view`: the specific presentation map `etaPresentationLinearMap` and its quotient
    `etaPresentationQuotient`;
- primitive data vs. derived API: the primitive data are the presentation map and its quotient.
  The alternating rank tail is derived theorem-supporting data, and the pointwise rank helper stays
  internal. -/

/-- The linear map `(f, d^i) : M^i → M^i ⊕ M^{i + 1}` used to define the determinantal ideal
attached to `M^•` and `f` in degree `i`. -/
abbrev etaPresentationLinearMap (f : A) (M : CpxA) (i : ℤ) :
    M.X i →ₗ[A] M.X i × M.X (i + 1) :=
  LinearMap.prod ((f • LinearMap.id : M.X i →ₗ[A] M.X i)) (M.d i (i + 1)).hom

/-- The quotient module presented by `(f, d^i) : M^i → M^i ⊕ M^{i + 1}`. -/
abbrev etaPresentationQuotient (f : A) (M : CpxA) (i : ℤ) :=
  (M.X i × M.X (i + 1)) ⧸ LinearMap.range (etaPresentationLinearMap f M i)

/-- The rank of the `j`th term of a termwise finite free complex, computed by `Module.finrank`. -/
private def termwiseFiniteFreeRank (M : CpxA) [CochainComplex.IsTermwiseFiniteFree M]
    (j : ℤ) : ℕ :=
  Module.finrank A (M.X j)

/-- The truncated alternating tail sum `∑_{j = i}^b (-1)^{j - i} rk(M^j)` for a termwise finite
free complex. -/
def alternatingRankTail (M : CpxA) [CochainComplex.IsTermwiseFiniteFree M] (i b : ℤ) : ℤ :=
  ((Int.range i (b + 1)).map fun j ↦
      ((-1 : ℤ) ^ Int.toNat (j - i)) * (termwiseFiniteFreeRank M j : ℤ)).sum

/-- The ideal `I_i(M^•, f)`, defined intrinsically as the Fitting ideal of the cokernel of the map
`(f, d^i) : M^i → M^i ⊕ M^{i + 1}`. -/
def etaDeterminantalIdeal (f : A) (M : CpxA) (i : ℤ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))] :
    Ideal A :=
  Fit[A]_(Module.finrank A (M.X (i + 1)))(etaPresentationQuotient f M i)

namespace EtaDeterminantalIdeal

scoped notation "I[" f "]_(" i ")(" M ")" => etaDeterminantalIdeal f M i

end EtaDeterminantalIdeal

open scoped EtaDeterminantalIdeal

local instance termwiseFiniteFreeTermModuleFree
    {M : CpxA} [hMff : CochainComplex.IsTermwiseFiniteFree M] (j : ℤ) :
    Module.Free A (M.X j) :=
  inferInstance

local instance termwiseFiniteFreeTermModuleFinite
    {M : CpxA} [hMff : CochainComplex.IsTermwiseFiniteFree M] (j : ℤ) :
    Module.Finite A (M.X j) :=
  inferInstance

-- Proof sketch: localize at each prime ideal and use Lemma `15.76.8` to replace derived-equivalent
-- bounded finite free complexes by stabilizations with finite direct sums of trivial two-term
-- complexes. The resulting determinantal ideals are compared case-by-case according to the degree
-- of the trivial summand, using the block-diagonal minors formula from Lemma `15.8.1`; this gives
-- the claimed equality after correcting by the shift in alternating tail ranks.
/-- Lemma 15.97.1: if bounded complexes `M^•` and `N^•` of finite free `A`-modules represent the
same object of `D(A)`, then the determinantal ideals `I_i(M^•, f)` and `I_i(N^•, f)` agree up to
a power of the nonzerodivisor `f`, with exponent shift measured by the alternating tail ranks. -/
theorem pow_etaDeterminantalIdeal_eq_of_same_derivedObject
    (f : A) (hf : IsRegular f) {M N : CpxA} (i : ℤ)
    [hMff : CochainComplex.IsTermwiseFiniteFree M]
    [hNff : CochainComplex.IsTermwiseFiniteFree N]
    {bM bN : ℤ} (hMle : M.IsStrictlyLE bM) (hNle : N.IsStrictlyLE bN)
    (hMN : IsIsomorphic ((Q).obj M) ((Q).obj N))
    {m n : ℕ}
    (hbalance :
      (m : ℤ) + alternatingRankTail M i bM =
        (n : ℤ) + alternatingRankTail N i bN) :
    principalIdeal (f ^ m) * I[f]_(i)(M) =
      principalIdeal (f ^ n) * I[f]_(i)(N) := sorry

end
