import Mathlib.Data.Matrix.Mul
import Mathlib.RingTheory.PrincipalIdealDomain

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Domain-style sampling:
- primary domain: elementary divisor domains and Smith normal form over commutative domains;
- sampled owner declarations:
  `IsBezout`,
  `Module.Basis.SmithNormalForm`,
  `Submodule.smithNormalForm`,
  `Submodule.exists_smith_normal_form_of_rank_eq`;
- source/core/bridge triage:
  `source-facing`: the ring property that every finite matrix over `R` admits an elementary-divisor
  diagonal form;
  `core/canonical`: mathlib's Smith-normal-form owner `Module.Basis.SmithNormalForm` for
  submodules of finite free modules over a PID, together with the canonical Bézout owner
  `IsBezout`;
  `bridge/view`: the explicit matrix predicate `Matrix.HasElementaryDivisorDiagonal` and the
  rectangular diagonal matrix `Matrix.smithNormalDiagonal`, which keep the source matrix language
  without introducing a second owner abstraction.
- primitive data: only the ring-level elementary-divisor property;
- derived API: the Bézout instance and the PID-to-elementary-divisor instance.
-/

section

variable {R : Type u} [CommRing R] [IsDomain R]

/- Definition 15.125.5 (1): a Bezout domain is the canonical mathlib property `IsBezout R`,
namely that every finitely generated ideal of `R` is principal. -/
#check IsBezout

end

namespace Matrix

variable {R : Type u}

/-- The rectangular diagonal matrix with diagonal entries `d` and all other entries equal to `0`.
-/
def smithNormalDiagonal [Zero R] {n m : ℕ} (d : Fin (Nat.min n m) → R) :
    Matrix (Fin n) (Fin m) R :=
  fun i j ↦ if hij : i.1 = j.1 ∧ i.1 < Nat.min n m then d ⟨i.1, hij.2⟩ else 0

/-- A matrix admits an elementary-divisor diagonal form if left and right multiplication by
invertible matrices turns it into a rectangular diagonal matrix whose diagonal entries form a
divisibility chain. -/
def HasElementaryDivisorDiagonal [CommRing R] {n m : ℕ} (A : Matrix (Fin n) (Fin m) R) : Prop :=
  ∃ U : (Matrix (Fin n) (Fin n) R)ˣ, ∃ V : (Matrix (Fin m) (Fin m) R)ˣ,
    ∃ d : Fin (Nat.min n m) → R,
      (((U : Matrix (Fin n) (Fin n) R) * A) * (V : Matrix (Fin m) (Fin m) R)) =
        smithNormalDiagonal d ∧
      List.IsChain (· ∣ ·) (List.ofFn d)

end Matrix

section

variable {R : Type u} [CommRing R] [IsDomain R]

/-- Definition 15.125.5: an elementary divisor domain is a domain such that every finite
rectangular matrix over `R` can be diagonalized by invertible left and right multipliers, with
diagonal entries forming a divisibility chain. -/
class IsElementaryDivisorDomain (R : Type u) [CommRing R] [IsDomain R] : Prop where
  hasElementaryDivisorDiagonal {n m : ℕ} (A : Matrix (Fin n) (Fin m) R) :
    A.HasElementaryDivisorDiagonal

-- Proof sketch: apply the elementary-divisor condition to the `1 × 2` matrix `[x y]`; the single
-- diagonal entry then generates the ideal `(x, y)`, showing that every two-generated ideal is
-- principal, hence `R` is Bézout by the standard mathlib characterization.
/-- An elementary divisor domain is a Bézout domain. -/
instance isBezout_of_isElementaryDivisorDomain [IsElementaryDivisorDomain R] : IsBezout R := sorry

-- Proof sketch: over a principal ideal domain, Smith normal form supplies the required
-- diagonalization data, and its diagonal coefficients satisfy the standard divisibility chain.
/-- Every principal ideal domain is an elementary divisor domain. -/
instance isElementaryDivisorDomain_of_isPrincipalIdealRing
    [IsPrincipalIdealRing R] : IsElementaryDivisorDomain R := sorry

end
