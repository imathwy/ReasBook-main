import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.PNat.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators DirectSum

universe u v

/- 
Source/core/bridge triage:
- `source-facing`: the bundled graded `R`-algebra from Definition 23.6.1, together with the
  parity-split surface on `A_even`, `A_odd`, and `A_even₊` used by the divided-power axioms.
- `core/canonical`: the graded-algebra core on the homogeneous pieces is still the standard
  `DirectSum.GSemiring` / `DirectSum.GAlgebra` package.
- `bridge/view`: the even and odd homogeneous inclusions stay the canonical direct-sum maps, while
  the positive even part and its parity operations are exposed as companion data for later reuse.
-/

/-- Definition 23.6.1. A strictly graded-commutative graded `R`-algebra. The parity-split
surface on `A_even`, `A_odd`, and `A_even₊` is recovered canonically from the underlying
graded multiplication. -/
@[stacks 09PG]
structure ParitySplitGradedAlgebra (R : Type u) [CommRing R] where
  /-- The family of homogeneous pieces. -/
  piece : ℕ → Type v
  /-- Additive structure on each homogeneous piece. -/
  [pieceAddCommMonoid : ∀ n : ℕ, AddCommMonoid (piece n)]
  /-- Scalar multiplication on each homogeneous piece. -/
  [pieceModule : ∀ n : ℕ, Module R (piece n)]
  /-- The canonical graded multiplication on the family of pieces. -/
  [pieceGSemiring : DirectSum.GSemiring piece]
  /-- The canonical graded `R`-algebra structure on the family of pieces. -/
  [pieceGAlgebra : DirectSum.GAlgebra R piece]
  /-- Homogeneous multiplication is graded commutative with the Koszul sign. -/
  graded_comm (p q : ℕ) (x : piece p) (y : piece q) :
      cast (congrArg piece (Nat.add_comm p q)) (GradedMonoid.GMul.mul x y) =
        ((-1 : R) ^ (p * q)) • GradedMonoid.GMul.mul y x
  /-- Every odd homogeneous element squares to zero. -/
  sq_eq_zero_of_odd (p : ℕ) (hp : Odd p) (x : piece p) :
      GradedMonoid.GMul.mul x x = 0

attribute [instance] ParitySplitGradedAlgebra.pieceAddCommMonoid
attribute [instance] ParitySplitGradedAlgebra.pieceModule
attribute [instance] ParitySplitGradedAlgebra.pieceGSemiring
attribute [instance] ParitySplitGradedAlgebra.pieceGAlgebra

namespace ParitySplitGradedAlgebra

variable {R : Type u} [CommRing R]
variable (A : ParitySplitGradedAlgebra R)

/-- The full even family of homogeneous pieces. -/
abbrev evenFamily : ℕ → Type v :=
  fun d ↦ A.piece (2 * d)

/-- The odd family of homogeneous pieces. -/
abbrev oddFamily : ℕ → Type v :=
  fun d ↦ A.piece (2 * d + 1)

/-- The full even part `A_even`. -/
abbrev evenPart : Type v :=
  ⨁ d : ℕ, A.piece (2 * d)

/-- The odd part `A_odd`. -/
abbrev oddPart : Type v :=
  ⨁ d : ℕ, A.piece (2 * d + 1)

/-- The positive even part `A_even₊`. -/
abbrev evenPositivePart : Type v :=
  ⨁ d : ℕ, A.piece (2 * (d + 1))

notation:max A "ₑᵥₑₙ" => ParitySplitGradedAlgebra.evenPart A
notation:max A "ₒdd" => ParitySplitGradedAlgebra.oddPart A
notation:max A "ₑᵥₑₙ₊" => ParitySplitGradedAlgebra.evenPositivePart A

instance evenFamilyAddCommMonoid (d : ℕ) : AddCommMonoid (A.evenFamily d) := by
  dsimp [evenFamily]
  infer_instance

instance evenFamilyModule (d : ℕ) : Module R (A.evenFamily d) := by
  exact A.pieceModule (2 * d)

instance oddFamilyAddCommMonoid (d : ℕ) : AddCommMonoid (A.oddFamily d) := by
  dsimp [oddFamily]
  infer_instance

instance oddFamilyModule (d : ℕ) : Module R (A.oddFamily d) := by
  exact A.pieceModule (2 * d + 1)

instance evenPartAddCommMonoid : AddCommMonoid A.evenPart := by
  exact instAddCommMonoidDirectSum ℕ (fun d ↦ A.piece (2 * d))

instance evenPartModule : Module R A.evenPart := by
  exact DirectSum.instModule

instance oddPartAddCommMonoid : AddCommMonoid A.oddPart := by
  exact instAddCommMonoidDirectSum ℕ (fun d ↦ A.piece (2 * d + 1))

instance oddPartModule : Module R A.oddPart := by
  exact DirectSum.instModule

instance evenPositivePartAddCommMonoid : AddCommMonoid A.evenPositivePart := by
  exact instAddCommMonoidDirectSum ℕ (fun d ↦ A.piece (2 * (d + 1)))

instance evenPositivePartModule : Module R A.evenPositivePart := by
  exact DirectSum.instModule

/-- Reindexing a homogeneous piece along an equality of degrees. -/
def pieceCast {m n : ℕ} (h : m = n) : A.piece m →ₗ[R] A.piece n where
  toFun x := cast (congrArg A.piece h) x
  map_add' := by
    intro x y
    subst h
    rfl
  map_smul' := by
    intro r x
    subst h
    rfl

/-- The homogeneous degree-`2d` piece inside the even part. -/
abbrev evenHom (d : ℕ) : A.piece (2 * d) →ₗ[R] A.evenPart :=
  DirectSum.lof R ℕ (fun e ↦ A.piece (2 * e)) d

/-- The homogeneous degree-`2(d + 1)` piece inside `A_even₊`. -/
abbrev evenPositiveHom (d : ℕ) : A.piece (2 * (d + 1)) →ₗ[R] A.evenPositivePart :=
  DirectSum.lof R ℕ (fun e ↦ A.piece (2 * (e + 1))) d

/-- The canonical inclusion `A_even₊ ⟶ A_even`. -/
def evenPositiveToEven : A.evenPositivePart →ₗ[R] A.evenPart :=
  DirectSum.toModule R ℕ A.evenPart fun d ↦
    A.evenHom (d + 1)

/-- On each homogeneous positive-even summand, `A_even₊ → A_even` is the canonical inclusion. -/
@[simp] theorem evenPositiveToEven_evenPositiveHom (d : ℕ) (x : A.piece (2 * (d + 1))) :
    A.evenPositiveToEven (A.evenPositiveHom d x) = A.evenHom (d + 1) x := by
  change
    (DirectSum.toModule R ℕ A.evenPart fun e ↦ A.evenHom (e + 1))
      ((DirectSum.lof R ℕ (fun e ↦ A.piece (2 * (e + 1))) d) x) =
        A.evenHom (d + 1) x
  rw [DirectSum.toModule_lof]

/-- The submodule of `A_even` generated by the positive even summands. -/
def evenPositiveSubmodule : Submodule R A.evenPart :=
  LinearMap.range A.evenPositiveToEven

/-- Every homogeneous piece of positive even degree lies in `A_even₊`. -/
theorem evenHom_mem_evenPositiveSubmodule (d : ℕ) (x : A.piece (2 * (d + 1))) :
    A.evenHom (d + 1) x ∈ A.evenPositiveSubmodule :=
  ⟨A.evenPositiveHom d x, by
    simpa using A.evenPositiveToEven_evenPositiveHom d x⟩

/-- The homogeneous degree-`2d + 1` piece inside the odd part. -/
abbrev oddHom (d : ℕ) : A.piece (2 * d + 1) →ₗ[R] A.oddPart :=
  DirectSum.lof R ℕ (fun e ↦ A.piece (2 * e + 1)) d

/-- The projection of `A_even` onto the direct sum of positive even pieces, discarding degree
zero. -/
def evenToEvenPositive : A.evenPart →ₗ[R] A.evenPositivePart :=
  DirectSum.toModule R ℕ A.evenPositivePart fun
    | 0 => 0
    | d + 1 => A.evenPositiveHom d

@[simp] theorem evenToEvenPositive_evenHom_zero (x : A.piece 0) :
    A.evenToEvenPositive (A.evenHom 0 x) = 0 := by
  change
    (DirectSum.toModule R ℕ A.evenPositivePart fun
      | 0 => 0
      | d + 1 => A.evenPositiveHom d)
      ((DirectSum.lof R ℕ (fun e ↦ A.piece (2 * e)) 0) x) = 0
  rw [DirectSum.toModule_lof]
  simp

@[simp] theorem evenToEvenPositive_evenHom_succ (d : ℕ) (x : A.piece (2 * (d + 1))) :
    A.evenToEvenPositive (A.evenHom (d + 1) x) = A.evenPositiveHom d x := by
  change
    (DirectSum.toModule R ℕ A.evenPositivePart fun
      | 0 => 0
      | e + 1 => A.evenPositiveHom e)
      ((DirectSum.lof R ℕ (fun e ↦ A.piece (2 * e)) (d + 1)) x) = A.evenPositiveHom d x
  rw [DirectSum.toModule_lof]

@[simp] theorem evenToEvenPositive_evenPositiveToEven (x : A.evenPositivePart) :
    A.evenToEvenPositive (A.evenPositiveToEven x) = x := by
  refine DirectSum.induction_on x ?_ ?_ ?_
  · rfl
  · intro d x
    have hinclude :
        A.evenPositiveToEven ((DirectSum.of (fun i ↦ A.piece (2 * (i + 1))) d) x) =
          A.evenHom (d + 1) x := by
      change A.evenPositiveToEven (A.evenPositiveHom d x) = A.evenHom (d + 1) x
      exact A.evenPositiveToEven_evenPositiveHom d x
    calc
      A.evenToEvenPositive (A.evenPositiveToEven ((DirectSum.of (fun i ↦ A.piece (2 * (i + 1))) d) x))
          = A.evenToEvenPositive (A.evenHom (d + 1) x) := by
              rw [hinclude]
      _ = A.evenPositiveHom d x :=
            A.evenToEvenPositive_evenHom_succ d x
      _ = (DirectSum.of (fun i ↦ A.piece (2 * (i + 1))) d) x := by
            rfl
  · intro x y hx hy
    calc
      A.evenToEvenPositive (A.evenPositiveToEven (x + y))
          = A.evenToEvenPositive (A.evenPositiveToEven x + A.evenPositiveToEven y) := by
              rw [A.evenPositiveToEven.map_add]
      _ = A.evenToEvenPositive (A.evenPositiveToEven x)
            + A.evenToEvenPositive (A.evenPositiveToEven y) := by
              rw [A.evenToEvenPositive.map_add]
      _ = x + y := by rw [hx, hy]

theorem evenPositiveToEven_injective : Function.Injective A.evenPositiveToEven := by
  intro x y hxy
  simpa using congrArg A.evenToEvenPositive hxy

/-- The canonical homogeneous contribution to multiplication on `A_even`. -/
private def evenMulTermMap (i j : ℕ) :
    A.piece (2 * i) →ₗ[R] A.piece (2 * j) →ₗ[R] A.evenPart :=
  (DirectSum.gMulLHom R A.piece).compr₂ <|
    (A.evenHom (i + j)).comp <|
      A.pieceCast (by simp [two_mul, Nat.add_left_comm, Nat.add_comm])

/-- The canonical homogeneous contribution to multiplication on `A_even`. -/
def evenMulTerm (i j : ℕ) (x : A.piece (2 * i)) (y : A.piece (2 * j)) : A.evenPart :=
  A.evenMulTermMap i j x y

/-- The canonical homogeneous contribution of `A_even × A_even₊` to `A_even₊`. -/
private def evenMulPositiveTermMap (i j : ℕ) :
    A.piece (2 * i) →ₗ[R] A.piece (2 * (j + 1)) →ₗ[R] A.evenPositivePart :=
  (DirectSum.gMulLHom R A.piece).compr₂ <|
    (A.evenPositiveHom (i + j)).comp <|
      A.pieceCast (by simp [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm])

/-- The canonical homogeneous contribution of `A_even × A_even₊` to `A_even₊`. -/
def evenMulPositiveTerm (i j : ℕ) (x : A.piece (2 * i)) (y : A.piece (2 * (j + 1))) :
    A.evenPositivePart :=
  A.evenMulPositiveTermMap i j x y

/-- The canonical homogeneous contribution of `A_odd × A_odd` to `A_even₊`. -/
private def oddMulTermMap (i j : ℕ) :
    A.piece (2 * i + 1) →ₗ[R] A.piece (2 * j + 1) →ₗ[R] A.evenPositivePart :=
  (DirectSum.gMulLHom R A.piece).compr₂ <|
    (A.evenPositiveHom (i + j)).comp <|
      A.pieceCast (by simp [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm])

/-- The canonical homogeneous contribution of `A_odd × A_odd` to `A_even₊`. -/
def oddMulTerm (i j : ℕ) (x : A.piece (2 * i + 1)) (y : A.piece (2 * j + 1)) :
    A.evenPositivePart :=
  A.oddMulTermMap i j x y

/-- The canonical homogeneous contribution of `A_even × A_odd` to `A_odd`. -/
private def evenMulOddTermMap (i j : ℕ) :
    A.piece (2 * i) →ₗ[R] A.piece (2 * j + 1) →ₗ[R] A.oddPart :=
  (DirectSum.gMulLHom R A.piece).compr₂ <|
    (A.oddHom (i + j)).comp <|
      A.pieceCast (by simp [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm])

/-- The canonical homogeneous contribution of `A_even × A_odd` to `A_odd`. -/
def evenMulOddTerm (i j : ℕ) (x : A.piece (2 * i)) (y : A.piece (2 * j + 1)) :
    A.oddPart :=
  A.evenMulOddTermMap i j x y

/-- Multiplication on the even part, obtained canonically from the homogeneous multiplication. -/
def evenMul : A ₑᵥₑₙ →ₗ[R] A ₑᵥₑₙ →ₗ[R] A ₑᵥₑₙ :=
  DirectSum.toModule R ℕ (A ₑᵥₑₙ →ₗ[R] A ₑᵥₑₙ) fun i ↦
    (DirectSum.toModule R ℕ (A.piece (2 * i) →ₗ[R] A ₑᵥₑₙ) fun j ↦
      (A.evenMulTermMap i j).flip).flip

/-- The canonical direct-sum multiplication `A_even × ⨁_{d > 0} A_{2d} → ⨁_{d > 0} A_{2d}`. -/
def evenMulPositiveDirect : A ₑᵥₑₙ →ₗ[R] A ₑᵥₑₙ₊ →ₗ[R] A ₑᵥₑₙ₊ :=
  DirectSum.toModule R ℕ (A ₑᵥₑₙ₊ →ₗ[R] A ₑᵥₑₙ₊) fun i ↦
    (DirectSum.toModule R ℕ (A.piece (2 * i) →ₗ[R] A ₑᵥₑₙ₊) fun j ↦
      (A.evenMulPositiveTermMap i j).flip).flip

/-- The canonical direct-sum multiplication `A_even × A_odd → A_odd`. -/
def evenMulOddDirect : A ₑᵥₑₙ →ₗ[R] A ₒdd →ₗ[R] A ₒdd :=
  DirectSum.toModule R ℕ (A ₒdd →ₗ[R] A ₒdd) fun i ↦
    (DirectSum.toModule R ℕ (A.piece (2 * i) →ₗ[R] A ₒdd) fun j ↦
      (A.evenMulOddTermMap i j).flip).flip

/-- The canonical direct-sum multiplication `A_odd × A_odd → ⨁_{d > 0} A_{2d}`. -/
def oddMulDirect : A ₒdd →ₗ[R] A ₒdd →ₗ[R] A ₑᵥₑₙ₊ :=
  DirectSum.toModule R ℕ (A ₒdd →ₗ[R] A ₑᵥₑₙ₊) fun i ↦
    (DirectSum.toModule R ℕ (A.piece (2 * i + 1) →ₗ[R] A ₑᵥₑₙ₊) fun j ↦
      (A.oddMulTermMap i j).flip).flip

/-- Multiplication of an even element with a positive even element, landing canonically in
`A_even₊`. -/
def evenMulPositive (x : A ₑᵥₑₙ) (y : A ₑᵥₑₙ₊) : A ₑᵥₑₙ₊ :=
  A.evenMulPositiveDirect x y

/-- Multiplication of an even element with an odd element, landing canonically in `A_odd`. -/
def evenMulOdd (x : A ₑᵥₑₙ) (y : A ₒdd) : A ₒdd :=
  A.evenMulOddDirect x y

/-- Multiplication of two odd elements, landing canonically in `A_even₊`. -/
def oddMul (x y : A ₒdd) : A ₑᵥₑₙ₊ :=
  A.oddMulDirect x y

@[simp] theorem evenMulOdd_zero (x : A ₑᵥₑₙ) :
    A.evenMulOdd x 0 = 0 := by
  simp [evenMulOdd]

/-- The unit in `A_even` is the degree-zero unit of the graded algebra. -/
abbrev oneEven : A.evenPart :=
  A.evenHom 0 <| cast (by simp) (show A.piece 0 from GradedMonoid.GOne.one)

/-- The power operation on the even part. -/
def evenPow : A.evenPart → ℕ → A.evenPart
  | _, 0 => A.oneEven
  | x, n + 1 => A.evenMul (evenPow x n) x

@[simp] theorem evenPow_zero (x : A.evenPart) :
    A.evenPow x 0 = A.oneEven :=
  rfl

@[simp] theorem evenPow_succ (x : A.evenPart) (n : ℕ) :
    A.evenPow x (n + 1) = A.evenMul (A.evenPow x n) x :=
  rfl

end ParitySplitGradedAlgebra

/-- A divided power structure on the positive even part of a parity-split graded algebra. -/
structure DividedPowerStructure (R : Type u) [CommRing R] (A : ParitySplitGradedAlgebra R) where
  /-- The total family `γ_n : Aₑᵥₑₙ₊ → Aₑᵥₑₙ`. -/
  gamma : ℕ → A ₑᵥₑₙ₊ → A ₑᵥₑₙ
  /-- For positive indices, the divided power canonically refines to `Aₑᵥₑₙ₊ → Aₑᵥₑₙ₊`. -/
  gammaPos : ℕ+ → A ₑᵥₑₙ₊ → A ₑᵥₑₙ₊
  /-- The positive-index refinement agrees with the total family after inclusion into `Aₑᵥₑₙ`. -/
  gamma_eq_gammaPos (n : ℕ+) (x : A ₑᵥₑₙ₊) :
      gamma n x = A.evenPositiveToEven (gammaPos n x)
  /-- A degree-`2(d + 1)` homogeneous input is sent to degree `2n(d + 1)`. -/
  gamma_degree (n d : ℕ) (x : A.piece (2 * (d + 1))) :
      ∃ y : A.piece (2 * (n * (d + 1))),
        gamma n (A.evenPositiveHom d x) = A.evenHom (n * (d + 1)) y
  /-- The first divided power is the inclusion of the positive even part into the even part. -/
  gamma_one (x : A ₑᵥₑₙ₊) :
      gamma 1 x = A.evenPositiveToEven x
  /-- The zeroth divided power is the unit. -/
  gamma_zero (x : A ₑᵥₑₙ₊) :
      gamma 0 x = A.oneEven
  /-- The product formula `γ_n(x) γ_m(x) = ((n + m)!)/(n!m!) γ_{n+m}(x)`. -/
  gamma_mul (n m : ℕ) (x : A ₑᵥₑₙ₊) :
      A.evenMul (gamma n x) (gamma m x) =
        (((n + m).factorial / (n.factorial * m.factorial) : ℕ) • gamma (n + m) x)
  /-- The compatibility `γ_n(xy) = x^n γ_n(y)` for `x ∈ Aₑᵥₑₙ` and `y ∈ Aₑᵥₑₙ₊`. -/
  gamma_evenMul (n : ℕ) (x : A ₑᵥₑₙ) (y : A ₑᵥₑₙ₊) :
      gamma n (A.evenMulPositive x y) =
        A.evenMul (A.evenPow x n) (gamma n y)
  /-- For homogeneous odd elements, `γ_n(xy) = 0` once `n > 1`. -/
  gamma_oddMul {n d e : ℕ} (hn : 1 < n) (x : A.piece (2 * d + 1))
      (y : A.piece (2 * e + 1)) :
      gamma n (A.oddMul (A.oddHom d x) (A.oddHom e y)) = 0
  /-- On the positive even part, divided powers turn sums into the usual convolution formula. -/
  gamma_add (n : ℕ) (x y : A ₑᵥₑₙ₊) :
      gamma n (x + y) =
        (Finset.antidiagonal n).sum fun ij ↦
          A.evenMul (gamma ij.1 x) (gamma ij.2 y)
  /-- Iterated divided powers satisfy `γ_n(γ_m(x)) = ((nm)!)/(n!(m!)^n) γ_{nm}(x)` for
  positive `m`. -/
  gamma_comp (n : ℕ) (m : ℕ+) (x : A ₑᵥₑₙ₊) :
      gamma n (gammaPos m x) =
        (((n * (m : ℕ)).factorial / (n.factorial * (m : ℕ).factorial ^ n) : ℕ) •
          gamma (n * (m : ℕ)) x)

namespace DividedPowerStructure

variable {R : Type u} [CommRing R]
variable {A : ParitySplitGradedAlgebra R}

attribute [simp] DividedPowerStructure.gamma_zero
attribute [simp] DividedPowerStructure.gamma_one

/-- A divided power structure evaluates to its family of maps `γ_n`. -/
instance : CoeFun (DividedPowerStructure R A) (fun _ ↦ ℕ → A ₑᵥₑₙ₊ → A ₑᵥₑₙ) where
  coe Γ := Γ.gamma

@[simp] theorem coe_apply (Γ : DividedPowerStructure R A) (n : ℕ) (x : A ₑᵥₑₙ₊) :
    Γ n x = Γ.gamma n x :=
  rfl

/-- A divided power structure is determined by its family of maps `γ_n`. -/
theorem ext (Γ Δ : DividedPowerStructure R A)
    (hγ : ∀ n x, Γ n x = Δ n x) : Γ = Δ := by
  cases Γ with
  | mk gamma gammaPos gamma_eq_gammaPos gamma_degree gamma_one gamma_zero gamma_mul
      gamma_evenMul gamma_oddMul gamma_add gamma_comp =>
      cases Δ with
      | mk gamma' gammaPos' gamma_eq_gammaPos' gamma_degree' gamma_one' gamma_zero'
          gamma_mul' gamma_evenMul' gamma_oddMul' gamma_add' gamma_comp' =>
          dsimp at hγ
          have hgamma : gamma = gamma' := funext fun n ↦ funext fun x ↦ hγ n x
          have hgammaPos : gammaPos = gammaPos' := by
            funext n x
            apply A.evenPositiveToEven_injective
            calc
              A.evenPositiveToEven (gammaPos n x) = gamma n x :=
                (gamma_eq_gammaPos n x).symm
              _ = gamma' n x := hγ n x
              _ = A.evenPositiveToEven (gammaPos' n x) :=
                gamma_eq_gammaPos' n x
          cases hgamma
          cases hgammaPos
          simp

/-- Including `γ_n : Aₑᵥₑₙ₊ → Aₑᵥₑₙ₊` into `Aₑᵥₑₙ` recovers the total family. -/
@[simp] theorem evenPositiveToEven_gammaPos
    (Γ : DividedPowerStructure R A) (n : ℕ+) (x : A ₑᵥₑₙ₊) :
    A.evenPositiveToEven (Γ.gammaPos n x) = Γ n x :=
  (Γ.gamma_eq_gammaPos n x).symm

/-- For a natural-number index equipped with a positivity proof, the divided power factors through
the positive even part. -/
theorem gamma_eq_gammaPos_nat (Γ : DividedPowerStructure R A)
    (n : ℕ) (hn : 0 < n) (x : A ₑᵥₑₙ₊) :
    Γ n x = A.evenPositiveToEven (Γ.gammaPos ⟨n, hn⟩ x) :=
  Γ.gamma_eq_gammaPos ⟨n, hn⟩ x

/-- Iterated divided powers can be evaluated with an explicit natural-number outer index and a
positive inner index. -/
theorem gamma_comp_nat (Γ : DividedPowerStructure R A)
    (n m : ℕ) (hm : 0 < m) (x : A ₑᵥₑₙ₊) :
    Γ n (Γ.gammaPos ⟨m, hm⟩ x) =
      (((n * m).factorial / (n.factorial * m.factorial ^ n) : ℕ) • Γ (n * m) x) :=
  Γ.gamma_comp n ⟨m, hm⟩ x

/-- Iterated divided powers with positive indices use the positive-index refinement on the inner
term. -/
theorem gamma_comp_pos (Γ : DividedPowerStructure R A) (n m : ℕ+) (x : A ₑᵥₑₙ₊) :
    A.evenPositiveToEven (Γ.gammaPos n (Γ.gammaPos m x)) =
      (((((n : ℕ) * (m : ℕ)).factorial
            / ((n : ℕ).factorial * (m : ℕ).factorial ^ (n : ℕ)) : ℕ)) •
        Γ ((n : ℕ) * (m : ℕ)) x) := by
  calc
    A.evenPositiveToEven (Γ.gammaPos n (Γ.gammaPos m x)) = Γ n (Γ.gammaPos m x) :=
      Γ.evenPositiveToEven_gammaPos n (Γ.gammaPos m x)
    _ = (((((n : ℕ) * (m : ℕ)).factorial
          / ((n : ℕ).factorial * (m : ℕ).factorial ^ (n : ℕ)) : ℕ)) •
        Γ ((n : ℕ) * (m : ℕ)) x) := Γ.gamma_comp n m x

end DividedPowerStructure
