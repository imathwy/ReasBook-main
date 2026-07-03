import Mathlib

universe u v w

section

variable {A : Type u} [CommRing A] [IsLocalRing A]

namespace Representation

section

variable {p : ℕ}
variable [CharP (IsLocalRing.ResidueField A) p]
variable {G : Type v} [Group G] [Finite G]
variable {E : Type w} [AddCommGroup E] [Module A E] [Module.Free A E] [Module.Finite A E]

local notation "𝔪" => IsLocalRing.maximalIdeal A
local notation "A⧸𝔪^(" n ")" => A ⧸ (𝔪 ^ n)
local notation "E⧸𝔪^(" n ")E" => E ⧸ ((𝔪 ^ n) • (⊤ : Submodule A E))

/-- Helper for Exercise 15-15.5-3: the canonical transition map on the quotient tower
`E / 𝔪^(n+1) E → E / 𝔪^n E`. -/
abbrev maximalIdealPowTransition (n : ℕ+) :
    E⧸𝔪^((n : ℕ) + 1)E →ₗ[A] E⧸𝔪^((n : ℕ))E :=
  Submodule.factorPowSucc 𝔪 E (n : ℕ)

/-- Helper for Exercise 15-15.5-3: the kernel of the transition
`E / 𝔪^(n+1) E → E / 𝔪^n E` is exactly the image of the `𝔪^n E` layer inside the
`(n + 1)`-st quotient. This is the coefficient module for Serre's square-zero cocycles. -/
private theorem maximalIdealPowTransition_ker_eq_powLayer
    (n : ℕ+) :
    LinearMap.ker (maximalIdealPowTransition (A := A) (E := E) n) =
      ((𝔪 ^ (n : ℕ) • (⊤ : Submodule A E)).map
        (Submodule.mkQ ((𝔪 ^ ((n : ℕ) + 1)) • (⊤ : Submodule A E)))) := by
  simpa [maximalIdealPowTransition, Submodule.factorPowSucc, Submodule.factorPow] using
    (Submodule.ker_mapQ
      (p := ((𝔪 ^ ((n : ℕ) + 1)) • (⊤ : Submodule A E)))
      (q := ((𝔪 ^ (n : ℕ)) • (⊤ : Submodule A E)))
      (f := (LinearMap.id : E →ₗ[A] E))
      (h := Submodule.pow_smul_top_le (I := 𝔪) (M := E) (h := Nat.le_succ (n : ℕ))))

/-- Helper for Exercise 15-15.5-3: the kernel of the transition is the canonical image of the
quotient layer `𝔪^n E / 𝔪^(n+1) E` inside `E / 𝔪^(n+1) E`. This is the source-faithful
square-zero coefficient object used for the obstruction and comparison cocycles. -/
private theorem maximalIdealPowTransition_ker_eq_powSMulLayer_range
    (n : ℕ+) :
    LinearMap.ker (maximalIdealPowTransition (A := A) (E := E) n) =
      (Submodule.powSMulQuotInclusion
        (I := 𝔪) (M := E)
        (a := (n : ℕ)) (b := 1) (c := (n : ℕ) + 1)
        (show (n : ℕ) + 1 = 1 + (n : ℕ) by simp [Nat.add_comm])
        (⊤ : Submodule A E)).range := by
  rw [maximalIdealPowTransition_ker_eq_powLayer (A := A) (E := E) n]
  simpa using
    (Submodule.range_powSMulQuotInclusion
      (I := 𝔪) (M := E)
      (a := (n : ℕ)) (b := 1) (c := (n : ℕ) + 1)
      (show (n : ℕ) + 1 = 1 + (n : ℕ) by simp [Nat.add_comm])
      (⊤ : Submodule A E)).symm

/-- Helper for Exercise 15-15.5-3: the transition
`E / 𝔪^(n+1) E → E / 𝔪^n E` is surjective, so any level-`n` vector has a representative one
step higher in the filtration. -/
private theorem maximalIdealPowTransition_surjective
    (n : ℕ+) :
    Function.Surjective (maximalIdealPowTransition (A := A) (E := E) n) := by
  intro x
  refine Quotient.inductionOn' x ?_
  intro y
  refine ⟨Submodule.Quotient.mk y, ?_⟩
  rfl

/-- Helper for Exercise 15-15.5-3: the kernel layer of
`E / 𝔪^(n+1) E → E / 𝔪^n E` is annihilated by `𝔪`. This is Serre's
source-level square-zero coefficient layer `𝔪^n E / 𝔪^(n+1) E`. -/
private theorem maximalIdealPowTransition_kernel_smul_eq_zero
    (n : ℕ+)
    {x : E⧸𝔪^((n : ℕ) + 1)E}
    (hx : x ∈ LinearMap.ker (maximalIdealPowTransition (A := A) (E := E) n))
    (a : 𝔪) :
    (a : A) • x = 0 := by
  let ι :
      ↑(𝔪 ^ (n : ℕ) • (⊤ : Submodule A E)) ⧸
        ((𝔪 ^ (1 : ℕ)) • (⊤ : Submodule A ↑(𝔪 ^ (n : ℕ) • (⊤ : Submodule A E)))) →ₗ[A]
      E⧸𝔪^((n : ℕ) + 1)E :=
    Submodule.powSMulQuotInclusion
      (I := 𝔪) (M := E)
      (a := (n : ℕ)) (b := 1) (c := (n : ℕ) + 1)
      (show (n : ℕ) + 1 = 1 + (n : ℕ) by simp [Nat.add_comm])
      (⊤ : Submodule A E)
  have hx' : x ∈ ι.range := by
    simpa [ι] using
      (show x ∈
          (Submodule.powSMulQuotInclusion
            (I := 𝔪) (M := E)
            (a := (n : ℕ)) (b := 1) (c := (n : ℕ) + 1)
            (show (n : ℕ) + 1 = 1 + (n : ℕ) by simp [Nat.add_comm])
            (⊤ : Submodule A E)).range by
        simpa [maximalIdealPowTransition_ker_eq_powSMulLayer_range (A := A) (E := E) n] using hx)
  rcases LinearMap.mem_range.mp hx' with ⟨y, rfl⟩
  rw [← ι.map_smul]
  refine Quotient.inductionOn' y ?_
  intro z
  change ι (Submodule.Quotient.mk ((a : A) • z)) = 0
  rw [Submodule.powSMulQuotInclusion_mk]
  rw [Submodule.Quotient.mk_eq_zero]
  simpa [pow_succ, Ideal.mul_comm, smul_smul] using
    Submodule.smul_mem_smul a.property z.property

/-- Helper for Exercise 15-15.5-3: an endomorphism whose image lies in the transition kernel has
`𝔪`-torsion image. This is the first structural input for the square-zero correction algebra. -/
private theorem correction_endomorphism_smul_eq_zero
    (n : ℕ+)
    {t : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)}
    (ht :
      (maximalIdealPowTransition (A := A) (E := E) n).comp (t.restrictScalars A) = 0)
    (a : 𝔪)
    (x : E⧸𝔪^((n : ℕ) + 1)E) :
    (a : A) • t x = 0 := by
  apply maximalIdealPowTransition_kernel_smul_eq_zero (A := A) (E := E) (n := n)
  rw [LinearMap.mem_ker]
  have htx := LinearMap.congr_fun ht x
  simpa [LinearMap.comp_apply] using htx

/-- Helper for Exercise 15-15.5-3: a correction endomorphism on
`E / 𝔪^(n+1) E` kills the canonical layer `𝔪^n E / 𝔪^(n+1) E` inside that quotient. This is the
source-faithful bridge from the kernel condition `π ∘ t = 0` to Serre's square-zero coefficient
module. -/
private theorem correction_endomorphism_comp_powSMulQuotInclusion_eq_zero
    (n : ℕ+)
    {t : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)}
    (ht :
      (maximalIdealPowTransition (A := A) (E := E) n).comp (t.restrictScalars A) = 0) :
    let ι :
        ↑(𝔪 ^ (n : ℕ) • (⊤ : Submodule A E)) ⧸
          ((𝔪 ^ (1 : ℕ)) • (⊤ : Submodule A ↑(𝔪 ^ (n : ℕ) • (⊤ : Submodule A E)))) →ₗ[A]
        E⧸𝔪^((n : ℕ) + 1)E :=
      Submodule.powSMulQuotInclusion
        (I := 𝔪) (M := E)
        (a := (n : ℕ)) (b := 1) (c := (n : ℕ) + 1)
        (show (n : ℕ) + 1 = 1 + (n : ℕ) by simp [Nat.add_comm])
        (⊤ : Submodule A E)
    (t.restrictScalars A).comp ι = 0 := by
  dsimp
  apply LinearMap.ext
  intro y
  refine Quotient.inductionOn' y ?_
  intro z
  change t (Submodule.Quotient.mk (z : E)) = 0
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp n.pos) with ⟨m, hm⟩
  have hz :
      (z : E) ∈ 𝔪 • (𝔪 ^ m • (⊤ : Submodule A E)) := by
    simpa [hm, pow_succ, Ideal.mul_comm, mul_smul] using z.property
  refine Submodule.smul_induction_on (I := 𝔪) (N := (𝔪 ^ m • (⊤ : Submodule A E))) hz ?_ ?_
  · intro a ha w hw
    simpa using
      correction_endomorphism_smul_eq_zero
        (A := A) (E := E) (n := n) (t := t) ht ⟨a, ha⟩ (Submodule.Quotient.mk w)
  · intro x y hx hy
    simp [hx, hy]

/-- Helper for Exercise 15-15.5-3: a correction endomorphism vanishes on the full kernel of the
transition `E / 𝔪^(n+1) E → E / 𝔪^n E` once that kernel is identified with the canonical layer
`𝔪^n E / 𝔪^(n+1) E`. -/
private theorem correction_endomorphism_eq_zero_on_transition_kernel
    (n : ℕ+)
    {t : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)}
    (ht :
      (maximalIdealPowTransition (A := A) (E := E) n).comp (t.restrictScalars A) = 0)
    {x : E⧸𝔪^((n : ℕ) + 1)E}
    (hx : x ∈ LinearMap.ker (maximalIdealPowTransition (A := A) (E := E) n)) :
    t x = 0 := by
  let ι :
      ↑(𝔪 ^ (n : ℕ) • (⊤ : Submodule A E)) ⧸
        ((𝔪 ^ (1 : ℕ)) • (⊤ : Submodule A ↑(𝔪 ^ (n : ℕ) • (⊤ : Submodule A E)))) →ₗ[A]
      E⧸𝔪^((n : ℕ) + 1)E :=
    Submodule.powSMulQuotInclusion
      (I := 𝔪) (M := E)
      (a := (n : ℕ)) (b := 1) (c := (n : ℕ) + 1)
      (show (n : ℕ) + 1 = 1 + (n : ℕ) by simp [Nat.add_comm])
      (⊤ : Submodule A E)
  have hx' : x ∈ ι.range := by
    simpa [ι, maximalIdealPowTransition_ker_eq_powSMulLayer_range (A := A) (E := E) n] using hx
  rcases LinearMap.mem_range.mp hx' with ⟨y, rfl⟩
  have hcomp :
      (t.restrictScalars A).comp ι = 0 :=
    correction_endomorphism_comp_powSMulQuotInclusion_eq_zero
      (A := A) (E := E) (n := n) (t := t) ht
  have hy := LinearMap.congr_fun hcomp y
  simpa [LinearMap.comp_apply] using hy

/-- Helper for Exercise 15-15.5-3: correction endomorphisms with image in the transition kernel
form a square-zero algebra. This is Serre's coefficient algebra for the obstruction and comparison
cocycles. -/
private theorem ker_correction_square_zero
    (n : ℕ+)
    {t₁ t₂ : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)}
    (ht₁ :
      (maximalIdealPowTransition (A := A) (E := E) n).comp (t₁.restrictScalars A) = 0)
    (ht₂ :
      (maximalIdealPowTransition (A := A) (E := E) n).comp (t₂.restrictScalars A) = 0) :
    t₁ * t₂ = 0 := by
  apply LinearMap.ext
  intro x
  have hxker : t₂ x ∈ LinearMap.ker (maximalIdealPowTransition (A := A) (E := E) n) := by
    rw [LinearMap.mem_ker]
    have htx := LinearMap.congr_fun ht₂ x
    simpa [LinearMap.comp_apply] using htx
  simpa [Module.End.mul_apply] using
    correction_endomorphism_eq_zero_on_transition_kernel
      (A := A) (E := E) (n := n) (t := t₁) ht₁ hxker

/-- Helper for Exercise 15-15.5-3: Serre's coefficient algebra on the tower
`E / 𝔪^(n+1) E → E / 𝔪^n E` is the subtype of endomorphisms annihilated by the transition. This
packages the already-verified kernel condition before adding the group-conjugation action. -/
private def maximalIdealPowTransitionCorrection (n : ℕ+) :
    Type _ :=
  { t : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E) //
      (maximalIdealPowTransition (A := A) (E := E) n).comp (t.restrictScalars A) = 0 }

/-- Helper for Exercise 15-15.5-3: the correction coefficient object is inhabited by the zero
endomorphism. This gives a canonical base point for the later defect and comparison cocycles. -/
private theorem maximalIdealPowTransitionCorrection_nonempty
    (n : ℕ+) :
    Nonempty (maximalIdealPowTransitionCorrection (A := A) (E := E) n) := by
  refine ⟨⟨0, ?_⟩⟩
  ext x
  simp

/-- Helper for Exercise 15-15.5-3: a correction endomorphism from the packaged coefficient object
still kills the full transition kernel. This is the stable API consumed later by the cocycle
correction step. -/
private theorem maximalIdealPowTransitionCorrection_apply_eq_zero_of_mem_ker
    (n : ℕ+)
    (t : maximalIdealPowTransitionCorrection (A := A) (E := E) n)
    {x : E⧸𝔪^((n : ℕ) + 1)E}
    (hx : x ∈ LinearMap.ker (maximalIdealPowTransition (A := A) (E := E) n)) :
    t.1 x = 0 := by
  exact
    correction_endomorphism_eq_zero_on_transition_kernel
      (A := A) (E := E) (n := n) (t := t.1) t.2 hx

/-- Helper for Exercise 15-15.5-3: the packaged correction endomorphisms form a square-zero
algebra under composition. This is the exact source-level input used when replacing a preliminary
lift by `id - a(g)` corrections. -/
private theorem maximalIdealPowTransitionCorrection_square_zero
    (n : ℕ+)
    (t₁ t₂ : maximalIdealPowTransitionCorrection (A := A) (E := E) n) :
    t₁.1 * t₂.1 = 0 := by
  exact
    ker_correction_square_zero
      (A := A) (E := E) (n := n) (t₁ := t₁.1) (t₂ := t₂.1) t₁.2 t₂.2

/-- Helper for Exercise 15-15.5-3: if an upstairs automorphism `U` reduces to some downstairs
endomorphism through `maximalIdealPowTransition`, then conjugation by `U` preserves the packaged
correction algebra. This is the stable interface needed before introducing Serre's cocycles. -/
private theorem maximalIdealPowTransitionCorrection_conj_mem
    (n : ℕ+)
    (U : E⧸𝔪^((n : ℕ) + 1)E ≃ₗ[A⧸𝔪^((n : ℕ) + 1)] E⧸𝔪^((n : ℕ) + 1)E)
    {u : Module.End A (E⧸𝔪^((n : ℕ))E)}
    (hU :
      (maximalIdealPowTransition (A := A) (E := E) n).comp (U.toLinearMap.restrictScalars A) =
        u.comp (maximalIdealPowTransition (A := A) (E := E) n))
    (t : maximalIdealPowTransitionCorrection (A := A) (E := E) n) :
    (maximalIdealPowTransition (A := A) (E := E) n).comp
        (((U.toLinearMap * t.1 * U.symm.toLinearMap).restrictScalars A)) = 0 := by
  apply LinearMap.ext
  intro x
  have hUx :
      (maximalIdealPowTransition (A := A) (E := E) n) (U (t.1 (U.symm x))) =
        u ((maximalIdealPowTransition (A := A) (E := E) n) (t.1 (U.symm x))) := by
    have hUfun := LinearMap.congr_fun hU (t.1 (U.symm x))
    simpa [LinearMap.comp_apply] using hUfun
  have htx :
      (maximalIdealPowTransition (A := A) (E := E) n) (t.1 (U.symm x)) = 0 := by
    have htfun := LinearMap.congr_fun t.2 (U.symm x)
    simpa [LinearMap.comp_apply] using htfun
  calc
    (maximalIdealPowTransition (A := A) (E := E) n)
        (((U.toLinearMap * t.1 * U.symm.toLinearMap) : Module.End _ _) x)
      = (maximalIdealPowTransition (A := A) (E := E) n) (U (t.1 (U.symm x))) := by
          simp [Module.End.mul_apply]
    _ = u ((maximalIdealPowTransition (A := A) (E := E) n) (t.1 (U.symm x))) := hUx
    _ = 0 := by rw [htx, map_zero]

/-- Helper for Exercise 15-15.5-3: package the previous conjugation-closure statement as an
actual endomorphism of the correction subtype. This is the coefficient-side conjugation action
used later for Serre's obstruction and comparison cocycles. -/
private def maximalIdealPowTransitionCorrection_conj
    (n : ℕ+)
    (U : E⧸𝔪^((n : ℕ) + 1)E ≃ₗ[A⧸𝔪^((n : ℕ) + 1)] E⧸𝔪^((n : ℕ) + 1)E)
    {u : Module.End A (E⧸𝔪^((n : ℕ))E)}
    (hU :
      (maximalIdealPowTransition (A := A) (E := E) n).comp (U.toLinearMap.restrictScalars A) =
        u.comp (maximalIdealPowTransition (A := A) (E := E) n))
    (t : maximalIdealPowTransitionCorrection (A := A) (E := E) n) :
    maximalIdealPowTransitionCorrection (A := A) (E := E) n :=
  ⟨U.toLinearMap * t.1 * U.symm.toLinearMap,
    maximalIdealPowTransitionCorrection_conj_mem
      (A := A) (E := E) (n := n) U hU t⟩

/-- Helper for Exercise 15-15.5-3: every packaged correction is annihilated by the maximal ideal
at each vector. This is the coefficient-side torsion fact used to view Serre's correction space
over the residue field. -/
private theorem maximalIdealPowTransitionCorrection_smul_apply_eq_zero
    (n : ℕ+)
    (t : maximalIdealPowTransitionCorrection (A := A) (E := E) n)
    (a : 𝔪)
    (x : E⧸𝔪^((n : ℕ) + 1)E) :
    (a : A) • t.1 x = 0 := by
  simpa using
    correction_endomorphism_smul_eq_zero
      (A := A) (E := E) (n := n) (t := t.1) t.2 a x

/-- Helper for Exercise 15-15.5-3: because corrections square to zero, `1 - c` is a left inverse
to `1 + c`. This is the algebraic core behind Serre's correction automorphisms. -/
private theorem maximalIdealPowTransitionCorrection_one_add_mul_one_sub
    (n : ℕ+)
    (c : maximalIdealPowTransitionCorrection (A := A) (E := E) n) :
    ((1 : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)) + c.1) * (1 - c.1) = 1 := by
  have hcc :
      c.1 * c.1 = 0 :=
    maximalIdealPowTransitionCorrection_square_zero (A := A) (E := E) (n := n) c c
  calc
    ((1 : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)) + c.1) * (1 - c.1)
        = 1 * (1 - c.1) + c.1 * (1 - c.1) := by
            rw [add_mul]
    _ = (1 - c.1) + (c.1 * 1 - c.1 * c.1) := by
          rw [one_mul, mul_sub]
    _ = (1 - c.1) + c.1 := by
          rw [mul_one, hcc, sub_zero]
    _ = 1 := by
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Exercise 15-15.5-3: because corrections square to zero, `1 - c` is also a right
inverse to `1 + c`. -/
private theorem maximalIdealPowTransitionCorrection_one_sub_mul_one_add
    (n : ℕ+)
    (c : maximalIdealPowTransitionCorrection (A := A) (E := E) n) :
    (1 - c.1) *
        ((1 : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)) + c.1) = 1 := by
  have hcc :
      c.1 * c.1 = 0 :=
    maximalIdealPowTransitionCorrection_square_zero (A := A) (E := E) (n := n) c c
  calc
    (1 - c.1) *
        ((1 : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)) + c.1)
        = (1 - c.1) * 1 + (1 - c.1) * c.1 := by
            rw [mul_add]
    _ = (1 - c.1) + (1 * c.1 - c.1 * c.1) := by
          rw [mul_one, sub_mul]
    _ = (1 - c.1) + c.1 := by
          rw [one_mul, hcc, sub_zero]
    _ = 1 := by
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Exercise 15-15.5-3: every square-zero correction produces the concrete
automorphism `1 + c` with inverse `1 - c`. This is the source-faithful correction automorphism
used later in Serre's uniqueness-by-conjugation argument. -/
private theorem maximalIdealPowTransitionCorrection_exists_one_add_linearEquiv
    (n : ℕ+)
    (c : maximalIdealPowTransitionCorrection (A := A) (E := E) n) :
    ∃ U : E⧸𝔪^((n : ℕ) + 1)E ≃ₗ[A⧸𝔪^((n : ℕ) + 1)] E⧸𝔪^((n : ℕ) + 1)E,
      U.toLinearMap =
          ((1 : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)) + c.1) ∧
        U.symm.toLinearMap = (1 - c.1) := by
  refine ⟨LinearEquiv.ofLinear
      (((1 : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)) + c.1))
      (1 - c.1) ?_ ?_, rfl, rfl⟩
  · simpa using
      maximalIdealPowTransitionCorrection_one_add_mul_one_sub
        (A := A) (E := E) (n := n) c
  · simpa using
      maximalIdealPowTransitionCorrection_one_sub_mul_one_add
        (A := A) (E := E) (n := n) c

/-- Helper for Exercise 15-15.5-3: conjugation by a defect term `1 + c` acts trivially on the
square-zero correction algebra, because every product of two corrections vanishes. -/
private theorem maximalIdealPowTransitionCorrection_conj_correction_eq_self
    (n : ℕ+)
    (c t : maximalIdealPowTransitionCorrection (A := A) (E := E) n) :
    (((1 : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)) + c.1) * t.1) * (1 - c.1) =
      t.1 := by
  have hct :
      c.1 * t.1 = 0 :=
    maximalIdealPowTransitionCorrection_square_zero (A := A) (E := E) (n := n) c t
  have htc :
      t.1 * c.1 = 0 :=
    maximalIdealPowTransitionCorrection_square_zero (A := A) (E := E) (n := n) t c
  calc
    (((1 : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)) + c.1) * t.1) * (1 - c.1)
        = (t.1 + c.1 * t.1) * (1 - c.1) := by
            rw [add_mul, one_mul]
    _ = t.1 * (1 - c.1) := by
          rw [hct, add_zero]
    _ = t.1 * 1 - t.1 * c.1 := by
          rw [mul_sub]
    _ = t.1 := by
          rw [mul_one, htc, sub_zero]

/-- Helper for Exercise 15-15.5-3: a correction automorphism `1 + c` still reduces to the
identity through `E / 𝔪^(n+1) E → E / 𝔪^n E`. This is the exact congruence condition needed in
the uniqueness statement. -/
private theorem maximalIdealPowTransitionCorrection_one_add_reduces_to_identity
    (n : ℕ+)
    (c : maximalIdealPowTransitionCorrection (A := A) (E := E) n) :
    (maximalIdealPowTransition (A := A) (E := E) n).comp
        (((1 : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)) + c.1).restrictScalars A) =
      maximalIdealPowTransition (A := A) (E := E) n := by
  apply LinearMap.ext
  intro x
  have hcx :
      (maximalIdealPowTransition (A := A) (E := E) n) (c.1 x) = 0 := by
    have hcfun := LinearMap.congr_fun c.2 x
    simpa [LinearMap.comp_apply] using hcfun
  change
    (maximalIdealPowTransition (A := A) (E := E) n)
        (((1 : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)) + c.1) x) =
      (maximalIdealPowTransition (A := A) (E := E) n) x
  simp [hcx]

/-- Helper for Exercise 15-15.5-3: every matrix over `A ⧸ 𝔪^n` lifts entrywise along the
canonical quotient map `A ⧸ 𝔪^(n+1) → A ⧸ 𝔪^n`. This isolates the source-faithful coordinate
surjectivity step before rebuilding preliminary automorphisms on the quotient tower. -/
private theorem exists_matrix_lift_of_ideal_quotient
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ+)
    (M : Matrix ι ι (A⧸𝔪^((n : ℕ)))) :
    ∃ N : Matrix ι ι (A⧸𝔪^((n : ℕ) + 1)),
      ∀ i j, Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ) (N i j) = M i j := by
  classical
  choose lift hlift using fun i j ↦ Ideal.Quotient.mk_surjective (M i j)
  refine ⟨fun i j ↦ lift i j, ?_⟩
  intro i j
  exact hlift i j

end

end Representation

end
