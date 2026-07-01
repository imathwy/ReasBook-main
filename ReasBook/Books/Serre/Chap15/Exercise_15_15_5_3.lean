import Mathlib
import Serre.Chap14.Corollary_14_14_4_4
import Serre.Chap14.Lemma_14_14_4_2
import Serre.Chap15.Definition_15_15_2_1
import Serre.Chap15.Exercise_15_15_5_3.Index
import Serre.Chap15.Exercise_15_15_5_3.ResidueFieldLift

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x y

open scoped MonoidAlgebra

section

variable {A : Type u} [CommRing A] [IsLocalRing A]

/- Domain-style sampling:
* source-facing: finite free linear representations modulo powers of the maximal ideal, and
  finite-dimensional residue-field representations together with free finitely generated lifts.
* core/canonical: `Representation`, `Representation.restrictScalars`,
  `Representation.IsIntertwiningMap`, `IsBaseChange`, `Submodule.factorPowSucc`, and the Chapter
  `14` owner `LinearMap.IsResidueFieldReduction`.
* bridge/view: the direct quotient-level lift and congruence conditions expressed through
  `Submodule.factorPowSucc` and `Representation.IsIntertwiningMap`, together with the thin
  representation-level residue-field lifting view `IsResidueFieldLift` that keeps the theorem
  surface in Serre's representation language while delegating the reduction owner to Chapter `14`.
-/

namespace Representation

section

variable {p : ℕ}
variable [CharP (IsLocalRing.ResidueField A) p]
variable {G : Type v} [Group G] [Finite G]
variable {E : Type w} [AddCommGroup E] [Module A E] [Module.Free A E] [Module.Finite A E]

local notation "𝔪" => IsLocalRing.maximalIdeal A
local notation "A⧸𝔪^(" n ")" => A ⧸ (𝔪 ^ n)
local notation "E⧸𝔪^(" n ")E" => E ⧸ ((𝔪 ^ n) • (⊤ : Submodule A E))

/-- Helper for Exercise 15-15.5-3: if two upstairs endomorphisms induce the same map on the
`n`-th quotient, then their difference already lies in the transition kernel. This is the stable
source-faithful bridge used before packaging square-zero correction terms. -/
private theorem transition_difference_reduces_to_zero
    (n : ℕ+)
    {U V : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)}
    (hUV :
      (maximalIdealPowTransition (A := A) (E := E) n).comp (U.restrictScalars A) =
        (maximalIdealPowTransition (A := A) (E := E) n).comp (V.restrictScalars A)) :
    (maximalIdealPowTransition (A := A) (E := E) n).comp ((U - V).restrictScalars A) = 0 := by
  -- The common reduction identifies the two images downstairs, so the pointwise difference dies
  -- after applying the transition map.
  ext x
  have hx := DFunLike.congr_fun hUV (Submodule.Quotient.mk x)
  -- Rewrite the difference pointwise and cancel the equal reduced images.
  simpa [LinearMap.comp_apply, LinearMap.sub_apply, map_sub] using sub_eq_zero.mpr hx

/-- Helper for Exercise 15-15.5-3: the transition
`E / 𝔪^(n+1) E → E / 𝔪^n E` is surjective. This is the basic pointwise lift input before
reconstructing Serre's preliminary automorphisms upstairs. -/
private theorem maximalIdealPowTransition_surjective
    (n : ℕ+) :
    Function.Surjective (maximalIdealPowTransition (A := A) (E := E) n) := by
  -- Every quotient class downstairs already has a representative one step higher in the tower.
  intro x
  refine Quotient.inductionOn' x ?_
  intro y
  exact ⟨Submodule.Quotient.mk y, rfl⟩

/-- Helper for Exercise 15-15.5-3: the transition `E / 𝔪^(n+1) E → E / 𝔪^n E` stays surjective
after the `n`-th quotient is viewed as an `A ⧸ 𝔪^(n + 1)`-module through
`Ideal.Quotient.factorPowSucc`. This isolates the map-shape required by the planned projective
lift. -/
private theorem maximalIdealPowTransition_surjective_factorPowSucc
    (n : ℕ+) :
    let R1 := A⧸𝔪^((n : ℕ) + 1)
    letI : Module R1 (E⧸𝔪^((n : ℕ))E) :=
      Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
    Function.Surjective (maximalIdealPowTransition (A := A) (E := E) n) := by
  intro R1
  letI : Module R1 (E⧸𝔪^((n : ℕ))E) :=
    Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
  -- The transported codomain action changes only the scalar bookkeeping, not the underlying map.
  exact maximalIdealPowTransition_surjective (A := A) (E := E) n

/-- Helper for Exercise 15-15.5-3: the kernel of the transition is the canonical image of the
layer `𝔪^n E / 𝔪^(n+1) E` in `E / 𝔪^(n+1) E`. This is the square-zero coefficient layer in
Serre's argument. -/
private theorem transition_ker_eq_powSMul_layer_range
    (n : ℕ+) :
    LinearMap.ker (maximalIdealPowTransition (A := A) (E := E) n) =
      (Submodule.powSMulQuotInclusion
        (I := 𝔪) (M := E)
        (a := (n : ℕ)) (b := 1) (c := (n : ℕ) + 1)
        (show (n : ℕ) + 1 = 1 + (n : ℕ) by simp [Nat.add_comm])
        (⊤ : Submodule A E)).range := by
  -- Rewrite the transition kernel via the standard quotient-power identification.
  rw [show LinearMap.ker (maximalIdealPowTransition (A := A) (E := E) n) =
      ((𝔪 ^ (n : ℕ) • (⊤ : Submodule A E)).map
        (Submodule.mkQ ((𝔪 ^ ((n : ℕ) + 1)) • (⊤ : Submodule A E)))) by
        simpa [maximalIdealPowTransition, Submodule.factorPowSucc, Submodule.factorPow] using
          (Submodule.ker_mapQ
            (p := ((𝔪 ^ ((n : ℕ) + 1)) • (⊤ : Submodule A E)))
            (q := ((𝔪 ^ (n : ℕ)) • (⊤ : Submodule A E)))
            (f := (LinearMap.id : E →ₗ[A] E))
            (h := Submodule.pow_smul_top_le (I := 𝔪) (M := E)
              (h := Nat.le_succ (n : ℕ))))]
  -- The standard inclusion from the layer quotient has exactly this image.
  simpa using
    (Submodule.range_powSMulQuotInclusion
      (I := 𝔪) (M := E)
      (a := (n : ℕ)) (b := 1) (c := (n : ℕ) + 1)
      (show (n : ℕ) + 1 = 1 + (n : ℕ) by simp [Nat.add_comm])
      (⊤ : Submodule A E)).symm

/-- Helper for Exercise 15-15.5-3: every vector in the transition kernel is annihilated by the
maximal ideal. This is the source-level square-zero property of the coefficient layer
`𝔪^n E / 𝔪^(n+1) E`. -/
private theorem transition_kernel_smul_eq_zero
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
    -- Identify the kernel with the canonical power layer once and then lift `x` from the range.
    simpa [ι, transition_ker_eq_powSMul_layer_range (A := A) (E := E) n] using hx
  rcases LinearMap.mem_range.mp hx' with ⟨y, rfl⟩
  -- On the layer quotient, multiplying by `a ∈ 𝔪` lands in `𝔪^(n+1) E`, so the class vanishes.
  rw [← ι.map_smul]
  refine Quotient.inductionOn' y ?_
  intro z
  change ι (Submodule.Quotient.mk ((a : A) • z)) = 0
  rw [Submodule.powSMulQuotInclusion_mk]
  rw [Submodule.Quotient.mk_eq_zero]
  simpa [pow_succ, Ideal.mul_comm, smul_smul] using
    Submodule.smul_mem_smul a.property z.property

/-- Helper for Exercise 15-15.5-3: a correction endomorphism with zero transition reduction has
`𝔪`-torsion image. This is the first structural input for the square-zero endomorphism algebra. -/
private theorem zero_reduction_smul_eq_zero
    (n : ℕ+)
    {c : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)}
    (hc :
      (maximalIdealPowTransition (A := A) (E := E) n).comp (c.restrictScalars A) = 0)
    (a : 𝔪)
    (x : E⧸𝔪^((n : ℕ) + 1)E) :
    (a : A) • c x = 0 := by
  -- The image point `c x` lies in the transition kernel, so the previous kernel-torsion lemma
  -- applies directly.
  apply transition_kernel_smul_eq_zero (A := A) (E := E) (n := n)
  rw [LinearMap.mem_ker]
  have hcx := LinearMap.congr_fun hc x
  simpa [LinearMap.comp_apply] using hcx

/-- Helper for Exercise 15-15.5-3: a zero-reduction correction endomorphism kills the canonical
layer `𝔪^n E / 𝔪^(n+1) E` inside `E / 𝔪^(n+1) E`. -/
private theorem zero_reduction_comp_powSMulQuotInclusion_eq_zero
    (n : ℕ+)
    {c : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)}
    (hc :
      (maximalIdealPowTransition (A := A) (E := E) n).comp (c.restrictScalars A) = 0) :
    let ι :
        ↑(𝔪 ^ (n : ℕ) • (⊤ : Submodule A E)) ⧸
          ((𝔪 ^ (1 : ℕ)) • (⊤ : Submodule A ↑(𝔪 ^ (n : ℕ) • (⊤ : Submodule A E)))) →ₗ[A]
        E⧸𝔪^((n : ℕ) + 1)E :=
      Submodule.powSMulQuotInclusion
        (I := 𝔪) (M := E)
        (a := (n : ℕ)) (b := 1) (c := (n : ℕ) + 1)
        (show (n : ℕ) + 1 = 1 + (n : ℕ) by simp [Nat.add_comm])
        (⊤ : Submodule A E)
    (c.restrictScalars A).comp ι = 0 := by
  dsimp
  -- It is enough to check the vanishing on representatives of the quotient layer.
  apply LinearMap.ext
  intro y
  refine Quotient.inductionOn' y ?_
  intro z
  change c (Submodule.Quotient.mk (z : E)) = 0
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp n.pos) with ⟨m, hm⟩
  have hz :
      (z : E) ∈ 𝔪 • (𝔪 ^ m • (⊤ : Submodule A E)) := by
    simpa [hm, pow_succ, Ideal.mul_comm, mul_smul] using z.property
  refine Submodule.smul_induction_on (I := 𝔪) (N := (𝔪 ^ m • (⊤ : Submodule A E))) hz ?_ ?_
  · intro a ha w hw
    simpa using
      zero_reduction_smul_eq_zero
        (A := A) (E := E) (n := n) (c := c) hc ⟨a, ha⟩ (Submodule.Quotient.mk w)
  · intro x y hx hy
    simp [hx, hy]

/-- Helper for Exercise 15-15.5-3: a zero-reduction correction endomorphism vanishes on the whole
transition kernel. This is the exact square-zero bridge used in Serre's cocycle algebra. -/
private theorem zero_reduction_eq_zero_on_transition_kernel
    (n : ℕ+)
    {c : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)}
    (hc :
      (maximalIdealPowTransition (A := A) (E := E) n).comp (c.restrictScalars A) = 0)
    {x : E⧸𝔪^((n : ℕ) + 1)E}
    (hx : x ∈ LinearMap.ker (maximalIdealPowTransition (A := A) (E := E) n)) :
    c x = 0 := by
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
    -- Move from the abstract kernel description back to the canonical quotient-layer inclusion.
    simpa [ι, transition_ker_eq_powSMul_layer_range (A := A) (E := E) n] using hx
  rcases LinearMap.mem_range.mp hx' with ⟨y, rfl⟩
  have hcomp :
      (c.restrictScalars A).comp ι = 0 :=
    zero_reduction_comp_powSMulQuotInclusion_eq_zero
      (A := A) (E := E) (n := n) (c := c) hc
  have hy := LinearMap.congr_fun hcomp y
  simpa [LinearMap.comp_apply] using hy

/-- Helper for Exercise 15-15.5-3: two zero-reduction correction endomorphisms compose to zero.
This is Serre's square-zero coefficient algebra on the transition tower. -/
private theorem zero_reduction_square_zero
    (n : ℕ+)
    {c d : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)}
    (hc :
      (maximalIdealPowTransition (A := A) (E := E) n).comp (c.restrictScalars A) = 0)
    (hd :
      (maximalIdealPowTransition (A := A) (E := E) n).comp (d.restrictScalars A) = 0) :
    c * d = 0 := by
  -- The image of `d` already lies in the transition kernel, where `c` vanishes.
  apply LinearMap.ext
  intro x
  have hxker : d x ∈ LinearMap.ker (maximalIdealPowTransition (A := A) (E := E) n) := by
    rw [LinearMap.mem_ker]
    have hdx := LinearMap.congr_fun hd x
    simpa [LinearMap.comp_apply] using hdx
  simpa [Module.End.mul_apply] using
    zero_reduction_eq_zero_on_transition_kernel
      (A := A) (E := E) (n := n) (c := c) hc hxker

/-- Helper for Exercise 15-15.5-3: conjugation by an upstairs lift preserves zero transition
reduction. This is the adapter needed for both the defect and comparison cocycles. -/
private theorem zero_reduction_conj
    (n : ℕ+)
    (U : E⧸𝔪^((n : ℕ) + 1)E ≃ₗ[A⧸𝔪^((n : ℕ) + 1)] E⧸𝔪^((n : ℕ) + 1)E)
    {u : Module.End A (E⧸𝔪^((n : ℕ))E)}
    (hU :
      (maximalIdealPowTransition (A := A) (E := E) n).comp (U.toLinearMap.restrictScalars A) =
        u.comp (maximalIdealPowTransition (A := A) (E := E) n))
    {c : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)}
    (hc :
      (maximalIdealPowTransition (A := A) (E := E) n).comp (c.restrictScalars A) = 0) :
    (maximalIdealPowTransition (A := A) (E := E) n).comp
        (((U.toLinearMap * c * U.symm.toLinearMap).restrictScalars A)) = 0 := by
  -- Push the conjugated correction through the transition map and use that `c` already reduces to
  -- zero before applying the downstairs endomorphism `u`.
  apply LinearMap.ext
  intro x
  have hUx :
      (maximalIdealPowTransition (A := A) (E := E) n) (U (c (U.symm x))) =
        u ((maximalIdealPowTransition (A := A) (E := E) n) (c (U.symm x))) := by
    have hUfun := LinearMap.congr_fun hU (c (U.symm x))
    simpa [LinearMap.comp_apply] using hUfun
  have hcx :
      (maximalIdealPowTransition (A := A) (E := E) n) (c (U.symm x)) = 0 := by
    have hcfun := LinearMap.congr_fun hc (U.symm x)
    simpa [LinearMap.comp_apply] using hcfun
  calc
    (maximalIdealPowTransition (A := A) (E := E) n)
        (((U.toLinearMap * c * U.symm.toLinearMap) : Module.End _ _) x)
      = (maximalIdealPowTransition (A := A) (E := E) n) (U (c (U.symm x))) := by
          simp [Module.End.mul_apply]
    _ = u ((maximalIdealPowTransition (A := A) (E := E) n) (c (U.symm x))) := hUx
    _ = 0 := by rw [hcx, map_zero]

/-- Helper for Exercise 15-15.5-3: because zero-reduction corrections square to zero,
`(1 + c) * (1 - c) = 1`. This is the algebraic core of Serre's correction automorphisms. -/
private theorem one_add_mul_one_sub_of_zero_reduction
    (n : ℕ+)
    {c : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)}
    (hc :
      (maximalIdealPowTransition (A := A) (E := E) n).comp (c.restrictScalars A) = 0) :
    ((1 : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)) + c) * (1 - c) = 1 := by
  have hcc : c * c = 0 :=
    zero_reduction_square_zero (A := A) (E := E) (n := n) hc hc
  -- Expand the product and drop the quadratic term.
  calc
    ((1 : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)) + c) * (1 - c)
        = 1 * (1 - c) + c * (1 - c) := by
            rw [add_mul]
    _ = (1 - c) + (c * 1 - c * c) := by
          rw [one_mul, mul_sub]
    _ = (1 - c) + c := by
          rw [mul_one, hcc, sub_zero]
    _ = 1 := by
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Exercise 15-15.5-3: because zero-reduction corrections square to zero,
`(1 - c) * (1 + c) = 1` as well. -/
private theorem one_sub_mul_one_add_of_zero_reduction
    (n : ℕ+)
    {c : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)}
    (hc :
      (maximalIdealPowTransition (A := A) (E := E) n).comp (c.restrictScalars A) = 0) :
    (1 - c) * ((1 : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)) + c) = 1 := by
  have hcc : c * c = 0 :=
    zero_reduction_square_zero (A := A) (E := E) (n := n) hc hc
  -- The symmetric expansion again reduces to the linear terms.
  calc
    (1 - c) * ((1 : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)) + c)
        = (1 - c) * 1 + (1 - c) * c := by
            rw [mul_add]
    _ = (1 - c) + (1 * c - c * c) := by
          rw [mul_one, sub_mul]
    _ = (1 - c) + c := by
          rw [one_mul, hcc, sub_zero]
    _ = 1 := by
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Exercise 15-15.5-3: every zero-reduction correction yields an automorphism
`1 + c` with inverse `1 - c`, and this automorphism still reduces to the identity downstairs. -/
private theorem exists_linearEquiv_one_add_of_zero_reduction
    (n : ℕ+)
    {c : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)}
    (hc :
      (maximalIdealPowTransition (A := A) (E := E) n).comp (c.restrictScalars A) = 0) :
    ∃ W : E⧸𝔪^((n : ℕ) + 1)E ≃ₗ[A⧸𝔪^((n : ℕ) + 1)] E⧸𝔪^((n : ℕ) + 1)E,
      W.toLinearMap =
          ((1 : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)) + c) ∧
        W.symm.toLinearMap = (1 - c) ∧
        (maximalIdealPowTransition (A := A) (E := E) n).comp
            (W.toLinearMap.restrictScalars A) =
          maximalIdealPowTransition (A := A) (E := E) n := by
  refine ⟨LinearEquiv.ofLinear
      (((1 : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)) + c))
      (1 - c) ?_ ?_, rfl, rfl, ?_⟩
  · -- The explicit inverse check is exactly the square-zero identity proved above.
    simpa using one_add_mul_one_sub_of_zero_reduction (A := A) (E := E) (n := n) hc
  · -- The opposite composite is identical for the same reason.
    simpa using one_sub_mul_one_add_of_zero_reduction (A := A) (E := E) (n := n) hc
  · -- The correction term still reduces to zero, so `1 + c` reduces to the identity.
    apply LinearMap.ext
    intro x
    have hcx :
        (maximalIdealPowTransition (A := A) (E := E) n) (c x) = 0 := by
      have hcfun := LinearMap.congr_fun hc x
      simpa [LinearMap.comp_apply] using hcfun
    change
      (maximalIdealPowTransition (A := A) (E := E) n)
          (((1 : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)) + c) x) =
        (maximalIdealPowTransition (A := A) (E := E) n) x
    simp [hcx]

/-- Helper for Exercise 15-15.5-3: once lifts of a downstairs automorphism and its inverse are
available upstairs, Serre's square-zero correction package turns them into a genuine upstairs
automorphism. -/
private theorem exists_linearEquiv_of_lifted_inverses
    (n : ℕ+)
    (u : E⧸𝔪^((n : ℕ))E ≃ₗ[A⧸𝔪^((n : ℕ))] E⧸𝔪^((n : ℕ))E)
    {L Linv : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)}
    (hL :
      (maximalIdealPowTransition (A := A) (E := E) n).comp (L.restrictScalars A) =
        (u.toLinearMap.restrictScalars A).comp
          (maximalIdealPowTransition (A := A) (E := E) n))
    (hLinv :
      (maximalIdealPowTransition (A := A) (E := E) n).comp (Linv.restrictScalars A) =
        (u.symm.toLinearMap.restrictScalars A).comp
          (maximalIdealPowTransition (A := A) (E := E) n)) :
    ∃ U : E⧸𝔪^((n : ℕ) + 1)E ≃ₗ[A⧸𝔪^((n : ℕ) + 1)] E⧸𝔪^((n : ℕ) + 1)E,
      U.toLinearMap = L ∧
        (maximalIdealPowTransition (A := A) (E := E) n).comp (U.toLinearMap.restrictScalars A) =
          (u.toLinearMap.restrictScalars A).comp
            (maximalIdealPowTransition (A := A) (E := E) n) := by
  let π := maximalIdealPowTransition (A := A) (E := E) n
  let c : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E) := L * Linv - 1
  let d : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E) := Linv * L - 1
  have hLLinv :
      π.comp ((L * Linv).restrictScalars A) = π := by
    -- The composite lift of `u` and `u⁻¹` reduces to the identity downstairs.
    apply LinearMap.ext
    intro x
    have hLx := LinearMap.congr_fun hL (Linv x)
    have hLinvx : π (Linv x) = u.symm.toLinearMap (π x) := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hLinv x
    calc
      π (((L * Linv) : Module.End _ _) x)
          = u.toLinearMap (π (Linv x)) := by
              simpa [LinearMap.comp_apply, Module.End.mul_apply] using hLx
      _ = u.toLinearMap (u.symm.toLinearMap (π x)) := by
            rw [hLinvx]
      _ = π x := by simp
  have hLinvL :
      π.comp ((Linv * L).restrictScalars A) = π := by
    -- The same reduction argument applied in the opposite order gives the other composite.
    apply LinearMap.ext
    intro x
    have hLinvx := LinearMap.congr_fun hLinv (L x)
    have hLx : π (L x) = u.toLinearMap (π x) := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hL x
    calc
      π (((Linv * L) : Module.End _ _) x)
          = u.symm.toLinearMap (π (L x)) := by
              simpa [LinearMap.comp_apply, Module.End.mul_apply] using hLinvx
      _ = u.symm.toLinearMap (u.toLinearMap (π x)) := by
            rw [hLx]
      _ = π x := by simp
  have hc :
      π.comp (c.restrictScalars A) = 0 := by
    -- Subtracting the lifted identity packages the first composite defect as a zero-reduction
    -- correction term.
    have hcomp :
        π.comp ((L * Linv).restrictScalars A) =
          π.comp ((1 : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)).restrictScalars A) := by
      simpa using hLLinv
    simpa [c] using
      transition_difference_reduces_to_zero
        (A := A) (E := E) (n := n) (U := L * Linv) (V := 1) hcomp
  have hd :
      π.comp (d.restrictScalars A) = 0 := by
    -- The opposite composite defect is handled identically.
    have hcomp :
        π.comp ((Linv * L).restrictScalars A) =
          π.comp ((1 : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)).restrictScalars A) := by
      simpa using hLinvL
    simpa [d] using
      transition_difference_reduces_to_zero
        (A := A) (E := E) (n := n) (U := Linv * L) (V := 1) hcomp
  have hcd : c * L = L * d := by
    -- Expanding the two defects shows they differ only by associativity of the lifted composites.
    apply LinearMap.ext
    intro x
    simp [c, d, Module.End.mul_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hshift : (1 - c) * L = L * (1 - d) := by
    -- This is the bridge that moves the correction from the left-composite defect to the
    -- right-composite defect.
    apply LinearMap.ext
    intro x
    have hcdx := LinearMap.congr_fun hcd x
    simp [Module.End.mul_apply] at hcdx ⊢
    rw [hcdx]
  have hone_add_c :
      (1 : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)) + c = L * Linv := by
    -- Record the canonical additive normal form of the first defect once, instead of asking `simp`
    -- to unfold it repeatedly through the endomorphism ring.
    dsimp [c]
    abel
  have hone_add_d :
      (1 : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)) + d = Linv * L := by
    -- The opposite composite defect has the same additive normal form.
    dsimp [d]
    abel
  have hright :
      L * (Linv * (1 - c)) = 1 := by
    -- Correct the right composite `L * Linv` by the square-zero inverse `1 - c`.
    calc
      L * (Linv * (1 - c)) = (L * Linv) * (1 - c) := by rw [mul_assoc]
      _ = ((1 : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)) + c) * (1 - c) := by
            rw [hone_add_c]
      _ = 1 := one_add_mul_one_sub_of_zero_reduction (A := A) (E := E) (n := n) hc
  have hleft :
      (Linv * (1 - c)) * L = 1 := by
    -- Move the correction term across `L`, then reduce the opposite composite defect.
    calc
      (Linv * (1 - c)) * L = Linv * ((1 - c) * L) := by rw [mul_assoc]
      _ = Linv * (L * (1 - d)) := by rw [hshift]
      _ = (Linv * L) * (1 - d) := by rw [← mul_assoc]
      _ = ((1 : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E)) + d) * (1 - d) := by
            rw [hone_add_d]
      _ = 1 := one_add_mul_one_sub_of_zero_reduction (A := A) (E := E) (n := n) hd
  refine ⟨LinearEquiv.ofLinear L (Linv * (1 - c)) hright hleft, rfl, ?_⟩
  -- The constructed equivalence uses `L` as its forward map, so it keeps the original reduction
  -- equation.
  simpa using hL

/-- Helper for Exercise 15-15.5-3: a single downstairs automorphism lifts across the transition
`E / 𝔪^(n+1) E → E / 𝔪^n E`. This is the preliminary-lift step before correcting the group law. -/
private theorem exists_linearEquiv_lift_of_transition
    (n : ℕ+)
    (u : E⧸𝔪^((n : ℕ))E ≃ₗ[A⧸𝔪^((n : ℕ))] E⧸𝔪^((n : ℕ))E) :
    ∃ U : E⧸𝔪^((n : ℕ) + 1)E ≃ₗ[A⧸𝔪^((n : ℕ) + 1)] E⧸𝔪^((n : ℕ) + 1)E,
      (maximalIdealPowTransition (A := A) (E := E) n).comp (U.toLinearMap.restrictScalars A) =
        (u.toLinearMap.restrictScalars A).comp
          (maximalIdealPowTransition (A := A) (E := E) n) := by
  -- Route correction: the scalar-tower surface is now fixed by
  -- `maximalIdealPowTransition_surjective_factorPowSucc`; the remaining task is to lift both
  -- `u` and `u⁻¹` as endomorphisms over `A⧸𝔪^(n+1)` and then close the source-faithful
  -- square-zero correction argument for their composites.
  let R1 := A⧸𝔪^((n : ℕ) + 1)
  letI : Module R1 (E⧸𝔪^((n : ℕ))E) :=
    Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
  obtain ⟨L, hL0⟩ :=
    exists_linearMap_lift_of_transition_factorPowSucc
      (A := A) (E := E) (n := n)
      (downstairs_endomorphism_over_factorPowSucc (A := A) (E := E) n u.toLinearMap)
  obtain ⟨Linv, hLinv0⟩ :=
    exists_linearMap_lift_of_transition_factorPowSucc
      (A := A) (E := E) (n := n)
      (downstairs_endomorphism_over_factorPowSucc (A := A) (E := E) n u.symm.toLinearMap)
  have hL :
      (maximalIdealPowTransition (A := A) (E := E) n).comp (L.restrictScalars A) =
        (u.toLinearMap.restrictScalars A).comp
          (maximalIdealPowTransition (A := A) (E := E) n) := by
    -- Forgetting the transported scalar structure recovers the original transition equation.
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun hL0 x
    simpa [LinearMap.comp_apply,
      maximalIdealPowTransition_linear_over_factorPowSucc_apply,
      downstairs_endomorphism_over_factorPowSucc_apply] using hx
  have hLinv :
      (maximalIdealPowTransition (A := A) (E := E) n).comp (Linv.restrictScalars A) =
        (u.symm.toLinearMap.restrictScalars A).comp
          (maximalIdealPowTransition (A := A) (E := E) n) := by
    -- The same normalization applies to the lifted inverse.
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun hLinv0 x
    simpa [LinearMap.comp_apply,
      maximalIdealPowTransition_linear_over_factorPowSucc_apply,
      downstairs_endomorphism_over_factorPowSucc_apply] using hx
  obtain ⟨U, -, hU⟩ :=
    exists_linearEquiv_of_lifted_inverses
      (A := A) (E := E) (n := n) u hL hLinv
  exact ⟨U, hU⟩

/-- Helper for Exercise 15-15.5-3: Serre's part `(a)` existence step, isolated to the finite-level
square-zero/prelift package on `E / 𝔪^(n+1) E → E / 𝔪^n E`. -/
private theorem exists_lift_of_maximalIdealPowLevel_via_square_zero_package
    (hG : ¬ p ∣ Nat.card G)
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E)) :
    ∃ ρn1 : Representation (A⧸𝔪^((n : ℕ) + 1)) G (E⧸𝔪^((n : ℕ) + 1)E),
      (ρn1.restrictScalars A).IsIntertwiningMap
        (ρn.restrictScalars A)
        (maximalIdealPowTransition n) := by
  -- Route correction: the preliminary automorphism lifts and the square-zero correction algebra are
  -- now in place locally. The remaining gap is the final averaged `H²` correction step.
  -- TODO: after proving `exists_linearEquiv_lift_of_transition`, choose preliminary lifts `U g`,
  -- form the normalized defect cocycle
  -- `a g h = U g * U h * (U (g * h)).symm - 1`, and average it in the square-zero correction
  -- algebra to repair the group law.
  sorry

/-- Helper for Exercise 15-15.5-3: Serre's part `(a)` uniqueness step, isolated to the
square-zero comparison-cocycle package on the same finite-level tower. -/
private theorem lift_of_maximalIdealPowLevel_unique_up_to_conjugation_via_square_zero_package
    (hG : ¬ p ∣ Nat.card G)
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E))
    (ρn1 ρn1' : Representation (A⧸𝔪^((n : ℕ) + 1)) G (E⧸𝔪^((n : ℕ) + 1)E))
    (hρn1 :
      (ρn1.restrictScalars A).IsIntertwiningMap
        (ρn.restrictScalars A)
        (maximalIdealPowTransition n))
    (hρn1' :
      (ρn1'.restrictScalars A).IsIntertwiningMap
        (ρn.restrictScalars A)
        (maximalIdealPowTransition n)) :
    let π := maximalIdealPowTransition n
    ∃ u : ρn1.Equiv ρn1',
      π ∘ₗ (u.toLinearMap.restrictScalars A) = π := by
  -- TODO: express the comparison term
  -- `a g = ρn1' g * (ρn1 g).symm - 1` as a zero-reduction `1`-cocycle in the proved square-zero
  -- correction algebra, average it to a coboundary, and convert the resulting correction into the
  -- conjugating automorphism via `exists_linearEquiv_one_add_of_zero_reduction`.
  sorry

-- Proof sketch: the obstruction to extending `ρn` from level `n` to level `n + 1` lies in a
-- second cohomology group of `G` with coefficients in `End(E / 𝔪E)`, and that cohomology group
-- vanishes when `|G|` is prime to `p`.
/-- Exercise 15-15.5-3 (1): if `|G|` is prime to `p`, every representation of `G` on the
`n`-th reduction of a finite free `A`-module `E` with `n ≥ 1` lifts to a representation on the
next reduction `E / 𝔪^(n+1) E`. -/
theorem exists_lift_of_maximalIdealPowLevel
    (hG : ¬ p ∣ Nat.card G)
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E)) :
    ∃ ρn1 : Representation (A⧸𝔪^((n : ℕ) + 1)) G (E⧸𝔪^((n : ℕ) + 1)E),
      (ρn1.restrictScalars A).IsIntertwiningMap
        (ρn.restrictScalars A)
        (maximalIdealPowTransition n) :=
  exists_lift_of_maximalIdealPowLevel_via_square_zero_package
    (A := A) (p := p) (G := G) (E := E) hG n ρn

-- Proof sketch: the vanishing of the first cohomology group identifies any two lifts as differing
-- by a coboundary, which is exactly conjugation by an automorphism reducing to the identity modulo
-- `𝔪^n`.
/-- Exercise 15-15.5-3 (2): if `|G|` is prime to `p`, two lifts of the same representation on the
`n`-th reduction of a finite free `A`-module are conjugate on `E / 𝔪^(n+1) E` by an automorphism
congruent to the identity modulo `𝔪^n`. -/
theorem lift_of_maximalIdealPowLevel_unique_up_to_conjugation
    (hG : ¬ p ∣ Nat.card G)
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E))
    (ρn1 ρn1' : Representation (A⧸𝔪^((n : ℕ) + 1)) G (E⧸𝔪^((n : ℕ) + 1)E))
    (hρn1 :
      (ρn1.restrictScalars A).IsIntertwiningMap
        (ρn.restrictScalars A)
        (maximalIdealPowTransition n))
    (hρn1' :
      (ρn1'.restrictScalars A).IsIntertwiningMap
        (ρn.restrictScalars A)
        (maximalIdealPowTransition n)) :
    let π := maximalIdealPowTransition n
    ∃ u : ρn1.Equiv ρn1',
      π ∘ₗ (u.toLinearMap.restrictScalars A) = π :=
  lift_of_maximalIdealPowLevel_unique_up_to_conjugation_via_square_zero_package
    (A := A) (p := p) (G := G) (E := E) hG n ρn ρn1 ρn1' hρn1 hρn1'

end

noncomputable section

variable {A : Type u} [CommRing A] [HenselianLocalRing A]
variable {p : ℕ}
variable [CharP (IsLocalRing.ResidueField A) p]
variable {G : Type u} [Group G] [Finite G]
variable {V : Type x} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]
variable [FiniteDimensional (IsLocalRing.ResidueField A) V]

local notation "k" => IsLocalRing.ResidueField A
noncomputable local instance : Module A k :=
  Module.compHom k (algebraMap A k)
local instance : IsScalarTower A k k :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
noncomputable local instance : Module A V :=
  Module.compHom V (algebraMap A k)
local instance : IsScalarTower A k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Exercise 15-15.5-3: after restricting the reduced `k[G]`-action along
`A[G] → k[G]`, a residue-field reduction map is automatically `A[G]`-linear. -/
private theorem map_smul_of_isResidueFieldReduction
    {P : Type*} [AddCommGroup P] [Module A P] [Module A[G] P]
    [IsScalarTower A A[G] P]
    [Module k[G] V] [IsScalarTower k k[G] V]
    {f : P →ₗ[A] V} (hf : f.IsResidueFieldReduction G)
    (a : A[G]) (x : P) :
    letI : Module A[G] V :=
      Module.compHom V (MonoidAlgebra.mapRingHom G (algebraMap A k))
    letI : IsScalarTower A A[G] V :=
      IsScalarTower.of_algebraMap_smul fun c y ↦ by
        change
          (MonoidAlgebra.mapRingHom G (algebraMap A k))
              (MonoidAlgebra.single (1 : G) c) • y =
            c • y
        rw [MonoidAlgebra.mapRingHom_single]
        have hsingle :
            MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) =
              algebraMap k k[G] (IsLocalRing.residue A c) := by
          rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
          simp
        calc
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) • y
              = (IsLocalRing.residue A c) • y := by
                  simpa only [hsingle] using
                    (IsScalarTower.algebraMap_smul k[G] (IsLocalRing.residue A c) y)
          _ = c • y := by
                simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                  (IsScalarTower.algebraMap_smul k c y)
    f (a • x) = a • f x := by
  letI : Module A[G] V := Module.compHom V (MonoidAlgebra.mapRingHom G (algebraMap A k))
  letI : IsScalarTower A A[G] V :=
    IsScalarTower.of_algebraMap_smul fun c y ↦ by
      change
        (MonoidAlgebra.mapRingHom G (algebraMap A k))
            (MonoidAlgebra.single (1 : G) c) • y =
          c • y
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) =
            algebraMap k k[G] (IsLocalRing.residue A c) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) • y
            = (IsLocalRing.residue A c) • y := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul k[G] (IsLocalRing.residue A c) y)
        _ = c • y := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul k c y)
  -- Check equivariance first on `MonoidAlgebra.of`, then extend linearly in the group algebra.
  refine MonoidAlgebra.induction_on (p := fun b : A[G] => f (b • x) = b • f x) a ?_ ?_ ?_
  · intro g
    change f (MonoidAlgebra.of A G g • x) =
      (MonoidAlgebra.mapRingHom G (algebraMap A k)) (MonoidAlgebra.of A G g) • f x
    simpa [MonoidAlgebra.of_apply] using
      LinearMap.IsResidueFieldReduction.map_monoidAlgebra_of hf g x
  · intro a b ha hb
    simp [add_smul, ha, hb]
  · intro c a ha
    simpa [smul_smul] using congrArg (fun y ↦ c • y) ha

/-- Helper for Exercise 15-15.5-3: package a residue-field reduction as an `A[G]`-linear map by
restricting the reduced `k[G]`-action along `A[G] → k[G]`. -/
private noncomputable def to_groupAlgebraLinearMap_of_isResidueFieldReduction
    {P : Type*} [AddCommGroup P] [Module A P] [Module A[G] P]
    [IsScalarTower A A[G] P]
    [Module k[G] V] [IsScalarTower k k[G] V]
    {f : P →ₗ[A] V} (hf : f.IsResidueFieldReduction G) :
    letI : Module A[G] V := Module.compHom V (MonoidAlgebra.mapRingHom G (algebraMap A k))
    letI : IsScalarTower A A[G] V :=
      IsScalarTower.of_algebraMap_smul fun c y ↦ by
        change
          (MonoidAlgebra.mapRingHom G (algebraMap A k))
              (MonoidAlgebra.single (1 : G) c) • y =
            c • y
        rw [MonoidAlgebra.mapRingHom_single]
        have hsingle :
            MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) =
              algebraMap k k[G] (IsLocalRing.residue A c) := by
          rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
          simp
        calc
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) • y
              = (IsLocalRing.residue A c) • y := by
                  simpa only [hsingle] using
                    (IsScalarTower.algebraMap_smul k[G] (IsLocalRing.residue A c) y)
          _ = c • y := by
                simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                  (IsScalarTower.algebraMap_smul k c y)
    P →ₗ[A[G]] V := by
  letI : Module A[G] V := Module.compHom V (MonoidAlgebra.mapRingHom G (algebraMap A k))
  letI : IsScalarTower A A[G] V :=
    IsScalarTower.of_algebraMap_smul fun c y ↦ by
      change
        (MonoidAlgebra.mapRingHom G (algebraMap A k))
            (MonoidAlgebra.single (1 : G) c) • y =
          c • y
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) =
            algebraMap k k[G] (IsLocalRing.residue A c) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) • y
            = (IsLocalRing.residue A c) • y := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul k[G] (IsLocalRing.residue A c) y)
        _ = c • y := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul k c y)
  exact
    { toFun := f
      map_add' := f.map_add
      map_smul' := map_smul_of_isResidueFieldReduction (A := A) (G := G) (V := V) hf }

/-- Helper for Exercise 15-15.5-3: a residue-field reduction map is surjective because every
element of the residue module is built from reduced scalars and images of source vectors. -/
private theorem surjective_of_isResidueFieldReduction
    {P : Type*} [AddCommGroup P] [Module A P] [Module A[G] P]
    [IsScalarTower A A[G] P]
    [Module k[G] V] [IsScalarTower k k[G] V]
    {f : P →ₗ[A] V} (hf : f.IsResidueFieldReduction G) :
    Function.Surjective f := by
  -- Use the tensor-product induction principle hidden inside `IsBaseChange`.
  intro y
  refine hf.1.inductionOn (motive := fun z : V ↦ ∃ a, f a = z) y ?_ ?_ ?_ ?_
  · exact ⟨0, by simp⟩
  · intro x
    exact ⟨x, rfl⟩
  · intro a y hy
    rcases hy with ⟨x, rfl⟩
    rcases Ideal.Quotient.mk_surjective a with ⟨b, hb⟩
    refine ⟨b • x, ?_⟩
    calc
      f (b • x) = b • f x := by simpa using f.map_smul b x
      _ = a • f x := by simpa [IsLocalRing.ResidueField.algebraMap_eq] using congrArg (fun c : k ↦ c • f x) hb
  · intro y z hy hz
    rcases hy with ⟨x, rfl⟩
    rcases hz with ⟨w, rfl⟩
    refine ⟨x + w, by simp⟩

/-- Helper for Exercise 15-15.5-3: postcomposing the canonical reduction map with a reduced
`k[G]`-linear equivalence keeps the same residue-field reduction structure. -/
private theorem isResidueFieldReduction_of_equiv_target
    {P : Type*} [AddCommGroup P] [Module A P] [Module A[G] P]
    [IsScalarTower A A[G] P]
    [Module k[G] V] [IsScalarTower k k[G] V]
    {V' : Type*} [AddCommGroup V'] [Module k V'] [Module k[G] V']
    [IsScalarTower k k[G] V']
    {f : P →ₗ[A] V'} (hf : f.IsResidueFieldReduction G)
    (e : V' ≃ₗ[k[G]] V) :
    (((e.restrictScalars k).toLinearMap.restrictScalars A).comp f).IsResidueFieldReduction G := by
  letI : Module A[G] V' := Module.compHom V' (MonoidAlgebra.mapRingHom G (algebraMap A k))
  letI : IsScalarTower A A[G] V' :=
    IsScalarTower.of_algebraMap_smul fun c y ↦ by
      change
        (MonoidAlgebra.mapRingHom G (algebraMap A k))
            (MonoidAlgebra.single (1 : G) c) • y =
          c • y
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) =
            algebraMap k k[G] (IsLocalRing.residue A c) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) • y
            = (IsLocalRing.residue A c) • y := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul k[G] (IsLocalRing.residue A c) y)
        _ = c • y := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul k c y)
  letI : Module A[G] V := Module.compHom V (MonoidAlgebra.mapRingHom G (algebraMap A k))
  letI : IsScalarTower A A[G] V :=
    IsScalarTower.of_algebraMap_smul fun c y ↦ by
      change
        (MonoidAlgebra.mapRingHom G (algebraMap A k))
            (MonoidAlgebra.single (1 : G) c) • y =
          c • y
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) =
            algebraMap k k[G] (IsLocalRing.residue A c) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) • y
            = (IsLocalRing.residue A c) • y := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul k[G] (IsLocalRing.residue A c) y)
        _ = c • y := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul k c y)
  constructor
  · -- Only the target realization changes; the tensor-product base-change witness transports
    -- directly along the chosen reduced equivalence.
    refine IsBaseChange.of_equiv (hf.1.equiv ≪≫ₗ e.restrictScalars k) ?_
    intro x
    simpa [LinearMap.comp_apply] using congrArg e (hf.1.equiv_tmul x)
  · -- Re-express equivariance on the group generators, then postcompose by the reduced
    -- `k[G]`-linear equivalence.
    refine Representation.IsIntertwiningMap.mk ?_
    intro g x
    calc
      (((e.restrictScalars k).toLinearMap.restrictScalars A).comp f)
          (MonoidAlgebra.of A G g • x)
        = e (MonoidAlgebra.of k G g • f x) := by
            change e (f (MonoidAlgebra.of A G g • x)) = _
            rw [LinearMap.IsResidueFieldReduction.map_monoidAlgebra_of hf g x]
      _ = MonoidAlgebra.of k G g • e (f x) := by
            simpa using e.map_smul (MonoidAlgebra.of k G g) (f x)
      _ = (MonoidAlgebra.mapRingHom G (algebraMap A k) (MonoidAlgebra.of A G g)) •
            e (f x) := by
            simp [MonoidAlgebra.of_apply]
      _ = MonoidAlgebra.of A G g •
            (((e.restrictScalars k).toLinearMap.restrictScalars A).comp f x) := by
            rfl

/-- Helper for Exercise 15-15.5-3: over the residue field, Maschke's theorem makes every
`k[G]`-module projective when `|G|` is prime to `p`. -/
private theorem residue_groupAlgebra_module_projective_of_order_prime_to_p
    (hG : ¬ p ∣ Nat.card G)
    {M : Type*} [AddCommGroup M] [Module k[G] M] :
    Module.Projective k[G] M := by
  let _ : Fintype G := Fintype.ofFinite G
  -- The source-facing prime-to-`p` hypothesis turns into semisimplicity of the group algebra.
  let _ : NeZero (Nat.card G : k) := NeZero.of_not_dvd k hG
  let _ : IsSemisimpleRing k[G] := by
    infer_instance
  exact Module.projective_of_isSemisimpleRing k[G] M

/-- Helper for Exercise 15-15.5-3: if two free `A`-lifts reduce to the same `k`-representation,
then the Chapter `14` projective comparison can be specialized to an equivariant isomorphism whose
reduction is exactly the identity on the common residue representation. -/
theorem equiv_of_common_residue_reduction_identity
    (hG : ¬ p ∣ Nat.card G)
    (ρl : Representation k G V)
    {P₁ : Type y} [AddCommGroup P₁] [Module A P₁] [Module.Free A P₁] [Module.Finite A P₁]
    (ρA₁ : Representation A G P₁)
    (red₁ : P₁ →ₗ[A] V)
    (hρA₁ : IsResidueFieldLift ρl ρA₁ red₁)
    {P₂ : Type y} [AddCommGroup P₂] [Module A P₂] [Module.Free A P₂] [Module.Finite A P₂]
    (ρA₂ : Representation A G P₂)
    (red₂ : P₂ →ₗ[A] V)
    (hρA₂ : IsResidueFieldLift ρl ρA₂ red₂) :
    ∃ e : ρA₁.Equiv ρA₂,
      red₂.comp e.toLinearMap = red₁ := by
  letI : Module A[G] P₁ := Module.compHom P₁ ρA₁.asAlgebraHom.toRingHom
  letI : IsScalarTower A A[G] P₁ :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρA₁.asAlgebraHom (algebraMap A A[G] a) x = a • x
      simp [Algebra.smul_def]
  letI : Module A[G] P₂ := Module.compHom P₂ ρA₂.asAlgebraHom.toRingHom
  letI : IsScalarTower A A[G] P₂ :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρA₂.asAlgebraHom (algebraMap A A[G] a) x = a • x
      simp [Algebra.smul_def]
  letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
  letI : IsScalarTower k k[G] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
      simp [Algebra.smul_def]
  letI : Module A[G] V := Module.compHom V (MonoidAlgebra.mapRingHom G (algebraMap A k))
  letI : IsScalarTower A A[G] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change
        (MonoidAlgebra.mapRingHom G (algebraMap A k))
            (MonoidAlgebra.single (1 : G) a) • x =
          a • x
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) =
            algebraMap k k[G] (IsLocalRing.residue A a) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) • x
            = (IsLocalRing.residue A a) • x := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul k[G] (IsLocalRing.residue A a) x)
        _ = a • x := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul k a x)
  have hred₁ : red₁.IsResidueFieldReduction G := by
    -- Unpack the source-facing lift hypothesis into the Chapter `14` reduction owner.
    simpa [IsResidueFieldLift] using hρA₁
  have hred₂ : red₂.IsResidueFieldReduction G := by
    -- The second lift supplies the same owner-level reduction data.
    simpa [IsResidueFieldLift] using hρA₂
  have hP₁ : Module.Projective A[G] P₁ :=
    free_groupAlgebra_module_projective_of_order_prime_to_p
      (A := A) (p := p) (G := G) (P := P₁) hG
  have hP₂ : Module.Projective A[G] P₂ :=
    free_groupAlgebra_module_projective_of_order_prime_to_p
      (A := A) (p := p) (G := G) (P := P₂) hG
  let f₁ : P₁ →ₗ[A[G]] V :=
    to_groupAlgebraLinearMap_of_isResidueFieldReduction
      (A := A) (G := G) (V := V) hred₁
  let f₂ : P₂ →ₗ[A[G]] V :=
    to_groupAlgebraLinearMap_of_isResidueFieldReduction
      (A := A) (G := G) (V := V) hred₂
  have hsurj₂ : Function.Surjective f₂ := by
    -- Forgetting the `A[G]`-linearity does not change the underlying surjective function.
    intro y
    rcases surjective_of_isResidueFieldReduction (A := A) (G := G) (V := V) hred₂ y with ⟨x, hx⟩
    exact ⟨x, hx⟩
  have hsurj₁ : Function.Surjective f₁ := by
    -- The same argument applies to the first reduction map.
    intro y
    rcases surjective_of_isResidueFieldReduction (A := A) (G := G) (V := V) hred₁ y with ⟨x, hx⟩
    exact ⟨x, hx⟩
  -- Lift the identity reduced map `red₁` across `red₂`.
  obtain ⟨w, hw⟩ := Module.projective_lifting_property f₂ f₁ hsurj₂
  -- Symmetrically lift `red₂` back across `red₁`.
  obtain ⟨w', hw'⟩ := Module.projective_lifting_property f₁ f₂ hsurj₁
  let u : Module.End A P₁ := (w'.restrictScalars A).comp (w.restrictScalars A)
  let u' : Module.End A P₂ := (w.restrictScalars A).comp (w'.restrictScalars A)
  have hu_red : hred₁.1.endHom u = LinearMap.id := by
    -- The composite `w' ∘ w` reduces to the identity because both lifts realize the identity on
    -- the common residue representation.
    apply hred₁.1.algHom_ext'
    ext x
    have hwx : red₂ (w x) = red₁ x := by
      have hwx' := LinearMap.congr_fun hw x
      simpa [f₁, f₂, to_groupAlgebraLinearMap_of_isResidueFieldReduction] using hwx'
    have hw'x (y : P₂) : red₁ (w' y) = red₂ y := by
      have hw'y := LinearMap.congr_fun hw' y
      simpa [f₁, f₂, to_groupAlgebraLinearMap_of_isResidueFieldReduction] using hw'y
    calc
      (hred₁.1.endHom u) (red₁ x) = red₁ (u x) := by
        simpa [u] using hred₁.1.endHom_comp_apply u x
      _ = red₁ (w' (w x)) := rfl
      _ = red₂ (w x) := by simpa using hw'x (w x)
      _ = red₁ x := hwx
      _ = (LinearMap.id : V →ₗ[k] V) (red₁ x) := rfl
  have hu'_red : hred₂.1.endHom u' = LinearMap.id := by
    -- The symmetric composite `w ∘ w'` has the same reduced identity property.
    apply hred₂.1.algHom_ext'
    ext x
    have hwx (y : P₁) : red₂ (w y) = red₁ y := by
      have hwy := LinearMap.congr_fun hw y
      simpa [f₁, f₂, to_groupAlgebraLinearMap_of_isResidueFieldReduction] using hwy
    have hw'x : red₁ (w' x) = red₂ x := by
      have hw'x' := LinearMap.congr_fun hw' x
      simpa [f₁, f₂, to_groupAlgebraLinearMap_of_isResidueFieldReduction] using hw'x'
    calc
      (hred₂.1.endHom u') (red₂ x) = red₂ (u' x) := by
        simpa [u'] using hred₂.1.endHom_comp_apply u' x
      _ = red₂ (w (w' x)) := rfl
      _ = red₁ (w' x) := by simpa using hwx (w' x)
      _ = red₂ x := hw'x
      _ = (LinearMap.id : V →ₗ[k] V) (red₂ x) := rfl
  have hu_unit : IsUnit u :=
    hred₁.endomorphism_isUnit_of_endHom_eq_id u hu_red
  have hu'_unit : IsUnit u' :=
    hred₂.endomorphism_isUnit_of_endHom_eq_id u' hu'_red
  have hu_bij : Function.Bijective u :=
    (Module.End.isUnit_iff u).mp hu_unit
  have hu'_bij : Function.Bijective u' :=
    (Module.End.isUnit_iff u').mp hu'_unit
  have hw_injective : Function.Injective w := by
    -- Injectivity follows because `u = w' ∘ w` is already invertible.
    intro x y hxy
    apply hu_bij.1
    simpa [u, hxy]
  have hw_surjective : Function.Surjective w := by
    -- Surjectivity is obtained from invertibility of the symmetric composite `u'`.
    intro y
    rcases hu'_bij.2 y with ⟨z, hz⟩
    refine ⟨w' z, ?_⟩
    simpa [u'] using hz
  let eLin : P₁ ≃ₗ[A[G]] P₂ := LinearEquiv.ofBijective w ⟨hw_injective, hw_surjective⟩
  let e : ρA₁.Equiv ρA₂ := by
    refine Representation.Equiv.mk (eLin.restrictScalars A) ?_
    intro g
    ext x
    -- The recovered `A[G]`-linear equivalence is automatically equivariant on the group
    -- generators.
    have hsrc : (MonoidAlgebra.single g (1 : A)) • x = ρA₁ g x := by
      show ρA₁.asAlgebraHom (MonoidAlgebra.single g 1) x = _
      simp [Representation.asAlgebraHom_single]
    have htgt : (MonoidAlgebra.single g (1 : A)) • eLin x = ρA₂ g (eLin x) := by
      show ρA₂.asAlgebraHom (MonoidAlgebra.single g 1) (eLin x) = _
      simp [Representation.asAlgebraHom_single]
    calc
      eLin (ρA₁ g x) = eLin ((MonoidAlgebra.single g (1 : A)) • x) := by rw [← hsrc]
      _ = (MonoidAlgebra.single g (1 : A)) • eLin x := by
            simpa using eLin.map_smul (MonoidAlgebra.single g (1 : A)) x
      _ = ρA₂ g (eLin x) := htgt
  refine ⟨e, ?_⟩
  -- By construction, the lifted map reduces to the identity on the common residue module.
  ext x
  have hwx := LinearMap.congr_fun hw x
  simpa [e, eLin, f₁, f₂, to_groupAlgebraLinearMap_of_isResidueFieldReduction] using hwx

/-- Helper for Exercise 15-15.5-3: the tautological owner module `ρl.asModule` identifies
`k[G]`-linearly with the original representation space `V`. This is the transport bridge needed
to compare any lifted reduced owner with the source-facing representation. -/
private theorem nonempty_asModuleLinearEquiv_target
    (ρl : Representation k G V) :
    letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
    letI : IsScalarTower k k[G] V :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
        simp [Algebra.smul_def]
    Nonempty (ρl.asModule ≃ₗ[k[G]] V) := by
  letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
  letI : IsScalarTower k k[G] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
      simp [Algebra.smul_def]
  refine ⟨
    { toFun := fun x ↦ ρl.asModuleEquiv x
      invFun := fun x ↦ ρl.asModuleEquiv.symm x
      left_inv := fun x ↦ ρl.asModuleEquiv.symm_apply_apply x
      right_inv := fun x ↦ ρl.asModuleEquiv.apply_symm_apply x
      map_add' := fun x y ↦ ρl.asModuleEquiv.map_add x y
      map_smul' := ?_ }⟩
  intro a x
  -- Transport the `k[G]`-action through `asModuleEquiv`, then read it as the original action on
  -- `V`.
  calc
    ρl.asModuleEquiv (a • x) = ρl.asAlgebraHom a (ρl.asModuleEquiv x) := by
      simpa using Representation.asModuleEquiv_map_smul (ρ := ρl) a x
    _ = a • ρl.asModuleEquiv x := rfl

/-- Helper for Exercise 15-15.5-3: when `|G|` is prime to `p`, the source-facing carrier `V`
itself becomes a finite projective `k[G]`-module after exposing the action of `ρl`. -/
private theorem target_module_finite_projective_of_order_prime_to_p
    (hG : ¬ p ∣ Nat.card G)
    (ρl : Representation k G V) :
    letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
    letI : IsScalarTower k k[G] V :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
        simp [Algebra.smul_def]
    Module.Projective k[G] V ∧ Module.Finite k[G] V := by
  letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
  letI : IsScalarTower k k[G] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
      simp [Algebra.smul_def]
  constructor
  · -- Maschke's theorem gives projectivity for the reduced `k[G]`-module.
    exact residue_groupAlgebra_module_projective_of_order_prime_to_p (A := A) (p := p) hG
  · -- Finite-dimensionality over `k` makes the same carrier finite over `k[G]`.
    exact Module.Finite.of_restrictScalars_finite k k[G] V

/-- Helper for Exercise 15-15.5-3: a representation equivalence yields a `k[G]`-linear
equivalence of the corresponding owner modules. -/
private noncomputable def representationEquiv_asModuleLinearEquiv
    {V' : Type*} [AddCommGroup V'] [Module k V']
    {W' : Type*} [AddCommGroup W'] [Module k W']
    {ρ : Representation k G V'} {σ : Representation k G W'}
    (e : ρ.Equiv σ) :
    ρ.asModule ≃ₗ[k[G]] σ.asModule := by
  refine
    { toFun := (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ) e.toIntertwiningMap
      invFun := (Representation.IntertwiningMap.equivLinearMapAsModule σ ρ) e.symm.toIntertwiningMap
      left_inv := by
        -- The inverse owner map is induced by the inverse representation equivalence.
        intro x
        change e.symm (e x) = x
        simp
      right_inv := by
        -- The same argument works in the opposite direction.
        intro x
        change e (e.symm x) = x
        simp
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro a x
        simp }

/-- Helper for Exercise 15-15.5-3: the Chapter `14` isomorphism
`Q.residueFieldReduction ≅ F` can be consumed once as a concrete reduced `k[G]`-linear
equivalence, so later part `(b)` proofs do not need to reopen the owner/category layer. -/
private theorem residueFieldReduction_nonempty_linearEquiv_of_nonempty_iso
    (F : FiniteProjectiveGroupAlgebraModule k G)
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (hQ : Nonempty (Q.residueFieldReduction ≅ F)) :
    Nonempty (Q.residueFieldReduction.V ≃ₗ[k[G]] F.V) := by
  -- Re-express the owner isomorphism as a `k[G]`-linear equivalence of the reduced modules.
  exact
    (finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
      (A := k) (G := G) Q.residueFieldReduction F).1 hQ

/-- Helper for Exercise 15-15.5-3: the same-universe coordinate model, its projective owner, and
the lifted owner over `A` compile to a single reduced `k[G]`-linear equivalence back to the
original target space `V`. -/
private theorem same_universe_owner_compiled_reduced_equiv
    {W : Type u} [AddCommGroup W] [Module k W]
    {ρl : Representation k G V}
    (ρW : Representation k G W)
    [FiniteDimensional k W]
    (eW : ρW.Equiv ρl)
    (F : FiniteProjectiveGroupAlgebraModule k G)
    (hF :
      letI : Module k[G] W := Module.compHom W ρW.asAlgebraHom.toRingHom
      letI : IsScalarTower k k[G] W :=
        IsScalarTower.of_algebraMap_smul fun a x ↦ by
          change ρW.asAlgebraHom (algebraMap k k[G] a) x = a • x
          simp [Algebra.smul_def]
      Nonempty (F.V ≃ₗ[k[G]] W))
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (hQ : Nonempty (Q.residueFieldReduction ≅ F)) :
    letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
    letI : IsScalarTower k k[G] V :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
        simp [Algebra.smul_def]
    Nonempty (Q.residueFieldReduction.V ≃ₗ[k[G]] V) := by
  letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
  letI : IsScalarTower k k[G] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
      simp [Algebra.smul_def]
  letI : Module k[G] W := Module.compHom W ρW.asAlgebraHom.toRingHom
  letI : IsScalarTower k k[G] W :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρW.asAlgebraHom (algebraMap k k[G] a) x = a • x
      simp [Algebra.smul_def]
  rcases residueFieldReduction_nonempty_linearEquiv_of_nonempty_iso
      (A := A) (G := G) (F := F) (Q := Q) hQ with ⟨eQF⟩
  rcases hF with ⟨eFW⟩
  have hW :
      letI : Module k[G] W := Module.compHom W ρW.asAlgebraHom.toRingHom
      letI : IsScalarTower k k[G] W :=
        IsScalarTower.of_algebraMap_smul fun a x ↦ by
          change ρW.asAlgebraHom (algebraMap k k[G] a) x = a • x
          simp [Algebra.smul_def]
      Nonempty (ρW.asModule ≃ₗ[k[G]] W) :=
    nonempty_asModuleLinearEquiv_target (A := A) (G := G) (V := W) ρW
  rcases hW with ⟨eWmod⟩
  have hV :
      letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
      letI : IsScalarTower k k[G] V :=
        IsScalarTower.of_algebraMap_smul fun a x ↦ by
          change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
          simp [Algebra.smul_def]
      Nonempty (ρl.asModule ≃ₗ[k[G]] V) :=
    nonempty_asModuleLinearEquiv_target (A := A) (G := G) (V := V) ρl
  rcases hV with ⟨eV⟩
  -- Compose the reduced owner equivalence with the coordinate-model bridge and the original
  -- representation equivalence.
  exact
    ⟨eQF.trans
      (eFW.trans
        (eWmod.symm.trans
          ((representationEquiv_asModuleLinearEquiv (ρ := ρW) (σ := ρl) eW).trans eV)))⟩

/-- Helper for Exercise 15-15.5-3: the Chapter `14` projective-lift owner can be consumed on the
current source import surface without introducing a second local wrapper family. -/
private theorem chapter14_projective_lift_surface
    (F : FiniteProjectiveGroupAlgebraModule k G) :
    ∃ Q : FiniteProjectiveGroupAlgebraModule A G,
      Nonempty (Q.residueFieldReduction ≅ F) := by
  -- Part `(b)` only needs the existing Chapter `14` projective-lift owner on the current import
  -- surface, so reuse it directly instead of rebuilding a parallel wrapper.
  simpa using
    Representation.exists_projective_lift_of_residueField_projective
      (A := A) (G := G) F

/-- Helper for Exercise 15-15.5-3: package the same-universe coordinate model, its projective
owner, and the Chapter `14` lift into one owner `Q` whose reduction is already identified with the
original residue representation space `V`. -/
private theorem exists_owner_lift_with_compiled_reduced_equiv
    (hG : ¬ p ∣ Nat.card G)
    (ρl : Representation k G V) :
    letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
    letI : IsScalarTower k k[G] V :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
        simp [Algebra.smul_def]
    ∃ Q : FiniteProjectiveGroupAlgebraModule A G,
      Nonempty (Q.residueFieldReduction.V ≃ₗ[k[G]] V) := by
  letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
  letI : IsScalarTower k k[G] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
      simp [Algebra.smul_def]
  -- Hide the coordinate carrier inside the same-universe model so the theorem surface never has to
  -- synthesize its `k[G]`-module structure again.
  have hmodel := Representation.exists_same_universe_finite_rep_model ρl
  rcases hmodel with ⟨ρW, ⟨eW⟩⟩
  letI : Module k k := Semiring.toModule
  letI : Module k (Fin (Module.finrank k V) → k) :=
    Pi.Function.module (Fin (Module.finrank k V)) k k
  letI : Module k[G] (Fin (Module.finrank k V) → k) :=
    Module.compHom (Fin (Module.finrank k V) → k) ρW.asAlgebraHom.toRingHom
  letI : IsScalarTower k k[G] (Fin (Module.finrank k V) → k) :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρW.asAlgebraHom (algebraMap k k[G] a) x = a • x
      simp [Algebra.smul_def]
  have hprojW :
      Module.Projective k[G] (Fin (Module.finrank k V) → k) ∧
        Module.Finite k[G] (Fin (Module.finrank k V) → k) :=
    target_module_finite_projective_of_order_prime_to_p
      (A := A) (p := p) (G := G) (V := Fin (Module.finrank k V) → k) hG ρW
  rcases hprojW with ⟨hprojW, hfinW⟩
  letI : Module.Projective k[G] (Fin (Module.finrank k V) → k) := hprojW
  letI : Module.Finite k[G] (Fin (Module.finrank k V) → k) := hfinW
  -- Build the projective owner of the coordinate model once and lift it through Chapter `14`.
  obtain ⟨F, hF⟩ := (Representation.same_universe_model_finiteProjective_owner :
    ∃ F : FiniteProjectiveGroupAlgebraModule k G,
      Nonempty (F.V ≃ₗ[k[G]] (Fin (Module.finrank k V) → k)))
  rcases chapter14_projective_lift_surface (A := A) (G := G) F with ⟨Q, hQ⟩
  -- Compile the reduced owner equivalence back to the original residue representation space.
  refine ⟨Q, ?_⟩
  simpa using
    (same_universe_owner_compiled_reduced_equiv
      (A := A) (G := G) (V := V) (ρl := ρl) ρW eW F hF Q hQ)

/-- Helper for Exercise 15-15.5-3: the intrinsic tensor-product reduction map on a finite
projective owner already gives the raw owner-side residue-field reduction
`Q.V → Q.residueFieldReduction.V`. -/
private theorem owner_exists_tensorProduct_mk_isResidueFieldReduction
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    ∃ redQ : (Q.V : Type u) →ₗ[A] (Q.residueFieldReduction.V : Type u),
      redQ.IsResidueFieldReduction G := by
  letI : Module k Q.residueFieldReduction.V :=
    Module.compHom Q.residueFieldReduction.V (algebraMap k k[G])
  letI : IsScalarTower k k[G] Q.residueFieldReduction.V :=
    IsScalarTower.of_compHom k k[G] Q.residueFieldReduction.V
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (Q.V : Type u)) := TensorProduct.leftModule
  letI : IsScalarTower A k (TensorProduct A k (Q.V : Type u)) :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · simp
      · intro z y
        simp [IsLocalRing.ResidueField.algebraMap_eq, Algebra.smul_def, TensorProduct.smul_tmul']
      · intro x₁ x₂ hx₁ hx₂
        rw [smul_add, smul_add, hx₁, hx₂]
  let redQ : (Q.V : Type u) →ₗ[A] (Q.residueFieldReduction.V : Type u) :=
    { toFun := fun x ↦ TensorProduct.mk A k (Q.V : Type u) 1 x
      map_add' := by
        intro x y
        simpa using (TensorProduct.tmul_add (1 : k) x y)
      map_smul' := by
        intro a x
        simpa using (TensorProduct.tmul_smul (1 : k) a x) }
  refine ⟨redQ, ?_⟩
  simpa [redQ, FiniteProjectiveGroupAlgebraModule.residueFieldReduction,
    FiniteProjectiveGroupAlgebraModule.V] using
    (MonoidAlgebra.tensorProduct_mk_isResidueFieldReduction
      (Λ := A) (G := G) (P := (Q.V : Type u)))

/-- Helper for Exercise 15-15.5-3: once a raw `A[G]`-equivariant residue-field reduction is known
on a module `P`, the same map is a source-facing `IsResidueFieldLift` for the representation
`Representation.ofModule' P`. -/
private theorem isResidueFieldLift_of_raw_isResidueFieldReduction
    (ρl : Representation k G V) :
    letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
    letI : IsScalarTower k k[G] V :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
        simp [Algebra.smul_def]
    ∀ {P : Type*} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
      [Module.Free A P] [Module.Finite A P] {red : P →ₗ[A] V},
      red.IsResidueFieldReduction G →
      IsResidueFieldLift ρl (Representation.ofModule' P) red := by
  intro P _ _ _ _ _ _ red hred
  letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
  letI : IsScalarTower k k[G] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
      simp [Algebra.smul_def]
  let ρP : Representation A G P := Representation.ofModule' P
  let ρV : Representation A G V := Representation.ofModule' V
  change IsBaseChange k red ∧ ρP.IsIntertwiningMap ρV red
  exact hred

/-- Helper for Exercise 15-15.5-3: Serre's part `(b)` after the local same-universe coordinate
model and the Chapter `14` projective-lift owner are both exposed on the import surface. -/
private theorem exists_residueFieldLift_via_same_universe_owner
    (hG : ¬ p ∣ Nat.card G)
    (ρl : Representation k G V) :
    ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A G P)
      (red : P →ₗ[A] V),
        IsResidueFieldLift ρl ρA red := by
  -- Route correction: work directly on the intrinsic owner carrier
  -- `Q.residueFieldReduction.V`, then postcompose once with the compiled reduced equivalence.
  letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
  letI : IsScalarTower k k[G] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
      simp [Algebra.smul_def]
  obtain ⟨Q, ⟨eQ⟩⟩ :=
    exists_owner_lift_with_compiled_reduced_equiv
      (A := A) (p := p) (G := G) (V := V) hG ρl
  let _ : Module.Free A Q.V := FiniteProjectiveGroupAlgebraModule.free (A := A) (G := G) Q
  have howner_exists :
      ∃ redQ : (Q.V : Type u) →ₗ[A] (Q.residueFieldReduction.V : Type u),
        redQ.IsResidueFieldReduction G := by
    -- The intrinsic owner reduction is exactly the tensor-product reduction map.
    exact owner_exists_tensorProduct_mk_isResidueFieldReduction (A := A) (G := G) Q
  rcases howner_exists with ⟨redQ, hredQ⟩
  let red : (Q.V : Type u) →ₗ[A] V :=
    (((eQ.restrictScalars k).toLinearMap.restrictScalars A).comp redQ)
  refine
    ⟨Q.V, inferInstance, inferInstance, inferInstance, inferInstance,
      (Representation.ofModule' (Q.V : Type u)), red, ?_⟩
  have hred : red.IsResidueFieldReduction G := by
    -- Then transport the reduced target along the compiled `k[G]`-equivalence `eQ`.
    simpa [red] using
      isResidueFieldReduction_of_equiv_target
        (A := A) (G := G) (V := V)
        (P := (Q.V : Type u))
        (V' := (Q.residueFieldReduction.V : Type u))
        (f := redQ) hredQ eQ
  -- Repackage the transported raw reduction on the theorem's representation-facing surface.
  simpa [red] using
    isResidueFieldLift_of_raw_isResidueFieldReduction
      (A := A) (G := G) (V := V) ρl hred

-- Proof sketch: apply the previous lifting theorem successively to the reductions modulo
-- `𝔪^n`, use the henselian-local hypothesis to pass from the compatible finite-level system to an
-- actual lift over `A`, and use uniqueness at each finite level to identify the result.
/-- Exercise 15-15.5-3 (3): if `A` is henselian local and `|G|` is prime to `p`, every
finite-dimensional linear representation of `G` over the residue field `k` lifts to a free
finitely generated representation of `G` over `A`. -/
theorem exists_residueFieldLift
    (hG : ¬ p ∣ Nat.card G)
    (ρl : Representation k G V) :
    ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A G P)
      (red : P →ₗ[A] V),
        IsResidueFieldLift ρl ρA red :=
by
  exact
    exists_residueFieldLift_via_same_universe_owner
    (A := A) (p := p) (G := G) (V := V) hG ρl

-- Proof sketch: compare the two lifts modulo `𝔪^n` for every `n`, use the finite-level
-- conjugacy statement to choose compatible identifications, and use the henselian-local
-- hypothesis when passing from the finite-level system to the limit over `A`.
/-- Exercise 15-15.5-3 (4): if `A` is henselian local and `|G|` is prime to `p`, two free
finitely generated lifts of the same finite-dimensional residue-field representation are
equivariantly isomorphic through an `A`-linear isomorphism whose induced reduction map is the
identity on the residue representation. -/
theorem residueFieldLift_unique_up_to_equivariant_iso
    (hG : ¬ p ∣ Nat.card G)
    (ρl : Representation k G V)
    {P₁ : Type y} [AddCommGroup P₁] [Module A P₁] [Module.Free A P₁] [Module.Finite A P₁]
    (ρA₁ : Representation A G P₁)
    (red₁ : P₁ →ₗ[A] V)
    (hρA₁ : IsResidueFieldLift ρl ρA₁ red₁)
    {P₂ : Type y} [AddCommGroup P₂] [Module A P₂] [Module.Free A P₂] [Module.Finite A P₂]
    (ρA₂ : Representation A G P₂)
    (red₂ : P₂ →ₗ[A] V)
    (hρA₂ : IsResidueFieldLift ρl ρA₂ red₂) :
    ∃ e : ρA₁.Equiv ρA₂,
      red₂.comp e.toLinearMap = red₁ := by
  -- Route correction: specialize the Chapter `14` projective comparison to the identity reduced
  -- map so the recovered equivariant isomorphism already preserves the chosen reduction maps.
  exact
    equiv_of_common_residue_reduction_identity
      (A := A) (G := G) (p := p) (V := V)
      hG ρl ρA₁ red₁ hρA₁ ρA₂ red₂ hρA₂

end

end Representation

end
