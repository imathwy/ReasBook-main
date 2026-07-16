import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_2_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_5_3.MaximalIdealPowSquareZero
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_5_3.TransitionLiftBridge

open scoped MonoidAlgebra

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

/-- Helper for Exercise 15-15.5-3: the raw multiplicative defect of chosen pointwise lifts lies in
the packaged correction algebra because it reduces to zero through the transition
`E / 𝔪^(n+1) E → E / 𝔪^n E`. -/
lemma liftDefect_comp_eq_zero
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E))
    (T : G → Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E))
    (hT : ∀ g,
      letI : Module (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E) :=
        Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
      maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n ∘ₗ T g =
        downstairs_endomorphism_over_factorPowSucc (A := A) (E := E) n (ρn g) ∘ₗ
          maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n)
    (g h : G) :
    (maximalIdealPowTransition (A := A) (E := E) n).comp
      (((T (g * h) - T g * T h).restrictScalars A)) = 0 := by
  letI : Module (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E) :=
    Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
  -- Compare both sides after applying the transition map to a vector and then rewrite the
  -- downstairs term with `ρn.map_mul`.
  apply LinearMap.ext
  intro x
  change
    maximalIdealPowTransition (A := A) (E := E) n (((T (g * h) - T g * T h)) x) = 0
  have hgh := LinearMap.congr_fun (hT (g * h)) x
  have hg := LinearMap.congr_fun (hT g) (T h x)
  have hh := LinearMap.congr_fun (hT h) x
  simp only [LinearMap.comp_apply,
    maximalIdealPowTransition_linear_over_factorPowSucc_apply,
    downstairs_endomorphism_over_factorPowSucc_apply] at hgh hg hh
  calc
    maximalIdealPowTransition (A := A) (E := E) n (((T (g * h) - T g * T h)) x)
        = maximalIdealPowTransition (A := A) (E := E) n (T (g * h) x) -
            maximalIdealPowTransition (A := A) (E := E) n ((T g * T h) x) := by
              simp [LinearMap.sub_apply]
    _ = ρn (g * h) (maximalIdealPowTransition (A := A) (E := E) n x) -
          ρn g (maximalIdealPowTransition (A := A) (E := E) n ((T h) x)) := by
            simp [hgh, hg, Module.End.mul_apply]
    _ = ρn (g * h) (maximalIdealPowTransition (A := A) (E := E) n x) -
          ρn g (ρn h (maximalIdealPowTransition (A := A) (E := E) n x)) := by
            rw [hh]
    _ = 0 := by
          rw [map_mul]
          simp

/-- Helper for Exercise 15-15.5-3: package the raw multiplicative defect as an element of the
public correction algebra. This is the stabilized finite-level coefficient object for the later
averaging step. -/
noncomputable def liftDefect_memTransitionCorrection
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E))
    (T : G → Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E))
    (hT : ∀ g,
      letI : Module (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E) :=
        Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
      maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n ∘ₗ T g =
        downstairs_endomorphism_over_factorPowSucc (A := A) (E := E) n (ρn g) ∘ₗ
          maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n)
    (g h : G) :
    maximalIdealPowTransitionCorrection (A := A) (E := E) n :=
  ⟨T (g * h) - T g * T h,
    liftDefect_comp_eq_zero (A := A) (E := E) (n := n) ρn T hT g h⟩

/-- Helper for Exercise 15-15.5-3: if two level-`n+1` lifts have the same reduction to level
`n`, then their pointwise difference lands in the packaged correction algebra. -/
lemma comparisonDifference_comp_eq_zero
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E))
    (ρn1 ρn1' : Representation (A⧸𝔪^((n : ℕ) + 1)) G (E⧸𝔪^((n : ℕ) + 1)E))
    (hρn1 :
      (Representation.restrictScalars A ρn1).IsIntertwiningMap
        (Representation.restrictScalars A ρn)
        (Submodule.factorPowSucc 𝔪 E (n : ℕ)))
    (hρn1' :
      (Representation.restrictScalars A ρn1').IsIntertwiningMap
        (Representation.restrictScalars A ρn)
        (Submodule.factorPowSucc 𝔪 E (n : ℕ)))
    (g : G) :
    (maximalIdealPowTransition (A := A) (E := E) n).comp
      (((ρn1' g - ρn1 g).restrictScalars A)) = 0 := by
  -- The two lifts have the same image under the transition, so their difference reduces to zero.
  apply LinearMap.ext
  intro x
  have h1 :
      maximalIdealPowTransition (A := A) (E := E) n (ρn1' g x) =
        ρn g (maximalIdealPowTransition (A := A) (E := E) n x) := by
    simpa [Representation.restrictScalars_apply, maximalIdealPowTransition] using
      hρn1'.isIntertwining g x
  have h2 :
      maximalIdealPowTransition (A := A) (E := E) n (ρn1 g x) =
        ρn g (maximalIdealPowTransition (A := A) (E := E) n x) := by
    simpa [Representation.restrictScalars_apply, maximalIdealPowTransition] using
      hρn1.isIntertwining g x
  change maximalIdealPowTransition (A := A) (E := E) n (((ρn1' g - ρn1 g)) x) = 0
  calc
    maximalIdealPowTransition (A := A) (E := E) n (((ρn1' g - ρn1 g)) x)
        = maximalIdealPowTransition (A := A) (E := E) n (ρn1' g x) -
            maximalIdealPowTransition (A := A) (E := E) n (ρn1 g x) := by
              simp [LinearMap.sub_apply]
    _ = ρn g (maximalIdealPowTransition (A := A) (E := E) n x) -
          ρn g (maximalIdealPowTransition (A := A) (E := E) n x) := by
            rw [h1, h2]
    _ = 0 := by simp

/-- Helper for Exercise 15-15.5-3: package the pointwise comparison of two lifts as an element of
the public correction algebra. This is the stabilized coefficient object for the later averaged
coboundary step. -/
noncomputable def comparisonCocycle_memTransitionCorrection
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E))
    (ρn1 ρn1' : Representation (A⧸𝔪^((n : ℕ) + 1)) G (E⧸𝔪^((n : ℕ) + 1)E))
    (hρn1 :
      (Representation.restrictScalars A ρn1).IsIntertwiningMap
        (Representation.restrictScalars A ρn)
        (Submodule.factorPowSucc 𝔪 E (n : ℕ)))
    (hρn1' :
      (Representation.restrictScalars A ρn1').IsIntertwiningMap
        (Representation.restrictScalars A ρn)
        (Submodule.factorPowSucc 𝔪 E (n : ℕ)))
    (g : G) :
    maximalIdealPowTransitionCorrection (A := A) (E := E) n :=
  ⟨ρn1' g - ρn1 g,
    comparisonDifference_comp_eq_zero
      (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' g⟩

/-- Helper for Exercise 15-15.5-3: the packaged defect satisfies the direct associativity identity
coming from comparing the two expansions of `T ((g * h) * k)`. This is the concrete `H²`
rewrite used by the later averaging step. -/
lemma liftDefect_assoc_identity
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E))
    (T : G → Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E))
    (hT : ∀ g,
      letI : Module (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E) :=
        Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
      maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n ∘ₗ T g =
        downstairs_endomorphism_over_factorPowSucc (A := A) (E := E) n (ρn g) ∘ₗ
          maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n)
    (g h k : G) :
    ((liftDefect_memTransitionCorrection (A := A) (E := E) (n := n) ρn T hT g h).1) * T k +
        (liftDefect_memTransitionCorrection
          (A := A) (E := E) (n := n) ρn T hT (g * h) k).1 =
      T g * ((liftDefect_memTransitionCorrection
          (A := A) (E := E) (n := n) ρn T hT h k).1) +
        (liftDefect_memTransitionCorrection
          (A := A) (E := E) (n := n) ρn T hT g (h * k)).1 := by
  -- Expand both defects and compare the two associative parenthesizations of the same triple
  -- product. Every middle term cancels on the nose after unfolding.
  apply LinearMap.ext
  intro x
  calc
    (((liftDefect_memTransitionCorrection (A := A) (E := E) (n := n) ρn T hT g h).1) * T k +
        (liftDefect_memTransitionCorrection
          (A := A) (E := E) (n := n) ρn T hT (g * h) k).1) x
      = (T (g * h) (T k x) - T g (T h (T k x))) +
          (T ((g * h) * k) x - T (g * h) (T k x)) := by
            simp [liftDefect_memTransitionCorrection, Module.End.mul_apply, LinearMap.sub_apply]
    _ = T ((g * h) * k) x - T g (T h (T k x)) := by
          abel_nf
    _ = T (g * (h * k)) x - T g (T h (T k x)) := by
          rw [mul_assoc]
    _ = (T g (T (h * k) x) - T g (T h (T k x))) +
          (T (g * (h * k)) x - T g (T (h * k) x)) := by
            abel_nf
    _ = (T g * ((liftDefect_memTransitionCorrection
          (A := A) (E := E) (n := n) ρn T hT h k).1) +
        (liftDefect_memTransitionCorrection
          (A := A) (E := E) (n := n) ρn T hT g (h * k)).1) x := by
            simp [liftDefect_memTransitionCorrection, Module.End.mul_apply,
              LinearMap.sub_apply, map_sub]

/-- Helper for Exercise 15-15.5-3: once the chosen pointwise lifts satisfy `T 1 = 1`, the
packaged multiplicative defect vanishes whenever the left argument is the identity. This is the
normalized `H²` boundary condition used when averaging the defect. -/
lemma liftDefect_identity_left
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E))
    (T : G → Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E))
    (hT : ∀ g,
      letI : Module (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E) :=
        Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
      maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n ∘ₗ T g =
        downstairs_endomorphism_over_factorPowSucc (A := A) (E := E) n (ρn g) ∘ₗ
          maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n)
    (hT1 : T 1 = 1)
    (g : G) :
    (liftDefect_memTransitionCorrection
      (A := A) (E := E) (n := n) ρn T hT 1 g).1 = 0 := by
  -- Normalize the chosen lift at `1`; then the defect is the difference of identical terms.
  apply LinearMap.ext
  intro x
  simp [liftDefect_memTransitionCorrection, hT1, Module.End.mul_apply]

/-- Helper for Exercise 15-15.5-3: once the chosen pointwise lifts satisfy `T 1 = 1`, the
packaged multiplicative defect vanishes whenever the right argument is the identity. This is the
second normalized `H²` boundary condition used when averaging the defect. -/
lemma liftDefect_identity_right
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E))
    (T : G → Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E))
    (hT : ∀ g,
      letI : Module (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E) :=
        Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
      maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n ∘ₗ T g =
        downstairs_endomorphism_over_factorPowSucc (A := A) (E := E) n (ρn g) ∘ₗ
          maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n)
    (hT1 : T 1 = 1)
    (g : G) :
    (liftDefect_memTransitionCorrection
      (A := A) (E := E) (n := n) ρn T hT g 1).1 = 0 := by
  -- The same normalization at the identity collapses the right-hand defect to zero.
  apply LinearMap.ext
  intro x
  simp [liftDefect_memTransitionCorrection, hT1, Module.End.mul_apply]

/-- Helper for Exercise 15-15.5-3: the packaged comparison difference is a concrete `1`-cocycle
for the two lifts. This is the executable `H¹` rewrite used by the later averaging step. -/
lemma comparisonDifference_cocycle_identity
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E))
    (ρn1 ρn1' : Representation (A⧸𝔪^((n : ℕ) + 1)) G (E⧸𝔪^((n : ℕ) + 1)E))
    (hρn1 :
      (Representation.restrictScalars A ρn1).IsIntertwiningMap
        (Representation.restrictScalars A ρn)
        (Submodule.factorPowSucc 𝔪 E (n : ℕ)))
    (hρn1' :
      (Representation.restrictScalars A ρn1').IsIntertwiningMap
        (Representation.restrictScalars A ρn)
        (Submodule.factorPowSucc 𝔪 E (n : ℕ)))
    (g h : G) :
    (comparisonCocycle_memTransitionCorrection
        (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' (g * h)).1 =
      ((comparisonCocycle_memTransitionCorrection
          (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' g).1) * (ρn1 h) +
        (ρn1' g) *
          ((comparisonCocycle_memTransitionCorrection
            (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' h).1) := by
  -- Expand the pointwise differences and use multiplicativity of the two lifts. The mixed terms
  -- cancel, leaving exactly the comparison at `g * h`.
  apply LinearMap.ext
  intro x
  calc
    (comparisonCocycle_memTransitionCorrection
        (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' (g * h)).1 x
      = ρn1' (g * h) x - ρn1 (g * h) x := by
          simp [comparisonCocycle_memTransitionCorrection]
    _ = ρn1' g (ρn1' h x) - ρn1 g (ρn1 h x) := by
          rw [map_mul, map_mul]
          rfl
    _ = (ρn1' g (ρn1 h x) - ρn1 g (ρn1 h x)) +
          (ρn1' g (ρn1' h x) - ρn1' g (ρn1 h x)) := by
            abel_nf
    _ = (((comparisonCocycle_memTransitionCorrection
            (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' g).1) * (ρn1 h) +
          (ρn1' g) *
            ((comparisonCocycle_memTransitionCorrection
              (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' h).1)) x := by
            simp [comparisonCocycle_memTransitionCorrection, Module.End.mul_apply,
              LinearMap.sub_apply, map_sub]

/-- Helper for Exercise 15-15.5-3: the comparison cocycle is normalized at the identity because
both lifts send `1` to the identity endomorphism. -/
lemma comparisonDifference_identity
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E))
    (ρn1 ρn1' : Representation (A⧸𝔪^((n : ℕ) + 1)) G (E⧸𝔪^((n : ℕ) + 1)E))
    (hρn1 :
      (Representation.restrictScalars A ρn1).IsIntertwiningMap
        (Representation.restrictScalars A ρn)
        (Submodule.factorPowSucc 𝔪 E (n : ℕ)))
    (hρn1' :
      (Representation.restrictScalars A ρn1').IsIntertwiningMap
        (Representation.restrictScalars A ρn)
        (Submodule.factorPowSucc 𝔪 E (n : ℕ))) :
    (comparisonCocycle_memTransitionCorrection
      (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' 1).1 = 0 := by
  -- At the identity both lifts are the identity endomorphism, so their difference vanishes.
  simp [comparisonCocycle_memTransitionCorrection]

/-- Helper for Exercise 15-15.5-3: if `p` does not divide `|G|`, then `|G|` is a unit on every
finite quotient `A / 𝔪^(n+1)`. -/
private lemma card_unit_mod_maximalIdeal_pow_succ
    (hG : ¬ p ∣ Nat.card G)
    (n : ℕ+) :
    IsUnit (Nat.card G : A⧸𝔪^((n : ℕ) + 1)) := by
  have hcardA : IsUnit (Nat.card G : A) := by
    let _ : NeZero (Nat.card G : IsLocalRing.ResidueField A) := NeZero.of_not_dvd _ hG
    have hresidue_ne_zero : IsLocalRing.residue A (Nat.card G : A) ≠ 0 := by
      rw [← IsLocalRing.ResidueField.algebraMap_eq]
      exact NeZero.ne (Nat.card G : IsLocalRing.ResidueField A)
    exact (IsLocalRing.residue_ne_zero_iff_isUnit (Nat.card G : A)).mp hresidue_ne_zero
  simpa using (IsUnit.map (Ideal.Quotient.mk (𝔪 ^ ((n : ℕ) + 1))) hcardA)

/-- Helper for Exercise 15-15.5-3: the right-normalized averaged defect still lands in the
transition-correction algebra. -/
private theorem liftDefect_rightAverage_comp_eq_zero
    [Fintype G]
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E))
    (T : G → Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E))
    (hT : ∀ g,
      letI : Module (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E) :=
        Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
      maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n ∘ₗ T g =
        downstairs_endomorphism_over_factorPowSucc (A := A) (E := E) n (ρn g) ∘ₗ
          maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n)
    (a : A⧸𝔪^((n : ℕ) + 1))
    (g : G) :
    (maximalIdealPowTransition (A := A) (E := E) n).comp
        (((a • ∑ k : G,
          (liftDefect_memTransitionCorrection
            (A := A) (E := E) (n := n) ρn T hT g k).1 * T k⁻¹).restrictScalars A)) =
      0 := by
  classical
  apply LinearMap.ext
  intro x
  letI : Module (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E) :=
    Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
  change maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n
    ((a • ∑ k : G,
          (liftDefect_memTransitionCorrection
            (A := A) (E := E) (n := n) ρn T hT g k).1 * T k⁻¹) x) = 0
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  rw [Finset.sum_eq_zero]
  · simp
  · intro k _
    have hkzero := LinearMap.congr_fun
      (liftDefect_memTransitionCorrection
        (A := A) (E := E) (n := n) ρn T hT g k).2
      ((T k⁻¹) x)
    simpa [LinearMap.comp_apply, Module.End.mul_apply,
      maximalIdealPowTransition_linear_over_factorPowSucc_apply] using hkzero

/-- Helper for Exercise 15-15.5-3: the associativity identity for the multiplicative defect after
right multiplication by the chosen inverse lift. -/
private theorem liftDefect_assoc_right_mul_inv
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E))
    (T : G → Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E))
    (hT : ∀ g,
      letI : Module (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E) :=
        Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
      maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n ∘ₗ T g =
        downstairs_endomorphism_over_factorPowSucc (A := A) (E := E) n (ρn g) ∘ₗ
          maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n)
    (hT1 : T 1 = 1)
    (g h k : G) :
    (liftDefect_memTransitionCorrection
      (A := A) (E := E) (n := n) ρn T hT (g * h) k).1 * T k⁻¹ =
      T g *
          ((liftDefect_memTransitionCorrection
            (A := A) (E := E) (n := n) ρn T hT h k).1 * T k⁻¹) +
        (liftDefect_memTransitionCorrection
            (A := A) (E := E) (n := n) ρn T hT g (h * k)).1 * T k⁻¹ -
          (liftDefect_memTransitionCorrection
            (A := A) (E := E) (n := n) ρn T hT g h).1 := by
  let D := fun a b =>
    liftDefect_memTransitionCorrection (A := A) (E := E) (n := n) ρn T hT a b
  have hassoc := liftDefect_assoc_identity (A := A) (E := E) (n := n) ρn T hT g h k
  have hassoc_mul : ((D g h).1 * T k + (D (g * h) k).1) * T k⁻¹ =
      (T g * (D h k).1 + (D g (h * k)).1) * T k⁻¹ := by
    simpa [D] using congrArg (fun u => u * T k⁻¹) hassoc
  rw [add_mul, add_mul] at hassoc_mul
  have hDkk : T k * T k⁻¹ = 1 - (D k k⁻¹).1 := by
    have hDkk_def : (D k k⁻¹).1 = 1 - T k * T k⁻¹ := by
      simp [D, liftDefect_memTransitionCorrection, hT1]
    rw [hDkk_def]
    abel
  have hDgh_Tk : (D g h).1 * T k * T k⁻¹ = (D g h).1 := by
    calc
      (D g h).1 * T k * T k⁻¹ = (D g h).1 * (T k * T k⁻¹) := by
        rw [mul_assoc]
      _ = (D g h).1 * (1 - (D k k⁻¹).1) := by
        rw [hDkk]
      _ = (D g h).1 := by
        rw [mul_sub, mul_one]
        have hzero : (D g h).1 * (D k k⁻¹).1 = 0 :=
          maximalIdealPowTransitionCorrection_square_zero
            (A := A) (E := E) (n := n) (D g h) (D k k⁻¹)
        rw [hzero, sub_zero]
  calc
    (D (g * h) k).1 * T k⁻¹
        = ((D g h).1 * T k + (D (g * h) k).1) * T k⁻¹ - (D g h).1 := by
          rw [add_mul]
          rw [hDgh_Tk]
          abel
    _ = (T g * (D h k).1 + (D g (h * k)).1) * T k⁻¹ - (D g h).1 := by
          rw [add_mul, add_mul]
          exact congrArg (fun u => u - (D g h).1) hassoc_mul
    _ = T g * ((D h k).1 * T k⁻¹) + (D g (h * k)).1 * T k⁻¹ -
          (D g h).1 := by
          symm
          rw [add_mul]
          rw [mul_assoc]

/-- Helper for Exercise 15-15.5-3: reindexing the right-normalized defect average turns the
translated second argument into right multiplication by the chosen lift. -/
private theorem liftDefect_rightAverage_reindex
    [Fintype G]
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E))
    (T : G → Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E))
    (hT : ∀ g,
      letI : Module (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E) :=
        Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
      maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n ∘ₗ T g =
        downstairs_endomorphism_over_factorPowSucc (A := A) (E := E) n (ρn g) ∘ₗ
          maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n)
    (g h : G) :
    (∑ k : G,
      (liftDefect_memTransitionCorrection
        (A := A) (E := E) (n := n) ρn T hT g (h * k)).1 * T k⁻¹) =
      (∑ k : G,
        (liftDefect_memTransitionCorrection
          (A := A) (E := E) (n := n) ρn T hT g k).1 * T k⁻¹) * T h := by
  classical
  let D := fun a b =>
    liftDefect_memTransitionCorrection (A := A) (E := E) (n := n) ρn T hT a b
  calc
    (∑ k : G, (D g (h * k)).1 * T k⁻¹)
        = ∑ l : G, (D g l).1 * T ((h⁻¹ * l)⁻¹) := by
          simpa [D, mul_assoc] using
            (Equiv.sum_comp (Equiv.mulLeft h)
              (fun l : G => (D g l).1 * T ((h⁻¹ * l)⁻¹)))
    _ = ∑ l : G, (D g l).1 * (T l⁻¹ * T h) := by
          refine Finset.sum_congr rfl ?_
          intro l _
          have hTl : T ((h⁻¹ * l)⁻¹) = T l⁻¹ * T h + (D l⁻¹ h).1 := by
            have hD : (D l⁻¹ h).1 = T (l⁻¹ * h) - T l⁻¹ * T h := by
              simp [D, liftDefect_memTransitionCorrection]
            rw [show (h⁻¹ * l)⁻¹ = l⁻¹ * h by group]
            rw [hD]
            abel
          calc
            (D g l).1 * T ((h⁻¹ * l)⁻¹)
                = (D g l).1 * (T l⁻¹ * T h + (D l⁻¹ h).1) := by
                  rw [hTl]
            _ = (D g l).1 * (T l⁻¹ * T h) + (D g l).1 * (D l⁻¹ h).1 := by
                  rw [mul_add]
            _ = (D g l).1 * (T l⁻¹ * T h) := by
                  have hzero : (D g l).1 * (D l⁻¹ h).1 = 0 :=
                    maximalIdealPowTransitionCorrection_square_zero
                      (A := A) (E := E) (n := n) (D g l) (D l⁻¹ h)
                  rw [hzero, add_zero]
    _ = (∑ k : G, (D g k).1 * T k⁻¹) * T h := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro l _
          rw [mul_assoc]

/-- Helper for Exercise 15-15.5-3: the unscaled right-normalized defect average is a coboundary
up to multiplication by `|G|`. -/
private theorem liftDefect_rightAverage_sum_coboundary
    [Fintype G]
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E))
    (T : G → Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E))
    (hT : ∀ g,
      letI : Module (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E) :=
        Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
      maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n ∘ₗ T g =
        downstairs_endomorphism_over_factorPowSucc (A := A) (E := E) n (ρn g) ∘ₗ
          maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n)
    (hT1 : T 1 = 1)
    (g h : G) :
    (∑ k : G,
      (liftDefect_memTransitionCorrection
        (A := A) (E := E) (n := n) ρn T hT (g * h) k).1 * T k⁻¹) =
      T g *
          (∑ k : G,
            (liftDefect_memTransitionCorrection
              (A := A) (E := E) (n := n) ρn T hT h k).1 * T k⁻¹) +
        (∑ k : G,
          (liftDefect_memTransitionCorrection
            (A := A) (E := E) (n := n) ρn T hT g k).1 * T k⁻¹) * T h -
          Fintype.card G •
            (liftDefect_memTransitionCorrection
              (A := A) (E := E) (n := n) ρn T hT g h).1 := by
  classical
  let D := fun a b =>
    liftDefect_memTransitionCorrection (A := A) (E := E) (n := n) ρn T hT a b
  calc
    (∑ k : G, (D (g * h) k).1 * T k⁻¹)
        = ∑ k : G,
            (T g * ((D h k).1 * T k⁻¹) + (D g (h * k)).1 * T k⁻¹ -
              (D g h).1) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          exact liftDefect_assoc_right_mul_inv
            (A := A) (E := E) (n := n) ρn T hT hT1 g h k
    _ = (∑ k : G, T g * ((D h k).1 * T k⁻¹)) +
          (∑ k : G, (D g (h * k)).1 * T k⁻¹) -
            ∑ _k : G, (D g h).1 := by
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = T g * (∑ k : G, (D h k).1 * T k⁻¹) +
          (∑ k : G, (D g k).1 * T k⁻¹) * T h -
            Fintype.card G • (D g h).1 := by
          rw [← Finset.mul_sum]
          rw [liftDefect_rightAverage_reindex (A := A) (E := E) (n := n) ρn T hT g h]
          rw [Finset.sum_const, Finset.card_univ]

/-- Helper for Exercise 15-15.5-3: after dividing by `|G|`, the right-normalized averaged defect
is a genuine coboundary for the preliminary lifts. -/
private theorem liftDefect_rightAverage_coboundary
    [Fintype G]
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E))
    (T : G → Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E))
    (hT : ∀ g,
      letI : Module (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E) :=
        Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
      maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n ∘ₗ T g =
        downstairs_endomorphism_over_factorPowSucc (A := A) (E := E) n (ρn g) ∘ₗ
          maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n)
    (hT1 : T 1 = 1)
    (hcard : IsUnit (Nat.card G : A⧸𝔪^((n : ℕ) + 1)))
    (g h : G) :
    let avg : G → Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E) :=
      fun a =>
        Ring.inverse (Nat.card G : A⧸𝔪^((n : ℕ) + 1)) •
          ∑ k : G,
            (liftDefect_memTransitionCorrection
              (A := A) (E := E) (n := n) ρn T hT a k).1 * T k⁻¹
    (liftDefect_memTransitionCorrection
        (A := A) (E := E) (n := n) ρn T hT g h).1 + avg (g * h) =
      T g * avg h + avg g * T h := by
  classical
  intro avg
  let D := fun a b =>
    liftDefect_memTransitionCorrection (A := A) (E := E) (n := n) ρn T hT a b
  let N : A⧸𝔪^((n : ℕ) + 1) := Nat.card G
  let Ninv : A⧸𝔪^((n : ℕ) + 1) := Ring.inverse N
  let S : G → Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E) :=
    fun a => ∑ k : G, (D a k).1 * T k⁻¹
  have hsum :
      S (g * h) = T g * S h + S g * T h - Fintype.card G • (D g h).1 := by
    simpa [S, D] using
      liftDefect_rightAverage_sum_coboundary
        (A := A) (E := E) (n := n) ρn T hT hT1 g h
  have hcancel :
      Ninv • (Fintype.card G • (D g h).1) = (D g h).1 := by
    rw [Fintype.card_eq_nat_card, ← Nat.cast_smul_eq_nsmul (A⧸𝔪^((n : ℕ) + 1))]
    rw [smul_smul]
    change (Ninv * N) • (D g h).1 = (D g h).1
    rw [Ring.inverse_mul_cancel N hcard, one_smul]
  calc
    (D g h).1 + avg (g * h)
        = (D g h).1 + Ninv • S (g * h) := by
          rfl
    _ = (D g h).1 + Ninv • (T g * S h + S g * T h -
          Fintype.card G • (D g h).1) := by
          rw [hsum]
    _ = T g * (Ninv • S h) + (Ninv • S g) * T h := by
          rw [smul_sub, smul_add, hcancel]
          rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
          abel
    _ = T g * avg h + avg g * T h := by
          rfl

/-- Helper for Exercise 15-15.5-3: the unscaled right-normalized average of the comparison
cocycle used in Serre's `H¹` vanishing argument. -/
private noncomputable def comparisonCocycleRightAverageSum
    [Fintype G]
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E))
    (ρn1 ρn1' : Representation (A⧸𝔪^((n : ℕ) + 1)) G (E⧸𝔪^((n : ℕ) + 1)E))
    (hρn1 :
      (Representation.restrictScalars A ρn1).IsIntertwiningMap
        (Representation.restrictScalars A ρn)
        (Submodule.factorPowSucc 𝔪 E (n : ℕ)))
    (hρn1' :
      (Representation.restrictScalars A ρn1').IsIntertwiningMap
        (Representation.restrictScalars A ρn)
        (Submodule.factorPowSucc 𝔪 E (n : ℕ))) :
    Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E) :=
  ∑ k : G,
    (comparisonCocycle_memTransitionCorrection
      (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' k).1 * ρn1 k⁻¹

/-- Helper for Exercise 15-15.5-3: the right-normalized average of the comparison cocycle after
division by `|G|`. -/
private noncomputable def comparisonCocycleRightAverage
    [Fintype G]
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E))
    (ρn1 ρn1' : Representation (A⧸𝔪^((n : ℕ) + 1)) G (E⧸𝔪^((n : ℕ) + 1)E))
    (hρn1 :
      (Representation.restrictScalars A ρn1).IsIntertwiningMap
        (Representation.restrictScalars A ρn)
        (Submodule.factorPowSucc 𝔪 E (n : ℕ)))
    (hρn1' :
      (Representation.restrictScalars A ρn1').IsIntertwiningMap
        (Representation.restrictScalars A ρn)
        (Submodule.factorPowSucc 𝔪 E (n : ℕ))) :
    Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E) :=
  Ring.inverse (Nat.card G : A⧸𝔪^((n : ℕ) + 1)) •
    comparisonCocycleRightAverageSum
      (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1'

/-- Helper for Exercise 15-15.5-3: the right-normalized averaged comparison cocycle still lands
in the transition-correction algebra. -/
private theorem comparisonCocycle_rightAverage_comp_eq_zero
    [Fintype G]
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E))
    (ρn1 ρn1' : Representation (A⧸𝔪^((n : ℕ) + 1)) G (E⧸𝔪^((n : ℕ) + 1)E))
    (hρn1 :
      (Representation.restrictScalars A ρn1).IsIntertwiningMap
        (Representation.restrictScalars A ρn)
        (Submodule.factorPowSucc 𝔪 E (n : ℕ)))
    (hρn1' :
      (Representation.restrictScalars A ρn1').IsIntertwiningMap
        (Representation.restrictScalars A ρn)
        (Submodule.factorPowSucc 𝔪 E (n : ℕ)))
    (a : A⧸𝔪^((n : ℕ) + 1)) :
    (maximalIdealPowTransition (A := A) (E := E) n).comp
        (((a • ∑ k : G,
          (comparisonCocycle_memTransitionCorrection
            (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' k).1 *
            ρn1 k⁻¹).restrictScalars A)) = 0 := by
  classical
  apply LinearMap.ext
  intro x
  letI : Module (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E) :=
    Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
  change maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n
    ((a • ∑ k : G,
          (comparisonCocycle_memTransitionCorrection
            (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' k).1 *
            ρn1 k⁻¹) x) = 0
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  rw [Finset.sum_eq_zero]
  · simp
  · intro k _
    have hkzero := LinearMap.congr_fun
      (comparisonCocycle_memTransitionCorrection
        (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' k).2
      ((ρn1 k⁻¹) x)
    simpa [LinearMap.comp_apply, Module.End.mul_apply,
      maximalIdealPowTransition_linear_over_factorPowSucc_apply] using hkzero

/-- Helper for Exercise 15-15.5-3: the unscaled right-normalized comparison average realizes
`|G|` times the comparison cocycle as a coboundary. -/
private theorem comparisonCocycle_rightAverage_sum_coboundary
    [Fintype G]
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E))
    (ρn1 ρn1' : Representation (A⧸𝔪^((n : ℕ) + 1)) G (E⧸𝔪^((n : ℕ) + 1)E))
    (hρn1 :
      (Representation.restrictScalars A ρn1).IsIntertwiningMap
        (Representation.restrictScalars A ρn)
        (Submodule.factorPowSucc 𝔪 E (n : ℕ)))
    (hρn1' :
      (Representation.restrictScalars A ρn1').IsIntertwiningMap
        (Representation.restrictScalars A ρn)
        (Submodule.factorPowSucc 𝔪 E (n : ℕ)))
    (g : G) :
    comparisonCocycleRightAverageSum
        (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' * ρn1 g =
      Fintype.card G •
          (comparisonCocycle_memTransitionCorrection
            (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' g).1 +
        ρn1' g *
          comparisonCocycleRightAverageSum
            (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' := by
  classical
  let C := fun a =>
    comparisonCocycle_memTransitionCorrection
      (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' a
  let R := A⧸𝔪^((n : ℕ) + 1)
  let S : Module.End R (E⧸𝔪^((n : ℕ) + 1)E) :=
    comparisonCocycleRightAverageSum
      (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1'
  have hS_def : S = ∑ k : G, (C k).1 * ρn1 k⁻¹ := by
    rfl
  have hreindex :
      (∑ k : G, (C (g * k)).1 * ρn1 k⁻¹) = S * ρn1 g := by
    calc
      (∑ k : G, (C (g * k)).1 * ρn1 k⁻¹)
          = ∑ l : G, (C l).1 * ρn1 ((g⁻¹ * l)⁻¹) := by
            simpa [C, mul_assoc] using
              (Equiv.sum_comp (Equiv.mulLeft g)
                (fun l : G => (C l).1 * ρn1 ((g⁻¹ * l)⁻¹)))
      _ = ∑ l : G, (C l).1 * (ρn1 l⁻¹ * ρn1 g) := by
            refine Finset.sum_congr rfl ?_
            intro l _
            rw [show (g⁻¹ * l)⁻¹ = l⁻¹ * g by group]
            rw [map_mul]
      _ = S * ρn1 g := by
            rw [hS_def]
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro l _
            rw [mul_assoc]
  calc
    S * ρn1 g = ∑ k : G, (C (g * k)).1 * ρn1 k⁻¹ := hreindex.symm
    _ = ∑ k : G, ((C g).1 * ρn1 k + ρn1' g * (C k).1) * ρn1 k⁻¹ := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [comparisonDifference_cocycle_identity
            (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' g k]
    _ = ∑ k : G, ((C g).1 + ρn1' g * ((C k).1 * ρn1 k⁻¹)) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          have hright : ρn1 k * ρn1 k⁻¹ = 1 := by
            rw [← map_mul]
            simp
          calc
            ((C g).1 * ρn1 k + ρn1' g * (C k).1) * ρn1 k⁻¹
                = (C g).1 * ρn1 k * ρn1 k⁻¹ +
                    (ρn1' g * (C k).1) * ρn1 k⁻¹ := by
                  rw [add_mul]
            _ = (C g).1 + ρn1' g * ((C k).1 * ρn1 k⁻¹) := by
                  have hleft : (C g).1 * ρn1 k * ρn1 k⁻¹ = (C g).1 := by
                    calc
                      (C g).1 * ρn1 k * ρn1 k⁻¹ =
                          (C g).1 * (ρn1 k * ρn1 k⁻¹) := by
                            rw [mul_assoc ((C g).1) (ρn1 k) (ρn1 k⁻¹)]
                      _ = (C g).1 := by
                            rw [hright, mul_one]
                  rw [hleft]
                  rw [mul_assoc (ρn1' g) ((C k).1) (ρn1 k⁻¹)]
    _ = Fintype.card G • (C g).1 + ρn1' g * S := by
          rw [Finset.sum_add_distrib]
          rw [Finset.sum_const, Finset.card_univ]
          rw [hS_def]
          rw [Finset.mul_sum]

/-- Helper for Exercise 15-15.5-3: after dividing by `|G|`, the right-normalized averaged
comparison cocycle is a coboundary. -/
private theorem comparisonCocycle_rightAverage_coboundary
    [Fintype G]
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E))
    (ρn1 ρn1' : Representation (A⧸𝔪^((n : ℕ) + 1)) G (E⧸𝔪^((n : ℕ) + 1)E))
    (hρn1 :
      (Representation.restrictScalars A ρn1).IsIntertwiningMap
        (Representation.restrictScalars A ρn)
        (Submodule.factorPowSucc 𝔪 E (n : ℕ)))
    (hρn1' :
      (Representation.restrictScalars A ρn1').IsIntertwiningMap
        (Representation.restrictScalars A ρn)
        (Submodule.factorPowSucc 𝔪 E (n : ℕ)))
    (hcard : IsUnit (Nat.card G : A⧸𝔪^((n : ℕ) + 1)))
    (g : G) :
    (comparisonCocycle_memTransitionCorrection
      (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' g).1 =
      comparisonCocycleRightAverage
          (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' * ρn1 g -
        ρn1' g *
          comparisonCocycleRightAverage
            (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' := by
  classical
  let R := A⧸𝔪^((n : ℕ) + 1)
  let C := fun a =>
    comparisonCocycle_memTransitionCorrection
      (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' a
  let S : Module.End R (E⧸𝔪^((n : ℕ) + 1)E) :=
    comparisonCocycleRightAverageSum
      (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1'
  let N : R := Nat.card G
  let Ninv : R := Ring.inverse N
  have hsum :
      S * ρn1 g = Fintype.card G • (C g).1 + ρn1' g * S := by
    simpa [S, C] using
      comparisonCocycle_rightAverage_sum_coboundary
        (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' g
  have hinside :
      Fintype.card G • (C g).1 = S * ρn1 g - ρn1' g * S := by
    rw [hsum]
    abel
  have hcancel :
      Ninv • (Fintype.card G • (C g).1) = (C g).1 := by
    rw [Fintype.card_eq_nat_card, ← Nat.cast_smul_eq_nsmul R]
    rw [smul_smul]
    change (Ninv * N) • (C g).1 = (C g).1
    rw [Ring.inverse_mul_cancel N hcard, one_smul]
  calc
    (C g).1 = Ninv • (Fintype.card G • (C g).1) := by
      rw [hcancel]
    _ = Ninv • (S * ρn1 g - ρn1' g * S) := by
      rw [hinside]
    _ = (Ninv • S) * ρn1 g - ρn1' g * (Ninv • S) := by
      rw [smul_sub]
      rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    _ = comparisonCocycleRightAverage
          (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' * ρn1 g -
        ρn1' g *
          comparisonCocycleRightAverage
            (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' := by
      rfl

-- Proof sketch: choose pointwise lifts, package their multiplicative defect in the correction
-- algebra using `liftDefect_memTransitionCorrection`, average that defect, and then correct the
-- preliminary lifts by a square-zero `1`-cochain.
/-- Helper for Exercise 15-15.5-3: the remaining finite-level existence step is exactly Serre's
averaged square-zero correction theorem on the packaged defect algebra. -/
theorem averagedCorrectionProducesLift
    (hG : ¬ p ∣ Nat.card G)
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E)) :
    ∃ ρn1 : Representation (A⧸𝔪^((n : ℕ) + 1)) G (E⧸𝔪^((n : ℕ) + 1)E),
      (Representation.restrictScalars A ρn1).IsIntertwiningMap
        (Representation.restrictScalars A ρn)
        (Submodule.factorPowSucc 𝔪 E (n : ℕ)) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let R := A⧸𝔪^((n : ℕ) + 1)
  let M := E⧸𝔪^((n : ℕ) + 1)E
  choose T hT using fun g =>
    existsGroupElementLiftOverFactorPowSucc (A := A) (E := E) n ρn g
  let T0 : G → Module.End R M := fun g => if g = 1 then 1 else T g
  have hT0 : ∀ g,
      letI : Module R (E⧸𝔪^((n : ℕ))E) :=
        Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
      maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n ∘ₗ T0 g =
        downstairs_endomorphism_over_factorPowSucc (A := A) (E := E) n (ρn g) ∘ₗ
          maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n := by
    intro g
    by_cases hg : g = 1
    · subst hg
      letI : Module R (E⧸𝔪^((n : ℕ))E) :=
        Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
      apply LinearMap.ext
      intro x
      simp [T0, maximalIdealPowTransition_linear_over_factorPowSucc_apply,
        downstairs_endomorphism_over_factorPowSucc_apply]
    · simpa [T0, hg, R, M] using hT g
  have hT01 : T0 1 = 1 := by
    simp [T0]
  have hcard : IsUnit (Nat.card G : R) :=
    card_unit_mod_maximalIdeal_pow_succ (A := A) (G := G) (p := p) hG n
  let avg : G → Module.End R M := fun g =>
    Ring.inverse (Nat.card G : R) •
      ∑ k : G,
        (liftDefect_memTransitionCorrection (A := A) (E := E) (n := n) ρn T0 hT0 g k).1 *
          T0 k⁻¹
  have havg_mem : ∀ g,
      (maximalIdealPowTransition (A := A) (E := E) n).comp
          (((avg g).restrictScalars A)) = 0 := by
    intro g
    simpa [avg, R, M] using
      liftDefect_rightAverage_comp_eq_zero
        (A := A) (E := E) (G := G) (n := n) ρn T0 hT0
        (Ring.inverse (Nat.card G : R)) g
  let avgCorr : G → maximalIdealPowTransitionCorrection (A := A) (E := E) n :=
    fun g => ⟨avg g, havg_mem g⟩
  let S : G → Module.End R M := fun g => T0 g + avg g
  have hS_mul : ∀ g h, S (g * h) = S g * S h := by
    intro g h
    let D := fun a b =>
      liftDefect_memTransitionCorrection (A := A) (E := E) (n := n) ρn T0 hT0 a b
    have hcob :
        (D g h).1 + avg (g * h) = T0 g * avg h + avg g * T0 h := by
      simpa [avg, R, M, D] using
        liftDefect_rightAverage_coboundary
          (A := A) (E := E) (G := G) (n := n) ρn T0 hT0 hT01 hcard g h
    have hsq : avg g * avg h = 0 :=
      maximalIdealPowTransitionCorrection_square_zero
        (A := A) (E := E) (n := n) (avgCorr g) (avgCorr h)
    have hD : (D g h).1 = T0 (g * h) - T0 g * T0 h := rfl
    calc
      S (g * h) = T0 (g * h) + avg (g * h) := rfl
      _ = T0 g * T0 h + ((D g h).1 + avg (g * h)) := by
            rw [hD]
            abel
      _ = T0 g * T0 h + (T0 g * avg h + avg g * T0 h) := by
            rw [hcob]
      _ = (T0 g + avg g) * (T0 h + avg h) := by
            rw [add_mul, mul_add, mul_add, hsq, add_zero]
            abel
      _ = S g * S h := rfl
  have havg_one : avg 1 = 0 := by
    simp [avg, liftDefect_identity_left (A := A) (E := E) (n := n) ρn T0 hT0 hT01]
  let ρn1 : Representation R G M :=
    { toFun := S
      map_one' := by
        simp [S, hT01, havg_one]
      map_mul' := hS_mul }
  refine ⟨ρn1, ?_⟩
  refine Representation.IsIntertwiningMap.mk ?_
  intro g x
  letI : Module R (E⧸𝔪^((n : ℕ))E) :=
    Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
  have hT0x := LinearMap.congr_fun (hT0 g) x
  simp only [LinearMap.comp_apply, maximalIdealPowTransition_linear_over_factorPowSucc_apply,
    downstairs_endomorphism_over_factorPowSucc_apply] at hT0x
  have havgx := LinearMap.congr_fun (havg_mem g) x
  have havgx' : maximalIdealPowTransition (A := A) (E := E) n (avg g x) = 0 := by
    simpa [LinearMap.comp_apply] using havgx
  change maximalIdealPowTransition (A := A) (E := E) n (S g x) =
    ρn g (maximalIdealPowTransition (A := A) (E := E) n x)
  simp [S, hT0x, havgx']

-- Proof sketch: package the pointwise difference of two lifts with
-- `comparisonCocycle_memTransitionCorrection`, average that `1`-cocycle, and conjugate by the
-- resulting automorphism `1 + c`.
/-- Helper for Exercise 15-15.5-3: the remaining finite-level uniqueness step is exactly Serre's
averaged coboundary theorem on the packaged comparison algebra. -/
theorem comparisonCoboundaryProducesConjugator
    (hG : ¬ p ∣ Nat.card G)
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E))
    (ρn1 ρn1' : Representation (A⧸𝔪^((n : ℕ) + 1)) G (E⧸𝔪^((n : ℕ) + 1)E))
    (hρn1 :
      (Representation.restrictScalars A ρn1).IsIntertwiningMap
        (Representation.restrictScalars A ρn)
        (Submodule.factorPowSucc 𝔪 E (n : ℕ)))
    (hρn1' :
      (Representation.restrictScalars A ρn1').IsIntertwiningMap
        (Representation.restrictScalars A ρn)
        (Submodule.factorPowSucc 𝔪 E (n : ℕ))) :
    let π := Submodule.factorPowSucc 𝔪 E (n : ℕ)
    ∃ u : ρn1.Equiv ρn1',
      π ∘ₗ (u.toLinearMap.restrictScalars A) = π := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let R := A⧸𝔪^((n : ℕ) + 1)
  let M := E⧸𝔪^((n : ℕ) + 1)E
  have hcard : IsUnit (Nat.card G : R) :=
    card_unit_mod_maximalIdeal_pow_succ (A := A) (G := G) (p := p) hG n
  let avg : Module.End R M :=
    Ring.inverse (Nat.card G : R) •
      ∑ k : G,
        (comparisonCocycle_memTransitionCorrection
          (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' k).1 *
          ρn1 k⁻¹
  have havg_def :
      avg =
        comparisonCocycleRightAverage
          (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' := by
    rfl
  have havg_mem :
      (maximalIdealPowTransition (A := A) (E := E) n).comp
          ((avg.restrictScalars A)) = 0 := by
    exact
      comparisonCocycle_rightAverage_comp_eq_zero
        (A := A) (E := E) (G := G) (n := n) ρn ρn1 ρn1' hρn1 hρn1'
        (Ring.inverse (Nat.card G : R))
  let avgCorr : maximalIdealPowTransitionCorrection (A := A) (E := E) n :=
    ⟨avg, havg_mem⟩
  obtain ⟨U, hU, _hUsymm⟩ :=
    maximalIdealPowTransitionCorrection_exists_one_add_linearEquiv
      (A := A) (E := E) (n := n) avgCorr
  let C := fun a =>
    comparisonCocycle_memTransitionCorrection
      (A := A) (E := E) (n := n) ρn ρn1 ρn1' hρn1 hρn1' a
  have hU_intertwines :
      ∀ g : G, U.toLinearMap ∘ₗ ρn1 g = ρn1' g ∘ₗ U.toLinearMap := by
    intro g
    change U.toLinearMap * ρn1 g = ρn1' g * U.toLinearMap
    rw [hU]
    have hcob :
        (C g).1 = avg * ρn1 g - ρn1' g * avg := by
      rw [havg_def]
      simpa [C, R, M] using
        comparisonCocycle_rightAverage_coboundary
          (A := A) (E := E) (G := G) (n := n) ρn ρn1 ρn1' hρn1 hρn1' hcard g
    have havg_mul :
        avg * ρn1 g = (C g).1 + ρn1' g * avg := by
      rw [hcob]
      abel
    have hC_def : (C g).1 = ρn1' g - ρn1 g := rfl
    calc
      (((1 : Module.End R M) + avg) * ρn1 g)
          = ρn1 g + avg * ρn1 g := by
              rw [add_mul, one_mul]
      _ = ρn1 g + ((C g).1 + ρn1' g * avg) := by
              rw [havg_mul]
      _ = ρn1' g + ρn1' g * avg := by
              rw [hC_def]
              abel
      _ = ρn1' g * ((1 : Module.End R M) + avg) := by
              rw [mul_add, mul_one]
  let u : ρn1.Equiv ρn1' := Representation.Equiv.mk U hU_intertwines
  refine ⟨u, ?_⟩
  simpa [u, hU, avgCorr, maximalIdealPowTransition] using
    maximalIdealPowTransitionCorrection_one_add_reduces_to_identity
      (A := A) (E := E) (n := n) avgCorr

end

end Representation

end
