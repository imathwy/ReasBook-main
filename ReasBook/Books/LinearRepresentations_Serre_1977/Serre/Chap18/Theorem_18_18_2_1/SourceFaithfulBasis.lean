import Mathlib
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1.RealizationCore
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1.MixedRealizationAssembly
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1.SpanningAssembly

/-!
Source-faithful coefficient setting for Definition 18-18.1-1 and Theorem 18-18.2-1.

Serre's modular characters are defined for a modular system `(K, A, k)`: `K` is a
characteristic-zero field that is *sufficiently large*, i.e. contains the `m`-th roots of unity
for `m` the lcm of the orders of the (`p`-regular) elements of `G`, and the eigenvalue lifts are
taken along the canonical multiplicative section of the reduction `μ_m(A) ≃ μ_m(k)`.

The previous formal interface asked instead for an injective monoid homomorphism
`PrimeToPRoot p k →* Kˣ` defined on *all* prime-to-`p` roots of unity of `k`.  That hypothesis is
strictly stronger than Serre's: a field such as `ℚ_p(μ_m)` has only finitely many roots of unity,
while every nontrivial divisible subgroup of `PrimeToPRoot p k` must die under any such
homomorphism — so Serre's own coefficient fields admit no globally defined injective lift at all,
and the global-lift theorems cannot be specialized to the source setting.

This file repairs the design.  Given only a primitive `pRegularExponent p G`-th root of unity
`ω` in a characteristic-zero field `K` (Serre's "sufficiently large" hypothesis, restricted to
the `p`-regular part that Chapter 18 actually uses), we fix once a generator `ζ` of the relevant
torsion of `PrimeToPRoot p k` and define the canonical torsion lift `ζ^t ↦ ω^t`.  The resulting
modular characters satisfy Theorem 18-18.2-1 (`serreTorsionLift_brauer_basis`), with both Serre
parts `(a)` and `(b)` obtained from the torsion-lift realization of part `(a)` and the residue
field count of part `(b)`.
-/

noncomputable section

universe u x

open CategoryTheory
open scoped Representation

namespace Representation

variable (p : ℕ) [Fact p.Prime]
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
variable (G : Type u) [Group G] [Finite G]

/-- The chosen generator of the `pRegularExponent p G`-torsion of the prime-to-`p` roots of
unity of `k`. -/
def torsionGenerator : PrimeToPRoot p k :=
  Classical.choose (exists_torsion_generator p k G)

theorem torsionGenerator_orderOf :
    orderOf (torsionGenerator p k G) = pRegularExponent p G :=
  (Classical.choose_spec (exists_torsion_generator p k G)).1

theorem torsionGenerator_generates :
    ∀ x : PrimeToPRoot p k, x ^ pRegularExponent p G = 1 →
      ∃ t : ℕ, x = torsionGenerator p k G ^ t :=
  (Classical.choose_spec (exists_torsion_generator p k G)).2

variable {K : Type u} [Field K]

open scoped Classical in
/-- Serre's canonical eigenvalue lift attached to a primitive `pRegularExponent p G`-th root of
unity `ω` of the coefficient field: the chosen torsion generator is sent to `ω`, its powers to
the corresponding powers, and the (irrelevant) non-torsion locus to `1`. -/
def serreTorsionLift (ω : K) : PrimeToPRoot p k → K := fun x ↦
  if hx : x ^ pRegularExponent p G = 1 then
    ω ^ Classical.choose (torsionGenerator_generates p k G x hx)
  else 1

variable {p k G}

/-- The defining power law of the canonical torsion lift. -/
theorem serreTorsionLift_pow {ω : K}
    (hω : IsPrimitiveRoot ω (pRegularExponent p G)) (t : ℕ) :
    serreTorsionLift p k G ω (torsionGenerator p k G ^ t) = ω ^ t := by
  classical
  have hm₀ : pRegularExponent p G ≠ 0 := pRegularExponent_ne_zero (p := p) (G := G)
  have hx : (torsionGenerator p k G ^ t) ^ pRegularExponent p G = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    rw [← torsionGenerator_orderOf p k G, pow_orderOf_eq_one, one_pow]
  rw [serreTorsionLift]
  rw [dif_pos hx]
  -- the chosen exponent is congruent to `t` modulo the common order
  have hspec := Classical.choose_spec (torsionGenerator_generates p k G _ hx)
  have hζmod : Classical.choose (torsionGenerator_generates p k G _ hx) ≡ t
      [MOD pRegularExponent p G] := by
    have hpow : torsionGenerator p k G ^
        Classical.choose (torsionGenerator_generates p k G _ hx) =
        torsionGenerator p k G ^ t := hspec.symm
    have := (pow_eq_pow_iff_modEq).mp hpow
    rwa [torsionGenerator_orderOf p k G] at this
  -- transfer the congruence through the unit underlying `ω`
  have hm₀ne : pRegularExponent p G ≠ 0 := hm₀
  have hωunit : IsUnit ω := hω.isUnit hm₀ne
  have hωuord : orderOf hωunit.unit = pRegularExponent p G :=
    ((hω.isUnit_unit hm₀ne).eq_orderOf).symm
  have hupow : hωunit.unit ^ Classical.choose (torsionGenerator_generates p k G _ hx) =
      hωunit.unit ^ t :=
    (pow_eq_pow_iff_modEq (x := hωunit.unit)).mpr (by rwa [hωuord])
  have := congrArg (Units.coeHom K) hupow
  simpa [Units.val_pow_eq_pow_val, IsUnit.unit_spec] using this

/-- Linear independence of the source-faithful modular characters (Serre part `(a)` for the
sufficiently-large setting). -/
theorem linearIndependent_brauer_serreTorsionLift [CharZero K]
    {ω : K} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
    {ι : Type x}
    (E : ι → FDRep k G)
    (hE_simple : ∀ i, Simple (E i))
    (hE_pairwise : PairwiseNonisomorphic E) :
    LinearIndependent K
      (fun i ↦
        FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
          (serreTorsionLift p k G ω)) := by
  classical
  have hm₀ : pRegularExponent p G ≠ 0 := pRegularExponent_ne_zero (p := p) (G := G)
  rw [linearIndependent_iff']
  intro s a hsum i hi
  by_contra hai
  -- normalize the distinguished coefficient
  set aNorm : ι → K := fun j ↦ a j / a i with haNormdef
  have hsumNorm :
      (Finset.sum s
          fun j ↦ aNorm j •
            FDRep.modularCharacterOnPRegularConjClass (p := p) (E j)
              (serreTorsionLift p k G ω)) =
        (0 : PRegularConjClass G p → K) := by
    funext c
    have hpoint := congrFun hsum c
    rw [Finset.sum_apply] at hpoint
    rw [Finset.sum_apply]
    have : (Finset.sum s fun j ↦
        (aNorm j • FDRep.modularCharacterOnPRegularConjClass (p := p) (E j)
          (serreTorsionLift p k G ω)) c) =
        (a i)⁻¹ * Finset.sum s fun j ↦
          (a j • FDRep.modularCharacterOnPRegularConjClass (p := p) (E j)
            (serreTorsionLift p k G ω)) c := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [haNormdef]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [this, hpoint]
    simp
  have haNorm_i : aNorm i = 1 := by
    rw [haNormdef]
    exact div_self hai
  -- the primitive root as a unit of full order
  have hωunit : IsUnit ω := hω.isUnit hm₀
  have hηord : orderOf hωunit.unit = pRegularExponent p G :=
    ((hω.isUnit_unit hm₀).eq_orderOf).symm
  refine
    supported_normalized_brauer_relation_contradiction_of_torsion_lift
      (p := p) (k := k) (K := K) (G := G)
      (serreTorsionLift p k G ω)
      (torsionGenerator p k G)
      (torsionGenerator_orderOf p k G)
      (torsionGenerator_generates p k G)
      hωunit.unit hηord ?_ (Or.inl ringChar.eq_zero)
      E hE_simple hE_pairwise s aNorm hsumNorm hi haNorm_i
  intro t
  rw [serreTorsionLift_pow hω t]
  rw [IsUnit.unit_spec]

/-- Spanning for the source-faithful modular characters (Serre part `(b)` for the
sufficiently-large setting). -/
theorem serreTorsionLift_brauer_span_eq_top [CharZero K]
    {ω : K} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
    {ι : Type x}
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E) :
    Submodule.span K
      (Set.range fun i ↦
        FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
          (serreTorsionLift p k G ω)) = ⊤ := by
  classical
  letI : Fintype (PRegularConjClass G p) := Fintype.ofFinite (PRegularConjClass G p)
  letI : Finite ι :=
    (linearIndependent_brauer_value (p := p) (k := k) (G := G) E
      (fun i ↦ hE_complete.isSimple i) hE_pairwise).finite
  letI : Fintype ι := Fintype.ofFinite ι
  have hind :=
    linearIndependent_brauer_serreTorsionLift (p := p) (k := k) (G := G) hω E
      (fun i ↦ hE_complete.isSimple i) hE_pairwise
  have hcard :=
    card_complete_family_eq_card_pRegularConjClass (p := p) (k := k) (G := G)
      E hE_pairwise hE_complete
  rcases isEmpty_or_nonempty ι with hempty | hne
  · -- without simple representations there are no `p`-regular classes either
    have hzero : Fintype.card (PRegularConjClass G p) = 0 := by
      rw [← hcard]
      exact Fintype.card_eq_zero
    haveI : IsEmpty (PRegularConjClass G p) := Fintype.card_eq_zero_iff.mp hzero
    apply top_unique
    intro f _
    have hf0 : f = 0 := funext fun c ↦ (IsEmpty.false c).elim
    rw [hf0]
    exact Submodule.zero_mem _
  · exact hind.span_eq_top_of_card_eq_finrank
      (by rw [Module.finrank_pi]; exact hcard)

/-- Theorem 18-18.2-1 in Serre's own coefficient setting: over a characteristic-zero field
containing a primitive root of unity of order the prime-to-`p` exponent of `G` (Serre's
"sufficiently large" hypothesis), the modular characters attached to the canonical torsion lift
of a complete pairwise nonisomorphic simple family form a basis of the space of `K`-valued
functions on the `p`-regular conjugacy classes. -/
noncomputable def serreTorsionLift_brauer_basis [CharZero K]
    {ω : K} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
    {ι : Type x}
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E) :
    Module.Basis ι K (PRegularConjClass G p → K) :=
  Module.Basis.mk
    (linearIndependent_brauer_serreTorsionLift (p := p) (k := k) (G := G) hω E
      (fun i ↦ hE_complete.isSimple i) hE_pairwise)
    (serreTorsionLift_brauer_span_eq_top (p := p) (k := k) (G := G) hω E
      hE_pairwise hE_complete).ge

/-- Evaluating the source-faithful basis returns the corresponding modular character. -/
@[simp] theorem serreTorsionLift_brauer_basis_apply [CharZero K]
    {ω : K} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
    {ι : Type x}
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (i : ι) :
    serreTorsionLift_brauer_basis (p := p) (k := k) (G := G) hω E hE_pairwise hE_complete i =
      FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
        (serreTorsionLift p k G ω) := by
  rw [serreTorsionLift_brauer_basis, Module.Basis.mk_apply]

end Representation
