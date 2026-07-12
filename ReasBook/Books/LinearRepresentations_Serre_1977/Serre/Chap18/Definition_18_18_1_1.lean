import Mathlib
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w x

namespace Representation

open Module.End

section PrimeToPRoot

variable {p : ℕ}
variable {k : Type u} [Field k]

/-- The canonical owner of prime-to-`p` roots of unity in `k`: the subgroup of units that are
`p`-regular in the sense of Definition `10-10.1-1`. -/
def primeToPRoots (p : ℕ) (k : Type u) [Field k] : Subgroup kˣ where
  carrier := {ζ | IsPRegular p ζ}
  one_mem' := isPRegular_one p
  mul_mem' {ζ ξ} hζ hξ := by
    exact Nat.Coprime.of_dvd_right
      (Commute.orderOf_mul_dvd_mul_orderOf (Commute.all _ _)) <| by
        rw [Nat.coprime_mul_iff_right]
        exact ⟨hζ, hξ⟩
  inv_mem' {ζ} hζ := by simpa [IsPRegular, orderOf_inv] using hζ

/-- A prime-to-`p` root of unity in `k`, viewed through the carrier of the canonical subgroup
owner `primeToPRoots p k`. -/
abbrev PrimeToPRoot (p : ℕ) (k : Type u) [Field k] :=
  ↥(primeToPRoots p k)

namespace PrimeToPRoot

/-- A prime-to-`p` root of unity is canonically an element of the ambient field. -/
instance : CoeTC (PrimeToPRoot p k) k where
  coe ζ := ((ζ : kˣ) : k)

/-- A multiplicative lift of prime-to-`p` roots of unity into `Kˣ`, viewed in the ambient field
`K`. -/
abbrev toFieldLift {K : Type v} [Field K] (lift : PrimeToPRoot p k →* Kˣ) :
    PrimeToPRoot p k → K :=
  ((↑) : Kˣ → K) ∘ lift

/-- View a lift defined on prime-to-`p` roots as a function on all units by extending it by
`0` away from the prime-to-`p` locus. This is the canonical bridge from the owner
`PrimeToPRoot p k → A` to the Chapter `18` notation `φ[...](...)`. -/
def zeroExtend {A : Type v} [Zero A] (lift : PrimeToPRoot p k → A) : kˣ → A :=
  let _ : DecidablePred fun ζ : kˣ ↦ ζ ∈ primeToPRoots p k := Classical.decPred _
  fun ζ ↦ if hζ : ζ ∈ primeToPRoots p k then lift ⟨ζ, hζ⟩ else 0

@[simp] theorem zeroExtend_coe {A : Type v} [Zero A] (lift : PrimeToPRoot p k → A)
    (ζ : PrimeToPRoot p k) :
    zeroExtend lift (ζ : kˣ) = lift ζ := by
  classical
  simp [zeroExtend]

/-- An `n`-th root of unity with `n` prime to `p` canonically determines a prime-to-`p` root of
unity. -/
def ofRootsOfUnity {n : ℕ} (hpn : Nat.Coprime p n) (ζ : rootsOfUnity n k) :
    PrimeToPRoot p k :=
  ⟨ζ, by
    have hζ : ((ζ : rootsOfUnity n k) : kˣ) ^ n = 1 := (mem_rootsOfUnity n (ζ : kˣ)).mp ζ.prop
    change IsPRegular p (ζ : kˣ)
    exact hpn.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hζ)⟩

end PrimeToPRoot

end PrimeToPRoot

section CharpolyRoots

variable {p : ℕ}
variable {k : Type u} [Field k]
variable {G : Type w} [Group G]

/-- The canonical `orderOf s`-th root of unity underlying a root of the characteristic polynomial
of `ρ s`. -/
def charpolyRoot_rootsOfUnity_orderOf {V : Type x} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (ρ : Representation k G V) (s : G) {μ : k}
    (hμ : μ ∈ (ρ s).charpoly.roots) :
    rootsOfUnity (orderOf s) k := by
  have hroot : (ρ s).charpoly.IsRoot μ :=
    (Polynomial.mem_roots ((ρ s).charpoly_monic.ne_zero)).1 hμ
  have hEig : Module.End.HasEigenvalue (ρ s) μ :=
    (hasEigenvalue_iff_isRoot_charpoly (ρ s) μ).2 hroot
  by_cases hs : orderOf s = 0
  · let v := Classical.choose hEig.exists_hasEigenvector
    have hv : Module.End.HasEigenvector (ρ s) μ v :=
      Classical.choose_spec hEig.exists_hasEigenvector
    have hv_ne : v ≠ 0 := (hasEigenvector_iff.mp hv).2
    have hμ_ne : μ ≠ 0 := by
      intro hμ0
      have hv_zero : ρ s v = 0 := by
        simpa [hμ0] using hv.apply_eq_smul
      exact hv_ne ((ρ.apply_bijective s).injective (by simpa using hv_zero))
    exact ⟨(isUnit_iff_ne_zero.mpr hμ_ne).unit, by simp [hs]⟩
  · let _ : NeZero (orderOf s) := ⟨hs⟩
    refine rootsOfUnity.mkOfPowEq μ ?_
    have hEigPow : Module.End.HasEigenvalue ((ρ s) ^ orderOf s) (μ ^ orderOf s) :=
      hEig.pow (orderOf s)
    have hpowρ : (ρ s) ^ orderOf s = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    have hroot_one : (1 : Module.End k V).charpoly.IsRoot (μ ^ orderOf s) :=
      (hasEigenvalue_iff_isRoot_charpoly (1 : Module.End k V) (μ ^ orderOf s)).1 <| by
        simpa [hpowρ] using hEigPow
    rw [Polynomial.IsRoot.def, LinearMap.charpoly_one, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X] at hroot_one
    simp only [Polynomial.eval_one] at hroot_one
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hroot_one)

/-- Helper for Definition 18-18.1-1: the `orderOf s`-th root of unity extracted from a
characteristic-polynomial root keeps the same field value. -/
@[simp] theorem charpolyRoot_rootsOfUnity_orderOf_coe
    {V : Type x} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k G V) (s : G) {μ : k}
    (hμ : μ ∈ (ρ s).charpoly.roots) :
    ((((charpolyRoot_rootsOfUnity_orderOf ρ s hμ : rootsOfUnity (orderOf s) k) : kˣ) : k) = μ) := by
  -- The construction only repackages the scalar root as a root of unity, so its field value is
  -- still the original root.
  by_cases hs : orderOf s = 0
  · simp [charpolyRoot_rootsOfUnity_orderOf, hs]
  · simp [charpolyRoot_rootsOfUnity_orderOf, hs]

end CharpolyRoots

section ModularCharacter

variable {p : ℕ}
variable {k : Type u} [Field k]
variable {A : Type v} [AddCommMonoid A]
variable {G : Type w} [Group G]

/-- Helper for Definition 18-18.1-1: a root of the characteristic polynomial of `ρ s`
canonically determines a prime-to-`p` root of unity whenever `s` is `p`-regular. -/
def charpolyRoot_primeToPRoot {V : Type x} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k G V) {s : G} (hs : IsPRegular p s) {μ : k}
    (hμ : μ ∈ (ρ s).charpoly.roots) :
    PrimeToPRoot p k :=
  PrimeToPRoot.ofRootsOfUnity hs (charpolyRoot_rootsOfUnity_orderOf ρ s hμ)

/-- Helper for Definition 18-18.1-1: the packaged prime-to-`p` root underlying a characteristic
polynomial root has the same field value as the original root. -/
@[simp] theorem charpolyRoot_primeToPRoot_coe
    {V : Type x} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k G V) {s : G} (hs : IsPRegular p s) {μ : k}
    (hμ : μ ∈ (ρ s).charpoly.roots) :
    ((charpolyRoot_primeToPRoot (p := p) (k := k) ρ hs hμ : PrimeToPRoot p k) : k) = μ := by
  -- The helper is defined by re-packaging the same scalar root, so the field-level value is
  -- unchanged.
  simp [charpolyRoot_primeToPRoot, PrimeToPRoot.ofRootsOfUnity]

/-- Definition 18-18.1-1: for a finite-dimensional representation of a group over an algebraically
closed field `k`, a chosen lift of the prime-to-`p` roots of unity in `k`, and a `p`-regular
element `s`, the modular character of `ρ` at `s` is the sum of the chosen lifts of the roots of
the characteristic polynomial of the endomorphism `ρ s`; these roots are canonically
`orderOf s`-th roots of unity. -/
def modularCharacter {V : Type x} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [IsAlgClosed k] (lift : PrimeToPRoot p k → A) (ρ : Representation k G V) :
    { s : G // IsPRegular p s } → A :=
  fun s ↦
    let roots := (ρ s.1).charpoly.roots.attach
    -- We follow the textbook eigenvalue sum through `charpoly.roots`, then package each root
    -- via the canonical prime-to-`p` owner before applying the chosen lift.
    (roots.map fun μ ↦
      lift <| charpolyRoot_primeToPRoot (p := p) (k := k) ρ s.2 μ.2).sum

scoped[Representation] notation:max "φ[" lift "](" ρ ")" =>
  modularCharacter (lift ∘ ((↑) : PrimeToPRoot _ _ → _)) ρ

end ModularCharacter

end Representation
