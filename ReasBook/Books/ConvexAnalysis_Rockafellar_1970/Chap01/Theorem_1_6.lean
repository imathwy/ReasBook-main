import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AffineSubspace Submodule

/- 
Source/core/bridge triage:
- `source-facing`: Theorem 1.6 states existence and uniqueness for ambient affine automorphisms
  carrying one affinely independent family to another.
- `core/canonical`: the owner abstractions are `AffineIndependent 𝕜`,
  `affineSpan 𝕜 (Set.range b)`, the span bases `Module.Basis.span`, `AffineMap`, and
  `AffineEquiv`.
- `bridge/view`: the existence theorem and the affine-equivalence uniqueness specialization below
  are the source-facing bridges from the affine-independence owners to ambient affine
  automorphisms.
- Primitive data vs derived API: the point families are the only primitive data. The affine
  automorphism and its uniqueness are derived theorem-level content, not packaged data.
- Domain-style sampling used here: `affineIndependent_iff_linearIndependent_vsub`,
  `Module.Basis.span`, `LinearEquiv.ofFinrankEq`,
  `AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one`, and `AffineMap.ext_on`.
-/

section AffineSpace

variable {𝕜 : Type*} {V : Type*} {P : Type*}
  [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
  [FiniteDimensional 𝕜 V]

private theorem exists_linearEquiv_of_linearIndependent
    {ι : Type*} {v v' : ι → V} (hv : LinearIndependent 𝕜 v) (hv' : LinearIndependent 𝕜 v') :
    ∃ A : V ≃ₗ[𝕜] V, ∀ i, A (v i) = v' i := by
  let S : Submodule 𝕜 V := span 𝕜 (Set.range v)
  let S' : Submodule 𝕜 V := span 𝕜 (Set.range v')
  let basis := Module.Basis.span hv
  let basis' := Module.Basis.span hv'
  let A₁ : S ≃ₗ[𝕜] S' := basis.equiv basis' (Equiv.refl _)
  obtain ⟨C, hC⟩ := S.exists_isCompl
  obtain ⟨C', hC'⟩ := S'.exists_isCompl
  have hfinrankS : Module.finrank 𝕜 S = Module.finrank 𝕜 S' := by
    simpa using LinearEquiv.finrank_eq A₁
  have hsum : Module.finrank 𝕜 S + Module.finrank 𝕜 C = Module.finrank 𝕜 V :=
    Submodule.finrank_add_eq_of_isCompl hC
  have hsum' : Module.finrank 𝕜 S' + Module.finrank 𝕜 C' = Module.finrank 𝕜 V :=
    Submodule.finrank_add_eq_of_isCompl hC'
  have hfinrankC : Module.finrank 𝕜 C = Module.finrank 𝕜 C' := by
    omega
  let A₂ : C ≃ₗ[𝕜] C' := LinearEquiv.ofFinrankEq C C' hfinrankC
  let A : V ≃ₗ[𝕜] V :=
    (S.prodEquivOfIsCompl C hC).symm.trans <|
      (A₁.prodCongr A₂).trans <|
        S'.prodEquivOfIsCompl C' hC'
  refine ⟨A, ?_⟩
  intro i
  let x : S := ⟨v i, subset_span (Set.mem_range_self i)⟩
  have hAx : (A x : V) = A₁ x := by
    calc
      (A x : V) =
          (S'.prodEquivOfIsCompl C' hC')
            ((A₁.prodCongr A₂) ((S.prodEquivOfIsCompl C hC).symm x)) :=
        rfl
      _ = (S'.prodEquivOfIsCompl C' hC') (A₁ x, 0) := by
        rw [prodEquivOfIsCompl_symm_apply_left]
        simp
      _ = A₁ x := by simp
  have hA₁x : (A₁ x : V) = v' i := by
    simpa [A₁, basis, basis', x] using congrArg (fun y : S' ↦ (y : V))
      (basis.equiv_apply i basis' (Equiv.refl _))
  simpa [x] using hAx.trans hA₁x

namespace AffineIndependent

/-- Theorem 1.6 (existence), stated at the affine-space owner level: two affinely independent
families with a common index type in finite-dimensional affine spaces modeled on the same vector
space are related by an affine equivalence. Specializing to equal source/target spaces recovers
the ambient-automorphism statement. -/
-- Proof sketch: choose a base point in each family and compare the corresponding linearly
-- independent difference-vector families. Extend the spanned submodules to complements, choose a
-- linear equivalence on the complements from the finrank computation, assemble the resulting
-- ambient linear equivalence, and upgrade it to an affine equivalence carrying the first family to
-- the second.
theorem exists_affineEquiv {ι : Type*}
    {P' : Type*} [AddTorsor V P'] {b : ι → P} {b' : ι → P'}
    (hb : AffineIndependent 𝕜 b) (hb' : AffineIndependent 𝕜 b') :
    ∃ T : P ≃ᵃ[𝕜] P', ∀ i, T (b i) = b' i := by
  classical
  by_cases hι : IsEmpty ι
  · let p0 : P := Classical.choice (inferInstance : Nonempty P)
    let p0' : P' := Classical.choice (inferInstance : Nonempty P')
    let T : P ≃ᵃ[𝕜] P' := AffineEquiv.mk'
      (fun x : P ↦ (LinearEquiv.refl 𝕜 V) (x -ᵥ p0) +ᵥ p0')
      (LinearEquiv.refl 𝕜 V) p0 (by intro x; simp)
    refine ⟨T, ?_⟩
    intro i
    exact (hι.false i).elim
  · letI : Nonempty ι := not_isEmpty_iff.mp hι
    let i0 : ι := Classical.choice ‹Nonempty ι›
    let v : {i : ι // i ≠ i0} → V := fun i ↦ b i -ᵥ b i0
    let v' : {i : ι // i ≠ i0} → V := fun i ↦ b' i -ᵥ b' i0
    have hv : LinearIndependent 𝕜 v := by
      simpa [v] using (affineIndependent_iff_linearIndependent_vsub 𝕜 b i0).mp hb
    have hv' : LinearIndependent 𝕜 v' := by
      simpa [v'] using (affineIndependent_iff_linearIndependent_vsub 𝕜 b' i0).mp hb'
    obtain ⟨A, hA⟩ := exists_linearEquiv_of_linearIndependent hv hv'
    let T : P ≃ᵃ[𝕜] P' := AffineEquiv.mk'
      (fun x : P ↦ A (x -ᵥ b i0) +ᵥ b' i0)
      A (b i0) (by intro x; simp)
    refine ⟨T, ?_⟩
    intro i
    by_cases hi : i = i0
    · subst hi
      change A (b i0 -ᵥ b i0) +ᵥ b' i0 = b' i0
      simp
    · let j : {i : ι // i ≠ i0} := ⟨i, hi⟩
      have hTi : T (b i) = A (b i -ᵥ b i0) +ᵥ b' i0 := by
        change A (b i -ᵥ b i0) +ᵥ b' i0 = A (b i -ᵥ b i0) +ᵥ b' i0
        rfl
      rw [hTi]
      simpa [v, v', j] using congrArg (fun x : V ↦ x +ᵥ b' i0) (hA j)

end AffineIndependent

end AffineSpace

section AffineSpaceFintype

variable {𝕜 : Type*} {V : Type*} {P : Type*}
  [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]

private theorem exists_linearEquiv_of_linearIndependent_of_finite
    {ι : Type*} [Finite ι] {v v' : ι → V}
    (hv : LinearIndependent 𝕜 v) (hv' : LinearIndependent 𝕜 v') :
    ∃ A : V ≃ₗ[𝕜] V, ∀ i, A (v i) = v' i := by
  let S : Submodule 𝕜 V := span 𝕜 (Set.range v)
  let S' : Submodule 𝕜 V := span 𝕜 (Set.range v')
  let basis := Module.Basis.span hv
  let basis' := Module.Basis.span hv'
  let A₁ : S ≃ₗ[𝕜] S' := basis.equiv basis' (Equiv.refl _)
  obtain ⟨C, hC⟩ := S.exists_isCompl
  obtain ⟨C', hC'⟩ := S'.exists_isCompl
  letI : FiniteDimensional 𝕜 S := by
    simpa [S] using
      (FiniteDimensional.span_of_finite (K := 𝕜) (A := Set.range v) (Set.finite_range v))
  have hrankS_lt_aleph0 : Module.rank 𝕜 S < Cardinal.aleph0 := Module.rank_lt_aleph0 𝕜 S
  have hrankS : Module.rank 𝕜 S = Module.rank 𝕜 S' := A₁.rank_eq
  have hrankQuot : Module.rank 𝕜 (V ⧸ S) = Module.rank 𝕜 (V ⧸ S') := by
    have hsum :
        Module.rank 𝕜 (V ⧸ S) + Module.rank 𝕜 S = Module.rank 𝕜 V :=
      Submodule.rank_quotient_add_rank S
    have hsum' :
        Module.rank 𝕜 (V ⧸ S') + Module.rank 𝕜 S' = Module.rank 𝕜 V :=
      Submodule.rank_quotient_add_rank S'
    have hsum'' :
        Module.rank 𝕜 (V ⧸ S') + Module.rank 𝕜 S = Module.rank 𝕜 V := by
      simpa [hrankS] using hsum'
    have hadd :
        Module.rank 𝕜 (V ⧸ S) + Module.rank 𝕜 S =
          Module.rank 𝕜 (V ⧸ S') + Module.rank 𝕜 S := by
      rw [hsum, hsum'']
    exact Cardinal.eq_of_add_eq_add_right hadd hrankS_lt_aleph0
  let A₂Q : (V ⧸ S) ≃ₗ[𝕜] (V ⧸ S') := LinearEquiv.ofRankEq (V ⧸ S) (V ⧸ S') hrankQuot
  let A₂ : C ≃ₗ[𝕜] C' :=
    (quotientEquivOfIsCompl S C hC).symm.trans <|
      A₂Q.trans <|
        quotientEquivOfIsCompl S' C' hC'
  let A : V ≃ₗ[𝕜] V :=
    (S.prodEquivOfIsCompl C hC).symm.trans <|
      (A₁.prodCongr A₂).trans <|
        S'.prodEquivOfIsCompl C' hC'
  refine ⟨A, ?_⟩
  intro i
  let x : S := ⟨v i, subset_span (Set.mem_range_self i)⟩
  have hAx : (A x : V) = A₁ x := by
    calc
      (A x : V) =
          (S'.prodEquivOfIsCompl C' hC')
            ((A₁.prodCongr A₂) ((S.prodEquivOfIsCompl C hC).symm x)) :=
        rfl
      _ = (S'.prodEquivOfIsCompl C' hC') (A₁ x, 0) := by
        rw [prodEquivOfIsCompl_symm_apply_left]
        simp
      _ = A₁ x := by simp
  have hA₁x : (A₁ x : V) = v' i := by
    simpa [A₁, basis, basis', x] using congrArg (fun y : S' ↦ (y : V))
      (basis.equiv_apply i basis' (Equiv.refl _))
  simpa [x] using hAx.trans hA₁x

namespace AffineIndependent

/-- Finite-index transport at the owner layer: two affinely independent finite families with a
common index type in affine spaces modeled on the same vector space are related by an affine
equivalence. -/
theorem exists_affineEquiv_of_finite {ι : Type*} [Finite ι]
    {P' : Type*} [AddTorsor V P'] {b : ι → P} {b' : ι → P'}
    (hb : AffineIndependent 𝕜 b) (hb' : AffineIndependent 𝕜 b') :
    ∃ T : P ≃ᵃ[𝕜] P', ∀ i, T (b i) = b' i := by
  classical
  by_cases hι : IsEmpty ι
  · let p0 : P := Classical.choice (inferInstance : Nonempty P)
    let p0' : P' := Classical.choice (inferInstance : Nonempty P')
    let T : P ≃ᵃ[𝕜] P' := AffineEquiv.mk'
      (fun x : P ↦ (LinearEquiv.refl 𝕜 V) (x -ᵥ p0) +ᵥ p0')
      (LinearEquiv.refl 𝕜 V) p0 (by intro x; simp)
    refine ⟨T, ?_⟩
    intro i
    exact (hι.false i).elim
  · letI : Nonempty ι := not_isEmpty_iff.mp hι
    let i0 : ι := Classical.choice ‹Nonempty ι›
    let v : {i : ι // i ≠ i0} → V := fun i ↦ b i -ᵥ b i0
    let v' : {i : ι // i ≠ i0} → V := fun i ↦ b' i -ᵥ b' i0
    have hv : LinearIndependent 𝕜 v := by
      simpa [v] using (affineIndependent_iff_linearIndependent_vsub 𝕜 b i0).mp hb
    have hv' : LinearIndependent 𝕜 v' := by
      simpa [v'] using (affineIndependent_iff_linearIndependent_vsub 𝕜 b' i0).mp hb'
    obtain ⟨A, hA⟩ := exists_linearEquiv_of_linearIndependent_of_finite hv hv'
    let T : P ≃ᵃ[𝕜] P' := AffineEquiv.mk'
      (fun x : P ↦ A (x -ᵥ b i0) +ᵥ b' i0)
      A (b i0) (by intro x; simp)
    refine ⟨T, ?_⟩
    intro i
    by_cases hi : i = i0
    · subst hi
      change A (b i0 -ᵥ b i0) +ᵥ b' i0 = b' i0
      simp
    · let j : {i : ι // i ≠ i0} := ⟨i, hi⟩
      have hTi : T (b i) = A (b i -ᵥ b i0) +ᵥ b' i0 := by
        change A (b i -ᵥ b i0) +ᵥ b' i0 = A (b i -ᵥ b i0) +ᵥ b' i0
        rfl
      rw [hTi]
      simpa [v, v', j] using congrArg (fun x : V ↦ x +ᵥ b' i0) (hA j)

end AffineIndependent

end AffineSpaceFintype

section AffineMapExtensionality

variable {𝕜 : Type*} {V : Type*} {P : Type*}
  [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]

namespace AffineMap

/-- Primitive extensionality at the owner layer: if the affine span of a family is all of `P`,
then agreement on that family determines an affine map uniquely. -/
theorem ext_of_range_affineSpan_eq_top
    {ι : Type*} {b : ι → P}
    (hspan : affineSpan 𝕜 (Set.range b) = ⊤)
    {V₂ : Type*} {P₂ : Type*}
    [AddCommGroup V₂] [Module 𝕜 V₂] [AddTorsor V₂ P₂]
    {S T : P →ᵃ[𝕜] P₂} (hST : ∀ i, S (b i) = T (b i)) :
    S = T := by
  exact AffineMap.ext_on (s := Set.range b) hspan (by
    rintro x ⟨i, rfl⟩
    exact hST i)

end AffineMap

namespace AffineEquiv

/-- Primitive extensionality specialization for affine equivalences. -/
theorem ext_of_range_affineSpan_eq_top
    {ι : Type*} {b : ι → P}
    (hspan : affineSpan 𝕜 (Set.range b) = ⊤)
    {V₂ : Type*} {P₂ : Type*}
    [AddCommGroup V₂] [Module 𝕜 V₂] [AddTorsor V₂ P₂]
    {S T : P ≃ᵃ[𝕜] P₂} (hST : ∀ i, S (b i) = T (b i)) :
    S = T := by
  exact (AffineEquiv.toAffineMap_inj).1 <|
    AffineMap.ext_of_range_affineSpan_eq_top (b := b) (hspan := hspan) hST

end AffineEquiv

namespace AffineBasis

/-- Extensionality from an affine basis owner: agreement on basis points determines an affine map
uniquely. -/
theorem affineMap_ext {ι : Type*} (b : AffineBasis ι 𝕜 P)
    {V₂ : Type*} {P₂ : Type*}
    [AddCommGroup V₂] [Module 𝕜 V₂] [AddTorsor V₂ P₂]
    {S T : P →ᵃ[𝕜] P₂} (hST : ∀ i, S (b i) = T (b i)) :
    S = T := by
  exact AffineMap.ext_of_range_affineSpan_eq_top (b := b) b.tot hST

/-- Extensionality from an affine basis owner, specialized to affine equivalences. -/
theorem affineEquiv_ext {ι : Type*} (b : AffineBasis ι 𝕜 P)
    {V₂ : Type*} {P₂ : Type*}
    [AddCommGroup V₂] [Module 𝕜 V₂] [AddTorsor V₂ P₂]
    {S T : P ≃ᵃ[𝕜] P₂} (hST : ∀ i, S (b i) = T (b i)) :
    S = T := by
  exact AffineEquiv.ext_of_range_affineSpan_eq_top (b := b) b.tot hST

end AffineBasis

end AffineMapExtensionality

section FiniteDimensionalExtensionality

variable {𝕜 : Type*} {V : Type*} {P : Type*}
  [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
  [FiniteDimensional 𝕜 V]
variable {ι : Type*} [Fintype ι]

namespace AffineIndependent

/-- Finite-dimensional extensionality at the canonical owner layer: an affine map out of `P` is
uniquely determined by its values on an affinely independent family of cardinality
`finrank + 1`. -/
theorem affineMap_ext_of_card_eq_finrank_add_one
    {V₂ : Type*} {P₂ : Type*}
    [AddCommGroup V₂] [Module 𝕜 V₂] [AddTorsor V₂ P₂]
    {b : ι → P} (hb : AffineIndependent 𝕜 b)
    (hcard : Fintype.card ι = Module.finrank 𝕜 V + 1)
    {S T : P →ᵃ[𝕜] P₂} (hST : ∀ i, S (b i) = T (b i)) :
    S = T := by
  let B : AffineBasis ι 𝕜 P := ⟨b, hb, (hb.affineSpan_eq_top_iff_card_eq_finrank_add_one).2 hcard⟩
  exact AffineBasis.affineMap_ext B hST

/-- Theorem 1.6 (uniqueness), finite-dimensional owner-level specialization: an affine equivalence
out of `P` is uniquely determined by its values on an affinely independent family whose
cardinality is `finrank + 1`. -/
theorem affineEquiv_ext_of_card_eq_finrank_add_one {b : ι → P} (hb : AffineIndependent 𝕜 b)
    (hcard : Fintype.card ι = Module.finrank 𝕜 V + 1)
    {V₂ : Type*} {P₂ : Type*}
    [AddCommGroup V₂] [Module 𝕜 V₂] [AddTorsor V₂ P₂]
    {S T : P ≃ᵃ[𝕜] P₂} (hST : ∀ i, S (b i) = T (b i)) :
    S = T := by
  let B : AffineBasis ι 𝕜 P := ⟨b, hb, (hb.affineSpan_eq_top_iff_card_eq_finrank_add_one).2 hcard⟩
  exact AffineBasis.affineEquiv_ext B hST

end AffineIndependent

end FiniteDimensionalExtensionality
