import Mathlib.Analysis.Matrix.Normed
import Mathlib.RepresentationTheory.Character
import Mathlib.Tactic.Recall
import LinearRepresentations_Serre_1977.Chap02.Proposition_2_2_1_1
import LinearRepresentations_Serre_1977.Chap04.Definition_4_9

/- Source/core/bridge triage:
- `source-facing`: Proposition 4-18 packages three character identities for finite-dimensional
  continuous complex representations of compact groups.
- `core/canonical`: parts (1) and (3) are already the canonical theorems
  `Representation.char_one` and `Representation.char_conj`.
- `bridge/view`: part (2) is the genuine compact-group refinement, since the chapter hypotheses
  add content beyond the earlier finite-order character identity.

Accordingly, this file recalls the canonical owners for (1) and (3), and keeps only the compact
continuous bridge theorem as a local declaration.
-/

noncomputable section

open scoped Matrix.Norms.Operator

/- Proposition 4-18 (1): for a finite-dimensional representation, the character at `1` is the
degree `Module.finrank ℂ V`. In Chapter 4 this is applied to continuous representations of compact
groups, but the identity itself is already the canonical theorem `Representation.char_one`. -/
recall Representation.char_one

namespace Representation

section

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [T2Space V] [FiniteDimensional ℂ V]
variable (ρ : Representation ℂ G V) [ρ.IsContinuous]

open Module.End

/-- Helper for Proposition 4-18: in a finite basis, the matrix coefficients of a continuous
representation vary continuously with the group element. -/
lemma continuous_toMatrix (ρ : Representation ℂ G V) [ρ.IsContinuous]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ V) :
    Continuous fun g : G ↦ LinearMap.toMatrix b b (ρ g) := by
  -- Check continuity entrywise by writing each matrix coefficient as a basis coordinate of an orbit
  -- map.
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simpa [LinearMap.toMatrix_apply] using
    (_root_.continuous_apply i).comp
      ((continuous_equivFun_basis b).comp (Representation.continuous_apply ρ (b j)))

/-- Helper for Proposition 4-18: compactness gives a uniform bound on the matrices of `ρ g` in any
finite basis. -/
lemma exists_bound_toMatrix (ρ : Representation ℂ G V) [ρ.IsContinuous]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ V) :
    ∃ C, ∀ g : G, ‖LinearMap.toMatrix b b (ρ g)‖ ≤ C := by
  -- A continuous map on the compact space `G` is uniformly bounded in sup norm.
  let F : C(G, Matrix ι ι ℂ) := ⟨fun g ↦ LinearMap.toMatrix b b (ρ g),
    Representation.continuous_toMatrix ρ b⟩
  refine ⟨‖F‖, fun g ↦ ?_⟩
  simpa [F] using ContinuousMap.norm_coe_le_norm F g

/-- Helper for Proposition 4-18: in basis coordinates, `f x` is obtained by multiplying the
coordinate vector of `x` by the matrix of `f`. -/
lemma toMatrix_mulVec_equivFun {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ V) (f : Module.End ℂ V) (x : V) :
    Matrix.mulVec (LinearMap.toMatrix b b f) (b.equivFun x) = b.equivFun (f x) := by
  ext i
  -- Expand `x` in the basis, apply `f`, and then read off the `i`-th coordinate.
  symm
  calc
    b.equivFun (f x) i = b.equivFun (f (∑ j, b.equivFun x j • b j)) i := by
      rw [Module.Basis.sum_equivFun]
    _ = b.equivFun (∑ j, b.equivFun x j • f (b j)) i := by
      rw [map_sum]
      simp_rw [LinearMap.map_smulₛₗ, RingHom.id_apply]
    _ = (∑ j, b.equivFun (b.equivFun x j • f (b j))) i := by
      simp
    _ = (∑ j, b.equivFun x j • b.equivFun (f (b j))) i := by
      simp
    _ = ∑ j, b.equivFun x j * b.equivFun (f (b j)) i := by
      simp
    _ = Matrix.mulVec (LinearMap.toMatrix b b f) (b.equivFun x) i := by
      simp [Matrix.mulVec, dotProduct, LinearMap.toMatrix_apply, mul_comm]

/-- Helper for Proposition 4-18: every characteristic root of `ρ s` has norm at most `1`. -/
lemma charpolyRoot_norm_le_one_of_isContinuousCompact (s : G) {μ : ℂ}
    (hμ : μ ∈ (ρ s).charpoly.roots) :
    ‖μ‖ ≤ 1 := by
  let ι := Module.Basis.ofVectorSpaceIndex ℂ V
  let b : Module.Basis ι ℂ V := Module.Basis.ofVectorSpace ℂ V
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  obtain ⟨C, hC⟩ := exists_bound_toMatrix ρ b
  have hμeig : HasEigenvalue (ρ s) μ :=
    (hasEigenvalue_iff_isRoot_charpoly (ρ s) μ).2 <|
      (Polynomial.mem_roots (ρ s).charpoly_monic.ne_zero).1 hμ
  obtain ⟨v, hv⟩ := hμeig.exists_hasEigenvector
  have hrepr_ne : b.equivFun v ≠ 0 := by
    intro hrepr
    apply hv.2
    exact b.equivFun.injective <| by simpa using hrepr
  have hrepr_pos : 0 < ‖b.equivFun v‖ := norm_pos_iff.mpr hrepr_ne
  -- Compare the growth of the eigenvector `v` under `(ρ s)^n` with the uniformly bounded matrices
  -- of `ρ (s^n)`.
  have hpow_bound : ∀ n : ℕ, ‖μ‖ ^ n ≤ C := by
    intro n
    have hpow_apply : (ρ s ^ n) v = μ ^ n • v := by
      simpa using hv.pow_apply n
    have hmatrix_eq :
        LinearMap.toMatrix b b (ρ s ^ n) = LinearMap.toMatrix b b (ρ (s ^ n)) := by
      congr 1
      simpa using (map_pow ρ.asGroupHom s n).symm
    let T : (ι → ℂ) →L[ℂ] (ι → ℂ) :=
      (Matrix.mulVecLin (LinearMap.toMatrix b b (ρ s ^ n))).toContinuousLinearMap
    have hmul :
        ‖Matrix.mulVec (LinearMap.toMatrix b b (ρ s ^ n)) (b.equivFun v)‖
          ≤ ‖LinearMap.toMatrix b b (ρ s ^ n)‖ * ‖b.equivFun v‖ := by
      simpa [T, Matrix.linfty_opNorm_eq_opNorm] using T.le_opNorm (b.equivFun v)
    have hbound_mul :
        ‖μ ^ n‖ * ‖b.equivFun v‖ ≤ C * ‖b.equivFun v‖ := by
      calc
        ‖μ ^ n‖ * ‖b.equivFun v‖ = ‖μ ^ n • b.equivFun v‖ := by rw [norm_smul]
        _ = ‖b.equivFun (μ ^ n • v)‖ := by simp
        _ = ‖b.equivFun ((ρ s ^ n) v)‖ := by rw [hpow_apply]
        _ = ‖Matrix.mulVec (LinearMap.toMatrix b b (ρ s ^ n)) (b.equivFun v)‖ := by
          rw [toMatrix_mulVec_equivFun]
        _ ≤ ‖LinearMap.toMatrix b b (ρ s ^ n)‖ * ‖b.equivFun v‖ := hmul
        _ = ‖LinearMap.toMatrix b b (ρ (s ^ n))‖ * ‖b.equivFun v‖ := by rw [hmatrix_eq]
        _ ≤ C * ‖b.equivFun v‖ := by
          gcongr
          exact hC (s ^ n)
    have hpow_le : ‖μ ^ n‖ ≤ C := le_of_mul_le_mul_right hbound_mul hrepr_pos
    exact (by simpa [norm_pow] using hpow_le : ‖μ‖ ^ n ≤ C)
  by_contra hμ_norm
  have hμ_gt : 1 < ‖μ‖ := lt_of_not_ge hμ_norm
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hμ_gt
  exact not_lt_of_ge (hpow_bound n) <| by simpa [norm_pow] using hn

/-- Helper for Proposition 4-18: the inverse of a nonzero characteristic root of `ρ s` is a
characteristic root of `ρ s⁻¹`. -/
lemma charpolyRootInvMemRoots (s : G) {μ : ℂ} (hμ : μ ∈ (ρ s).charpoly.roots) :
    μ ≠ 0 ∧ μ⁻¹ ∈ (ρ s⁻¹).charpoly.roots := by
  have hμeig : HasEigenvalue (ρ s) μ :=
    (hasEigenvalue_iff_isRoot_charpoly (ρ s) μ).2 <|
      (Polynomial.mem_roots (ρ s).charpoly_monic.ne_zero).1 hμ
  obtain ⟨v, hv⟩ := hμeig.exists_hasEigenvector
  have hμ_ne : μ ≠ 0 := by
    intro hμ_zero
    have hzero : ρ s v = 0 := by simpa [hμ_zero] using hv.apply_eq_smul
    have hzero' := congrArg (fun w ↦ ρ s⁻¹ w) hzero
    exact hv.2 <| by simpa [Representation.self_inv_apply] using hzero'
  have hv_inv : Module.End.HasEigenvector (ρ s⁻¹) (μ⁻¹) v := by
    rw [hasEigenvector_iff]
    refine ⟨?_, hv.2⟩
    rw [mem_eigenspace_iff]
    -- Apply `ρ s⁻¹` to the eigenvector equation and cancel the nonzero scalar `μ`.
    calc
      ρ s⁻¹ v = μ⁻¹ • (μ • ρ s⁻¹ v) := by
        simp [smul_smul, hμ_ne]
      _ = μ⁻¹ • v := by
        congr 1
        calc
          μ • ρ s⁻¹ v = ρ s⁻¹ (μ • v) := by simp
          _ = ρ s⁻¹ (ρ s v) := by rw [hv.apply_eq_smul]
          _ = v := by simpa [Representation.self_inv_apply]
  have hμinv_eig : HasEigenvalue (ρ s⁻¹) μ⁻¹ :=
    hasEigenvalue_of_hasEigenvector hv_inv
  refine ⟨hμ_ne, ?_⟩
  exact
    (Polynomial.mem_roots (ρ s⁻¹).charpoly_monic.ne_zero).2 <|
      (hasEigenvalue_iff_isRoot_charpoly (ρ s⁻¹) (μ⁻¹)).1 hμinv_eig

/-- Helper for Proposition 4-18: every characteristic root of `ρ s` lies on the unit circle. -/
lemma charpolyRoot_norm_eq_one_of_isContinuousCompact (s : G) {μ : ℂ}
    (hμ : μ ∈ (ρ s).charpoly.roots) :
    ‖μ‖ = 1 := by
  have hμ_le : ‖μ‖ ≤ 1 := ρ.charpolyRoot_norm_le_one_of_isContinuousCompact s hμ
  rcases ρ.charpolyRootInvMemRoots s hμ with ⟨hμ_ne, hμinv⟩
  have hμinv_le : ‖μ⁻¹‖ ≤ 1 :=
    ρ.charpolyRoot_norm_le_one_of_isContinuousCompact s⁻¹ hμinv
  have hμ_pos : 0 < ‖μ‖ := norm_pos_iff.mpr hμ_ne
  have hμ_ge : 1 ≤ ‖μ‖ := by
    have hinv : ‖μ‖⁻¹ ≤ 1 := by simpa [norm_inv] using hμinv_le
    exact (inv_le_one₀ hμ_pos).1 hinv
  exact le_antisymm hμ_le hμ_ge

/-- Helper for Proposition 4-18: complex conjugation inverts each characteristic root of `ρ s`. -/
lemma star_eq_inv_of_charpoly_root_of_isContinuousCompact (s : G) {μ : ℂ}
    (hμ : μ ∈ (ρ s).charpoly.roots) :
    star μ = μ⁻¹ := by
  -- Once the root lies on the unit circle, `Complex.inv_eq_conj` gives the desired scalar identity.
  simpa using (Complex.inv_eq_conj (ρ.charpolyRoot_norm_eq_one_of_isContinuousCompact s hμ)).symm

/-- Proposition 4-18 (2): for a finite-dimensional continuous representation of a compact group,
the character satisfies `χ(s⁻¹) = star (χ(s))`. This is the Chapter 4 compact-group bridge beyond
the earlier finite-order theorem `Representation.char_inv_eq_star_of_isOfFinOrder`. -/
theorem char_inv_eq_star_of_isContinuousCompact (s : G) :
    ρ.character s⁻¹ = star (ρ.character s) := by
  -- Reuse the Chapter 2 trace/root normal form; only the compact-specific root identity is new.
  change LinearMap.trace ℂ V (ρ s⁻¹) = star (ρ.character s)
  rw [ρ.trace_inv_eq_sum_inv_charpoly_roots s]
  change ((ρ s).charpoly.roots.map fun μ ↦ μ⁻¹).sum = star (LinearMap.trace ℂ V (ρ s))
  rw [trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  rw [show star (Multiset.sum (ρ s).charpoly.roots) =
      (Multiset.map star (ρ s).charpoly.roots).sum by
        simpa using map_multiset_sum (starRingEnd ℂ) ((ρ s).charpoly.roots)]
  -- Replace conjugation by inversion on each characteristic root and finish termwise.
  refine congrArg Multiset.sum ?_
  refine Multiset.map_congr rfl fun μ hμ ↦ ?_
  simpa using (ρ.star_eq_inv_of_charpoly_root_of_isContinuousCompact s hμ).symm

end

end Representation

/- Proposition 4-18 (3): the character is constant on conjugacy classes. In Chapter 4 this is
applied to continuous representations of compact groups, but the statement itself is already the
canonical theorem `Representation.char_conj`. -/
recall Representation.char_conj
