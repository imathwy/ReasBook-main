import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_4_10
import ConvexAnalysis_Rockafellar_1970.Chap01.Corollary_1_6_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {𝕜 : Type*} [DivisionRing 𝕜] {n : ℕ}

open scoped Rockafellar
open scoped AffineSubspace
open AffineSubspace

local notation "E" => Fin n → 𝕜

/- 
Source/core/bridge triage:
- `source-facing`: Text 6.16 records the standard coordinate-model reduction for an
  `m`-dimensional convex subset of `ℝ^n`: after an affine automorphism of the ambient space, its
  affine hull becomes the coordinate subspace cut out by the equations `x_i = 0` for `i ≥ m`.
- `core/canonical`: the owner abstractions are the chapter set-dimension bridge `Set.affineDim`,
  the affine-subspace owner `AffineSubspace.affineDim`, affine-subspace transport by
  `AffineSubspace.map`, and the existing ambient transport theorem
  `AffineSubspace.exists_map_eq_of_affineDim_eq`.
- `bridge/view`: `standardCoordinateSubspace m n` is the concrete coordinate model used later in
  coordinate arguments; the affine-equivalence theorem below is just the
  specialization of the chapter owner theorem to the affine hull of a set and that coordinate
  owner, with the hypothesis stated in source-facing notation `dim[𝕜](C)` rather than on the
  lower-level affine-subspace expression `(affineSpan 𝕜 C).affineDim`.
- Primitive data vs derived API: the primitive datum is the coordinate subspace itself, best
  presented by the source equations `x_i = 0` for `i ≥ m`; internally this is the coordinatewise
  `Submodule.pi` on `Fin n → 𝕜`. Its affine dimension and the ambient affine-equivalence theorem
  are derived API. Accordingly, the submodule owner is exposed at semiring level and only the
  affine wrapper / affine-dimension layer asks for stronger structure.
- Domain-style sampling used here:
  `Set.affineDim`,
  `AffineSubspace.affineDim`,
  `AffineSubspace.exists_map_eq_of_affineDim_eq`,
  `Submodule.pi`,
  `LinearMap.iInfKerProjEquiv`,
  and `Submodule.toAffineSubspace`.
- Layer target: `bridge/view`. The reusable owner name `standardCoordinateSubspace` is kept
  because it materially shortens later coordinate normal-form statements, while the main theorem is
  expressed on `Set.affineDim` and derived directly from the existing affine-subspace owner
  theorem.
- Topology / intrinsic-relative checklist item: intentionally non-applicable for this item. The
  statement is purely affine-algebraic (affine dimension and affine equivalence to a coordinate
  affine subspace), with no ambient/interior/closure formulation to replace by an intrinsic
  topological variant.
-/

/-- The standard coordinate subspace of `𝕜^n`, represented as `Fin n → 𝕜`, cut out by the equations
`x_i = 0` for every coordinate with index at least `m`. -/
def standardCoordinateSubspace (𝕜 : Type*) [Semiring 𝕜] (m n : ℕ) :
    Submodule 𝕜 (Fin n → 𝕜) :=
  Submodule.pi {i : Fin n | m ≤ (i : ℕ)} (fun _ ↦ (⊥ : Submodule 𝕜 𝕜))

/-- A vector belongs to the standard coordinate subspace exactly when every coordinate with index
at least `m` vanishes. -/
@[simp] theorem mem_standardCoordinateSubspace_iff
    {𝕜 : Type*} [Semiring 𝕜] {m n : ℕ} {x : Fin n → 𝕜} :
    x ∈ standardCoordinateSubspace 𝕜 m n ↔ ∀ i : Fin n, m ≤ (i : ℕ) → x i = 0 :=
  by
    simp [standardCoordinateSubspace]

/-- A vector belongs to the affine subspace associated to the standard coordinate subspace exactly
when every coordinate with index at least `m` vanishes. -/
@[simp] theorem mem_toAffineSubspace_standardCoordinateSubspace_iff
    {𝕜 : Type*} [Ring 𝕜] {m n : ℕ} {x : Fin n → 𝕜} :
    x ∈ (standardCoordinateSubspace 𝕜 m n).toAffineSubspace ↔
      ∀ i : Fin n, m ≤ (i : ℕ) → x i = 0 := by
  simp [Submodule.mem_toAffineSubspace,
    (mem_standardCoordinateSubspace_iff (𝕜 := 𝕜) (m := m) (n := n) (x := x))
  ]

private theorem standardCoordinateSubspace_finrank {m n : ℕ} :
    Module.finrank 𝕜 (standardCoordinateSubspace 𝕜 m n : Submodule 𝕜 (Fin n → 𝕜)) =
      min m n := by
  let I : Set (Fin n) := {i | (i : ℕ) < m}
  let J : Set (Fin n) := {i | m ≤ (i : ℕ)}
  have hcoord :
      (standardCoordinateSubspace 𝕜 m n : Submodule 𝕜 (Fin n → 𝕜)) =
        ⨅ i ∈ J, LinearMap.ker (LinearMap.proj i : (Fin n → 𝕜) →ₗ[𝕜] 𝕜) := by
    ext x
    simp [standardCoordinateSubspace, J, LinearMap.mem_ker]
  have hd : Disjoint I J := by
    rw [Set.disjoint_left]
    intro i hiI hiJ
    have hiI' : (i : ℕ) < m := by simpa [I] using hiI
    have hiJ' : m ≤ (i : ℕ) := by simpa [J] using hiJ
    exact not_le_of_gt hiI' hiJ'
  have hu : Set.univ ⊆ I ∪ J := by
    intro i _
    by_cases hi : (i : ℕ) < m
    · exact Or.inl <| by simpa [I] using hi
    · exact Or.inr <| by simpa [J] using Nat.le_of_not_gt hi
  let e :
      ↥(⨅ i ∈ J, LinearMap.ker (LinearMap.proj i : (Fin n → 𝕜) →ₗ[𝕜] 𝕜)) ≃ₗ[𝕜]
        (i : I) → 𝕜 :=
    LinearMap.iInfKerProjEquiv 𝕜 (fun _ : Fin n ↦ 𝕜) hd hu
  calc
    Module.finrank 𝕜 (standardCoordinateSubspace 𝕜 m n : Submodule 𝕜 (Fin n → 𝕜)) =
        Module.finrank 𝕜 ↥(⨅ i ∈ J, LinearMap.ker (LinearMap.proj i : (Fin n → 𝕜) →ₗ[𝕜] 𝕜)) := by
          rw [hcoord]
    _ = Module.finrank 𝕜 ((i : I) → 𝕜) := LinearEquiv.finrank_eq e
    _ = min m n := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_subtype]
      simpa [I, Nat.min_comm] using
        (@Fin.card_filter_val_lt n m)

/-- The standard coordinate affine subspace has affine dimension `min m n`. -/
theorem standardCoordinateAffineSubspace_affineDim_eq_min {m : ℕ} :
    ((standardCoordinateSubspace 𝕜 m n).toAffineSubspace).affineDim = min m n := by
  have hfinrank : Module.finrank 𝕜 (standardCoordinateSubspace 𝕜 m n) = min m n :=
    standardCoordinateSubspace_finrank
  have hnonbot : (standardCoordinateSubspace 𝕜 m n).toAffineSubspace ≠ ⊥ := by
    intro h
    have hzero : (0 : E) ∈ (standardCoordinateSubspace 𝕜 m n).toAffineSubspace := by
      simp [Submodule.mem_toAffineSubspace]
    simpa [h] using hzero
  letI : FiniteDimensional 𝕜 (standardCoordinateSubspace 𝕜 m n : Submodule 𝕜 E) := inferInstance
  letI :
      FiniteDimensional 𝕜
        ((standardCoordinateSubspace 𝕜 m n).toAffineSubspace).direction := by
    rwa [Submodule.toAffineSubspace_direction]
  rw [AffineSubspace.affineDim, if_neg hnonbot,
    Submodule.toAffineSubspace_direction]
  exact_mod_cast hfinrank

/-- The standard coordinate affine subspace has affine dimension `m` when `m ≤ n`. -/
theorem standardCoordinateAffineSubspace_affineDim {m : ℕ} (hmn : m ≤ n) :
    ((standardCoordinateSubspace 𝕜 m n).toAffineSubspace).affineDim = m := by
  simpa [Nat.min_eq_left hmn] using
    (standardCoordinateAffineSubspace_affineDim_eq_min (𝕜 := 𝕜) (n := n) (m := m))

namespace AffineSubspace

/-- Owner-level coordinate normal form for Text 6.16: an affine subspace of `𝕜^n` with affine
dimension `m` is affinely equivalent to the standard coordinate affine subspace cut out by
`x_i = 0` for `i ≥ m`. -/
theorem exists_map_eq_standardCoordinateAffineSubspace_of_affineDim_eq
    {m : ℕ} {A : AffineSubspace 𝕜 E}
    (hAdim : A.affineDim = m) :
    A ≈ᵃ
      (standardCoordinateSubspace 𝕜 m n).toAffineSubspace := by
  have hmn : m ≤ n := by
    have hA_ne : A ≠ ⊥ := by
      intro hA_bot
      rw [AffineSubspace.affineDim, if_pos hA_bot] at hAdim
      omega
    have hfinrank : Module.finrank 𝕜 A.direction = m := by
      rw [AffineSubspace.affineDim, if_neg hA_ne] at hAdim
      exact Int.ofNat.inj hAdim
    have hle : Module.finrank 𝕜 A.direction ≤ Module.finrank 𝕜 E :=
      Submodule.finrank_le _
    have hfinrankE : Module.finrank 𝕜 E = n := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    simpa [hfinrank, hfinrankE] using hle
  have hdim :
      A.affineDim = ((standardCoordinateSubspace 𝕜 m n).toAffineSubspace).affineDim := by
    exact hAdim.trans (standardCoordinateAffineSubspace_affineDim (𝕜 := 𝕜) (n := n) hmn).symm
  exact AffineSubspace.exists_map_eq_of_affineDim_eq A
    ((standardCoordinateSubspace 𝕜 m n).toAffineSubspace) hdim

end AffineSubspace

namespace Set

/-- Text 6.16 on the canonical coordinate owner layer: if a subset of `𝕜^n`, represented by
`Fin n → 𝕜`, has affine dimension `m`, then some affine automorphism of `𝕜^n` carries that affine
hull onto the standard coordinate affine subspace `{x | x_i = 0 for every i ≥ m}`. Specializing to
`𝕜 = ℝ` recovers the textbook `ℝ^n` statement. -/
theorem exists_affineEquiv_affineSpan_eq_standardCoordinateAffineSubspace
    {m : ℕ} {C : Set E}
    (hCdim : dim[𝕜](C) = m) :
    (affineSpan 𝕜 C) ≈ᵃ
      (standardCoordinateSubspace 𝕜 m n).toAffineSubspace := by
  have hspanDim : (affineSpan 𝕜 C).affineDim = m := by
    simpa [Set.affineDim] using hCdim
  exact AffineSubspace.exists_map_eq_standardCoordinateAffineSubspace_of_affineDim_eq
    (A := affineSpan 𝕜 C) hspanDim

end Set

end
