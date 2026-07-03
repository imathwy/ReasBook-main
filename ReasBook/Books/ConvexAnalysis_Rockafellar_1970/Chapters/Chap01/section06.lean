import Mathlib
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_1_6_1 (from Chap01) -/
open AffineSubspace
open scoped AffineSubspace

/- 
Source/core/bridge triage:
- `source-facing`: Corollary 1.6.1 says that affine subspaces with the same affine dimension are
  related by an ambient affine automorphism.
- `core/canonical`: the owner abstractions are `AffineSubspace.affineDim`, `AffineBasis`,
  `AffineIndependent`, and `AffineEquiv`.
- `bridge/view`: the theorem below is the source-facing bridge from equal affine dimensions to the
  ambient transport theorem `AffineIndependent.exists_affineEquiv_of_finite`.
- Layer target: `source-facing`, but stated on the owner affine-space abstraction rather than the
  concrete coordinate model `ℝ^n`; specializing to `EuclideanSpace ℝ (Fin n)` recovers the
  textbook statement unchanged.
- Primitive data vs derived API: the affine subspaces and their affine dimensions are primitive;
  the ambient affine automorphism is derived theorem-level API and should not be repackaged.
- Domain-style sampling used here: `AffineSubspace.affineDim`,
  `AffineBasis.exists_affineBasis_of_finiteDimensional`,
  `AffineIndependent.affineSpan_eq_of_le_of_card_eq_finrank_add_one`, and
  `AffineIndependent.exists_affineEquiv_of_finite`.
-/

section AffineSpace

variable {𝕜 : Type*} {V : Type*} {P : Type*}
  [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]

namespace AffineSubspace

/-- Source-facing owner for ambient affine-equivalence of affine subspaces. -/
abbrev IsAffineEquivalent (M₁ M₂ : AffineSubspace 𝕜 P) : Prop :=
  ∃ T : P ≃ᵃ[𝕜] P, M₁.map T = M₂

-- Source-facing relation notation: `M₁ ≈ᵃ M₂` means that an ambient affine automorphism of `P`
-- maps `M₁` onto `M₂`.
scoped[AffineSubspace] notation:50 M₁ " ≈ᵃ " M₂ =>
  AffineSubspace.IsAffineEquivalent M₁ M₂

/-- Internal bridge theorem: two nonempty affine subspaces with finite-dimensional directions and
equal direction `finrank` are related by an ambient affine automorphism. -/
private theorem exists_map_eq_of_ne_bot_of_finrank_direction_eq
    (M₁ M₂ : AffineSubspace 𝕜 P)
    [FiniteDimensional 𝕜 M₁.direction] [FiniteDimensional 𝕜 M₂.direction]
    (hM₁ : M₁ ≠ ⊥) (hM₂ : M₂ ≠ ⊥)
    (hfinrank : Module.finrank 𝕜 M₁.direction = Module.finrank 𝕜 M₂.direction) :
    M₁ ≈ᵃ M₂ := by
  classical
  letI : Nonempty M₁ := ((nonempty_iff_ne_bot M₁).2 hM₁).to_subtype
  letI : Nonempty M₂ := ((nonempty_iff_ne_bot M₂).2 hM₂).to_subtype
  let ι := Fin (Module.finrank 𝕜 M₁.direction + 1)
  have hι₁ : Fintype.card ι = Module.finrank 𝕜 M₁.direction + 1 := by
    simp [ι]
  have hι₂ : Fintype.card ι = Module.finrank 𝕜 M₂.direction + 1 := by
    simp [ι, hfinrank]
  obtain ⟨B₁⟩ : Nonempty (AffineBasis ι 𝕜 M₁) :=
    AffineBasis.exists_affineBasis_of_finiteDimensional hι₁
  obtain ⟨B₂⟩ : Nonempty (AffineBasis ι 𝕜 M₂) :=
    AffineBasis.exists_affineBasis_of_finiteDimensional hι₂
  let b₁ : ι → P := M₁.subtype ∘ B₁
  let b₂ : ι → P := M₂.subtype ∘ B₂
  have hb₁ : AffineIndependent 𝕜 b₁ :=
    B₁.ind.map' M₁.subtype M₁.subtype_injective
  have hb₂ : AffineIndependent 𝕜 b₂ :=
    B₂.ind.map' M₂.subtype M₂.subtype_injective
  have hle₁ : affineSpan 𝕜 (Set.range b₁) ≤ M₁ := by
    rw [affineSpan_le]
    rintro _ ⟨i, rfl⟩
    exact (B₁ i).property
  have hle₂ : affineSpan 𝕜 (Set.range b₂) ≤ M₂ := by
    rw [affineSpan_le]
    rintro _ ⟨i, rfl⟩
    exact (B₂ i).property
  have hspan₁ : affineSpan 𝕜 (Set.range b₁) = M₁ := by
    exact hb₁.affineSpan_eq_of_le_of_card_eq_finrank_add_one hle₁ hι₁
  have hspan₂ : affineSpan 𝕜 (Set.range b₂) = M₂ := by
    exact hb₂.affineSpan_eq_of_le_of_card_eq_finrank_add_one hle₂ hι₂
  obtain ⟨T, hT⟩ := AffineIndependent.exists_affineEquiv_of_finite hb₁ hb₂
  refine ⟨T, ?_⟩
  calc
    M₁.map T = (affineSpan 𝕜 (Set.range b₁)).map T := by
      rw [hspan₁]
    _ = affineSpan 𝕜 (T.toAffineMap '' Set.range b₁) := by
      rw [AffineSubspace.map_span]
    _ = affineSpan 𝕜 (Set.range b₂) := by
      congr 1
      ext x
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, by simpa using (hT i).symm⟩
      · rintro ⟨i, rfl⟩
        exact ⟨b₁ i, ⟨i, rfl⟩, hT i⟩
    _ = M₂ := hspan₂

/-- Corollary 1.6.1, stated at the affine-space owner level: if two affine subspaces have the
same affine dimension, then an ambient affine automorphism maps one onto the other. Specializing
to `EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝ^n` statement. -/
-- Corollary bridge: equal affine dimensions imply equal direction `finrank` in the nonempty case,
-- then apply `exists_map_eq_of_ne_bot_of_finrank_direction_eq`.
theorem exists_map_eq_of_affineDim_eq
    (M₁ M₂ : AffineSubspace 𝕜 P)
    [FiniteDimensional 𝕜 M₁.direction] [FiniteDimensional 𝕜 M₂.direction]
    (hdim : M₁.affineDim = M₂.affineDim) :
    M₁ ≈ᵃ M₂ := by
  by_cases hM₁ : M₁ = ⊥
  · have hM₂ : M₂ = ⊥ := by
      by_contra hM₂
      rw [affineDim, if_pos hM₁, affineDim, if_neg hM₂] at hdim
      omega
    refine ⟨AffineEquiv.refl 𝕜 P, ?_⟩
    simp [hM₁, hM₂]
  · have hM₂ : M₂ ≠ ⊥ := by
      intro hM₂
      rw [affineDim, if_neg hM₁, affineDim, if_pos hM₂] at hdim
      omega
    have hfinrank :
        Module.finrank 𝕜 M₁.direction = Module.finrank 𝕜 M₂.direction := by
      rw [affineDim, if_neg hM₁, affineDim, if_neg hM₂] at hdim
      exact Int.ofNat.inj hdim
    exact exists_map_eq_of_ne_bot_of_finrank_direction_eq M₁ M₂ hM₁ hM₂ hfinrank

/-- Affine dimension is invariant under affine equivalences. -/
theorem affineDim_map_eq {V₂ : Type*} {P₂ : Type*}
    [AddCommGroup V₂] [Module 𝕜 V₂] [AddTorsor V₂ P₂]
    (M : AffineSubspace 𝕜 P) [FiniteDimensional 𝕜 M.direction]
    (T : P ≃ᵃ[𝕜] P₂) :
    ((M.map T : AffineSubspace 𝕜 P₂)).affineDim = M.affineDim := by
  by_cases hM : M = ⊥
  · subst hM
    have hmap : ((⊥ : AffineSubspace 𝕜 P).map T : AffineSubspace 𝕜 P₂) = ⊥ := by
      simp
    rw [affineDim, if_pos hmap, affineDim, if_pos rfl]
  · have hmap : (M.map T : AffineSubspace 𝕜 P₂) ≠ ⊥ := by
      intro hbot
      exact hM ((AffineSubspace.map_eq_bot_iff (s := M) (f := (T : P →ᵃ[𝕜] P₂))).1 hbot)
    have hfinrank :
        Module.finrank 𝕜 (M.map T : AffineSubspace 𝕜 P₂).direction =
          Module.finrank 𝕜 M.direction := by
      rw [AffineSubspace.map_direction]
      simpa using (LinearEquiv.finrank_eq (T.linear.submoduleMap M.direction)).symm
    rw [affineDim, if_neg hmap, affineDim, if_neg hM]
    exact_mod_cast hfinrank

/-- If one affine subspace is the image of another under an ambient affine automorphism, then they
have the same affine dimension. -/
theorem affineDim_eq_of_exists_map_eq {M₁ M₂ : AffineSubspace 𝕜 P}
    [FiniteDimensional 𝕜 M₁.direction] [FiniteDimensional 𝕜 M₂.direction]
    (h : M₁ ≈ᵃ M₂) :
    M₁.affineDim = M₂.affineDim := by
  rcases h with ⟨T, hT⟩
  simpa [hT] using (affineDim_map_eq (M := M₁) T).symm

/-- Classification at the owner layer: two affine subspaces are related by an ambient affine
automorphism exactly when their affine dimensions are equal. -/
theorem exists_map_eq_iff_affineDim_eq
    (M₁ M₂ : AffineSubspace 𝕜 P)
    [FiniteDimensional 𝕜 M₁.direction] [FiniteDimensional 𝕜 M₂.direction] :
    (M₁ ≈ᵃ M₂) ↔ M₁.affineDim = M₂.affineDim := by
  constructor
  · exact affineDim_eq_of_exists_map_eq
  · exact exists_map_eq_of_affineDim_eq M₁ M₂

end AffineSubspace

end AffineSpace

/-! ### Text_1_6 (from Chap01) -/
open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Text 1.6 names the orthogonal complement of a linear subspace.
- `core/canonical`: at the chapter API layer, this notion only needs pairing-evaluation vanishing,
  so the owner is the pairing annihilator `Submodule.pairingOrthogonal`.
- `bridge/view` (dual model): in the concrete algebraic-dual model this owner is exactly
  mathlib's canonical
  `Submodule.dualAnnihilator`, via `Submodule.pairingOrthogonal_eq_dualAnnihilator`.
- `bridge/view` (inner-product specialization): the textbook notation `Kᗮ` is recorded by
  `Submodule.pairingOrthogonal_eq_orthogonal` and, for the canonical real instance,
  `Submodule.pairingOrthogonal_eq_orthogonal_real`.
- Primitive data vs derived API: primitive data are a submodule `K` and a pairing
  `HasLinearPairing X Y 𝕜`; inner-product self-pairing is derived bridge data.
- Domain-style sampling used here: `HasLinearPairing.pairingLinear.flip`,
  `Submodule.dualAnnihilator`, `Submodule.comap`, `Submodule.orthogonal`,
  `Submodule.mem_orthogonal`.
- Layer target: `core/canonical` at the pairing layer, with the inner-product owner retained as a
  thin specialization.
- Canonicalization checks:
  - codomain/ambient: the owner is submodule-level annihilation; no concrete coordinate codomain.
  - scalar/structure: only `CommSemiring`/module data are used for the owner; inner-product
    bridges use the `Submodule.orthogonal` API layer, whose ambient assumptions are inherited.
  - owner choice: keep `Submodule.pairingOrthogonal` as the intrinsic chapter owner and treat
    `Submodule.orthogonal` as a bridge/view.
  - topology/intrinsic language: no ambient-topology owner is introduced in this item.
  - notation surface: use the textbook-style postfix `Kᗮₚ` directly on theorem surfaces.
-/
namespace Submodule

section PairingOrthogonal

variable {𝕜 : Type*} {X : Type*} {Y : Type*}
variable [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- Pairing-level orthogonal complement of a submodule: all `y` whose pairing with every
`x ∈ K` vanishes. -/
def pairingOrthogonal (K : Submodule 𝕜 X) : Submodule 𝕜 Y :=
  K.dualAnnihilator.comap
    (HasLinearPairing.pairingLinear.flip : Y →ₗ[𝕜] Module.Dual 𝕜 X)

scoped[Rockafellar] postfix:max "ᗮₚ" => Submodule.pairingOrthogonal

/-- `pairingOrthogonal` is the pullback of `dualAnnihilator` along the flipped pairing map. -/
@[simp] theorem pairingOrthogonal_eq_comap_dualAnnihilator (K : Submodule 𝕜 X) :
    Kᗮₚ = K.dualAnnihilator.comap
      (HasLinearPairing.pairingLinear.flip : Y →ₗ[𝕜] Module.Dual 𝕜 X) :=
  rfl

/-- Membership in `pairingOrthogonal` is exactly pointwise vanishing of the pairing on `K`. -/
@[simp] theorem mem_pairingOrthogonal_iff {K : Submodule 𝕜 X} {y : Y} :
    y ∈ Kᗮₚ ↔ ∀ x ∈ K, ⟪x, y⟫ₚ = (0 : 𝕜) :=
by
  simp [pairingOrthogonal, Submodule.mem_dualAnnihilator, LinearMap.flip_apply]

end PairingOrthogonal

section DualBridge

variable {𝕜 : Type*} {X : Type*}
variable [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]

/-- In the canonical evaluation pairing with the algebraic dual, `Kᗮₚ` is exactly
`K.dualAnnihilator`. -/
@[simp] theorem pairingOrthogonal_eq_dualAnnihilator (K : Submodule 𝕜 X) :
    Kᗮₚ = K.dualAnnihilator := by
  ext φ
  rw [mem_pairingOrthogonal_iff, Submodule.mem_dualAnnihilator]
  constructor
  · intro h x hx
    exact h x hx
  · intro h x hx
    exact h x hx

end DualBridge

section InnerProductMembershipBridge

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [HasLinearPairing E E 𝕜]

/-- If the chapter pairing agrees pointwise with the ambient inner product, then pairing
orthogonality is exactly textbook orthogonality. -/
@[simp] theorem mem_pairingOrthogonal_iff_inner_eq_zero
    (hpair : ∀ x y : E,
      ⟪x, y⟫ₚ = inner 𝕜 x y)
    {K : Submodule 𝕜 E} {y : E} :
    y ∈ Kᗮₚ ↔ ∀ x ∈ K, inner 𝕜 x y = 0 := by
  rw [mem_pairingOrthogonal_iff]
  constructor
  · intro hy x hx
    exact (hpair x y).symm.trans (hy x hx)
  · intro hy x hx
    exact (hpair x y).trans (hy x hx)

end InnerProductMembershipBridge

section InnerProductOrthogonalBridge

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [HasLinearPairing E E 𝕜]

/-- If the chapter pairing agrees pointwise with the ambient inner product, then pairing
orthogonality is exactly textbook orthogonality. -/
theorem pairingOrthogonal_eq_orthogonal
    (hpair : ∀ x y : E,
      ⟪x, y⟫ₚ = inner 𝕜 x y)
    (K : Submodule 𝕜 E) :
    Kᗮₚ = (Kᗮ : Submodule 𝕜 E) := by
  ext y
  simpa [Submodule.mem_orthogonal] using
    (mem_pairingOrthogonal_iff_inner_eq_zero (hpair := hpair) (K := K) (y := y))

end InnerProductOrthogonalBridge

section InnerProductMembershipBridgeReal

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For the canonical real inner-product pairing, pairing orthogonality is exactly `Kᗮ`. -/
@[simp] theorem mem_pairingOrthogonal_iff_inner_eq_zero_real
    {K : Submodule ℝ E} {y : E} :
    y ∈ Kᗮₚ ↔ ∀ x ∈ K, inner ℝ x y = 0 :=
  mem_pairingOrthogonal_iff_inner_eq_zero (hpair := by intro x y; rfl)

end InnerProductMembershipBridgeReal

section InnerProductOrthogonalBridgeReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For the canonical real inner-product pairing, pairing orthogonality is exactly `Kᗮ`. -/
@[simp] theorem pairingOrthogonal_eq_orthogonal_real (K : Submodule ℝ E) :
    Kᗮₚ = (Kᗮ : Submodule ℝ E) :=
  pairingOrthogonal_eq_orthogonal (hpair := by intro x y; rfl) K

end InnerProductOrthogonalBridgeReal

/- Text 1.6: the canonical chapter owner for orthogonal complement is the pairing-level
`Submodule.pairingOrthogonal` (surface notation `Kᗮₚ`); the textbook inner-product owner `Kᗮ`
(i.e. `Submodule.orthogonal`) is recovered as the bridge specialization
`pairingOrthogonal_eq_orthogonal_real`. -/
recall pairingOrthogonal
recall pairingOrthogonal_eq_comap_dualAnnihilator
recall mem_pairingOrthogonal_iff
recall pairingOrthogonal_eq_dualAnnihilator
recall Submodule.orthogonal
recall Submodule.mem_orthogonal
recall Submodule.mem_orthogonal'
recall mem_pairingOrthogonal_iff_inner_eq_zero
recall mem_pairingOrthogonal_iff_inner_eq_zero_real
recall pairingOrthogonal_eq_orthogonal
recall pairingOrthogonal_eq_orthogonal_real

end Submodule

/-! ### Theorem_1_6 (from Chap01) -/
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
