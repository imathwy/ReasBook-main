import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped InnerProductSpace
open Module End

variable {𝕜 : Type u} {G : Type v} {V : Type w}
variable [RCLike 𝕜] [Group G] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- Helper for Remark 1-1.3-2: a `G`-stable subspace is also stable under the inverse action. -/
lemma stable_preimage_mem_of_mem_invtSubmodule
    (ρ : Representation 𝕜 G V) (W : Submodule 𝕜 V)
    (hW : W ∈ ρ.invtSubmodule) :
    ∀ s : G, ∀ y : V, y ∈ W → ρ s⁻¹ y ∈ W := by
  -- Rewrite stability into the pointwise closure condition for the action.
  simp only [Representation.mem_invtSubmodule,
    Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at hW
  intro s y hy
  exact hW s⁻¹ y hy

/-- Helper for Remark 1-1.3-2: inner-product invariance sends vectors orthogonal to `W`
to vectors still orthogonal to `W`. -/
lemma orthogonal_image_mem_of_inner_invariant
    (ρ : Representation 𝕜 G V) (W : Submodule 𝕜 V)
    (hρ : ∀ s : G, ∀ x y : V, ⟪ρ s x, ρ s y⟫_𝕜 = ⟪x, y⟫_𝕜)
    (hW : W ∈ ρ.invtSubmodule) :
    ∀ s : G, ∀ x : V, x ∈ Wᗮ → ρ s x ∈ Wᗮ := by
  intro s x hx
  -- Rewrite orthogonality as vanishing against every element of `W`.
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro y hy
  -- Pull `y` back along `ρ s` so the known orthogonality of `x` applies.
  have hy' : ρ s⁻¹ y ∈ W := stable_preimage_mem_of_mem_invtSubmodule ρ W hW s y hy
  -- Inner-product invariance transports the zero pairing from `ρ s⁻¹ y` to `y`.
  simpa [ρ.self_inv_apply] using (hρ s (ρ s⁻¹ y) x).trans (hx (ρ s⁻¹ y) hy')

/-- Remark 1-1.3-2: if a representation preserves the scalar product, the orthogonal complement of
a `G`-stable subspace is again `G`-stable; together with orthogonal decomposition, this yields a
`G`-stable complementary subspace. -/
theorem orthogonalComplement_mem_invtSubmodule_of_inner_invariant
    (ρ : Representation 𝕜 G V) (W : Submodule 𝕜 V)
    (hρ : ∀ s : G, ∀ x y : V, ⟪ρ s x, ρ s y⟫_𝕜 = ⟪x, y⟫_𝕜)
    (hW : W ∈ ρ.invtSubmodule) :
    Wᗮ ∈ ρ.invtSubmodule := by
  -- The source proof reduces stability of `Wᗮ` to the pointwise orthogonality transfer.
  simp only [Representation.mem_invtSubmodule,
    Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
  exact orthogonal_image_mem_of_inner_invariant ρ W hρ hW

/-- Helper for Remark 1-1.3-2: once `Wᗮ` is packaged as a stable subspace, the usual orthogonal
decomposition theorem supplies the complementary-subspace statement. -/
lemma orthogonal_complement_is_stable_complement [FiniteDimensional 𝕜 V]
    (ρ : Representation 𝕜 G V) (W : Submodule 𝕜 V)
    (hWortho : Wᗮ ∈ ρ.invtSubmodule) :
    IsCompl W ((⟨Wᗮ, hWortho⟩ : ρ.invtSubmodule) : Submodule 𝕜 V) := by
  -- The complement is the standard orthogonal complement in a finite-dimensional space.
  simpa using W.isCompl_orthogonal_of_hasOrthogonalProjection

/-- Under an inner-product-preserving representation, every stable subspace admits the stable
orthogonal complement as a complementary subspace. -/
theorem exists_isCompl_of_mem_invtSubmodule_of_inner_invariant [FiniteDimensional 𝕜 V]
    (ρ : Representation 𝕜 G V) (W : Submodule 𝕜 V)
    (hρ : ∀ s : G, ∀ x y : V, ⟪ρ s x, ρ s y⟫_𝕜 = ⟪x, y⟫_𝕜)
    (hW : W ∈ ρ.invtSubmodule) :
    ∃ W₀ : ρ.invtSubmodule, IsCompl W (W₀ : Submodule 𝕜 V) := by
  -- Take the orthogonal complement, already shown to be stable.
  let hWortho : Wᗮ ∈ ρ.invtSubmodule :=
    orthogonalComplement_mem_invtSubmodule_of_inner_invariant ρ W hρ hW
  refine ⟨⟨Wᗮ, hWortho⟩, ?_⟩
  -- The complement statement is now just orthogonal decomposition.
  exact orthogonal_complement_is_stable_complement ρ W hWortho

/-- Helper for Remark 1-1.3-2: the action of `s` is inverted by the action of `s⁻¹`. -/
lemma representation_element_inv_comp
    (ρ : Representation 𝕜 G V) (s : G) :
    (ρ s⁻¹).comp (ρ s) = LinearMap.id := by
  -- The representation law identifies the composite with the identity map.
  ext x
  simp

/-- Helper for Remark 1-1.3-2: the action of `s⁻¹` is inverted by the action of `s`. -/
lemma representation_element_comp_inv
    (ρ : Representation 𝕜 G V) (s : G) :
    (ρ s).comp (ρ s⁻¹) = LinearMap.id := by
  -- This is the same inverse relation, written in the opposite order.
  ext x
  simp

/-- Helper for Remark 1-1.3-2: each representation operator is a linear equivalence with inverse
given by the inverse group element. -/
def representation_element_linear_equiv
    (ρ : Representation 𝕜 G V) (s : G) : V ≃ₗ[𝕜] V :=
  LinearEquiv.ofLinear (ρ s) (ρ s⁻¹)
    (representation_element_comp_inv ρ s)
    (representation_element_inv_comp ρ s)

/-- Helper for Remark 1-1.3-2: inner-product invariance upgrades a representation operator to a
linear isometry equivalence. -/
def representation_element_linear_isometry_equiv
    (ρ : Representation 𝕜 G V)
    (hρ : ∀ s : G, ∀ x y : V, ⟪ρ s x, ρ s y⟫_𝕜 = ⟪x, y⟫_𝕜)
    (s : G) : V ≃ₗᵢ[𝕜] V :=
  (representation_element_linear_equiv ρ s).isometryOfInner (hρ s)

/-- With respect to an orthonormal basis, the matrix of an inner-product-preserving
representation operator is unitary. -/
theorem toMatrix_mem_unitaryGroup_of_inner_invariant {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 V) (ρ : Representation 𝕜 G V)
    (hρ : ∀ s : G, ∀ x y : V, ⟪ρ s x, ρ s y⟫_𝕜 = ⟪x, y⟫_𝕜) (s : G) :
    (ρ s).toMatrix b.toBasis b.toBasis ∈ Matrix.unitaryGroup ι 𝕜 := by
  -- Package `ρ s` as a linear isometry equivalence and apply the standard matrix theorem.
  let hi : V ≃ₗᵢ[𝕜] V := representation_element_linear_isometry_equiv ρ hρ s
  simpa [representation_element_linear_isometry_equiv, representation_element_linear_equiv]
    using hi.toMatrix_mem_unitaryGroup b b
