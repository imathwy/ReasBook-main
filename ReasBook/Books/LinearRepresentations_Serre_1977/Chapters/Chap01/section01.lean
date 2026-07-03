import Mathlib
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RepresentationTheory.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_1_1_1 (from Chap01) -/
universe u

section

variable {G : Type u} [Group G]
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {V' : Type u} [AddCommGroup V'] [Module ℂ V']
variable (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V')

/- Definition 1-1.1-1: a complex linear representation of a group `G` on `V` is the canonical
mathlib notion `Representation ℂ G V`, namely a homomorphism from `G` to the invertible complex
linear endomorphisms of `V`. -/
recall Representation

/- Similarity of two complex representations is modeled by the equivariant linear equivalence type
`ρ.Equiv ρ'`. -/
recall Representation.Equiv

section

variable [FiniteDimensional ℂ V]

/- The degree of a finite-dimensional complex representation is its complex dimension
`Module.finrank ℂ V`. -/
recall Module.finrank

end

namespace Representation.Equiv

-- Proof sketch: forget the equivariance and apply `LinearEquiv.finrank_eq` to the underlying
-- linear equivalence `τ.toLinearEquiv`.
/-- Similar complex representations have the same complex dimension, hence the same degree
whenever both are finite-dimensional. -/
theorem finrank_eq (τ : ρ.Equiv ρ') : Module.finrank ℂ V = Module.finrank ℂ V' :=
  τ.toLinearEquiv.finrank_eq

end Representation.Equiv

end

/-! ### Definition_1_1_2_1 (from Chap01) -/
universe u

section

variable {G : Type u} [Group G]

/- Definition 1-1.2-1: a degree-1 complex representation of a group `G` is the canonical type
`G →* ℂˣ` of group homomorphisms from `G` to the multiplicative group of nonzero complex numbers. -/
#check (G →* ℂˣ)

namespace MonoidHom

/-- A degree-1 complex character canonically yields a one-dimensional complex representation. -/
def toRepresentation (ρ : G →* ℂˣ) : Representation ℂ G ℂ where
  toFun g := LinearMap.lsmul ℂ ℂ (ρ g : ℂ)
  map_one' := by
    apply LinearMap.ext
    intro z
    simp [LinearMap.lsmul_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro z
    simp [LinearMap.lsmul_apply, mul_assoc]

@[simp] theorem toRepresentation_character_apply (ρ : G →* ℂˣ) (g : G) :
    ρ.toRepresentation.character g = (ρ g : ℂ) := by
  rw [Representation.character]
  have hρg :
      ρ.toRepresentation g = (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (ρ g : ℂ) := by
    apply LinearMap.ext
    intro z
    simp [MonoidHom.toRepresentation, LinearMap.lsmul_apply, mul_comm]
  rw [hρg]
  exact LinearMap.trace_smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) (ρ g : ℂ)

end MonoidHom

/-- The value of a degree-1 complex representation at `s` lies in
`rootsOfUnity (orderOf s) ℂ`. -/
theorem degree_one_representation_value_mem_rootsOfUnity (ρ : G →* ℂˣ) (s : G) :
    ρ s ∈ rootsOfUnity (orderOf s) ℂ := by
  rw [mem_rootsOfUnity, ← map_pow, pow_orderOf_eq_one, map_one]

/-- A degree-1 complex representation takes every finite-order element to the unit circle. -/
theorem degree_one_representation_norm_eq_one (ρ : G →* ℂˣ) (s : G) (hs : IsOfFinOrder s) :
    ‖(ρ s : ℂ)‖ = 1 := by
  exact (Units.isOfFinOrder_val.mpr <| ρ.isOfFinOrder hs).norm_eq_one

end

/-! ### Definition_1_1_2_2 (from Chap01) -/
open Representation

universe u

section

variable {G : Type u} [Finite G]

/-- The regular complex representation has degree equal to the order of the group. -/
theorem leftRegular_finrank_eq_nat_card :
    Module.finrank ℂ (G →₀ ℂ) = Nat.card G := by
  let _ : Fintype G := Fintype.ofFinite G
  simpa [Nat.card_eq_fintype_card] using
    (show Module.finrank ℂ (G →₀ ℂ) = Fintype.card G from Module.finrank_finsupp_self)

end

section

variable {G : Type u} [Group G]

/- Definition 1-1.2-2: for a finite group `G`, the regular complex representation is the
canonical representation `Representation.leftRegular ℂ G` on the free complex vector space
`G →₀ ℂ`, whose standard basis is indexed by the elements of `G`. -/
#check Representation.leftRegular ℂ G

/-- In the regular representation, the translate of the basis vector at `1` is the basis vector
indexed by the translating group element. -/
theorem leftRegular_basisSingleOne_eq_orbit (s : G) :
    (Finsupp.basisSingleOne : Module.Basis G ℂ (G →₀ ℂ)) s =
      Representation.leftRegular ℂ G s (Finsupp.single (1 : G) (1 : ℂ)) := by
  simpa [Finsupp.coe_basisSingleOne] using
    (show Representation.leftRegular ℂ G s (Finsupp.single (1 : G) (1 : ℂ)) =
        Finsupp.single s (1 : ℂ) from
      Representation.ofMulAction_single s (1 : G) (1 : ℂ)).symm

section orbit_basis

variable {W : Type u} [AddCommGroup W] [Module ℂ W]
variable (ρ : Representation ℂ G W) (b : Module.Basis G ℂ W) (w : W)

private theorem leftRegularMapEquiv_symm_bijective
    (hb : ∀ s : G, b s = ρ s w) :
    Function.Bijective ((Representation.leftRegularMapEquiv ρ).symm w) := by
  let f := (Representation.leftRegularMapEquiv ρ).symm w
  -- The candidate intertwiner sends each standard basis vector to the corresponding orbit vector.
  have hf_basis : ∀ s : G, f (Finsupp.single s (1 : ℂ)) = b s := by
    intro s
    simpa [f, hb s] using Representation.leftRegularMapEquiv_symm_single ρ s w
  -- In basis coordinates, the candidate intertwiner is the identity on the standard basis.
  have hcomp : b.repr.toLinearMap.comp f.toLinearMap = LinearMap.id := by
    refine Finsupp.basisSingleOne.ext fun s ↦ ?_
    simpa [Finsupp.coe_basisSingleOne, LinearMap.comp_apply, hf_basis s] using Basis.repr_self b s
  -- Hence every vector has the same coordinates before and after applying `f`.
  have hrepr : ∀ x : G →₀ ℂ, b.repr (f x) = x := by
    intro x
    have h := congrArg (fun l : (G →₀ ℂ) →ₗ[ℂ] G →₀ ℂ => l x) hcomp
    simpa [LinearMap.comp_apply] using h
  constructor
  · intro x y hxy
    -- Injectivity follows by comparing the basis coordinates of equal images.
    rw [← hrepr x, ← hrepr y]
    exact congrArg b.repr hxy
  · intro y
    -- The coordinate vector `b.repr y` is a preimage of `y`.
    refine ⟨b.repr y, ?_⟩
    apply b.repr.injective
    rw [hrepr]
/-- If the orbit of `w` under `ρ` is a basis indexed by `G`, then `ρ` is equivariantly
isomorphic to the regular representation. -/
noncomputable def leftRegular_equiv_of_basis_eq_orbit
    (hb : ∀ s : G, b s = ρ s w) :
    (Representation.leftRegular ℂ G).Equiv ρ :=
  (((Representation.leftRegularMapEquiv ρ).symm w).ofBijective
    (leftRegularMapEquiv_symm_bijective ρ b w hb))

/-- The canonical orbit-basis equivalence sends the standard basis vector at `s` to `ρ s w`. -/
theorem leftRegular_equiv_of_basis_eq_orbit_apply_single
    (hb : ∀ s : G, b s = ρ s w) (s : G) :
    leftRegular_equiv_of_basis_eq_orbit ρ b w hb (Finsupp.single s (1 : ℂ)) = ρ s w := by
  simpa [leftRegular_equiv_of_basis_eq_orbit] using
    Representation.leftRegularMapEquiv_symm_single ρ s w

end orbit_basis

end

/-! ### Definition_1_1_3_3 (from Chap01) -/
universe u v w w₀ x

section

variable {k : Type u} {G : Type v} {W : Type w} {W₀ : Type w₀}
variable [Semiring k] [Monoid G]
variable [AddCommMonoid W] [Module k W]
variable [AddCommMonoid W₀] [Module k W₀]
variable (ρW : Representation k G W) (ρW₀ : Representation k G W₀)

/- Definition 1-1.3-3: the direct sum of two representations is the canonical product
representation `ρW.prod ρW₀`; its vectors are pairs `(w, w₀)` and the action is given
componentwise, corresponding to the block-diagonal matrix description. -/
recall Representation.prod

/-- The direct-sum representation acts componentwise on pairs. -/
-- Proof sketch: unfold the product representation; its underlying monoid homomorphism is the
-- product of the two actions, so evaluation on `(w, w₀)` is componentwise.
theorem prod_apply_pair (g : G) (w : W) (w₀ : W₀) :
    (ρW.prod ρW₀) g (w, w₀) = (ρW g w, ρW₀ g w₀) := rfl

section

variable {ι : Type x} {V : ι → Type w}
variable [(i : ι) → AddCommMonoid (V i)] [(i : ι) → Module k (V i)]
variable (ρ : (i : ι) → Representation k G (V i))

/- Finite direct sums of representations are realized by the canonical family-level construction
`Representation.directSum`; when `ι` is finite, this matches the final sentence of the definition.
-/
recall Representation.directSum

end

end

/-! ### Remark_1_1_3_2 (from Chap01) -/
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

/-! ### Theorem_1_1_3_1 (from Chap01) -/
universe u v w

open Representation

section

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [NeZero (Nat.card G : k)]
variable [AddCommGroup V] [Module k V]

/-- Theorem 1-1.3-1: every `G`-stable subspace of a representation over a field in which `|G|` is
invertible has a `G`-stable complementary subspace; in particular, this recovers the complex case
from the text. -/
-- Proof sketch: view the stable subspace `W` as a subrepresentation of `ρ`. Maschke's theorem
-- makes `ρ` semisimple, so this subrepresentation has a complementary subrepresentation; then
-- pass back to the underlying submodules.
theorem exists_isCompl_of_mem_invtSubmodule (ρ : Representation k G V) (W : Submodule k V)
    (hW : W ∈ ρ.invtSubmodule) :
    ∃ W₀ : ρ.invtSubmodule, IsCompl W (W₀ : Submodule k V) := by
  -- Maschke's theorem needs finiteness of `G`, which follows from `Nat.card G ≠ 0`.
  have hcard : Nat.card G ≠ 0 := by
    intro h
    exact NeZero.ne (Nat.card G : k) <| by simp [h]
  let _ : Finite G := Nat.finite_of_card_ne_zero hcard
  -- Repackage the stable subspace as a subrepresentation so that Maschke applies directly.
  let σ : Subrepresentation ρ :=
    { toSubmodule := W
      apply_mem_toSubmodule := by
        simpa [Representation.mem_invtSubmodule,
          Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] using hW }
  obtain ⟨σ₀, hσ₀⟩ := exists_isCompl σ
  refine ⟨⟨σ₀.toSubmodule, ?_⟩, ?_⟩
  · simpa [Representation.mem_invtSubmodule,
      Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] using σ₀.apply_mem_toSubmodule
  -- Transport the complement relation from subrepresentations back to submodules.
  · refine ⟨?_, ?_⟩
    · rw [disjoint_iff]
      have hdisj : σ ⊓ σ₀ = ⊥ := by
        simpa [disjoint_iff] using hσ₀.disjoint
      simpa [σ] using congrArg Subrepresentation.toSubmodule hdisj
    · rw [codisjoint_iff]
      have hcodisj : σ ⊔ σ₀ = ⊤ := by
        simpa [codisjoint_iff] using hσ₀.codisjoint
      simpa [σ] using congrArg Subrepresentation.toSubmodule hcodisj

end

/-! ### Definition_1_1_4_1 (from Chap01) -/
universe u v

section

variable {G : Type u} [Monoid G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V)

/- Definition 1-1.4-1: an irreducible or simple complex representation is the canonical mathlib
notion `ρ.IsIrreducible`, meaning that `ρ` is nontrivial and has no proper
nontrivial stable subspaces. -/
recall Representation.IsIrreducible

/-- A degree-1 complex representation is irreducible. -/
-- Proof sketch: a one-dimensional `ℂ`-vector space is a simple `ℂ`-module, so every
-- `G`-stable subspace of `V` is either `⊥` or `⊤`; hence the lattice of
-- subrepresentations of `ρ` is simple.
theorem isIrreducible_of_finrank_eq_one (hV : Module.finrank ℂ V = 1) :
    ρ.IsIrreducible := by
  letI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  letI : Nontrivial (Subrepresentation ρ) :=
    ⟨⊥, ⊤, fun h ↦
      bot_ne_top <| by simpa using congrArg Subrepresentation.toSubmodule h⟩
  letI : IsSimpleOrder (Submodule ℂ V) :=
    (isSimpleModule_iff ℂ V).1 ((isSimpleModule_iff_finrank_eq_one).2 hV)
  refine IsSimpleOrder.of_forall_eq_top fun σ hσ ↦ ?_
  have hσtop : σ.toSubmodule = ⊤ := by
    rcases eq_bot_or_eq_top σ.toSubmodule with hσbot | hσtop
    · exact False.elim <| hσ <| Subrepresentation.toSubmodule_injective (by simpa using hσbot)
    · exact hσtop
  exact Subrepresentation.toSubmodule_injective (by simpa using hσtop)

namespace MonoidHom

/-- A degree-1 complex character yields an irreducible one-dimensional complex representation. -/
theorem toRepresentation_isIrreducible {G : Type u} [Group G] (ρ : G →* ℂˣ) :
    ρ.toRepresentation.IsIrreducible := by
  simpa using
    (isIrreducible_of_finrank_eq_one ρ.toRepresentation
      (by simp : Module.finrank ℂ ℂ = 1))

end MonoidHom

end

/-! ### Remark_1_1_4_3 (from Chap01) -/
universe u

open Representation

section

variable {G : Type u} [Monoid G]

/-- Helper for Remark 1-1.4-3: the span of any vector is stable for the trivial action. -/
lemma trivial_span_singleton_apply_mem (v : ℂ × ℂ) :
    ∀ g x, x ∈ (ℂ ∙ v : Submodule ℂ (ℂ × ℂ)) →
      (Representation.trivial ℂ G (ℂ × ℂ)) g x ∈ (ℂ ∙ v : Submodule ℂ (ℂ × ℂ)) := by
  intro g x hx
  -- The trivial representation acts by the identity, so stability is immediate.
  simpa [Representation.trivial] using hx

/-- Helper for Remark 1-1.4-3: the line spanned by a vector in `ℂ × ℂ`, viewed as a
subrepresentation of the trivial representation. -/
abbrev trivial_line_subrepresentation (v : ℂ × ℂ) :
    Subrepresentation (Representation.trivial ℂ G (ℂ × ℂ)) :=
  { toSubmodule := ℂ ∙ v
    apply_mem_toSubmodule := trivial_span_singleton_apply_mem (G := G) v }

/-- Helper for Remark 1-1.4-3: the two coordinate-axis lines in `ℂ × ℂ`. -/
abbrev coordinate_lines : Fin 2 → Subrepresentation (Representation.trivial ℂ G (ℂ × ℂ))
  | 0 => trivial_line_subrepresentation (G := G) ((1 : ℂ), (0 : ℂ))
  | 1 => trivial_line_subrepresentation (G := G) ((0 : ℂ), (1 : ℂ))

/-- Helper for Remark 1-1.4-3: the diagonal and anti-diagonal lines in `ℂ × ℂ`. -/
abbrev diagonal_lines : Fin 2 → Subrepresentation (Representation.trivial ℂ G (ℂ × ℂ))
  | 0 => trivial_line_subrepresentation (G := G) ((1 : ℂ), (1 : ℂ))
  | 1 => trivial_line_subrepresentation (G := G) ((1 : ℂ), (-1 : ℂ))

/-- Helper for Remark 1-1.4-3: a nonzero line in the trivial two-dimensional
representation has dimension one. -/
lemma trivial_line_finrank_eq_one {v : ℂ × ℂ} (hv : v ≠ 0) :
    Module.finrank ℂ (trivial_line_subrepresentation (G := G) v).toSubmodule = 1 := by
  -- The underlying submodule is literally the span of a single nonzero vector.
  simpa [trivial_line_subrepresentation] using finrank_span_singleton hv

/-- Helper for Remark 1-1.4-3: every nonzero line in the trivial two-dimensional
representation is irreducible. -/
lemma trivial_line_is_irreducible {v : ℂ × ℂ} (hv : v ≠ 0) :
    (trivial_line_subrepresentation (G := G) v).toRepresentation.IsIrreducible := by
  -- We pass from the one-dimensionality of the line to irreducibility.
  exact
    isIrreducible_of_finrank_eq_one
      (trivial_line_subrepresentation (G := G) v).toRepresentation
      (trivial_line_finrank_eq_one (G := G) hv)

/-- Helper for Remark 1-1.4-3: the coordinate-axis lines form a complementary pair. -/
lemma coordinate_axes_are_compl :
    IsCompl
      (coordinate_lines (G := G) 0).toSubmodule
      (coordinate_lines (G := G) 1).toSubmodule := by
  have h10 : ((1 : ℂ), (0 : ℂ)) ≠ 0 := by
    simp
  have h01 : ((0 : ℂ), (1 : ℂ)) ≠ 0 := by
    simp
  have hfin0 :
      Module.finrank ℂ (coordinate_lines (G := G) 0).toSubmodule = 1 := by
    simpa [coordinate_lines] using trivial_line_finrank_eq_one (G := G) h10
  have hfin1 :
      Module.finrank ℂ (coordinate_lines (G := G) 1).toSubmodule = 1 := by
    simpa [coordinate_lines] using trivial_line_finrank_eq_one (G := G) h01
  -- The geometric content is that two distinct one-dimensional axes in `ℂ²`
  -- are disjoint and have dimensions summing to the ambient dimension.
  refine (Submodule.isCompl_iff_disjoint _ _ ?_).2 ?_
  · simp [hfin0, hfin1]
  · apply Submodule.disjoint_span_singleton_of_notMem
    simp [Submodule.mem_span_singleton]

/-- Helper for Remark 1-1.4-3: the diagonal and anti-diagonal lines form a complementary pair. -/
lemma diagonal_lines_are_compl :
    IsCompl
      (diagonal_lines (G := G) 0).toSubmodule
      (diagonal_lines (G := G) 1).toSubmodule := by
  have h11 : ((1 : ℂ), (1 : ℂ)) ≠ 0 := by
    simp
  have h1m1 : ((1 : ℂ), (-1 : ℂ)) ≠ 0 := by
    simp
  have hfin0 :
      Module.finrank ℂ (diagonal_lines (G := G) 0).toSubmodule = 1 := by
    simpa [diagonal_lines] using trivial_line_finrank_eq_one (G := G) h11
  have hfin1 :
      Module.finrank ℂ (diagonal_lines (G := G) 1).toSubmodule = 1 := by
    simpa [diagonal_lines] using trivial_line_finrank_eq_one (G := G) h1m1
  -- The same dimension-and-disjointness argument works for the diagonal pair.
  refine (Submodule.isCompl_iff_disjoint _ _ ?_).2 ?_
  · simp [hfin0, hfin1]
  · apply Submodule.disjoint_span_singleton_of_notMem
    simp [Submodule.mem_span_singleton]
    norm_num

/-- Helper for Remark 1-1.4-3: for a `Fin 2`-indexed family, a complementary pair gives an
internal direct sum decomposition. -/
lemma fin2_is_internal_of_is_compl
    {σ : Fin 2 → Submodule ℂ (ℂ × ℂ)} (hσ : IsCompl (σ 0) (σ 1)) :
    DirectSum.IsInternal σ := by
  have h01 : (0 : Fin 2) ≠ 1 := by
    decide
  have hfin2 : (Set.univ : Set (Fin 2)) = {0, 1} := by
    ext i
    fin_cases i
    · simp
    · simp
  -- For two summands, `IsInternal` is exactly the `IsCompl` condition.
  exact (DirectSum.isInternal_submodule_iff_isCompl σ h01 hfin2).2 hσ

/-- Helper for Remark 1-1.4-3: each coordinate-axis summand is irreducible. -/
lemma coordinate_lines_are_irreducible :
    ∀ i, (coordinate_lines (G := G) i).toRepresentation.IsIrreducible := by
  intro i
  fin_cases i
  · have h10 : ((1 : ℂ), (0 : ℂ)) ≠ 0 := by
      simp
    simpa [coordinate_lines] using trivial_line_is_irreducible (G := G) h10
  · have h01 : ((0 : ℂ), (1 : ℂ)) ≠ 0 := by
      simp
    simpa [coordinate_lines] using trivial_line_is_irreducible (G := G) h01

/-- Helper for Remark 1-1.4-3: each diagonal summand is irreducible. -/
lemma diagonal_lines_are_irreducible :
    ∀ i, (diagonal_lines (G := G) i).toRepresentation.IsIrreducible := by
  intro i
  fin_cases i
  · have h11 : ((1 : ℂ), (1 : ℂ)) ≠ 0 := by
      simp
    simpa [diagonal_lines] using trivial_line_is_irreducible (G := G) h11
  · have h1m1 : ((1 : ℂ), (-1 : ℂ)) ≠ 0 := by
      simp
    simpa [diagonal_lines] using trivial_line_is_irreducible (G := G) h1m1

/-- Helper for Remark 1-1.4-3: the coordinate-axis pair and the diagonal pair are distinct
families of summands. -/
lemma coordinate_and_diagonal_ranges_ne :
    Set.range (coordinate_lines (G := G)) ≠ Set.range (diagonal_lines (G := G)) := by
  intro hEq
  have hcoord_mem :
      trivial_line_subrepresentation (G := G) ((1 : ℂ), (0 : ℂ)) ∈
        Set.range (coordinate_lines (G := G)) := by
    exact ⟨0, by simp [coordinate_lines]⟩
  rw [hEq] at hcoord_mem
  rcases hcoord_mem with ⟨i, hi⟩
  fin_cases i
  · have hdiag_mem :
        ((1 : ℂ), (1 : ℂ)) ∈ (diagonal_lines (G := G) 0).toSubmodule := by
      simp
    have haxis_mem :
        ((1 : ℂ), (1 : ℂ)) ∈
          (trivial_line_subrepresentation (G := G) ((1 : ℂ), (0 : ℂ))).toSubmodule := by
      exact hi ▸ hdiag_mem
    -- `(1,1)` lies on the diagonal but not on the first coordinate axis.
    simp [Submodule.mem_span_singleton] at haxis_mem
  · have hdiag_mem :
        ((1 : ℂ), (-1 : ℂ)) ∈ (diagonal_lines (G := G) 1).toSubmodule := by
      simp
    have haxis_mem :
        ((1 : ℂ), (-1 : ℂ)) ∈
          (trivial_line_subrepresentation (G := G) ((1 : ℂ), (0 : ℂ))).toSubmodule := by
      exact hi ▸ hdiag_mem
    -- `(1,-1)` lies on the anti-diagonal but not on the first coordinate axis.
    simp [Submodule.mem_span_singleton] at haxis_mem

/-- Remark 1-1.4-3: the decomposition of a representation into irreducible summands is not unique
in general. The trivial representation on `ℂ × ℂ` admits two distinct decompositions into
irreducible lines: the coordinate axes and the diagonal/anti-diagonal lines. -/
theorem exists_distinct_irreducible_line_decompositions_trivial :
    ∃ σ τ : Fin 2 → Subrepresentation (Representation.trivial ℂ G (ℂ × ℂ)),
      Set.range σ ≠ Set.range τ ∧
        DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) ∧
        DirectSum.IsInternal (fun i ↦ (τ i).toSubmodule) ∧
        (∀ i, (σ i).toRepresentation.IsIrreducible) ∧
        ∀ i, (τ i).toRepresentation.IsIrreducible := by
  have hcoord_internal :
      DirectSum.IsInternal (fun i ↦ (coordinate_lines (G := G) i).toSubmodule) := by
    -- The coordinate axes give the first internal direct sum decomposition.
    exact
      fin2_is_internal_of_is_compl
        (σ := fun i ↦ (coordinate_lines (G := G) i).toSubmodule)
        (coordinate_axes_are_compl (G := G))
  have hdiag_internal :
      DirectSum.IsInternal (fun i ↦ (diagonal_lines (G := G) i).toSubmodule) := by
    -- The diagonal lines give the second internal direct sum decomposition.
    exact
      fin2_is_internal_of_is_compl
        (σ := fun i ↦ (diagonal_lines (G := G) i).toSubmodule)
        (diagonal_lines_are_compl (G := G))
  -- We witness non-uniqueness by these two concrete decompositions.
  exact
    ⟨coordinate_lines (G := G), diagonal_lines (G := G),
      coordinate_and_diagonal_ranges_ne (G := G),
      hcoord_internal, hdiag_internal,
      coordinate_lines_are_irreducible (G := G),
      diagonal_lines_are_irreducible (G := G)⟩

/- The second sentence of Remark 1-1.4-3 is a forward reference to §2.3:
the multiplicity of a fixed irreducible summand is decomposition-independent.
That later theorem is intentionally not anticipated in this source-facing file. -/

end

/-! ### Theorem_1_1_4_2 (from Chap01) -/
universe u v w

open Representation
open scoped MonoidAlgebra

noncomputable section

section

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [NeZero (Nat.card G : k)]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Helper for Theorem 1-1.4-2: a semisimple finite-dimensional representation admits a finite
family of simple `k[G]`-submodules that is independent and spans the whole module. -/
theorem exists_finite_sSupIndep_simple_submodule_family (ρ : Representation k G V) :
    ∃ s : Set (Submodule k[G] ρ.asModule),
      s.Finite ∧ sSupIndep s ∧ sSup s = ⊤ ∧ ∀ N ∈ s, IsSimpleModule k[G] N := by
  letI : Module k[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsScalarTower k k[G] V := by
    simpa [Representation.asModule] using
      (inferInstance : IsScalarTower k k[G] ρ.asModule)
  have hcard : Nat.card G ≠ 0 := by
    intro h
    exact NeZero.ne (Nat.card G : k) <| by simp [h]
  letI : Finite G := Nat.finite_of_card_ne_zero hcard
  letI : Fintype G := Fintype.ofFinite G
  haveI : ρ.IsSemisimpleRepresentation := inferInstance
  haveI : IsSemisimpleModule k[G] V := by
    -- Maschke turns the owner `k[G]`-module of `ρ` into a semisimple module.
    simpa [Representation.asModule] using
      (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp
        inferInstance
  haveI : Module.Finite k[G] V := Module.Finite.of_restrictScalars_finite k k[G] V
  -- Finite generation upgrades the semisimple decomposition to a finite independent family.
  simpa [Representation.asModule] using
    (((IsSemisimpleModule.finite_tfae (R := k[G]) (M := V)).out 0 4).mp
      (inferInstance : Module.Finite k[G] V))

/-- Helper for Theorem 1-1.4-2: a simple `k[G]`-submodule of `ρ.asModule` gives an irreducible
subrepresentation of `ρ`. -/
private theorem subrepresentation_ofSubmodule'_asAlgebraHom_apply
    (ρ : Representation k G V) (N : Submodule k[G] ρ.asModule)
    (r : k[G]) (x : N) :
    (((Subrepresentation.ofSubmodule' N).toRepresentation).asAlgebraHom r) x = r • x := by
  -- Compare the two `k[G]`-actions after forgetting to the ambient carrier of the subtype.
  apply Subtype.ext
  induction r using MonoidAlgebra.induction_linear with
  | zero =>
      -- Both actions send `0` to the zero vector.
      rfl
  | add a b ha hb =>
      -- Additivity reduces the ambient equality to the induction hypotheses.
      rw [map_add, LinearMap.add_apply, Submodule.coe_add, add_smul, Submodule.coe_add, ha, hb]
      rfl
  | single g a =>
      -- On basis monomials, both actions are the scalar multiple of the restricted `ρ g`.
      simp [Representation.asAlgebraHom_single, Representation.single_smul]
      rfl

/-- Helper for Theorem 1-1.4-2: the owner module of
`(Subrepresentation.ofSubmodule' N).toRepresentation` is canonically the original submodule `N`.
-/
private noncomputable def subrepresentation_ofSubmodule'_asModule_linearEquiv
    (ρ : Representation k G V) (N : Submodule k[G] ρ.asModule) :
    ((Subrepresentation.ofSubmodule' N).toRepresentation).asModule ≃ₗ[k[G]] N := by
  let ρN : Representation k G N := (Subrepresentation.ofSubmodule' N).toRepresentation
  letI : Module k[G] ρN.asModule := ρN.instModuleMonoidAlgebraAsModule
  refine
    { toFun := fun x => ρN.asModuleEquiv x
      invFun := fun x => ρN.asModuleEquiv.symm x
      left_inv := by
        intro x
        simp
      right_inv := by
        intro x
        simp
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        -- The transported owner action agrees with the original `k[G]`-action on `N`.
        intro r x
        calc
          ρN.asModuleEquiv (r • x) = (ρN.asAlgebraHom r) (ρN.asModuleEquiv x) := by
            exact Representation.asModuleEquiv_map_smul (ρ := ρN) r x
          _ = r • ρN.asModuleEquiv x := by
            exact subrepresentation_ofSubmodule'_asAlgebraHom_apply ρ N r (ρN.asModuleEquiv x) }

theorem isIrreducible_toRepresentation_of_isSimpleModule_asSubmodule
    (ρ : Representation k G V) (N : Submodule k[G] ρ.asModule)
    (hN : IsSimpleModule k[G] N) :
    (Subrepresentation.ofSubmodule' N).toRepresentation.IsIrreducible := by
  -- Route correction: the proof closes by transporting simplicity across the owner-module bridge
  -- instead of trying to coerce the two module instances directly.
  let ρN : Representation k G N := (Subrepresentation.ofSubmodule' N).toRepresentation
  -- The standard irreducible/simple-module equivalence finishes the transport.
  letI : Module k[G] ρN.asModule := ρN.instModuleMonoidAlgebraAsModule
  exact
    (Representation.irreducible_iff_isSimpleModule_asModule ρN).mpr
      (@IsSimpleModule.congr (k[G]) inferInstance ρN.asModule
        ρN.instAddCommGroupAsModule ρN.instModuleMonoidAlgebraAsModule
        N N.addCommGroup N.module
        (subrepresentation_ofSubmodule'_asModule_linearEquiv (ρ := ρ) N) hN)

/-- Helper for Theorem 1-1.4-2: transporting a finite simple owner-submodule decomposition across
`Subrepresentation.ofSubmodule'` gives a subtype-indexed family of subrepresentations that is
independent and spans the whole representation. -/
private theorem toSubmodule_ofSubmodule'_eq_restrictScalars
    (ρ : Representation k G V) (N : Submodule k[G] ρ.asModule) :
    (Subrepresentation.ofSubmodule' N).toSubmodule = N.restrictScalars k := rfl

/-- Helper for Theorem 1-1.4-2: transporting a finite simple owner-submodule decomposition across
`Subrepresentation.ofSubmodule'` gives a subtype-indexed family whose underlying `k`-submodules
are independent and span the whole representation. -/
private theorem iSupIndep_and_iSup_top_of_subtype_ofSubmodule'_family
    (ρ : Representation k G V) (s : Set (Submodule k[G] ρ.asModule))
    (hs_indep : sSupIndep s) (hs_top : sSup s = ⊤) :
    iSupIndep (fun i : s ↦ (Subrepresentation.ofSubmodule' i.1).toSubmodule) ∧
      (⨆ i : s, (Subrepresentation.ofSubmodule' i.1).toSubmodule) = ⊤ := by
  -- Convert the set-indexed independence to a subtype-indexed family of owner submodules.
  have hs_indep' : iSupIndep (fun i : s ↦ (i : Submodule k[G] ρ.asModule)) :=
    (sSupIndep_iff s).mp hs_indep
  -- Restrict scalars from `k[G]` to `k`; this preserves both independence and the supremum.
  have hσ_indep :
      iSupIndep (fun i : s ↦ Submodule.restrictScalars k (i : Submodule k[G] ρ.asModule)) := by
    rw [iSupIndep] at hs_indep'
    rw [iSupIndep]
    intro i
    rw [disjoint_iff_inf_le]
    have hi :
        ((i : Submodule k[G] ρ.asModule) ⊓
            ⨆ (j : s) (_ : j ≠ i), (j : Submodule k[G] ρ.asModule)) ≤ ⊥ := by
      simpa [disjoint_iff_inf_le] using hs_indep' i
    simpa [Submodule.restrictScalars_inf, Submodule.restrictScalars_iSup] using
      (Submodule.restrictScalars_mono (S := k) (hst := hi))
  -- The spanning statement is transported by applying `restrictScalars` to the `iSup` equality.
  have hs_top' : (⨆ i : s, (i : Submodule k[G] ρ.asModule)) = ⊤ := by
    simpa [sSup_eq_iSup'] using hs_top
  have hσ_top :
      (⨆ i : s, Submodule.restrictScalars k (i : Submodule k[G] ρ.asModule)) = ⊤ := by
    simpa [Submodule.restrictScalars_iSup] using
      congrArg (Submodule.restrictScalars k) hs_top'
  exact
    by
      simpa [toSubmodule_ofSubmodule'_eq_restrictScalars (ρ := ρ)] using ⟨hσ_indep, hσ_top⟩

/-- Helper for Theorem 1-1.4-2: an internal direct sum of subrepresentations gives an external
direct-sum equivalence of representations. -/
noncomputable def directSum_equiv_of_iSupIndep_of_iSup_eq_top {ι : Type*} [Fintype ι]
    (ρ : Representation k G V) (σ : ι → Subrepresentation ρ)
    (hσ_indep : iSupIndep (fun i ↦ (σ i).toSubmodule))
    (hσ_top : (⨆ i, (σ i).toSubmodule) = ⊤) :
    (directSum fun i ↦ (σ i).toRepresentation).Equiv ρ := by
  classical
  letI : DecidableEq ι := Classical.decEq ι
  let hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  letI := DirectSum.IsInternal.chooseDecomposition (fun i ↦ (σ i).toSubmodule) hinternal
  -- The canonical decomposition equivalence is `G`-equivariant because each summand is stable.
  exact
    Representation.Equiv.mk
      (DirectSum.decomposeLinearEquiv (fun i ↦ (σ i).toSubmodule)).symm
      (fun g ↦ by
        ext i x
        simp [Representation.directSum]
        rfl)

/-- Theorem 1-1.4-2: every finite-dimensional representation of a finite group over a field in
which `|G|` is invertible admits a finite family of irreducible subrepresentations whose
underlying submodules are independent and span the whole representation. This is the canonical
submodule-owner form of an internal direct-sum decomposition, and it specializes to the complex
case in the text. -/
-- Proof sketch: Maschke's theorem makes `ρ` semisimple, so `ρ.asModule` is a semisimple
-- `k[G]`-module. Finite-dimensionality implies finite length, hence the semisimple-module API
-- yields a finite family of simple `k[G]`-submodules with an internal direct-sum decomposition of
-- the whole module. Transport those simple submodules across the canonical order isomorphism with
-- `Subrepresentation ρ`.
theorem exists_isInternal_irreducible_subrepresentations (ρ : Representation k G V) :
    ∃ (ι : Type*) (_ : Fintype ι) (σ : ι → Subrepresentation ρ),
      iSupIndep (fun i ↦ (σ i).toSubmodule) ∧
        (⨆ i, (σ i).toSubmodule) = ⊤ ∧
        ∀ i, (σ i).toRepresentation.IsIrreducible := by
  -- Route correction: keep the semisimple owner-submodule decomposition and only transport it
  -- once, first to subrepresentations and then to their underlying `k`-submodules.
  classical
  obtain ⟨s, hs_fin, hs_indep, hs_top, hs_simple⟩ :=
    exists_finite_sSupIndep_simple_submodule_family (ρ := ρ)
  letI : Fintype s := hs_fin.fintype
  let τ : s → Subrepresentation ρ := fun i ↦ Subrepresentation.ofSubmodule' i.1
  have hτ :
      iSupIndep (fun i ↦ (τ i).toSubmodule) ∧
        (⨆ i, (τ i).toSubmodule) = ⊤ := by
    -- The structural helper turns the set-indexed owner decomposition into a finite family.
    simpa [τ] using
      (iSupIndep_and_iSup_top_of_subtype_ofSubmodule'_family
        (ρ := ρ) (s := s) hs_indep hs_top)
  rcases hτ with ⟨hτ_indep, hτ_top⟩
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let σ₀ : Fin (Fintype.card s) → Subrepresentation ρ := fun i ↦ τ (e i)
  have hσ₀_indep : iSupIndep (fun i ↦ (σ₀ i).toSubmodule) := by
    -- Reindex the independent family along the finite equivalence `e`.
    simpa [σ₀, e] using hτ_indep.comp e.injective
  have hσ₀_top : (⨆ i, (σ₀ i).toSubmodule) = ⊤ := by
    -- Reindex the spanning `iSup` along the same equivalence.
    calc
      (⨆ i, (σ₀ i).toSubmodule) = ⨆ j : s, (τ j).toSubmodule := by
        simpa [σ₀, e] using (e.iSup_comp (g := fun j : s ↦ (τ j).toSubmodule))
      _ = ⊤ := hτ_top
  let σ : ULift (Fin (Fintype.card s)) → Subrepresentation ρ := fun i ↦ σ₀ i.down
  have hσ_indep : iSupIndep (fun i ↦ (σ i).toSubmodule) := by
    -- Lift the finite index type so the existential over `Type*` elaborates cleanly.
    simpa [σ] using hσ₀_indep.comp ULift.down_injective
  have hσ_top : (⨆ i, (σ i).toSubmodule) = ⊤ := by
    calc
      (⨆ i, (σ i).toSubmodule) = ⨆ j : Fin (Fintype.card s), (σ₀ j).toSubmodule := by
        simpa [σ] using (Equiv.ulift.iSup_comp (g := fun j : Fin (Fintype.card s) ↦
          (σ₀ j).toSubmodule))
      _ = ⊤ := hσ₀_top
  refine ⟨ULift (Fin (Fintype.card s)), inferInstance, σ, hσ_indep, hσ_top, ?_⟩
  intro i
  -- Each simple owner submodule becomes an irreducible subrepresentation by the bridge above.
  exact
    isIrreducible_toRepresentation_of_isSimpleModule_asSubmodule
      (ρ := ρ) (N := (e i.down).1) (hs_simple (e i.down).1 (e i.down).2)

/-- Derived external direct-sum form of Theorem 1-1.4-2. -/
theorem exists_equiv_directSum_irreducible_subrepresentations (ρ : Representation k G V) :
    ∃ (ι : Type*) (_ : Fintype ι) (σ : ι → Subrepresentation ρ)
      (e : (directSum fun i ↦ (σ i).toRepresentation).Equiv ρ),
      ∀ i, (σ i).toRepresentation.IsIrreducible := by
  classical
  obtain ⟨ι, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :=
    exists_isInternal_irreducible_subrepresentations (ρ := ρ)
  -- Once the internal decomposition is available, the standard direct-sum equivalence closes the
  -- external statement.
  exact
    ⟨ι, inferInstance, σ,
      directSum_equiv_of_iSupIndep_of_iSup_eq_top (ρ := ρ) σ hσ_indep hσ_top,
      hσ_irr⟩

end

/-! ### Definition_1_1_5_1 (from Chap01) -/
universe u v w u₁ u₂

open scoped TensorProduct

section

variable (K : Type u) [Field K]
variable (V₁ : Type v) (V₂ : Type w)
variable [AddCommGroup V₁] [AddCommGroup V₂] [Module K V₁] [Module K V₂]

/- Definition 1-1.5-1: for vector spaces `V₁` and `V₂` over `K`, the tensor product is the
canonical vector space `V₁ ⊗[K] V₂`, with pure-tensor map linear in each variable and whose
pure tensors of basis vectors form a basis. -/
#check (V₁ ⊗[K] V₂)

/- The canonical map `(x₁, x₂) ↦ x₁ ⊗ₜ[K] x₂` is the owner declaration `TensorProduct.mk`. -/
recall TensorProduct.mk

section BasisClause

variable {ι₁ : Type u₁} {ι₂ : Type u₂}
variable (b₁ : Module.Basis ι₁ K V₁) (b₂ : Module.Basis ι₂ K V₂)

/- If `b₁` and `b₂` are bases of `V₁` and `V₂`, then the family of pure tensors
`b₁ i₁ ⊗ₜ[K] b₂ i₂` is the basis constructed by `Module.Basis.tensorProduct`. -/
recall Module.Basis.tensorProduct

end BasisClause
end

/-! ### Definition_1_1_5_2 (from Chap01) -/
universe u v w w'

open scoped TensorProduct

section

variable {𝕜 : Type u} [CommSemiring 𝕜]
variable {G : Type v} [Monoid G]
variable {V₁ : Type w} {V₂ : Type w'}
variable [AddCommMonoid V₁] [Module 𝕜 V₁]
variable [AddCommMonoid V₂] [Module 𝕜 V₂]
variable (ρ₁ : Representation 𝕜 G V₁) (ρ₂ : Representation 𝕜 G V₂)

/- Definition 1-1.5-2: the tensor product of two linear representations is the canonical
mathlib construction `Representation.tprod`, yielding the representation `ρ₁.tprod ρ₂` on
`V₁ ⊗[𝕜] V₂`. -/
recall Representation.tprod

/-- The tensor-product representation acts on pure tensors by applying each representation to its
own factor. -/
-- Proof sketch: use `Representation.tprod_apply` to rewrite the action as `TensorProduct.map`,
-- then apply `TensorProduct.map_tmul`.
theorem tprod_apply_tmul (g : G) (x₁ : V₁) (x₂ : V₂) :
    (ρ₁.tprod ρ₂ g) (x₁ ⊗ₜ[𝕜] x₂) = ρ₁ g x₁ ⊗ₜ[𝕜] ρ₂ g x₂ := by
  rw [Representation.tprod_apply, TensorProduct.map_tmul]

end

/-! ### Definition_1_1_6_1 (from Chap01) -/
open scoped TensorProduct

universe u v w

namespace Representation

noncomputable section

section SymmetricAlternatingSquare

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

/- Definition 1-1.6-1: the tensor-factor swap `θ` on `V ⊗[k] V` is the canonical intertwining
equivalence `Representation.TensorProduct.comm ρ ρ`; its `+1`- and `-1`-eigenspaces are the
symmetric and alternating squares of `ρ`. The source's complex case is the specialization
`k = ℂ`. -/
recall Representation.TensorProduct.comm

/-- The tensor-factor swap, viewed as an endomorphism so that its eigenspaces can be taken. -/
abbrev tensorSwap : Module.End k (V ⊗[k] V) :=
  (Representation.TensorProduct.comm ρ ρ).toLinearMap

/-- Helper for Definition 1-1.6-1: the tensor swap intertwines the tensor-square action. -/
theorem tensorSwap_commutes_tprod_apply (g : G) (z : V ⊗[k] V) :
    ρ.tensorSwap ((ρ.tprod ρ) g z) = (ρ.tprod ρ) g (ρ.tensorSwap z) := by
  -- The canonical commutor is itself an intertwining map for `ρ.tprod ρ`.
  have h := (Representation.TensorProduct.comm ρ ρ).isIntertwining' g
  simpa [tensorSwap] using congrArg (fun f : V ⊗[k] V →ₗ[k] V ⊗[k] V => f z) h

/-- Helper for Definition 1-1.6-1: swapping tensor factors twice is the identity. -/
theorem tensorSwap_involutive (z : V ⊗[k] V) :
    ρ.tensorSwap (ρ.tensorSwap z) = z := by
  -- The tensor commutor is an involution on the tensor square.
  have h := congrArg (fun f : V ⊗[k] V →ₗ[k] V ⊗[k] V => f z)
    (TensorProduct.comm_comp_comm k V V)
  simpa [tensorSwap, Representation.TensorProduct.toLinearMap_comm] using h

/-- The `+1`-eigenspace of the tensor swap is stable under the tensor-square action. -/
-- Proof sketch: `Representation.TensorProduct.comm ρ ρ` is an intertwiner, so its underlying
-- linear map commutes with every operator `(ρ.tprod ρ) g`; this preserves the `+1`-eigenspace.
private theorem symmetricSquareSubrepresentation_apply_mem (g : G) {z : V ⊗[k] V}
    (hz : z ∈ ρ.tensorSwap.eigenspace (1 : k)) :
    (ρ.tprod ρ) g z ∈ ρ.tensorSwap.eigenspace (1 : k) := by
  -- Rewrite the eigenspace condition as the fixed-point equation for the swap.
  rw [Module.End.mem_eigenspace_iff] at hz ⊢
  simp only [one_smul] at hz ⊢
  -- Commuting the swap past the action transports the fixed-point relation.
  rw [tensorSwap_commutes_tprod_apply]
  simpa using congrArg ((ρ.tprod ρ) g) hz

/-- The `-1`-eigenspace of the tensor swap is stable under the tensor-square action. -/
-- Proof sketch: as for the symmetric square, use that the tensor swap commutes with the
-- tensor-square action and therefore preserves the `-1`-eigenspace.
private theorem alternatingSquareSubrepresentation_apply_mem (g : G) {z : V ⊗[k] V}
    (hz : z ∈ ρ.tensorSwap.eigenspace (-1 : k)) :
    (ρ.tprod ρ) g z ∈ ρ.tensorSwap.eigenspace (-1 : k) := by
  -- Rewrite the eigenspace condition as the anti-fixed-point equation for the swap.
  rw [Module.End.mem_eigenspace_iff] at hz ⊢
  simp only [neg_one_smul] at hz ⊢
  -- The intertwining property carries the `-1`-eigenvector equation through the action.
  rw [tensorSwap_commutes_tprod_apply]
  simpa using congrArg ((ρ.tprod ρ) g) hz

/-- The symmetric square of `ρ` as a `G`-stable subspace of `V ⊗[k] V`. -/
def symmetricSquareSubrepresentation : Subrepresentation (ρ.tprod ρ) where
  toSubmodule := ρ.tensorSwap.eigenspace (1 : k)
  apply_mem_toSubmodule := symmetricSquareSubrepresentation_apply_mem ρ

/-- The alternating square of `ρ` as a `G`-stable subspace of `V ⊗[k] V`. -/
def alternatingSquareSubrepresentation : Subrepresentation (ρ.tprod ρ) where
  toSubmodule := ρ.tensorSwap.eigenspace (-1 : k)
  apply_mem_toSubmodule := alternatingSquareSubrepresentation_apply_mem ρ

instance : AddCommGroup ↥ρ.symmetricSquareSubrepresentation.toSubmodule := inferInstance

instance : AddCommGroup ↥ρ.alternatingSquareSubrepresentation.toSubmodule := inferInstance

/-- The symmetric square representation carried by the `+1`-eigenspace of the tensor swap. -/
abbrev symmetricSquare :
    Representation k G ρ.symmetricSquareSubrepresentation.toSubmodule :=
  ρ.symmetricSquareSubrepresentation.toRepresentation

/-- The alternating square representation carried by the `-1`-eigenspace of the tensor swap. -/
abbrev alternatingSquare :
    Representation k G ρ.alternatingSquareSubrepresentation.toSubmodule :=
  ρ.alternatingSquareSubrepresentation.toRepresentation

scoped[TensorProduct] notation3:max "Sym²ₛ " ρ:arg =>
  Representation.symmetricSquareSubrepresentation ρ

scoped[TensorProduct] notation3:max "Alt²ₛ " ρ:arg =>
  Representation.alternatingSquareSubrepresentation ρ

scoped[TensorProduct] notation3:max "Sym² " ρ:arg =>
  Representation.symmetricSquare ρ

scoped[TensorProduct] notation3:max "Alt² " ρ:arg =>
  Representation.alternatingSquare ρ

-- Proof sketch: membership in an eigenspace is exactly the eigenvector equation
-- `tensorSwap ρ z = 1 • z`, which simplifies to `tensorSwap ρ z = z`.
/-- A tensor lies in the symmetric square exactly when it is fixed by the tensor swap. -/
theorem mem_symmetricSquareSubrepresentation_iff {z : V ⊗[k] V} :
    z ∈ Sym²ₛ ρ ↔ ρ.tensorSwap z = z := by
  -- The symmetric square is defined as the `+1`-eigenspace of the swap.
  show z ∈ ρ.tensorSwap.eigenspace (1 : k) ↔ ρ.tensorSwap z = z
  rw [Module.End.mem_eigenspace_iff]
  simp

-- Proof sketch: membership in the `-1`-eigenspace is the eigenvector equation
-- `tensorSwap ρ z = (-1 : k) • z`, which is the same as `tensorSwap ρ z = -z`.
/-- A tensor lies in the alternating square exactly when the tensor swap acts by `-1`. -/
theorem mem_alternatingSquareSubrepresentation_iff {z : V ⊗[k] V} :
    z ∈ Alt²ₛ ρ ↔ ρ.tensorSwap z = -z := by
  -- The alternating square is the `-1`-eigenspace of the swap.
  show z ∈ ρ.tensorSwap.eigenspace (-1 : k) ↔ ρ.tensorSwap z = -z
  rw [Module.End.mem_eigenspace_iff]
  simp

-- Proof sketch: the representation on a subrepresentation is obtained by restricting the ambient
-- action, so coercing back to `V ⊗[k] V` recovers the tensor-square action.
/-- The symmetric square representation acts by restricting the tensor-square action. -/
theorem symmetricSquare_apply (g : G) (z : (Sym²ₛ ρ).toSubmodule) :
    (((Sym² ρ) g) z : V ⊗[k] V) = (ρ.tprod ρ) g z := by
  -- The restricted representation uses the ambient tensor-square action on the carrier.
  rfl

-- Proof sketch: as for the symmetric square, this is the restriction of the tensor-square action
-- to the alternating-square carrier.
/-- The alternating square representation acts by restricting the tensor-square action. -/
theorem alternatingSquare_apply (g : G) (z : (Alt²ₛ ρ).toSubmodule) :
    (((Alt² ρ) g) z : V ⊗[k] V) = (ρ.tprod ρ) g z := by
  -- The alternating-square action is the same ambient action restricted to the subspace.
  rfl

section Basis

variable {ι : Type*}
variable (b : Module.Basis ι k V)

/-- The symmetrized tensor attached to two basis vectors, viewed in the symmetric square. -/
-- Proof sketch: apply `mem_symmetricSquareSubrepresentation_iff` and use that the tensor swap
-- exchanges the two pure-tensor summands.
private theorem symmetrizedTensor_mem (i j : ι) :
    (b i ⊗ₜ[k] b j) + (b j ⊗ₜ[k] b i) ∈ Sym²ₛ ρ := by
  -- The tensor swap simply exchanges the two pure tensors in the sum.
  rw [mem_symmetricSquareSubrepresentation_iff]
  simp [tensorSwap, add_comm]

/-- The symmetrized pure tensor attached to two basis vectors. -/
def symmetrizedTensor (i j : ι) : (Sym²ₛ ρ).toSubmodule :=
  ⟨(b i ⊗ₜ[k] b j) + (b j ⊗ₜ[k] b i), symmetrizedTensor_mem ρ b i j⟩

/-- The antisymmetrized pure tensor attached to two basis vectors, viewed inside the alternating
square. -/
-- Proof sketch: apply `mem_alternatingSquareSubrepresentation_iff` and compute the action of the
-- tensor swap on the difference of the two pure tensors.
private theorem alternatingTensor_mem (i j : ι) :
    (b i ⊗ₜ[k] b j) - (b j ⊗ₜ[k] b i) ∈ Alt²ₛ ρ := by
  -- Swapping the factors reverses the ordered difference.
  rw [mem_alternatingSquareSubrepresentation_iff]
  simp [tensorSwap, sub_eq_add_neg, add_comm]

/-- The antisymmetrized pure tensor attached to two basis vectors. -/
def alternatingTensor (i j : ι) : (Alt²ₛ ρ).toSubmodule :=
  ⟨(b i ⊗ₜ[k] b j) - (b j ⊗ₜ[k] b i), alternatingTensor_mem ρ b i j⟩

end Basis

end SymmetricAlternatingSquare

section TwoInvertibleSymmetricAlternatingSquare

variable {k : Type u} [CommRing k] [Invertible (2 : k)]
variable {G : Type v} [Monoid G]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

/-- Helper for Definition 1-1.6-1: the symmetrization projector onto the fixed-point space of the
tensor swap. -/
abbrev symmetrization : Module.End k (V ⊗[k] V) :=
  ⅟(2 : k) • (LinearMap.id + ρ.tensorSwap)

/-- Helper for Definition 1-1.6-1: a tensor is fixed by symmetrization exactly when it is fixed by
the tensor swap. -/
theorem symmetrization_apply_eq_self_iff {z : V ⊗[k] V} :
    ρ.symmetrization z = z ↔ ρ.tensorSwap z = z := by
  constructor
  · intro hz
    -- Rewrite the symmetrization equation before cancelling the scalar `1 / 2`.
    have hz' : ⅟(2 : k) • (z + ρ.tensorSwap z) = z := by
      simpa only [symmetrization, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply]
        using hz
    have hz'' : z + ρ.tensorSwap z = (2 : k) • z := (invOf_smul_eq_iff).mp hz'
    have hz''' : z + ρ.tensorSwap z = z + z := by
      simpa [two_smul] using hz''
    exact add_left_cancel hz'''
  · intro hz
    -- A tensor fixed by the swap is unchanged by averaging it with its swap.
    calc
      ρ.symmetrization z = ⅟(2 : k) • (z + ρ.tensorSwap z) := by
        simp only [symmetrization, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply]
      _ = ⅟(2 : k) • (z + z) := by rw [hz]
      _ = ⅟(2 : k) • z + ⅟(2 : k) • z := by rw [smul_add]
      _ = (⅟(2 : k) + ⅟(2 : k)) • z := by rw [← add_smul]
      _ = z := by simp [invOf_two_add_invOf_two]

/-- Helper for Definition 1-1.6-1: symmetrization vanishes exactly on tensors anti-fixed by the
tensor swap. -/
theorem symmetrization_apply_eq_zero_iff {z : V ⊗[k] V} :
    ρ.symmetrization z = 0 ↔ ρ.tensorSwap z = -z := by
  constructor
  · intro hz
    -- Rewrite the equation in a form where the invertible scalar can be cancelled.
    have hz' : ⅟(2 : k) • (z + ρ.tensorSwap z) = 0 := by
      simpa only [symmetrization, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply]
        using hz
    have hz'' : z + ρ.tensorSwap z = 0 := by
      simpa using (invOf_smul_eq_iff).mp hz'
    exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using hz'')
  · intro hz
    -- The average of a tensor and its negative swap is zero.
    calc
      ρ.symmetrization z = ⅟(2 : k) • (z + ρ.tensorSwap z) := by
        simp only [symmetrization, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply]
      _ = ⅟(2 : k) • (z + -z) := by rw [hz]
      _ = 0 := by simp

/-- Helper for Definition 1-1.6-1: the symmetrization map is an idempotent projector. -/
theorem symmetrization_isIdempotentElem :
    IsIdempotentElem (ρ.symmetrization) := by
  -- Route correction: use that symmetrization already lands in the swap-fixed subspace.
  change ρ.symmetrization * ρ.symmetrization = ρ.symmetrization
  refine LinearMap.ext fun z ↦ ?_
  have hz : ρ.tensorSwap (ρ.symmetrization z) = ρ.symmetrization z := by
    -- Applying the swap to an averaged tensor just reverses the two summands.
    simp only [symmetrization, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
      map_add, map_smul, tensorSwap_involutive]
    rw [add_comm]
  -- A second symmetrization acts trivially because the first output is already fixed.
  calc
    ρ.symmetrization (ρ.symmetrization z)
        = ⅟(2 : k) • (ρ.symmetrization z + ρ.tensorSwap (ρ.symmetrization z)) := by
            simp only [symmetrization, LinearMap.smul_apply, LinearMap.add_apply,
              LinearMap.id_apply]
    _ = ⅟(2 : k) • (ρ.symmetrization z + ρ.symmetrization z) := by rw [hz]
    _ = ⅟(2 : k) • ρ.symmetrization z + ⅟(2 : k) • ρ.symmetrization z := by rw [smul_add]
    _ = (⅟(2 : k) + ⅟(2 : k)) • ρ.symmetrization z := by rw [← add_smul]
    _ = ρ.symmetrization z := by simp [invOf_two_add_invOf_two]

/-- Helper for Definition 1-1.6-1: the range of symmetrization is the symmetric square. -/
theorem symmetrization_range_eq_symmetricSquare :
    LinearMap.range (ρ.symmetrization) = (Sym²ₛ ρ).toSubmodule := by
  -- The range of an idempotent consists exactly of its fixed points.
  ext z
  rw [LinearMap.IsIdempotentElem.mem_range_iff (ρ.symmetrization_isIdempotentElem)]
  show ρ.symmetrization z = z ↔ z ∈ Sym²ₛ ρ
  exact (ρ.symmetrization_apply_eq_self_iff).trans
    (ρ.mem_symmetricSquareSubrepresentation_iff).symm

/-- Helper for Definition 1-1.6-1: the kernel of symmetrization is the alternating square. -/
theorem symmetrization_ker_eq_alternatingSquare :
    LinearMap.ker (ρ.symmetrization) = (Alt²ₛ ρ).toSubmodule := by
  -- The kernel consists exactly of tensors on which the swap acts by `-1`.
  ext z
  rw [LinearMap.mem_ker]
  show ρ.symmetrization z = 0 ↔ z ∈ Alt²ₛ ρ
  exact (ρ.symmetrization_apply_eq_zero_iff).trans
    (ρ.mem_alternatingSquareSubrepresentation_iff).symm

-- Proof sketch: the involution `tensorSwap ρ` has eigenvalues `1` and `-1`, and when `2` is
-- invertible the ambient tensor square splits as the direct sum of these eigenspaces.
/-- If `2` is invertible in `k`, the tensor square decomposes as the direct sum of the symmetric
and alternating squares. -/
theorem isCompl_symmetricSquare_alternatingSquare :
    IsCompl (Sym²ₛ ρ).toSubmodule (Alt²ₛ ρ).toSubmodule := by
  -- The projector `1 / 2 • (id + θ)` splits the tensor square into its range and kernel.
  rw [← ρ.symmetrization_range_eq_symmetricSquare, ← ρ.symmetrization_ker_eq_alternatingSquare]
  exact LinearMap.IsIdempotentElem.isCompl (ρ.symmetrization_isIdempotentElem)

-- Proof sketch: the underlying linear equivalence is the canonical direct-sum decomposition of a
-- pair of complementary submodules, and the two restricted actions agree with the ambient
-- tensor-square action on each summand.
private theorem symmetricAlternatingSquareEquivTensor_aux (g : G) :
    ((Sym²ₛ ρ).toSubmodule.prodEquivOfIsCompl (Alt²ₛ ρ).toSubmodule
      (ρ.isCompl_symmetricSquare_alternatingSquare)).toLinearMap ∘ₗ
        (((Sym² ρ).prod (Alt² ρ)) g) =
      (ρ.tprod ρ) g ∘ₗ
        ((Sym²ₛ ρ).toSubmodule.prodEquivOfIsCompl (Alt²ₛ ρ).toSubmodule
          (ρ.isCompl_symmetricSquare_alternatingSquare)).toLinearMap := by
  ext z <;> simp [symmetricSquare_apply, alternatingSquare_apply]

/-- If `2` is invertible in `k`, the direct product of the symmetric and alternating squares is
equivariantly isomorphic to the tensor square. This is the canonical bridge/view from the
source-facing decomposition to the tensor-square owner. -/
def symmetricAlternatingSquareEquivTensor :
    ((Sym² ρ).prod (Alt² ρ)).Equiv (ρ.tprod ρ) :=
  .mk
    ((Sym²ₛ ρ).toSubmodule.prodEquivOfIsCompl (Alt²ₛ ρ).toSubmodule
      (ρ.isCompl_symmetricSquare_alternatingSquare))
    (ρ.symmetricAlternatingSquareEquivTensor_aux)

end TwoInvertibleSymmetricAlternatingSquare

end

end Representation
