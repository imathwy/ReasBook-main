import Mathlib
import Serre.Chap06.Proposition_6_6_2_1
import Serre.Chap06.Proposition_6_6_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MonoidAlgebra Representation
open CategoryTheory

noncomputable section

universe u v

namespace Representation

section

variable {k G : Type u} {ι : Type v} [Field k] [IsAlgClosed k]
variable [Monoid G]
variable (π : ι → Rep k G)
variable [∀ i, FiniteDimensional k (π i)]

/-- The source-facing product algebra homomorphism whose `i`-th coordinate is the central
character of `π i`. This is the thin bridge from the family of central characters to the canonical
product owner `Pi.algHom`. -/
abbrev centralCharacterFamilyAlgHom
    (hπ_irreducible : ∀ i, (π i).ρ.IsIrreducible)
    : Subalgebra.center k (k[G]) →ₐ[k] (ι → k) :=
  Pi.algHom k (fun _ : ι ↦ k) fun i ↦
    letI := hπ_irreducible i
    ω[(π i).ρ]

-- Proof sketch: for a central element `u`, the `i`-th component of the canonical Wedderburn map
-- is `(π i).ρ.asAlgebraHom u`; Proposition `asAlgebraHom_center_eq_centralCharacter_smul_id`
-- identifies this endomorphism with the scalar `ω[(π i).ρ] u` times the identity.
/-- On central elements, the `i`-th factor of the canonical Wedderburn map is scalar
multiplication by the `i`-th value of the central-character family map. -/
@[simp] theorem familyEndAlgHom_center_apply
    (hπ_irreducible : ∀ i, (π i).ρ.IsIrreducible)
    (u : Subalgebra.center k (k[G])) (i : ι) :
    (ρ̃[π]) u i = centralCharacterFamilyAlgHom π hπ_irreducible u i • LinearMap.id := by
  -- Read the `i`-th coordinate of the product map and then apply Proposition `6-6.3-1`.
  simpa [centralCharacterFamilyAlgHom, familyEndAlgHom] using
    asAlgebraHom_center_eq_centralCharacter_smul_id ((π i).ρ) u

end

section

variable {k G : Type u} {ι : Type v} [Field k] [IsAlgClosed k]
variable [Group G] [Finite G] [Invertible (Nat.card G : k)]
variable (π : ι → Rep k G)
variable [∀ i, FiniteDimensional k (π i)]

/-- Helper for Proposition 6-6.3-2: if the canonical Wedderburn image of a group-algebra element
is a family of homotheties, then the element itself lies in the center. -/
lemma mem_center_of_familyEndAlgHom_eq_smul_id
    (hinj : Function.Injective (ρ̃[π])) {x : k[G]} {a : ι → k}
    (hx : (ρ̃[π]) x = fun i ↦ a i • LinearMap.id) :
    x ∈ Subalgebra.center k (k[G]) := by
  -- Pull commutativity of the scalar family back through the injective Wedderburn map.
  rw [Subalgebra.mem_center_iff]
  intro y
  apply hinj
  ext i v
  have hxi : (π i).ρ.asAlgebraHom x = a i • LinearMap.id := by
    simpa [familyEndAlgHom] using congrArg (fun f : (∀ j, Module.End k (π j)) ↦ f i) hx
  -- Each scalar endomorphism commutes with every endomorphism on the `i`-th factor.
  simp [familyEndAlgHom, map_mul, hxi, Module.End.mul_apply]

-- Proof sketch: combine Proposition `irreducibleFamilyEndAlgHom_bijective` with the restriction of
-- the Wedderburn isomorphism to the center. Proposition
-- `asAlgebraHom_center_eq_centralCharacter_smul_id`
-- identifies the scalar on the `i`-th simple factor with the central character of the `i`-th
-- member of the complete family,
-- and Schur's lemma identifies the center of `Module.End k (π i)` with `k`.
/-- The product of the central characters furnished by a complete pairwise nonisomorphic
irreducible family is bijective on the center of `k[G]`. -/
theorem centralCharacterFamilyAlgHom_bijective
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    Function.Bijective
      (centralCharacterFamilyAlgHom π
        (fun i ↦ IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i)) := by
  let hπ_irreducible : ∀ i, (π i).ρ.IsIrreducible :=
    fun i ↦ IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i
  let hρ := irreducibleFamilyEndAlgHom_bijective π hπ_pairwise hπ_complete
  constructor
  · intro u v huv
    -- Compare the two central elements through the injective Wedderburn map.
    apply Subtype.ext
    apply hρ.1
    ext i x
    rw [familyEndAlgHom_center_apply (π := π) hπ_irreducible u i,
      familyEndAlgHom_center_apply (π := π) hπ_irreducible v i]
    have hcoord :
        centralCharacterFamilyAlgHom π hπ_irreducible u i =
          centralCharacterFamilyAlgHom π hπ_irreducible v i := by
      simpa using congrArg (fun f : ι → k ↦ f i) huv
    rw [hcoord]
  · intro a
    -- Lift the scalar family through the surjective Wedderburn map.
    obtain ⟨x, hx⟩ := hρ.2 (fun i ↦ a i • LinearMap.id)
    let u : Subalgebra.center k (k[G]) :=
      ⟨x, mem_center_of_familyEndAlgHom_eq_smul_id (π := π) hρ.1 hx⟩
    refine ⟨u, ?_⟩
    ext i
    letI : (π i).ρ.IsIrreducible := hπ_irreducible i
    letI : Nontrivial (π i) := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hV
      have htop : (⊤ : Subrepresentation (π i).ρ).toSubmodule = ⊥ := by
        apply le_antisymm
        · intro x hx
          change x = 0
          exact hV.elim x 0
        · exact bot_le
      have hEq : (⊤ : Subrepresentation (π i).ρ) = ⊥ :=
        Subrepresentation.toSubmodule_injective htop
      exact bot_ne_top hEq.symm
    -- Compare the two scalar endomorphisms on the `i`-th factor and cancel `LinearMap.id`.
    have hcoord :
        centralCharacterFamilyAlgHom π hπ_irreducible u i •
            (LinearMap.id : Module.End k (π i)) =
          a i • (LinearMap.id : Module.End k (π i)) := by
      calc
        centralCharacterFamilyAlgHom π hπ_irreducible u i •
            (LinearMap.id : Module.End k (π i)) =
          (ρ̃[π]) u i := by
          symm
          exact familyEndAlgHom_center_apply (π := π) hπ_irreducible u i
        _ = a i • (LinearMap.id : Module.End k (π i)) := by
          simpa [u] using congrArg (fun f : (∀ j, Module.End k (π j)) ↦ f i) hx
    have hscalar : centralCharacterFamilyAlgHom π hπ_irreducible u i = a i := by
      apply sub_eq_zero.mp
      have hid_ne : (LinearMap.id : Module.End k (π i)) ≠ 0 := by
        intro hid
        obtain ⟨x, hx⟩ := exists_ne (0 : π i)
        exact hx <| by
          simpa using congrArg (fun f : Module.End k (π i) ↦ f x) hid
      have hzero :
          (centralCharacterFamilyAlgHom π hπ_irreducible u i - a i) •
              (LinearMap.id : Module.End k (π i)) = 0 := by
        rw [sub_smul, hcoord, sub_self]
      exact (smul_eq_zero.mp hzero).resolve_right hid_ne
    exact hscalar

/-- Proposition 6-6.3-2: for a complete pairwise nonisomorphic family of irreducible
finite-dimensional representations over an algebraically closed field in which `|G|` is
invertible, the family of central characters yields an algebra isomorphism from the center of
`k[G]` onto the product algebra `ι → k`. Specializing to `k = ℂ` recovers Serre's original
statement `\mathbf{C}^h`. -/
def centralCharacterFamilyAlgEquiv
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    : Subalgebra.center k (k[G]) ≃ₐ[k] (ι → k) :=
  AlgEquiv.ofBijective
    (centralCharacterFamilyAlgHom π
      (fun i ↦ IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i))
    (centralCharacterFamilyAlgHom_bijective π hπ_pairwise hπ_complete)

-- Proof sketch: the underlying algebra homomorphism of `centralCharacterFamilyAlgEquiv` is
-- `centralCharacterFamilyAlgHom`, so the coordinate formula reduces to the defining `Pi.algHom`
-- coordinate formula for that bridge.
/-- The central-character equivalence acts by the source-facing product central-character map. -/
@[simp] theorem centralCharacterFamilyAlgEquiv_apply
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (u : Subalgebra.center k (k[G])) :
    centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete u =
      centralCharacterFamilyAlgHom π
        (fun i ↦ IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i) u := by
  -- The packaged equivalence was built from `AlgEquiv.ofBijective`, so its forward map is
  -- definitionally the original product central-character homomorphism.
  rfl

end

end Representation
