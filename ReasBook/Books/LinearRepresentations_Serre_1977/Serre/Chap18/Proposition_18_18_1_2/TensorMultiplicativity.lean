import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap18.Definition_18_18_1_1
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.FiniteOrderEigenbasis
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.RealizationCore

noncomputable section

open scoped Representation
open scoped TensorProduct

universe u v x y

namespace Representation

section Tensor

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {A : Type v} [CommSemiring A]
variable {G : Type u} [Group G]
variable {V : Type x} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {W : Type y} [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- Helper for Proposition 18-18.1-2: the modular character is multiplicative on tensor products
at a `p`-regular element. -/
theorem modularCharacter_tensor_bridge [Fact p.Prime]
    (lift : PrimeToPRoot p k →* A) (ρ : Representation k G V) (σ : Representation k G W)
    (s : { t : G // IsPRegular p t }) :
    φ[lift](tprod ρ σ) s =
      φ[lift](ρ) s *
        φ[lift](σ) s := by
  classical
  -- A `p`-regular element has order nonzero in both `ℕ` and the characteristic-`p` field.
  have hm : orderOf s.1 ≠ 0 := by
    intro h0
    have hs := s.2
    unfold IsPRegular at hs
    rw [h0, Nat.coprime_zero_right] at hs
    exact (Fact.out : p.Prime).one_lt.ne' hs
  have hmk : ((orderOf s.1 : ℕ) : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k p]
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp s.2
  -- Extend the root lift to all field elements, using zero outside the prime-to-`p` roots.
  let fA : k → A := fun μ ↦
    if h : ∃ x : PrimeToPRoot p k, ((x : kˣ) : k) = μ then lift (Classical.choose h) else 0
  have hfA : ∀ x : PrimeToPRoot p k, lift x = fA ((x : kˣ) : k) := by
    intro x
    have hex : ∃ y : PrimeToPRoot p k, ((y : kˣ) : k) = ((x : kˣ) : k) := ⟨x, rfl⟩
    have hsel : fA ((x : kˣ) : k) = lift (Classical.choose hex) := dif_pos hex
    rw [hsel]
    congr 1
    apply Subtype.ext
    apply Units.ext
    exact (Classical.choose_spec hex).symm
  have hfA_mul : ∀ x y : PrimeToPRoot p k,
      fA (((x : kˣ) : k) * ((y : kˣ) : k)) = fA ((x : kˣ) : k) * fA ((y : kˣ) : k) := by
    intro x y
    have hxy : (((x * y : PrimeToPRoot p k) : kˣ) : k) = ((x : kˣ) : k) * ((y : kˣ) : k) := by
      push_cast
      rfl
    rw [← hxy, ← hfA (x * y), map_mul, hfA x, hfA y]
  -- Diagonalize the two actions of the chosen `p`-regular element.
  have hu₁ : (ρ s.1) ^ orderOf s.1 = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hu₂ : (σ s.1) ^ orderOf s.1 = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  obtain ⟨κ₁, _, b₁, d₁, hb₁⟩ := exists_eigenbasis_of_pow_eq_one (ρ s.1) hm hmk hu₁
  obtain ⟨κ₂, _, b₂, d₂, hb₂⟩ := exists_eigenbasis_of_pow_eq_one (σ s.1) hm hmk hu₂
  -- Tensoring eigenvectors multiplies eigenvalues.
  have hbT : ∀ ij : κ₁ × κ₂,
      (Representation.tprod ρ σ) s.1 ((Module.Basis.tensorProduct b₁ b₂) ij) =
        (d₁ ij.1 * d₂ ij.2) • (Module.Basis.tensorProduct b₁ b₂) ij := by
    intro ij
    rw [Module.Basis.tensorProduct_apply']
    rw [Representation.tprod_apply]
    rw [TensorProduct.map_tmul]
    rw [hb₁ ij.1, hb₂ ij.2]
    rw [TensorProduct.smul_tmul_smul]
  -- Rewrite the three modular characters as root sums.
  have h₁ := modularCharacter_eq_roots_sum (p := p) (k := k) (G := G)
    (lift := fun x : PrimeToPRoot p k ↦ lift x) (f := fA) hfA ρ s
  have h₂ := modularCharacter_eq_roots_sum (p := p) (k := k) (G := G)
    (lift := fun x : PrimeToPRoot p k ↦ lift x) (f := fA) hfA σ s
  have hT := modularCharacter_eq_roots_sum (p := p) (k := k) (G := G)
    (lift := fun x : PrimeToPRoot p k ↦ lift x) (f := fA) hfA
    (Representation.tprod ρ σ) s
  show modularCharacter (fun x : PrimeToPRoot p k ↦ lift x) (Representation.tprod ρ σ) s =
    modularCharacter (fun x : PrimeToPRoot p k ↦ lift x) ρ s *
      modularCharacter (fun x : PrimeToPRoot p k ↦ lift x) σ s
  rw [h₁, h₂, hT]
  -- Replace characteristic-root multisets by the eigenvalue multisets from the chosen bases.
  rw [charpoly_roots_of_eigenbasis (ρ s.1) b₁ d₁ hb₁]
  rw [charpoly_roots_of_eigenbasis (σ s.1) b₂ d₂ hb₂]
  rw [charpoly_roots_of_eigenbasis ((Representation.tprod ρ σ) s.1)
    (Module.Basis.tensorProduct b₁ b₂) (fun ij ↦ d₁ ij.1 * d₂ ij.2) hbT]
  -- Every eigenvalue is the field value of a prime-to-`p` root, so `fA` is multiplicative there.
  have hd₁ : ∀ i, ∃ x : PrimeToPRoot p k, ((x : kˣ) : k) = d₁ i := by
    intro i
    have hroot : d₁ i ∈ (ρ s.1).charpoly.roots := by
      rw [charpoly_roots_of_eigenbasis (ρ s.1) b₁ d₁ hb₁]
      exact Multiset.mem_map_of_mem d₁ (Finset.mem_univ i)
    exact ⟨charpolyRoot_primeToPRoot (p := p) (k := k) ρ s.2 hroot,
      charpolyRoot_primeToPRoot_coe (p := p) (k := k) ρ s.2 hroot⟩
  have hd₂ : ∀ j, ∃ y : PrimeToPRoot p k, ((y : kˣ) : k) = d₂ j := by
    intro j
    have hroot : d₂ j ∈ (σ s.1).charpoly.roots := by
      rw [charpoly_roots_of_eigenbasis (σ s.1) b₂ d₂ hb₂]
      exact Multiset.mem_map_of_mem d₂ (Finset.mem_univ j)
    exact ⟨charpolyRoot_primeToPRoot (p := p) (k := k) σ s.2 hroot,
      charpolyRoot_primeToPRoot_coe (p := p) (k := k) σ s.2 hroot⟩
  -- Factor the double sum over the tensor-product eigenbasis.
  have hsum₁ : (Finset.univ.val.map d₁).map fA = Finset.univ.val.map fun i ↦ fA (d₁ i) := by
    rw [Multiset.map_map]
    rfl
  have hsum₂ : (Finset.univ.val.map d₂).map fA = Finset.univ.val.map fun j ↦ fA (d₂ j) := by
    rw [Multiset.map_map]
    rfl
  have hsumT : (Finset.univ.val.map fun ij : κ₁ × κ₂ ↦ d₁ ij.1 * d₂ ij.2).map fA =
      Finset.univ.val.map fun ij : κ₁ × κ₂ ↦ fA (d₁ ij.1) * fA (d₂ ij.2) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl ?_
    intro ij _
    obtain ⟨x, hx⟩ := hd₁ ij.1
    obtain ⟨y, hy⟩ := hd₂ ij.2
    show fA (d₁ ij.1 * d₂ ij.2) = fA (d₁ ij.1) * fA (d₂ ij.2)
    rw [← hx, ← hy]
    exact hfA_mul x y
  rw [hsum₁, hsum₂, hsumT]
  show (∑ ij : κ₁ × κ₂, fA (d₁ ij.1) * fA (d₂ ij.2)) =
    (∑ i : κ₁, fA (d₁ i)) * (∑ j : κ₂, fA (d₂ j))
  rw [Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  rfl

end Tensor

end Representation
