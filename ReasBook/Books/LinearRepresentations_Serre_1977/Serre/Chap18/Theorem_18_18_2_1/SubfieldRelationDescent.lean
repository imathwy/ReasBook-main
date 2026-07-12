import Mathlib

/-!
# Descent of linear relations to a subfield

If a family of vectors with entries in a subfield `F` of `K` admits a nontrivial finite
`K`-linear relation, then it already admits a nontrivial `F`-linear relation on the same
support.  The proof views `K` as an `F`-vector space, picks a basis, and reads off the
coordinates of the given relation in that basis.
-/

noncomputable section

universe u x y

namespace Representation

/-- If a family of vectors with entries in a subfield `F` of `K` admits a nontrivial finite
`K`-linear relation, then it admits a nontrivial `F`-linear relation (on the same support). -/
theorem exists_subfield_relation_of_relation {K : Type u} [Field K] (F : Subfield K)
    {ι : Type x} {C : Type y} (s : Finset ι) (v : ι → C → F)
    (a : ι → K)
    (hrel : ∀ x : C, (∑ j ∈ s, a j * ((v j x : F) : K)) = 0)
    {i : ι} (hi : i ∈ s) (hai : a i ≠ 0) :
    ∃ c : ι → F,
      (∀ x : C, (∑ j ∈ s, c j * v j x) = 0) ∧
      ∃ j₀, j₀ ∈ s ∧ c j₀ ≠ 0 := by
  classical
  -- `K` is a vector space over `↥F`; pick a basis.
  let B : Module.Basis (Module.Basis.ofVectorSpaceIndex F K) F K :=
    Module.Basis.ofVectorSpace F K
  -- The `↥F`-scalar action on `K` is multiplication by the coercion.
  have hsmul : ∀ (f : F) (y : K), f • y = (f : K) * y := fun f y => rfl
  -- Coordinates of the relation in the basis `B`.
  have key : ∀ x : C, (∑ j ∈ s, v j x • B.repr (a j)) = 0 := by
    intro x
    have h0 : (∑ j ∈ s, v j x • a j) = 0 := by
      rw [← hrel x]
      exact Finset.sum_congr rfl fun j _ => by rw [hsmul, mul_comm]
    calc
      ∑ j ∈ s, v j x • B.repr (a j) = B.repr (∑ j ∈ s, v j x • a j) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun j _ => (map_smul B.repr _ _).symm
      _ = 0 := by rw [h0, map_zero]
  -- Since `a i ≠ 0`, some coordinate of `a i` is nonzero.
  have hrep : B.repr (a i) ≠ 0 := fun h => hai (B.repr.map_eq_zero_iff.mp h)
  obtain ⟨β₀, hβ₀⟩ : ∃ β, B.repr (a i) β ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hrep (Finsupp.ext fun β => by simpa using hall β)
  -- The `β₀`-coordinates give the desired relation over `F`.
  refine ⟨fun j => B.repr (a j) β₀, fun x => ?_, i, hi, hβ₀⟩
  have h : (∑ j ∈ s, v j x • B.repr (a j)) β₀ = 0 := by rw [key x]; simp
  rw [Finset.sum_apply'] at h
  simpa [Finsupp.smul_apply, smul_eq_mul, mul_comm] using h

end Representation

end
