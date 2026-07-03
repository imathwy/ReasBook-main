import Mathlib
import StacksProject_2024.Chap11.Lemma_11_7_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain-style sampling for Lemma 11.7.4:
- primary domain: maximal subfields of finite-dimensional central division algebras, viewed through
  the chapter's canonical `Subalgebra`-level centralizer API;
- sampled owner declarations:
  `Subalgebra.IsMaximalCommutative`,
  `Subalgebra.centralizer_eq_iff_isMaximalCommutative`,
  `Subalgebra.IsMaximalCommutative.mem_of_commutes`,
  `subfield_tfae_finrank_sq_centralizer_eq_maximal_commutative`;
- best owner abstraction: `IsMaximalSubfield` on `Subalgebra k A` is the source-facing owner for
  maximal subfields in a division algebra, while `Subalgebra.IsMaximalCommutative` is the
  core/canonical owner reused from Lemma 11.7.3;
- primitive data: a `k`-subalgebra `K : Subalgebra k A` together with maximality among
  commutative `k`-subalgebras;
- derived API: field structure on `K`, inverse-closure inside `K`, and the square-dimension
  formula coming from the TFAE of Lemma 11.7.3.

Source/core/bridge triage:
- `source-facing`: maximal subfields of a finite central skew field, encoded by
  `IsMaximalSubfield`;
- `core/canonical`: `Subalgebra.IsMaximalCommutative` and the centralizer-based TFAE from
  `Lemma_11_7_3`;
- `bridge/view`: `IsMaximalSubfield.isField` and `IsMaximalSubfield.finrank_sq`, which specialize
  the core API to the division-algebra setting. -/

section

open Subalgebra

variable {k : Type u} [Field k]
variable {A : Type v} [DivisionRing A] [Algebra k A] [FiniteDimensional k A]
  [Algebra.IsCentral k A]

/-- A `k`-subalgebra of a division algebra is a maximal subfield if it is commutative and maximal
among commutative `k`-subalgebras. In a division algebra, the field structure is then derived. -/
class IsMaximalSubfield (K : Subalgebra k A) : Prop extends K.IsMaximalCommutative

namespace IsMaximalSubfield

variable {K : Subalgebra k A}

omit [FiniteDimensional k A] [Algebra.IsCentral k A] in
theorem inv_mem (hK : IsMaximalSubfield K) {x : A} (hx : x ∈ K) : x⁻¹ ∈ K := by
  by_cases hx0 : x = 0
  · rw [hx0, inv_zero]
    exact K.zero_mem
  · refine hK.toIsMaximalCommutative.mem_of_commutes ?_
    intro y hy
    letI : IsMulCommutative K := hK.toIsMaximalCommutative.toIsMulCommutative
    have hxy : x * y = y * x := by
      exact setLike_mul_comm hx hy
    have hxy' : x⁻¹ * (x * y) * x⁻¹ = x⁻¹ * (y * x) * x⁻¹ :=
      congrArg (fun z : A ↦ x⁻¹ * z * x⁻¹) hxy
    calc
      y * x⁻¹ = (x⁻¹ * x) * y * x⁻¹ := by rw [inv_mul_cancel₀ hx0, one_mul]
      _ = x⁻¹ * (x * y) * x⁻¹ := by simp [mul_assoc]
      _ = x⁻¹ * (y * x) * x⁻¹ := hxy'
      _ = x⁻¹ * y * (x * x⁻¹) := by simp [mul_assoc]
      _ = x⁻¹ * y := by rw [mul_inv_cancel₀ hx0, mul_one]

omit [FiniteDimensional k A] [Algebra.IsCentral k A] in
theorem isField (hK : IsMaximalSubfield K) : IsField K := by
  letI : IsMulCommutative K := hK.toIsMaximalCommutative.toIsMulCommutative
  refine ⟨⟨0, 1, zero_ne_one⟩, fun a b ↦ Subtype.ext <| setLike_mul_comm a.2 b.2, ?_⟩
  intro a ha
  refine ⟨⟨(a : A)⁻¹, hK.inv_mem a.2⟩, ?_⟩
  apply Subtype.ext
  exact mul_inv_cancel₀ fun h ↦ ha <| Subtype.ext h

attribute [instance] isField

noncomputable instance (K : Subalgebra k A) [hK : IsMaximalSubfield K] : Field K :=
  hK.isField.toField

-- Proof sketch: apply Lemma 11.7.3 to the subfield `K ⊆ A`, using the derived field structure on
-- `K`. The maximal-subfield hypothesis yields the maximal-commutative clause of the TFAE, so the
-- implication from (3) to (1) gives the square-dimension formula.
/-- Lemma 11.7.4: if `A` is a finite central skew field over `k` and `K` is a maximal subfield of
`A`, encoded by `IsMaximalSubfield K`, then `[A : k] = [K : k]^2`. -/
theorem finrank_sq (K : Subalgebra k A) [hK : IsMaximalSubfield K] :
    Module.finrank k A = Module.finrank k K ^ 2 := by
  let A' : CSA.{u, v} k := CSA.mk (AlgCat.of k A)
  exact
    ((subfield_tfae_finrank_sq_centralizer_eq_maximal_commutative A' K hK.isField).out 2 0).mp
      hK.toIsMaximalCommutative

end IsMaximalSubfield

end
