import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_11_7_1 (from Chap11) -/
universe u v

namespace Subalgebra

section

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k) (B : Subalgebra k A)
variable [IsSimpleRing B]

/- Theorem 11.7.1 is `source-facing`: its public statements are about the canonical owner
abstraction `Subalgebra.centralizer`, so the results live on the `Subalgebra` owner namespace
rather than behind file-local wrapper names. The supporting `core/canonical` API is the
simple-module double-centralizer equivalence from Lemma 11.4.6 together with the tensor-product
simplicity bridge from Lemma 11.4.7, so no extra local wrapper is introduced here. -/
local notation "C" => centralizer k (B : Set A)

-- Proof sketch: choose a simple left `A`-module `M`, let `L := Module.End A M`, and rewrite the
-- centralizer of `B` as the endomorphism ring of `M` as a right `B ⊗[k] Lᵐᵒᵖ`-module. The tensor
-- product algebra is simple by the earlier tensor-product lemma, so the endomorphism ring is
-- simple by the finite-module structure theorem for simple algebras.
/-- Theorem 11.7.1 (1): if `A` is a finite central simple `k`-algebra and `B` is a simple
subalgebra of `A`, then the centralizer of `B` in `A` is simple. -/
theorem isSimpleRing_centralizer :
    IsSimpleRing C := sorry

-- Proof sketch: with the same simple `A`-module `M` and `L := Module.End A M`, identify
-- `B ⊗[k] Lᵐᵒᵖ` and the centralizer `C` with matrix algebras over opposite division rings, then
-- compare the resulting dimension formulas from the simple-module structure theorem.
/-- Theorem 11.7.1 (2): if `C` is the centralizer of a simple subalgebra `B ⊆ A`, then
`[A : k] = [B : k] [C : k]`. -/
theorem finrank_mul_finrank_centralizer :
    Module.finrank k A =
      Module.finrank k B * Module.finrank k C := sorry

-- Proof sketch: apply the dimension formula again to the inclusion `C ⊆ A`, where `C` is the
-- centralizer of `B`, to show that the centralizer of `C` has the same `k`-dimension as `B`;
-- combine this with the obvious inclusion `B ≤ C_A(C)` to deduce equality.
/-- Theorem 11.7.1 (3): if `C` is the centralizer of a simple subalgebra `B ⊆ A`, then the
centralizer of `C` in `A` is exactly `B`. -/
theorem centralizer_centralizer_eq :
    centralizer k (C : Set A) = B := sorry

end

end Subalgebra

/-! ### Lemma_11_7_2 (from Chap11) -/
open scoped TensorProduct
open Algebra.TensorProduct

universe u v

namespace Subalgebra

section

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k) (B : Subalgebra k A)

local notation "C" => centralizer k (B : Set A)

private theorem centralizer_commutes (b : B) (c : C) :
    Commute (b : A) (c : A) := by
  change (b : A) * (c : A) = (c : A) * (b : A)
  exact c.2 b b.2

variable [IsSimpleRing B] [Algebra.IsCentral k B]

/- Domain sampling for Lemma 11.7.2.
- primary domain: tensor products of central simple algebras and centralizers of subalgebras;
- inspected owner declarations:
  `Subalgebra.finrank_mul_finrank_centralizer`,
  `Subalgebra.centralizer_centralizer_eq`,
  `Algebra.TensorProduct.lift`,
  `Algebra.TensorProduct.lift_tmul`;
- best owner abstraction: `Subalgebra.centralizer` on the subalgebra side, together with the
  canonical tensor-product multiplication map given directly by `Algebra.TensorProduct.lift`;
- primitive data: the subalgebra `B` and its centralizer `C_A(B)`;
- derived API: bijectivity of the canonical multiplication map and the resulting algebra
  equivalence;
- layer classification:
  `source-facing`: the algebra equivalence `B ⊗[k] C_A(B) ≃ₐ[k] A`;
  `core/canonical`: `Subalgebra.centralizer` and `Algebra.TensorProduct.lift`;
  `bridge/view`: the bijectivity theorem upgrading the canonical lift to an equivalence. -/

/- Lemma 11.7.2 is a `bridge/view` item: the source-facing statement is an explicit algebra
equivalence `B ⊗[k] C_A(B) ≃ₐ[k] A`, while the core owner map is the canonical tensor-product lift
`Algebra.TensorProduct.lift B.val C.val ...`. -/
-- Proof sketch: Theorem 11.7.1 gives the dimension identity
-- `[A : k] = [B : k] [C_A(B) : k]`, while Lemma 11.4.7 shows that `B ⊗[k] C_A(B)` is simple
-- because `B` is central simple over `k`. The canonical multiplication map is therefore injective,
-- and the dimension equality forces surjectivity.
/-- Lemma 11.7.2, owner form: the canonical multiplication map
`B ⊗[k] Subalgebra.centralizer k (B : Set A) →ₐ[k] A` is bijective. -/
theorem centralizerTensorProduct_bijective :
    Function.Bijective
      (lift B.val (centralizer k (B : Set A)).val (centralizer_commutes A B)) := sorry

/-- Lemma 11.7.2: if `A` is a finite central simple `k`-algebra and `B` is a simple central
`k`-subalgebra of `A`, then the canonical multiplication map identifies
`B ⊗[k] Subalgebra.centralizer k (B : Set A)` with `A`. -/
noncomputable def centralizerTensorProductAlgEquiv :
    B ⊗[k] C ≃ₐ[k] A :=
  AlgEquiv.ofBijective
    (lift B.val (centralizer k (B : Set A)).val (centralizer_commutes A B))
    (centralizerTensorProduct_bijective A B)

@[simp]
theorem centralizerTensorProductAlgEquiv_tmul (b : B) (c : C) :
    centralizerTensorProductAlgEquiv A B (b ⊗ₜ[k] c) = (b : A) * c := by
  simp [centralizerTensorProductAlgEquiv]

end

end Subalgebra

/-! ### Lemma_11_7_3 (from Chap11) -/
universe u v

namespace Subalgebra

section

variable {R : Type u} [CommSemiring R]
variable {A : Type v} [Semiring A] [Algebra R A]

/-- A subalgebra is maximal commutative if it is commutative and maximal among commutative
subalgebras. -/
class IsMaximalCommutative (K : Subalgebra R A) : Prop extends IsMulCommutative K where
  eq_of_le_of_comm (L : Subalgebra R A) (hKL : K ≤ L)
      (hcomm : ∀ x y : L, x * y = y * x) : L = K

theorem centralizer_eq_iff_isMaximalCommutative (K : Subalgebra R A) :
    centralizer R (K : Set A) = K ↔ K.IsMaximalCommutative := by
  constructor
  · intro hC
    refine
      { toIsMulCommutative := IsMulCommutative.of_comm fun x y ↦ ?_
        eq_of_le_of_comm := ?_ }
    · have hKC : K ≤ centralizer R (K : Set A) := hC.symm ▸ le_rfl
      exact Subtype.ext <| hKC y.2 x x.2
    · intro L hKL hcomm
      apply le_antisymm
      · intro x hx
        have hxC : x ∈ centralizer R (K : Set A) := by
          rw [mem_centralizer_iff]
          intro y hy
          exact congrArg Subtype.val (hcomm ⟨y, hKL hy⟩ ⟨x, hx⟩)
        simpa [hC] using hxC
      · exact hKL
  · intro hK
    letI : IsMulCommutative K := hK.toIsMulCommutative
    apply le_antisymm
    · intro x hxC
      rw [mem_centralizer_iff] at hxC
      have hcomm :
          ∀ a ∈ ((K : Set A) ∪ {x}), ∀ b ∈ ((K : Set A) ∪ {x}), a * b = b * a := by
        intro a ha b hb
        rcases ha with haK | rfl
        · rcases hb with hbK | rfl
          · exact setLike_mul_comm haK hbK
          · exact hxC a haK
        · rcases hb with hbK | rfl
          · exact (hxC b hbK).symm
          · simp
      let L : Subalgebra R A := Algebra.adjoin R ((K : Set A) ∪ {x})
      have hKL : K ≤ L := by
        intro y hy
        exact Algebra.subset_adjoin (Or.inl hy)
      letI : IsMulCommutative L := Algebra.isMulCommutative_adjoin R hcomm
      have hLK : L = K := hK.eq_of_le_of_comm L hKL fun a b ↦ by
        exact Subtype.ext <| setLike_mul_comm a.2 b.2
      have hxL : x ∈ L := by
        dsimp [L]
        exact Algebra.subset_adjoin (Or.inr (by simp))
      simpa [hLK] using hxL
    · have hKC : K ≤ centralizer R (K : Set A) := by
        intro x hx
        rw [mem_centralizer_iff]
        intro y hy
        exact setLike_mul_comm hy hx
      exact hKC

namespace IsMaximalCommutative

variable {K : Subalgebra R A}

theorem centralizer_eq (hK : K.IsMaximalCommutative) :
    centralizer R (K : Set A) = K :=
  (K.centralizer_eq_iff_isMaximalCommutative).2 hK

theorem mem_of_commutes (hK : K.IsMaximalCommutative) {x : A}
    (hx : ∀ y ∈ K, y * x = x * y) : x ∈ K := by
  have hxC : x ∈ centralizer R (K : Set A) := by
    rw [mem_centralizer_iff]
    intro y hy
    exact hx y hy
  simpa [hK.centralizer_eq] using hxC

end IsMaximalCommutative

end

end Subalgebra

section

open Subalgebra

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k)
variable (K : Subalgebra k A) (hK : IsField K)

local notation "C" => centralizer k (K : Set A)

private theorem subfield_le_centralizer (hK : IsField K) :
    K ≤ C := by
  letI : Field K := hK.toField
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  simpa using congrArg (fun z : K ↦ (z : A)) (mul_comm (⟨y, hy⟩ : K) ⟨x, hx⟩)

private theorem finrank_sq_iff_centralizer_eq (hK : IsField K) :
    Module.finrank k A = Module.finrank k K ^ 2 ↔ C = K := by
  letI : Field K := hK.toField
  have hKC : K ≤ C := by
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    simpa using mul_comm (⟨y, hy⟩ : K) ⟨x, hx⟩
  have hdim := K.finrank_mul_finrank_centralizer A
  constructor
  · intro hsq
    have hfin : Module.finrank k K = Module.finrank k C := by
      exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos <| by
        calc
          Module.finrank k K * Module.finrank k K = Module.finrank k A := by
            simpa [pow_two] using hsq.symm
          _ = Module.finrank k K * Module.finrank k C := hdim
    exact (Subalgebra.eq_of_le_of_finrank_eq hKC hfin).symm
  · intro hC
    calc
      Module.finrank k A = Module.finrank k K * Module.finrank k C := hdim
      _ = Module.finrank k K ^ 2 := by rw [hC, pow_two]

-- Proof sketch: apply Theorem 11.7.1 to the field subalgebra `K`. The dimension formula
-- identifies condition (1) with `Module.finrank k (Subalgebra.centralizer k (K : Set A)) = 1`,
-- which is equivalent to the centralizer being `K`; condition (3) is equivalent to the same
-- centralizer statement because a commutative `k`-subalgebra containing `K` lies in that
-- centralizer, and conversely `K` itself is commutative since it is a field.
/-- Lemma 11.7.3: for a subfield `K` of a finite central simple `k`-algebra `A`, represented as a
`k`-subalgebra with `IsField K`, the following are equivalent: `[A : k] = [K : k]^2`, `K` is its
own centralizer in `A`, and `K` is a maximal commutative `k`-subalgebra of `A`. -/
theorem subfield_tfae_finrank_sq_centralizer_eq_maximal_commutative (hK : IsField K) :
    List.TFAE
      [ Module.finrank k A = Module.finrank k K ^ 2,
        C = K,
        K.IsMaximalCommutative ] := by
  letI : Field K := hK.toField
  tfae_have 1 ↔ 2 := finrank_sq_iff_centralizer_eq A K hK
  tfae_have 2 ↔ 3 := K.centralizer_eq_iff_isMaximalCommutative
  tfae_finish

end

/-! ### Lemma_11_7_4 (from Chap11) -/
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
