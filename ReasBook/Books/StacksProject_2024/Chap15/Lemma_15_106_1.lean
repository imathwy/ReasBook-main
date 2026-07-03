import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap15.Definition_15_105_1
import StacksProject_2024.Chap15.Lemma_15_105_7
import StacksProject_2024.Chap15.Lemma_15_105_8
import StacksProject_2024.Chap15.Lemma_15_105_9
import StacksProject_2024.Chap15.Lemma_15_105_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

section

variable {K : Type u} [Field K]
variable {B : Type v} [CommRing B] [Algebra K B]

section WeaklyEtale

variable [Algebra.IsWeaklyEtale K B]

/- Domain-style sampling for Lemma 15.106.1:
- primary domain: weakly étale commutative `K`-algebras over a field and their finite-type
  subalgebras, quotients, and tensor products;
- sampled owner declarations:
  `Algebra.IsWeaklyEtale`,
  `isReduced_of_isWeaklyEtale`,
  `etale_of_fg_subalgebra_of_isWeaklyEtale`,
  `Algebra.Etale.iff_exists_algEquiv_prod`,
  `Algebra.IsSeparable`,
  `isSeparable_of_flat_tensorSquareMultiplication`,
  `Algebra.IsWeaklyEtale.comp`;
- best owner abstraction: the canonical owner is `Algebra.IsWeaklyEtale K B`; finite generation of
  a `K`-subalgebra belongs primitively to `A.FG`, while the `FiniteType` phrasing in part `(3)` is
  a downstream bridge from the existing owner theorem in `Lemma 15.105.16` to
  `Algebra.Etale.iff_exists_algEquiv_prod`;
- primitive data: the weakly étale owner class on `K → B`, the subalgebra `A : Subalgebra K B`,
  and field structure when part `(5)` specializes to a field extension;
- derived API: reducedness, the finite-product classification bridge for finitely generated
  subalgebras, the canonical separability owner in the field case, and the tensor-product closure
  obtained by reusing the base-change and composition API from `15.105.*`.

This file therefore keeps the Stacks source-facing consequences, but it should not introduce a
parallel owner-level API where the chapter already proved the canonical theorem upstream.
-/

/- Lemma 15.106.1 (1): if `B` is weakly étale over a field `K`, then `B` is reduced. This is the
canonical theorem `isReduced_of_isWeaklyEtale`, specialized to the reduced base ring `K`. -/
recall isReduced_of_isWeaklyEtale

-- Proof sketch: by Lemma `15.105.16`, every finitely generated `K`-subalgebra of `B` is étale
-- over `K`, hence finite over `K`; finite algebras over a field are integral, and every element
-- of `B` lies in some finitely generated `K`-subalgebra.
/-- Lemma 15.106.1 (2): if `B` is weakly étale over a field `K`, then `B` is integral over `K`. -/
theorem isIntegral_of_isWeaklyEtale_over_field
    : Algebra.IsIntegral K B := sorry

/- Lemma 15.106.1 (3): any finitely generated `K`-subalgebra of a weakly étale `K`-algebra is
étale over `K`, equivalently a finite product of finite separable extensions of `K`. This is
exactly the canonical theorem `etale_of_fg_subalgebra_of_isWeaklyEtale` from `Lemma 15.105.16`,
with the finite-product classification supplied by `Algebra.Etale.iff_exists_algEquiv_prod`. -/
recall etale_of_fg_subalgebra_of_isWeaklyEtale

/-- Lemma 15.106.1 (3), source-facing finite-product form: any finitely generated `K`-subalgebra
of a weakly étale `K`-algebra is isomorphic to a finite product of finite separable extensions
of `K`. -/
theorem exists_algEquiv_prod_of_fg_subalgebra_of_isWeaklyEtale_over_field
    (A : Subalgebra K B) (hA : A.FG) :
    ∃ (I : Type v) (_ : Finite I) (Ai : I → Type v) (_ : ∀ i, Field (Ai i))
      (_ : ∀ i, Algebra K (Ai i)) (_ : A ≃ₐ[K] Π i, Ai i),
      ∀ i, Module.Finite K (Ai i) ∧ Algebra.IsSeparable K (Ai i) := by
  exact (Algebra.Etale.iff_exists_algEquiv_prod K A).mp
    (etale_of_fg_subalgebra_of_isWeaklyEtale A hA)

-- Proof sketch: by `etale_of_fg_subalgebra_of_isWeaklyEtale`, every weakly étale `K`-algebra over
-- a field is a filtered colimit of finite products of finite separable field extensions. Such a
-- nontrivial product is a field exactly when it has only the trivial idempotents `0` and `1`,
-- and this criterion passes to `B`.
/-- Lemma 15.106.1 (4): a weakly étale `K`-algebra `B` is a field if and only if it has no
nontrivial idempotents. -/
theorem isField_iff_idempotents_eq_zero_or_one_of_isWeaklyEtale_over_field
    [Nontrivial B] :
    IsField B ↔ ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1 := sorry

-- Proof sketch: if `B` is a field, then part `(4)` together with
-- `etale_of_fg_subalgebra_of_isWeaklyEtale` reduces to the case of a single finite separable
-- field extension at each finitely generated stage. Taking the filtered colimit shows that every
-- element of `B` is separable over `K`; algebraicity is absorbed canonically by
-- `Algebra.IsSeparable`.
/-- Lemma 15.106.1 (5): if a weakly étale `K`-algebra `B` is a field, then `B` is a separable
algebraic extension of `K`. -/
theorem isSeparable_of_isField_of_isWeaklyEtale_over_field
    (hB : IsField B) :
    Algebra.IsSeparable K B := sorry

-- Proof sketch: a `K`-subalgebra is the filtered colimit of its finitely generated
-- `K`-subalgebras. Each finitely generated stage is étale over `K` by
-- `etale_of_fg_subalgebra_of_isWeaklyEtale`, hence weakly étale; then Lemma `15.105.14 (3)` gives
-- weak étaleness of the filtered colimit.
/-- Lemma 15.106.1 (6): any `K`-subalgebra of a weakly étale `K`-algebra is weakly étale over
`K`. -/
theorem isWeaklyEtale_subalgebra_of_isWeaklyEtale_over_field
    (A : Subalgebra K B) :
    Algebra.IsWeaklyEtale K A := sorry

-- Proof sketch: every quotient of a finite product of finite separable field extensions is again
-- a product of some of those factors, hence weakly étale over `K`. Express the quotient of `B` as
-- a filtered colimit of quotients of finitely generated weakly étale subalgebras and apply Lemma
-- `15.105.14 (3)`.
/-- Lemma 15.106.1 (7): any quotient `K`-algebra of a weakly étale `K`-algebra is weakly étale
over `K`. -/
theorem isWeaklyEtale_quotient_of_isWeaklyEtale_over_field
    (I : Ideal B) :
    Algebra.IsWeaklyEtale K (B ⧸ I) := sorry

end WeaklyEtale

-- Proof sketch: write both weakly étale `K`-algebras as filtered colimits of finite étale
-- `K`-algebras by `etale_of_fg_subalgebra_of_isWeaklyEtale`. Tensor products of finite étale
-- algebras over a field are again finite étale, so the tensor product is a filtered colimit of
-- weakly étale `K`-algebras; conclude with Lemma `15.105.14 (3)`.
/-- Lemma 15.106.1 (8): the tensor product of two weakly étale `K`-algebras is weakly étale over
`K`. -/
theorem isWeaklyEtale_tensorProduct_of_isWeaklyEtale_over_field
    {B' : Type v} [CommRing B'] [Algebra K B']
    [Algebra.IsWeaklyEtale K B] [Algebra.IsWeaklyEtale K B'] :
    Algebra.IsWeaklyEtale K (B ⊗[K] B') := by
  let hKB : Algebra.IsWeaklyEtale K B := inferInstance
  let hBT : Algebra.IsWeaklyEtale B (B ⊗[K] B') :=
    (inferInstance : Algebra.IsWeaklyEtale K B').baseChange
  exact (Algebra.IsWeaklyEtale.comp hKB hBT : Algebra.IsWeaklyEtale K (B ⊗[K] B'))

end
