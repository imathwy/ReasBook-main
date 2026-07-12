import Mathlib.Data.List.TFAE
import Mathlib.Tactic.TFAE
import StacksProject_2024.Chap10.Definition_10_49_1
import StacksProject_2024.Chap10.Lemma_10_44_4
import StacksProject_2024.Chap10.Lemma_10_45_6
import StacksProject_2024.Chap10.Lemma_10_47_3
import StacksProject_2024.Chap10.Lemma_10_49_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CommRingCat
open scoped TensorProduct

namespace Algebra

universe u

section

variable {k S : Type u} [Field k] [CommRing S] [Algebra k S]

-- Proof sketch: clause `(1)` is the owner notion from Definition `10.49.1`. For `(1) ↔ (2)`,
-- use the owner theorem `geometricallyIntegral_iff_isDomain_tensorProduct` together with Lemma
-- `10.47.3` for geometric irreducibility and Lemma `10.44.4` for geometric reducedness. For
-- `(1) ↔ (3)`, combine the algebraic-closure clauses of the same irreducibility/reducedness
-- criteria with Lemma `10.49.2`.
/-- Lemma 10.49.3: for a `k`-algebra `S`, the following are equivalent: `S` is geometrically
integral over `k`, every finite field extension `k' / k` gives a domain `S ⊗[k] k'`, and the base
change `S ⊗[k] AlgebraicClosure k` is a domain. -/
theorem geometricallyIntegral_tfae_isDomain_tensorProduct_finiteExtension_algebraicClosure :
    List.TFAE
      [ GeometricallyIntegral (Spec.map (ofHom (algebraMap k S))),
        (∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K],
            IsDomain (S ⊗[k] K)),
        IsDomain (S ⊗[k] AlgebraicClosure k) ] := by
  tfae_have 1 ↔ 2 := by
    constructor
    · intro h K _ _ _
      exact (geometricallyIntegral_iff_isDomain_tensorProduct.mp h) K
    · intro h
      have hReduced : IsGeometricallyReduced k S := by
        refine isGeometricallyReduced_iff_isReduced_tensorProduct_finitePurelyInseparable.2 ?_
        intro K _ _ _ _
        let e : S ⊗[k] K ≃ₐ[k] K ⊗[k] S := Algebra.TensorProduct.comm k S K
        letI : IsDomain (S ⊗[k] K) := h K
        exact isReduced_of_injective e.symm.toRingHom e.symm.injective
      have hIrreducible : GeometricallyIrreducible (Spec.map (ofHom (algebraMap k S))) := by
        refine geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_finiteSeparable_baseChange.2 ?_
        intro K _ _ _ _
        letI : IsDomain (S ⊗[k] K) := h K
        infer_instance
      exact
        geometricallyIntegral_iff_geometricallyIrreducible_and_geometricallyReduced.2
          ⟨hIrreducible, hReduced⟩
  tfae_have 1 ↔ 3 := by
    constructor
    · intro h
      exact (geometricallyIntegral_iff_isDomain_tensorProduct.mp h) (AlgebraicClosure k)
    · intro h
      letI : IsDomain (S ⊗[k] AlgebraicClosure k) := h
      have hIrreducible : GeometricallyIrreducible (Spec.map (ofHom (algebraMap k S))) :=
        geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_algebraicClosure.2
          inferInstance
      have hReduced : IsGeometricallyReduced k S := by
        let e : S ⊗[k] AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k ⊗[k] S :=
          Algebra.TensorProduct.comm k S (AlgebraicClosure k)
        exact
          (Algebra.isGeometricallyReduced_iff k S).2
            (isReduced_of_injective e.symm.toRingHom e.symm.injective)
      exact
        geometricallyIntegral_iff_geometricallyIrreducible_and_geometricallyReduced.2
          ⟨hIrreducible, hReduced⟩
  tfae_finish

/-- Lemma 10.49.3, clauses `(1) ↔ (2)`: geometric integrality can be checked after tensoring with
finite field extensions of `k`. -/
theorem geometricallyIntegral_iff_isDomain_tensorProduct_finiteExtension :
    GeometricallyIntegral (Spec.map (ofHom (algebraMap k S))) ↔
      ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K],
        IsDomain (S ⊗[k] K) := by
  have htfae :
      List.TFAE
        [ GeometricallyIntegral (Spec.map (ofHom (algebraMap k S))),
          (∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K],
              IsDomain (S ⊗[k] K)),
          IsDomain (S ⊗[k] AlgebraicClosure k) ] :=
    geometricallyIntegral_tfae_isDomain_tensorProduct_finiteExtension_algebraicClosure
  exact htfae.out 0 1 (by simp) (by simp)

/-- Lemma 10.49.3, clauses `(1) ↔ (3)`: a `k`-algebra is geometrically integral iff its base
change to `AlgebraicClosure k` is a domain. -/
theorem geometricallyIntegral_iff_isDomain_tensorProduct_algebraicClosure :
    GeometricallyIntegral (Spec.map (ofHom (algebraMap k S))) ↔
      IsDomain (S ⊗[k] AlgebraicClosure k) := by
  have htfae :
      List.TFAE
        [ GeometricallyIntegral (Spec.map (ofHom (algebraMap k S))),
          (∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K],
              IsDomain (S ⊗[k] K)),
          IsDomain (S ⊗[k] AlgebraicClosure k) ] :=
    geometricallyIntegral_tfae_isDomain_tensorProduct_finiteExtension_algebraicClosure
  exact htfae.out 0 2 (by simp) (by simp)

end

end Algebra
