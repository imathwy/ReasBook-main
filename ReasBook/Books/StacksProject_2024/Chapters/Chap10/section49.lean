import Mathlib
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.Recall
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_49_1 (from Chap10) -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CommRingCat
open scoped TensorProduct

universe u

/- Definition 10.49.1: the canonical scheme-theoretic notion of a geometrically integral
`k`-algebra `S` is
`AlgebraicGeometry.GeometricallyIntegral (Spec.map (ofHom (algebraMap k S)))`.
-/
recall AlgebraicGeometry.GeometricallyIntegral

section

variable {k S : Type u} [Field k] [CommRing S] [Algebra k S]

/-- Companion bridge for Definition 10.49.1: the affine morphism `Spec S ⟶ Spec k` is
geometrically integral if and only if every field extension `K / k` makes `S ⊗[k] K` a domain.
-/
theorem geometricallyIntegral_iff_isDomain_tensorProduct :
    GeometricallyIntegral (Spec.map (ofHom (algebraMap k S))) ↔
      ∀ (K : Type u) [Field K] [Algebra k K], IsDomain (S ⊗[k] K) := by
  let f : Spec (of S) ⟶ Spec (of k) := Spec.map (ofHom (algebraMap k S))
  change GeometricallyIntegral f ↔
    ∀ (K : Type u) [Field K] [Algebra k K], IsDomain (S ⊗[k] K)
  letI : ObjectProperty.IsClosedUnderIsomorphisms (IsIntegral : ObjectProperty Scheme) :=
    ⟨fun e _ ↦ IsIntegral.of_isIso e.hom⟩
  rw [geometricallyIntegral_iff]
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  constructor
  · intro h K _ _
    let _ : IsIntegral (pullback f (Spec.map (ofHom (algebraMap k K)))) := h K
    exact
      (affine_isIntegral_iff (of (S ⊗[k] K))).1 <|
        IsIntegral.of_isIso (pullbackSpecIso k S K).hom
  · intro h K _ _
    let _ : IsIntegral (Spec (of (S ⊗[k] K))) :=
      (affine_isIntegral_iff (of (S ⊗[k] K))).2 (h K)
    exact IsIntegral.of_isIso (pullbackSpecIso k S K).inv

end

/-! ### Lemma_10_49_2 (from Chap10) -/
open AlgebraicGeometry CommRingCat
open scoped TensorProduct

namespace Algebra

universe u

section

variable {k S : Type u} [Field k] [CommRing S] [Algebra k S]

/-- Lemma 10.49.2: a `k`-algebra is geometrically integral exactly when it is geometrically
irreducible over `k` and geometrically reduced over `k`. -/
-- Proof sketch: this is a thin `bridge/view` statement. The owner abstraction is the affine
-- morphism `Spec S ⟶ Spec k`: geometric integrality supplies the owner-side reduced and
-- irreducible instances, and conversely those two owner properties recover geometric integrality.
-- The only non-owner step is the affine bridge
-- `geometricallyReduced_iff_isGeometricallyReduced`.
theorem geometricallyIntegral_iff_geometricallyIrreducible_and_geometricallyReduced :
    GeometricallyIntegral (Spec.map (ofHom (algebraMap k S))) ↔
      GeometricallyIrreducible (Spec.map (ofHom (algebraMap k S))) ∧
        IsGeometricallyReduced k S := by
  let f : Spec (of S) ⟶ Spec (of k) := Spec.map (ofHom (algebraMap k S))
  change GeometricallyIntegral f ↔ GeometricallyIrreducible f ∧ IsGeometricallyReduced k S
  constructor
  · intro h
    letI : GeometricallyIntegral f := h
    exact ⟨inferInstance, geometricallyReduced_iff_isGeometricallyReduced.mp inferInstance⟩
  · rintro ⟨hIrreducible, hReduced⟩
    letI : GeometricallyIrreducible f := hIrreducible
    have hReduced' : GeometricallyReduced f :=
      geometricallyReduced_iff_isGeometricallyReduced.mpr hReduced
    letI : GeometricallyReduced f := hReduced'
    exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f

end

end Algebra

/-! ### Lemma_10_49_3 (from Chap10) -/
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

/-! ### Lemma_10_49_4 (from Chap10) -/
open AlgebraicGeometry CommRingCat CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Algebra

universe u

section

variable {k R S : Type u}
variable [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

-- Proof sketch: by Lemma `10.43.5`, geometric integrality implies that `R ⊗[k] S` is reduced
-- because `R` is a domain. By Lemma `10.47.7`, geometric integrality also implies geometric
-- irreducibility, so `Spec (R ⊗[k] S)` is irreducible. A commutative ring whose prime spectrum is
-- irreducible and which is reduced is a domain.
/-- Lemma 10.49.4 (Tag 09P9): if `k` is a field, `S` is geometrically integral over `k`, and
`R` is an integral-domain `k`-algebra, then `R ⊗[k] S` is an integral domain. -/
@[stacks 09P9]
theorem Lemma_10_49_4
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap k S)))] [IsDomain R] :
    IsDomain (R ⊗[k] S) := by
  letI : IsGeometricallyReduced k S :=
    geometricallyReduced_iff_isGeometricallyReduced.mp inferInstance
  letI : IsReduced (R ⊗[k] S) := inferInstance
  let f : Spec (of (R ⊗[k] S)) ⟶ Spec (of R) :=
    Spec.map (ofHom (algebraMap R (R ⊗[k] S)))
  letI : GeometricallyIrreducible f := by
    simpa [f] using
      (inferInstance :
        GeometricallyIrreducible (Spec.map (ofHom (algebraMap R (R ⊗[k] S)))))
  haveI : IrreducibleSpace (Spec (of (R ⊗[k] S))) := by
    exact GeometricallyIrreducible.irreducibleSpace f
      (by
        simpa using
          (PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field :
            IsOpenMap (PrimeSpectrum.comap (algebraMap R (R ⊗[k] S)))))
  exact (affine_isIntegral_iff (of (R ⊗[k] S))).mp <|
    isIntegral_of_irreducibleSpace_of_isReduced _

end

end Algebra
