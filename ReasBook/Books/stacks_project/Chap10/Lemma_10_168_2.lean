import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable (R : Type u) (A : Type v) (B : Type w)
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

variable [Algebra.FinitePresentation A B]

/- Domain-style sampling:
* Primary domain: descent/approximation of faithfully flat finitely presented algebra maps.
* Relevant owner declarations inspected:
  - `Algebra.IsPushout`
  - `TensorProduct.isPushout`
  - `Algebra.IsPushout.equiv`
  - `RingHom.FaithfullyFlat`
* Best owner abstraction:
  - `source-facing`: the existence theorem below
  - `core/canonical`: `Algebra.IsPushout` for the tensor-product base-change square, together with
    `Algebra.FinitePresentation` and `RingHom.FaithfullyFlat`
  - `bridge/view`: the explicit `A`-algebra equivalence `Algebra.IsPushout.equiv A₀ A B₀ B`
* Primitive vs. derived:
  - primitive data: the descended rings `A₀`, `B₀`, their algebra structures, finite-presentation
    hypotheses, faithful flatness, and the compatible tower/pushout data relating them to `A` and
    `B`
  - derived API: the explicit tensor-product comparison `A ⊗[A₀] B₀ ≃ₐ[A] B`
-/

-- Proof sketch: first apply Lemma `10.168.1` over `ℤ` to descend the finitely presented flat map
-- `A → B` to a finitely presented model `A₀ → B₀`. The faithfully flat hypothesis implies
-- surjectivity on spectra after base change, and finitely many coefficients witnessing this
-- surjectivity can be adjoined to `A₀`, after which the descended map `A₀ → B₀` becomes
-- faithfully flat. The descended square is then organized by the canonical owner
-- `Algebra.IsPushout A₀ A B₀ B`, whose associated equivalence `A ⊗[A₀] B₀ ≃ₐ[A] B` recovers the
-- usual base-change formulation.
/-- Lemma 10.168.2: if `A` is an `R`-algebra and `B` is a faithfully flat finitely presented
`A`-algebra, then the map `A → B` descends to a faithfully flat finitely presented map
`A₀ → B₀` with `A₀` finitely presented over `R`, organized by a compatible pushout square
`R → A₀ → A`, `A₀ → B₀ → B`. The explicit `A`-algebra equivalence `A ⊗[A₀] B₀ ≃ₐ[A] B`
is the canonical derived map `Algebra.IsPushout.equiv A₀ A B₀ B`. -/
theorem exists_faithfullyFlat_finitePresentation_approximation
    (hff : (algebraMap A B).FaithfullyFlat) :
    ∃ (A₀ : Type (max u v w)) (_ : CommRing A₀) (r : R →+* A₀) (a : A₀ →+* A),
      ∃ (ha : a.comp r = algebraMap R A),
      r.FinitePresentation ∧
      ∃ (B₀ : Type (max u v w)) (_ : CommRing B₀) (g : A₀ →+* B₀) (b : B₀ →+* B),
        ∃ (hb : b.comp g = (algebraMap A B).comp a),
        g.FinitePresentation ∧
        g.FaithfullyFlat ∧
        let _ : Algebra A₀ A := a.toAlgebra
        let _ : Algebra A₀ B₀ := g.toAlgebra
        let _ : Algebra B₀ B := b.toAlgebra
        let _ : Algebra A₀ B := ((algebraMap A B).comp a).toAlgebra
        let _ : IsScalarTower A₀ A B := IsScalarTower.of_algebraMap_eq' rfl
        let _ : IsScalarTower A₀ B₀ B := IsScalarTower.of_algebraMap_eq' <| by
          simpa [RingHom.algebraMap_toAlgebra] using hb.symm
        Algebra.IsPushout A₀ A B₀ B := sorry

end
