import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Ring
open scoped TensorProduct

universe u v w

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {Λ : Type v} [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
variable (RStage : Λ → Type u) [∀ i, CommRing (RStage i)]
variable (map : ∀ i j, i ≤ j → RStage i →+* RStage j)
variable [DirectedSystem RStage (fun i j h ↦ map i j h)]
variable (colimitIso : Ring.DirectLimit RStage (fun i j h ↦ map i j h) ≃+* R)

/-
Domain sampling:
* Primary domain: filtered colimits of commutative rings and finite-presentation descent.
* Core/canonical owners inspected:
  - `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit`
  - `RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit`
  - `CommRingCat.FilteredColimits.colimitCoconeIsColimit`
* Owner choice: the mathlib filtered-colimit / `Under` API is the core owner abstraction.
* Layer triage:
  - `source-facing`: the three direct-limit descent lemmas below
  - `core/canonical`: the filtered-colimit / `Under` lemmas above
  - `bridge/view`: the chosen `Ring.DirectLimit ... ≃+* R` and the induced stage maps into `R`
* Primitive vs. derived:
  - primitive data: the raw directed system and its chosen limit identification
  - derived bridge data: the stage maps to `R` and the resulting scalar-tower compatibility
-/

namespace Ring.DirectLimit

/-- The map from a stage of a directed system to the chosen limit ring. -/
noncomputable def toLimitHom (i : Λ) : RStage i →+* R :=
  colimitIso.toRingHom.comp (Ring.DirectLimit.of RStage (fun i j h ↦ map i j h) i)

-- Proof sketch: this is the compatibility of the direct-limit structure maps, transported across
-- the chosen identification with `R`.
/-- The stage maps to the chosen limit ring are compatible with the transition maps. -/
theorem toLimitHom_comp_map {i j : Λ} (h : i ≤ j) :
    (toLimitHom RStage map colimitIso j).comp (map i j h) =
      toLimitHom RStage map colimitIso i := sorry

-- Proof sketch: convert the preceding compatibility of ring homomorphisms into the standard
-- algebra-tower compatibility condition.
/-- The transition map to a later stage and the induced maps to the limit ring form a scalar tower.
-/
theorem toLimit_isScalarTower {i j : Λ} (h : i ≤ j) :
    letI : Algebra (RStage i) (RStage j) := (map i j h).toAlgebra
    letI : Algebra (RStage i) R := (toLimitHom RStage map colimitIso i).toAlgebra
    letI : Algebra (RStage j) R := (toLimitHom RStage map colimitIso j).toAlgebra
    IsScalarTower (RStage i) (RStage j) R := sorry

attribute [instance] toLimit_isScalarTower

end Ring.DirectLimit

-- Proof sketch: choose a finite presentation of `A` over `R`; only finitely many coefficients of
-- the defining equations are involved, so they already lie in some stage `R_i`. Defining the same
-- quotient algebra over `R_i` gives a finitely presented model whose base change to `R` recovers
-- `A`.
/-- Lemma 10.127.8 (1): every finitely presented `R`-algebra is obtained by base change from a
finitely presented algebra over some stage of a directed colimit presentation of `R`. -/
theorem finitelyPresented_algebra_is_baseChange_of_stage
    (A : Type w) [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A] :
    ∃ (i : Λ) (A_i : Type w) (_ : CommRing A_i) (_ : Algebra (RStage i) A_i)
      (_ : Algebra.FinitePresentation (RStage i) A_i),
      letI : Algebra (RStage i) R := (Ring.DirectLimit.toLimitHom RStage map colimitIso i).toAlgebra
      letI : Algebra R (A_i ⊗[RStage i] R) := Algebra.TensorProduct.rightAlgebra
      Nonempty (A_i ⊗[RStage i] R ≃ₐ[R] A) := sorry

-- Proof sketch: the given morphism over `R` is equivalently an `R_i`-algebra map from `A_i` to
-- `B_i ⊗[R_i] R` by the tensor-product universal property. The filtered-colimit descent theorem
-- `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit` then descends that map to some later
-- stage `R_j`.
/-- Lemma 10.127.8 (2): an algebra map over the colimit ring from a base-changed finitely
presented stage algebra descends to a map over some later stage. -/
theorem finitePresentation_hom_to_limit_baseChange_descends {i : Λ}
    (A_i : Type w) [CommRing A_i] [Algebra (RStage i) A_i]
    [Algebra.FinitePresentation (RStage i) A_i]
    (B_i : Type w) [CommRing B_i] [Algebra (RStage i) B_i]
    [Algebra.FinitePresentation (RStage i) B_i]
    (φ :
      letI : Algebra (RStage i) R := (Ring.DirectLimit.toLimitHom RStage map colimitIso i).toAlgebra
      A_i →ₐ[RStage i] B_i ⊗[RStage i] R) :
    ∃ (j : Λ) (hij : i ≤ j),
      letI : Algebra (RStage i) (RStage j) := (map i j hij).toAlgebra
      letI : Algebra (RStage i) R := (Ring.DirectLimit.toLimitHom RStage map colimitIso i).toAlgebra
      letI : Algebra (RStage j) R := (Ring.DirectLimit.toLimitHom RStage map colimitIso j).toAlgebra
      letI : IsScalarTower (RStage i) (RStage j) R :=
        Ring.DirectLimit.toLimit_isScalarTower RStage map colimitIso hij
      ∃ φ_j : A_i →ₐ[RStage i] B_i ⊗[RStage i] RStage j,
        (Algebra.TensorProduct.map (AlgHom.id (RStage i) B_i)
          (IsScalarTower.toAlgHom (RStage i) (RStage j) R)).comp φ_j = φ := sorry

-- Proof sketch: equality after base change to `R` is equality of the corresponding maps into
-- `B_i ⊗[R_i] R`. The filtered-colimit injectivity theorem
-- `RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit` shows that the equality already holds
-- after enlarging to one stage `R_j`.
/-- Lemma 10.127.8 (3): if two maps between finitely presented stage algebras become equal after
base change to the colimit ring `R`, then they become equal after base change to some later stage.
-/
theorem finitePresentation_map_equality_stabilizes {i : Λ}
    (A_i : Type w) [CommRing A_i] [Algebra (RStage i) A_i]
    [Algebra.FinitePresentation (RStage i) A_i]
    (B_i : Type w) [CommRing B_i] [Algebra (RStage i) B_i]
    [Algebra.FinitePresentation (RStage i) B_i]
    (φ ψ : A_i →ₐ[RStage i] B_i)
    (hφψ :
      letI : Algebra (RStage i) R := (Ring.DirectLimit.toLimitHom RStage map colimitIso i).toAlgebra
      Algebra.TensorProduct.map φ (AlgHom.id (RStage i) R) =
        Algebra.TensorProduct.map ψ (AlgHom.id (RStage i) R)) :
    ∃ (j : Λ) (hij : i ≤ j),
      letI : Algebra (RStage i) (RStage j) := (map i j hij).toAlgebra
      Algebra.TensorProduct.map φ (AlgHom.id (RStage i) (RStage j)) =
        Algebra.TensorProduct.map ψ (AlgHom.id (RStage i) (RStage j)) := sorry

end
