import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

noncomputable section

section

/-
Domain sampling:
* Primary domain: descent of algebra maps along filtered/direct-ring colimits via tensor-product
  base change.
* Relevant owner declarations inspected:
  - `Algebra.TensorProduct.map`
  - `Ring.DirectLimit.of`
  - `finite_type_surjectivity_descends` from `Lemma_10_127_7`
  - `DirectedFiniteTypeHomApproximation.stageBaseChange` from `Lemma_10_127_14`
* Best owner abstraction:
  - `source-facing`: the directed-ring-colimit descent theorem below
  - `core/canonical`: tensor-product base change via `Algebra.TensorProduct.map` together with
    the direct-limit ring `Ring.DirectLimit`
  - `bridge/view`: the chosen directed-system presentation of that filtered-colimit situation
* Primitive vs. derived:
  - primitive data: the directed system `A`, transition maps `f`, the distinguished stage `i₀`,
    and the algebra map `φ₀`
  - derived API: the stagewise and direct-limit base-change maps expressed directly by
    `Algebra.TensorProduct.map`
-/

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
variable (A : I → Type u) [∀ i, CommRing (A i)]
variable (f : ∀ i j, i ≤ j → A i →+* A j)
variable [DirectedSystem A (fun i j hij ↦ f i j hij)]
variable {i₀ : I}
variable {B₀ C₀ : Type w} [CommRing B₀] [CommRing C₀]
variable [Algebra (A i₀) B₀] [Algebra (A i₀) C₀]
local notation "A∞" => Ring.DirectLimit A (fun i j hij ↦ f i j hij)

-- Proof sketch: apply the filtered-colimit descent statement for surjectivity from
-- the direct-limit presentation `Ring.DirectLimit A f`. Finite type of `C₀` over `B₀` is encoded
-- as `φ₀.FiniteType`, so finitely many generators admit preimages after base change to the direct
-- limit; directedness lets one realize those preimages simultaneously at a single stage.
/-- Lemma 10.168.4: for a directed colimit `A = colim_i A_i`, if `φ₀ : B₀ → C₀` is a map of
`A₀`-algebras whose base change to the colimit ring is surjective and `C₀` is of finite type over
`B₀`, then the base change of `φ₀` to some later stage `Aᵢ` is already surjective. -/
theorem finite_type_surjectivity_descends_along_directed_ring_colimit
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    (hsurj :
      letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
      Function.Surjective (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)))
    (hfinite : φ₀.FiniteType) :
    ∃ (i : I) (hi : i₀ ≤ i),
      letI : Algebra (A i₀) (A i) := (f i₀ i hi).toAlgebra
      Function.Surjective (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A i))) :=
  sorry

end
