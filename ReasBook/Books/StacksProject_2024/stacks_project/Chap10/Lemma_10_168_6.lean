import StacksProject_2024.Chap10.Lemma_10_168_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

noncomputable section

section

/-
Domain sampling:
* Primary domain: descent of isomorphism for tensor-product base changes of finitely presented
  algebra maps along directed ring colimits.
* Relevant owner declarations inspected:
  - `Algebra.TensorProduct.map`
  - `Ring.DirectLimit.of`
  - `AlgHom.FinitePresentation`
  - `finite_type_surjectivity_descends_along_directed_ring_colimit` from `Lemma_10_168_4`
* Best owner abstraction:
  - `source-facing`: the directed-ring-colimit descent theorem below
  - `core/canonical`: tensor-product base change via `Algebra.TensorProduct.map` and finite
    presentation via the owner predicate `AlgHom.FinitePresentation`
  - `bridge/view`: the chosen directed-system presentation of the direct limit ring
* Primitive vs. derived:
  - primitive data: the directed system `A`, transition maps `f`, the distinguished stage `i₀`,
    and the algebra map `φ₀`
  - derived API: the stagewise and direct-limit base-change maps given by
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

-- Proof sketch: apply Lemma `10.168.4` to descend surjectivity of the colimit base change to some
-- stage. Finite presentation of `φ₀` identifies the kernel of each stagewise base change as a
-- finitely generated ideal, and the vanishing of finitely many kernel generators after passing to
-- the direct limit descends to a later stage by directedness. At that enlarged stage the map is
-- both surjective and injective, hence bijective.
/-- Lemma 10.168.6: let `A = colim_i A_i` be a directed colimit of rings, let `φ₀ : B₀ → C₀` be a
map of `A₀`-algebras, and assume the base change `A ⊗[A₀] B₀ → A ⊗[A₀] C₀` is an isomorphism.
If `φ₀` is of finite presentation, then for some stage `i ≥ i₀` the base-changed map
`Aᵢ ⊗[A₀] B₀ → Aᵢ ⊗[A₀] C₀` is already an isomorphism. -/
theorem finite_presentation_bijectivity_descends_along_directed_ring_colimit
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    (hbij :
      letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
      Function.Bijective (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)))
    (hfinite : φ₀.FinitePresentation) :
    ∃ (i : I) (hi : i₀ ≤ i),
      letI : Algebra (A i₀) (A i) := (f i₀ i hi).toAlgebra
      Function.Bijective (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A i))) :=
  sorry

end
