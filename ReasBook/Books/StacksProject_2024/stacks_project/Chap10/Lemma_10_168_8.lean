import StacksProject_2024.stacks_project.Chap10.Lemma_10_168_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

noncomputable section

section

/- 
Domain sampling:
* Primary domain: descent of smoothness for finitely presented algebra maps along directed ring
  colimits.
* Relevant owner declarations inspected:
  - `Algebra.TensorProduct.map`
  - `Ring.DirectLimit.of`
  - `DirectedFiniteTypeHomApproximation.stageBaseChange` from `Lemma_10_127_14`
  - `finite_presentation_bijectivity_descends_along_directed_ring_colimit` from `Lemma_10_168_6`
  - `finitePresentation_etale_baseChange_descends_to_stage` from `Lemma_10_168_7`
* Best owner abstraction:
  - `source-facing`: the smoothness descent theorem below
  - `core/canonical`: stagewise and direct-limit tensor-product base change via
    `Algebra.TensorProduct.map`
  - `bridge/view`: the chosen directed-system presentation of the colimit
* Layer triage:
  - `source-facing`: the smoothness descent theorem below
  - `core/canonical`: tensor-product base change to a stage or to `Ring.DirectLimit`
  - `bridge/view`: any chosen ring isomorphic to the direct limit
* Primitive vs. derived:
  - primitive data: the directed system, the distinguished stage, and the stage algebra map `φ₀`
  - derived API: the stagewise and direct-limit tensor-product base-change maps
-/

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (A : I → Type u) [∀ i, CommRing (A i)]
variable (f : ∀ i j, i ≤ j → A i →+* A j)
variable [DirectedSystem A (fun i j hij ↦ f i j hij)]
variable {i₀ : I}
variable {B₀ : Type w} [CommRing B₀] [Algebra (A i₀) B₀]
variable {C₀ : Type w} [CommRing C₀] [Algebra (A i₀) C₀]

local notation "A∞" => Ring.DirectLimit A (fun i j hij ↦ f i j hij)

-- Proof sketch: write the limit base change of `φ₀` as the filtered-colimit base change of the
-- finitely presented map `B₀ → C₀`. Choose a finite presentation of `φ₀`, express smoothness by a
-- Jacobian criterion over the colimit ring, and descend the finitely many coefficients and
-- splitting data appearing in that criterion to some sufficiently large stage using the directed
-- colimit approximation lemmas from Section `10.127`.
/-- Lemma 10.168.8: if a finitely presented map of stage algebras becomes smooth after base change to
the direct limit ring, then its base change to some later stage is already smooth. -/
theorem exists_smooth_stageBaseChange_of_smooth_limitBaseChange
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    (hfp : φ₀.FinitePresentation)
    (hsmooth :
      letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).Smooth) :
    ∃ (j : I) (hij : i₀ ≤ j),
      letI : Algebra (A i₀) (A j) := (f i₀ j hij).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j))).Smooth := sorry

end
