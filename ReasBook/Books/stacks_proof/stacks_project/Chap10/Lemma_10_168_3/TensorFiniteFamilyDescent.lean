import stacks_proof.stacks_project.Chap10.Lemma_10_127_5

open LinearMap
open scoped TensorProduct

universe u v w y

noncomputable section

namespace DirectedTensorDescend

section

variable {A : Type u} [CommRing A]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (R : I → Type w) [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
variable (f : ∀ i j, i ≤ j → R i →ₐ[A] R j)
variable [DirectedSystem R (fun i j hij ↦ (f i j hij : R i →+* R j))]

local notation "R∞" => Ring.DirectLimit R (fun i j hij ↦ (f i j hij : R i →+* R j))

/-- Helper for Lemma 10.168.3: reuse the canonical stage tensor map from the earlier filtered
colimit tensor-descent API, rather than maintaining a duplicate local copy. -/
abbrev stageTensorMap (X : Type*) [AddCommGroup X] [Module A X] (i : I) :
    R i ⊗[A] X →ₗ[A] R∞ ⊗[A] X :=
  _root_.stageTensorMap (A := A) (R := R) (f := f) X i

/-- Helper for Lemma 10.168.3: every tensor over the direct-limit ring already lifts from some
stage, via the canonical owner theorem from Section 10.127. -/
theorem tensor_lifts_from_stage
    (X : Type*) [AddCommGroup X] [Module A X]
    (z : R∞ ⊗[A] X) :
    ∃ i : I, ∃ z_i : R i ⊗[A] X,
      stageTensorMap (R := R) (f := f) X i z_i = z := by
  -- Proof comment: this is exactly the earlier proved tensor-lifting theorem, specialized to the
  -- current directed system and re-expressed through the local namespace alias.
  simpa [stageTensorMap] using
    (_root_.tensor_lifts_from_stage (A := A) (R := R) (f := f) X z)

/-- Helper for Lemma 10.168.3: finitely many tensors over the direct-limit ring lift
simultaneously to one common stage, reusing the canonical Section 10.127 descent lemma. -/
theorem tensor_lifts_from_stage_on_finset
    {ι : Type y} [DecidableEq ι]
    (X : Type*) [AddCommGroup X] [Module A X]
    (s : Finset ι) (z : ι → R∞ ⊗[A] X) :
    ∃ i : I, ∃ z_i : ι → R i ⊗[A] X,
      ∀ a ∈ s, stageTensorMap (R := R) (f := f) X i (z_i a) = z a := by
  -- Proof comment: pass directly to the canonical finite-family lifting theorem and rewrite the
  -- stage tensor map through the local alias.
  simpa [stageTensorMap] using
    (_root_.tensor_lifts_from_stage_on_finset (A := A) (R := R) (f := f) (X := X) s z)

/-- Helper for Lemma 10.168.3: finitely many equalities that hold after tensoring to the direct
limit already hold at one sufficiently large stage, by the canonical tensor-descent owner lemma. -/
theorem tensor_equalities_descend_on_finset
    {ι : Type y} [DecidableEq ι]
    (X : Type*) [AddCommGroup X] [Module A X]
    (s : Finset ι) {i : I}
    (x y : ι → R i ⊗[A] X)
    (hxy :
      ∀ a ∈ s,
        stageTensorMap (R := R) (f := f) X i (x a) =
          stageTensorMap (R := R) (f := f) X i (y a)) :
    ∃ j : I, ∃ hij : i ≤ j,
      ∀ a ∈ s,
        LinearMap.rTensor X ((f i j hij).toLinearMap : R i →ₗ[A] R j) (x a) =
          LinearMap.rTensor X ((f i j hij).toLinearMap : R i →ₗ[A] R j) (y a) := by
  -- Proof comment: the local file only needs the established stagewise stabilization statement,
  -- so we re-export the earlier proof instead of keeping a second unfinished copy here.
  simpa [stageTensorMap] using
    (_root_.tensor_equalities_descend_on_finset (A := A) (R := R) (f := f)
      (X := X) s x y hxy)

end

end DirectedTensorDescend
