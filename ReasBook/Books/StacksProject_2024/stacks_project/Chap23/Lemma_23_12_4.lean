import StacksProject_2024.stacks_project.Chap23.Lemma_23_12_1
import Mathlib.RingTheory.TensorProduct.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra.TensorProduct
open scoped TensorProduct

universe uR uK uA uι

section

variable {R : Type uR} [CommRing R]
variable {r : ℕ} {f : Fin r → R}

/- Source/core/bridge triage:
- `source-facing`: Lemma 23.12.4 is an existence statement for a morphism
  `K_t ⟶ K_n ⊗_R K_t` in the derived category of left differential graded `K_N`-modules.
- `core/canonical`: the Chapter 23 powered-Koszul owner already present in the repository is
  `PoweredKoszulApproximationContext`, together with the Tate-approximation roof
  `PoweredKoszulTateApproximation` from `Lemma_23_12_1`.
- `bridge/view`: the structure below records a source-facing representative of the derived
  morphism by such a roof: a Tate approximation `A → K_t` at a stage `N > n` together with a map
  `A → K_n ⊗_R A` whose composite with the tensor multiplication induced by `K_n → K_t` and
  `A → K_t` recovers `A → K_t`.
-/

/-- The underlying `R`-algebra map of the comparison map `A ⟶ K_n` in a powered Koszul Tate
approximation. -/
abbrev PoweredKoszulTateApproximation.toKoszulAlgHom
    {f : Fin r → R} {ctx : PoweredKoszulApproximationContext.{uR, uK} f} {n : ℕ}
    (A : PoweredKoszulTateApproximation.{uR, uK, uA, uι} ctx n) :
    A.A →ₐ[R] ctx.koszul n :=
  A.toKoszul.toAlgHom

/-- A source-facing witness for Lemma 23.12.4: a Tate approximation `A → K_t` at a larger stage
`N > n`, together with a factorization `A ⟶ K_n ⊗_R A` whose composite with the tensor
multiplication `K_n ⊗_R A ⟶ K_t` induced by `K_n ⟶ K_t` and `A ⟶ K_t` recovers the approximation
map `A ⟶ K_t`. This is the Chapter 23 roof realizing the derived morphism
`K_t ⟶ K_n ⊗_R K_t`. -/
structure PoweredKoszulTensorFactorization
    {f : Fin r → R} (ctx : PoweredKoszulApproximationContext.{uR, uK} f)
    {n t : ℕ} (htn : t ≤ n) where
  /-- The chosen Tate approximation of `K_t`. -/
  approximation : PoweredKoszulTateApproximation.{uR, uK, uA, uι} ctx t
  /-- The larger powered stage attached to the Tate approximation strictly dominates `n`. -/
  lt_stage : n < approximation.N
  /-- The factorization map `A ⟶ K_n ⊗_R A`. -/
  factorization : approximation.A →ₐ[R] ctx.koszul n ⊗[R] approximation.A
  /-- Composing with the induced tensor multiplication recovers `A ⟶ K_t`. -/
  factorization_comp :
    (productMap (ctx.transitionAlgHom htn) approximation.toKoszulAlgHom).comp factorization =
      approximation.toKoszulAlgHom

/-- The tensor-product target `K_n ⊗_R A` associated to a powered Koszul tensor factorization. -/
abbrev PoweredKoszulTensorFactorization.target
    {ctx : PoweredKoszulApproximationContext.{uR, uK} f} {n t : ℕ} {htn : t ≤ n}
    (F : PoweredKoszulTensorFactorization.{uR, uK, uA, uι} ctx htn) :=
  ctx.koszul n ⊗[R] F.approximation.A

/-- The multiplication map `K_n ⊗_R A ⟶ K_t` attached to a powered Koszul tensor factorization. -/
abbrev PoweredKoszulTensorFactorization.multiplication
    {ctx : PoweredKoszulApproximationContext.{uR, uK} f} {n t : ℕ} {htn : t ≤ n}
    (F : PoweredKoszulTensorFactorization.{uR, uK, uA, uι} ctx htn) :
    F.target →ₐ[R] ctx.koszul t :=
  productMap (ctx.transitionAlgHom htn) F.approximation.toKoszulAlgHom

/-- The factorization stored in `PoweredKoszulTensorFactorization` lands in its canonical tensor
target. -/
abbrev PoweredKoszulTensorFactorization.toTarget
    {ctx : PoweredKoszulApproximationContext.{uR, uK} f} {n t : ℕ} {htn : t ≤ n}
    (F : PoweredKoszulTensorFactorization.{uR, uK, uA, uι} ctx htn) :
    F.approximation.A →ₐ[R] F.target :=
  F.factorization

/-- The defining compatibility of a powered Koszul tensor factorization. -/
theorem PoweredKoszulTensorFactorization.multiplication_comp_toTarget
    {ctx : PoweredKoszulApproximationContext.{uR, uK} f} {n t : ℕ} {htn : t ≤ n}
    (F : PoweredKoszulTensorFactorization.{uR, uK, uA, uι} ctx htn) :
    (F.multiplication).comp F.toTarget = F.approximation.toKoszulAlgHom :=
  F.factorization_comp

/-- Lemma 23.12.4: over a Noetherian ring, for every `n ≥ t ≥ 1` there exists a larger stage
`N > n`, a Tate-approximation roof `A → K_t` from Lemma 23.12.1 at stage `N`, and a map
`A ⟶ K_n ⊗_R A` whose composite with the tensor multiplication
`K_n ⊗_R A ⟶ K_t` induced by `K_n ⟶ K_t` and `A ⟶ K_t` recovers the approximation map
`A ⟶ K_t`. This witness is the source-facing representative of the derived morphism
`K_t ⟶ K_n ⊗_R K_t`. -/
@[stacks 0GZ7]
theorem exists_koszulTensorFactorization
    [IsNoetherianRing R]
    (ctx : PoweredKoszulApproximationContext.{uR, uK} f)
    {n t : ℕ} (ht : 1 ≤ t) (htn : t ≤ n) :
    Nonempty (PoweredKoszulTensorFactorization.{uR, uK, uA, uι} ctx htn) := by
  sorry

end
