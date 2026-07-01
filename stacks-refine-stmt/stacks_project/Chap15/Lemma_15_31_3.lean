import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Basic
import stacks_project.Chap15.Lemma_15_90_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped TensorProduct
open scoped KoszulComplex
open Algebra.TensorProduct
open TensorProduct.AlgebraTensorModule

namespace RingTheory.Sequence

section

variable {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
variable [Algebra A B] [Algebra A A']
variable {r : ℕ}

local notation "B'" => A' ⊗[A] B

/- Domain-style sampling for the base-change map on first Koszul homology:
- primary domain: first Koszul homology under scalar extension/base change in commutative algebra;
- sampled owner declarations:
  `koszulH1`,
  `koszulH1Presentation`,
  `koszulH1IsoPresentation`,
  `LinearMap.baseChange`,
  `LinearMap.liftBaseChange`;
- owner abstraction: the source-facing owner is the chapter declaration `koszulH1 f B`; the
  quotient presentation `koszulH1Presentation` is only an internal bridge/view;
- source/core/bridge triage:
  `source-facing`: the canonical comparison on first Koszul homology under base change;
  `core/canonical`: the owner `koszulH1 f B`;
  `bridge/view`: the quotient presentation `koszulH1Presentation` and its induced base-change map;
- primitive data vs derived API: the only public datum is the canonical base-change map on the
  owner `koszulH1`, obtained by conjugating the private quotient-presentation map with the
  canonical presentation isomorphisms; surjectivity under the flat-quotient hypothesis is the
  derived theorem.
-/
private abbrev baseChangeSequence (f : Fin r → B) : Fin r → B' :=
  fun i ↦ includeRight (f i)

private abbrev koszulFirstCyclesSelf
    (R : Type u) [CommRing R] {n : ℕ} (f : Fin n → R) : Submodule R (Fin n → R) :=
  show Submodule R (Fin n → R) from koszulFirstCycles f R

private abbrev koszulH1Self
    (R : Type u) [CommRing R] {n : ℕ} (f : Fin n → R) : ModuleCat R :=
  show ModuleCat R from koszulH1 f R

private abbrev koszulH1PresentationSelf
    (R : Type u) [CommRing R] {n : ℕ} (f : Fin n → R) : Type u :=
  (koszulFirstCyclesSelf R f) ⧸ (koszulDiagonalMap f R).range

private theorem baseChangeSequence_firstCycleCondition (f : Fin r → B)
    (x : koszulFirstCyclesSelf B f) :
    ∀ i j : Fin r,
      (includeRight (f i) : B') * (includeRight (x.1 j) : B') =
        (includeRight (f j) : B') * (includeRight (x.1 i) : B') := by
  intro i j
  simpa [Algebra.smul_def] using
    congrArg (includeRight : B →ₐ[A] B') ((koszulFirstCycleCondition_of_mem f B x.2) i j)

private def koszulFirstCyclesBaseChangeMap (f : Fin r → B) :
    koszulFirstCyclesSelf B f →ₗ[A]
      koszulFirstCyclesSelf (A' ⊗[A] B) (baseChangeSequence f) where
  toFun x := ⟨fun i ↦ includeRight (x.1 i), by
    exact
      (mem_koszulFirstCycles_iff (baseChangeSequence f) B' (fun i ↦ includeRight (x.1 i))).2
        (baseChangeSequence_firstCycleCondition f x)⟩
  map_add' x y := by
    ext i
    simpa using (includeRight : B →ₐ[A] B').toLinearMap.map_add (x.1 i) (y.1 i)
  map_smul' a x := by
    ext i
    simpa using (includeRight : B →ₐ[A] B').toLinearMap.map_smul a (x.1 i)

local instance (f : Fin r → B) : Module A ↑(koszulH1 f B) :=
  Module.compHom ↑(koszulH1 f B) (algebraMap A B)

local instance (f : Fin r → B) : Module A (koszulH1PresentationSelf B f) :=
  inferInstance

local instance (f : Fin r → B) :
    Module A ↑(koszulH1Self (A' ⊗[A] B) (baseChangeSequence f)) :=
  Module.compHom ↑(koszulH1Self (A' ⊗[A] B) (baseChangeSequence f)) (algebraMap A B')

local instance (f : Fin r → B) :
    Module A' ↑(koszulH1Self (A' ⊗[A] B) (baseChangeSequence f)) :=
  Module.compHom ↑(koszulH1Self (A' ⊗[A] B) (baseChangeSequence f)) (algebraMap A' B')

local instance (f : Fin r → B) :
    IsScalarTower A A' ↑(koszulH1Self (A' ⊗[A] B) (baseChangeSequence f)) :=
  IsScalarTower.of_compHom A A' ↑(koszulH1Self (A' ⊗[A] B) (baseChangeSequence f))

local instance (f : Fin r → B) :
    Module A (koszulH1PresentationSelf (A' ⊗[A] B) (baseChangeSequence f)) :=
  inferInstance

local instance (f : Fin r → B) :
    Module A' (koszulH1PresentationSelf (A' ⊗[A] B) (baseChangeSequence f)) :=
  inferInstance

local instance (f : Fin r → B) :
    IsScalarTower A A' (koszulH1PresentationSelf (A' ⊗[A] B) (baseChangeSequence f)) :=
  inferInstance

private def koszulH1PresentationBaseChangeMap (f : Fin r → B) :
    koszulH1PresentationSelf B f →ₗ[A]
      koszulH1PresentationSelf (A' ⊗[A] B) (baseChangeSequence f) :=
  let pB : Submodule B (koszulFirstCyclesSelf B f) :=
    LinearMap.range (koszulDiagonalMap f B)
  let p : Submodule A (koszulFirstCyclesSelf B f) :=
    pB.restrictScalars A
  let qB : Submodule B' (koszulFirstCyclesSelf (A' ⊗[A] B) (baseChangeSequence f)) :=
    LinearMap.range (koszulDiagonalMap (baseChangeSequence f) B')
  let q : Submodule A (koszulFirstCyclesSelf (A' ⊗[A] B) (baseChangeSequence f)) :=
    qB.restrictScalars A
  let mapQ : (koszulFirstCyclesSelf B f ⧸ p) →ₗ[A]
      (koszulFirstCyclesSelf (A' ⊗[A] B) (baseChangeSequence f) ⧸ q) :=
    p.mapQ q (koszulFirstCyclesBaseChangeMap f) (by
      intro x hx
      rcases hx with ⟨y, rfl⟩
      refine ⟨includeRight y, ?_⟩
      ext i
      change
        (includeRight (f i) : B') * (includeRight y : B') =
          (includeRight (f i * y) : B')
      simp)
  let sourceEquiv' :
      (koszulFirstCyclesSelf B f ⧸ p) ≃ₗ[A]
        ((koszulFirstCyclesSelf B f) ⧸ (koszulDiagonalMap f B).range) :=
    by
      simpa [p, pB] using (Submodule.Quotient.restrictScalarsEquiv A pB)
  let sourceEquiv :
      (koszulFirstCyclesSelf B f ⧸ p) ≃ₗ[A] koszulH1PresentationSelf B f :=
    by
      simpa [koszulH1PresentationSelf] using sourceEquiv'
  let targetEquiv' :
      (koszulFirstCyclesSelf (A' ⊗[A] B) (baseChangeSequence f) ⧸ q) ≃ₗ[A]
        ((koszulFirstCyclesSelf (A' ⊗[A] B) (baseChangeSequence f)) ⧸
          (koszulDiagonalMap (baseChangeSequence f) B').range) :=
    by
      simpa [q, qB] using (Submodule.Quotient.restrictScalarsEquiv A qB)
  let targetEquiv :
      (koszulFirstCyclesSelf (A' ⊗[A] B) (baseChangeSequence f) ⧸ q) ≃ₗ[A]
        koszulH1PresentationSelf (A' ⊗[A] B) (baseChangeSequence f) :=
    by
      simpa [koszulH1PresentationSelf] using targetEquiv'
  targetEquiv.toLinearMap ∘ₗ mapQ ∘ₗ sourceEquiv.symm.toLinearMap

private noncomputable def koszulH1PresentationBaseChangeHom (f : Fin r → B) :
    A' ⊗[A] koszulH1PresentationSelf B f →ₗ[A']
      koszulH1PresentationSelf (A' ⊗[A] B) (baseChangeSequence f) :=
  (koszulH1PresentationBaseChangeMap f).liftBaseChange A'

-- Proof sketch: first send a degree-one Koszul cycle `(x₁, …, xᵣ)` in `B` to the base-changed
-- cycle `(1 ⊗ x₁, …, xᵣ)` in `A' ⊗[A] B`; compatibility with diagonal boundaries makes this
-- descend to the canonical base-change map on the quotient presentation of `H₁`. Conjugating
-- that map by the presentation isomorphisms `koszulH1IsoPresentation` yields the public owner-
-- level comparison `A' ⊗[A] koszulH1(B, f) → koszulH1(A' ⊗[A] B, f')`.
private noncomputable def koszulH1BaseChangeCore (f : Fin r → B) :
    A' ⊗[A] koszulH1Self B f →ₗ[A']
      koszulH1Self (A' ⊗[A] B) (baseChangeSequence f) :=
  let sourceIso :
      koszulH1Self B f ≅ ModuleCat.of B (koszulH1PresentationSelf B f) := by
    simpa [koszulH1Self, koszulH1PresentationSelf] using (koszulH1IsoPresentation f B)
  let targetIso :
      koszulH1Self (A' ⊗[A] B) (baseChangeSequence f) ≅
        ModuleCat.of B' (koszulH1PresentationSelf (A' ⊗[A] B) (baseChangeSequence f)) := by
    simpa [koszulH1Self, koszulH1PresentationSelf] using
      (koszulH1IsoPresentation (baseChangeSequence f) B')
  let sourceHom : koszulH1Self B f →ₗ[B] koszulH1PresentationSelf B f := sourceIso.hom.hom
  let sourceToPresentation :
      koszulH1Self B f →ₗ[A] koszulH1PresentationSelf B f :=
    { toFun := sourceHom
      map_add' := sourceHom.map_add
      map_smul' := by
        intro a x
        have hx : a • x = ((algebraMap A B) a) • x := by
          rfl
        rw [hx, sourceHom.map_smul]
        have hy :
            ((algebraMap A B) a) • sourceHom x = a • sourceHom x := by
          sorry
        exact hy }
  let sourceToPresentationBaseChange :
      A' ⊗[A] koszulH1Self B f →ₗ[A']
        A' ⊗[A] koszulH1PresentationSelf B f :=
    LinearMap.baseChange A' sourceToPresentation
  let targetHom :
      koszulH1PresentationSelf (A' ⊗[A] B) (baseChangeSequence f) →ₗ[B']
        koszulH1Self (A' ⊗[A] B) (baseChangeSequence f) :=
    targetIso.inv.hom
  let targetToKoszulH1 :
      koszulH1PresentationSelf (A' ⊗[A] B) (baseChangeSequence f) →ₗ[A']
        koszulH1Self (A' ⊗[A] B) (baseChangeSequence f) :=
    { toFun := targetHom
      map_add' := targetHom.map_add
      map_smul' := by
        intro a x
        have hx : a • x = ((algebraMap A' B') a) • x := by
          sorry
        rw [hx, targetHom.map_smul]
        rfl }
  targetToKoszulH1 ∘ₗ
    koszulH1PresentationBaseChangeHom f ∘ₗ sourceToPresentationBaseChange

variable (A A') in
/-- The canonical base-change map on the source-facing first Koszul homology owner `koszulH1`.
The quotient presentation `koszulH1Presentation` remains private support data. -/
noncomputable def koszulH1BaseChange (f : Fin r → B) :
    A' ⊗[A] koszulH1 f B →ₗ[A']
      koszulH1 (fun i : Fin r ↦ (includeRight (f i) : A' ⊗[A] B)) (A' ⊗[A] B) :=
  show A' ⊗[A] koszulH1 f B →ₗ[A']
      koszulH1 (fun i : Fin r ↦ (includeRight (f i) : A' ⊗[A] B)) (A' ⊗[A] B) from
    koszulH1BaseChangeCore f

-- Proof sketch: tensoring the owner `koszulH1(B, f)` over `A` can be computed through the
-- private quotient presentation, and flatness of `B ⧸ Ideal.span (Set.range f)` over `A` makes
-- the resulting canonical comparison map onto the base-changed first homology surjective.
variable (A A') in
/-- Lemma 15.31.3: if `B ⧸ Ideal.span (Set.range f)` is flat over `A`, then the canonical map
`A' ⊗[A] H_1(K_\\bullet(B, f)) → H_1(K_\\bullet(A' ⊗[A] B, f'))` is surjective. In Lean the public
surface is the chapter owner `koszulH1`, with the quotient presentation
used only privately to build the comparison map. -/
theorem koszulH1_baseChange_surjective_of_flat_quotient (f : Fin r → B)
    [Module.Flat A (B ⧸ Ideal.span (Set.range f))] :
    Function.Surjective (koszulH1BaseChange A A' f) := by
  sorry

end

end RingTheory.Sequence
