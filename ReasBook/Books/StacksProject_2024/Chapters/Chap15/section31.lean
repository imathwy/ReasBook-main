import Mathlib
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_31_1 (from Chap15) -/
noncomputable section

universe u

open CategoryTheory.Limits

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]

-- Proof sketch: by Lemma 15.30.4 and induction, replacing any entry of a Koszul-regular sequence
-- by a positive power preserves Koszul-regularity, and Lemma 15.28.4 lets us permute the sequence.
-- Hence each powered family `(fun i ↦ f i ^ (n + 1))` is still Koszul-regular, so its Koszul
-- complex has vanishing positive homology. Lemma 15.29.6 identifies the extended alternating Čech
-- complex with the colimit of these Koszul complexes, from which the only possible nonvanishing
-- cohomology degree is the top degree `r`.
/-- Lemma 15.31.1: if `f : Fin r → R` is a Koszul-regular sequence, then the extended alternating
Čech complex attached to `f` has vanishing cohomology in every degree `i ≠ r`. -/
theorem extendedAlternatingCechComplex_homology_isZero_of_isKoszulRegularSequence {r : ℕ}
    (f : Fin r → R) (hKoszul : IsKoszulRegularSequence f) (i : ℕ) (hi : i ≠ r) :
    IsZero ((extendedAlternatingCechComplex f R).homology i) := sorry

end RingTheory.Sequence

/-! ### Lemma_15_31_2 (from Chap15) -/
noncomputable section

universe u

open scoped AffineBlowupChart

section

variable {R : Type u} [CommRing R]
variable {r : ℕ} (f : Fin (r + 1) → R)

local notation "I" => Ideal.span (Set.range f)
local notation "a" => tupleSpanFirst f
local notation "Q" => affineBlowupTuplePresentationQuotient f
local notation "Chart" => R[I / a]

/- Domain triage:
* primary domain: affine blowup charts and their canonical quotient presentations;
* sampled owner declarations: `affineBlowupTuplePresentationMap`,
  `affineBlowupTuplePresentationQuotient`, `tupleSpanFirst`, and the chart owner `R[I / a]`;
* best owner abstraction: the Chapter 10 presentation map is the primitive owner, and this file
  adds the `H₁`-regularity specialization upgrading that map to an equivalence;
* primitive data: the quotient presentation and its canonical map to the affine blowup chart;
* derived API: bijectivity of that map under `IsH1RegularSequence` and the resulting `AlgEquiv`.
-/

/-- Under `H₁`-regularity, the canonical presentation map to the affine blowup algebra is
bijective. -/
-- Proof sketch: Lemma `10.70.6` gives a surjective presentation map whose kernel is the
-- `a₁`-power torsion. The `H₁`-regularity hypothesis implies the quotient presentation is
-- `a₁`-torsion free, so that kernel is zero and the canonical map is injective.
private theorem affineBlowupTuplePresentationMap_bijective_of_isH1RegularSequence
    (hreg : RingTheory.Sequence.IsH1RegularSequence f) :
    Function.Bijective (affineBlowupTuplePresentationMap f) := sorry

/-- Lemma 15.31.2: if `a₁, …, aᵣ₊₁` is an `H_1`-regular sequence in `R`, then the affine blowup
algebra of the ideal it generates at `a₁` is canonically isomorphic to the quotient
`R[y₂, …, yᵣ₊₁] / (a₁ yᵢ - aᵢ₊₁)`. -/
noncomputable def affineBlowupTuplePresentationOfIsH1RegularSequence
    (hreg : RingTheory.Sequence.IsH1RegularSequence f) : Q ≃ₐ[R] Chart :=
  AlgEquiv.ofBijective (affineBlowupTuplePresentationMap f)
    (affineBlowupTuplePresentationMap_bijective_of_isH1RegularSequence f hreg)

/-- The canonical isomorphism of Lemma 15.31.2 is the Chapter 10 presentation map equipped with
its `H₁`-regularity inverse. -/
theorem affineBlowupTuplePresentationOfIsH1RegularSequence_toAlgHom
    (hreg : RingTheory.Sequence.IsH1RegularSequence f) :
    (affineBlowupTuplePresentationOfIsH1RegularSequence f hreg).toAlgHom =
      affineBlowupTuplePresentationMap f := rfl

end

/-! ### Lemma_15_31_3 (from Chap15) -/
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

/-! ### Lemma_15_31_4 (from Chap15) -/
universe u

open scoped TensorProduct
open Algebra.TensorProduct

namespace RingTheory.Sequence

section

variable {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
variable [Algebra A B] [Algebra A A']
variable {r : ℕ}

local notation "B'" => A' ⊗[A] B

/- Domain triage:
* primary domain: quasi-regular and `H₁`-regular finite sequences under tensor base change in
  commutative algebra;
* sampled owner declarations: `IsQuasiRegularSequence` from Chapter 10, `IsH1RegularSequence`
  from Definition `15.30.1`, `IsQuasiRegular.of_flat` from Lemma `10.69.3`, and
  `koszulH1BaseChange`/`koszulH1_baseChange_surjective_of_flat_quotient` from Lemma `15.31.3`;
* best owner abstraction: the ring-valued quasi-regular statement should use the ring-level owner
  `IsQuasiRegularSequence`, while the `H₁`-regular statement should stay on the finite-family
  owner `IsH1RegularSequence`;
* primitive data vs derived API: the only primitive input is the finite family `f`; the tensor
  base-changed family is a derived view, so the public surface should reuse the existing owner
  predicates rather than restating the regular-module case through the more general
  module-valued predicate.
-/

-- Proof sketch: let `J = Ideal.span (Set.range f)`. Quasi-regularity identifies each graded piece
-- `J^n / J^(n + 1)` with a direct sum of copies of `B ⧸ J`, hence these graded pieces are flat
-- over `A`. By the flatness criterion for successive quotients, the quotients `B ⧸ J^n` remain
-- flat over `A`. After base change, the powers of the extended ideal are the tensor products of
-- the powers of `J`, so the associated graded criterion for quasi-regularity carries over to the
-- image sequence in `A' ⊗[A] B`.
/-- Lemma 15.31.4 (1): if `B ⧸ Ideal.span (Set.range f)` is flat over `A` and the finite family
`f` is quasi-regular in `B`, then its image in `A' ⊗[A] B` is quasi-regular. -/
theorem isQuasiRegularSequence_baseChange_of_flat_quotient (f : Fin r → B)
    [Module.Flat A (B ⧸ Ideal.span (Set.range f))]
    (hqr : IsQuasiRegularSequence (List.ofFn f)) :
    IsQuasiRegularSequence
      (List.ofFn fun i : Fin r ↦ (includeRight (f i) : B')) := sorry

-- Proof sketch: apply Lemma `15.31.3` to obtain a surjective comparison map from the base change
-- of `H_1(K_\bullet(B, f))` onto `H_1(K_\bullet(A' ⊗[A] B, f'))`. If `f` is `H_1`-regular, then
-- the source is zero, so surjectivity forces the target first Koszul homology to vanish as well.
/-- Lemma 15.31.4 (2): if `B ⧸ Ideal.span (Set.range f)` is flat over `A` and the finite family
`f` is `H_1`-regular in `B`, then its image in `A' ⊗[A] B` is `H_1`-regular. -/
theorem isH1RegularSequence_baseChange_of_flat_quotient (f : Fin r → B)
    [Module.Flat A (B ⧸ Ideal.span (Set.range f))]
    (hreg : IsH1RegularSequence f) :
    IsH1RegularSequence
      (fun i ↦ includeRight (f i) : Fin r → B') := sorry

end

end RingTheory.Sequence

/-! ### Lemma_15_31_5 (from Chap15) -/
universe u

open RingTheory

namespace RingTheory.Sequence

section

variable {A' : Type u} [CommRing A']
variable {B' : Type u} [CommRing B'] [Algebra A' B']
variable [Module.Flat A' B'] [Algebra.FinitePresentation A' B']

variable {I : Ideal A'} {r : ℕ} (f' : Fin r → B')

local notation "IB" => Ideal.map (algebraMap A' B') I
local notation "FiberRing" => B' ⧸ IB
local notation "fbar" => fun i : Fin r ↦ Ideal.Quotient.mk IB (f' i)
local notation "FiberQuot" => FiberRing ⧸ Ideal.span (Set.range fbar)
local notation "Quot" => B' ⧸ Ideal.span (Set.range f')

/- Domain-style sampling for Lemma 15.31.5:
* primary domain: flatness of quotients by finite quasi-regular sequences across a locally
  nilpotent thickening in commutative algebra;
* sampled owner declarations:
  `Ideal.IsLocallyNilpotent`,
  `RingTheory.Sequence.IsQuasiRegularSequence`,
  `RingTheory.Sequence.isQuasiRegularSequence_baseChange_of_flat_quotient`,
  `flat_over_middleRing_of_locallyNilpotent_of_flat_over_base_and_flat_mod_extended_ideal`;
* best owner abstraction: the theorem itself is `source-facing` and should stay a direct flatness
  statement for the quotient ring `B' ⧸ (f'_1, ..., f'_r)`, but the ambient flatness and finite
  presentation of `A' → B'` belong to the canonical algebra owners `[Module.Flat A' B']` and
  `[Algebra.FinitePresentation A' B']`;
* primitive data vs derived API: the primitive data are the algebra `A' → B'`, the locally
  nilpotent ideal `I`, and the tuple `f'`; the quotient presentations `FiberRing`, `FiberQuot`,
  and `Quot` are only bridge views, and the quasi-regularity hypothesis serves only to supply the
  closed-fiber flatness input.

Source/core/bridge triage:
* `source-facing`: the flatness of `Quot` over `A'`;
* `core/canonical`: `Module.Flat`, `Algebra.FinitePresentation`, `Ideal.IsLocallyNilpotent`, and
  `IsQuasiRegularSequence`;
* `bridge/view`: the quotient models `FiberRing = B' / IB` and
  `FiberQuot = FiberRing / (fbar_1, ..., fbar_r)`.
-/

-- Proof sketch: localize at a prime of `Quot` and use the local criterion for flatness. The
-- ambient owners `[Module.Flat A' B']` and `[Algebra.FinitePresentation A' B']` provide the
-- finitely presented flat map needed to invoke the fiberwise criterion on the localized diagram,
-- reducing to regularity in the fiber. Lemma `15.31.4` gives quasi-regularity after passage to
-- the fiber, and Lemma `15.30.7` upgrades quasi-regularity to regularity in the Noetherian local
-- fiber ring, yielding flatness of `Quot` over `A'`.
/-- Lemma 15.31.5: let `A' → B'` be a flat finitely presented ring map, let `I ⊆ A'` be a locally
nilpotent ideal, and let `f'_1, \ldots, f'_r ∈ B'`. If the images of `f'_1, \ldots, f'_r` in
`B' / I B'` form a quasi-regular sequence and the quotient `(B' / I B') / (f'_1, \ldots, f'_r)`
is flat over `A' / I`, then `B' / (f'_1, \ldots, f'_r)` is flat over `A'`. -/
theorem flat_quotient_of_quasiRegularSequence_mod_locallyNilpotent
    (hI : I.IsLocallyNilpotent)
    (hqr : IsQuasiRegularSequence (List.ofFn fbar))
    (hquot : Module.Flat (A' ⧸ I) FiberQuot) :
    Module.Flat A' Quot := sorry

end

end RingTheory.Sequence

/-! ### Lemma_15_31_6 (from Chap15) -/
universe u

open RingTheory

namespace RingTheory.Sequence

section

variable {A' : Type u} [CommRing A']
variable {B' : Type u} [CommRing B'] [Algebra A' B']
variable [Module.Flat A' B'] [Algebra.FinitePresentation A' B']
variable {I : Ideal A'} {r : ℕ} (f' : Fin r → B')

local notation "IB" => Ideal.map (algebraMap A' B') I
local notation "FiberRing" => B' ⧸ IB
local notation "fbar" => fun i : Fin r ↦ Ideal.Quotient.mk IB (f' i)
local notation "FiberQuot" => FiberRing ⧸ Ideal.span (Set.range fbar)
local notation "Quot" => B' ⧸ Ideal.span (Set.range f')

/- Domain-style sampling for Lemma 15.31.6:
* primary domain: smooth quotients by finite quasi-regular sequences across a locally nilpotent
  thickening in commutative algebra;
* sampled owner declarations:
  `Ideal.IsLocallyNilpotent`,
  `RingTheory.Sequence.IsQuasiRegularSequence`,
  `RingTheory.Sequence.flat_quotient_of_quasiRegularSequence_mod_locallyNilpotent`,
  `Algebra.smooth_iff_forall_smoothAtPrime`;
* best owner abstraction: this theorem is `source-facing` and should remain a direct smoothness
  statement for the quotient ring, while the ambient flatness and finite presentation of
  `A' → B'` belong to the canonical algebra owners `[Module.Flat A' B']` and
  `[Algebra.FinitePresentation A' B']`;
* primitive data vs derived API: the primitive inputs are the algebra `A' → B'`, the locally
  nilpotent ideal `I`, the tuple `f'`, and the smooth closed fiber `FiberQuot`; the quotient
  presentations `FiberRing`, `FiberQuot`, and `Quot` are only bridge views.

Source/core/bridge triage:
* `source-facing`: the smoothness of `Quot` over `A'`;
* `core/canonical`: `Algebra.Smooth`, `Module.Flat`, `Algebra.FinitePresentation`,
  `Ideal.IsLocallyNilpotent`, and `IsQuasiRegularSequence`;
* `bridge/view`: the quotient models `FiberRing = B' / IB` and
  `FiberQuot = FiberRing / (fbar_1, ..., fbar_r)`.
-/

-- Proof sketch: Lemma `15.31.5` gives flatness of `Quot` over `A'`. Smoothness of the closed
-- fiber `FiberQuot` over `A' ⧸ I` implies finite presentation of `FiberQuot`, hence finite
-- presentation of `Quot` over `A'` across the locally nilpotent thickening. For every prime of
-- `Quot`, reduction modulo `I` leaves the fiber over the corresponding prime of `A'` unchanged,
-- so the fiber is smooth by
-- the hypothesis on `FiberQuot`. The flat finitely presented smooth-fiber criterion then yields
-- smoothness of `Quot` over `A'`.
/-- Lemma 15.31.6: let `A' → B'` be a flat finitely presented ring map, let `I ⊆ A'` be a locally
nilpotent ideal, and let `f'_1, \ldots, f'_r ∈ B'`. If the images of `f'_1, \ldots, f'_r` in
`B' / I B'` form a quasi-regular sequence and the quotient
`(B' / I B') / (f'_1, \ldots, f'_r)` is smooth over `A' / I`, then `B' / (f'_1, \ldots, f'_r)`
is smooth over `A'`. -/
theorem smooth_quotient_of_quasiRegularSequence_mod_locallyNilpotent
    (hI : I.IsLocallyNilpotent)
    (hqr : IsQuasiRegularSequence (List.ofFn fbar))
    (hsmooth : Algebra.Smooth (A' ⧸ I) FiberQuot) :
    Algebra.Smooth A' Quot := sorry

end

end RingTheory.Sequence
