import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Definition_17_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Construction_17_2_1
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.PrincipalIdealDomain

noncomputable section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

universe u

-- Semantic recall via `Definition_17_1_1`: `ModuleCat.tor` is the source-facing Chapter 17
-- surface for the `Tor` summands. No pre-existing Kunneth short exact sequence owner surfaced in
-- the current environment, so this file records the source-faithful short exact sequence package,
-- natural in the second chain complex `Y` for fixed flat `X`, with the finite direct-sum terms
-- presented by their equivalent finite product modules over the nat antidiagonals.

/-- The left direct-sum term `⨁_(i + j = n + 1) H_i(X) ⊗ H_j(Y)` in the nat-indexed Kunneth
short exact sequence, presented as the finite product module over `Finset.antidiagonal (n + 1)`.
-/
abbrev kunnethTensorTerm
    (R : Type u) [CommRing R] (X Y : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    ModuleCat R :=
  ModuleCat.of R
    (∀ pq : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal (n + 1)},
      (X.homology pq.1.1 ⊗ Y.homology pq.1.2 : ModuleCat R))

/-- `kunnethTensorTerm R X Y n` is the finite product presentation of the tensor-product homology
summands indexed by `Finset.antidiagonal (n + 1)`. -/
@[simp] theorem kunnethTensorTerm_def
    (R : Type u) [CommRing R] (X Y : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    kunnethTensorTerm R X Y n =
      ModuleCat.of R
        (∀ pq : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal (n + 1)},
          (X.homology pq.1.1 ⊗ Y.homology pq.1.2 : ModuleCat R)) :=
  rfl

/-- The middle homology term `H_(n + 1)(X ⊗ Y)` in the nat-indexed Kunneth short exact
sequence. -/
abbrev kunnethHomologyTerm
    (R : Type u) [CommRing R] (X Y : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    ModuleCat R :=
  (HomologicalComplex.tensorObj X Y).homology (n + 1)

/-- `kunnethHomologyTerm R X Y n` is the homology object
`(HomologicalComplex.tensorObj X Y).homology (n + 1)`. -/
@[simp] theorem kunnethHomologyTerm_def
    (R : Type u) [CommRing R] (X Y : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    kunnethHomologyTerm R X Y n =
      (HomologicalComplex.tensorObj X Y).homology (n + 1) :=
  rfl

/-- The right direct-sum term `⨁_(i + j = n) Tor(H_i(X), H_j(Y))` in the nat-indexed Kunneth
short exact sequence, presented as the finite product module over `Finset.antidiagonal n`. -/
abbrev kunnethTorTerm
    (R : Type u) [CommRing R] (X Y : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    ModuleCat R :=
  ModuleCat.of R
    (∀ pq : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n},
      (ModuleCat.tor R (X.homology pq.1.1) (Y.homology pq.1.2) : ModuleCat R))

/-- `kunnethTorTerm R X Y n` is the finite product presentation of the `Tor(H_i(X), H_j(Y))`
summands indexed by `Finset.antidiagonal n`. -/
@[simp] theorem kunnethTorTerm_def
    (R : Type u) [CommRing R] (X Y : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    kunnethTorTerm R X Y n =
      ModuleCat.of R
        (∀ pq : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n},
          (ModuleCat.tor R (X.homology pq.1.1) (Y.homology pq.1.2) : ModuleCat R)) :=
  rfl

/-- The canonical map on the left Kunneth tensor term induced by a chain map in the second
variable. -/
abbrev kunnethTensorMap
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    {Y Y' : ChainComplex (ModuleCat R) ℕ} (f : Y ⟶ Y') :
    kunnethTensorTerm R X Y n ⟶ kunnethTensorTerm R X Y' n :=
  ModuleCat.ofHom <|
    LinearMap.piMap fun pq ↦
      (𝟙 (X.homology pq.1.1) ⊗ₘ HomologicalComplex.homologyMap f pq.1.2).hom

/-- The canonical homology map on `H_(n + 1)(X ⊗ Y)` induced by `𝟙 X ⊗ f`. -/
abbrev kunnethHomologyMap
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    {Y Y' : ChainComplex (ModuleCat R) ℕ} (f : Y ⟶ Y') :
    kunnethHomologyTerm R X Y n ⟶ kunnethHomologyTerm R X Y' n :=
  HomologicalComplex.homologyMap (HomologicalComplex.tensorHom (𝟙 X) f) (n + 1)

/-- The canonical map on the right Kunneth `Tor` term induced by a chain map in the second
variable. -/
abbrev kunnethTorMap
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    {Y Y' : ChainComplex (ModuleCat R) ℕ} (f : Y ⟶ Y') :
    kunnethTorTerm R X Y n ⟶ kunnethTorTerm R X Y' n :=
  ModuleCat.ofHom <|
    LinearMap.piMap fun pq ↦
      (((ModuleCat.torFunctor R).obj (X.homology pq.1.1)).map
        (HomologicalComplex.homologyMap f pq.1.2)).hom

/-- A short exact sequence realizing the nat-indexed Kunneth theorem for the pair `(X, Y)` in
degree `n + 1`. -/
structure KunnethHomologySequence
    (R : Type u) [CommRing R] (X Y : ChainComplex (ModuleCat R) ℕ) (n : ℕ) where
  tensorToHomology : kunnethTensorTerm R X Y n ⟶ kunnethHomologyTerm R X Y n
  homologyToTor : kunnethHomologyTerm R X Y n ⟶ kunnethTorTerm R X Y n
  zero : tensorToHomology ≫ homologyToTor = 0
  shortExact : (ShortComplex.mk tensorToHomology homologyToTor zero).ShortExact

namespace KunnethHomologySequence

/-- The underlying short complex of a Kunneth homology short exact sequence. -/
abbrev toShortComplex
    {R : Type u} [CommRing R] {X Y : ChainComplex (ModuleCat R) ℕ} {n : ℕ}
    (S : KunnethHomologySequence R X Y n) :
    ShortComplex (ModuleCat R) :=
  ShortComplex.mk S.tensorToHomology S.homologyToTor S.zero

/-- Coercion from a Kunneth homology sequence to its underlying short complex. -/
instance instCoeOut
    {R : Type u} [CommRing R] {X Y : ChainComplex (ModuleCat R) ℕ} {n : ℕ} :
    CoeOut (KunnethHomologySequence R X Y n) (ShortComplex (ModuleCat R)) where
  coe S := S.toShortComplex

end KunnethHomologySequence

/-- A Kunneth short exact sequence that is natural in the second chain complex `Y`, using the
canonical comparison maps on the left tensor term, middle homology term, and right `Tor` term. -/
structure KunnethHomologyNaturality
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ) where
  seq : ∀ Y : ChainComplex (ModuleCat R) ℕ, KunnethHomologySequence R X Y n
  comm₁₂ :
    ∀ {Y Y' : ChainComplex (ModuleCat R) ℕ} (f : Y ⟶ Y'),
      kunnethTensorMap R X n f ≫ (seq Y').tensorToHomology =
        (seq Y).tensorToHomology ≫ kunnethHomologyMap R X n f
  comm₂₃ :
    ∀ {Y Y' : ChainComplex (ModuleCat R) ℕ} (f : Y ⟶ Y'),
      kunnethHomologyMap R X n f ≫ (seq Y').homologyToTor =
        (seq Y).homologyToTor ≫ kunnethTorMap R X n f

namespace KunnethHomologyNaturality

/-- Coercion from a natural Kunneth package to its family of short exact sequences. -/
instance instCoeFun
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℕ} {n : ℕ} :
    CoeFun (KunnethHomologyNaturality R X n)
      (fun _ ↦ ∀ Y : ChainComplex (ModuleCat R) ℕ, KunnethHomologySequence R X Y n) where
  coe S := S.seq

/-- The morphism of short complexes induced by a chain map in the second variable. -/
def map
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℕ} {n : ℕ}
    (S : KunnethHomologyNaturality R X n)
    {Y Y' : ChainComplex (ModuleCat R) ℕ} (f : Y ⟶ Y') :
    (S Y).toShortComplex ⟶ (S Y').toShortComplex :=
  ShortComplex.homMk
    (kunnethTensorMap R X n f)
    (kunnethHomologyMap R X n f)
    (kunnethTorMap R X n f)
    (S.comm₁₂ f)
    (S.comm₂₃ f)

end KunnethHomologyNaturality

/-- Helper for Theorem 17.2.2: each fixed-`Y` Kunneth short complex extracted from a natural
package is short exact. -/
theorem KunnethHomologyNaturality.shortExact
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℕ} {n : ℕ}
    (S : KunnethHomologyNaturality R X n) (Y : ChainComplex (ModuleCat R) ℕ) :
    ((S Y).toShortComplex).ShortExact := by
  -- Evaluate the package at `Y` and read off the stored short exactness witness.
  exact (S Y).shortExact

/-- Helper for Theorem 17.2.2: package a pointwise family of Kunneth short exact sequences
together with the two canonical naturality squares. -/
private def mkKunnethHomologyNaturality
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℕ} {n : ℕ}
    (seq : ∀ Y : ChainComplex (ModuleCat R) ℕ, KunnethHomologySequence R X Y n)
    (comm₁₂ :
      ∀ {Y Y' : ChainComplex (ModuleCat R) ℕ} (f : Y ⟶ Y'),
        kunnethTensorMap R X n f ≫ (seq Y').tensorToHomology =
          (seq Y).tensorToHomology ≫ kunnethHomologyMap R X n f)
    (comm₂₃ :
      ∀ {Y Y' : ChainComplex (ModuleCat R) ℕ} (f : Y ⟶ Y'),
        kunnethHomologyMap R X n f ≫ (seq Y').homologyToTor =
          (seq Y).homologyToTor ≫ kunnethTorMap R X n f) :
    KunnethHomologyNaturality R X n where
  -- This isolates the final assembly step so the theorem body only supplies the fixed-`Y`
  -- sequence and the two naturality squares.
  seq := seq
  comm₁₂ := comm₁₂
  comm₂₃ := comm₂₃

/-- Helper for Theorem 17.2.2: once the fixed-`Y` short exact sequences and naturality squares
are constructed, the full natural Kunneth package exists. -/
private theorem nonempty_kunnethHomologyNaturality_of_data
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℕ} {n : ℕ}
    (seq : ∀ Y : ChainComplex (ModuleCat R) ℕ, KunnethHomologySequence R X Y n)
    (comm₁₂ :
      ∀ {Y Y' : ChainComplex (ModuleCat R) ℕ} (f : Y ⟶ Y'),
        kunnethTensorMap R X n f ≫ (seq Y').tensorToHomology =
          (seq Y).tensorToHomology ≫ kunnethHomologyMap R X n f)
    (comm₂₃ :
      ∀ {Y Y' : ChainComplex (ModuleCat R) ℕ} (f : Y ⟶ Y'),
        kunnethHomologyMap R X n f ≫ (seq Y').homologyToTor =
          (seq Y).homologyToTor ≫ kunnethTorMap R X n f) :
    Nonempty (KunnethHomologyNaturality R X n) := by
  -- Package the pointwise data and witness nonemptiness.
  exact ⟨mkKunnethHomologyNaturality seq comm₁₂ comm₂₃⟩

/-- Helper for Theorem 17.2.2: the left edge for fixed `Y` is the sum of the homology
cross-product maps over the finite antidiagonal. -/
private noncomputable def kunnethTensorSummandToHomology
    (R : Type u) [CommRing R] (X Y : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (pq : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal (n + 1)}) :
    (X.homology pq.1.1 ⊗ Y.homology pq.1.2 : ModuleCat R) ⟶
      kunnethHomologyTerm R X Y n := by
  -- Rewrite the summand degree `pq.1.1 + pq.1.2` to the common total degree `n + 1`.
  rcases pq with ⟨⟨p, q⟩, hpq⟩
  rw [Finset.mem_antidiagonal] at hpq
  simpa [kunnethHomologyTerm, hpq] using
    (chainComplexHomologyCrossProduct (X := X) (Y := Y) (p := p) (q := q))

/-- Helper for Theorem 17.2.2: the left edge for fixed `Y` is the sum of the homology
cross-product maps over the finite antidiagonal. -/
private noncomputable def fixedYKunnethTensorToHomology
    (R : Type u) [CommRing R] (X Y : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    kunnethTensorTerm R X Y n ⟶ kunnethHomologyTerm R X Y n :=
  ModuleCat.ofHom <|
    ∑ pq : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal (n + 1)},
      ((kunnethTensorSummandToHomology R X Y n pq).hom).comp
        (LinearMap.proj pq)

/-- Helper for Theorem 17.2.2: evaluating the left Kunneth map on a single-supported antidiagonal
input recovers the corresponding summand map. -/
private theorem fixedYKunnethTensorToHomology_apply_single
    (R : Type u) [CommRing R]
    (X Y : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (pq : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal (n + 1)})
    (x : (X.homology pq.1.1 ⊗ Y.homology pq.1.2 : ModuleCat R)) :
    ModuleCat.Hom.hom (fixedYKunnethTensorToHomology R X Y n) (Pi.single pq x) =
      ModuleCat.Hom.hom (kunnethTensorSummandToHomology R X Y n pq) x := by
  -- Rewrite the finite antidiagonal sum as the standard `LinearMap.lsum`, whose value on
  -- `Pi.single` is exactly the chosen summand map.
  change
    (∑ pq' : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal (n + 1)},
        ((kunnethTensorSummandToHomology R X Y n pq').hom).comp (LinearMap.proj pq'))
      (Pi.single pq x) =
      ModuleCat.Hom.hom (kunnethTensorSummandToHomology R X Y n pq) x
  simpa [fixedYKunnethTensorToHomology, LinearMap.lsum_apply] using
    (LinearMap.lsum_piSingle
      (R := R)
      (φ := fun pq : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal (n + 1)} ↦
        ((X.homology pq.1.1 ⊗ Y.homology pq.1.2 : ModuleCat R) : Type u))
      (S := R)
      (f := fun pq ↦ (kunnethTensorSummandToHomology R X Y n pq).hom)
      pq x)

/-- Helper for Theorem 17.2.2: on each `(p, q)` summand, the tensor of cycle inclusions is
natural in the second chain complex. -/
private theorem kunnethTensorCycleInclusion_natural
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) {Y Y' : ChainComplex (ModuleCat R) ℕ}
    (f : Y ⟶ Y') (p q : ℕ)
    [HomologicalComplex.HasHomology X p]
    [HomologicalComplex.HasHomology Y q]
    [HomologicalComplex.HasHomology Y' q] :
    ((𝟙 (X.cycles p)) ⊗ₘ HomologicalComplex.cyclesMap f q) ≫
        (X.iCycles p ⊗ₘ Y'.iCycles q) =
      (X.iCycles p ⊗ₘ Y.iCycles q) ≫ X.X p ◁ f.f q := by
  -- Rewrite the source tensor map through the target cycle inclusion.
  calc
    ((𝟙 (X.cycles p)) ⊗ₘ HomologicalComplex.cyclesMap f q) ≫
          (X.iCycles p ⊗ₘ Y'.iCycles q) =
        X.iCycles p ⊗ₘ (HomologicalComplex.cyclesMap f q ≫ Y'.iCycles q) := by
          simpa using
            (whiskerLeft_comp_tensorHom (V := X.cycles p)
              (f := X.iCycles p) (g := HomologicalComplex.cyclesMap f q) (h := Y'.iCycles q))
    -- Then use the naturality square defining `cyclesMap`.
    _ = X.iCycles p ⊗ₘ (Y.iCycles q ≫ f.f q) := by
          rw [HomologicalComplex.cyclesMap_i]
    -- Finally normalize the right tensor factor back to whiskering notation.
    _ = (X.iCycles p ⊗ₘ Y.iCycles q) ≫ X.X p ◁ f.f q := by
          simpa using
            (tensorHom_comp_whiskerLeft (f := X.iCycles p)
              (g := Y.iCycles q) (h := f.f q)).symm

/-- Helper for Theorem 17.2.2: the cycles-level Kunneth cross product is natural in the second
chain complex. -/
private theorem chainComplexCycleCrossProduct_natural
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) {Y Y' : ChainComplex (ModuleCat R) ℕ}
    (f : Y ⟶ Y') (p q : ℕ)
    [HomologicalComplex.HasHomology X p]
    [HomologicalComplex.HasHomology Y q]
    [HomologicalComplex.HasHomology Y' q]
    [HomologicalComplex.HasHomology (HomologicalComplex.tensorObj X Y) (p + q)]
    [HomologicalComplex.HasHomology (HomologicalComplex.tensorObj X Y') (p + q)] :
    ((𝟙 (X.cycles p)) ⊗ₘ HomologicalComplex.cyclesMap f q) ≫
        chainComplexCycleCrossProduct (X := X) (Y := Y') (p := p) (q := q) =
      chainComplexCycleCrossProduct (X := X) (Y := Y) (p := p) (q := q) ≫
        HomologicalComplex.cyclesMap (HomologicalComplex.tensorHom (𝟙 X) f) (p + q) := by
  -- Compare both sides after postcomposing with the target cycle inclusion.
  apply (cancel_mono ((HomologicalComplex.tensorObj X Y').iCycles (p + q))).1
  calc
    ((𝟙 (X.cycles p)) ⊗ₘ HomologicalComplex.cyclesMap f q) ≫
          chainComplexCycleCrossProduct (X := X) (Y := Y') (p := p) (q := q) ≫
          (HomologicalComplex.tensorObj X Y').iCycles (p + q) =
        ((𝟙 (X.cycles p)) ⊗ₘ HomologicalComplex.cyclesMap f q) ≫
          ((X.iCycles p ⊗ₘ Y'.iCycles q) ≫
            HomologicalComplex.ιTensorObj X Y' p q (p + q) rfl) := by
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ ((𝟙 (X.cycles p)) ⊗ₘ HomologicalComplex.cyclesMap f q) ≫ t)
              ((chainComplexCycleCrossProduct_iCycles (X := X) (Y := Y') (p := p) (q := q)).w.symm)
    -- Rewrite the source tensor map and then use graded tensor naturality on `ιTensorObj`.
    _ =
        (X.iCycles p ⊗ₘ Y.iCycles q) ≫ HomologicalComplex.ιTensorObj X Y p q (p + q) rfl ≫
          (HomologicalComplex.tensorHom (𝟙 X) f).f (p + q) := by
          calc
            ((𝟙 (X.cycles p)) ⊗ₘ HomologicalComplex.cyclesMap f q) ≫
                ((X.iCycles p ⊗ₘ Y'.iCycles q) ≫
                  HomologicalComplex.ιTensorObj X Y' p q (p + q) rfl) =
              (((𝟙 (X.cycles p)) ⊗ₘ HomologicalComplex.cyclesMap f q) ≫
                  (X.iCycles p ⊗ₘ Y'.iCycles q)) ≫
                HomologicalComplex.ιTensorObj X Y' p q (p + q) rfl := by
                  simp [Category.assoc]
            _ =
              ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ X.X p ◁ f.f q) ≫
                HomologicalComplex.ιTensorObj X Y' p q (p + q) rfl := by
                  rw [kunnethTensorCycleInclusion_natural R X f p q]
            _ =
              (X.iCycles p ⊗ₘ Y.iCycles q) ≫
                (X.X p ◁ f.f q ≫ HomologicalComplex.ιTensorObj X Y' p q (p + q) rfl) := by
                  simp [Category.assoc]
            _ =
              (X.iCycles p ⊗ₘ Y.iCycles q) ≫
                (HomologicalComplex.ιTensorObj X Y p q (p + q) rfl ≫
                  (HomologicalComplex.tensorHom (𝟙 X) f).f (p + q)) := by
                  exact congrArg
                    (fun t ↦ (X.iCycles p ⊗ₘ Y.iCycles q) ≫ t)
                    (GradedObject.Monoidal.ι_tensorHom (𝟙 X.X) f.f p q (p + q) rfl).symm
            _ =
              (X.iCycles p ⊗ₘ Y.iCycles q) ≫ HomologicalComplex.ιTensorObj X Y p q (p + q) rfl ≫
                (HomologicalComplex.tensorHom (𝟙 X) f).f (p + q) := by
                  simp
    -- Fold the source tensor of cycle inclusions back into the cycles-level cross product.
    _ =
        chainComplexCycleCrossProduct (X := X) (Y := Y) (p := p) (q := q) ≫
          HomologicalComplex.cyclesMap (HomologicalComplex.tensorHom (𝟙 X) f) (p + q) ≫
          (HomologicalComplex.tensorObj X Y').iCycles (p + q) := by
          calc
            (X.iCycles p ⊗ₘ Y.iCycles q) ≫ HomologicalComplex.ιTensorObj X Y p q (p + q) rfl ≫
                (HomologicalComplex.tensorHom (𝟙 X) f).f (p + q) =
              (chainComplexCycleCrossProduct (X := X) (Y := Y) (p := p) (q := q) ≫
                (HomologicalComplex.tensorObj X Y).iCycles (p + q)) ≫
                  (HomologicalComplex.tensorHom (𝟙 X) f).f (p + q) := by
                    simpa [Category.assoc] using
                      congrArg
                        (fun t ↦ t ≫ (HomologicalComplex.tensorHom (𝟙 X) f).f (p + q))
                        ((chainComplexCycleCrossProduct_iCycles
                          (X := X) (Y := Y) (p := p) (q := q)).w)
            _ =
              chainComplexCycleCrossProduct (X := X) (Y := Y) (p := p) (q := q) ≫
                HomologicalComplex.cyclesMap (HomologicalComplex.tensorHom (𝟙 X) f) (p + q) ≫
                  (HomologicalComplex.tensorObj X Y').iCycles (p + q) := by
                    rw [Category.assoc, HomologicalComplex.cyclesMap_i]

/-- Helper for Theorem 17.2.2: after precomposing by the source homology projections, the
homology cross product is natural in the second chain complex. -/
private theorem chainComplexHomologyCrossProduct_natural_precomp
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) {Y Y' : ChainComplex (ModuleCat R) ℕ}
    (f : Y ⟶ Y') (p q : ℕ)
    [HomologicalComplex.HasHomology X p]
    [HomologicalComplex.HasHomology Y q]
    [HomologicalComplex.HasHomology Y' q]
    [HomologicalComplex.HasHomology (HomologicalComplex.tensorObj X Y) (p + q)]
    [HomologicalComplex.HasHomology (HomologicalComplex.tensorObj X Y') (p + q)] :
    ((X.homologyπ p ⊗ₘ Y.homologyπ q) ≫
        ((𝟙 (X.homology p)) ⊗ₘ HomologicalComplex.homologyMap f q) ≫
        chainComplexHomologyCrossProduct (X := X) (Y := Y') (p := p) (q := q)) =
    ((X.homologyπ p ⊗ₘ Y.homologyπ q) ≫
        chainComplexHomologyCrossProduct (X := X) (Y := Y) (p := p) (q := q) ≫
        HomologicalComplex.homologyMap (HomologicalComplex.tensorHom (𝟙 X) f) (p + q)) := by
  -- Rewrite the source tensor map using homology-quotient naturality on the `Y` factor.
  calc
    ((X.homologyπ p ⊗ₘ Y.homologyπ q) ≫
          ((𝟙 (X.homology p)) ⊗ₘ HomologicalComplex.homologyMap f q) ≫
          chainComplexHomologyCrossProduct (X := X) (Y := Y') (p := p) (q := q)) =
        (((𝟙 (X.cycles p)) ⊗ₘ HomologicalComplex.cyclesMap f q) ≫
          (X.homologyπ p ⊗ₘ Y'.homologyπ q) ≫
          chainComplexHomologyCrossProduct (X := X) (Y := Y') (p := p) (q := q)) := by
          -- Move the `homologyMap` across `Y.homologyπ q`, then reassociate the tensor factors.
          have hsource :
              (X.homologyπ p ⊗ₘ Y.homologyπ q) ≫
                  ((𝟙 (X.homology p)) ⊗ₘ HomologicalComplex.homologyMap f q) =
                ((𝟙 (X.cycles p)) ⊗ₘ HomologicalComplex.cyclesMap f q) ≫
                  (X.homologyπ p ⊗ₘ Y'.homologyπ q) := by
            calc
              (X.homologyπ p ⊗ₘ Y.homologyπ q) ≫
                    ((𝟙 (X.homology p)) ⊗ₘ HomologicalComplex.homologyMap f q) =
                  (X.homologyπ p ≫ 𝟙 (X.homology p)) ⊗ₘ
                    (Y.homologyπ q ≫ HomologicalComplex.homologyMap f q) := by
                      rw [tensorHom_comp_tensorHom]
              _ =
                  (X.homologyπ p ≫ 𝟙 (X.homology p)) ⊗ₘ
                    (HomologicalComplex.cyclesMap f q ≫ Y'.homologyπ q) := by
                      rw [HomologicalComplex.homologyπ_naturality]
              _ =
                  ((𝟙 (X.cycles p)) ⊗ₘ HomologicalComplex.cyclesMap f q) ≫
                    (X.homologyπ p ⊗ₘ Y'.homologyπ q) := by
                      simpa [Category.id_comp] using
                        (tensorHom_comp_tensorHom
                          (f₁ := 𝟙 (X.cycles p))
                          (f₂ := HomologicalComplex.cyclesMap f q)
                          (g₁ := X.homologyπ p)
                          (g₂ := Y'.homologyπ q)).symm
          simpa [Category.assoc] using
            congrArg
              (fun t ↦
                t ≫ chainComplexHomologyCrossProduct (X := X) (Y := Y') (p := p) (q := q))
              hsource
    -- Descend the right-hand cross product through the target homology quotient.
    _ =
        ((𝟙 (X.cycles p)) ⊗ₘ HomologicalComplex.cyclesMap f q) ≫
          chainComplexCycleCrossProduct (X := X) (Y := Y') (p := p) (q := q) ≫
          (HomologicalComplex.tensorObj X Y').homologyπ (p + q) := by
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ ((𝟙 (X.cycles p)) ⊗ₘ HomologicalComplex.cyclesMap f q) ≫ t)
              (chainComplexHomologyCrossProduct_spec (X := X) (Y := Y') (p := p) (q := q)).w
    -- Replace the cycles-level square by the already-proved naturality statement.
    _ =
        chainComplexCycleCrossProduct (X := X) (Y := Y) (p := p) (q := q) ≫
          HomologicalComplex.cyclesMap (HomologicalComplex.tensorHom (𝟙 X) f) (p + q) ≫
          (HomologicalComplex.tensorObj X Y').homologyπ (p + q) := by
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ t ≫ (HomologicalComplex.tensorObj X Y').homologyπ (p + q))
              (chainComplexCycleCrossProduct_natural R X f p q)
    -- Push the target cycles map across the target homology projection.
    _ =
        chainComplexCycleCrossProduct (X := X) (Y := Y) (p := p) (q := q) ≫
          (HomologicalComplex.tensorObj X Y).homologyπ (p + q) ≫
          HomologicalComplex.homologyMap (HomologicalComplex.tensorHom (𝟙 X) f) (p + q) := by
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ chainComplexCycleCrossProduct (X := X) (Y := Y) (p := p) (q := q) ≫ t)
              (HomologicalComplex.homologyπ_naturality
                (φ := HomologicalComplex.tensorHom (𝟙 X) f) (i := p + q)).symm
    -- Finally rewrite the source cross product back to the homology-level owner for `(X, Y)`.
    _ =
        (X.homologyπ p ⊗ₘ Y.homologyπ q) ≫
          chainComplexHomologyCrossProduct (X := X) (Y := Y) (p := p) (q := q) ≫
          HomologicalComplex.homologyMap (HomologicalComplex.tensorHom (𝟙 X) f) (p + q) := by
          simpa [Category.assoc] using
            congrArg
              (fun t ↦
                t ≫ HomologicalComplex.homologyMap (HomologicalComplex.tensorHom (𝟙 X) f) (p + q))
              (chainComplexHomologyCrossProduct_spec (X := X) (Y := Y) (p := p) (q := q)).w.symm

/-- Helper for Theorem 17.2.2: homology maps commute with the degree-transport `eqToHom`
isomorphisms coming from an index equality. -/
private theorem homologyMap_eqToHom_degreeShift
    (R : Type u) [CommRing R]
    {K L : ChainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) {i j : ℕ} (h : i = j) :
    HomologicalComplex.homologyMap φ i ≫
        eqToHom (congrArg (fun n ↦ L.homology n) h) =
      eqToHom (congrArg (fun n ↦ K.homology n) h) ≫
        HomologicalComplex.homologyMap φ j := by
  -- Reduce the degree transport to the reflexive case so both sides are definitionally equal.
  cases h
  simp

/-- Helper for Theorem 17.2.2: each antidiagonal summand of the left edge is natural in the
second chain complex. -/
private theorem kunnethTensorSummandToHomology_natural
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    {Y Y' : ChainComplex (ModuleCat R) ℕ} (f : Y ⟶ Y')
    (pq : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal (n + 1)}) :
    ((𝟙 (X.homology pq.1.1)) ⊗ₘ HomologicalComplex.homologyMap f pq.1.2) ≫
        kunnethTensorSummandToHomology R X Y' n pq =
      kunnethTensorSummandToHomology R X Y n pq ≫
        kunnethHomologyMap R X n f := by
  -- Evaluate the antidiagonal index once so the total degree is literally `n + 1`.
  rcases pq with ⟨⟨p, q⟩, hpq⟩
  rw [Finset.mem_antidiagonal] at hpq
  -- Compare the two maps on representatives coming from the surjective source quotient map.
  apply ModuleCat.hom_ext
  ext z
  have hXsurj : Function.Surjective (X.homologyπ p).hom := by
    exact (ModuleCat.epi_iff_surjective (X.homologyπ p)).mp inferInstance
  have hYsurj : Function.Surjective (Y.homologyπ q).hom := by
    exact (ModuleCat.epi_iff_surjective (Y.homologyπ q)).mp inferInstance
  have hsurj : Function.Surjective ((X.homologyπ p ⊗ₘ Y.homologyπ q).hom) := by
    simpa using TensorProduct.map_surjective (g := (X.homologyπ p).hom) hXsurj
      (g' := (Y.homologyπ q).hom) hYsurj
  obtain ⟨w, rfl⟩ := hsurj z
  -- Now the source quotient maps are visible, so the precomposed naturality square applies.
  have hcomp :
      (X.homologyπ p ⊗ₘ Y.homologyπ q) ≫
          (((𝟙 (X.homology p)) ⊗ₘ HomologicalComplex.homologyMap f q) ≫
            kunnethTensorSummandToHomology R X Y' n ⟨⟨p, q⟩, by simpa [hpq]⟩) =
        (X.homologyπ p ⊗ₘ Y.homologyπ q) ≫
          (kunnethTensorSummandToHomology R X Y n ⟨⟨p, q⟩, by simpa [hpq]⟩ ≫
            kunnethHomologyMap R X n f) := by
    calc
      (X.homologyπ p ⊗ₘ Y.homologyπ q) ≫
            (((𝟙 (X.homology p)) ⊗ₘ HomologicalComplex.homologyMap f q) ≫
              kunnethTensorSummandToHomology R X Y' n ⟨⟨p, q⟩, by simpa [hpq]⟩) =
          ((X.homologyπ p ⊗ₘ Y.homologyπ q) ≫
            ((𝟙 (X.homology p)) ⊗ₘ HomologicalComplex.homologyMap f q) ≫
              chainComplexHomologyCrossProduct (X := X) (Y := Y') (p := p) (q := q)) ≫
                eqToHom
                  (congrArg
                    (fun m ↦ (HomologicalComplex.tensorObj X Y').homology m) hpq) := by
            simp [kunnethTensorSummandToHomology, hpq, Category.assoc]
      -- Replace the precomposed left edge by the proved homology-level naturality square.
      _ =
          ((X.homologyπ p ⊗ₘ Y.homologyπ q) ≫
            chainComplexHomologyCrossProduct (X := X) (Y := Y) (p := p) (q := q) ≫
              HomologicalComplex.homologyMap (HomologicalComplex.tensorHom (𝟙 X) f) (p + q)) ≫
                eqToHom
                  (congrArg
                    (fun m ↦ (HomologicalComplex.tensorObj X Y').homology m) hpq) := by
            simpa [Category.assoc] using
              congrArg
                (fun t ↦
                  t ≫
                    eqToHom
                      (congrArg
                        (fun m ↦ (HomologicalComplex.tensorObj X Y').homology m) hpq))
                (chainComplexHomologyCrossProduct_natural_precomp R X f p q)
      -- Then move the target degree cast across `homologyMap`.
      _ =
          ((X.homologyπ p ⊗ₘ Y.homologyπ q) ≫
            chainComplexHomologyCrossProduct (X := X) (Y := Y) (p := p) (q := q) ≫
              eqToHom
                (congrArg (fun m ↦ (HomologicalComplex.tensorObj X Y).homology m) hpq)) ≫
                  HomologicalComplex.homologyMap (HomologicalComplex.tensorHom (𝟙 X) f) (n + 1) := by
            rw [← Category.assoc]
            exact congrArg
              (fun t ↦
                ((X.homologyπ p ⊗ₘ Y.homologyπ q) ≫
                  chainComplexHomologyCrossProduct (X := X) (Y := Y) (p := p) (q := q)) ≫ t)
              (homologyMap_eqToHom_degreeShift R
                (φ := HomologicalComplex.tensorHom (𝟙 X) f) hpq)
      -- Fold the `(p, q)` representative back to the public Kunneth summand map.
      _ =
          (X.homologyπ p ⊗ₘ Y.homologyπ q) ≫
            (kunnethTensorSummandToHomology R X Y n ⟨⟨p, q⟩, by simpa [hpq]⟩ ≫
              kunnethHomologyMap R X n f) := by
            simp [kunnethTensorSummandToHomology, kunnethHomologyMap, hpq, Category.assoc]
  exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hcomp) w

/-- Helper for Theorem 17.2.2: the transported fixed-`Y` row on the public Kunneth surface,
with left edge `fixedYKunnethTensorToHomology R X Y n`. -/
private noncomputable def fixedYKunnethTransportedRow
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X Y : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i)) :
    ComposableArrows (ModuleCat R) 3 := by
  -- Route correction: reverse the dependency direction and keep the public right edge as the
  -- primitive object, so the concrete quotient-model owner below becomes a thin adapter.
  refine ComposableArrows.mk₃
    (0 : kunnethTensorTerm R X Y n ⟶ kunnethTensorTerm R X Y n)
    (fixedYKunnethTensorToHomology R X Y n)
    (?_ : kunnethHomologyTerm R X Y n ⟶ kunnethTorTerm R X Y n)
  -- TODO: transport the fixed-`Y` Chapter 12 homology row once to
  -- `0 ⟶ kunnethTensorTerm ⟶ kunnethHomologyTerm ⟶ kunnethTorTerm` and take its last map here.
  sorry

/-- Helper for Theorem 17.2.2: the fixed-`Y` right edge on public homology is the last map of the
transported Kunneth row. -/
private noncomputable def fixedYKunnethHomologyToTor
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X Y : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i)) :
    kunnethHomologyTerm R X Y n ⟶ kunnethTorTerm R X Y n :=
  -- Read off the public right edge directly from the transported row.
  (fixedYKunnethTransportedRow R X Y n hX).map' 2 3

/-- Helper for Theorem 17.2.2: the concrete fixed-`Y` owner of the right edge is obtained by
precomposing the public right edge with the concrete quotient projection from `K`. -/
private noncomputable def fixedYKunnethCyclesToTor
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X Y : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i)) :
    ((HomologicalComplex.tensorObj X Y).sc (n + 1)).moduleCatLeftHomologyData.K ⟶
      kunnethTorTerm R X Y n :=
  -- Keep the concrete quotient-model owner secondary to the public right edge.
  ((HomologicalComplex.tensorObj X Y).sc (n + 1)).moduleCatLeftHomologyData.π ≫
    ((HomologicalComplex.tensorObj X Y).sc (n + 1)).moduleCatHomologyIso.inv ≫
      fixedYKunnethHomologyToTor R X Y n hX

/-- Helper for Theorem 17.2.2: the concrete fixed-`Y` owner kills target boundaries because the
quotient map `π` already kills them before the public right edge is applied. -/
private theorem fixedYKunnethCyclesToTor_descZero
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X Y : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i)) :
    ((HomologicalComplex.tensorObj X Y).sc (n + 1)).moduleCatLeftHomologyData.f' ≫
        fixedYKunnethCyclesToTor R X Y n hX = 0 := by
  -- The adapter starts with the quotient projection `π`, so the concrete boundary map vanishes
  -- before the transported public right edge is even used.
  calc
    ((HomologicalComplex.tensorObj X Y).sc (n + 1)).moduleCatLeftHomologyData.f' ≫
          fixedYKunnethCyclesToTor R X Y n hX =
        (((HomologicalComplex.tensorObj X Y).sc (n + 1)).moduleCatLeftHomologyData.f' ≫
            ((HomologicalComplex.tensorObj X Y).sc (n + 1)).moduleCatLeftHomologyData.π) ≫
          ((HomologicalComplex.tensorObj X Y).sc (n + 1)).moduleCatHomologyIso.inv ≫
            fixedYKunnethHomologyToTor R X Y n hX := by
          simp [fixedYKunnethCyclesToTor, Category.assoc]
    _ =
        0 ≫ ((HomologicalComplex.tensorObj X Y).sc (n + 1)).moduleCatHomologyIso.inv ≫
          fixedYKunnethHomologyToTor R X Y n hX := by
          rw [CategoryTheory.ShortComplex.LeftHomologyData.f'_π]
    _ = 0 := by
          rw [CategoryTheory.Limits.zero_comp]

/-- Helper for Theorem 17.2.2: precomposing the descended right edge with the tensor-product
homology quotient recovers the concrete target-side owner. -/
private theorem fixedYKunnethHomologyToTor_spec
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X Y : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i)) :
    (HomologicalComplex.tensorObj X Y).homologyπ (n + 1) ≫
        fixedYKunnethHomologyToTor R X Y n hX =
      ((HomologicalComplex.tensorObj X Y).sc (n + 1)).moduleCatCyclesIso.hom ≫
        fixedYKunnethCyclesToTor R X Y n hX := by
  -- Insert the concrete cycles comparison isomorphism once, then rewrite the quotient map to the
  -- explicit `K ⟶ H` presentation used by the adapter.
  have hinsert :
      ((HomologicalComplex.tensorObj X Y).sc (n + 1)).moduleCatCyclesIso.hom ≫
          (((HomologicalComplex.tensorObj X Y).sc (n + 1)).moduleCatCyclesIso.inv ≫
            (HomologicalComplex.tensorObj X Y).homologyπ (n + 1)) ≫
            fixedYKunnethHomologyToTor R X Y n hX =
        (HomologicalComplex.tensorObj X Y).homologyπ (n + 1) ≫
          fixedYKunnethHomologyToTor R X Y n hX := by
    calc
      ((HomologicalComplex.tensorObj X Y).sc (n + 1)).moduleCatCyclesIso.hom ≫
            (((HomologicalComplex.tensorObj X Y).sc (n + 1)).moduleCatCyclesIso.inv ≫
              (HomologicalComplex.tensorObj X Y).homologyπ (n + 1)) ≫
              fixedYKunnethHomologyToTor R X Y n hX =
          ((((HomologicalComplex.tensorObj X Y).sc (n + 1)).moduleCatCyclesIso.hom ≫
              ((HomologicalComplex.tensorObj X Y).sc (n + 1)).moduleCatCyclesIso.inv) ≫
                (HomologicalComplex.tensorObj X Y).homologyπ (n + 1)) ≫
                  fixedYKunnethHomologyToTor R X Y n hX := by
            simp [Category.assoc]
      _ =
          (HomologicalComplex.tensorObj X Y).homologyπ (n + 1) ≫
            fixedYKunnethHomologyToTor R X Y n hX := by
            rw [Iso.hom_inv_id, Category.id_comp]
            rfl
  have hπ :
      ((HomologicalComplex.tensorObj X Y).sc (n + 1)).moduleCatCyclesIso.inv ≫
          (HomologicalComplex.tensorObj X Y).homologyπ (n + 1) =
        ((HomologicalComplex.tensorObj X Y).sc (n + 1)).moduleCatLeftHomologyData.π ≫
          ((HomologicalComplex.tensorObj X Y).sc (n + 1)).moduleCatHomologyIso.inv := by
    simpa using
      (CategoryTheory.ShortComplex.moduleCatCyclesIso_inv_π
        (S := (HomologicalComplex.tensorObj X Y).sc (n + 1)))
  calc
    (HomologicalComplex.tensorObj X Y).homologyπ (n + 1) ≫
          fixedYKunnethHomologyToTor R X Y n hX =
        ((HomologicalComplex.tensorObj X Y).sc (n + 1)).moduleCatCyclesIso.hom ≫
          (((HomologicalComplex.tensorObj X Y).sc (n + 1)).moduleCatCyclesIso.inv ≫
            (HomologicalComplex.tensorObj X Y).homologyπ (n + 1)) ≫
              fixedYKunnethHomologyToTor R X Y n hX := by
          exact hinsert.symm
    _ =
        ((HomologicalComplex.tensorObj X Y).sc (n + 1)).moduleCatCyclesIso.hom ≫
          fixedYKunnethCyclesToTor R X Y n hX := by
          simpa [fixedYKunnethCyclesToTor, Category.assoc] using
            congrArg
              (fun t ↦
                ((HomologicalComplex.tensorObj X Y).sc (n + 1)).moduleCatCyclesIso.hom ≫
                  t ≫ fixedYKunnethHomologyToTor R X Y n hX)
              hπ

/-- Helper for Theorem 17.2.2: the transported fixed-`Y` row packages the public zero relation
and short exactness of the Kunneth row at once. -/
private theorem fixedYKunnethTransportedRowShortExactData
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X Y : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i)) :
    ∃ zero :
        fixedYKunnethTensorToHomology R X Y n ≫ fixedYKunnethHomologyToTor R X Y n hX = 0,
      (ShortComplex.mk
          (fixedYKunnethTensorToHomology R X Y n)
          (fixedYKunnethHomologyToTor R X Y n hX)
          zero).ShortExact := by
  -- Route correction: keep the transported fixed-`Y` exact-row argument in one theorem-local
  -- owner and let the public wrappers below simply project from it.
  -- TODO: transport the Chapter 12 fixed-`Y` row once, prove the endpoints are zero, and then
  -- read off the zero relation and short exactness on the public Kunneth surface.
  sorry

/-- Helper for Theorem 17.2.2: the public fixed-`Y` short exact row should be packaged only once,
so the visible zero relation and short exactness are thin wrappers. -/
private theorem fixedYKunnethRightEdgeShortExactData
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X Y : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i)) :
    ∃ zero :
        fixedYKunnethTensorToHomology R X Y n ≫ fixedYKunnethHomologyToTor R X Y n hX = 0,
      (ShortComplex.mk
          (fixedYKunnethTensorToHomology R X Y n)
          (fixedYKunnethHomologyToTor R X Y n hX)
          zero).ShortExact := by
  -- Reuse the single transported-row package instead of reopening the fixed-`Y` exactness proof.
  exact fixedYKunnethTransportedRowShortExactData R X Y n hX

/-- Helper for Theorem 17.2.2: the transported public right edge is natural in the second chain
complex. -/
private theorem fixedYKunnethTransportedRow_natural
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i))
    {Y Y' : ChainComplex (ModuleCat R) ℕ} (f : Y ⟶ Y') :
    kunnethHomologyMap R X n f ≫ fixedYKunnethHomologyToTor R X Y' n hX =
      fixedYKunnethHomologyToTor R X Y n hX ≫ kunnethTorMap R X n f := by
  -- Route correction: prove the right-hand naturality square on the transported public row, then
  -- derive any concrete-owner square only by precomposing with the quotient projection.
  -- TODO: build the morphism between the transported fixed-`Y` rows and project its last square.
  sorry

/-- Helper for Theorem 17.2.2: the fixed-`Y` right edge annihilates the summed cross-product map.
-/
private theorem fixedYKunnethHomologyToTor_zero
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X Y : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i)) :
    fixedYKunnethTensorToHomology R X Y n ≫ fixedYKunnethHomologyToTor R X Y n hX = 0 :=
  -- Read off the visible zero relation from the single packaged fixed-`Y` short exact row.
  Classical.choose (fixedYKunnethRightEdgeShortExactData R X Y n hX)

/-- Helper for Theorem 17.2.2: the fixed-`Y` Kunneth short complex is short exact. -/
private theorem fixedYKunnethHomologySequence_shortExact
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X Y : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i)) :
    (ShortComplex.mk
        (fixedYKunnethTensorToHomology R X Y n)
        (fixedYKunnethHomologyToTor R X Y n hX)
        (fixedYKunnethHomologyToTor_zero R X Y n hX)).ShortExact := by
  -- Reuse the single packaged fixed-`Y` short exact row instead of reconstructing it here.
  simpa [fixedYKunnethHomologyToTor_zero] using
    (Classical.choose_spec (fixedYKunnethRightEdgeShortExactData R X Y n hX))

/-- Helper for Theorem 17.2.2: the concrete fixed-`Y` owner is natural in the second chain
complex after precomposing with the target cycles quotient. -/
private theorem fixedYKunnethCyclesToTor_natural
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i))
    {Y Y' : ChainComplex (ModuleCat R) ℕ} (f : Y ⟶ Y') :
    HomologicalComplex.cyclesMap (HomologicalComplex.tensorHom (𝟙 X) f) (n + 1) ≫
        ((HomologicalComplex.tensorObj X Y').sc (n + 1)).moduleCatCyclesIso.hom ≫
        fixedYKunnethCyclesToTor R X Y' n hX =
      ((HomologicalComplex.tensorObj X Y).sc (n + 1)).moduleCatCyclesIso.hom ≫
        fixedYKunnethCyclesToTor R X Y n hX ≫
        kunnethTorMap R X n f := by
  -- Route correction: after the public right-edge square is available, this concrete-owner square
  -- should be recovered formally by precomposing with the target quotient projection.
  calc
    HomologicalComplex.cyclesMap (HomologicalComplex.tensorHom (𝟙 X) f) (n + 1) ≫
          ((HomologicalComplex.tensorObj X Y').sc (n + 1)).moduleCatCyclesIso.hom ≫
          fixedYKunnethCyclesToTor R X Y' n hX =
        HomologicalComplex.cyclesMap (HomologicalComplex.tensorHom (𝟙 X) f) (n + 1) ≫
          (HomologicalComplex.tensorObj X Y').homologyπ (n + 1) ≫
          fixedYKunnethHomologyToTor R X Y' n hX := by
          -- Rewrite the concrete target-side owner back to the public right edge.
          simpa [Category.assoc] using
            congrArg
              (fun t ↦
                HomologicalComplex.cyclesMap (HomologicalComplex.tensorHom (𝟙 X) f) (n + 1) ≫ t)
              (fixedYKunnethHomologyToTor_spec R X Y' n hX).symm
    _ =
        (HomologicalComplex.tensorObj X Y).homologyπ (n + 1) ≫
          kunnethHomologyMap R X n f ≫
          fixedYKunnethHomologyToTor R X Y' n hX := by
          -- Move the homology quotient across the induced tensor-product map.
          simpa [kunnethHomologyMap, Category.assoc] using
            congrArg
              (fun t ↦ t ≫ fixedYKunnethHomologyToTor R X Y' n hX)
              ((HomologicalComplex.homologyπ_naturality
                (φ := HomologicalComplex.tensorHom (𝟙 X) f)
                (i := n + 1)).symm)
    _ =
        (HomologicalComplex.tensorObj X Y).homologyπ (n + 1) ≫
          fixedYKunnethHomologyToTor R X Y n hX ≫
          kunnethTorMap R X n f := by
          -- Then apply the already isolated public naturality square on homology.
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ (HomologicalComplex.tensorObj X Y).homologyπ (n + 1) ≫ t)
              (fixedYKunnethTransportedRow_natural R X n hX f)
    _ =
        ((HomologicalComplex.tensorObj X Y).sc (n + 1)).moduleCatCyclesIso.hom ≫
          fixedYKunnethCyclesToTor R X Y n hX ≫
          kunnethTorMap R X n f := by
          -- Finally rewrite the public right edge back to the concrete quotient-model owner.
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ t ≫ kunnethTorMap R X n f)
              (fixedYKunnethHomologyToTor_spec R X Y n hX)

/-- Helper for Theorem 17.2.2: package the fixed-`Y` maps into the public Kunneth sequence. -/
private noncomputable def fixedYKunnethHomologySequence
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X Y : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i)) :
    KunnethHomologySequence R X Y n :=
  { tensorToHomology := fixedYKunnethTensorToHomology R X Y n
    homologyToTor := fixedYKunnethHomologyToTor R X Y n hX
    zero := fixedYKunnethHomologyToTor_zero R X Y n hX
    shortExact := fixedYKunnethHomologySequence_shortExact R X Y n hX }

/-- Helper for Theorem 17.2.2: the left Kunneth map is natural in the second chain complex. -/
private theorem fixedYKunnethTensorToHomology_natural
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    {Y Y' : ChainComplex (ModuleCat R) ℕ} (f : Y ⟶ Y') :
    kunnethTensorMap R X n f ≫ fixedYKunnethTensorToHomology R X Y' n =
      fixedYKunnethTensorToHomology R X Y n ≫ kunnethHomologyMap R X n f := by
  -- Route correction: instead of normalizing the whole dependent `Pi` map globally, compare the
  -- two linear maps on single-supported antidiagonal inputs.
  exact ModuleCat.hom_ext_iff.mpr <|
    LinearMap.pi_ext fun pq x => by
      -- First rewrite the source tensor map on the single-supported tuple.
      have hmap :
          ModuleCat.Hom.hom (kunnethTensorMap R X n f) (Pi.single pq x) =
            ((Pi.single pq
              (ModuleCat.Hom.hom
                ((𝟙 (X.homology pq.1.1)) ⊗ₘ HomologicalComplex.homologyMap f pq.1.2) x)) :
              ∀ pq : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal (n + 1)},
                (X.homology pq.1.1 ⊗ Y'.homology pq.1.2 : ModuleCat R)) := by
        -- Evaluate the dependent `piMap` coordinatewise on a single-supported tuple.
        ext pq'
        by_cases hpq' : pq' = pq
        · subst hpq'
          simp [kunnethTensorMap]
        · simp [kunnethTensorMap, hpq']
      -- Then compare both sides through the visible `(p, q)` summand square.
      calc
        ModuleCat.Hom.hom
            (kunnethTensorMap R X n f ≫ fixedYKunnethTensorToHomology R X Y' n)
            (Pi.single pq x) =
          ModuleCat.Hom.hom
            (fixedYKunnethTensorToHomology R X Y' n)
            (Pi.single pq
              (ModuleCat.Hom.hom
                ((𝟙 (X.homology pq.1.1)) ⊗ₘ HomologicalComplex.homologyMap f pq.1.2) x)) := by
              change
                ModuleCat.Hom.hom (fixedYKunnethTensorToHomology R X Y' n)
                  (ModuleCat.Hom.hom (kunnethTensorMap R X n f) (Pi.single pq x)) = _
              rw [hmap]
        _ =
          ModuleCat.Hom.hom (kunnethTensorSummandToHomology R X Y' n pq)
            (ModuleCat.Hom.hom
              ((𝟙 (X.homology pq.1.1)) ⊗ₘ HomologicalComplex.homologyMap f pq.1.2) x) := by
              rw [fixedYKunnethTensorToHomology_apply_single]
        _ =
          ModuleCat.Hom.hom (kunnethHomologyMap R X n f)
            (ModuleCat.Hom.hom (kunnethTensorSummandToHomology R X Y n pq) x) := by
              exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp
                (kunnethTensorSummandToHomology_natural R X n f pq)) x
        _ =
          ModuleCat.Hom.hom (kunnethHomologyMap R X n f)
            (ModuleCat.Hom.hom (fixedYKunnethTensorToHomology R X Y n) (Pi.single pq x)) := by
              rw [fixedYKunnethTensorToHomology_apply_single]
        _ =
          ModuleCat.Hom.hom
            (fixedYKunnethTensorToHomology R X Y n ≫ kunnethHomologyMap R X n f)
            (Pi.single pq x) := by
              rfl

/-- Helper for Theorem 17.2.2: the fixed-`Y` right edge is natural in the second chain complex. -/
private theorem fixedYKunnethHomologyToTor_natural
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i))
    {Y Y' : ChainComplex (ModuleCat R) ℕ} (f : Y ⟶ Y') :
    kunnethHomologyMap R X n f ≫ fixedYKunnethHomologyToTor R X Y' n hX =
      fixedYKunnethHomologyToTor R X Y n hX ≫ kunnethTorMap R X n f := by
  -- The public naturality square is exactly the transported-row naturality theorem.
  exact fixedYKunnethTransportedRow_natural R X n hX f

/-- Theorem 17.2.2. Over a PID `R`, if the chain complex `X` consists of flat `R`-modules, then
for each `n` there exists a `KunnethHomologyNaturality R X n`, i.e. a short exact sequence
natural in `Y`,
`0 ⟶ ⨁_(i + j = n + 1) H_i(X) ⊗ H_j(Y) ⟶ H_(n + 1)(X ⊗ Y) ⟶
    ⨁_(i + j = n) Tor(H_i(X), H_j(Y)) ⟶ 0`.
This is the nat-indexed form of the textbook sequence
`0 ⟶ ⨁_(i + j = m) H_i(X) ⊗ H_j(Y) ⟶ H_m(X ⊗ Y) ⟶
    ⨁_(i + j = m - 1) Tor(H_i(X), H_j(Y)) ⟶ 0`. -/
theorem kunnethHomologyShortExact
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i)) :
    Nonempty (KunnethHomologyNaturality R X n) := by
  -- Route correction: the theorem body only assembles the fixed-`Y` short exact sequence and
  -- the two naturality squares. The unresolved tensor-filtration work is isolated above.
  refine nonempty_kunnethHomologyNaturality_of_data
    (fun Y ↦ fixedYKunnethHomologySequence R X Y n hX)
    ?_ ?_
  · intro Y Y' f
    exact fixedYKunnethTensorToHomology_natural R X n f
  · intro Y Y' f
    exact fixedYKunnethHomologyToTor_natural R X n hX f
