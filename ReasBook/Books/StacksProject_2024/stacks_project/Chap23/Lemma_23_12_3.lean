import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Homology.SpectralSequence.Basic
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.RingTheory.Derivation.Basic
import StacksProject_2024.stacks_project.Chap12.Definition_12_19_1
import StacksProject_2024.stacks_project.Chap12.Definition_12_20_2
import StacksProject_2024.stacks_project.Chap23.Lemma_23_6_8

-- Declarations for this item will be appended below by the statement pipeline.

universe uR uA uB uH uHT

open DifferentialGradedAlgebra
open CategoryTheory

/- Semantic search note: `lean_leansearch` did not surface a ready-made homological spectral
sequence owner for this bidegree convention. Local Chapter 12 precedent uses the generic owner
`CategoryTheory.SpectralSequence` together with `SpectralSequence.infinityPage`, so the degree-`2`
part below is stated via the canonical homological shape `ComplexShape.down' (r, 1 - r)` and an
explicit filtration on the abutment groups. -/

section

variable {R : Type uR} {A : Type uA} {B : Type uB}
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Helper for Lemma 23.12.3: the canonical owner for a bigraded homological spectral sequence
with differentials `d_r : E_r(i, j) ⟶ E_r(i - r, j + r - 1)`. -/
abbrev HomologicalBigradedSpectralSequence
    (C : Type _) [Category C] [Abelian C] (r₀ : ℤ) :=
  SpectralSequence C (fun r ↦ ComplexShape.down' (⟨r, 1 - r⟩ : ℤ × ℤ)) r₀

/-- Helper for Lemma 23.12.3: unfolding `HomologicalBigradedSpectralSequence` recovers the
generic spectral-sequence owner with homological bidegree shift `(r, 1 - r)`. -/
theorem homologicalBigradedSpectralSequence_def
    (C : Type _) [Category C] [Abelian C] (r₀ : ℤ) :
    HomologicalBigradedSpectralSequence C r₀ =
      SpectralSequence C (fun r ↦ ComplexShape.down' (⟨r, 1 - r⟩ : ℤ × ℤ)) r₀ :=
  rfl

/-- Helper for Lemma 23.12.3: a chosen degree-zero homology group of `(A, grading, d)` is
presented by a quotient map that kills boundaries, vanishes on positive degrees, is surjective on
degree `0`, and detects degree-zero boundaries exactly. -/
def IsDegreeZeroHomology
    (grading : ℕ → Submodule R A) (d : Derivation R A A)
    {H0 : Type _} [AddCommGroup H0] (q : A →+ H0) : Prop :=
  (∀ x : A, q (d x) = 0) ∧
    (∀ ⦃n : ℕ⦄ ⦃x : A⦄, 0 < n → x ∈ grading n → q x = 0) ∧
    (∀ z : H0, ∃ x : A, x ∈ grading 0 ∧ q x = z) ∧
    ∀ ⦃x : A⦄, x ∈ grading 0 → (q x = 0 ↔ ∃ y : A, y ∈ grading 1 ∧ d y = x)

/-- Helper for Lemma 23.12.3: the map `H₀(A) → H₀(A)` is multiplication by the closed degree-zero
class of `f` when it is induced by chain-level multiplication with `f` on degree-zero
representatives. -/
def IsMulByClosedDegreeZeroOnH0
    (grading : ℕ → Submodule R A)
    {H0 : Type _} [AddCommGroup H0]
    (q : A →+ H0) (f : A) (mulByF : H0 →+ H0) : Prop :=
  ∀ ⦃x : A⦄, x ∈ grading 0 → mulByF (q x) = q (f * x)

/-- Helper for Lemma 23.12.3: a map `H₀(A) → H₀(A⟨T⟩)` is the map induced by the base inclusion
`A → A⟨T⟩` when it agrees with `includeBase` on degree-zero representatives. -/
def InducesH0Map
    (gradingA : ℕ → Submodule R A)
    {H0A : Type _} {H0B : Type _} [AddCommGroup H0A] [AddCommGroup H0B]
    (includeBase : A →ₐ[R] B) (qA : A →+ H0A) (qB : B →+ H0B) (φ : H0A →+ H0B) : Prop :=
  ∀ ⦃x : A⦄, x ∈ gradingA 0 → φ (qA x) = qB (includeBase x)

/-- Helper for Lemma 23.12.3: closed homogeneous elements of degree `n` in `(A, grading, d)`. -/
abbrev HomologyCycles
    (grading : ℕ → Submodule R A) (d : Derivation R A A) (n : ℕ) :=
  {x : A // x ∈ grading n ∧ d x = 0}

/-- Helper for Lemma 23.12.3: a chosen family `H_n(A)` indexed by `ℤ` presents the actual
homology of `(A, grading, d)` when the negative groups are trivial and the nonnegative groups are
realized by class maps from cycles modulo boundaries. -/
def IsHomologyGroupFamily
    (grading : ℕ → Submodule R A) (d : Derivation R A A)
    (H : ℤ → Type _) [∀ n : ℤ, AddCommGroup (H n)]
    (classOf : ∀ n : ℕ, HomologyCycles grading d n → H n) : Prop :=
  (∀ n : ℤ, n < 0 → Subsingleton (H n)) ∧
    (∀ n : ℕ, Function.Surjective (classOf n)) ∧
    ∀ n : ℕ, ∀ x y : HomologyCycles grading d n,
      classOf n x = classOf n y ↔
        ∃ z : A, z ∈ grading (n + 1) ∧ d z = y.1 - x.1

/-- Helper for Lemma 23.12.3: the degree-`+1` maps on homology induced by multiplication with the
closed degree-one element `f`. -/
abbrev AdjoinVariableDegreeTwoHomologyMap
    (HA : ℤ → Type uH) [∀ n : ℤ, AddCommGroup (HA n)] :=
  ∀ n : ℤ, HA n →+ HA (n + 1)

/-- Helper for Lemma 23.12.3: the codomain of the degree-`j - i - 1` homology map is the same as
`H_{j - i}(A)`, via the tautological equality `(j - (i + 1)) + 1 = j - i`. -/
def adjoinVariableDegreeTwoPageOneTargetIso
    {HA : ℤ → Type uH} [∀ n : ℤ, AddCommGroup (HA n)]
    (i : ℕ) (j : ℤ) :
    AddCommGrpCat.of (HA (j - (i + 1) + 1)) ≅ AddCommGrpCat.of (HA (j - i)) := by
  have h : j - (i + 1 : ℤ) + 1 = j - i := by
    simp [sub_eq_add_neg, add_left_comm, add_comm]
  rw [h]

/-- Helper for Lemma 23.12.3: the chosen map `H_n(A) → H_{n + 1}(A)` is multiplication by the
degree-one homology class of `f` when it is represented on cycles by chain-level multiplication
with `f`. -/
def IsMulByClosedDegreeOneOnHomology
    (grading : ℕ → Submodule R A) (d : Derivation R A A)
    (HA : ℤ → Type uH) [∀ n : ℤ, AddCommGroup (HA n)]
    (classOf : ∀ n : ℕ, HomologyCycles grading d n → HA n)
    (f : A) (mulByF : AdjoinVariableDegreeTwoHomologyMap HA) : Prop :=
  ∀ n : ℕ, ∀ x : HomologyCycles grading d n,
    ∃ y : HomologyCycles grading d (n + 1),
      y.1 = f * x.1 ∧ mulByF n (classOf n x) = classOf (n + 1) y

/-- Helper for Lemma 23.12.3: `S` has the `E₁`-page description from part (2), and under those
identifications the `d₁` differential is induced by multiplication by `f`. -/
def HasAdjoinVariableDegreeTwoPageOne
    (S : HomologicalBigradedSpectralSequence AddCommGrpCat.{uH} 1)
    (HA : ℤ → Type uH) [∀ n : ℤ, AddCommGroup (HA n)]
    (mulByF : AdjoinVariableDegreeTwoHomologyMap HA) : Prop :=
  ∃ pageOneIso : ∀ i : ℕ, ∀ j : ℤ, (S.page 1).X (i, j) ≅ AddCommGrpCat.of (HA (j - i)),
    ∀ i : ℕ, ∀ j : ℤ,
      (S.page 1).d (i + 1, j) (i, j) =
        (pageOneIso (i + 1) j).hom ≫
          AddCommGrpCat.ofHom (mulByF (j - (i + 1))) ≫
          (adjoinVariableDegreeTwoPageOneTargetIso i j).hom ≫
          (pageOneIso i j).inv

/-- Helper for Lemma 23.12.3: for each total degree `n`, the `E_∞`-page of `S` is isomorphic to
the graded pieces of a chosen decreasing filtration on `H_n(A⟨T⟩)`. -/
def HasAdjoinVariableDegreeTwoInfinityPageIdentifications
    (S : HomologicalBigradedSpectralSequence AddCommGrpCat.{uH} 1)
    (HAT : ℤ → Type uH) [∀ n : ℤ, AddCommGroup (HAT n)] (n : ℤ)
    (F : DecreasingFiltration (AddCommGrpCat.of (HAT n))) : Prop :=
  ∃ infinityPageIso : ∀ i : ℕ, S.infinityPage (i, n - i) ≅ F.gradedPiece i,
    let _ := infinityPageIso
    True

/-- Helper for Lemma 23.12.3: for each total degree `n`, the `E_∞`-page of `S` is identified
with the graded pieces of some decreasing filtration on `H_n(A⟨T⟩)`. -/
def HasAdjoinVariableDegreeTwoInfinityPageFiltration
    (S : HomologicalBigradedSpectralSequence AddCommGrpCat.{uH} 1)
    (HAT : ℤ → Type uH) [∀ n : ℤ, AddCommGroup (HAT n)] :=
  ∀ n : ℤ,
    ∃ F : DecreasingFiltration (AddCommGrpCat.of (HAT n)),
      HasAdjoinVariableDegreeTwoInfinityPageIdentifications S HAT n F

/-- Helper for Lemma 23.12.3: `S` is a bounded degree-`2` homological spectral sequence with the
`E₁`-page, `d₁`, and `E_∞`-filtration behavior described in part (2). -/
structure IsAdjoinVariableDegreeTwoSpectralSequence
    (S : HomologicalBigradedSpectralSequence AddCommGrpCat.{uH} 1)
    (HA : ℤ → Type uH) (HAT : ℤ → Type uH)
    [∀ n : ℤ, AddCommGroup (HA n)] [∀ n : ℤ, AddCommGroup (HAT n)]
    (mulByF : AdjoinVariableDegreeTwoHomologyMap HA) : Prop where
  pageOne : HasAdjoinVariableDegreeTwoPageOne S HA mulByF
  finiteSupport (n : ℤ) :
    Set.Finite { i : ℕ | ¬ CategoryTheory.Limits.IsZero ((S.page 1).X (i, n - i)) }
  infinityPageFiltration : HasAdjoinVariableDegreeTwoInfinityPageFiltration S HAT

/-- Helper for Lemma 23.12.3: from the `E₁`-page specification one can extract the chosen
identifications with the shifted homology groups and the induced `d₁` formula. -/
theorem HasAdjoinVariableDegreeTwoPageOne.exists_pageOneIso
    (S : HomologicalBigradedSpectralSequence AddCommGrpCat.{uH} 1)
    (HA : ℤ → Type uH) [∀ n : ℤ, AddCommGroup (HA n)]
    (mulByF : AdjoinVariableDegreeTwoHomologyMap HA)
    (hS : HasAdjoinVariableDegreeTwoPageOne S HA mulByF) :
    ∃ pageOneIso : ∀ i : ℕ, ∀ j : ℤ, (S.page 1).X (i, j) ≅ AddCommGrpCat.of (HA (j - i)),
      ∀ i : ℕ, ∀ j : ℤ,
        (S.page 1).d (i + 1, j) (i, j) =
          (pageOneIso (i + 1) j).hom ≫
            AddCommGrpCat.ofHom (mulByF (j - (i + 1))) ≫
            (adjoinVariableDegreeTwoPageOneTargetIso i j).hom ≫
            (pageOneIso i j).inv := by
  exact hS

/-- Helper for Lemma 23.12.3: the boundedness clause of the degree-`2` spectral-sequence
conclusion says only finitely many `E₁(i, n - i)` are nonzero in each total degree `n`. -/
theorem IsAdjoinVariableDegreeTwoSpectralSequence.finiteSupportOfTotalDegree
    (S : HomologicalBigradedSpectralSequence AddCommGrpCat.{uH} 1)
    (HA : ℤ → Type uH) (HAT : ℤ → Type uH)
    [∀ n : ℤ, AddCommGroup (HA n)] [∀ n : ℤ, AddCommGroup (HAT n)]
    (mulByF : AdjoinVariableDegreeTwoHomologyMap HA)
    (hS : IsAdjoinVariableDegreeTwoSpectralSequence S HA HAT mulByF) (n : ℤ) :
    Set.Finite { i : ℕ | ¬ CategoryTheory.Limits.IsZero ((S.page 1).X (i, n - i)) } := by
  exact hS.finiteSupport n

/-- Helper for Lemma 23.12.3: for each total degree `n`, the `E_∞`-page clause supplies a
filtration on `H_n(A⟨T⟩)` whose graded pieces realize the corresponding `E_∞`-terms. -/
theorem IsAdjoinVariableDegreeTwoSpectralSequence.infinityPageFiltrationAt
    (S : HomologicalBigradedSpectralSequence AddCommGrpCat.{uH} 1)
    (HA : ℤ → Type uH) (HAT : ℤ → Type uH)
    [∀ n : ℤ, AddCommGroup (HA n)] [∀ n : ℤ, AddCommGroup (HAT n)]
    (mulByF : AdjoinVariableDegreeTwoHomologyMap HA)
    (hS : IsAdjoinVariableDegreeTwoSpectralSequence S HA HAT mulByF) (n : ℤ) :
    ∃ F : DecreasingFiltration (AddCommGrpCat.of (HAT n)),
      HasAdjoinVariableDegreeTwoInfinityPageIdentifications S HAT n F := by
  exact hS.infinityPageFiltration n

/-- Helper for Lemma 23.12.3: once a filtration on `H_n(A⟨T⟩)` is chosen, the `E_∞`-page clause
supplies the corresponding family of identifications `E_∞(i, n - i) ≅ gr^i(F)`. -/
theorem HasAdjoinVariableDegreeTwoInfinityPageIdentifications.exists_infinityPageIso
    (S : HomologicalBigradedSpectralSequence AddCommGrpCat.{uH} 1)
    (HAT : ℤ → Type uH) [∀ n : ℤ, AddCommGroup (HAT n)] (n : ℤ)
    (F : DecreasingFiltration (AddCommGrpCat.of (HAT n)))
    (hF : HasAdjoinVariableDegreeTwoInfinityPageIdentifications S HAT n F) :
    ∃ infinityPageIso : ∀ i : ℕ, S.infinityPage (i, n - i) ≅ F.gradedPiece i,
      let _ := infinityPageIso
      True := by
  exact hF

/-- Lemma 23.12.3 (1): if the adjoined variable has degree `1`, then the tail
`H₀(A) --f→ H₀(A) → H₀(A⟨T⟩) → 0` of the long exact homology sequence is realized on any chosen
degree-zero homology presentations of `(A, d)` and `(A⟨T⟩, D)`, with the displayed maps induced by
multiplication by `f` and the inclusion `A → A⟨T⟩`. -/
@[stacks 0GZ6]
theorem exists_h0_exactTail_of_adjoinVariableDegree_one
    (gradingA : ℕ → Submodule R A) (gradingB : ℕ → Submodule R B)
    (dA : Derivation R A A) (gammaA : ℕ → A → A) (gammaB : ℕ → B → B)
    (includeBase : A →ₐ[R] B) (variableT : B)
    (hincludeBase_mem :
      ∀ ⦃n : ℕ⦄ ⦃x : A⦄, x ∈ gradingA n → includeBase x ∈ gradingB n)
    (hvariable_mem : variableT ∈ gradingB 1)
    (hvariable_sq : variableT * variableT = 0)
    (hgrading :
      ∀ m : ℕ, gradingB m ≃ₗ[R] (gradingA m × gradingA (m - 1)))
    [CompatibleDividedPowers gradingA dA gammaA]
    (f : A) (hf : f ∈ gradingA 0) (hdf : dA f = 0)
    (D : Derivation R B B)
    (hD : IsAdjoinVariableDifferential gradingB dA gammaB includeBase variableT f D)
    {H0A : Type uH} {H0AT : Type uHT}
    [AddCommGroup H0A] [AddCommGroup H0AT]
    (qA : A →+ H0A) (hqA : IsDegreeZeroHomology gradingA dA qA)
    (qAT : B →+ H0AT) (hqAT : IsDegreeZeroHomology gradingB D qAT)
    (mulByF : H0A →+ H0A) (hmulByF : IsMulByClosedDegreeZeroOnH0 gradingA qA f mulByF) :
    ∃ q : H0A →+ H0AT,
      InducesH0Map gradingA includeBase qA qAT q ∧
        Function.Exact mulByF q ∧ Function.Surjective q := sorry

/-- Lemma 23.12.3 (2): if the adjoined variable has degree `2`, then there is a bounded
homological spectral sequence with `E₁(i, j) = H_{j - i}(A) · T^[i]`, with `d₁` induced by
multiplication by `f`, and converging to `H_{i + j}(A⟨T⟩)`. The chosen homology groups and
multiplication-by-`f` maps are required to come from actual cycle representatives for `(A, d)` and
`(A⟨T⟩, D)`. -/
@[stacks 0GZ6]
theorem exists_homologicalSpectralSequence_of_adjoinVariableDegree_two
    (gradingA : ℕ → Submodule R A) (gradingB : ℕ → Submodule R B)
    (dA : Derivation R A A) (gammaA : ℕ → A → A) (gammaB : ℕ → B → B)
    (includeBase : A →ₐ[R] B) (variableT : B)
    (hincludeBase_mem :
      ∀ ⦃n : ℕ⦄ ⦃x : A⦄, x ∈ gradingA n → includeBase x ∈ gradingB n)
    (hvariable_mem : variableT ∈ gradingB 2)
    (tDividedPower : ℕ → B)
    (htDividedPower_zero : tDividedPower 0 = 1)
    (htDividedPower_one : tDividedPower 1 = variableT)
    (htDividedPower_mem : ∀ i : ℕ, tDividedPower i ∈ gradingB (2 * i))
    (hgrading :
      ∀ m : ℕ, gradingB m ≃ₗ[R] (Π₀ i : ℕ, gradingA (m - 2 * i)))
    [CompatibleDividedPowers gradingA dA gammaA]
    (f : A) (hf : f ∈ gradingA 1) (hdf : dA f = 0)
    (D : Derivation R B B)
    (hD : IsAdjoinVariableDifferential gradingB dA gammaB includeBase variableT f D)
    (HA : ℤ → Type uH) (HAT : ℤ → Type uH)
    [∀ n : ℤ, AddCommGroup (HA n)] [∀ n : ℤ, AddCommGroup (HAT n)]
    (classOfA : ∀ n : ℕ, HomologyCycles gradingA dA n → HA n)
    (hHA : IsHomologyGroupFamily gradingA dA HA classOfA)
    (classOfAT : ∀ n : ℕ, HomologyCycles gradingB D n → HAT n)
    (hHAT : IsHomologyGroupFamily gradingB D HAT classOfAT)
    (mulByF : AdjoinVariableDegreeTwoHomologyMap HA)
    (hmulByF : IsMulByClosedDegreeOneOnHomology gradingA dA HA classOfA f mulByF) :
    ∃ S : HomologicalBigradedSpectralSequence AddCommGrpCat.{uH} 1,
      IsAdjoinVariableDegreeTwoSpectralSequence S HA HAT mulByF := sorry

end
