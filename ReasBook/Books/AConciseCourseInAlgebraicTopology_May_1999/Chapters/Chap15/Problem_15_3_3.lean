import Mathlib.Algebra.Category.ModuleCat.AB
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.IntegralSingularHomology
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.IntegralReducedHomology
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Definition_14_4_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Construction_14_1_3

open CategoryTheory Limits

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)

/-- Any two Chapter 13 integral pair-homology theories induce isomorphic reduced homology modules
on a based space. -/
theorem integralReducedHomology_iso
    (H K : PairHomologyTheory ℤ) (k : ℕ) (X : BasedSpace) :
    Nonempty (integralReducedHomology H k X ≅ integralReducedHomology K k X) :=
  sorry

/-- A based space `X` is a Moore space for the abelian group `π` in degree `n` when `X.right` is
a connected CW complex whose reduced integral homology, computed by some Chapter 13 integral
pair-homology theory, is `π` in degree `n` and zero in every other natural degree. -/
class IsMooreSpace
    (π : Type) [AddCommGroup π] (n : ℕ) (X : BasedSpace) : Prop
    extends ConnectedSpace X.right where
  /-- A Moore-space witness has CW-complex underlying space. -/
  hasCWComplexUnderlyingSpace : IsBasedCWComplex X
  /-- Some integral pair-homology theory realizes the Moore-space reduced-homology pattern. -/
  integralReducedHomologyExists :
    ∃ H : PairHomologyTheory ℤ,
      Nonempty (integralReducedHomology H n X ≅ ModuleCat.of ℤ π) ∧
        ∀ k : ℕ, k ≠ n → IsZero (integralReducedHomology H k X)

/-- `IsMooreSpace π n X` is exactly the reduced-integral-homology formulation of the Moore-space
condition for a based connected CW complex. -/
theorem isMooreSpace_iff
    {π : Type} [AddCommGroup π] {n : ℕ} {X : BasedSpace} :
    IsMooreSpace π n X ↔
      ConnectedSpace X.right ∧
        IsBasedCWComplex X ∧
          ∃ H : PairHomologyTheory ℤ,
            Nonempty (integralReducedHomology H n X ≅ ModuleCat.of ℤ π) ∧
              ∀ k : ℕ, k ≠ n → IsZero (integralReducedHomology H k X) :=
  sorry

namespace IsMooreSpace

/-- The defining data of a Moore space consist of connectedness, a CW-complex structure, and a
reduced-homology pattern for some integral pair-homology theory. -/
theorem spec {π : Type} [AddCommGroup π] {n : ℕ} {X : BasedSpace}
    (hX : IsMooreSpace π n X) :
    ConnectedSpace X.right ∧
      IsBasedCWComplex X ∧
        ∃ H : PairHomologyTheory ℤ,
          Nonempty (integralReducedHomology H n X ≅ ModuleCat.of ℤ π) ∧
            ∀ k : ℕ, k ≠ n → IsZero (integralReducedHomology H k X) :=
  isMooreSpace_iff.mp hX

/-- A Moore space carries the repository's canonical based-CW witness. -/
abbrev toBasedCWComplex {π : Type} [AddCommGroup π] {n : ℕ} {X : BasedSpace}
    (hX : IsMooreSpace π n X) : BasedCWComplex :=
  ⟨X, hX.hasCWComplexUnderlyingSpace⟩

/-- A Moore space has an underlying `TopCat.CWComplex` structure. -/
theorem cwComplex {π : Type} [AddCommGroup π] {n : ℕ} {X : BasedSpace}
    (hX : IsMooreSpace π n X) : Nonempty (TopCat.CWComplex X.right) :=
  hX.hasCWComplexUnderlyingSpace

/-- The reduced-homology characterization of a Moore space is independent of the integral
pair-homology theory used to compute it. -/
theorem degreeIntegralReducedHomologyIso
    {π : Type} [AddCommGroup π] {n : ℕ} {X : BasedSpace}
    (hX : IsMooreSpace π n X) (H : PairHomologyTheory ℤ) :
    Nonempty (integralReducedHomology H n X ≅ ModuleCat.of ℤ π) :=
  sorry

/-- Away from the defining degree, every integral pair-homology theory computes zero reduced
homology on a Moore space. -/
theorem otherIntegralReducedHomologyIsZero
    {π : Type} [AddCommGroup π] {n : ℕ} {X : BasedSpace}
    (hX : IsMooreSpace π n X) (H : PairHomologyTheory ℤ) (k : ℕ) (hk : k ≠ n) :
    IsZero (integralReducedHomology H k X) :=
  sorry

end IsMooreSpace

/-- For `n ≥ 1`, the reduced-homology definition of a Moore space is equivalent to the ordinary
integral singular-homology formulation with `H₀(X) ≅ ℤ`, `Hₙ(X) ≅ π`, and all other homology
groups zero. -/
theorem isMooreSpace_iff_integralSingularHomology
    {π : Type} [AddCommGroup π] {n : ℕ} (hn : 1 ≤ n) {X : BasedSpace} :
    IsMooreSpace π n X ↔
      ConnectedSpace X.right ∧
        IsBasedCWComplex X ∧
          Nonempty (integralSingularHomology 0 X.right ≅ ModuleCat.of ℤ ℤ) ∧
          Nonempty (integralSingularHomology n X.right ≅ ModuleCat.of ℤ π) ∧
            ∀ k : ℕ, k ≠ 0 → k ≠ n → IsZero (integralSingularHomology k X.right) :=
  sorry

/-- A Moore space `M(π, n)` is a based space equipped with the defining Moore-space property. -/
structure MooreSpace (π : Type) [AddCommGroup π] (n : ℕ) where
  /-- The underlying based space. -/
  toBasedSpace : BasedSpace
  /-- The defining Moore-space property of the underlying based space. -/
  isMooreSpace : IsMooreSpace π n toBasedSpace

instance {π : Type} [AddCommGroup π] {n : ℕ} : CoeOut (MooreSpace π n) BasedSpace where
  coe X := X.toBasedSpace

namespace MooreSpace

instance {π : Type} [AddCommGroup π] {n : ℕ} (X : MooreSpace π n) :
    IsMooreSpace π n (X : BasedSpace) :=
  X.isMooreSpace

instance {π : Type} [AddCommGroup π] {n : ℕ} (X : MooreSpace π n) :
    ConnectedSpace X.toBasedSpace.right :=
  X.isMooreSpace.toConnectedSpace

/-- A bundled Moore space exposes the source-facing reduced-homology and CW-complex conditions. -/
theorem spec {π : Type} [AddCommGroup π] {n : ℕ} (X : MooreSpace π n) :
    ConnectedSpace X.toBasedSpace.right ∧
      IsBasedCWComplex X.toBasedSpace ∧
        ∃ H : PairHomologyTheory ℤ,
          Nonempty (integralReducedHomology H n X.toBasedSpace ≅ ModuleCat.of ℤ π) ∧
            ∀ k : ℕ, k ≠ n → IsZero (integralReducedHomology H k X.toBasedSpace) :=
  IsMooreSpace.spec X.isMooreSpace

/-- A bundled Moore space determines an object of the repository's based-CW-complex category. -/
abbrev toBasedCWComplex {π : Type} [AddCommGroup π] {n : ℕ} (X : MooreSpace π n) :
    BasedCWComplex :=
  X.isMooreSpace.toBasedCWComplex

/-- A bundled Moore space satisfies the reduced-homology formulation for any integral
pair-homology theory. -/
theorem spec_integralReducedHomology
    {π : Type} [AddCommGroup π] {n : ℕ} (H : PairHomologyTheory ℤ) (X : MooreSpace π n) :
    ConnectedSpace X.toBasedSpace.right ∧
      IsBasedCWComplex X.toBasedSpace ∧
        Nonempty (integralReducedHomology H n X.toBasedSpace ≅ ModuleCat.of ℤ π) ∧
          ∀ k : ℕ, k ≠ n → IsZero (integralReducedHomology H k X.toBasedSpace) :=
  ⟨X.isMooreSpace.toConnectedSpace, X.isMooreSpace.hasCWComplexUnderlyingSpace,
    IsMooreSpace.degreeIntegralReducedHomologyIso X.isMooreSpace H,
    IsMooreSpace.otherIntegralReducedHomologyIsZero X.isMooreSpace H⟩

/-- In positive degree, a bundled Moore space also satisfies the ordinary singular-homology
formulation of the Moore-space condition. -/
theorem spec_integralSingularHomology
    {π : Type} [AddCommGroup π] {n : ℕ} (hn : 1 ≤ n) (X : MooreSpace π n) :
    ConnectedSpace X.toBasedSpace.right ∧
      IsBasedCWComplex X.toBasedSpace ∧
        Nonempty
          (integralSingularHomology 0 X.toBasedSpace.right ≅ ModuleCat.of ℤ ℤ) ∧
        Nonempty (integralSingularHomology n X.toBasedSpace.right ≅ ModuleCat.of ℤ π) ∧
          ∀ k : ℕ, k ≠ 0 → k ≠ n →
            IsZero (integralSingularHomology k X.toBasedSpace.right) :=
  (isMooreSpace_iff_integralSingularHomology hn).mp X.isMooreSpace

/-- A bundled Moore space carries a CW-complex structure on its underlying space. -/
theorem cwComplex {π : Type} [AddCommGroup π] {n : ℕ} (X : MooreSpace π n) :
    Nonempty (TopCat.CWComplex X.toBasedSpace.right) :=
  X.isMooreSpace.cwComplex

end MooreSpace

/-- Problem 15.3.3. For an abelian group `π` and `n ≥ 1`, there exists a Moore space `M(π, n)`,
that is, a based connected CW complex whose reduced integral homology is `π` in degree `n` and
zero in every other natural degree. By
`isMooreSpace_iff_integralSingularHomology`, this is equivalently the positive-degree ordinary
integral singular-homology formulation with `H₀ ≅ ℤ`. -/
theorem existsMooreSpace
    (π : Type) [AddCommGroup π] (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (MooreSpace π n) :=
  sorry
