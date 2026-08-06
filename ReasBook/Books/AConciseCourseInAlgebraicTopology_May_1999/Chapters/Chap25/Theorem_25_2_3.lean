import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Construction_25_3_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Theorem_25_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Theorem_25_5_2.PiStar

open CategoryTheory
open scoped Topology Topology.Homotopy

noncomputable section

universe u v

-- Semantic recall via `lean_leansearch`: `HomotopyGroup.Pi` is the canonical owner for the
-- unstable groups `π_k`, and repo inspection shows `TO_prespectrum` together with
-- `Prespectrum.stableHomotopyGroup` is the local stable owner for the Thom-space family `TO`.

section

variable (BO : ℕ → Type u)
variable [∀ q, TopologicalSpace (BO q)]
variable (γ : ∀ q, BO q → Type v)
variable [∀ q, TopologicalSpace (Bundle.TotalSpace (Fin q → ℝ) (γ q))]
variable [∀ q, (b : BO q) → TopologicalSpace (γ q b)]
variable [∀ q, FiberBundle (Fin q → ℝ) (γ q)]
variable [∀ q, (b : BO q) → AddCommGroup (γ q b)]
variable [∀ q, (b : BO q) → Module ℝ (γ q b)]
variable [∀ q, RealPlaneBundleClassifyingSpace q (BO q) (γ q)]
variable [TOStagewiseNormedBundle BO γ]

/-- Theorem 25.2.3 (1). Thom: after passing far enough out in the Thom-space family `TO q`, the
degree-`n` unoriented cobordism group `N_n` is isomorphic to the unstable homotopy group of the
stage `TO(q)` based at the common point at infinity. The phrase "for sufficiently large `q`" is
formalized as a tail `q = q₀ + r + 1`, so the homotopy-group degree is automatically positive. -/
theorem unorientedCobordismGroup_eventually_mulEquiv_homotopyGroup_TO
    (n : ℕ)
    (bInf : ∀ q, BO q) :
    ∃ q₀ : ℕ,
      ∀ r : ℕ,
        Nonempty
          (π_ (n + (q₀ + r + 1))
              (TO (q₀ + r + 1) (BO (q₀ + r + 1)) (γ (q₀ + r + 1)))
              (thomSpaceMk (q₀ + r + 1) (γ (q₀ + r + 1)) (bInf (q₀ + r + 1))
                (OnePoint.infty : OnePoint (γ (q₀ + r + 1) (bInf (q₀ + r + 1)))))
            ≃* Multiplicative (N_(n))) := sorry

/-- Theorem 25.2.3 (2). Thom: once the stagewise Thom spaces are assembled into a prespectrum
`TO`, the stable degree-`n` homotopy group of that Thom prespectrum is isomorphic to the
degree-`n` unoriented cobordism group `N_n`. -/
theorem unorientedCobordismGroup_mulEquiv_stableHomotopyGroup_TO
    (n : ℕ)
    (bInf : ∀ q, BO q)
    (structureMap :
      ∀ q : ℕ,
        reducedSuspension (TOPointedCompactlyGenerated BO γ bInf q) ⟶
          TOPointedCompactlyGenerated BO γ bInf (q + 1)) :
    Nonempty
      (Prespectrum.stableHomotopyGroup (TO_prespectrum BO γ bInf structureMap) (n : ℤ) ≃*
        Multiplicative (N_(n))) := sorry

/-- Theorem 25.2.3 (3).  The degreewise Thom comparisons assemble compatibly with products:
`N_*` and the nonnegative graded stable homotopy ring `π_*(TO)` are isomorphic as graded
`ZMod 2`-algebras.  Since the repository's ring owners on the two direct sums are not
definitionally the canonical direct-sum additive structures, the isomorphism is stated by an
explicit bijection preserving zero, addition, the unit, homogeneous products, and both directions
of the grading. -/
theorem unorientedCobordismAlgebraEquiv_stableHomotopy_TO
    (TO : RingPrespectrum.{u, v})
    (stableRing : StableHomotopyGradedRing TO)
    (NStar : ThomUnorientedCobordismPolynomialAlgebra) :
    ∃ e : TO.piStar → N_*,
      Function.Bijective e ∧
      e 0 = NStar.toCommRing.zero ∧
      (∀ x y, e (x + y) = NStar.toCommRing.add (e x) (e y)) ∧
      e (TO.piStarClass 0 stableRing.one) = NStar.toCommRing.one ∧
      (∀ (m n : ℕ)
          (x : Prespectrum.stableHomotopyGroup TO.toPrespectrum (m : ℤ))
          (y : Prespectrum.stableHomotopyGroup TO.toPrespectrum (n : ℤ)),
        e (TO.piStarClass (m + n) (stableRing.mul (m : ℤ) (n : ℤ) x y)) =
          NStar.toCommRing.mul
            (e (TO.piStarClass m x))
            (e (TO.piStarClass n y))) ∧
      (∀ (n : ℕ) (x : Prespectrum.stableHomotopyGroup TO.toPrespectrum (n : ℤ)),
        ∃ y : N_(n),
          e (TO.piStarClass n x) =
            DirectSum.lof ℤ ℕ (fun k ↦ N_(k)) n y) ∧
      ∀ (n : ℕ) (y : N_(n)),
        ∃ x : Prespectrum.stableHomotopyGroup TO.toPrespectrum (n : ℤ),
          e (TO.piStarClass n x) =
            DirectSum.lof ℤ ℕ (fun k ↦ N_(k)) n y := by
  sorry

end
