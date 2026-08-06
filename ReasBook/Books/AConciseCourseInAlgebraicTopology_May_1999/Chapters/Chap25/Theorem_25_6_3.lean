import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Theorem_25_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_6_1

open CategoryTheory
open scoped Topology Topology.Homotopy

universe u v

noncomputable section

-- Semantic recall: `lean_leansearch` only surfaced generic homotopy-group owners, not the local
-- Chapter 25 bridge from the Thom prespectrum `TO` to its associated omega-spectrum `MO`. Repo
-- inspection shows that `Theorem_25_2_3` supplies the cobordism computation for `TO`, while
-- `Definition_25_6_1` provides the source-faithful owner `MO` for the associated spectrum.

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
variable (bInf : ∀ q, BO q)
variable
  (structureMap :
    ∀ q : ℕ,
      reducedSuspension (TOPointedCompactlyGenerated BO γ bInf q) ⟶
        TOPointedCompactlyGenerated BO γ bInf (q + 1))
variable (model : OmegaSpectrumModel (TO_prespectrum BO γ bInf structureMap))

/-- Transporting a chosen Thom-spectrum comparison for `TO` across the canonical stable-homotopy
group isomorphism `TO ⟶ MO` yields the corresponding comparison for `MO`. -/
def unorientedCobordismGroup_mulEquiv_stableHomotopyGroup_MO_of_TO
    (n : ℕ)
    (eTO :
      Prespectrum.stableHomotopyGroup (TO_prespectrum BO γ bInf structureMap) (n : ℤ) ≃*
        Multiplicative (N_(n))) :
    Prespectrum.stableHomotopyGroup (MO (TO_prespectrum BO γ bInf structureMap) model) (n : ℤ) ≃*
      Multiplicative (N_(n)) :=
  (CategoryTheory.Iso.groupIsoToMulEquiv
      ((moStableHomotopyGroupIso (TO_prespectrum BO γ bInf structureMap) model (n : ℤ)).symm)).trans
    eTO

/-- Theorem 25.6.3. If `MO` is the spectrum associated to the Thom prespectrum `TO`, then the
degree-`n` stable homotopy group of `MO` computes the unoriented cobordism group `N_n`. Here
`TO` is the Thom prespectrum built from the Thom spaces of the universal real `q`-plane bundles,
and `MO` is a chosen omega-spectrum replacement of that prespectrum. -/
theorem unorientedCobordismGroup_mulEquiv_stableHomotopyGroup_MO
    (n : ℕ) :
    Nonempty
      (Prespectrum.stableHomotopyGroup
          (MO (TO_prespectrum BO γ bInf structureMap) model) (n : ℤ) ≃*
        Multiplicative (N_(n))) := by
  rcases unorientedCobordismGroup_mulEquiv_stableHomotopyGroup_TO
      BO γ n bInf structureMap with ⟨eTO⟩
  exact ⟨unorientedCobordismGroup_mulEquiv_stableHomotopyGroup_MO_of_TO
    BO γ bInf structureMap model n eTO⟩

end
