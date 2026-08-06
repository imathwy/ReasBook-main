import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Theorem_11_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.HurewiczComparison

noncomputable section

open CategoryTheory
open scoped TopCat Topology Topology.Homotopy

-- Chapter 11 already owns the canonical computation `spherePiSelfMulEquivInt` on the
-- suspension-sphere model `suspensionSphere n = Σ^n S⁰`, while Chapter 9 uses the standard sphere
-- model `𝕊 n` with basepoint `sphereBasepoint n`. The public Chapter 9 statement is therefore a
-- source-facing consequence of a theorem-level bridge between these based sphere models.

/-- A based-space comparison from the Chapter 11 suspension sphere `Σ^n S⁰` to the
canonical Chapter 9 based sphere `basedSphere n` exists. -/
theorem suspensionSphereToBasedSphereIso_nonempty (n : ℕ+) :
    Nonempty ((suspensionSphere (n : ℕ)).toBasedSpace ≅ basedSphere (n : ℕ)) :=
  sorry

/-- Transporting the canonical Chapter 11 computation `spherePiSelfMulEquivInt n` across any
based-space comparison `i : (suspensionSphere n).toBasedSpace ≅ basedSphere n` yields the
canonical `basedSphere` form of `π_ n(S^n) ≃* Multiplicative ℤ`. -/
theorem basedSpherePiSelfMulEquivInt_ofComparison (n : ℕ+)
    (i : (suspensionSphere (n : ℕ)).toBasedSpace ≅ basedSphere (n : ℕ)) :
    Nonempty
      (π_ n (basedSphere (n : ℕ)).right (underTopBasepoint (basedSphere (n : ℕ))) ≃*
        Multiplicative ℤ) := by
  let h :
      (suspensionSphere (n : ℕ)).toCompactlyGenerated ≃ₜ (basedSphere (n : ℕ)).right :=
    TopCat.homeoOfIso ((Under.forget (⊤_ TopCat)).mapIso i)
  rcases spherePiSelfMulEquivInt n with ⟨e⟩
  let _ := h
  let _ := e
  sorry

/-- The canonical based sphere owner `basedSphere n` has infinite-cyclic `n`th homotopy group. -/
theorem basedSpherePiSelfMulEquivInt (n : ℕ+) :
    Nonempty
      (π_ n (basedSphere (n : ℕ)).right (underTopBasepoint (basedSphere (n : ℕ))) ≃*
        Multiplicative ℤ) := by
  rcases suspensionSphereToBasedSphereIso_nonempty n with ⟨i⟩
  exact basedSpherePiSelfMulEquivInt_ofComparison n i

/-- Theorem 9.4.11: for every positive `n`, the `n`th homotopy group `π_ n(S^n)` at the
standard sphere basepoint `sphereBasepoint n` is infinite cyclic. -/
theorem standardSpherePiSelfMulEquivInt (n : ℕ+) :
    Nonempty (π_ n (𝕊 n) (sphereBasepoint n) ≃* Multiplicative ℤ) := by
  simpa using basedSpherePiSelfMulEquivInt n

/-- The canonical based sphere owner `basedSphere n` has infinite `n`th homotopy group. -/
instance basedSpherePiSelf_infinite (n : ℕ+) :
    Infinite (π_ n (basedSphere (n : ℕ)).right (underTopBasepoint (basedSphere (n : ℕ)))) := by
  rcases basedSpherePiSelfMulEquivInt n with ⟨e⟩
  exact (e.toEquiv.infinite_iff).2 inferInstance

/-- The standard degree-`n` sphere homotopy group `π_ n(S^n)` at `sphereBasepoint n` is infinite. -/
instance standardSpherePiSelf_infinite (n : ℕ+) :
    Infinite (π_ n (𝕊 n) (sphereBasepoint n)) := by
  simpa using
    (basedSpherePiSelf_infinite n :
      Infinite (π_ n (basedSphere (n : ℕ)).right (underTopBasepoint (basedSphere (n : ℕ)))))
