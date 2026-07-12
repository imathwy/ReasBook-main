import StacksProject_2024.Chap10.Example_10_35_23.CoordinateRings

open Matrix MvPolynomial PrimeSpectrum

universe u

noncomputable section

section

variable (k : Type u) [Field k]

/-- Helper for Example 10.35.23: the ambient ideal cutting out the `Y = 0` stratum before
passing to the quotient coordinate ring. -/
def matrixProductAmbientYIdeal :
    Ideal (MvPolynomial (Fin 2 × Fin 2 × Fin 2) k) :=
  Ideal.span <| Set.range fun ij : Fin 2 × Fin 2 ↦
    (matrixProductPolynomialMatrix k 1) ij.1 ij.2

/-- Helper for Example 10.35.23: the ambient ideal cutting out the `X = 0` stratum before
passing to the quotient coordinate ring. -/
def matrixProductAmbientXIdeal :
    Ideal (MvPolynomial (Fin 2 × Fin 2 × Fin 2) k) :=
  Ideal.span <| Set.range fun ij : Fin 2 × Fin 2 ↦
    (matrixProductPolynomialMatrix k 0) ij.1 ij.2

/-- Helper for Example 10.35.23: the embedding of the `X`-coordinates into the ambient polynomial
ring of `(X, Y)`. -/
def matrixProductXVariableEmbedding :
    Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2 := fun ij ↦ (0, ij.1, ij.2)

/-- Helper for Example 10.35.23: the embedding of the `Y`-coordinates into the ambient polynomial
ring of `(X, Y)`. -/
def matrixProductYVariableEmbedding :
    Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2 := fun ij ↦ (1, ij.1, ij.2)

/-- Helper for Example 10.35.23: the `X`-coordinate embedding is injective. -/
theorem matrixProductXVariableEmbedding_injective :
    Function.Injective (matrixProductXVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2) :=
  by
    intro a b h
    simpa [matrixProductXVariableEmbedding] using h

/-- Helper for Example 10.35.23: the `Y`-coordinate embedding is injective. -/
theorem matrixProductYVariableEmbedding_injective :
    Function.Injective (matrixProductYVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2) :=
  by
    intro a b h
    simpa [matrixProductYVariableEmbedding] using h

/-- Helper for Example 10.35.23: keeping only the `X`-variables kills the `Y`-variables. -/
def matrixProductKeepX :
    MvPolynomial (Fin 2 × Fin 2 × Fin 2) k →ₐ[k] MvPolynomial (Fin 2 × Fin 2) k :=
  MvPolynomial.killCompl matrixProductXVariableEmbedding_injective

/-- Helper for Example 10.35.23: keeping only the `Y`-variables kills the `X`-variables. -/
def matrixProductKeepY :
    MvPolynomial (Fin 2 × Fin 2 × Fin 2) k →ₐ[k] MvPolynomial (Fin 2 × Fin 2) k :=
  MvPolynomial.killCompl matrixProductYVariableEmbedding_injective

/-- Helper for Example 10.35.23: the defining relations `XY = 0` already vanish modulo `Y = 0` in
the ambient polynomial ring. -/
theorem matrixProductCoordinateRingIdeal_le_ambientYIdeal :
    matrixProductCoordinateRingIdeal k ≤ matrixProductAmbientYIdeal k := by
  -- Each entry of `XY` is a sum of terms with a `Y`-coordinate factor.
  rw [matrixProductCoordinateRingIdeal, matrixProductAmbientYIdeal]
  refine Ideal.span_le.mpr ?_
  intro f hf
  rcases hf with ⟨⟨i, j⟩, rfl⟩
  simp only [matrixProductPolynomialMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  refine Ideal.add_mem _ ?_ ?_
  · exact Ideal.mul_mem_left _ _
      (Ideal.subset_span ⟨(0, j), by simp⟩)
  · exact Ideal.mul_mem_left _ _
      (Ideal.subset_span ⟨(1, j), by simp⟩)

/-- Helper for Example 10.35.23: the defining relations `XY = 0` already vanish modulo `X = 0` in
the ambient polynomial ring. -/
theorem matrixProductCoordinateRingIdeal_le_ambientXIdeal :
    matrixProductCoordinateRingIdeal k ≤ matrixProductAmbientXIdeal k := by
  -- Each entry of `XY` is a sum of terms with an `X`-coordinate factor.
  rw [matrixProductCoordinateRingIdeal, matrixProductAmbientXIdeal]
  refine Ideal.span_le.mpr ?_
  intro f hf
  rcases hf with ⟨⟨i, j⟩, rfl⟩
  simp only [matrixProductPolynomialMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  refine Ideal.add_mem _ ?_ ?_
  · exact Ideal.mul_mem_right _ _
      (Ideal.subset_span ⟨(i, 0), by simp⟩)
  · exact Ideal.mul_mem_right _ _
      (Ideal.subset_span ⟨(i, 1), by simp⟩)

/-- Helper for Example 10.35.23: if no `Y`-coordinate occurs in a monomial, then that monomial is
supported on the `X`-coordinate embedding. -/
theorem matrixProduct_support_subset_xEmbedding_of_no_y
    {m : (Fin 2 × Fin 2 × Fin 2) →₀ ℕ}
    (hm : ∀ ij : Fin 2 × Fin 2, m (1, ij.1, ij.2) = 0) :
    ↑m.support ⊆ Set.range (matrixProductXVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2) :=
  by
    intro a ha
    rcases a with ⟨s, i, j⟩
    fin_cases s
    · exact ⟨(i, j), by simp [matrixProductXVariableEmbedding]⟩
    · have hs : m (1, i, j) ≠ 0 := by
        simpa using Finsupp.mem_support_iff.mp ha
      exact False.elim (hs (hm (i, j)))

/-- Helper for Example 10.35.23: if no `X`-coordinate occurs in a monomial, then that monomial is
supported on the `Y`-coordinate embedding. -/
theorem matrixProduct_support_subset_yEmbedding_of_no_x
    {m : (Fin 2 × Fin 2 × Fin 2) →₀ ℕ}
    (hm : ∀ ij : Fin 2 × Fin 2, m (0, ij.1, ij.2) = 0) :
    ↑m.support ⊆ Set.range (matrixProductYVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2) :=
  by
    intro a ha
    rcases a with ⟨s, i, j⟩
    fin_cases s
    · have hs : m (0, i, j) ≠ 0 := by
        simpa using Finsupp.mem_support_iff.mp ha
      exact False.elim (hs (hm (i, j)))
    · exact ⟨(i, j), by simp [matrixProductYVariableEmbedding]⟩

/-- Helper for Example 10.35.23: killing the `Y`-variables has kernel exactly the ambient
`Y = 0` ideal. -/
theorem matrixProductKeepX_ker :
    RingHom.ker (matrixProductKeepX k) = matrixProductAmbientYIdeal k := by
  classical
  have hYrange :
      Set.range (fun ij : Fin 2 × Fin 2 ↦ (matrixProductPolynomialMatrix k 1) ij.1 ij.2) =
        MvPolynomial.X ''
          Set.range
            (matrixProductYVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2) := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨⟨i, j⟩, rfl⟩
      refine ⟨(1, i, j), ⟨(i, j), rfl⟩, ?_⟩
      simp [matrixProductPolynomialMatrix]
    · intro hz
      rcases hz with ⟨a, ⟨⟨i, j⟩, rfl⟩, rfl⟩
      exact ⟨(i, j), by simp [matrixProductPolynomialMatrix, matrixProductYVariableEmbedding]⟩
  apply le_antisymm
  · intro f hf
    -- Route correction: compute the kernel by support control, matching the source proof that
    -- every surviving monomial must involve a `Y`-variable.
    rw [RingHom.mem_ker] at hf
    rw [matrixProductAmbientYIdeal, hYrange, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hmY
    have hmYzero : ∀ ij : Fin 2 × Fin 2, m (1, ij.1, ij.2) = 0 := by
      intro ij
      by_contra hij
      exact hmY ⟨(1, ij.1, ij.2), ⟨ij, rfl⟩, hij⟩
    have hsupp :
        ↑m.support ⊆
          Set.range
            (matrixProductXVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2) :=
      matrixProduct_support_subset_xEmbedding_of_no_y hmYzero
    let mx : (Fin 2 × Fin 2) →₀ ℕ :=
      m.comapDomain
        (matrixProductXVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2)
        matrixProductXVariableEmbedding_injective.injOn
    have hcoeff_zero : (matrixProductKeepX k f).coeff mx = 0 := by
      simpa [hf, mx]
    have hmap :
        Finsupp.mapDomain
            (matrixProductXVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2) mx =
          m := by
      exact Finsupp.mapDomain_comapDomain
        (f := matrixProductXVariableEmbedding)
        matrixProductXVariableEmbedding_injective m hsupp
    have hcoeff :
        (matrixProductKeepX k f).coeff mx = f.coeff m := by
      -- Read the killed-complement coefficient back on the ambient monomial supported only on `X`.
      rw [matrixProductKeepX, MvPolynomial.coeff_killCompl, hmap]
    rw [hcoeff] at hcoeff_zero
    exact (Finsupp.mem_support_iff.mp hm) hcoeff_zero
  · intro f hf
    rw [matrixProductAmbientYIdeal] at hf
    -- Each `Y`-generator is killed by `matrixProductKeepX`, so the whole span lies in the kernel.
    exact (Ideal.span_le.mpr (by
      intro z hz
      rcases hz with ⟨⟨i, j⟩, rfl⟩
      change (matrixProductKeepX k) ((matrixProductPolynomialMatrix k 1) i j) = 0
      fin_cases i <;> fin_cases j <;>
        simp [matrixProductKeepX, matrixProductPolynomialMatrix, Matrix.mvPolynomialX_apply,
          MvPolynomial.rename_X, MvPolynomial.killCompl, matrixProductXVariableEmbedding]
    )) hf

/-- Helper for Example 10.35.23: killing the `X`-variables has kernel exactly the ambient
`X = 0` ideal. -/
theorem matrixProductKeepY_ker :
    RingHom.ker (matrixProductKeepY k) = matrixProductAmbientXIdeal k := by
  classical
  have hXrange :
      Set.range (fun ij : Fin 2 × Fin 2 ↦ (matrixProductPolynomialMatrix k 0) ij.1 ij.2) =
        MvPolynomial.X ''
          Set.range
            (matrixProductXVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2) := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨⟨i, j⟩, rfl⟩
      refine ⟨(0, i, j), ⟨(i, j), rfl⟩, ?_⟩
      simp [matrixProductPolynomialMatrix]
    · intro hz
      rcases hz with ⟨a, ⟨⟨i, j⟩, rfl⟩, rfl⟩
      exact ⟨(i, j), by simp [matrixProductPolynomialMatrix, matrixProductXVariableEmbedding]⟩
  apply le_antisymm
  · intro f hf
    -- Route correction: the symmetric kernel computation again follows the support criterion,
    -- now detecting monomials that must involve an `X`-variable.
    rw [RingHom.mem_ker] at hf
    rw [matrixProductAmbientXIdeal, hXrange, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hmX
    have hmXzero : ∀ ij : Fin 2 × Fin 2, m (0, ij.1, ij.2) = 0 := by
      intro ij
      by_contra hij
      exact hmX ⟨(0, ij.1, ij.2), ⟨ij, rfl⟩, hij⟩
    have hsupp :
        ↑m.support ⊆
          Set.range
            (matrixProductYVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2) :=
      matrixProduct_support_subset_yEmbedding_of_no_x hmXzero
    let my : (Fin 2 × Fin 2) →₀ ℕ :=
      m.comapDomain
        (matrixProductYVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2)
        matrixProductYVariableEmbedding_injective.injOn
    have hcoeff_zero : (matrixProductKeepY k f).coeff my = 0 := by
      simpa [hf, my]
    have hmap :
        Finsupp.mapDomain
            (matrixProductYVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2) my =
          m := by
      exact Finsupp.mapDomain_comapDomain
        (f := matrixProductYVariableEmbedding)
        matrixProductYVariableEmbedding_injective m hsupp
    have hcoeff :
        (matrixProductKeepY k f).coeff my = f.coeff m := by
      -- Read the killed-complement coefficient back on the ambient monomial supported only on `Y`.
      rw [matrixProductKeepY, MvPolynomial.coeff_killCompl, hmap]
    rw [hcoeff] at hcoeff_zero
    exact (Finsupp.mem_support_iff.mp hm) hcoeff_zero
  · intro f hf
    rw [matrixProductAmbientXIdeal] at hf
    -- Each `X`-generator is killed by `matrixProductKeepY`, so the whole span lies in the kernel.
    exact (Ideal.span_le.mpr (by
      intro z hz
      rcases hz with ⟨⟨i, j⟩, rfl⟩
      change (matrixProductKeepY k) ((matrixProductPolynomialMatrix k 0) i j) = 0
      fin_cases i <;> fin_cases j <;>
        simp [matrixProductKeepY, matrixProductPolynomialMatrix, Matrix.mvPolynomialX_apply,
          MvPolynomial.rename_X, MvPolynomial.killCompl, matrixProductYVariableEmbedding]
    )) hf

/-- Helper for Example 10.35.23: the ambient `Y = 0` ideal is prime because its quotient is a
polynomial ring in the `X`-coordinates. -/
theorem matrixProductAmbientYIdeal_isPrime :
    (matrixProductAmbientYIdeal k).IsPrime := by
  -- The `Y = 0` ambient ideal is exactly the kernel of the retraction to the `X`-polynomial ring.
  rw [← matrixProductKeepX_ker (k := k)]
  exact RingHom.ker_isPrime (matrixProductKeepX k)

/-- Helper for Example 10.35.23: the ambient `X = 0` ideal is prime because its quotient is a
polynomial ring in the `Y`-coordinates. -/
theorem matrixProductAmbientXIdeal_isPrime :
    (matrixProductAmbientXIdeal k).IsPrime := by
  -- The `X = 0` ambient ideal is exactly the kernel of the retraction to the `Y`-polynomial ring.
  rw [← matrixProductKeepY_ker (k := k)]
  exact RingHom.ker_isPrime (matrixProductKeepY k)

end
