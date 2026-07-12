import LinearRepresentations_Serre_1977.Chap09.Exercise_9_9_1_3.SymmetricExteriorProduct

open scoped Representation

noncomputable section

universe u v w

namespace Representation

/- The Adams operators themselves only use the monoid power map, so the power-series layer is
kept at that generality. -/
section

variable {G : Type u} [Group G]
variable {A : Type v} [CommSemiring A] [Algebra ℚ A]

def weightedPsiGeneratingSeries (w : ℕ → ℚ) (f : G → A) : PowerSeries (G → A) :=
  PowerSeries.mk fun
    | 0 => 0
    | m + 1 => algebraMap ℚ A (w m) • Ψ^m.succPNat(f)

/-- The logarithmic series `∑_{k ≥ 1} Ψ^k(f) T^k / k` attached to an `A`-valued function `f`.
It specializes below to character-valued series. -/
def psiGeneratingSeries (f : G → A) : PowerSeries (G → A) :=
  weightedPsiGeneratingSeries (fun m ↦ (m + 1 : ℚ)⁻¹) f

/-- The alternating logarithmic series
`∑_{k ≥ 1} (-1)^{k-1} Ψ^k(f) T^k / k` attached to an `A`-valued function `f`.
It specializes below to character-valued series. -/
def alternatingPsiGeneratingSeries (f : G → A) : PowerSeries (G → A) :=
  weightedPsiGeneratingSeries (fun m ↦ ((-1 : ℚ) ^ m) * (m + 1 : ℚ)⁻¹) f

@[simp] theorem coeff_psiGeneratingSeries_zero (f : G → A) :
    PowerSeries.coeff 0 (psiGeneratingSeries f) = 0 := by
  simp [psiGeneratingSeries, weightedPsiGeneratingSeries]

@[simp] theorem coeff_psiGeneratingSeries_succ (f : G → A) (m : ℕ) :
    PowerSeries.coeff (m + 1) (psiGeneratingSeries f) =
      algebraMap ℚ A ((m + 1 : ℚ)⁻¹) • Ψ^m.succPNat(f) := by
  simp [psiGeneratingSeries, weightedPsiGeneratingSeries]

@[simp] theorem coeff_alternatingPsiGeneratingSeries_zero (f : G → A) :
    PowerSeries.coeff 0 (alternatingPsiGeneratingSeries f) = 0 := by
  simp [alternatingPsiGeneratingSeries, weightedPsiGeneratingSeries]

@[simp] theorem coeff_alternatingPsiGeneratingSeries_succ (f : G → A) (m : ℕ) :
    PowerSeries.coeff (m + 1) (alternatingPsiGeneratingSeries f) =
      algebraMap ℚ A (((-1 : ℚ) ^ m) * (m + 1 : ℚ)⁻¹) • Ψ^m.succPNat(f) := by
  simp [alternatingPsiGeneratingSeries, weightedPsiGeneratingSeries]
end

end Representation
