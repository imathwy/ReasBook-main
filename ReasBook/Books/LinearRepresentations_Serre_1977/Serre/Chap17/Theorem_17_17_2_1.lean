import Mathlib
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_2_1.GammaElementarySurjective
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_2_1.ProjectiveGammaElementarySurjective
import LinearRepresentations_Serre_1977.Chap17.Corollary_17_17_2_2.ElementarySubgroupInduction

open scoped Representation

noncomputable section

universe u

namespace Representation

section

variable {G : Type u} [Group G] [Finite G]

/-
Theorem 17-17.2-1 (Serre's Theorem 39), faithful DVR form.

The original statements (quantified over an ARBITRARY field `k` with no relation to `K`) are FALSE:
for `G = S₃`, `k = 𝔽₂`, `K = ⊤`, the inductions from `Γ_⊤ = ⊥`-elementary subgroups span an
index-2 subgroup of `R₀[𝔽₂](S₃) ≅ ℤ²` that misses the unit class.  The faithful statement is the
modular DVR one (the `(K, A, k)` `p`-modular system): `A` a discrete valuation ring,
`↥K = Frac A` a characteristic-zero intermediate field of a cyclotomic extension `L ⊇ ℚ` realizing
the exponent of `G`, and `k = IsLocalRing.ResidueField A`.  In that setting `k` automatically
contains enough prime-to-`p` roots of unity, which is exactly what makes the theorem true.

The proofs descend Serre's Theorem 27 (Brauer induction over the character ring `R[↥K]`) through the
decomposition homomorphism `d`, using `d(1) = 1`, `d ∘ Ind = Ind ∘ d` (the induced-lattice/reduction
bridge `hind`), and the projection formula; see
`Serre/Chap17/Theorem_17_17_2_1/GammaElementarySurjective.lean` (R₀) and
`.../ProjectiveGammaElementarySurjective.lean` (P₀).
-/

local instance
    (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) :
    DecidableEq { H : Subgroup G // Subgroup.IsGammaElementary ΓK H } :=
  Classical.decEq _

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {L : Type u} [Field L] [NumberField L] [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
variable (K : IntermediateField ℚ L) [Algebra A ↥K] [IsFractionRing A ↥K]

local instance instDecEqGammaElem_t1721 :
    DecidableEq { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H } :=
  Classical.decEq _
local instance instDecNeR0_t1721 (i : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H })
    (x : R₀[IsLocalRing.ResidueField A](i.1)) : Decidable (x ≠ 0) := Classical.dec _
local instance instDecNeP0_t1721 (i : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H })
    (x : P₀[IsLocalRing.ResidueField A](i.1)) : Decidable (x ≠ 0) := Classical.dec _

section

open scoped FiniteRepGrothendieckInduction

/-- Theorem 17-17.2-1 (1), DVR form: with `Γ_K = Γ[K](G)` attached to the intermediate field
`K ⊆ L` of a cyclotomic realization of the exponent of `G`, and `k = ResidueField A` the residue
field of the DVR `A` with `Frac A = ↥K`, every class `x ∈ R₀[k](G)` is a finite sum of inductions
from `Γ_K`-elementary subgroups, with coefficients in `R₀[k](H)`. -/
theorem gammaElementarySubgroupFiniteRepGrothendieckInduction_surjective
    (x : R₀[IsLocalRing.ResidueField A](G)) :
    ∃ (ι : Type u) (_ : Fintype ι) (H : ι → Subgroup G)
      (hH : ∀ i, Subgroup.IsGammaElementary (Γ[K](G)) (H i)),
        ∃ y : ∀ i, R₀[IsLocalRing.ResidueField A](H i),
          x = ∑ i, (Ind[H i]) (y i) := by
  classical
  obtain ⟨z'', hz''⟩ := gammaElementary_finiteRepGrothendieck_surjective K x
  refine ⟨{ H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H }, inferInstance,
    fun H => H.1, fun H => H.2, fun H => z'' H, ?_⟩
  rw [hz'', DFinsupp.sum, Finset.sum_subset (Finset.subset_univ _)]
  intro H _ hH
  have hz : z'' H = 0 := by by_contra h; exact hH (DFinsupp.mem_support_iff.mpr h)
  rw [hz, map_zero]

end

section

open scoped FiniteProjectiveGrothendieckInduction

/-- Theorem 17-17.2-1 (2), DVR form: the projective analog, for `x ∈ P₀[k](G)`. -/
theorem gammaElementarySubgroupFiniteProjectiveRepGrothendieckInduction_surjective
    (x : P₀[IsLocalRing.ResidueField A](G)) :
    ∃ (ι : Type u) (_ : Fintype ι) (H : ι → Subgroup G)
      (hH : ∀ i, Subgroup.IsGammaElementary (Γ[K](G)) (H i)),
        ∃ y : ∀ i, P₀[IsLocalRing.ResidueField A](H i),
          x = ∑ i, (Ind[H i]) (y i) := by
  classical
  obtain ⟨z'', hz''⟩ := gammaElementary_finiteProjectiveGrothendieck_surjective K x
  refine ⟨{ H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H }, inferInstance,
    fun H => H.1, fun H => H.2, fun H => z'' H, ?_⟩
  rw [hz'', DFinsupp.sum, Finset.sum_subset (Finset.subset_univ _)]
  intro H _ hH
  have hz : z'' H = 0 := by by_contra h; exact hH (DFinsupp.mem_support_iff.mpr h)
  rw [hz, map_zero]

end

end

end

end Representation
