import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap03.Definition_3_8
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap12.ScaledProximityOperator

open scoped InnerProductSpace

universe u

namespace ERealFunction

-- Semantic recall: `lean_leansearch` did not surface a usable project-local theorem for this
-- item, so the verified owner surface here is the canonical lower level set
-- `lowerLevelSet f.asEReal ζ`, the scaled proximity operator `Prox[ν, f, hf]`, and the
-- set-valued projector `P[C]`.

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Proposition 29.37 (1): let `f ∈ Γ₀(H)` and `z ∈ H`. If
`(ζ : EReal) ∈ Set.Ioo (sInf (Set.range f.asEReal)) (f.asEReal z)` and the lower level set
`lowerLevelSet f.asEReal ζ` is contained in `interior (effectiveDomain f)`, then the equation
`f (Prox[ν, f, hf] z) = ζ` has at least one solution `ν ∈ ℝ₊₊`, written here as a `PosReal`
parameter with value identity on the canonical `EReal` surface. -/
theorem exists_posReal_prox_eq_level_of_lowerLevelSet_subset_interior_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {z : H} {ζ : ℝ}
    (hζ : (ζ : EReal) ∈ Set.Ioo (sInf (Set.range f.asEReal)) (f.asEReal z))
    (hC_subset : lowerLevelSet f.asEReal ζ ⊆ interior (effectiveDomain f)) :
    ∃ ν : PosReal, f.asEReal (Prox[ν, f, hf] z) = (ζ : EReal) := sorry

/-- Proposition 29.37 (2): under the same assumptions, if `νbar ∈ ℝ₊₊` satisfies
`f (Prox[νbar, f, hf] z) = ζ`, then the metric projection of `z` onto
`C = lowerLevelSet f.asEReal ζ` is exactly that proximal point, expressed on the canonical
set-valued projector surface as `P[C] z = {Prox[νbar, f, hf] z}`. -/
theorem setValuedProjector_lowerLevelSet_eq_singleton_prox_of_prox_eq_level
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {z : H} {ζ : ℝ}
    (hζ : (ζ : EReal) ∈ Set.Ioo (sInf (Set.range f.asEReal)) (f.asEReal z))
    (hC_subset : lowerLevelSet f.asEReal ζ ⊆ interior (effectiveDomain f))
    {νbar : PosReal} (hνbar : f.asEReal (Prox[νbar, f, hf] z) = (ζ : EReal)) :
    P[lowerLevelSet f.asEReal ζ] z = ({Prox[νbar, f, hf] z} : Set H) := sorry

/-- Under Proposition 29.37's hypotheses, the proximal point at level `ζ` belongs to the
set-valued projector of the lower level set at `z`. -/
theorem prox_mem_setValuedProjector_lowerLevelSet_of_prox_eq_level
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {z : H} {ζ : ℝ}
    (hζ : (ζ : EReal) ∈ Set.Ioo (sInf (Set.range f.asEReal)) (f.asEReal z))
    (hC_subset : lowerLevelSet f.asEReal ζ ⊆ interior (effectiveDomain f))
    {νbar : PosReal} (hνbar : f.asEReal (Prox[νbar, f, hf] z) = (ζ : EReal)) :
    Prox[νbar, f, hf] z ∈ P[lowerLevelSet f.asEReal ζ] z := by
  rw [setValuedProjector_lowerLevelSet_eq_singleton_prox_of_prox_eq_level
    hf hζ hC_subset hνbar]
  simp

/-- Under Proposition 29.37's hypotheses, any point of the set-valued projector of the lower level
set at `z` is the proximal point realizing the level `ζ`. -/
theorem eq_prox_of_mem_setValuedProjector_lowerLevelSet_of_prox_eq_level
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {z : H} {ζ : ℝ}
    (hζ : (ζ : EReal) ∈ Set.Ioo (sInf (Set.range f.asEReal)) (f.asEReal z))
    (hC_subset : lowerLevelSet f.asEReal ζ ⊆ interior (effectiveDomain f))
    {νbar : PosReal} (hνbar : f.asEReal (Prox[νbar, f, hf] z) = (ζ : EReal)) {p : H}
    (hp : p ∈ P[lowerLevelSet f.asEReal ζ] z) :
    p = Prox[νbar, f, hf] z := by
  rw [setValuedProjector_lowerLevelSet_eq_singleton_prox_of_prox_eq_level
    hf hζ hC_subset hνbar] at hp
  simpa using hp

/-- Under Proposition 29.37's hypotheses, any Chebyshev projection point of the lower level set at
`z` is the proximal point realizing the level `ζ`. -/
theorem projectionPoint_lowerLevelSet_eq_prox_of_prox_eq_level
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {z : H} {ζ : ℝ}
    (hζ : (ζ : EReal) ∈ Set.Ioo (sInf (Set.range f.asEReal)) (f.asEReal z))
    (hC_subset : lowerLevelSet f.asEReal ζ ⊆ interior (effectiveDomain f))
    {νbar : PosReal} (hνbar : f.asEReal (Prox[νbar, f, hf] z) = (ζ : EReal))
    (hC : IsChebyshev (lowerLevelSet f.asEReal ζ)) :
    P[lowerLevelSet f.asEReal ζ, hC] z = Prox[νbar, f, hf] z :=
  eq_prox_of_mem_setValuedProjector_lowerLevelSet_of_prox_eq_level
    hf hζ hC_subset hνbar (projectionPoint_mem_setValuedProjector _ hC z)

end ERealFunction
