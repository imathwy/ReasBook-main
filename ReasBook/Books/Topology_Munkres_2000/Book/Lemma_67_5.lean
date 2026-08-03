module

public import Topology_Munkres_2000.Book.Definition_67_4.ExternalDirectSum

public section

universe u v w x

variable {J : Type v} {G : Type u} {H : Type w}
variable {Gα : J → Type x} [∀ α, AddCommGroup (Gα α)]
variable [AddCommGroup G]
variable (i : ∀ α, Gα α →+ G)

namespace AddMonoidHom

/-- Helper for Lemma 67.5: the canonical summation map of an external direct sum is bijective. -/
lemma IsExternalDirectSum.toAddMonoid_bijective [DecidableEq J] [IsExternalDirectSum i] :
    Function.Bijective (DirectSum.toAddMonoid i) := by
  classical
  let rangeMap : DirectSum J Gα →+ DirectSum J (fun α ↦ (i α).range) :=
    DirectSum.map fun α ↦ (i α).rangeRestrict
  -- Each component maps bijectively onto its range, so their direct-sum map is bijective.
  have h_rangeMap : Function.Bijective rangeMap := by
    constructor
    · exact (DirectSum.map_injective _).mpr fun α ↦
        rangeRestrict_injective_iff.mpr (IsExternalDirectSum.injective α)
    · exact (DirectSum.map_surjective _).mpr fun α ↦ rangeRestrict_surjective (i α)
  -- Summation through the ranges agrees with the original summation on every generator.
  have h_factor :
      DirectSum.toAddMonoid i =
        (DirectSum.coeAddMonoidHom fun α ↦ (i α).range).comp rangeMap := by
    refine DirectSum.addHom_ext' fun α ↦ ?_
    apply AddMonoidHom.ext
    intro x
    simp only [AddMonoidHom.comp_apply, rangeMap, DirectSum.map_of,
      DirectSum.coeAddMonoidHom_of, DirectSum.toAddMonoid_of, coe_rangeRestrict]
  -- The internal direct sum of the ranges supplies the remaining bijective factor.
  rw [h_factor]
  exact IsExternalDirectSum.isInternal.comp h_rangeMap

/-- Lemma 67.5 (forward direction). An external direct sum has the expected universal property:
every family of additive homomorphisms from its summands extends uniquely to the whole group. -/
theorem IsExternalDirectSum.existsUnique_extension [IsExternalDirectSum i] [AddCommGroup H]
    (hα : ∀ α, Gα α →+ H) :
    ∃! h : G →+ H, ∀ α, h.comp (i α) = hα α := by
  classical
  let e : DirectSum J Gα ≃+ G :=
    AddEquiv.ofBijective (DirectSum.toAddMonoid i)
      (IsExternalDirectSum.toAddMonoid_bijective i)
  let h : G →+ H :=
    (DirectSum.toAddMonoid hα).comp e.symm.toAddMonoidHom
  -- The inverse of the summation equivalence sends each summand back to its generator.
  have h_inverse_of (α : J) (x : Gα α) :
      e.symm.toAddMonoidHom (i α x) = DirectSum.of Gα α x := by
    calc
      e.symm.toAddMonoidHom (i α x) = e.symm (i α x) := by
        rw [AddEquiv.coe_toAddMonoidHom]
      _ = e.symm (e (DirectSum.of Gα α x)) :=
        congrArg e.symm (DirectSum.toAddMonoid_of i α x).symm
      _ = DirectSum.of Gα α x := e.symm_apply_apply (DirectSum.of Gα α x)
  -- Consequently the transported direct-sum homomorphism has the prescribed restrictions.
  have h_restrict : ∀ α, h.comp (i α) = hα α := by
    intro α
    apply AddMonoidHom.ext
    intro x
    simp only [AddMonoidHom.comp_apply, h]
    rw [h_inverse_of, DirectSum.toAddMonoid_of]
  refine ⟨h, h_restrict, ?_⟩
  intro g hg
  -- Equality on the generators determines the pullbacks along the surjective summation map.
  have h_comp :
      g.comp (DirectSum.toAddMonoid i) = h.comp (DirectSum.toAddMonoid i) := by
    refine DirectSum.addHom_ext' fun α ↦ ?_
    apply AddMonoidHom.ext
    intro x
    simp only [AddMonoidHom.comp_apply, DirectSum.toAddMonoid_of]
    calc
      g (i α x) = hα α x := DFunLike.congr_fun (hg α) x
      _ = h (i α x) := (DFunLike.congr_fun (h_restrict α) x).symm
  -- Surjectivity then turns equality of pullbacks into equality on all of `G`.
  apply AddMonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := (IsExternalDirectSum.toAddMonoid_bijective i).surjective x
  exact DFunLike.congr_fun h_comp y

/-- Helper for Lemma 67.5: the `β`-coordinate homomorphism is identity at `β` and zero away
from `β`. -/
private def coordinateProjectionHom [DecidableEq J] (β α : J) : Gα α →+ Gα β :=
  if h : α = β then (AddEquiv.cast h).toAddMonoidHom else 0

/-- Helper for Lemma 67.5: the coordinate homomorphism at its selected index is the identity. -/
private lemma coordinateProjectionHom_same [DecidableEq J] (β : J) :
    coordinateProjectionHom (Gα := Gα) β β = AddMonoidHom.id (Gα β) := by
  -- At the selected coordinate the dependent cast is reflexive.
  simp only [coordinateProjectionHom, dite_true]
  rfl

/-- Helper for Lemma 67.5: the coordinate homomorphism vanishes off its selected index. -/
private lemma coordinateProjectionHom_of_ne [DecidableEq J] {α β : J} (h : α ≠ β) :
    coordinateProjectionHom (Gα := Gα) β α = 0 := by
  -- The unequal-index branch is definitionally the zero homomorphism.
  simp only [coordinateProjectionHom, h, dite_false]

/-- Helper for Lemma 67.5: the extension property supplies retractions onto every coordinate,
vanishing on all other coordinates. -/
private lemma coordinateRetractions_of_extension
    (h_extension : ∀ {H : Type x} [AddCommGroup H] (hα : ∀ α, Gα α →+ H),
      ∃ h : G →+ H, ∀ α, h.comp (i α) = hα α) :
    ∀ β, ∃ p : G →+ Gα β,
      p.comp (i β) = AddMonoidHom.id (Gα β) ∧
        ∀ α, α ≠ β → p.comp (i α) = 0 := by
  classical
  intro β
  -- Extend the identity/zero coordinate family to the ambient group.
  obtain ⟨p, hp⟩ := h_extension (coordinateProjectionHom (Gα := Gα) β)
  refine ⟨p, ?_, ?_⟩
  · rw [hp β, coordinateProjectionHom_same]
  · intro α hαβ
    rw [hp α, coordinateProjectionHom_of_ne hαβ]

/-- Helper for Lemma 67.5: coordinate retractions make the ranges of a family of additive
homomorphisms independent. -/
private lemma iSupIndep_range_of_coordinateRetractions
    (h_retractions : ∀ β, ∃ p : G →+ Gα β,
      p.comp (i β) = AddMonoidHom.id (Gα β) ∧
        ∀ α, α ≠ β → p.comp (i α) = 0) :
    iSupIndep (fun α ↦ (i α).range) := by
  rw [iSupIndep_def]
  intro β
  obtain ⟨p, hpβ, hp_other⟩ := h_retractions β
  -- Every off-diagonal range lies in the kernel of the selected retraction.
  have h_other_le_ker :
      (⨆ (α) (_ : α ≠ β), (i α).range) ≤ p.ker := by
    refine iSup_le fun α ↦ iSup_le fun hαβ ↦ ?_
    exact (AddMonoidHom.range_le_ker_iff (i α) p).mpr (hp_other α hαβ)
  -- Applying the retraction separates the selected range from all the other ranges.
  rw [AddSubgroup.disjoint_def]
  intro z hzβ hz_other
  obtain ⟨y, rfl⟩ := hzβ
  have hp_zero : p (i β y) = 0 := h_other_le_ker hz_other
  have hy : y = 0 := by
    calc
      y = (AddMonoidHom.id (Gα β)) y := (AddMonoidHom.id_apply (Gα β) y).symm
      _ = (p.comp (i β)) y := congrArg (fun q : Gα β →+ Gα β ↦ q y) hpβ.symm
      _ = p (i β y) := rfl
      _ = 0 := hp_zero
  rw [hy, map_zero]

/-- Companion for Lemma 67.5: if the ranges of `i α` generate `G` and every family of
additive homomorphisms from the summands extends to `G`, then `i` exhibits `G` as their external
direct sum. -/
theorem isExternalDirectSum_of_extension
    (h_generate : (⨆ α, (i α).range) = ⊤)
    (h_extension : ∀ {H : Type x} [AddCommGroup H] (hα : ∀ α, Gα α →+ H),
      ∃ h : G →+ H, ∀ α, h.comp (i α) = hα α) :
    IsExternalDirectSum i := by
  classical
  -- Coordinate extensions simultaneously provide left inverses and separate the ranges.
  have h_retractions := coordinateRetractions_of_extension i h_extension
  rw [isExternalDirectSum_iff]
  refine ⟨?_, iSupIndep_range_of_coordinateRetractions i h_retractions, h_generate⟩
  intro β
  obtain ⟨p, hpβ, -⟩ := h_retractions β
  -- A map with a coordinate retraction is injective.
  apply Function.LeftInverse.injective (g := p)
  intro y
  calc
    p (i β y) = (p.comp (i β)) y := rfl
    _ = (AddMonoidHom.id (Gα β)) y := congrArg (fun q : Gα β →+ Gα β ↦ q y) hpβ
    _ = y := AddMonoidHom.id_apply (Gα β) y

/- Lemma 67.5. The external-direct-sum condition gives the unique extension property, and the
extension property together with generation conversely gives an external direct sum. -/
#check AddMonoidHom.IsExternalDirectSum.existsUnique_extension
#check AddMonoidHom.isExternalDirectSum_of_extension

end AddMonoidHom

end
