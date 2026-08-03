module

public import Topology_Munkres_2000.Book.Definition_67_4

public section

namespace DirectSum

universe u v

variable {ι : Type u} {H : Type v}

/-- Helper for Definition 67.4: additive subgroups form an internal direct sum exactly when they
are independent and generate the ambient additive group. -/
theorem isInternal_addSubgroup_iff_iSupIndep_and_iSup_eq_top [DecidableEq ι]
    [AddCommGroup H] (A : ι → AddSubgroup H) :
    DirectSum.IsInternal A ↔ iSupIndep A ∧ (⨆ α, A α) = ⊤ := by
  let e : AddSubgroup H ≃o Submodule ℤ H := AddSubgroup.toIntSubmodule
  -- Regard the subgroup decomposition as the definitionally equal ℤ-submodule decomposition.
  have hInternal :
      DirectSum.IsInternal A ↔ DirectSum.IsInternal (e ∘ A) := Iff.rfl
  -- The order isomorphism preserves both independence and generation of the top element.
  have hIndependent : iSupIndep (e ∘ A) ↔ iSupIndep A :=
    iSupIndep_map_orderIso_iff e
  have hFamily : e ∘ A = fun α ↦ e (A α) := rfl
  have hGenerate : iSup (e ∘ A) = ⊤ ↔ (⨆ α, A α) = ⊤ := by
    rw [hFamily, ← e.map_iSup, map_eq_top_iff]
  rw [hInternal, DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top,
    hIndependent, hGenerate]

end DirectSum

namespace AddMonoidHom

universe u v w

variable {ι : Type u} {G : ι → Type v} {H : Type w}
variable [∀ α, AddCommGroup (G α)] [AddCommGroup H]

/-- The external-direct-sum property is equivalent to injectivity of every map, independence of
their ranges, and generation of the ambient group by those ranges. -/
theorem isExternalDirectSum_iff (i : ∀ α, G α →+ H) :
    IsExternalDirectSum i ↔
      (∀ α, Function.Injective (i α)) ∧
        iSupIndep (fun α ↦ (i α).range) ∧
          (⨆ α, (i α).range) = ⊤ := by
  -- Unpack the class into the three mathematical conditions in the definition.
  constructor
  · intro h
    exact ⟨h.injective, h.iSupIndep_range, h.iSup_range_eq_top⟩
  -- Conversely, package those conditions as the external-direct-sum class.
  · rintro ⟨hinjective, hindependent, hgenerate⟩
    exact ⟨hinjective, hindependent, hgenerate⟩

/-- The ranges of an external-direct-sum family form an internal direct sum. -/
theorem IsExternalDirectSum.isInternal [DecidableEq ι] {i : ∀ α, G α →+ H}
    [IsExternalDirectSum i] : DirectSum.IsInternal (fun α ↦ (i α).range) := by
  -- The class fields are precisely the independence and generation conditions for internalness.
  rw [DirectSum.isInternal_addSubgroup_iff_iSupIndep_and_iSup_eq_top]
  exact ⟨IsExternalDirectSum.iSupIndep_range, IsExternalDirectSum.iSup_range_eq_top⟩

end AddMonoidHom

namespace DirectSum

universe u v w

variable {ι : Type u} (G : ι → Type v) [∀ α, AddCommGroup (G α)]

private noncomputable def inclusionImpl (α : ι) : G α →+ DirectSum ι G :=
  @DirectSum.of ι G _ (Classical.decEq ι) α

/-- The canonical inclusion of one coordinate into a direct sum. -/
noncomputable def inclusion (α : ι) : G α →+ DirectSum ι G :=
  inclusionImpl G α

/-- The canonical inclusion has the prescribed value in its own coordinate. -/
@[simp]
theorem inclusion_apply_same (α : ι) (x : G α) : inclusion G α x α = x := by
  classical
  exact DirectSum.of_eq_same α x

/-- A canonical inclusion vanishes in every other coordinate. -/
theorem inclusion_apply_of_ne {α β : ι} (x : G α) (h : β ≠ α) : inclusion G α x β = 0 := by
  classical
  exact DirectSum.of_eq_of_ne α β x h

/-- An element lies in the range of one canonical inclusion exactly when it vanishes away from
that coordinate. -/
theorem mem_inclusion_range_iff (α : ι) (x : DirectSum ι G) :
    x ∈ (inclusion G α).range ↔ ∀ β, β ≠ α → x β = 0 := by
  classical
  constructor
  · rintro ⟨y, rfl⟩ β h
    exact inclusion_apply_of_ne G y h
  · intro h
    refine ⟨x α, DFinsupp.ext fun β ↦ ?_⟩
    by_cases hβα : β = α
    · subst β
      exact inclusion_apply_same G α (x α)
    · exact (inclusion_apply_of_ne G (x α) hβα).trans (h β hβα).symm

/-- The canonical inclusion of each coordinate is injective. -/
theorem inclusion_injective (α : ι) : Function.Injective (inclusion G α) := by
  classical
  exact DirectSum.of_injective α

/-- Helper for Definition 67.4: the canonical inclusion agrees with the active-instance spelling
of `DirectSum.of`. -/
theorem inclusion_eq_of [DecidableEq ι] (α : ι) (x : G α) :
    inclusion G α x = DirectSum.of G α x := by
  -- Compare the two direct-sum elements coordinatewise, avoiding equality of `DecidableEq` data.
  ext β
  by_cases hβα : β = α
  · subst β
    rw [inclusion_apply_same, DirectSum.of_eq_same]
  · rw [inclusion_apply_of_ne G x hβα, DirectSum.of_eq_of_ne α β x hβα]

/-- Helper for Definition 67.4: the direct-sum equivalence induced coordinatewise sends a
generator to the corresponding generator. -/
theorem congrAddEquiv_toAddMonoidHom_of [DecidableEq ι]
    {N : ι → Type v} {P : ι → Type w}
    [∀ α, AddCommMonoid (N α)] [∀ α, AddCommMonoid (P α)]
    (e : ∀ α, N α ≃+ P α) (α : ι) (x : N α) :
    (DirectSum.congrAddEquiv e).toAddMonoidHom (DirectSum.of N α x) =
      DirectSum.of P α (e α x) := by
  -- The additive equivalence is implemented by the coordinatewise direct-sum map.
  exact DirectSum.map_of (fun β ↦ (e β).toAddMonoidHom) α x

/-- Helper for Definition 67.4: the ranges of the canonical direct-sum inclusions form an internal
direct sum. -/
private theorem inclusionRangesIsInternal [DecidableEq ι] :
    DirectSum.IsInternal (fun α ↦ (inclusion G α).range) := by
  let coordinateEquiv : ∀ α, G α ≃+ (inclusion G α).range :=
    fun α ↦ AddMonoidHom.ofInjective (inclusion_injective G α)
  let rangeEquiv :
      (⨁ α, G α) ≃+ (⨁ α, (inclusion G α).range) :=
    DirectSum.congrAddEquiv coordinateEquiv
  -- On every generator, summing after the coordinatewise equivalence recovers the inclusion.
  have hComposite :
      (DirectSum.coeAddMonoidHom (fun α ↦ (inclusion G α).range)).comp
          rangeEquiv.toAddMonoidHom = AddMonoidHom.id (DirectSum ι G) := by
    apply DirectSum.addHom_ext
    intro α x
    simp only [AddMonoidHom.comp_apply, rangeEquiv, congrAddEquiv_toAddMonoidHom_of,
      DirectSum.coeAddMonoidHom_of, coordinateEquiv, AddMonoidHom.ofInjective_apply,
      AddMonoidHom.id_apply]
    exact inclusion_eq_of G α x
  -- Since the coordinatewise map is an equivalence and the composite is the identity, the
  -- canonical summation map is bijective.
  have hCompositeBijective :
      Function.Bijective
        ((DirectSum.coeAddMonoidHom (fun α ↦ (inclusion G α).range)).comp
          rangeEquiv.toAddMonoidHom) := by
    rw [hComposite]
    exact Function.bijective_id
  exact (Function.Bijective.of_comp_iff
    (DirectSum.coeAddMonoidHom (fun α ↦ (inclusion G α).range))
    rangeEquiv.bijective).mp hCompositeBijective

/-- The canonical inclusions exhibit `DirectSum ι G` as the external direct sum of `G`. -/
noncomputable instance instIsExternalDirectSum :
    AddMonoidHom.IsExternalDirectSum (inclusion G) := by
  classical
  -- Canonical internalness supplies independence and generation; coordinate evaluation supplies
  -- injectivity of every inclusion.
  have hinternal := inclusionRangesIsInternal G
  have hconditions :=
    (DirectSum.isInternal_addSubgroup_iff_iSupIndep_and_iSup_eq_top
      (fun α ↦ (inclusion G α).range)).mp hinternal
  exact ⟨inclusion_injective G, hconditions.1, hconditions.2⟩

end DirectSum
