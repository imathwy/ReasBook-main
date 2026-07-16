import DifferentialForms_Cartan_1970.cartan.V.section21.«0001_Definition_V_4_extra_1»

-- Declarations for this item will be appended below by the statement pipeline.

open Set

variable {𝕜 : Type*} [RCLike 𝕜]

-- Domain sampling: this corollary lies in the compact-open compactness API for holomorphic
-- families. Relevant declarations inspected before refinement: the source-facing boundedness owner
-- `UniformlyBoundedOnCompacta`, the canonical compact-open owner `C(D, 𝕜)`, the bridge
-- `analyticFunctionSubring 𝕜 D → C(D, 𝕜)`, the canonical restriction continuity
-- `continuous_precomp`, and the compact-domain norm control `ContinuousMap.norm_coe_le_norm`.
-- Layer triage: the family `A` is source-facing, while compactness and closedness are stated on
-- its canonical image in `C(D, 𝕜)`.
/-- A compact family of holomorphic restrictions is uniformly bounded on every compact subset of
`D`. The proof uses the canonical compact-open owner `C(D, 𝕜)`: restrict the compact family to a
fixed compact `K ⊆ D`, obtain a compact subset of `C(K, 𝕜)`, then use the compact-domain sup norm
on `C(K, 𝕜)` to get one bound for all values on `K`. -/
theorem compact_holomorphic_family_is_bounded
    {D : Set 𝕜}
    {A : Set (analyticFunctionSubring 𝕜 D)}
    (hA : IsCompact (((↑) : analyticFunctionSubring 𝕜 D → C(D, 𝕜)) '' A)) :
    UniformlyBoundedOnCompacta D A := by
  intro K hK hKD
  let iK : C(K, D) := ⟨fun z ↦ ⟨z.1, hKD z.2⟩, by fun_prop⟩
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hA_restrict :
      IsCompact
        ((fun g : C(D, 𝕜) ↦ g.comp iK) ''
          (((↑) : analyticFunctionSubring 𝕜 D → C(D, 𝕜)) '' A)) :=
    hA.image (ContinuousMap.continuous_precomp iK)
  obtain ⟨M, hM⟩ := hA_restrict.isBounded.exists_norm_le
  refine ⟨M, ?_⟩
  intro f hf z hz
  let g : C(K, 𝕜) := (f : C(D, 𝕜)).comp iK
  have hg :
      g ∈
        (fun g' : C(D, 𝕜) ↦ g'.comp iK) ''
          (((↑) : analyticFunctionSubring 𝕜 D → C(D, 𝕜)) '' A) := by
    refine ⟨(f : C(D, 𝕜)), ?_, rfl⟩
    exact mem_image_of_mem ((↑) : analyticFunctionSubring 𝕜 D → C(D, 𝕜)) hf
  exact (ContinuousMap.norm_coe_le_norm g ⟨z, hz⟩).trans <| by
    simpa [g, iK] using hM g hg

/-- Theorem V.4-extra-3: a family of holomorphic restrictions is compact in the canonical
compact-open function space `C(D, 𝕜)` as soon as it is uniformly bounded on compact subsets of `D`
and its image in `C(D, 𝕜)` is closed, assuming the preceding relative-compactness input that every
uniformly bounded family has compact closure in `C(D, 𝕜)`. -/
theorem holomorphic_compact_of_bounded_closed
    {D : Set 𝕜}
    (hrelcompact :
      ∀ A : Set (analyticFunctionSubring 𝕜 D),
        UniformlyBoundedOnCompacta D A →
          IsCompact (closure (((↑) : analyticFunctionSubring 𝕜 D → C(D, 𝕜)) '' A)))
    {A : Set (analyticFunctionSubring 𝕜 D)}
    (hA_bounded : UniformlyBoundedOnCompacta D A)
    (hA_closed : IsClosed (((↑) : analyticFunctionSubring 𝕜 D → C(D, 𝕜)) '' A)) :
    IsCompact (((↑) : analyticFunctionSubring 𝕜 D → C(D, 𝕜)) '' A) := by
  simpa [hA_closed.closure_eq] using hrelcompact A hA_bounded

/-- Corollary V.4-extra-4: a family of holomorphic restrictions is compact in the canonical
compact-open function space `C(D, 𝕜)` exactly when it is uniformly bounded on compact subsets of
`D` and its image in `C(D, 𝕜)` is closed, assuming the preceding relative-compactness result that
every uniformly bounded family has compact closure in `C(D, 𝕜)`. -/
theorem holomorphic_compact_iff_bounded_closed
    {D : Set 𝕜}
    (hrelcompact :
      ∀ A : Set (analyticFunctionSubring 𝕜 D),
        UniformlyBoundedOnCompacta D A →
          IsCompact (closure (((↑) : analyticFunctionSubring 𝕜 D → C(D, 𝕜)) '' A)))
    (A : Set (analyticFunctionSubring 𝕜 D)) :
    IsCompact (((↑) : analyticFunctionSubring 𝕜 D → C(D, 𝕜)) '' A) ↔
      UniformlyBoundedOnCompacta D A ∧
        IsClosed (((↑) : analyticFunctionSubring 𝕜 D → C(D, 𝕜)) '' A) := by
  constructor
  · intro hA
    exact ⟨compact_holomorphic_family_is_bounded hA, hA.isClosed⟩
  · rintro ⟨hA_bounded, hA_closed⟩
    exact holomorphic_compact_of_bounded_closed hrelcompact hA_bounded hA_closed
