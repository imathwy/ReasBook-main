import Mathlib
import DifferentialForms_Cartan_1970.V.section21.«0001_Definition_V_4_extra_1»

-- Declarations for this item will be appended below by the statement pipeline.

open Set

-- Domain sampling: this file lies in the compact-open topology domain for families of holomorphic
-- functions. The relevant owner declarations inspected before refinement were the chapter's
-- holomorphic restriction-space carrier `analyticFunctionSubring`, its canonical bridge to
-- `C(D, 𝕜)`, and mathlib's compact-open owners `ContinuousMap.continuous_precomp`,
-- `continuous_eval`, `IsCompact.exists_bound_of_continuousOn`, and `IsCompact.isClosed`.
-- Layer triage: `A : Set (analyticFunctionSubring 𝕜 D)` is source-facing, `C(D, 𝕜)` is the
-- core/canonical owner carrying the compact-open topology, and the coercion
-- `analyticFunctionSubring 𝕜 D → C(D, 𝕜)` is the bridge/view.
-- Primitive data: compactness of the image of `A` in `C(D, 𝕜)`. Derived API: closedness and
-- uniform boundedness on compact subsets of `D`.
variable {𝕜 : Type*} [RCLike 𝕜]
variable {D : Set 𝕜}
variable {A : Set (analyticFunctionSubring 𝕜 D)}

/- Proposition 2.1 (1): after viewing a holomorphic family `A` in the canonical compact-open
owner `C(D, 𝕜)`, compactness implies closedness by the standard owner theorem
`IsCompact.isClosed`. -/
#check
  (IsCompact.isClosed :
    IsCompact (((↑) : analyticFunctionSubring 𝕜 D → C(D, 𝕜)) '' A) →
      IsClosed (((↑) : analyticFunctionSubring 𝕜 D → C(D, 𝕜)) '' A))

/-- Proposition 2.1 (2): if a family of holomorphic restrictions is compact in the canonical
compact-open topology inherited from `C(D, 𝕜)`, then it is uniformly bounded on compact subsets of
`D`. -/
theorem compact_holomorphic_family_is_bounded
    (hA : IsCompact (((↑) : analyticFunctionSubring 𝕜 D → C(D, 𝕜)) '' A)) :
    UniformlyBoundedOnCompacta D A := by
  intro K hK hKD
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let incl : C(K, D) :=
    ⟨fun z ↦ ⟨z.1, hKD z.2⟩, continuous_subtype_val.subtype_mk fun z ↦ hKD z.2⟩
  have hEvalK : Continuous (fun q : C(K, 𝕜) × K ↦ q.1 q.2) :=
    (ContinuousEval.continuous_eval : Continuous fun q : C(K, 𝕜) × K ↦ q.1 q.2)
  have hCompIncl : Continuous fun p : C(D, 𝕜) × K ↦ (p.1.comp incl, p.2) :=
    ((ContinuousMap.continuous_precomp incl).comp continuous_fst).prodMk continuous_snd
  have hEval : Continuous fun p : C(D, 𝕜) × K ↦ (p.1.comp incl) p.2 := by
    simpa using hEvalK.comp hCompIncl
  obtain ⟨M, hM⟩ :=
    (hA.prod (isCompact_univ : IsCompact (Set.univ : Set K))).exists_bound_of_continuousOn
      hEval.continuousOn
  refine ⟨M, ?_⟩
  intro f hf z hz
  let zK : K := ⟨z, hz⟩
  let zD : D := ⟨z, hKD hz⟩
  have hf' : (f : C(D, 𝕜)) ∈ (((↑) : analyticFunctionSubring 𝕜 D → C(D, 𝕜)) '' A) :=
    ⟨f, hf, rfl⟩
  have hMz := hM ((f : C(D, 𝕜)), zK) ⟨hf', by simp⟩
  simpa [incl, zD, zK] using hMz
