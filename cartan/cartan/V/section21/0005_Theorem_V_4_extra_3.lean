import cartan.V.section21.«0001_Definition_V_4_extra_1»

-- Declarations for this item will be appended below by the statement pipeline.

open Set

variable {𝕜 : Type*} [RCLike 𝕜]
variable {D : Set 𝕜}

-- Domain sampling: this item lies in the compact-open compactness API for holomorphic families.
-- The relevant owner declarations checked before refinement were the source-facing boundedness
-- predicate `UniformlyBoundedOnCompacta`, the canonical compact-open owner `C(D, 𝕜)`, the bridge
-- `analyticFunctionSubring 𝕜 D → C(D, 𝕜)`, and the owner compactness lemma
-- `IsClosed.closure_eq`.
-- Layer triage: `A : Set (analyticFunctionSubring 𝕜 D)` is source-facing, `C(D, 𝕜)` is the
-- core/canonical owner, and the image of `A` in `C(D, 𝕜)` is the bridge/view on which compactness
-- and closedness live.
-- Primitive data: uniform boundedness on compact subsets of `D`. Derived API: compactness of the
-- corresponding subset of `C(D, 𝕜)` from the relative-compactness hypothesis.

/-- Theorem V.4-extra-3: a family of holomorphic restrictions is compact in the canonical
compact-open function space `C(D, 𝕜)` as soon as it is uniformly bounded on compact subsets of `D`
and its image in `C(D, 𝕜)` is closed, assuming the preceding relative-compactness input that every
uniformly bounded family has compact closure in `C(D, 𝕜)`. -/
theorem holomorphic_compact_of_bounded_closed
    (hrelcompact :
      ∀ A : Set (analyticFunctionSubring 𝕜 D),
        UniformlyBoundedOnCompacta D A →
          IsCompact (closure (((↑) : analyticFunctionSubring 𝕜 D → C(D, 𝕜)) '' A)))
    {A : Set (analyticFunctionSubring 𝕜 D)}
    (hA_bounded : UniformlyBoundedOnCompacta D A)
    (hA_closed : IsClosed (((↑) : analyticFunctionSubring 𝕜 D → C(D, 𝕜)) '' A)) :
    IsCompact (((↑) : analyticFunctionSubring 𝕜 D → C(D, 𝕜)) '' A) := by
  simpa [hA_closed.closure_eq] using hrelcompact A hA_bounded
