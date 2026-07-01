import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_31_0_7

noncomputable section

universe u

namespace Bifunction

section

open scoped Rockafellar

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.11 is the identity-map specialization of the Fenchel-duality
  qualification statement: if `riDom[𝕜](f)` meets `riDom[𝕜](-g)`, then the associated
  identity-map Fenchel perturbation is strongly consistent.
- `core/canonical`: the owner abstractions are already `fenchelPerturbation` and
  `IsStronglyConsistent`, with the general qualification theorem
  `isStronglyConsistent_fenchelPerturbation_iff_exists_mem_riDom` established upstream in
  `Lemma_31_0_7`.
- `bridge/view`: the source intersection condition is a thin rewrite of the canonical
  existential qualification witness when the linear map is `LinearMap.id`.

Domain-style sampling used here:
- `Bifunction.fenchelPerturbation`;
- `Bifunction.IsStronglyConsistent`;
- `Bifunction.isStronglyConsistent_fenchelPerturbation_iff_exists_mem_riDom`;
- the Chapter 1 domain owner `riDom[𝕜](·)`.

Primitive data vs derived API:
- primitive source data: the functions `f`, `g`, and a witness `x` with
  `x ∈ riDom[𝕜](f)` and `x ∈ riDom[𝕜](-g)`;
- primitive owner object: `F := fenchelPerturbation LinearMap.id f g`;
- derived API: the strong-consistency conclusion for that owner.

Layer target: `source-facing`, kept as the source's identity-map corollary while delegating the
actual owner-level proof to the general Chapter 31 theorem instead of duplicating its domain and
epigraph infrastructure locally.
-/

variable (f g : E → WithBotTop 𝕜)

local notation "F" => fenchelPerturbation LinearMap.id f g

/-- Identity-map specialization of Lemma 31.0.7 at the canonical existential qualification layer.
For `F := fenchelPerturbation id f g`, strong consistency is equivalent to existence of
`x ∈ riDom[𝕜](f)` with `x ∈ riDom[𝕜](-g)`. -/
theorem isStronglyConsistent_fenchelPerturbation_id_iff_exists_mem_riDom
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hg_concave : g.IsConcave 𝕜) (hg_proper : g.IsProperConcave) :
    IsStronglyConsistent 𝕜 F ↔
      ∃ x : E, x ∈ riDom[𝕜](f) ∧ x ∈ riDom[𝕜](-g) := by
  simpa using
    (isStronglyConsistent_fenchelPerturbation_iff_exists_mem_riDom
      (A := (LinearMap.id : E →ₗ[𝕜] E)) hf hf_proper hg_concave hg_proper)

/-- Identity-map specialization of Lemma 31.0.7: for `F := fenchelPerturbation id f g`, strong
consistency is equivalent to nonempty qualification intersection
`riDom[𝕜](f) ∩ riDom[𝕜](-g)`. -/
theorem isStronglyConsistent_fenchelPerturbation_id_iff_riDom_inter_nonempty
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hg_concave : g.IsConcave 𝕜) (hg_proper : g.IsProperConcave) :
    IsStronglyConsistent 𝕜 F ↔
      (riDom[𝕜](f) ∩ riDom[𝕜](-g)).Nonempty := by
  simpa [Set.nonempty_def, Set.mem_inter_iff] using
    (isStronglyConsistent_fenchelPerturbation_id_iff_exists_mem_riDom
      (f := f) (g := g) hf hf_proper hg_concave hg_proper)

/-- Canonical implication form: any existential `riDom` qualification witness implies strong
consistency for the identity-map Fenchel perturbation. -/
theorem isStronglyConsistent_fenchelPerturbation_id_of_exists_mem_riDom
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hg_concave : g.IsConcave 𝕜) (hg_proper : g.IsProperConcave)
    (hri : ∃ x : E, x ∈ riDom[𝕜](f) ∧ x ∈ riDom[𝕜](-g)) :
    IsStronglyConsistent 𝕜 F := by
  exact
    (isStronglyConsistent_fenchelPerturbation_id_iff_exists_mem_riDom
      (f := f) (g := g) hf hf_proper hg_concave hg_proper).2 hri

/- Lemma 31.0.11: if `riDom[𝕜](f)` and `riDom[𝕜](-g)` intersect, then the identity-map Fenchel
perturbation associated to `f` and `g` is strongly consistent. -/
theorem isStronglyConsistent_fenchelPerturbation_id_of_riDom_inter_nonempty
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hg_concave : g.IsConcave 𝕜) (hg_proper : g.IsProperConcave)
    (hri : (riDom[𝕜](f) ∩ riDom[𝕜](-g)).Nonempty) :
    IsStronglyConsistent 𝕜 F := by
  exact
    isStronglyConsistent_fenchelPerturbation_id_of_exists_mem_riDom
      (f := f) (g := g) hf hf_proper hg_concave hg_proper
      (by simpa [Set.nonempty_def, Set.mem_inter_iff] using hri)

end

end Bifunction
