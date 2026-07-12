import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_0_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

/-
Source/core/bridge triage:
- `source-facing`: Definition 2.1.2 introduces polyhedral subsets as finite intersections of
  closed half-spaces. On the public owner surface, the primitive data should therefore be finitely
  many inequality normals and levels, not an ambient inner product model.
- `core/canonical`: the owner abstraction is an ordinary subset `s : Set E`, presented as a
  finite intersection of the chapter half-space owner `closedHalfSpaceLE` attached to a pairing
  witness type `Y` and levels `β : 𝕜`. The owner is pairing-parametric at this primitive layer,
  with linear-dual and other concrete models treated as downstream bridge specializations.
- `bridge/view`: downstream files can pass between this owner and explicit finite indexed
  inequality systems by enumerating the defining `Finset` of `(normal, level)` parameters; no
  separate subset-family owner is needed here.
- Primitive data vs derived API: the primitive source-facing data are finitely many inequality
  parameters `(y, β)` in the chosen pairing layer; convexity and closedness are derived API.
- Domain-style sampling: the relevant owner-side declarations are `closedHalfSpaceLE`,
  `mem_closedHalfSpaceLE_iff`, `convex_halfSpace_le`, `convex_iInter₂`,
  `isClosed_Iic.preimage`, and `LinearMap.continuous_of_finiteDimensional`.
-/

variable {𝕜 : Type u} {E : Type v}
variable [Preorder 𝕜]

namespace Set

variable (𝕜)

/-- Definition 2.1.2: a subset is polyhedral when it can be written as the intersection of
finitely many closed half-spaces, equivalently by finitely many weak pairing inequalities. -/
def IsPolyhedral (s : Set E) (Y : Type _) [HasPairing E Y 𝕜] : Prop :=
  ∃ S : Finset (Y × 𝕜), s = ⋂ y ∈ S, closedHalfSpaceLE y.1 y.2

/-- The intersection of two polyhedral sets is polyhedral. -/
theorem IsPolyhedral.inter {Y : Type _} [HasPairing E Y 𝕜] {s t : Set E}
    (hs : s.IsPolyhedral 𝕜 Y)
    (ht : t.IsPolyhedral 𝕜 Y) :
    (s ∩ t).IsPolyhedral 𝕜 Y := by
  classical
  rcases hs with ⟨S, rfl⟩
  rcases ht with ⟨T, rfl⟩
  refine ⟨S ∪ T, ?_⟩
  ext x
  constructor
  · rintro ⟨hxS, hxT⟩
    simp only [Set.mem_iInter] at hxS hxT ⊢
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact hxS y hy
    · exact hxT y hy
  · intro hx
    simp only [Set.mem_inter_iff, Set.mem_iInter] at hx ⊢
    refine ⟨?_, ?_⟩ <;> intro y hy
    · exact hx y (Finset.mem_union.mpr <| Or.inl hy)
    · exact hx y (Finset.mem_union.mpr <| Or.inr hy)

end Set

end

section Convexity

variable {𝕜 : Type u} {E : Type v}
variable [CommSemiring 𝕜] [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜] [PosSMulMono 𝕜 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

namespace Set

/-- A finite intersection of weak closed half-spaces is convex once each appearing pairing
evaluation map is linear in the primal variable. -/
theorem convex_iInter_closedHalfSpaceLE_of_forall_isLinear {Y : Type _}
    [HasPairing E Y 𝕜] (S : Finset (Y × 𝕜))
    (hlin : ∀ y ∈ S, IsLinearMap 𝕜 (fun x : E ↦ (HasPairing.pairing x y.1 : 𝕜))) :
    Convex 𝕜 ((⋂ y ∈ S, closedHalfSpaceLE y.1 y.2) : Set E) := by
  refine convex_iInter₂ fun y hy ↦ ?_
  simpa [closedHalfSpaceLE] using
    convex_halfSpace_le (hlin y hy) y.2

/-- Convenience bridge: finite intersections of weak closed half-spaces are convex under a linear
pairing. -/
theorem convex_iInter_closedHalfSpaceLE {Y : Type (max u v)}
    [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing E Y 𝕜] (S : Finset (Y × 𝕜)) :
    Convex 𝕜 ((⋂ y ∈ S, closedHalfSpaceLE y.1 y.2) : Set E) :=
  convex_iInter_closedHalfSpaceLE_of_forall_isLinear (𝕜 := 𝕜) (E := E) (Y := Y) S
    (fun y _ ↦ HasLinearPairing.isLinear_pairing_left y.1)

/-- Every polyhedral set is convex once pairing evaluation is linear in the primal variable. -/
theorem IsPolyhedral.convex_of_forall_isLinear {s : Set E} {Y : Type _}
    [HasPairing E Y 𝕜]
    (hs : s.IsPolyhedral 𝕜 Y)
    (hlin : ∀ y : Y, IsLinearMap 𝕜 (fun x : E ↦ (HasPairing.pairing x y : 𝕜))) :
    Convex 𝕜 s := by
  rcases hs with ⟨S, rfl⟩
  exact convex_iInter_closedHalfSpaceLE_of_forall_isLinear
    (𝕜 := 𝕜) (E := E) (Y := Y) S (fun y _ ↦ hlin y.1)

/-- Every polyhedral set is convex. -/
theorem IsPolyhedral.convex {s : Set E}
    {Y : Type (max u v)} [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing E Y 𝕜]
    (hs : s.IsPolyhedral 𝕜 Y) : Convex 𝕜 s := by
  exact hs.convex_of_forall_isLinear
    (fun y ↦ HasLinearPairing.isLinear_pairing_left y)

end Set

end Convexity

section TopologicalCanonical

variable {𝕜 : Type u} {E : Type v}
variable [Preorder 𝕜] [TopologicalSpace 𝕜] [ClosedIicTopology 𝕜]
variable [TopologicalSpace E]

namespace Set

/-- A finite intersection of weak closed half-spaces is closed once each appearing pairing
evaluation is continuous in the primal variable. -/
theorem isClosed_iInter_closedHalfSpaceLE {Y : Type _}
    [HasPairing E Y 𝕜] (S : Finset (Y × 𝕜))
    (hcont : ∀ y ∈ S, Continuous (fun x : E ↦ (HasPairing.pairing x y.1 : 𝕜))) :
    IsClosed ((⋂ y ∈ S, closedHalfSpaceLE y.1 y.2) : Set E) := by
  exact isClosed_biInter fun y hy ↦ by
    change IsClosed ((fun x : E ↦ (HasPairing.pairing x y.1 : 𝕜)) ⁻¹' Set.Iic y.2)
    simpa [closedHalfSpaceLE] using isClosed_Iic.preimage (hcont y hy)

/-- Convenience bridge: if pairing evaluation is globally continuous in the primal variable, then
finite intersections of weak closed half-spaces are closed. -/
theorem isClosed_iInter_closedHalfSpaceLE_of_continuousPairing {Y : Type _}
    [HasPairing E Y 𝕜] [HasContinuousPairing E Y 𝕜] (S : Finset (Y × 𝕜)) :
    IsClosed ((⋂ y ∈ S, closedHalfSpaceLE y.1 y.2) : Set E) :=
  isClosed_iInter_closedHalfSpaceLE (𝕜 := 𝕜) (E := E) (Y := Y) S
    (fun y _ ↦ HasContinuousPairing.continuous_pairing_left (X := E) (Y := Y) (𝕜 := 𝕜) y.1)

/-- A polyhedral set is closed whenever pairing evaluation is continuous in the primal variable. -/
theorem IsPolyhedral.isClosed {s : Set E}
    {Y : Type (max u v)} [HasPairing E Y 𝕜] [HasContinuousPairing E Y 𝕜]
    (hs : s.IsPolyhedral 𝕜 Y) : IsClosed s := by
  rcases hs with ⟨S, rfl⟩
  simpa using isClosed_iInter_closedHalfSpaceLE_of_continuousPairing
    (𝕜 := 𝕜) (E := E) (Y := Y) S

end Set

end TopologicalCanonical

section TopologicalPairingBridge

variable {𝕜 : Type u} {E : Type v}
variable [Preorder 𝕜] [TopologicalSpace 𝕜] [ClosedIicTopology 𝕜]
variable [TopologicalSpace E]

namespace Set

/-- Pairing bridge: finite intersections of half-spaces are closed when each appearing pairing
functional is continuous in the primal variable. -/
theorem isClosed_iInter_closedHalfSpaceLE_of_forall_continuous
    {Y : Type _} [HasPairing E Y 𝕜] (S : Finset (Y × 𝕜))
    (hcont : ∀ y ∈ S, Continuous (fun x : E ↦ (HasPairing.pairing x y.1 : 𝕜))) :
    IsClosed ((⋂ y ∈ S, closedHalfSpaceLE y.1 y.2) : Set E) :=
  isClosed_iInter_closedHalfSpaceLE (𝕜 := 𝕜) (E := E) (Y := Y) S hcont

/-- Pairing bridge: a polyhedral set is closed when all pairing evaluations
`x ↦ ⟪x, y⟫ₚ` are continuous in the ambient topology. -/
theorem IsPolyhedral.isClosed_of_forall_continuous {Y : Type _}
    [HasPairing E Y 𝕜]
    {s : Set E} (hs : s.IsPolyhedral 𝕜 Y)
    (hcont : ∀ y : Y, Continuous (fun x : E ↦ (HasPairing.pairing x y : 𝕜))) : IsClosed s := by
  rcases hs with ⟨S, rfl⟩
  exact isClosed_iInter_closedHalfSpaceLE_of_forall_continuous (𝕜 := 𝕜) (E := E) (Y := Y) S
    (fun y hy ↦ hcont y.1)

end Set

end TopologicalPairingBridge

section TopologicalBridgeFiniteDimensional

variable {𝕜 : Type u} {E : Type v}
variable [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [Preorder 𝕜] [ClosedIicTopology 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable [T2Space E] [FiniteDimensional 𝕜 E]
variable {Y : Type _}
variable [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing E Y 𝕜]

/-- Every pairing-linear polyhedral set is closed in a finite-dimensional topological
`𝕜`-module. -/
theorem Set.IsPolyhedral.isClosed_of_finiteDimensional {s : Set E} (hs : s.IsPolyhedral 𝕜 Y) :
    IsClosed s :=
  hs.isClosed_of_forall_continuous fun y ↦ by
    have hycont : Continuous ((HasLinearPairing.pairingLinear.flip y : E →ₗ[𝕜] 𝕜)) := by
      simpa using
        (LinearMap.continuous_of_finiteDimensional
          (f := (HasLinearPairing.pairingLinear.flip y : E →ₗ[𝕜] 𝕜)))
    simpa [HasLinearPairing.pairing_eq_pairingLinear] using hycont

end TopologicalBridgeFiniteDimensional
