module

public import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactness.SigmaCompact

public section

open Set TopologicalSpace

universe u

namespace OnePoint

/-- The one-point compactification of a locally compact second-countable space is
second-countable. -/
noncomputable instance {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X]
    [T2Space X] [SecondCountableTopology X] : SecondCountableTopology (OnePoint X) := by
  let K : CompactExhaustion X := CompactExhaustion.choice X
  let B : Set (Set (OnePoint X)) :=
    ((fun s : Set X ↦ ((↑) : X → OnePoint X) '' s) '' countableBasis X) ∪
      range (fun n ↦ (((↑) : X → OnePoint X) '' K n)ᶜ)
  have hB : IsTopologicalBasis B := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro _ (⟨s, hs, rfl⟩ | ⟨n, rfl⟩)
      · exact isOpen_image_coe.2 ((isBasis_countableBasis X).isOpen hs)
      · exact isOpen_compl_image_coe.2 ⟨(K.isCompact n).isClosed, K.isCompact n⟩
    · intro z U hzU hU
      induction z using OnePoint.rec with
      | infty =>
          have hcompact : IsCompact (((↑) : X → OnePoint X) ⁻¹' U)ᶜ :=
            ((isOpen_iff_of_mem hzU).1 hU).2
          obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hcompact
          refine ⟨(((↑) : X → OnePoint X) '' K n)ᶜ, Or.inr ⟨n, rfl⟩,
            infty_notMem_image_coe, ?_⟩
          rintro y hy
          induction y using OnePoint.rec with
          | infty => exact hzU
          | coe x =>
              rw [mem_compl_iff, mem_image] at hy
              by_contra hxU
              exact hy ⟨x, hn hxU, rfl⟩
      | coe x =>
          have hpreOpen : IsOpen (((↑) : X → OnePoint X) ⁻¹' U) := (isOpen_def.1 hU).2
          have hxpre : x ∈ ((↑) : X → OnePoint X) ⁻¹' U := hzU
          obtain ⟨s, hsB, hxs, hsU⟩ :=
            (isBasis_countableBasis X).isOpen_iff.1 hpreOpen x hxpre
          refine ⟨((↑) : X → OnePoint X) '' s, Or.inl ⟨s, hsB, rfl⟩, ⟨x, hxs, rfl⟩, ?_⟩
          rintro _ ⟨y, hy, rfl⟩
          exact hsU hy
  exact hB.secondCountableTopology <|
    ((countable_countableBasis X).image _).union (Set.countable_range _)

end OnePoint

end
