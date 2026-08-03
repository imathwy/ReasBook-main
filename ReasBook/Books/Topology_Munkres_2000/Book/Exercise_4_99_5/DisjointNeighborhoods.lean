module

public import Mathlib.Topology.NatEmbedding
public import Mathlib.Topology.Compactification.StoneCech

public section

open Function Filter Set Topology

/-- Helper for Exercise 4.99.5: an accumulated set meets pairwise disjoint ambient open sets. -/
lemma AccPt.existsPairwiseDisjointOpen_meets {X : Type*} [TopologicalSpace X] [T2Space X]
    {C : Set X} {x : X} (hx : AccPt x (Filter.principal C)) :
    ∃ U : ℕ → Set X, (∀ n, IsOpen (U n)) ∧
      (∀ n, (U n ∩ C).Nonempty) ∧ Pairwise (Disjoint on U) := by
  -- Recursively separate a fresh point of `C` from `x` and all earlier open sets.
  have : Std.Symm (Disjoint on (id : Set X → Set X)) :=
    ⟨fun _ _ h ↦ h.symm⟩
  obtain ⟨U, hU, hdisj⟩ :=
      exists_seq_of_forall_finset_exists'
        (fun V : Set X ↦ (V ∩ C).Nonempty ∧ IsOpen V ∧ Vᶜ ∈ 𝓝 x)
        Disjoint (fun S hS ↦ by
          have hnear : (⋂ V ∈ S, interior (Vᶜ)) \ {x} ∈ 𝓝[≠] x :=
            inter_mem_inf ((biInter_finset_mem _).2
              (fun V hV ↦ interior_mem_nhds.2 (hS V hV).2.2))
              (mem_principal_self {x}ᶜ)
          have hboth : ((⋂ V ∈ S, interior (Vᶜ)) \ {x}) ∩ C ∈
              𝓝[≠] x ⊓ Filter.principal C :=
            inter_mem_inf hnear (mem_principal_self C)
          obtain ⟨y, hyNear, hyC⟩ := hx.nonempty_of_mem hboth
          have hyx : y ≠ x := by
            exact hyNear.2
          obtain ⟨V, W, hVopen, hWopen, hyV, hxW, hVW⟩ := t2_separation hyx
          refine ⟨V ∩ ⋂ Z ∈ S, interior (Zᶜ), ?_, fun Z hZ ↦ ?_⟩
          · refine ⟨⟨y, ⟨hyV, hyNear.1⟩, hyC⟩,
              hVopen.inter (isOpen_biInter_finset fun _ _ ↦ isOpen_interior), ?_⟩
            refine mem_of_superset (hWopen.mem_nhds hxW) ?_
            intro z hzW hzNew
            exact (disjoint_left.mp hVW) hzNew.1 hzW
          · exact disjoint_left.mpr (fun z hzZ hzNew ↦
              interior_subset (mem_iInter₂.mp hzNew.2 Z hZ) hzZ))
  exact ⟨U, fun n ↦ (hU n).2.1, fun n ↦ (hU n).1, hdisj⟩
