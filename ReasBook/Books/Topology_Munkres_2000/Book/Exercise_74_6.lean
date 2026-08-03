module

public import Topology_Munkres_2000.Book.Theorem_74_3
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

public section

namespace OrientableSurfacePresentation

-- The Boolean coordinate is deliberately ignored so each surface commutator is killed.
/-- Helper for Exercise 74.6: project each paired surface generator to the first free
generator at index zero and to the second free generator at every other index. -/
def twoGeneratorProjection (n : ℕ) : Fin n × Bool → Fin 2 :=
  fun ib ↦ if ib.1.val = 0 then 0 else 1

/-- Helper for Exercise 74.6: the projection to the two free generators is surjective
when the surface has at least two handles. -/
lemma twoGeneratorProjection_surjective (n : ℕ) (hn : 1 < n) :
    Function.Surjective (twoGeneratorProjection n) := by
  -- The source indices zero and one map to the two respective target indices.
  intro j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · have hzero : twoGeneratorProjection n (⟨0, Nat.zero_lt_of_lt hn⟩, false) = 0 := by
      simp [twoGeneratorProjection]
    exact ⟨(⟨0, Nat.zero_lt_of_lt hn⟩, false), hzero⟩
  · have hk : k = 0 := Fin.eq_zero k
    subst k
    have hone : twoGeneratorProjection n (⟨1, hn⟩, false) = 1 := by
      simp [twoGeneratorProjection]
    exact ⟨(⟨1, hn⟩, false), hone⟩

/-- Helper for Exercise 74.6: the two-generator projection kills the orientable
surface relator. -/
lemma twoGeneratorProjection_relator_eq_one (n : ℕ) :
    FreeGroup.map (twoGeneratorProjection n) (OrientableSurfaceGroup.relator n) = 1 := by
  -- Each paired pair has the same image, so every commutator in the product vanishes.
  rw [OrientableSurfaceGroup.relator_def, map_list_prod]
  apply List.prod_eq_one
  intro g hg
  obtain ⟨surfaceCommutator, hsurfaceCommutator, rfl⟩ := List.mem_map.mp hg
  rw [List.mem_ofFn'] at hsurfaceCommutator
  obtain ⟨i, rfl⟩ := hsurfaceCommutator
  simp only [map_commutatorElement, FreeGroup.map.of, twoGeneratorProjection,
    commutatorElement_self]

/-- Helper for Exercise 74.6: for genus at least two, the surface fundamental group
surjects onto the free group on two generators. -/
theorem exists_surjective_to_freeGroup_finTwo (n : ℕ) (hn : 1 < n)
    (x : nFoldTorus n (Nat.zero_lt_of_lt hn)) :
    ∃ φ : FundamentalGroup (nFoldTorus n (Nat.zero_lt_of_lt hn)) x →* FreeGroup (Fin 2),
      Function.Surjective φ := by
  -- The relator calculation lets the generator projection descend to the presentation.
  have hrel : ∀ r ∈ ({OrientableSurfaceGroup.relator n} :
      Set (FreeGroup (Fin n × Bool))),
      FreeGroup.lift (FreeGroup.of ∘ twoGeneratorProjection n) r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst r
    rw [← FreeGroup.map_eq_lift]
    exact twoGeneratorProjection_relator_eq_one n
  let presentationHom : OrientableSurfaceGroup.Presentation n →* FreeGroup (Fin 2) :=
    PresentedGroup.toGroup hrel
  -- On the free group, the descended map agrees with the original generator map.
  have hpresentation_comp :
      presentationHom.comp
          (PresentedGroup.mk ({OrientableSurfaceGroup.relator n} :
            Set (FreeGroup (Fin n × Bool)))) =
        FreeGroup.map (twoGeneratorProjection n) := by
    apply FreeGroup.ext_hom
    intro a
    change PresentedGroup.toGroup hrel (PresentedGroup.of a) =
      FreeGroup.of (twoGeneratorProjection n a)
    exact PresentedGroup.toGroup.of hrel
  -- Surjectivity before descent therefore supplies surjectivity after descent.
  have hpresentation_surjective : Function.Surjective presentationHom := by
    intro y
    obtain ⟨z, hz⟩ :=
      FreeGroup.map_surjective (twoGeneratorProjection_surjective n hn) y
    refine ⟨PresentedGroup.mk
      ({OrientableSurfaceGroup.relator n} : Set (FreeGroup (Fin n × Bool))) z, ?_⟩
    have hz' := DFunLike.congr_fun hpresentation_comp z
    exact hz'.trans hz
  -- Compose the descended map with the presentation equivalence from Theorem 74.3.
  obtain ⟨e⟩ := fundamentalGroupMulEquiv n (Nat.zero_lt_of_lt hn) x
  let φ := presentationHom.comp e.toMonoidHom
  have hφ : Function.Surjective φ := hpresentation_surjective.comp e.surjective
  exact ⟨φ, hφ⟩

/-- Helper for Exercise 74.6: the free group on two generators is not commutative. -/
lemma freeGroupFinTwo_not_isMulCommutative :
    ¬ IsMulCommutative (FreeGroup (Fin 2)) := by
  -- Commutativity would identify the two distinct positive reduced words of length two.
  intro hcomm
  have hwords :
      FreeGroup.mk [((0 : Fin 2), true), ((1 : Fin 2), true)] =
        FreeGroup.mk [((1 : Fin 2), true), ((0 : Fin 2), true)] := by
    simpa [FreeGroup.of, FreeGroup.mul_mk] using
      hcomm.is_comm.comm (FreeGroup.of (0 : Fin 2)) (FreeGroup.of (1 : Fin 2))
  have hleft :
      FreeGroup.IsReduced [((0 : Fin 2), true), ((1 : Fin 2), true)] := by
    simp [FreeGroup.isReduced_cons_cons]
  have hright :
      FreeGroup.IsReduced [((1 : Fin 2), true), ((0 : Fin 2), true)] := by
    simp [FreeGroup.isReduced_cons_cons]
  -- A common reduct of reduced words must equal both, contradicting their first letters.
  obtain ⟨word, hwordLeft, hwordRight⟩ := FreeGroup.Red.exact.mp hwords
  have hwordLeftEq := hleft.red_iff_eq.mp hwordLeft
  have hwordRightEq := hright.red_iff_eq.mp hwordRight
  have :
      [((0 : Fin 2), true), ((1 : Fin 2), true)] =
        [((1 : Fin 2), true), ((0 : Fin 2), true)] :=
    hwordLeftEq.symm.trans hwordRightEq
  simp at this

/-- Exercise 74.6: If `n > 1`, the fundamental group of the `n`-fold torus is not
abelian, for every choice of basepoint. -/
theorem fundamentalGroup_not_isMulCommutative (n : ℕ) (hn : 1 < n)
    (x : nFoldTorus n (Nat.zero_lt_of_lt hn)) :
    ¬ IsMulCommutative
      (FundamentalGroup (nFoldTorus n (Nat.zero_lt_of_lt hn)) x) := by
  -- Any alleged commutativity descends along the surjection to the rank-two free group.
  intro hcomm
  obtain ⟨φ, hφ⟩ := exists_surjective_to_freeGroup_finTwo n hn x
  exact freeGroupFinTwo_not_isMulCommutative
    (Function.Surjective.mul_comm (f := φ) hφ hcomm)

end OrientableSurfacePresentation
