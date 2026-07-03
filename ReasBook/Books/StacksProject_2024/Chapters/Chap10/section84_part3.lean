import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_10_84_5 (from Chap10) -/
universe u v w x y z

section

variable {R : Type u} {P : Type v}
variable [Ring R] [AddCommGroup P] [Module R P] [Module.Projective R P]

/-- A submodule is countably generated projective if, as an `R`-module, it is both countably
generated and projective. -/
class Submodule.IsCountablyGeneratedProjective (A : Submodule R P) : Prop where
  countablyGenerated : Module.CountablyGenerated R A
  projective : Module.Projective R A

namespace Module

/-- Helper for Theorem 10.84.5: the free rank-one module `R` is countably generated over itself. -/
lemma ring_isCountablyGenerated : Module.CountablyGenerated R R := by
  -- The singleton `{1}` spans the regular module.
  refine (Module.countablyGenerated_iff (R := R) (M := R)).2 ?_
  refine ⟨{1}, Set.to_countable _, ?_⟩
  rw [Submodule.span_singleton_eq_top_iff]
  intro x
  exact ⟨x, by simp⟩

/-- Helper for Theorem 10.84.5: each canonical inclusion into a direct sum is injective. -/
lemma lof_injective
    {ι : Type*} [DecidableEq ι] (A : ι → Type*)
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] (i : ι) :
    Function.Injective (DirectSum.lof R ι A i) := by
  -- Apply the matching component projection to recover the original coordinate.
  intro x y hxy
  simpa using congrArg (DirectSum.component R ι A i) hxy

/-- Helper for Theorem 10.84.5: the canonical summands of a direct sum form an internal family. -/
lemma range_lof_isInternal
    {ι : Type*} [DecidableEq ι] (A : ι → Type*)
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] :
    DirectSum.IsInternal (fun i ↦ LinearMap.range (DirectSum.lof R ι A i)) := by
  classical
  let rangeEquiv : (i : ι) → A i ≃ₗ[R] LinearMap.range (DirectSum.lof R ι A i) :=
    fun i ↦
      LinearEquiv.ofBijective ((DirectSum.lof R ι A i).rangeRestrict) <| by
        constructor
        · -- The range-restricted inclusion is injective because `lof i` is.
          rw [LinearMap.injective_rangeRestrict_iff]
          exact Module.lof_injective (R := R) A i
        · -- Surjectivity is built into `rangeRestrict`.
          exact LinearMap.surjective_rangeRestrict (DirectSum.lof R ι A i)
  let decompose :
      DirectSum ι A →ₗ[R] DirectSum ι (fun i ↦ LinearMap.range (DirectSum.lof R ι A i)) :=
    (DirectSum.congrLinearEquiv (R := R) rangeEquiv).toLinearMap
  letI :
      DirectSum.Decomposition (fun i ↦ LinearMap.range (DirectSum.lof R ι A i)) :=
    DirectSum.Decomposition.ofLinearMap
      (ℳ := fun i ↦ LinearMap.range (DirectSum.lof R ι A i))
      decompose
      (by
        -- On each generator, recomposing after `decompose` returns the original `lof` term.
        apply DirectSum.linearMap_ext (R := R) (ι := ι) (M := A)
        intro i
        apply LinearMap.ext
        intro x
        ext j
        by_cases hji : j = i
        · subst hji
          simp [decompose, DirectSum.congrLinearEquiv_toLinearMap, rangeEquiv]
        · simp [decompose, DirectSum.congrLinearEquiv_toLinearMap, rangeEquiv])
      (by
        -- On each range generator, surjectivity of `rangeRestrict` reduces back to a `lof` term.
        apply DirectSum.linearMap_ext
          (R := R) (ι := ι) (M := fun i ↦ LinearMap.range (DirectSum.lof R ι A i))
        intro i
        apply LinearMap.ext
        intro x
        rcases x with ⟨x, hx⟩
        rcases hx with ⟨y, rfl⟩
        simpa [LinearMap.comp_apply, decompose, DirectSum.congrLinearEquiv_toLinearMap, rangeEquiv]
          using congrArg
            (DirectSum.lof R ι (fun j ↦ LinearMap.range (DirectSum.lof R ι A j)) i)
            (Subtype.ext (by rfl) :
              (DirectSum.lof R ι A i).rangeRestrict y =
                ⟨(DirectSum.lof R ι A i) y, by exact ⟨y, rfl⟩⟩))
  -- The packaged decomposition is exactly the required internality statement.
  exact DirectSum.Decomposition.isInternal
    (ℳ := fun i ↦ LinearMap.range (DirectSum.lof R ι A i))

/-- Helper for Theorem 10.84.5: the image of a countably generated submodule under a linear map is
again countably generated, without imposing a common universe on source and target modules. -/
lemma countablyGenerated_map_explicit
    {M : Type y} [AddCommGroup M] [Module R M]
    {P' : Type z} [AddCommGroup P'] [Module R P']
    (f : M →ₗ[R] P') {Q : Submodule R M}
    (hQ : Q.CountablyGenerated) :
    (Q.map f).CountablyGenerated := by
  rcases (Submodule.countablyGenerated_iff (P := Q)).mp hQ with ⟨s, hs, hspan⟩
  -- Push the chosen spanning set through the linear map.
  refine (Submodule.countablyGenerated_iff (P := Q.map f)).2 ?_
  refine ⟨f '' s, hs.image f, ?_⟩
  calc
    Submodule.span R (f '' s) = (Submodule.span R s).map f := by
      rw [Submodule.map_span]
    _ = Q.map f := by
      rw [hspan]

/-- Helper for Theorem 10.84.5: a finitely supported function module is an internal direct sum of
countably generated coordinate summands. -/
lemma finsupp_isDirectSumOfCountablyGenerated
    {ι : Type x} :
    Module.IsDirectSumOfCountablyGenerated.{u, max u x, x} R (ι →₀ R) := by
  classical
  let summand : ι → Submodule R (ι →₀ R) :=
    fun i ↦ LinearMap.range (Finsupp.lsingle (R := R) (M := R) i)
  -- Use the coordinate ranges as the direct-sum family.
  refine ⟨ι, inferInstance, summand, ?_, ?_⟩
  · -- The coordinate ranges are pairwise disjoint and their supremum is all of `ι →₀ R`.
    exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr <| by
      constructor
      · -- The `lsingle` ranges are disjoint from the supremum of all the other coordinates.
        exact (iSupIndep_def (t := summand)).2 <| by
          intro i
          have hdisjSets : Disjoint ({i} : Set ι) {j : ι | j ≠ i} := by
            simp
          simpa [summand, iSup_subtype] using
            (Finsupp.disjoint_lsingle_lsingle
              (R := R) (M := R) ({i} : Set ι) {j : ι | j ≠ i} hdisjSets)
      · simpa [summand] using (Finsupp.iSup_lsingle_range (R := R) (M := R) (α := ι))
  · intro i
    -- Each coordinate range is the image of the countably generated module `R`.
    simpa [summand, Submodule.map_top] using
      (Module.countablyGenerated_map_explicit
        (R := R)
        (M := R)
        (P' := ι →₀ R)
        (f := Finsupp.lsingle (R := R) (M := R) i)
        (Q := (⊤ : Submodule R R))
        (Module.ring_isCountablyGenerated (R := R)))

/-- Helper for Theorem 10.84.5: an explicit direct-sum decomposition transports across a linear
equivalence even when the source and target modules live in different universes. -/
lemma isDirectSumOfCountablyGenerated_via_linearEquiv_explicit
    {M : Type y} [AddCommGroup M] [Module R M]
    {P' : Type z} [AddCommGroup P'] [Module R P']
    (e : P' ≃ₗ[R] M) (hM : Module.IsDirectSumOfCountablyGenerated.{u, y, x} R M) :
    Module.IsDirectSumOfCountablyGenerated.{u, z, x} R P' := by
  rcases hM with ⟨ι, _, summand, hsum, hcount⟩
  classical
  -- Transport each summand along the inverse equivalence.
  refine ⟨ι, inferInstance, fun i ↦ (summand i).map (e.symm : M →ₗ[R] P'), ?_, ?_⟩
  · -- Internality is preserved because `e.symm` is injective and surjective.
    exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr <| by
      constructor
      · exact LinearMap.iSupIndep_map (e.symm : M →ₗ[R] P') e.symm.injective
          hsum.submodule_iSupIndep
      · calc
          iSup (fun i ↦ (summand i).map (e.symm : M →ₗ[R] P'))
              = (iSup summand).map (e.symm : M →ₗ[R] P') := by
                  rw [Submodule.map_iSup]
          _ = (⊤ : Submodule R M).map (e.symm : M →ₗ[R] P') := by
                  rw [hsum.submodule_iSup_eq_top]
          _ = ⊤ := by
                  rw [Submodule.map_top]
                  exact LinearMap.range_eq_top.2 e.symm.surjective
  · intro i
    -- Countable spanning sets push forward along linear maps.
    exact Module.countablyGenerated_map_explicit
      (R := R) (f := (e.symm : M →ₗ[R] P')) (hcount i)

/-- Helper for Theorem 10.84.5: every free module is an internal direct sum of countably generated
submodules, after reindexing its basis into the target universe. -/
lemma free_isDirectSumOfCountablyGenerated
    {M : Type x} [AddCommGroup M] [Module R M] [Module.Free R M] :
    Module.IsDirectSumOfCountablyGenerated.{u, x, max x w} R M := by
  let b := Module.Free.chooseBasis R M
  let e : M ≃ₗ[R] (ULift.{w} (Module.Free.ChooseBasisIndex R M) →₀ R) :=
    b.repr.trans (Finsupp.domLCongr Equiv.ulift.symm)
  -- Transport the canonical coordinate decomposition across the chosen basis.
  exact Module.isDirectSumOfCountablyGenerated_via_linearEquiv_explicit (R := R) e <|
    Module.finsupp_isDirectSumOfCountablyGenerated
      (R := R) (ι := ULift.{w} (Module.Free.ChooseBasisIndex R M))

end Module

namespace Submodule

/-- Helper for Theorem 10.84.5: in an internal direct sum, a fixed summand is complemented by the
supremum of all the other summands. -/
lemma internal_summand_isCompl_iSup_others
    {ι : Type*} [DecidableEq ι] (A : ι → Submodule R P)
    (hA : DirectSum.IsInternal A) (i : ι) :
    IsCompl (A i) (⨆ j : {j // j ≠ i}, A j.1) := by
  let others : Submodule R P := ⨆ j : {j // j ≠ i}, A j.1
  have hindep : iSupIndep A := hA.submodule_iSupIndep
  have hdisj : Disjoint (A i) others := by
    -- Independence already gives the required disjointness after rewriting the indexing type.
    simpa [others, iSup_subtype] using (hindep i)
  have hAi_sup : A i ⊔ others = iSup A := by
    refine le_antisymm ?_ ?_
    · -- Both the chosen summand and the complementary supremum lie inside the total supremum.
      refine sup_le (le_iSup A i) ?_
      exact iSup_le fun j ↦ le_iSup A j.1
    · -- Every summand lies either at the chosen index or among the complementary indices.
      refine iSup_le fun j ↦ ?_
      by_cases hji : j = i
      · simpa [hji] using le_sup_of_le_left (show A i ≤ A i from le_rfl)
      · exact le_sup_of_le_right (le_iSup (fun j : {j // j ≠ i} ↦ A j.1) ⟨j, hji⟩)
  have hsup : A i ⊔ others = ⊤ := by
    -- Replace the total supremum by `⊤` using internality.
    calc
      A i ⊔ others = iSup A := hAi_sup
      _ = ⊤ := hA.submodule_iSup_eq_top
  exact ⟨hdisj, codisjoint_iff.mpr hsup⟩

/-- Helper for Theorem 10.84.5: each countably generated summand in an internal decomposition of a
projective module is itself countably generated and projective. -/
lemma isCountablyGeneratedProjective_of_internal_projective
    {ι : Type*} [DecidableEq ι] (A : ι → Submodule R P)
    (hA : DirectSum.IsInternal A) (hcount : ∀ i, (A i).CountablyGenerated) :
    ∀ i, Submodule.IsCountablyGeneratedProjective (A i) := by
  intro i
  let others : Submodule R P := ⨆ j : {j // j ≠ i}, A j.1
  have hCompl : IsCompl (A i) others :=
    Submodule.internal_summand_isCompl_iSup_others (R := R) (P := P) A hA i
  refine ⟨?_, ?_⟩
  · -- Convert the countable generation statement from the ambient submodule language to modules.
    exact (Submodule.countablyGenerated_iff_moduleCountablyGenerated
      (R := R) (M := P) (Q := A i)).mp (hcount i)
  · -- The complementary projection splits the inclusion of the summand into the projective module.
    exact Module.Projective.of_split (A i).subtype
      ((A i).linearProjOfIsCompl others hCompl)
      (Submodule.linearProjOfIsCompl_comp_subtype hCompl)

end Submodule

-- Proof sketch: realize `P` as a direct summand of a free `R`-module. Decompose the free module
-- as the internal direct sum of its rank-one free summands, which are countably generated and
-- projective, then apply the direct-summand result from Theorem `10.84.4` and observe that each
-- resulting summand remains projective.
/-- Theorem 10.84.5: if `P` is a projective `R`-module, then `P` is an internal direct sum of
countably generated projective `R`-submodules. -/
theorem projective_isDirectSumOfCountablyGeneratedProjective :
    ∃ (ι : Type (max u v w)) (_ : DecidableEq ι) (A : ι → Submodule R P),
      DirectSum.IsInternal A ∧ ∀ i, Submodule.IsCountablyGeneratedProjective (A i) := by
  classical
  -- Realize `P` as a split summand of a free module.
  obtain ⟨F, hFAdd, hFModule, hFFree, i, s, hs⟩ :=
    (Module.Projective.iff_split (R := R) (P := P)).mp
      (inferInstance : Module.Projective R P)
  letI : AddCommMonoid F := hFAdd
  letI : Module R F := hFModule
  letI : Module.Free R F := hFFree
  letI : AddCommGroup F := Module.addCommMonoidToAddCommGroup R (M := F)
  let eP : ULift.{u} P ≃ₗ[R] P := ULift.moduleEquiv
  let iLift : ULift.{u} P →ₗ[R] F := i.comp eP.toLinearMap
  let sLift : F →ₗ[R] ULift.{u} P := eP.symm.toLinearMap.comp s
  have hsLift : sLift.comp iLift = LinearMap.id := by
    -- The split identity survives after moving `P` into the ambient universe.
    ext x
    simpa [iLift, sLift, eP, LinearMap.comp_apply] using
      congrArg (fun f : P →ₗ[R] P => f x.down) hs
  have hF :
      Module.IsDirectSumOfCountablyGenerated R F := by
    -- Decompose the ambient free module by its basis vectors.
    exact Module.free_isDirectSumOfCountablyGenerated (R := R) (M := F)
  have hLift :
      Module.IsDirectSumOfCountablyGenerated R (ULift.{u} P) := by
    -- Apply Theorem 10.84.4 to the lifted copy of `P`, which matches the free ambient universe.
    exact Module.directSummand_isDirectSumOfCountablyGenerated
      (R := R) (M := F) iLift sLift hsLift hF
  have hP :
      Module.IsDirectSumOfCountablyGenerated R P := by
    -- Transport the lifted decomposition back down to the original module.
    exact Module.isDirectSumOfCountablyGenerated_via_linearEquiv_explicit
      (R := R) eP.symm hLift
  rcases hP with
    ⟨ι, hι, A, hA, hcount⟩
  refine ⟨ι, hι, A, hA, ?_⟩
  -- Each descended summand stays projective because it is complemented inside the projective
  -- ambient module `P`.
  exact Submodule.isCountablyGeneratedProjective_of_internal_projective
    (R := R) (P := P) A hA hcount

end
