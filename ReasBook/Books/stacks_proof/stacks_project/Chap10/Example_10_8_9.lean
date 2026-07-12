import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Example_10_8_5
import StacksProject_2024.Chap10.Lemma_10_8_8
import Mathlib.Tactic.StacksAttribute

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

/-
Lemma 10.8.8 (1): for a directed system of complexes of `R`-modules, the stagewise homology
modules form a system over the directed set. This is formalized by `module_system_homology`.
-/
recall module_system_homology

/- Lemma 10.8.8 (2): the induced sequence on colimits is again a complex. -/
recall colimit_module_system_isComplex

/- Lemma 10.8.8 (3): the canonical comparison from the colimit of the stagewise homology modules
to the homology of the colimit complex is an isomorphism. -/
recall module_system_homology_comparison_isIso

noncomputable section

/-- The zero map `0 → ℤ` used at the source vertex of the counterexample span. -/
private abbrev forkZeroToInt : PUnit →ₗ[ℤ] ℤ :=
  0

/-- The identity map `ℤ → ℤ` used at the target vertices of the counterexample span. -/
private abbrev forkIntId : ℤ →ₗ[ℤ] ℤ :=
  LinearMap.id

/-- The source system `(0, \mathbf{Z}, \mathbf{Z}, 0, 0)` on the fork-shaped preorder used in
Example 10.8.9, written as the canonical walking-span diagram. -/
def forkColimitExactnessSource : WalkingSpan ⥤ ModuleCat ℤ :=
  span (ModuleCat.ofHom forkZeroToInt) (ModuleCat.ofHom forkZeroToInt)

/-- The constant target system `(\mathbf{Z}, \mathbf{Z}, \mathbf{Z}, 1, 1)` on the fork-shaped
preorder used in Example 10.8.9. -/
def forkColimitExactnessTarget : WalkingSpan ⥤ ModuleCat ℤ :=
  span (ModuleCat.ofHom forkIntId) (ModuleCat.ofHom forkIntId)

private instance : Subsingleton ↑(forkColimitExactnessSource.obj WalkingSpan.zero) := by
  change Subsingleton PUnit
  infer_instance

/-- The morphism of systems
`(0, \mathbf{Z}, \mathbf{Z}, 0, 0) → (\mathbf{Z}, \mathbf{Z}, \mathbf{Z}, 1, 1)` from
Example 10.8.9. -/
def forkColimitExactnessHom : forkColimitExactnessSource ⟶ forkColimitExactnessTarget :=
  spanHomMk 0 (𝟙 _) (𝟙 _)

private theorem forkColimitExactnessHom_app_mono (i : WalkingSpan) :
    Mono (forkColimitExactnessHom.app i) := by
  rcases i with _ | (_ | _)
  · exact (ModuleCat.mono_iff_injective _).2 <| by
      intro x y h
      exact Subsingleton.elim _ _
  · simpa [forkColimitExactnessSource, forkColimitExactnessTarget, forkColimitExactnessHom,
      forkZeroToInt, forkIntId] using
      (show Mono (𝟙 (ModuleCat.of ℤ ℤ)) from inferInstance)
  · simpa [forkColimitExactnessSource, forkColimitExactnessTarget, forkColimitExactnessHom,
      forkZeroToInt, forkIntId] using
      (show Mono (𝟙 (ModuleCat.of ℤ ℤ)) from inferInstance)

/-- Helper for Chap10 Example 10 8 9: the identity and zero projections coequalize the two
zero source maps. -/
private theorem forkSourceLeftProjectionComm :
    ModuleCat.ofHom forkZeroToInt ≫ ModuleCat.ofHom (LinearMap.id : ℤ →ₗ[ℤ] ℤ) =
      ModuleCat.ofHom forkZeroToInt ≫ ModuleCat.ofHom (0 : ℤ →ₗ[ℤ] ℤ) := by
  -- The two composites out of the singleton module are both the zero linear map.
  apply ModuleCat.hom_ext
  ext x
  simp [forkZeroToInt]

/-- Helper for Chap10 Example 10 8 9: a cocone from the source fork separating the left and
right integer summands. -/
private def forkSourceLeftProjection :
    PushoutCocone (ModuleCat.ofHom forkZeroToInt) (ModuleCat.ofHom forkZeroToInt) :=
  PushoutCocone.mk
    (ModuleCat.ofHom (LinearMap.id : ℤ →ₗ[ℤ] ℤ))
    (ModuleCat.ofHom (0 : ℤ →ₗ[ℤ] ℤ))
    forkSourceLeftProjectionComm

/-- Helper for Chap10 Example 10 8 9: nonzero equal integer elements in the two source legs stay
distinct in the source colimit. -/
private lemma forkSourceColimitLeftNeRightOfNeZero (n : ℤ) (hn : n ≠ 0) :
    (colimit.ι forkColimitExactnessSource WalkingSpan.left).hom n ≠
      (colimit.ι forkColimitExactnessSource WalkingSpan.right).hom n := by
  intro hEq
  let q : (colimit forkColimitExactnessSource : ModuleCat ℤ) ⟶ ModuleCat.of ℤ ℤ :=
    colimit.desc forkColimitExactnessSource forkSourceLeftProjection
  -- Composing the left colimit leg with the separating cocone recovers the input integer.
  have hleft : q.hom ((colimit.ι forkColimitExactnessSource WalkingSpan.left).hom n) = n := by
    have h := LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom
        (colimit.ι_desc forkSourceLeftProjection WalkingSpan.left)) n
    simpa [q, forkSourceLeftProjection, forkIntId] using h
  -- Composing the right colimit leg with the same cocone sends every integer to zero.
  have hright : q.hom ((colimit.ι forkColimitExactnessSource WalkingSpan.right).hom n) = 0 := by
    have h := LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom
        (colimit.ι_desc forkSourceLeftProjection WalkingSpan.right)) n
    simpa [q, forkSourceLeftProjection] using h
  -- An equality of the two colimit-leg elements would therefore force `n = 0`.
  have hnzero : n = 0 := by
    calc
      n = q.hom ((colimit.ι forkColimitExactnessSource WalkingSpan.left).hom n) := hleft.symm
      _ = q.hom ((colimit.ι forkColimitExactnessSource WalkingSpan.right).hom n) := by
        rw [hEq]
      _ = 0 := hright
  exact hn hnzero

/-- Helper for Chap10 Example 10 8 9: the target colimit identifies the left and right integer
legs. -/
private lemma forkTargetColimitLeftEqRight (n : ℤ) :
    (colimit.ι forkColimitExactnessTarget WalkingSpan.left).hom n =
      (colimit.ι forkColimitExactnessTarget WalkingSpan.right).hom n := by
  -- The `fst` relation identifies the left leg with the central leg because the map is `id`.
  have hleftZero :
      (colimit.ι forkColimitExactnessTarget WalkingSpan.left).hom n =
        (colimit.ι forkColimitExactnessTarget WalkingSpan.zero).hom n := by
    have h := LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom
        (colimit.w forkColimitExactnessTarget WalkingSpan.Hom.fst)) n
    simpa [forkColimitExactnessTarget, forkIntId] using h
  -- The `snd` relation gives the same identification for the right leg.
  have hrightZero :
      (colimit.ι forkColimitExactnessTarget WalkingSpan.right).hom n =
        (colimit.ι forkColimitExactnessTarget WalkingSpan.zero).hom n := by
    have h := LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom
        (colimit.w forkColimitExactnessTarget WalkingSpan.Hom.snd)) n
    simpa [forkColimitExactnessTarget, forkIntId] using h
  exact hleftZero.trans hrightZero.symm

/-- Helper for Chap10 Example 10 8 9: the induced colimit map sends the left and right source
classes of any integer to the same target-colimit element. -/
private lemma forkColimitExactnessHomColimitLeftEqRight (n : ℤ) :
    (colim.map forkColimitExactnessHom).hom
        ((colimit.ι forkColimitExactnessSource WalkingSpan.left).hom n) =
      (colim.map forkColimitExactnessHom).hom
        ((colimit.ι forkColimitExactnessSource WalkingSpan.right).hom n) := by
  -- Naturality of `colim.map` transports the left source leg to the left target leg.
  have hleft :
      (colim.map forkColimitExactnessHom).hom
          ((colimit.ι forkColimitExactnessSource WalkingSpan.left).hom n) =
        (colimit.ι forkColimitExactnessTarget WalkingSpan.left).hom n := by
    have h := LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom
        (colimit.ι_map forkColimitExactnessHom WalkingSpan.left)) n
    simpa [forkColimitExactnessSource, forkColimitExactnessTarget, forkColimitExactnessHom,
      forkZeroToInt, forkIntId] using h
  -- The same naturality computation transports the right source leg to the right target leg.
  have hright :
      (colim.map forkColimitExactnessHom).hom
          ((colimit.ι forkColimitExactnessSource WalkingSpan.right).hom n) =
        (colimit.ι forkColimitExactnessTarget WalkingSpan.right).hom n := by
    have h := LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom
        (colimit.ι_map forkColimitExactnessHom WalkingSpan.right)) n
    simpa [forkColimitExactnessSource, forkColimitExactnessTarget, forkColimitExactnessHom,
      forkZeroToInt, forkIntId] using h
  -- The target colimit already identifies those transported left and right elements.
  exact hleft.trans ((forkTargetColimitLeftEqRight n).trans hright.symm)

/-- Chap10 Example 10 8 9: the induced map on colimits for the fork counterexample is not
injective. -/
private theorem forkColimitExactnessHom_colimit_not_injective :
    ¬ Function.Injective (colim.map forkColimitExactnessHom).hom := by
  intro hInjective
  -- The images of the two source-colimit classes represented by `1` are equal in the target.
  have hImageEq := forkColimitExactnessHomColimitLeftEqRight (1 : ℤ)
  -- Injectivity would force those two source-colimit classes to be equal.
  have hSourceEq := hInjective hImageEq
  -- The separating cocone shows that the same two classes are distinct.
  have hone : (1 : ℤ) ≠ 0 := by
    norm_num
  exact forkSourceColimitLeftNeRightOfNeZero (1 : ℤ) hone hSourceEq

private theorem forkColimitExactnessHom_colimit_not_mono :
    ¬ Mono (colim.map forkColimitExactnessHom) := by
  intro h
  exact forkColimitExactnessHom_colimit_not_injective ((ModuleCat.mono_iff_injective _).1 h)

private theorem forkColimitExactnessHom_mono : Mono forkColimitExactnessHom := by
  rw [NatTrans.mono_iff_mono_app]
  exact forkColimitExactnessHom_app_mono

/-- Consequence of Chap10 Example 10 8 9: on the fork-shaped preorder `a < b`, `a < c`, the morphism of systems
`(0, \mathbf{Z}, \mathbf{Z}, 0, 0) → (\mathbf{Z}, \mathbf{Z}, \mathbf{Z}, 1, 1)` is a
monomorphism, but the induced map on colimits is not. Hence the result of Lemma 10.8.8 is false
for general systems. -/
@[stacks 00DC]
theorem fork_colimit_counterexample_to_exactness :
    Mono forkColimitExactnessHom ∧ ¬ Mono (colim.map forkColimitExactnessHom) := by
  constructor
  · exact forkColimitExactnessHom_mono
  · exact forkColimitExactnessHom_colimit_not_mono

/-- Textbook injectivity formulation of Example 10.8.9. -/
theorem fork_colimit_counterexample_to_exactness_injective :
    (∀ i : WalkingSpan, Function.Injective (forkColimitExactnessHom.app i).hom) ∧
      ¬ Function.Injective (colim.map forkColimitExactnessHom).hom := by
  refine ⟨?_, forkColimitExactnessHom_colimit_not_injective⟩
  intro i
  exact (ModuleCat.mono_iff_injective _).1 (forkColimitExactnessHom_app_mono i)

end
