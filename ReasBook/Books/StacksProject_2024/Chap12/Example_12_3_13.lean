import StacksProject_2024.Chap12.Lemma_12_19_2

open CategoryTheory
open CategoryTheory.Limits
open Abelian.OfCoimageImageComparisonIsIso
open Function OrderDual
open ModuleCat

noncomputable section

universe w v u

namespace CategoryTheory

section Ring

variable (k : Type u) [Ring k]

private abbrev lineObject : ModuleCat k := ModuleCat.of k k

private noncomputable abbrev lineSubobject (S : Submodule k k) :
    Subobject (lineObject k) :=
  (ModuleCat.subobjectModule (lineObject k)).symm S

private theorem lineSubobject_mono {S T : Submodule k k} (h : S ≤ T) :
    lineSubobject k S ≤ lineSubobject k T :=
  (ModuleCat.subobjectModule (lineObject k)).symm.monotone h

private theorem topBotSubmoduleFiltration_antitone {P : ℤ → Prop} [DecidablePred P]
    (hP : Antitone P) :
    Antitone (fun i : ℤ ↦ if P i then (⊤ : Submodule k k) else ⊥) := by
  intro i j hij
  by_cases hj : P j
  · simp [hj, hP hij hj]
  · simp [hj]

/-- The filtered `k`-module `(V, F)` with `V = k` and `F^i V = V` for `i < 0`, `F^i V = 0`
for `i ≥ 0`. -/
private def strictNegativeFilteredLine : FilteredObject (ModuleCat k) :=
  { obj := lineObject k
    filtration :=
      { toFun := fun p ↦ lineSubobject k (if ofDual p < 0 then (⊤ : Submodule k k) else ⊥)
        monotone' := by
          intro p q hpq
          exact lineSubobject_mono k <|
            topBotSubmoduleFiltration_antitone k
              (fun _ _ hij ↦ lt_of_le_of_lt hij) hpq } }

/-- The filtered `k`-module `(W, F)` with `W = k` and `F^i W = W` for `i ≤ 0`, `F^i W = 0`
for `i > 0`. -/
private def nonpositiveFilteredLine : FilteredObject (ModuleCat k) :=
  { obj := lineObject k
    filtration :=
      { toFun := fun p ↦ lineSubobject k (if ofDual p ≤ 0 then (⊤ : Submodule k k) else ⊥)
        monotone' := by
          intro p q hpq
          exact lineSubobject_mono k <|
            topBotSubmoduleFiltration_antitone k (fun _ _ hij ↦ le_trans hij) hpq } }

private theorem strictNegativeFilteredLine_zero :
    (strictNegativeFilteredLine k).filtration 0 = (⊥ : Subobject (lineObject k)) := by
  change lineSubobject k (if (0 : ℤ) < 0 then (⊤ : Submodule k k) else ⊥) = ⊥
  simp

private theorem nonpositiveFilteredLine_zero :
    (nonpositiveFilteredLine k).filtration 0 = (⊤ : Subobject (lineObject k)) := by
  change lineSubobject k (if (0 : ℤ) ≤ 0 then (⊤ : Submodule k k) else ⊥) = ⊤
  simp

/-- The identity map on the underlying line preserves the two filtrations. -/
private theorem strictNegativeToNonpositiveFilteredLine_preserves (i : ℤ) :
    ((nonpositiveFilteredLine k).filtration i).Factors
      (((strictNegativeFilteredLine k).filtration i).arrow ≫ 𝟙 (lineObject k)) := by
  have hle :
      lineSubobject k (if i < 0 then (⊤ : Submodule k k) else ⊥) ≤
        lineSubobject k (if i ≤ 0 then (⊤ : Submodule k k) else ⊥) := by
    refine lineSubobject_mono k ?_
    by_cases hi : i < 0
    · simp [hi, le_of_lt hi]
    · simp [hi]
  simpa using
    Subobject.factors_of_le (((strictNegativeFilteredLine k).filtration i).arrow) hle
      (((strictNegativeFilteredLine k).filtration i).factors_self)

/-- The morphism of filtered lines induced by the identity map on the underlying module `k`.
-/
private def strictNegativeToNonpositiveFilteredLine :
    strictNegativeFilteredLine k ⟶ nonpositiveFilteredLine k where
  hom := 𝟙 (lineObject k)
  preserves := strictNegativeToNonpositiveFilteredLine_preserves k

section Nontrivial

variable [Nontrivial k]

/-- The filtered identity map from the stricter filtration to the looser one is not an
isomorphism. -/
private theorem strictNegativeToNonpositiveFilteredLine_not_iso :
    ¬ IsIso (strictNegativeToNonpositiveFilteredLine k) := by
  let f := strictNegativeToNonpositiveFilteredLine k
  intro hIso
  haveI : IsIso f := by simpa [f] using hIso
  have hComp :
      f.hom ≫ (inv f).hom = 𝟙 (lineObject k) := by
    exact congrArg FilteredObject.Hom.hom (IsIso.hom_inv_id f)
  have hInv :
      (inv f).hom = 𝟙 (lineObject k) := by
    simpa [f, strictNegativeToNonpositiveFilteredLine] using hComp
  have hpres := (inv f).pullback_preserves 0
  have hTopBot : (⊤ : Subobject (lineObject k)) ≤ ⊥ := by
    have hpres' :
        (nonpositiveFilteredLine k).filtration 0 ≤
          (Subobject.pullback (𝟙 (lineObject k))).obj ((strictNegativeFilteredLine k).filtration 0) := by
      simpa [hInv] using hpres
    change lineSubobject k (if (0 : ℤ) ≤ 0 then (⊤ : Submodule k k) else ⊥) ≤
        (Subobject.pullback (𝟙 (lineObject k))).obj
          (lineSubobject k (if (0 : ℤ) < 0 then (⊤ : Submodule k k) else ⊥)) at hpres'
    simpa [Subobject.pullback_id] using hpres'
  have hEq : (⊥ : Subobject (lineObject k)) = ⊤ := top_le_iff.mp hTopBot
  have hSubmoduleEq : (⊥ : Submodule k k) = ⊤ := by
    simpa [lineSubobject] using congrArg (ModuleCat.subobjectModule (lineObject k)) hEq
  have hOneMem : (1 : k) ∈ (⊥ : Submodule k k) := by
    simp [hSubmoduleEq]
  exact (show (1 : k) ≠ 0 from one_ne_zero) (by simp at hOneMem)

/-- The category of filtered `k`-modules is not abelian for any nontrivial ring `k`; it is
witnessed by the identity map on `k` between the filtration `F^i = k` for `i < 0`, `F^i = 0` for
`i ≥ 0` and the filtration `F^i = k` for `i ≤ 0`, `F^i = 0` for `i > 0`, which is mono and epi
but not an isomorphism. -/
theorem filtered_modules_not_abelian :
    ¬ Nonempty (Abelian (FilteredObject (ModuleCat k))) := by
  sorry

end Nontrivial
end Ring

section Field

variable (k : Type u) [Field k]

/-- Example 12.3.13: the category of filtered vector spaces over a field `k` is not abelian; it is
witnessed by the identity map on `k` between the filtration `F^i = k` for `i < 0`, `F^i = 0` for
`i ≥ 0` and the filtration `F^i = k` for `i ≤ 0`, `F^i = 0` for `i > 0`, which is mono and epi
but not an isomorphism. -/
theorem filtered_vector_spaces_not_abelian :
    ¬ Nonempty (Abelian (FilteredObject (ModuleCat k))) :=
  filtered_modules_not_abelian k

end Field

end CategoryTheory
