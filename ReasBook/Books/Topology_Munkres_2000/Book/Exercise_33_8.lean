module

public import Topology_Munkres_2000.Book.Definition_33_1.FunctionalSeparation
public import Topology_Munkres_2000.Book.Definition_33_2
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.UnitInterval

public section

open Set Topology unitInterval

universe u

namespace FunctionallySeparated

/-- Helper for Exercise 33.8: the affine cutoff collapses the lower half of the unit interval. -/
private noncomputable def halfCutoff : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 :=
  projIcc 0 1 zero_le_one ∘ fun t ↦ 2 * (t : ℝ) - 1

/-- Helper for Exercise 33.8: the affine cutoff is continuous. -/
private lemma continuous_halfCutoff : Continuous halfCutoff := by
  -- Compose the continuous affine expression with projection onto the unit interval.
  exact continuous_projIcc.comp
    ((continuous_const.mul continuous_subtype_val).sub continuous_const)

/-- Helper for Exercise 33.8: values in the lower half are sent to zero. -/
private lemma halfCutoff_eq_zero_of_le {t : Icc (0 : ℝ) 1} (ht : (t : ℝ) ≤ 1 / 2) :
    halfCutoff t = 0 := by
  -- The affine expression is nonpositive, so projection selects the left endpoint.
  apply Set.projIcc_eq_left zero_lt_one |>.2
  dsimp [halfCutoff]
  linarith

/-- Helper for Exercise 33.8: the affine cutoff fixes the upper endpoint. -/
private lemma halfCutoff_one : halfCutoff (1 : Icc (0 : ℝ) 1) = 1 := by
  -- At the upper endpoint the affine expression is exactly one.
  apply Set.projIcc_eq_right zero_lt_one |>.2
  norm_num [halfCutoff]

/-- Exercise 33.8. In a completely regular space, disjoint closed subsets are
functionally separated when the first subset is compact. -/
theorem of_isCompact_left {X : Type u} [TopologicalSpace X] [T35Space X]
    {A B : Set X} (hB : IsClosed B) (hAB : Disjoint A B) (hA : IsCompact A) :
    FunctionallySeparated A B := by
  classical
  -- Separate each point of the compact set from the closed set.
  have hnotMem : ∀ a : A, (a : X) ∉ B := by
    intro a haB
    exact Set.disjoint_left.1 hAB a.property haB
  choose f hfContinuous hfa hfB using fun a : A ↦
    CompletelyRegularSpace.completely_regular (a : X) B hB (hnotMem a)
  let g : A → X → Icc (0 : ℝ) 1 := fun a x ↦ halfCutoff (f a x)
  let U : A → Set X := fun a ↦ {x | (f a x : ℝ) < 1 / 2}
  have hgContinuous : ∀ a : A, Continuous (g a) := by
    intro a
    exact continuous_halfCutoff.comp (hfContinuous a)
  have hUOpen : ∀ a : A, IsOpen (U a) := by
    intro a
    -- The neighborhood is the preimage of an open lower ray under the real coercion.
    exact isOpen_lt
      (continuous_subtype_val.comp (hfContinuous a))
      continuous_const
  have haU : ∀ a : A, (a : X) ∈ U a := by
    intro a
    -- The original separator vanishes at its indexing point.
    dsimp [U]
    rw [hfa a]
    norm_num
  have hUcover : A ⊆ ⋃ a : A, U a := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, haU ⟨x, hx⟩⟩
  obtain ⟨s, hsCover⟩ := hA.elim_finite_subcover U hUOpen hUcover
  have hgZero : ∀ a : A, EqOn (g a) 0 (U a) := by
    intro a x hx
    -- Membership in the chosen neighborhood places the separator in the collapsed half.
    exact halfCutoff_eq_zero_of_le (le_of_lt hx)
  have hgOne : ∀ a : A, EqOn (g a) 1 B := by
    intro a x hx
    -- Every point separator is one on B, and the cutoff fixes one.
    dsimp [g]
    rw [hfB a hx]
    exact halfCutoff_one
  have hInfContinuous : Continuous (fun x ↦ s.inf fun a ↦ g a x) := by
    -- A finite pointwise infimum of continuous interval-valued functions is continuous.
    exact Continuous.finset_inf_apply fun a _ ↦ hgContinuous a
  let separator : C(X, Icc (0 : ℝ) 1) :=
    ⟨fun x ↦ s.inf fun a ↦ g a x, hInfContinuous⟩
  have hSeparatorZero : EqOn separator (fun _ ↦ (0 : Icc (0 : ℝ) 1)) A := by
    intro x hx
    -- Select a covering neighborhood; its zero factor forces the infimum to zero.
    obtain ⟨a, haS, hxaU⟩ := Set.mem_iUnion₂.1 (hsCover hx)
    apply le_antisymm
    · exact (Finset.inf_le haS).trans_eq (hgZero a hxaU)
    · exact bot_le
  have hSeparatorOne : EqOn separator (fun _ ↦ (1 : Icc (0 : ℝ) 1)) B := by
    intro x hx
    -- On B every factor is one, so the finite infimum is one, including the empty case.
    dsimp [separator]
    apply le_antisymm
    · exact le_top
    · exact Finset.le_inf fun a _ ↦ (hgOne a hx).ge
  have hRealContinuous : Continuous (fun x ↦ (separator x : ℝ)) :=
    continuous_subtype_val.comp separator.continuous
  let realSeparator : C(X, ℝ) := ⟨fun x ↦ (separator x : ℝ), hRealContinuous⟩
  -- Use the public real-valued interface of functional separation.
  apply of_continuousMap_real realSeparator
  · intro x hx
    exact congrArg Subtype.val (hSeparatorZero hx)
  · intro x hx
    exact congrArg Subtype.val (hSeparatorOne hx)
  · intro x
    exact (separator x).property

end FunctionallySeparated

end
