import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_9
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Pointwise Rockafellar PolarCone

section

variable {ι : Type*}
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.4.2.1 states that the polar cone of a finite Minkowski sum of
  nonempty cones is the intersection of the individual polar cones.
- `core/canonical`: the owner objects already present in the project are the pairing-layer
  set-valued polar operator `polarCone` (used below via the canonical notation `Kᵒ[𝕜]`), its owner
  dual-cone API `PointedCone.dual` from `Text_14_0_1`, the cone predicate `Set.IsCone 𝕜`,
  pointwise finite set sums, and indexed intersections.
- `bridge/view`: the textbook finite family is rendered by an arbitrary finite index type `ι`,
  which is the minimal canonical layer because no order or coordinate data is used.

Domain-style sampling used here:
- `polarCone` / notation `Kᵒ[𝕜]` from `Text_14_0_1`;
- `mem_polarCone_iff_pairing` from `Text_14_0_1`;
- `Set.IsCone 𝕜` from `Definition_2_5_9`;
- `Set.IsCone.finset_sum` from `Definition_2_5_9`;
- `Set.IsCone.pairing_upperBound_nonneg_of_nonempty` from `Definition_2_5_9`;
- finite pointwise set sums `∑ i in s, K i`;
- finite indexed intersections `⋂ i ∈ s, (K i)ᵒ[𝕜]`.

Primitive data vs derived API:
- primitive inputs: the family of sets `K` together with nonemptiness and cone hypotheses;
- derived output: the polar/intersection identity itself.

The source's convexity hypothesis is redundant for this identity, so the Lean statement keeps only
the mathematically active assumptions. Familywise nonemptiness is essential: without it, an empty
summand makes the pointwise sum empty, so the displayed identity need not hold. The theorem lives
on the pairing owner layer, not on the concrete self-dual inner-product model.
The primal ambient additive structure is kept at the primitive `AddCommMonoid` layer; the
remaining scalar/order assumptions are exactly those currently required by
`Set.IsCone.pairing_upperBound_nonneg_of_nonempty`, which is the upstream cone-level bridge used
in the proof.
-/

-- Proof sketch: if `xStar` lies in every `(K i)ᵒ[𝕜]` over `i ∈ s`, then bilinearity makes it lie
-- in the polar of the finite sum `∑ i in s, K i`. Conversely, fix `i ∈ s` and `x ∈ K i`. Replace
-- the `i`-th summand by `{0}` and keep the others unchanged; this gives a nonempty cone family
-- whose finite sum is again a cone by `Set.IsCone.finset_sum`. Membership of `xStar` in the polar
-- of the original finite sum yields an upper bound `-⟪x, xStar⟫ₚ` for the pairing on that
-- auxiliary cone, and
-- `Set.IsCone.pairing_upperBound_nonneg_of_nonempty` forces `⟪x, xStar⟫ ≤ 0`.
/-- Corollary 16.4.2.1 at the pairing owner layer: for a finite family of nonempty cones, the
polar of a finite Minkowski sum is the finite intersection of the individual polars.
The source states this for convex cones, but convexity is redundant for the displayed identity and
is therefore omitted from the Lean header. -/
theorem polarCone_finset_sum_eq_iInter
    (s : Finset ι)
    (K : ι → Set X)
    (hK : ∀ i ∈ s, (K i).Nonempty ∧ Set.IsCone 𝕜 (K i)) :
    (((∑ i ∈ s, K i)ᵒ[𝕜] : PointedCone 𝕜 Y) : Set Y) =
      ⋂ i ∈ s, (((K i)ᵒ[𝕜] : PointedCone 𝕜 Y) : Set Y) := by
  classical
  have hK_nonempty : ∀ i ∈ s, (K i).Nonempty := fun i hi ↦ (hK i hi).1
  have hK_cone : ∀ i ∈ s, Set.IsCone 𝕜 (K i) := fun i hi ↦ (hK i hi).2
  ext xStar
  constructor
  · intro hxStar
    have hxStar_pair :
        ∀ x ∈ ∑ i ∈ s, K i, (⟪x, xStar⟫ₚ : 𝕜) ≤ (0 : 𝕜) :=
      (mem_polarCone_iff_pairing (K := ∑ i ∈ s, K i) (xStar := xStar)).1 hxStar
    rw [Set.mem_iInter]
    intro i
    rw [Set.mem_iInter]
    intro hi
    refine (mem_polarCone_iff_pairing (K := K i) (xStar := xStar)).2 ?_
    intro x hx
    let L : ι → Set X := fun j ↦ if j = i then ({0} : Set X) else K j
    have hL_nonempty : ∀ j ∈ s, (L j).Nonempty := by
      intro j hj
      by_cases hji : j = i
      · subst hji
        exact ⟨0, by simp [L]⟩
      · simpa [L, hji] using hK_nonempty j hj
    have hL_cone : ∀ j ∈ s, Set.IsCone 𝕜 (L j) := by
      intro j hj
      by_cases hji : j = i
      · subst hji
        intro a y ha hy
        have hy0 : y = 0 := by simpa [L] using hy
        simp [L, hy0]
      · simpa [L, hji] using hK_cone j hj
    have hLsum_nonempty : (∑ j ∈ s, L j).Nonempty := by
      choose y hy using hL_nonempty
      let g : ι → X := fun j ↦ if hj : j ∈ s then y j hj else 0
      refine ⟨∑ j ∈ s, g j, ?_⟩
      refine (Set.mem_finset_sum (t := s) (f := L) (a := ∑ j ∈ s, g j)).2 ?_
      refine ⟨g, ?_, rfl⟩
      intro j hj
      simp [g, hj, hy j hj]
    have hbound : ∀ y ∈ ∑ j ∈ s, L j, (⟪y, xStar⟫ₚ : 𝕜) ≤ -(⟪x, xStar⟫ₚ : 𝕜) := by
      intro y hy
      have hxy : x + y ∈ ∑ j ∈ s, K j := by
        rcases (Set.mem_finset_sum (t := s) (f := L) (a := y)).1 hy with ⟨g, hg, rfl⟩
        refine (Set.mem_finset_sum (t := s) (f := K) (a := x + ∑ j ∈ s, g j)).2 ?_
        refine ⟨fun j ↦ if j = i then x else g j, ?_, ?_⟩
        · intro j hj
          by_cases hji : j = i
          · simpa [hji] using hx
          · simpa [L, hji] using hg (i := j) hj
        · have hgi_zero : g i = 0 := by
            have : g i ∈ ({0} : Set X) := by simpa [L] using hg (i := i) hi
            simpa using this
          calc
            ∑ j ∈ s, (if j = i then x else g j) =
                ∑ j ∈ s, (if j = i then x else 0) + ∑ j ∈ s, g j := by
                  rw [← Finset.sum_add_distrib]
                  refine Finset.sum_congr rfl fun j _ ↦ ?_
                  by_cases hj : j = i
                  · subst hj
                    simp [hgi_zero]
                  · simp [hj]
            _ = x + ∑ j ∈ s, g j := by
              have hsum_ite : ∑ j ∈ s, (if j = i then x else (0 : X)) = x := by
                calc
                  ∑ j ∈ s, (if j = i then x else (0 : X)) = if i ∈ s then x else 0 := by
                    exact Finset.sum_ite_eq' (s := s) (a := i) (b := fun _ : ι ↦ x)
                  _ = x := by simp [hi]
              rw [hsum_ite]
      have hy_le : (⟪x + y, xStar⟫ₚ : 𝕜) ≤ (0 : 𝕜) := hxStar_pair (x + y) hxy
      have hxy_pair :
          (⟪x + y, xStar⟫ₚ : 𝕜) = ⟪x, xStar⟫ₚ + ⟪y, xStar⟫ₚ := by
        exact
          (HasPairingAddLeft.pairing_add_left (𝕜 := 𝕜) (x₁ := x) (x₂ := y) (y := xStar))
      have hy_le' : (⟪x, xStar⟫ₚ : 𝕜) + (⟪y, xStar⟫ₚ : 𝕜) ≤ (0 : 𝕜) := by
        simpa [hxy_pair] using hy_le
      linarith
    have hneg : (0 : 𝕜) ≤ -(⟪x, xStar⟫ₚ : 𝕜) :=
      Set.IsCone.pairing_upperBound_nonneg_of_nonempty
        (Set.IsCone.finset_sum hL_cone) hLsum_nonempty hbound
    linarith
  · intro hxStar
    rw [Set.mem_iInter] at hxStar
    refine (mem_polarCone_iff_pairing (K := ∑ i ∈ s, K i) (xStar := xStar)).2 ?_
    intro x hx
    rcases (Set.mem_finset_sum (t := s) (f := K) (a := x)).1 hx with ⟨g, hg, rfl⟩
    have hg_nonpos : ∀ i ∈ s, (⟪g i, xStar⟫ₚ : 𝕜) ≤ (0 : 𝕜) := by
      intro i hi
      have hxStar_i : xStar ∈ (K i)ᵒ[𝕜] := (Set.mem_iInter.mp (hxStar i)) hi
      exact (mem_polarCone_iff_pairing).mp hxStar_i (g i) (hg (i := i) hi)
    have hsum_pair :
        (⟪∑ i ∈ s, g i, xStar⟫ₚ : 𝕜) = ∑ i ∈ s, ⟪g i, xStar⟫ₚ := by
      calc
        (⟪∑ i ∈ s, g i, xStar⟫ₚ : 𝕜) =
            (HasLinearPairing.pairingLinear (∑ i ∈ s, g i)) xStar := by
              rfl
        _ = (∑ i ∈ s, HasLinearPairing.pairingLinear (g i)) xStar := by
              exact congrArg (fun φ : Module.Dual 𝕜 Y => φ xStar)
                (map_sum (HasLinearPairing.pairingLinear : X →ₗ[𝕜] Module.Dual 𝕜 Y) g s)
        _ = ∑ i ∈ s, ⟪g i, xStar⟫ₚ := by
              simp [HasLinearPairing.pairing_eq_pairingLinear]
    calc
      (⟪∑ i ∈ s, g i, xStar⟫ₚ : 𝕜) = ∑ i ∈ s, ⟪g i, xStar⟫ₚ := hsum_pair
      _ ≤ (0 : 𝕜) := Finset.sum_nonpos fun i hi ↦ hg_nonpos i hi

/-- `Fintype`-indexed specialization of `polarCone_finset_sum_eq_iInter` (`s = Finset.univ`). -/
theorem polarCone_sum_eq_iInter [Fintype ι]
    (K : ι → Set X)
    (hK : ∀ i, (K i).Nonempty ∧ Set.IsCone 𝕜 (K i)) :
    (((∑ i, K i)ᵒ[𝕜] : PointedCone 𝕜 Y) : Set Y) =
      ⋂ i, (((K i)ᵒ[𝕜] : PointedCone 𝕜 Y) : Set Y) := by
  simpa using
    (polarCone_finset_sum_eq_iInter (s := (Finset.univ : Finset ι)) K
      (fun i _ ↦ hK i))

end
