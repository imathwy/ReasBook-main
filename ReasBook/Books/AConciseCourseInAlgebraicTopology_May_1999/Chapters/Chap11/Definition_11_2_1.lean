import Mathlib.Topology.Homotopy.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_2_2

open scoped Topology Topology.Homotopy unitInterval

universe u w

-- Semantic recall via `lean_leansearch`: `HomotopyGroup.Pi`, written `π_ q X x`, is the
-- canonical owner for homotopy groups, and local Chapter 8 precedent fixes `Σ X` as the reduced
-- suspension owner. No existing suspension map on homotopy groups was found in the current
-- environment, so this file defines the source-faithful map directly on cubical representatives
-- and then descends to quotients.

/-- Compatibility bridge to the canonical reduced-suspension notation `Σ X`. -/
abbrev suspensionSpace (X : PointedCompactlyGenerated.{u, w}) : PointedCompactlyGenerated.{u, w} :=
  Σ X

/-- Helper for Definition 11.2.1: adjoining the last interval coordinate gives a continuous map
from the `(q + 1)`-cube into `Σ X`. -/
theorem continuous_suspensionRepresentative
    (q : ℕ) (X : PointedCompactlyGenerated.{u, w})
    (p : GenLoop (Fin q) X.toCompactlyGenerated X.point) :
    Continuous fun t : I^(Fin (q + 1)) ↦
      (reducedSuspensionMk X (p (fun i ↦ t i.castSucc), t (Fin.last q)) :
        (Σ X).toCompactlyGenerated) := by
  -- Factor the suspended representative through the product map into `X × I`.
  have hstrip :
      Continuous fun t : I^(Fin (q + 1)) ↦
        (p (fun i ↦ t i.castSucc), t (Fin.last q)) := by
    exact (p.1.continuous.comp (by fun_prop)).prodMk (by fun_prop)
  simpa using (continuous_reducedSuspensionMk X).comp hstrip

/-- Helper for Definition 11.2.1: a suspended representative sends the boundary of the
`(q + 1)`-cube to the distinguished point of `Σ X`. -/
theorem suspensionRepresentative_boundary_eq_point
    (q : ℕ) (X : PointedCompactlyGenerated.{u, w})
    (p : GenLoop (Fin q) X.toCompactlyGenerated X.point)
    (t : I^(Fin (q + 1))) (ht : t ∈ Cube.boundary (Fin (q + 1))) :
    reducedSuspensionMk X (p (fun i ↦ t i.castSucc), t (Fin.last q)) = (Σ X).point := by
  -- Split a boundary coordinate into an old coordinate or the new suspension coordinate.
  rcases ht with ⟨j, hj | hj⟩
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · have hp : p (fun i ↦ t i.castSucc) = X.point := by
        exact GenLoop.boundary p (fun i ↦ t i.castSucc) ⟨i, Or.inl hj⟩
      rw [hp]
      simpa [reducedSuspension_point] using
        reducedSuspensionMk_eq_point_of_fst_eq_point X (t (Fin.last q))
    · simpa [hj, reducedSuspension_point] using
        reducedSuspensionMk_eq_point_of_snd_eq_zero X (p (fun i ↦ t i.castSucc))
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · have hp : p (fun i ↦ t i.castSucc) = X.point := by
        exact GenLoop.boundary p (fun i ↦ t i.castSucc) ⟨i, Or.inr hj⟩
      rw [hp]
      simpa [reducedSuspension_point] using
        reducedSuspensionMk_eq_point_of_fst_eq_point X (t (Fin.last q))
    · simpa [hj, reducedSuspension_point] using
        reducedSuspensionMk_eq_point_of_snd_eq_one X (p (fun i ↦ t i.castSucc))

/-- The suspended cubical representative of `p : π_q(X)` is obtained by adjoining one interval
coordinate and sending `(s, t)` to the suspension class of `(p s, t)`. This is the cubical model
of the source formula `f ∧ id : S^q ∧ S^1 → ΣX`. -/
def suspensionGenLoop
    (q : ℕ) (X : PointedCompactlyGenerated.{u, w})
    (p : GenLoop (Fin q) X.toCompactlyGenerated X.point) :
    GenLoop (Fin (q + 1)) (Σ X).toCompactlyGenerated (Σ X).point :=
  ⟨⟨fun t ↦ reducedSuspensionMk X (p (fun i ↦ t i.castSucc), t (Fin.last q)),
      continuous_suspensionRepresentative q X p⟩,
    suspensionRepresentative_boundary_eq_point q X p⟩

/-- Evaluating `suspensionGenLoop X p` at a cube point amounts to adjoining the last coordinate as
the suspension direction. -/
@[simp] theorem suspensionGenLoop_apply
    (q : ℕ) (X : PointedCompactlyGenerated.{u, w})
    (p : GenLoop (Fin q) X.toCompactlyGenerated X.point) (t : I^(Fin (q + 1))) :
    suspensionGenLoop q X p t =
      reducedSuspensionMk X (p (fun i ↦ t i.castSucc), t (Fin.last q)) := rfl

/-- Helper for Definition 11.2.1: stripping off the new suspension coordinate commutes with
updating an old coordinate. -/
theorem stripCastSucc_update_eq
    (q : ℕ) (t : I^(Fin (q + 1))) (i : Fin q) (u : I) :
    (fun j : Fin q ↦ Function.update t i.castSucc u j.castSucc) =
      Function.update (fun j : Fin q ↦ t j.castSucc) i u := by
  -- Check the update coordinatewise on the old cube.
  ext j
  by_cases h : j = i
  · subst h
    simp
  · simp [Function.update, h]

/-- Helper for Definition 11.2.1: updating an old coordinate leaves the new suspension
coordinate unchanged. -/
theorem lastCoord_update_castSucc_eq
    (q : ℕ) (t : I^(Fin (q + 1))) (i : Fin q) (u : I) :
    Function.update t i.castSucc u (Fin.last q) = t (Fin.last q) := by
  -- The last coordinate is disjoint from every `castSucc i`.
  by_cases h : Fin.last q = i.castSucc
  · exact (Fin.castSucc_ne_last i h.symm).elim
  · simp [Function.update, h]

/-- Helper for Definition 11.2.1: evaluating a suspended representative after updating an old
coordinate only updates the underlying `q`-cube representative. -/
theorem suspensionGenLoop_apply_update_castSucc
    (q : ℕ) (X : PointedCompactlyGenerated.{u, w})
    (p : GenLoop (Fin q) X.toCompactlyGenerated X.point)
    (i : Fin q) (t : I^(Fin (q + 1))) (u : I) :
    suspensionGenLoop q X p (Function.update t i.castSucc u) =
      reducedSuspensionMk X (p (Function.update (fun j ↦ t j.castSucc) i u), t (Fin.last q)) := by
  -- Expand the suspended evaluation and simplify the update on stripped coordinates.
  rw [suspensionGenLoop_apply]
  simp [stripCastSucc_update_eq, lastCoord_update_castSucc_eq]

/-- Helper for Definition 11.2.1: suspending commutes with the cubical concatenation `transAt`
along any old coordinate. -/
theorem suspensionGenLoop_transAtCastSucc
    (q : ℕ) (X : PointedCompactlyGenerated.{u, w})
    (i : Fin q)
    (p₀ p₁ : GenLoop (Fin q) X.toCompactlyGenerated X.point) :
    suspensionGenLoop q X (GenLoop.transAt i p₀ p₁) =
      GenLoop.transAt i.castSucc (suspensionGenLoop q X p₀) (suspensionGenLoop q X p₁) := by
  ext t
  -- Expand both concatenations and normalize the `Function.update` bookkeeping once.
  rw [suspensionGenLoop_apply, GenLoop.transAt, GenLoop.coe_copy, GenLoop.transAt, GenLoop.coe_copy]
  split_ifs
  · rw [suspensionGenLoop_apply_update_castSucc]
  · rw [suspensionGenLoop_apply_update_castSucc]

/-- A homotopy between cubical representatives descends to a homotopy between their suspensions. -/
theorem suspensionGenLoop_homotopic
    (q : ℕ) (X : PointedCompactlyGenerated.{u, w})
    {p p' : GenLoop (Fin q) X.toCompactlyGenerated X.point}
    (h : GenLoop.Homotopic p p') :
    GenLoop.Homotopic (suspensionGenLoop q X p) (suspensionGenLoop q X p') := by
  rcases h with ⟨H⟩
  refine ⟨?_⟩
  refine { toHomotopy := ?_, prop' := ?_ }
  · refine
      { toFun := fun s ↦
          (reducedSuspensionMk X (H (s.1, fun i ↦ s.2 i.castSucc), s.2 (Fin.last q)) :
            (Σ X).toCompactlyGenerated)
        continuous_toFun := ?_
        map_zero_left := ?_
        map_one_left := ?_ }
    · -- Compose the original homotopy with the strip-last-coordinate map.
      have hstrip :
          Continuous fun s : I × I^(Fin (q + 1)) ↦ (s.1, fun i : Fin q ↦ s.2 i.castSucc) := by
        fun_prop
      have hpair :
          Continuous fun s : I × I^(Fin (q + 1)) ↦
            (H (s.1, fun i ↦ s.2 i.castSucc), s.2 (Fin.last q)) := by
        exact (H.continuous.comp hstrip).prodMk (by fun_prop)
      simpa using (continuous_reducedSuspensionMk X).comp hpair
    · intro t
      -- At time `0`, the suspended homotopy recovers the suspension of `p`.
      rw [H.apply_zero (fun i ↦ t i.castSucc)]
      rfl
    · intro t
      -- At time `1`, the suspended homotopy recovers the suspension of `p'`.
      rw [H.apply_one (fun i ↦ t i.castSucc)]
      rfl
  · intro s t ht
    -- Boundary points stay at the suspension basepoint throughout the homotopy.
    have hpoint :
        reducedSuspensionMk X (H (s, fun i ↦ t i.castSucc), t (Fin.last q)) = (Σ X).point := by
      rcases ht with ⟨j, hj | hj⟩
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
        · have hfixed : H (s, fun i ↦ t i.castSucc) = p (fun i ↦ t i.castSucc) := by
            exact H.eq_fst s ⟨i, Or.inl hj⟩
          rw [hfixed]
          exact suspensionRepresentative_boundary_eq_point q X p t ⟨i.castSucc, Or.inl hj⟩
        · simpa [hj, reducedSuspension_point] using
            reducedSuspensionMk_eq_point_of_snd_eq_zero X (H (s, fun i ↦ t i.castSucc))
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
        · have hfixed : H (s, fun i ↦ t i.castSucc) = p (fun i ↦ t i.castSucc) := by
            exact H.eq_fst s ⟨i, Or.inr hj⟩
          rw [hfixed]
          exact suspensionRepresentative_boundary_eq_point q X p t ⟨i.castSucc, Or.inr hj⟩
        · simpa [hj, reducedSuspension_point] using
            reducedSuspensionMk_eq_point_of_snd_eq_one X (H (s, fun i ↦ t i.castSucc))
    exact hpoint.trans (suspensionRepresentative_boundary_eq_point q X p t ht).symm

/-- The suspension map on homotopy-group classes sends the class of a cubical representative to
the class of its suspended cubical representative. -/
def suspensionPiMap
    (q : ℕ) (X : PointedCompactlyGenerated.{u, w}) :
    π_ q X.toCompactlyGenerated X.point →
      π_ (q + 1) (Σ X).toCompactlyGenerated (Σ X).point :=
  Quotient.map
    (suspensionGenLoop q X)
    (fun _ _ ↦ suspensionGenLoop_homotopic q X)

/-- Applying `suspensionPiMap q X` to the class of a representative returns the class of its
suspension. -/
@[simp] theorem suspensionPiMap_apply_mk
    (q : ℕ) (X : PointedCompactlyGenerated.{u, w})
    (p : GenLoop (Fin q) X.toCompactlyGenerated X.point) :
    suspensionPiMap q X ⟦p⟧ = ⟦suspensionGenLoop q X p⟧ := rfl

/-- Helper for Definition 11.2.1: the quotient-level suspension map preserves the identity class.
-/
theorem suspensionPiMap_map_one
    (q : ℕ) [NeZero q] (X : PointedCompactlyGenerated.{u, w}) :
    suspensionPiMap q X (1 : π_ q X.toCompactlyGenerated X.point) = 1 := by
  -- Rewrite the identity element by the constant representative and suspend that representative.
  rw [HomotopyGroup.one_def, suspensionPiMap_apply_mk, HomotopyGroup.one_def]
  apply Quotient.sound
  have hconst :
      suspensionGenLoop q X
          (GenLoop.const : GenLoop (Fin q) X.toCompactlyGenerated X.point) =
        (GenLoop.const : GenLoop (Fin (q + 1)) (Σ X).toCompactlyGenerated (Σ X).point) := by
    ext t
    -- The suspension of the constant loop collapses through the basepoint segment.
    exact
      (by
        calc
          suspensionGenLoop q X
              (GenLoop.const : GenLoop (Fin q) X.toCompactlyGenerated X.point) t =
              reducedSuspensionPoint X := by
                rw [suspensionGenLoop_apply, GenLoop.const_apply]
                exact reducedSuspensionMk_eq_point_of_fst_eq_point X (t (Fin.last q))
          _ = GenLoop.const t := rfl)
  simpa [hconst] using
    (GenLoop.Homotopic.refl
      (GenLoop.const : GenLoop (Fin (q + 1)) (Σ X).toCompactlyGenerated (Σ X).point))

/-- Helper for Definition 11.2.1: the quotient-level suspension map preserves multiplication. -/
theorem suspensionPiMap_map_mul
    (q : ℕ) [NeZero q] (X : PointedCompactlyGenerated.{u, w})
    (x y : π_ q X.toCompactlyGenerated X.point) :
    suspensionPiMap q X (x * y) = suspensionPiMap q X x * suspensionPiMap q X y := by
  let i : Fin q := ⟨0, Nat.pos_of_neZero q⟩
  refine Quotient.inductionOn₂ x y ?_
  intro p₀ p₁
  -- Reduce both products to `transAt`, then use the representative-level compatibility lemma.
  have hmul_domain :
      suspensionPiMap q X
          (((· * ·) :
              π_ q X.toCompactlyGenerated X.point →
                π_ q X.toCompactlyGenerated X.point →
                  π_ q X.toCompactlyGenerated X.point)
            ⟦p₀⟧ ⟦p₁⟧) =
        suspensionPiMap q X
          (⟦GenLoop.transAt i p₁ p₀⟧ : π_ q X.toCompactlyGenerated X.point) := by
    simpa using congrArg (suspensionPiMap q X)
      (HomotopyGroup.mul_spec (i := i) (p := p₀) (q := p₁))
  have happly :
      suspensionPiMap q X
          (⟦GenLoop.transAt i p₁ p₀⟧ : π_ q X.toCompactlyGenerated X.point) =
        (⟦suspensionGenLoop q X (GenLoop.transAt i p₁ p₀)⟧ :
          π_ (q + 1) (Σ X).toCompactlyGenerated (Σ X).point) := by
    rw [suspensionPiMap_apply_mk]
  have htrans :
      (⟦suspensionGenLoop q X (GenLoop.transAt i p₁ p₀)⟧ :
        π_ (q + 1) (Σ X).toCompactlyGenerated (Σ X).point) =
        (⟦GenLoop.transAt i.castSucc (suspensionGenLoop q X p₁)
            (suspensionGenLoop q X p₀)⟧ :
          π_ (q + 1) (Σ X).toCompactlyGenerated (Σ X).point) := by
    simpa using congrArg
      (fun z : GenLoop (Fin (q + 1)) (Σ X).toCompactlyGenerated (Σ X).point ↦
        (⟦z⟧ : π_ (q + 1) (Σ X).toCompactlyGenerated (Σ X).point))
      (suspensionGenLoop_transAtCastSucc q X i p₁ p₀)
  have hmul_codomain :
      (⟦GenLoop.transAt i.castSucc (suspensionGenLoop q X p₁)
          (suspensionGenLoop q X p₀)⟧ :
        π_ (q + 1) (Σ X).toCompactlyGenerated (Σ X).point) =
        suspensionPiMap q X ⟦p₀⟧ * suspensionPiMap q X ⟦p₁⟧ := by
    symm
    simpa [suspensionPiMap_apply_mk] using
      (HomotopyGroup.mul_spec (i := i.castSucc)
        (p := suspensionGenLoop q X p₀) (q := suspensionGenLoop q X p₁))
  simpa using hmul_domain.trans (happly.trans (htrans.trans hmul_codomain))

/-- Definition 11.2.1. For `q > 0`, the suspension homomorphism
`Σ : π_ q(X) → π_ (q + 1)(ΣX)` sends a representative `f` to the suspended representative
`f ∧ id : S^q ∧ S^1 → ΣX`, formalized here on the cubical owner `HomotopyGroup.Pi` by
`suspensionGenLoop q X`. -/
def suspensionHomomorphism
    (q : ℕ) [NeZero q] (X : PointedCompactlyGenerated.{u, w}) :
    π_ q X.toCompactlyGenerated X.point →*
      π_ (q + 1) (Σ X).toCompactlyGenerated (Σ X).point where
  toFun := suspensionPiMap q X
  map_one' := suspensionPiMap_map_one q X
  map_mul' := suspensionPiMap_map_mul q X

/-- Applying `suspensionHomomorphism q X` agrees with the quotient-level suspension map
`suspensionPiMap q X`. -/
theorem suspensionHomomorphism_apply
    (q : ℕ) [NeZero q] (X : PointedCompactlyGenerated.{u, w})
    (x : π_ q X.toCompactlyGenerated X.point) :
    suspensionHomomorphism q X x = suspensionPiMap q X x := rfl

/-- Applying `suspensionHomomorphism q X` to the class of a representative returns the class of
its suspended cubical representative. -/
@[simp] theorem suspensionHomomorphism_apply_mk
    (q : ℕ) [NeZero q] (X : PointedCompactlyGenerated.{u, w})
    (p : GenLoop (Fin q) X.toCompactlyGenerated X.point) :
    suspensionHomomorphism q X ⟦p⟧ = ⟦suspensionGenLoop q X p⟧ := rfl
