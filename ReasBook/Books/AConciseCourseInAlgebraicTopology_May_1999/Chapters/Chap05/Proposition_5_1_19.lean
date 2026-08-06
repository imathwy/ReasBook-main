import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Homeomorph.Lemmas
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_10
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_17

universe u v

open scoped Topology

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Helper for Proposition 5.1.19: a `UCompactlyGeneratedSpace` stays compactly generated after
raising the probe universe. -/
lemma uCompactlyGeneratedSpaceLift
    (X : Type u) [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X] :
    UCompactlyGeneratedSpace.{max u v} X := by
  -- Check closedness against larger-universe compact probes by inserting a `ULift`.
  refine uCompactlyGeneratedSpace_of_isClosed fun s hs ↦ ?_
  refine UCompactlyGeneratedSpace.isClosed fun S ⟨f, hf⟩ ↦ ?_
  let g : ULift.{v} S → X := f ∘ ULift.down
  have hg : Continuous g := hf.comp continuous_uliftDown
  simpa [g, Function.comp_def] using
    (hs (CompHaus.of (ULift.{v} S)) ⟨g, hg⟩).preimage continuous_uliftUp

/-- Helper for Proposition 5.1.19: a product with a compact Hausdorff left factor preserves
`UCompactlyGeneratedSpace`. -/
lemma uCompactlyGeneratedSpaceCompHausProd
    (S : Type v) [TopologicalSpace S] [CompactSpace S] [T2Space S]
    (X : Type u) [TopologicalSpace X] [UCompactlyGeneratedSpace.{max u v} X] :
    UCompactlyGeneratedSpace.{max u v} (S × X) := by
  let _ : LocallyCompactSpace S := inferInstance
  -- Prove continuity on `S × X` by currying in the compact factor `S`.
  refine uCompactlyGeneratedSpace_of_continuous_maps ?_
  intro Z tZ f hf
  let F : X → C(S, Z) := fun x ↦
    ⟨fun s ↦ f (s, x), by
      -- A compact probe into `S` already detects continuity of each section `s ↦ f (s, x)`.
      let gx : C(ULift.{u} S, S × X) :=
        ⟨fun s ↦ (s.down, x), continuous_uliftDown.prodMk continuous_const⟩
      have hsec : Continuous fun s : ULift.{u} S ↦ f (s.down, x) := by
        simpa [gx] using hf (CompHaus.of (ULift.{u} S)) gx
      simpa using hsec.comp continuous_uliftUp⟩
  have hF : Continuous F := by
    -- Test continuity into `C(S, Z)` after precomposing with compact probes into `X`.
    refine continuous_from_uCompactlyGeneratedSpace F ?_
    intro T g
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    let h : C(T × S, S × X) :=
      ⟨fun p ↦ (p.2, g p.1), continuous_snd.prodMk (g.continuous.comp continuous_fst)⟩
    simpa [F, h, Function.uncurry, Function.comp_def] using hf (CompHaus.of (T × S)) h
  have hUncurry : Continuous fun xs : X × S ↦ f (xs.2, xs.1) := by
    -- Uncurrying the continuous family `x ↦ (s ↦ f (s, x))` gives continuity on `X × S`.
    simpa [F, Function.uncurry] using ContinuousMap.continuous_uncurry_of_continuous ⟨F, hF⟩
  -- Swap the factors back to the requested source order `S × X`.
  simpa [Function.comp_def] using hUncurry.comp (continuous_snd.prodMk continuous_fst)

/-- Helper for Proposition 5.1.19: a compact Hausdorff space is compactly generated because its
identity map is itself one of the compact probes. -/
lemma compactHausdorff_uCompactlyGenerated
    {K : Type (max u v)} [TopologicalSpace K] [CompactSpace K] [T2Space K] :
    UCompactlyGeneratedSpace.{max u v} K := by
  refine uCompactlyGeneratedSpace_of_continuous_maps ?_
  intro Z _ f hf
  -- The identity probe on `K` already belongs to the defining compact family.
  simpa [Function.comp] using hf (CompHaus.of K) ⟨id, continuous_id⟩

/-- Helper for Proposition 5.1.19: taking the product with a quotient map on the right preserves
quotient maps when the left factor is locally compact. -/
lemma isQuotientMap_prodMap_right_of_locallyCompact
    {K : Type u} [TopologicalSpace K] [LocallyCompactSpace K]
    {A : Type v} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (π : A → B) (hπ : Topology.IsQuotientMap π) :
    Topology.IsQuotientMap (fun p : K × A ↦ (p.1, π p.2)) := by
  let q : K × A → K × B := fun p ↦ (p.1, π p.2)
  refine ⟨?_, ?_⟩
  · -- Surjectivity is inherited coordinatewise from the quotient map on the right.
    intro p
    rcases hπ.surjective p.2 with ⟨a, ha⟩
    refine ⟨(p.1, a), ?_⟩
    ext <;> simp [ha]
  · have hq : Continuous q := continuous_fst.prodMk (hπ.continuous.comp continuous_snd)
    have hCoinducedLe :
        TopologicalSpace.coinduced q (inferInstance : TopologicalSpace (K × A)) ≤
          (inferInstance : TopologicalSpace (K × B)) :=
      continuous_iff_coinduced_le.mp hq
    have hLeCoinduced :
        (inferInstance : TopologicalSpace (K × B)) ≤
          TopologicalSpace.coinduced q (inferInstance : TopologicalSpace (K × A)) := by
      rw [← continuous_id_iff_le]
      let _ : TopologicalSpace (K × B) :=
        TopologicalSpace.coinduced q (inferInstance : TopologicalSpace (K × A))
      -- The compact-open lifting theorem reconstructs continuity on the target product.
      exact
          @Topology.IsQuotientMap.continuous_lift_prod_right
            A B K (K × B)
            inferInstance inferInstance inferInstance
            (TopologicalSpace.coinduced q (inferInstance : TopologicalSpace (K × A)))
            inferInstance π hπ id continuous_coinduced_rng
    exact le_antisymm hLeCoinduced hCoinducedLe

/-- Helper for Proposition 5.1.19: the ordinary product topology `X ×_c Y` is already
compactly generated when the left factor is locally compact and the right factor is compactly
generated weak Hausdorff. -/
lemma ordinaryProductTopology_uCompactlyGenerated
    [LocallyCompactSpace X] [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y] :
    UCompactlyGeneratedSpace.{max u v} (X × Y) := by
  -- Route correction: the curry proof still fails because the non-`T2` locally-compact-to-`UCG`
  -- bridge for `X` is unavailable in this checkout.
  -- TODO: complete the quotient/coinduced route by presenting `Y` via its compact-probe sigma
  -- source, using `isQuotientMap_prodMap_right_of_locallyCompact` for the product quotient, and
  -- reducing the remaining domain problem to the base case `UCompactlyGeneratedSpace (S × X)` for
  -- compact Hausdorff `S`.
  sorry

/-- Helper for Proposition 5.1.19: when `X` is locally compact and `Y` is compactly generated
weak Hausdorff, the ordinary product topology on `X × Y` already equals its k-ification. -/
lemma ordinaryProductTopology_eq_compactlyGenerated
    [LocallyCompactSpace X] [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y] :
    (X ×_c Y : TopologicalSpace (X × Y)) =
      TopologicalSpace.compactlyGenerated.{max u v} (X × Y) := by
  -- Work in the ordinary product topology so `eq_compactlyGenerated` targets the right space.
  let _ : TopologicalSpace (X × Y) := X ×_c Y
  -- Local instance justification (bridge): the local comparison lemma provides the exact
  -- `UCompactlyGeneratedSpace` witness for the active ordinary product topology.
  let _ : UCompactlyGeneratedSpace.{max u v} (X × Y) :=
    ordinaryProductTopology_uCompactlyGenerated (X := X) (Y := Y)
  -- Identify the active topology with its compactly generated replacement.
  simpa using (eq_compactlyGenerated (X := X × Y))

/-- Proposition 5.1.19. If `X` is locally compact and `Y` is compactly generated in the sense of
Definition 5.1.10, then the compactly generated product topology on `X × Y` agrees with the
ordinary product topology `X ×_c Y`. -/
theorem compactlyGeneratedProductTopology_eq_ordinaryProductTopology
    [LocallyCompactSpace X] [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y] :
    compactlyGeneratedProductTopology X Y = X ×_c Y := by
  -- Rewrite the source-facing product topology alias to the owner k-ification.
  rw [compactlyGeneratedProductTopology_def]
  -- The auxiliary lemma shows the ordinary product topology is already compactly generated.
  exact (ordinaryProductTopology_eq_compactlyGenerated (X := X) (Y := Y)).symm

end
