module

public import Topology_Munkres_2000.Book.Definition_82_1.SemilocallySimplyConnected
public import Topology_Munkres_2000.Book.Definition_80_1.Covering
import all Topology_Munkres_2000.Book.Lemma_55_1.Inclusions

public section

open Filter
open scoped Topology

universe u v w

namespace IsCoveringMap

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- Helper for Lemma 80.4: induced maps on fundamental groups preserve composition of
continuous maps. -/
private lemma fundamentalGroupMap_comp
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (x : X) :
    (FundamentalGroup.map g (f x)).comp (FundamentalGroup.map f x) =
      FundamentalGroup.map (g.comp f) x := by
  -- Compare the homomorphisms on a loop class and use functoriality of quotient maps.
  ext q
  have innerMap :
      FundamentalGroup.map f x q = Path.Homotopic.Quotient.map q f :=
    FundamentalGroup.map_apply f x q
  have nestedMap :
      Path.Homotopic.Quotient.map
          (Path.Homotopic.Quotient.map q f) g =
        Path.Homotopic.Quotient.map q (g.comp f) := by
    exact (Path.Homotopic.Quotient.map_comp (p := q) (f := f) (g := g)).symm
  have outerToComposite :
      FundamentalGroup.map g (f x) (Path.Homotopic.Quotient.map q f) =
        FundamentalGroup.map (g.comp f) x q := by
    rw [FundamentalGroup.map_apply, FundamentalGroup.map_apply]
    exact nestedMap
  exact (congrArg (fun z ↦ FundamentalGroup.map g (f x) z) innerMap).trans
    outerToComposite

/-- Helper for Lemma 80.4: a composite through a subsingleton fundamental group is the
trivial homomorphism. -/
private lemma fundamentalGroupMap_factor_eq_one_of_subsingleton
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (x : X)
    [Subsingleton (FundamentalGroup Y (f x))] :
    (FundamentalGroup.map g (f x)).comp (FundamentalGroup.map f x) = 1 := by
  -- Extensionality reduces triviality to the unique value of the intermediate group.
  ext q
  have htrivial : FundamentalGroup.map f x q = 1 := Subsingleton.elim _ _
  calc
    ((FundamentalGroup.map g (f x)).comp (FundamentalGroup.map f x)) q =
        FundamentalGroup.map g (f x) (FundamentalGroup.map f x q) := rfl
    _ = FundamentalGroup.map g (f x) 1 :=
      congrArg (fun z ↦ FundamentalGroup.map g (f x) z) htrivial
    _ = 1 := (FundamentalGroup.map g (f x)).map_one
    _ = (1 : FundamentalGroup X x →* FundamentalGroup Z (g (f x))) q := rfl

/-- Helper for Lemma 80.4: a continuous map factoring through a space with subsingleton
fundamental group induces the trivial homomorphism. -/
private lemma fundamentalGroupMap_comp_eq_one_of_subsingleton
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (x : X)
    [Subsingleton (FundamentalGroup Y (f x))] :
    FundamentalGroup.map (g.comp f) x = 1 := by
  -- Transport the factor-map calculation through functoriality of the induced map.
  exact (fundamentalGroupMap_comp f g x).symm.trans
    (fundamentalGroupMap_factor_eq_one_of_subsingleton f g x)

/-- Helper for Lemma 80.4: an induced map is trivial when its continuous map factors through
a space with subsingleton fundamental group. -/
private lemma fundamentalGroupMap_eq_one_of_factorization
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (i : C(X, Z)) (x : X)
    (hfactor : g.comp f = i) [Subsingleton (FundamentalGroup Y (f x))] :
    FundamentalGroup.map i x = 1 := by
  -- Substitute the factorization as a dependent equality, aligning the target basepoint.
  subst i
  exact fundamentalGroupMap_comp_eq_one_of_subsingleton f g x

/-- Helper for Lemma 80.4: `mapOfSubtype` is induced by the canonical subtype inclusion. -/
private lemma fundamentalGroupMapOfSubtype_eq_map_subtypeVal
    {X : Type u} [TopologicalSpace X] (U : Set X) (x : U) :
    FundamentalGroup.mapOfSubtype U x =
      FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) x := by
  -- Expose the owner definition once, leaving the main proof in the continuous-map API.
  unfold FundamentalGroup.mapOfSubtype
  ext q
  rw [FundamentalGroup.map_apply]

/-- Lemma 80.4. A covered point has a neighborhood whose inclusion induces the trivial
homomorphism on fundamental groups when the covering space is simply connected. -/
theorem exists_nhds_fundamentalGroupMap_eq_one {p : E → B} (hp : IsCoveringMap p)
    (e₀ : E) [SimplyConnectedSpace E] :
    ∃ (U : Set B) (hU : U ∈ 𝓝 (p e₀)),
      FundamentalGroup.mapOfSubtype U (SemilocallySimplyConnectedSpace.point hU) = 1 := by
  -- Choose the local inverse sheet through `e₀`; its source is the desired neighborhood.
  let hlocal : IsLocalHomeomorph p := hp.isLocalHomeomorph
  let inverse := hlocal.localInverseAt e₀
  let U : Set B := inverse.source
  have hcenter : p e₀ ∈ U := hlocal.apply_self_mem_localInverseAt_source
  have hU : U ∈ 𝓝 (p e₀) := inverse.open_source.mem_nhds hcenter
  refine ⟨U, hU, ?_⟩
  -- Restrict the chosen local inverse to its source to obtain a continuous section into `E`.
  have hsectionContinuous : Continuous (fun y : U ↦ inverse y) :=
    inverse.continuousOn.restrict
  let localSection : C(U, E) := ⟨fun y ↦ inverse y, hsectionContinuous⟩
  let coveringMap : C(E, B) := ⟨p, hp.continuous⟩
  -- The local-inverse equation identifies the neighborhood inclusion with this factorization.
  have hfactor : coveringMap.comp localSection =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)) := by
    ext y
    exact hlocal.apply_localInverseAt_of_mem y.property
  -- Functoriality now factors the induced map through the trivial fundamental group of `E`.
  rw [fundamentalGroupMapOfSubtype_eq_map_subtypeVal]
  exact fundamentalGroupMap_eq_one_of_factorization localSection coveringMap
    (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B))
    (SemilocallySimplyConnectedSpace.point hU) hfactor

/-- A space admitting a surjective covering by a simply connected space is semilocally
simply connected. -/
theorem semilocallySimplyConnectedSpace_of_surjective {p : E → B} (hp : IsCoveringMap p)
    (hp_surjective : Function.Surjective p) [SimplyConnectedSpace E] :
    SemilocallySimplyConnectedSpace B := by
  constructor
  intro b₀
  obtain ⟨e₀, rfl⟩ := hp_surjective b₀
  exact hp.exists_nhds_fundamentalGroupMap_eq_one e₀

end IsCoveringMap
