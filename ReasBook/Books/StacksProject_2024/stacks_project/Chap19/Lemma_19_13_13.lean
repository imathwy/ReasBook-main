import Mathlib
import StacksProject_2024.stacks_project.Chap13.Lemma_13_9_6
import StacksProject_2024.stacks_project.Chap19.Lemma_19_13_12

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe w v u

namespace CategoryTheory

section

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]

/-
Domain-style sampling for Lemma 19.13.13:
- primary domain: bifiltered complexes in a Grothendieck abelian category, with each filtration
  realizing an inverse system in the derived category;
- sampled owner declarations:
  `FilteredComplex`,
  `FilteredComplex.RealizesInverseSystem`,
  `FilteredComplex.underlying`,
  `Cocone.mk`,
  `FilteredObject`;
- best owner abstraction: the two filtered-complex owners carried by a bifiltered complex, namely
  the first filtration `K.base` and the second filtration `K.second`;
- primitive data: two filtered complexes with a common underlying cochain complex;
- derived API: the realization predicates for the two inverse-system cocones, together with the
  common-underlying comparison `K.underlying_eq`;
- source/core/bridge triage:
  `source-facing`: the existence theorem below for one bifiltered complex realizing two inverse
    systems with common target;
  `core/canonical`: `FilteredComplex A` together with
    `FilteredComplex.RealizesInverseSystem`;
  `bridge/view`: the common-underlying equality between the two filtered-complex owners.

The previous downstream API duplicated the owner-level `FilteredComplex` abstraction by storing
the second filtration degreewise and then rebuilding a filtered complex from that stagewise data.
This file keeps the source-facing bifiltered owner, but its primitive fields now live directly at
the canonical `FilteredComplex` layer reused from Lemma 19.13.12. -/

attribute [local instance] HasDerivedCategory.standard

/-- A bifiltered cochain complex is a filtered cochain complex together with a second decreasing
filtration on the same underlying complex that is preserved by the differentials. -/
structure BifilteredCochainComplex (A : Type u) [Category.{v} A] [Abelian A] where
  /-- The first filtration on the complex. -/
  base : FilteredComplex A
  /-- The second filtration on the same underlying cochain complex. -/
  second : FilteredComplex A
  /-- The two filtered-complex owners have the same underlying cochain complex. -/
  underlying_eq : second.underlying = base.underlying

namespace BifilteredCochainComplex

variable (K : BifilteredCochainComplex A)

omit [IsGrothendieckAbelian.{w} A] in
@[simp] theorem second_underlying :
    K.second.underlying = K.base.underlying := K.underlying_eq

end BifilteredCochainComplex

/-- Helper for Lemma 19.13.13: a realization witness identifies the derived object of the
underlying complex with the cocone point. -/
noncomputable def FilteredComplex.pointIsoOfRealizesInverseSystem
    (K : FilteredComplex A) {system : ℤᵒᵖ ⥤ DerivedCategory A} (c : Cocone system)
    (hK : K.RealizesInverseSystem c) : DerivedCategory.Q.obj K.underlying ≅ c.pt := by
  classical
  -- Extract the point component of the realizing cocone isomorphism by classical choice.
  let stageIso : K.stageTower ≅ system := Classical.choose hK
  let coconeHom : K.stageTowerCocone ⟶ (Cocone.precompose stageIso.hom).obj c :=
    Classical.choose (Classical.choose_spec hK)
  let hIso : IsIso coconeHom := Classical.choose_spec (Classical.choose_spec hK)
  letI : IsIso coconeHom := hIso
  -- The forgetful functor from cocones to their points carries the cocone isomorphism to the
  -- desired point isomorphism.
  simpa using (CategoryTheory.Limits.Cocone.forget K.stageTower).mapIso (asIso coconeHom)

/-- Helper for Lemma 19.13.13: after replacing the underlying complex by a quasi-isomorphic one,
the realization point is identified by composing with the derived inverse of that quasi-isomorphism.
-/
noncomputable def FilteredComplex.pointIsoOfRealizesInverseSystem_of_underlyingQuasiIso
    (K : FilteredComplex A) {system : ℤᵒᵖ ⥤ DerivedCategory A} (c : Cocone system)
    (hK : K.RealizesInverseSystem c) {L : CochainComplex A ℤ}
    (s : K.underlying ⟶ L) (hs : QuasiIso s) :
    DerivedCategory.Q.obj L ≅ c.pt := by
  -- Proof comment: invert `Q.map s` in the derived category and compose with the original point
  -- identification coming from the realization witness on `K`.
  letI : IsIso (DerivedCategory.Q.map s) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso A s).2 hs
  exact
    (asIso (DerivedCategory.Q.map s)).symm ≪≫
      FilteredComplex.pointIsoOfRealizesInverseSystem (A := A) K c hK

/-- Helper for Lemma 19.13.13: a filtered-complex morphism commutes with the canonical
stage-comparison maps. -/
lemma FilteredComplex.stageMap_comp_stageMapOfLE
    {K L : FilteredComplex A} (α : K ⟶ L) {p q : ℤ} (hpq : p ≤ q) :
    FilteredComplex.stageMap α q ≫ L.stageMapOfLE hpq =
      K.stageMapOfLE hpq ≫ FilteredComplex.stageMap α p := by
  -- Proof comment: this is exactly the naturality square of the canonical stage-comparison
  -- transformation `stageFunctor q ⟶ stageFunctor p`, lifted to cochain complexes.
  simpa [FilteredComplex.stageMap, FilteredComplex.stageMapOfLE] using
    (NatTrans.mapHomologicalComplex (FilteredObject.stageFunctorMapOfLE hpq)
      (ComplexShape.up ℤ)).naturality α

/-- Helper for Lemma 19.13.13: a filtered-complex morphism commutes with the inclusions of each
filtration stage into the underlying complex. -/
lemma FilteredComplex.stageMap_comp_stageInclusion
    {K L : FilteredComplex A} (α : K ⟶ L) (p : ℤ) :
    FilteredComplex.stageMap α p ≫ L.stageInclusion p =
      K.stageInclusion p ≫ FilteredComplex.underlyingMap α := by
  -- This is the filtered-object stage-map commutative square evaluated degreewise.
  ext n
  exact FilteredObject.Hom.stageMap_comm (α.f n) p

/-- Helper for Lemma 19.13.13: a filtered-complex morphism induces a natural transformation on
the derived stage towers. -/
noncomputable def FilteredComplex.stageTowerMap
    {K L : FilteredComplex A} (α : K ⟶ L) :
    K.stageTower ⟶ L.stageTower where
  app i := DerivedCategory.Q.map (FilteredComplex.stageMap α i.unop)
  naturality i j f := by
    -- Proof comment: the naturality square is exactly the stage-comparison square after applying
    -- the localization functor `Q`.
    change
      DerivedCategory.Q.map (K.stageMapOfLE f.unop.le) ≫
          DerivedCategory.Q.map (FilteredComplex.stageMap α j.unop) =
        DerivedCategory.Q.map (FilteredComplex.stageMap α i.unop) ≫
          DerivedCategory.Q.map (L.stageMapOfLE f.unop.le)
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
    exact congrArg (DerivedCategory.Q.map)
      (FilteredComplex.stageMap_comp_stageMapOfLE
        (A := A) α (p := j.unop) (q := i.unop) f.unop.le).symm

/-- Helper for Lemma 19.13.13: after inverting the derived image of the underlying map, the stage
inclusion of the target filtered complex rewrites through the inverse stage map and the source
stage inclusion. -/
lemma FilteredComplex.stageInclusion_comp_underlyingMapInv
    {K L : FilteredComplex A} (α : K ⟶ L) (p : ℤ)
    [IsIso (DerivedCategory.Q.map (FilteredComplex.underlyingMap α))]
    [IsIso (DerivedCategory.Q.map (FilteredComplex.stageMap α p))] :
    DerivedCategory.Q.map (L.stageInclusion p) ≫
        inv (DerivedCategory.Q.map (FilteredComplex.underlyingMap α)) =
      inv (DerivedCategory.Q.map (FilteredComplex.stageMap α p)) ≫
        DerivedCategory.Q.map (K.stageInclusion p) := by
  -- TODO: postcompose with `Q.map (underlyingMap α)` and rewrite using
  -- `FilteredComplex.stageMap_comp_stageInclusion`; the present proof term times out in the
  -- current toolchain before `lake lean` returns.
  sorry

/-- Helper for Lemma 19.13.13: realization data transports across a filtered quasi-isomorphism
whose underlying complex map and every stage map are quasi-isomorphisms. -/
lemma FilteredComplex.realizesInverseSystemTransfer
    {K L : FilteredComplex A} (α : K ⟶ L)
    {system : ℤᵒᵖ ⥤ DerivedCategory A} (c : Cocone system)
    (hUnderlying : QuasiIso (FilteredComplex.underlyingMap α))
    (hStage : ∀ p : ℤ, QuasiIso (FilteredComplex.stageMap α p))
    (hK : K.RealizesInverseSystem c) :
    L.RealizesInverseSystem c := by
  -- TODO: rebuild the realization witness directly on `L` using the normalized stage-inclusion
  -- identity `FilteredComplex.stageInclusion_comp_underlyingMapInv`; the current direct cocone
  -- reconstruction still times out before `lake lean` returns.
  sorry

/-- Helper for Lemma 19.13.13: once two filtered realizations already share the same underlying
complex, they package into a bifiltered complex immediately. -/
lemma exists_bifilteredCochainComplex_of_commonUnderlying
    (K K' : FilteredComplex A)
    (hEq : K'.underlying = K.underlying)
    (system system' : ℤᵒᵖ ⥤ DerivedCategory A) (E : DerivedCategory A)
    (π : system ⟶ (Functor.const ℤᵒᵖ).obj E)
    (π' : system' ⟶ (Functor.const ℤᵒᵖ).obj E)
    (hK : K.RealizesInverseSystem (Cocone.mk E π))
    (hK' : K'.RealizesInverseSystem (Cocone.mk E π')) :
    ∃ B : BifilteredCochainComplex A,
      B.base.RealizesInverseSystem (Cocone.mk E π) ∧
        B.second.RealizesInverseSystem (Cocone.mk E π') := by
  -- Package the two filtered complexes using the supplied equality of underlying complexes.
  refine ⟨⟨K, K', hEq⟩, hK, hK'⟩

/-- Helper for Lemma 19.13.13: a derived comparison into a K-injective representative can be
strictified to an actual quasi-isomorphism of cochain complexes. -/
lemma exists_quasiIso_to_kInjective_of_pointIso
    (L K : CochainComplex A ℤ) [K.IsKInjective]
    (e : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj K) :
    ∃ u : L ⟶ K, QuasiIso u ∧ DerivedCategory.Q.map u = e.hom := by
  let KQ := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let eQh :
      DerivedCategory.Qh.obj (KQ.obj L) ≅ DerivedCategory.Qh.obj (KQ.obj K) :=
    (DerivedCategory.quotientCompQhIso A).app L ≪≫
      e ≪≫
        ((DerivedCategory.quotientCompQhIso A).app K).symm
  obtain ⟨uQ, huQh⟩ :=
    (CochainComplex.IsKInjective.Qh_map_bijective (KQ.obj L) K).surjective eQh.hom
  obtain ⟨u, rfl⟩ := KQ.map_surjective uQ
  refine ⟨u, ?_, ?_⟩
  · -- Proof comment: once `Q.map u` is identified with the isomorphism `e.hom`, `u` is a
    -- quasi-isomorphism by the standard derived-category criterion.
    have hQmap : DerivedCategory.Q.map u = e.hom := by
      have hcongr := congrArg
        (Iso.homCongr ((DerivedCategory.quotientCompQhIso A).app L)
          ((DerivedCategory.quotientCompQhIso A).app K)) huQh
      have hmap :
          (Iso.homCongr ((DerivedCategory.quotientCompQhIso A).app L)
            ((DerivedCategory.quotientCompQhIso A).app K))
              (DerivedCategory.Qh.map (KQ.map u)) =
            DerivedCategory.Q.map u := by
        -- Proof comment: this is the naturality square for `quotientCompQhIso`, rewritten as a
        -- conjugation identity on morphisms.
        change
          (DerivedCategory.quotientCompQhIso A).inv.app L ≫
              DerivedCategory.Qh.map (KQ.map u) ≫
                (DerivedCategory.quotientCompQhIso A).hom.app K =
            DerivedCategory.Q.map u
        have hnat :
            DerivedCategory.Qh.map (KQ.map u) ≫
                (DerivedCategory.quotientCompQhIso A).hom.app K =
              (DerivedCategory.quotientCompQhIso A).hom.app L ≫
                DerivedCategory.Q.map u := by
          simpa [Functor.comp_map] using
            ((DerivedCategory.quotientCompQhIso A).hom.naturality u)
        calc
          (DerivedCategory.quotientCompQhIso A).inv.app L ≫
              DerivedCategory.Qh.map (KQ.map u) ≫
                (DerivedCategory.quotientCompQhIso A).hom.app K =
            (DerivedCategory.quotientCompQhIso A).inv.app L ≫
              ((DerivedCategory.quotientCompQhIso A).hom.app L ≫
                DerivedCategory.Q.map u) := by
                  simpa [Category.assoc] using
                    congrArg
                      (fun k ↦ (DerivedCategory.quotientCompQhIso A).inv.app L ≫ k) hnat
          _ = DerivedCategory.Q.map u := by
            simpa using
              (Iso.inv_hom_id_assoc ((DerivedCategory.quotientCompQhIso A).app L)
                (DerivedCategory.Q.map u))
      calc
        DerivedCategory.Q.map u =
            (Iso.homCongr ((DerivedCategory.quotientCompQhIso A).app L)
              ((DerivedCategory.quotientCompQhIso A).app K))
                (DerivedCategory.Qh.map (KQ.map u)) := by
              simpa using hmap.symm
        _ =
            (Iso.homCongr ((DerivedCategory.quotientCompQhIso A).app L)
              ((DerivedCategory.quotientCompQhIso A).app K)) eQh.hom := by
              simpa using hcongr
        _ = e.hom := by
          change
            (DerivedCategory.quotientCompQhIso A).inv.app L ≫
                ((DerivedCategory.quotientCompQhIso A).hom.app L ≫
                  e.hom ≫
                    (DerivedCategory.quotientCompQhIso A).inv.app K) ≫
                  (DerivedCategory.quotientCompQhIso A).hom.app K =
              e.hom
          have hleft :
              (DerivedCategory.quotientCompQhIso A).inv.app L ≫
                  ((DerivedCategory.quotientCompQhIso A).hom.app L ≫
                    e.hom ≫
                      (DerivedCategory.quotientCompQhIso A).inv.app K) ≫
                    (DerivedCategory.quotientCompQhIso A).hom.app K =
                e.hom ≫
                  (DerivedCategory.quotientCompQhIso A).inv.app K ≫
                    (DerivedCategory.quotientCompQhIso A).hom.app K := by
            simpa [Category.assoc] using
              (Iso.inv_hom_id_assoc ((DerivedCategory.quotientCompQhIso A).app L)
                (e.hom ≫
                  (DerivedCategory.quotientCompQhIso A).inv.app K ≫
                    (DerivedCategory.quotientCompQhIso A).hom.app K))
          calc
            (DerivedCategory.quotientCompQhIso A).inv.app L ≫
                ((DerivedCategory.quotientCompQhIso A).hom.app L ≫
                  e.hom ≫
                    (DerivedCategory.quotientCompQhIso A).inv.app K) ≫
                  (DerivedCategory.quotientCompQhIso A).hom.app K =
              e.hom ≫
                (DerivedCategory.quotientCompQhIso A).inv.app K ≫
                  (DerivedCategory.quotientCompQhIso A).hom.app K := hleft
            _ = e.hom := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ e.hom ≫ k)
                  (Iso.inv_hom_id ((DerivedCategory.quotientCompQhIso A).app K))
    letI : IsIso (DerivedCategory.Q.map u) := by
      rw [hQmap]
      infer_instance
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso A u).1 inferInstance
  · -- Proof comment: the chosen map represents `e.hom` by construction.
    have hcongr := congrArg
      (Iso.homCongr ((DerivedCategory.quotientCompQhIso A).app L)
        ((DerivedCategory.quotientCompQhIso A).app K)) huQh
    have hmap :
        (Iso.homCongr ((DerivedCategory.quotientCompQhIso A).app L)
          ((DerivedCategory.quotientCompQhIso A).app K))
            (DerivedCategory.Qh.map (KQ.map u)) =
          DerivedCategory.Q.map u := by
      -- Proof comment: conjugating the `Qh`-image of `u` across `quotientCompQhIso` recovers
      -- the ordinary derived-category image.
      change
        (DerivedCategory.quotientCompQhIso A).inv.app L ≫
            DerivedCategory.Qh.map (KQ.map u) ≫
              (DerivedCategory.quotientCompQhIso A).hom.app K =
          DerivedCategory.Q.map u
      have hnat :
          DerivedCategory.Qh.map (KQ.map u) ≫
              (DerivedCategory.quotientCompQhIso A).hom.app K =
            (DerivedCategory.quotientCompQhIso A).hom.app L ≫
              DerivedCategory.Q.map u := by
        simpa [Functor.comp_map] using
          ((DerivedCategory.quotientCompQhIso A).hom.naturality u)
      calc
        (DerivedCategory.quotientCompQhIso A).inv.app L ≫
            DerivedCategory.Qh.map (KQ.map u) ≫
              (DerivedCategory.quotientCompQhIso A).hom.app K =
          (DerivedCategory.quotientCompQhIso A).inv.app L ≫
            ((DerivedCategory.quotientCompQhIso A).hom.app L ≫
              DerivedCategory.Q.map u) := by
                simpa [Category.assoc] using
                  congrArg
                    (fun k ↦ (DerivedCategory.quotientCompQhIso A).inv.app L ≫ k) hnat
        _ = DerivedCategory.Q.map u := by
          simpa using
            (Iso.inv_hom_id_assoc ((DerivedCategory.quotientCompQhIso A).app L)
              (DerivedCategory.Q.map u))
    calc
      DerivedCategory.Q.map u =
          (Iso.homCongr ((DerivedCategory.quotientCompQhIso A).app L)
            ((DerivedCategory.quotientCompQhIso A).app K))
              (DerivedCategory.Qh.map (KQ.map u)) := by
            simpa using hmap.symm
      _ =
          (Iso.homCongr ((DerivedCategory.quotientCompQhIso A).app L)
            ((DerivedCategory.quotientCompQhIso A).app K)) eQh.hom := by
            simpa using hcongr
      _ = e.hom := by
        change
          (DerivedCategory.quotientCompQhIso A).inv.app L ≫
              ((DerivedCategory.quotientCompQhIso A).hom.app L ≫
                e.hom ≫
                  (DerivedCategory.quotientCompQhIso A).inv.app K) ≫
                (DerivedCategory.quotientCompQhIso A).hom.app K =
            e.hom
        have hleft :
            (DerivedCategory.quotientCompQhIso A).inv.app L ≫
                ((DerivedCategory.quotientCompQhIso A).hom.app L ≫
                  e.hom ≫
                    (DerivedCategory.quotientCompQhIso A).inv.app K) ≫
                  (DerivedCategory.quotientCompQhIso A).hom.app K =
              e.hom ≫
                (DerivedCategory.quotientCompQhIso A).inv.app K ≫
                  (DerivedCategory.quotientCompQhIso A).hom.app K := by
          simpa [Category.assoc] using
            (Iso.inv_hom_id_assoc ((DerivedCategory.quotientCompQhIso A).app L)
              (e.hom ≫
                (DerivedCategory.quotientCompQhIso A).inv.app K ≫
                  (DerivedCategory.quotientCompQhIso A).hom.app K))
        calc
          (DerivedCategory.quotientCompQhIso A).inv.app L ≫
              ((DerivedCategory.quotientCompQhIso A).hom.app L ≫
                e.hom ≫
                  (DerivedCategory.quotientCompQhIso A).inv.app K) ≫
                (DerivedCategory.quotientCompQhIso A).hom.app K =
            e.hom ≫
              (DerivedCategory.quotientCompQhIso A).inv.app K ≫
                (DerivedCategory.quotientCompQhIso A).hom.app K := hleft
          _ = e.hom := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ e.hom ≫ k)
                (Iso.inv_hom_id ((DerivedCategory.quotientCompQhIso A).app K))

-- Proof sketch: first choose a filtered realization of the system `E^i ⟶ E` as in Lemma
-- `19.13.12`, then choose a second filtered realization of `(E')^i ⟶ E`. Replace the first one by
-- a filtered K-injective complex using Lemma `19.13.7`, map the second realization into that
-- K-injective representative, and add an acyclic K-injective correction so that both maps into a
-- common target become termwise injective quasi-isomorphisms. Transport the two filtrations by
-- images to the common target to obtain the required bifiltered complex.
/-- Lemma 19.13.13: given two compatible inverse systems `E^i ⟶ E` and `(E')^i ⟶ E` in the
derived category of a Grothendieck abelian category, there exists a bifiltered cochain complex
whose underlying complex represents `E`, whose first filtration stages `F^i K^•` represent
`E^i`, and whose second filtration stages `(F')^i K^•` represent `(E')^i`, compatibly with the
given maps. -/
theorem exists_bifilteredCochainComplexRealization_of_inverseSystems
    (system system' : ℤᵒᵖ ⥤ DerivedCategory A) (E : DerivedCategory A)
    (π : system ⟶ (Functor.const ℤᵒᵖ).obj E)
    (π' : system' ⟶ (Functor.const ℤᵒᵖ).obj E) :
    ∃ K : BifilteredCochainComplex A,
      K.base.RealizesInverseSystem (Cocone.mk E π) ∧
        K.second.RealizesInverseSystem (Cocone.mk E π') := by
  -- Proof comment: first realize the first inverse system, then replace only the underlying
  -- complex by a K-injective one. The remaining filtration work is to push the realization
  -- forward along the resulting mono quasi-isomorphism into a common target.
  obtain ⟨K₀, hK₀⟩ :=
    exists_filteredCochainComplexRealization_of_inverseSystem
      (A := A) system (Cocone.mk E π)
  -- Route correction: the stable prefix is the first filtered realization `K₀`. The next step is
  -- to replace `K₀.underlying` by a mono quasi-isomorphic K-injective complex, retarget the
  -- second inverse system to that concrete representative, and then strictify the second
  -- comparison map by `exists_quasiIso_to_kInjective_of_pointIso`.
  -- TODO: import or restore a dependency-closed theorem giving a mono quasi-isomorphic
  -- K-injective replacement of `K₀.underlying` inside the current Lake build state; then push the
  -- two filtrations to a common target and invoke
  -- `exists_bifilteredCochainComplex_of_commonUnderlying`.
  sorry

end

end CategoryTheory
