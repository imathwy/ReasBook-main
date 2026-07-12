import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Lemma_17_28_12
import Mathlib.AlgebraicGeometry.Modules.Sheaf

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory AlgebraicGeometry.RingedSpace.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Domain-style sampling for Lemma 17.28.13:
- primary domain: functoriality of the canonical base-change morphism on relative differentials;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.pullbackDifferentialsComparison`,
  `AlgebraicGeometry.RingedSpace.pullbackDifferentialsComparison_unique`,
  `SheafOfModules.pullbackComp`,
  `CategoryTheory.CommSq.horiz_comp`;
- best owner abstraction:
  the source-facing base-change morphism `pullbackDifferentialsComparison`, with
  `SheafOfModules.pullbackComp` as the canonical bridge from pullback along a composite to the
  iterated pullback;
- primitive data:
  only the two composable commutative squares `hf` and `hg`;
- derived API:
  compatibility of the canonical comparison morphism with composition.

Source/core/bridge triage:
- `source-facing`: the composition law for the comparison morphisms on relative differentials;
- `core/canonical`: `pullbackDifferentialsComparison`, `pullbackDifferentialsComparison_unique`,
  and `SheafOfModules.pullbackComp`;
- `bridge/view`: `CommSq.horiz_comp` and the adjunction transposes appearing in the proof.

The local theorem `pullbackDifferentialsComparison_outer_square_commutes` was a duplicate wrapper
around `CommSq.horiz_comp`, so this file should use the owner declaration directly. -/

namespace AlgebraicGeometry.RingedSpace

variable {X X' X'' S S' S'' : RingedSpace.{u}}

/-
Proof sketch: prove that the iterated base-change morphism satisfies the same sectionwise
characterization as the canonical morphism for the pasted square, then apply the uniqueness
statement from Lemma `17.28.12`.

Lemma 17.28.13: the comparison morphism on relative differentials is compatible with composition,
so the map for the outer rectangle equals `c_g ∘ g^* c_f` after identifying `(f \circ g)^*` with
the iterated pullback.
-/
/-- Helper for Lemma 17.28.13: the structure-sheaf map of a composite morphism of ringed spaces
acts on local sections by the expected composite of the two structure-sheaf maps. -/
private theorem toRingCatSheafHom_comp_app
    (f : X' ⟶ X) (g : X'' ⟶ X')
    (U : (TopologicalSpace.Opens X)ᵒᵖ) (x : X.presheaf.obj U) :
    ((toRingCatSheafHom (g ≫ f)).hom.app U) x =
      ((toRingCatSheafHom g).hom.app ((TopologicalSpace.Opens.map f.hom.base).op.obj U))
        (((toRingCatSheafHom f).hom.app U) x) := by
  rfl

/-- Helper for Lemma 17.28.13: under the composed pullback-pushforward adjunction, the iterated
comparison morphism is the nested adjoint composite. -/
private theorem pullbackDifferentialsComparison_comp_composed_adjunction
    (f : X' ⟶ X) (g : X'' ⟶ X')
    (s : S' ⟶ S) (t : S'' ⟶ S')
    (h : X ⟶ S) (h' : X' ⟶ S') (h'' : X'' ⟶ S'')
    (hf : CommSq f h' h s) (hg : CommSq g h'' h' t) :
    let adjf := SheafOfModules.pullbackPushforwardAdjunction (toRingCatSheafHom f)
    let adjg := SheafOfModules.pullbackPushforwardAdjunction (toRingCatSheafHom g)
    ((CategoryTheory.Adjunction.comp adjf adjg).homEquiv Ω[h] Ω[h''])
      ((g^*).map (pullbackDifferentialsComparison f s h h' hf) ≫
        pullbackDifferentialsComparison g t h' h'' hg) =
    (adjf.homEquiv Ω[h] ((SheafOfModules.pushforward (toRingCatSheafHom g)).obj Ω[h'']))
      (pullbackDifferentialsComparison f s h h' hf ≫
        (adjg.homEquiv Ω[h'] Ω[h''])
          (pullbackDifferentialsComparison g t h' h'' hg)) := by
  dsimp
  -- Rewrite the composite adjunction in terms of the two successive adjunctions.
  rw [CategoryTheory.Adjunction.comp_homEquiv]
  -- Then the first adjunction consumes `g^* c_f`, leaving the adjoint of `c_g`.
  change ((SheafOfModules.pullbackPushforwardAdjunction (toRingCatSheafHom f)).homEquiv Ω[h]
      ((SheafOfModules.pushforward (toRingCatSheafHom g)).obj Ω[h'']))
    (((SheafOfModules.pullbackPushforwardAdjunction (toRingCatSheafHom g)).homEquiv
      ((SheafOfModules.pullback (toRingCatSheafHom f)).obj Ω[h]) Ω[h''])
      ((g^*).map (pullbackDifferentialsComparison f s h h' hf) ≫
        pullbackDifferentialsComparison g t h' h'' hg)) = _
  rw [CategoryTheory.Adjunction.homEquiv_naturality_left
    (SheafOfModules.pullbackPushforwardAdjunction (toRingCatSheafHom g))
    (pullbackDifferentialsComparison f s h h' hf)
    (pullbackDifferentialsComparison g t h' h'' hg)]

/-- Helper for Lemma 17.28.13: the `pullbackComp` comparison has identity mate on the
pushforward side, so it transports the outer adjoint to the composite adjoint without changing
the resulting sectionwise map. -/
private theorem pullbackDifferentialsComparison_comp_bridge
    (f : X' ⟶ X) (g : X'' ⟶ X')
    (s : S' ⟶ S) (t : S'' ⟶ S')
    (h : X ⟶ S) (h' : X' ⟶ S') (h'' : X'' ⟶ S'')
    (hf : CommSq f h' h s) (hg : CommSq g h'' h' t) :
    let adjfg := SheafOfModules.pullbackPushforwardAdjunction (toRingCatSheafHom (g ≫ f))
    let adjf := SheafOfModules.pullbackPushforwardAdjunction (toRingCatSheafHom f)
    let adjg := SheafOfModules.pullbackPushforwardAdjunction (toRingCatSheafHom g)
    let compAdj := CategoryTheory.Adjunction.comp adjf adjg
    let τ0 :=
      (g^*).map (pullbackDifferentialsComparison f s h h' hf) ≫
        pullbackDifferentialsComparison g t h' h'' hg
    ((adjfg.homEquiv Ω[h] Ω[h''])
      (((SheafOfModules.pullbackComp
            (toRingCatSheafHom f)
            (toRingCatSheafHom g)).symm.hom.app Ω[h]) ≫ τ0)) =
      (compAdj.homEquiv Ω[h] Ω[h'']) τ0 := by
  dsimp
  let adjfg := SheafOfModules.pullbackPushforwardAdjunction (toRingCatSheafHom (g ≫ f))
  let adjf := SheafOfModules.pullbackPushforwardAdjunction (toRingCatSheafHom f)
  let adjg := SheafOfModules.pullbackPushforwardAdjunction (toRingCatSheafHom g)
  let compAdj := CategoryTheory.Adjunction.comp adjf adjg
  let pullIter :=
    (SheafOfModules.pullback (toRingCatSheafHom f)) ⋙
      (SheafOfModules.pullback (toRingCatSheafHom g))
  let pushIter :=
    (SheafOfModules.pushforward (toRingCatSheafHom g)) ⋙
      (SheafOfModules.pushforward (toRingCatSheafHom f))
  let τ0 :=
    (g^*).map (pullbackDifferentialsComparison f s h h' hf) ≫
      pullbackDifferentialsComparison g t h' h'' hg
  let α :=
    (SheafOfModules.pullbackComp
      (toRingCatSheafHom f)
      (toRingCatSheafHom g)).symm.hom
  let β :=
    (SheafOfModules.pushforwardComp
      (toRingCatSheafHom f)
      (toRingCatSheafHom g)).hom
  have hβ :
      CategoryTheory.conjugateEquiv compAdj adjfg α = β := by
    dsimp [compAdj, adjf, adjg, adjfg, α, β]
    exact SheafOfModules.conjugateEquiv_pullbackComp_inv
      (toRingCatSheafHom f)
      (toRingCatSheafHom g)
  have hβunit :
      compAdj.unit.app Ω[h] ≫
          β.app ((SheafOfModules.pullback (toRingCatSheafHom g)).obj
            ((SheafOfModules.pullback (toRingCatSheafHom f)).obj Ω[h])) =
        adjfg.unit.app Ω[h] ≫
          (SheafOfModules.pushforward (toRingCatSheafHom (g ≫ f))).map (α.app Ω[h]) := by
    have hβunit' := CategoryTheory.unit_conjugateEquiv compAdj adjfg α Ω[h]
    rw [hβ] at hβunit'
    exact hβunit'
  have hmate :
      (adjfg.homEquiv Ω[h] Ω[h'']) (α.app Ω[h] ≫ τ0) =
        (compAdj.homEquiv Ω[h] Ω[h'']) τ0 ≫ β.app Ω[h''] := by
    have h1 :
        (adjfg.homEquiv Ω[h] Ω[h'']) (α.app Ω[h] ≫ τ0) =
          adjfg.unit.app Ω[h] ≫
            (SheafOfModules.pushforward (toRingCatSheafHom (g ≫ f))).map
              (α.app Ω[h] ≫ τ0) :=
      CategoryTheory.Adjunction.homEquiv_unit (adj := adjfg) (f := α.app Ω[h] ≫ τ0)
    have h2 :
        adjfg.unit.app Ω[h] ≫
            (SheafOfModules.pushforward (toRingCatSheafHom (g ≫ f))).map
              (α.app Ω[h] ≫ τ0) =
          adjfg.unit.app Ω[h] ≫
            (SheafOfModules.pushforward (toRingCatSheafHom (g ≫ f))).map (α.app Ω[h]) ≫
              (SheafOfModules.pushforward (toRingCatSheafHom (g ≫ f))).map τ0 := by
      simpa [Functor.map_comp, Category.assoc]
    have h3 :
        adjfg.unit.app Ω[h] ≫
            (SheafOfModules.pushforward (toRingCatSheafHom (g ≫ f))).map (α.app Ω[h]) ≫
              (SheafOfModules.pushforward (toRingCatSheafHom (g ≫ f))).map τ0 =
          compAdj.unit.app Ω[h] ≫
            β.app ((SheafOfModules.pullback (toRingCatSheafHom g)).obj
              ((SheafOfModules.pullback (toRingCatSheafHom f)).obj Ω[h])) ≫
            (SheafOfModules.pushforward (toRingCatSheafHom (g ≫ f))).map τ0 := by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ k ≫
            (SheafOfModules.pushforward (toRingCatSheafHom (g ≫ f))).map τ0)
          hβunit.symm
    have h4 :
        compAdj.unit.app Ω[h] ≫
            β.app ((SheafOfModules.pullback (toRingCatSheafHom g)).obj
              ((SheafOfModules.pullback (toRingCatSheafHom f)).obj Ω[h])) ≫
            (SheafOfModules.pushforward (toRingCatSheafHom (g ≫ f))).map τ0 =
          compAdj.unit.app Ω[h] ≫ pushIter.map τ0 ≫ β.app Ω[h''] := by
      simpa [pushIter, Category.assoc] using
        congrArg (fun k ↦ compAdj.unit.app Ω[h] ≫ k) (β.naturality τ0).symm
    have h5 :
        compAdj.unit.app Ω[h] ≫ pushIter.map τ0 ≫ β.app Ω[h''] =
          (compAdj.homEquiv Ω[h] Ω[h'']) τ0 ≫ β.app Ω[h''] := by
      simpa [Category.assoc] using
        congrArg (fun k ↦ k ≫ β.app Ω[h''])
          (CategoryTheory.Adjunction.homEquiv_unit (adj := compAdj) (f := τ0)).symm
    exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
  have hβid : β.app Ω[h''] = 𝟙 _ := by
    ext U x
    rfl
  simpa [α, hβid] using hmate

/-- Helper for Lemma 17.28.13: the iterated comparison map satisfies the characterizing property
for the outer square once the pullback-composition bridge is inserted. -/
private theorem pullbackDifferentialsComparison_comp_property
    (f : X' ⟶ X) (g : X'' ⟶ X')
    (s : S' ⟶ S) (t : S'' ⟶ S')
    (h : X ⟶ S) (h' : X' ⟶ S') (h'' : X'' ⟶ S'')
    (hf : CommSq f h' h s) (hg : CommSq g h'' h' t) :
    pullbackDifferentialsComparisonProperty (g ≫ f) h h''
      (((SheafOfModules.pullbackComp
            (toRingCatSheafHom f)
            (toRingCatSheafHom g)).symm.hom.app Ω[h]) ≫
        (g^*).map (pullbackDifferentialsComparison f s h h' hf) ≫
        pullbackDifferentialsComparison g t h' h'' hg) := by
  intro U x
  dsimp
  let adjfg := SheafOfModules.pullbackPushforwardAdjunction (toRingCatSheafHom (g ≫ f))
  let adjf := SheafOfModules.pullbackPushforwardAdjunction (toRingCatSheafHom f)
  let adjg := SheafOfModules.pullbackPushforwardAdjunction (toRingCatSheafHom g)
  let compAdj := CategoryTheory.Adjunction.comp adjf adjg
  let τ :=
    ((SheafOfModules.pullbackComp
          (toRingCatSheafHom f)
          (toRingCatSheafHom g)).symm.hom.app Ω[h]) ≫
      (g^*).map (pullbackDifferentialsComparison f s h h' hf) ≫
      pullbackDifferentialsComparison g t h' h'' hg
  have hbridge :
      ((adjfg.homEquiv Ω[h] Ω[h'']) τ) =
        (compAdj.homEquiv Ω[h] Ω[h''])
          ((g^*).map (pullbackDifferentialsComparison f s h h' hf) ≫
            pullbackDifferentialsComparison g t h' h'' hg) := by
    -- Replace the former local gap by the dedicated mates bridge.
    exact pullbackDifferentialsComparison_comp_bridge f g s t h h' h'' hf hg
  have hbridge_app :
      ((((adjfg.homEquiv Ω[h] Ω[h'']) τ).val.app U) (((d[h]).app U).d x)) =
        ((((compAdj.homEquiv Ω[h] Ω[h''])
            ((g^*).map (pullbackDifferentialsComparison f s h h' hf) ≫
              pullbackDifferentialsComparison g t h' h'' hg)).val.app U)
          (((d[h]).app U).d x)) := by
    exact congrArg (fun k ↦ (k.val.app U) (((d[h]).app U).d x)) hbridge
  have hcomp_app :
      ((((compAdj.homEquiv Ω[h] Ω[h''])
          ((g^*).map (pullbackDifferentialsComparison f s h h' hf) ≫
            pullbackDifferentialsComparison g t h' h'' hg)).val.app U)
        (((d[h]).app U).d x)) =
        ((((adjf.homEquiv Ω[h] ((SheafOfModules.pushforward (toRingCatSheafHom g)).obj Ω[h'']))
            (pullbackDifferentialsComparison f s h h' hf ≫
              (adjg.homEquiv Ω[h'] Ω[h''])
                (pullbackDifferentialsComparison g t h' h'' hg))).val.app U)
          (((d[h]).app U).d x)) := by
    exact congrArg (fun k ↦ (k.val.app U) (((d[h]).app U).d x))
      (pullbackDifferentialsComparison_comp_composed_adjunction
        f g s t h h' h'' hf hg)
  -- The two existing characterizing theorems now apply in sequence.
  have hnatf := CategoryTheory.Adjunction.homEquiv_naturality_right adjf
    (pullbackDifferentialsComparison f s h h' hf)
    ((adjg.homEquiv Ω[h'] Ω[h''])
      (pullbackDifferentialsComparison g t h' h'' hg))
  have hnatf_app :
      ((((adjf.homEquiv Ω[h] ((SheafOfModules.pushforward (toRingCatSheafHom g)).obj Ω[h'']))
          (pullbackDifferentialsComparison f s h h' hf ≫
            (adjg.homEquiv Ω[h'] Ω[h''])
              (pullbackDifferentialsComparison g t h' h'' hg))).val.app U)
        (((d[h]).app U).d x)) =
        (((((adjf.homEquiv Ω[h] Ω[h'])
            (pullbackDifferentialsComparison f s h h' hf)) ≫
            (SheafOfModules.pushforward (toRingCatSheafHom f)).map
              ((adjg.homEquiv Ω[h'] Ω[h''])
                (pullbackDifferentialsComparison g t h' h'' hg))).val.app U)
          (((d[h]).app U).d x)) := by
    exact congrArg (fun k ↦ (k.val.app U) (((d[h]).app U).d x)) hnatf
  let adjgComp :=
    (adjg.homEquiv Ω[h'] Ω[h''])
      (pullbackDifferentialsComparison g t h' h'' hg)
  have hf_char :=
    pullbackDifferentialsComparison_characterizing f s h h' hf (U := U) x
  have hg_char :=
    pullbackDifferentialsComparison_characterizing g t h' h'' hg
      (U := (TopologicalSpace.Opens.map f.hom.base).op.obj U)
      (((toRingCatSheafHom f).hom.app U) x)
  have hf_char_mapped :
      (((((adjf.homEquiv Ω[h] Ω[h'])
            (pullbackDifferentialsComparison f s h h' hf)) ≫
            (SheafOfModules.pushforward (toRingCatSheafHom f)).map adjgComp).val.app U)
          (((d[h]).app U).d x)) =
        ((((SheafOfModules.pushforward (toRingCatSheafHom f)).map adjgComp).val.app U)
          (((d[h']).app ((TopologicalSpace.Opens.map f.hom.base).op.obj U)).d
            (((toRingCatSheafHom f).hom.app U) x))) := by
    exact congrArg
      (fun z ↦ (((SheafOfModules.pushforward (toRingCatSheafHom f)).map adjgComp).val.app U) z)
      hf_char
  -- Evaluate the first comparison map on the universal differential, then apply the second.
  refine Eq.trans hbridge_app ?_
  refine Eq.trans hcomp_app ?_
  refine Eq.trans hnatf_app ?_
  refine Eq.trans hf_char_mapped ?_
  simpa [adjgComp, toRingCatSheafHom_comp_app] using hg_char

/-- Lemma 17.28.13: for composable commutative squares of ringed spaces, the canonical
comparison morphism on relative differentials for the outer rectangle is the composite
`c_g ∘ g^* c_f`, after identifying pullback along a composite with the iterated pullback. -/
theorem pullbackDifferentialsComparison_comp
    (f : X' ⟶ X) (g : X'' ⟶ X')
    (s : S' ⟶ S) (t : S'' ⟶ S')
    (h : X ⟶ S) (h' : X' ⟶ S') (h'' : X'' ⟶ S'')
    (hf : CommSq f h' h s) (hg : CommSq g h'' h' t) :
    pullbackDifferentialsComparison (g ≫ f) (t ≫ s) h h'' (CommSq.horiz_comp hg hf) =
      ((SheafOfModules.pullbackComp
            (toRingCatSheafHom f)
            (toRingCatSheafHom g)).symm.hom.app Ω[h]) ≫
        (g^*).map (pullbackDifferentialsComparison f s h h' hf) ≫
        pullbackDifferentialsComparison g t h' h'' hg := by
  symm
  -- Uniqueness for the outer square reduces the theorem to the sectionwise characterization.
  apply pullbackDifferentialsComparison_unique (g ≫ f) (t ≫ s) h h'' (CommSq.horiz_comp hg hf)
  -- The iterated map satisfies the same generator formula as the canonical outer comparison map.
  exact pullbackDifferentialsComparison_comp_property f g s t h h' h'' hf hg

end AlgebraicGeometry.RingedSpace
