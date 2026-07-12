import Mathlib
import StacksProject_2024.Chap18.Lemma_18_36_4
import StacksProject_2024.Chap18.«18_40_2_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite Limits

universe u v

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type (max u v))]
variable [J.HasSheafCompose (forget CommRingCat.{max u v})]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

/-
Domain-style sampling for Lemma 18.40.3:
- primary domain: point stalks of sheaves of commutative rings on a site, together with
  conservativity of point-fiber functors under enough points;
- sampled relevant declarations:
  `oneNeverZeroEqualizerMap`,
  `GrothendieckTopology.Point.sheafFiber`,
  `sourcePointRing`,
  `GrothendieckTopology.HasEnoughPoints.exists_objectProperty`;
- best owner abstraction: the source-facing chapter map `oneNeverZeroEqualizerMap 𝒪`, with the
  stalk condition expressed through the chapter bridge owner `sourcePointRing 𝒪 p`, which is the
  commutative-ring view of `GrothendieckTopology.Point.sheafFiber`;
- primitive data: the sheaf `𝒪` and the point `p`;
- derived API: stalkwise nontriviality and the enough-points reflection equivalence.

Source/core/bridge triage:
- `source-facing`: the implication from the `18.40.2.1` isomorphism to nontriviality of every
  stalk, and the converse under enough points;
- `core/canonical`: `oneNeverZeroEqualizerMap`, `Point.sheafFiber`, and the enough-points
  conservativity machinery;
- `bridge/view`: the earlier ring-valued stalk abbreviation `sourcePointRing`, which is the
  commutative-ring view of `Point.sheafFiber`.

The old single conjunction-valued theorem bundled two mathematically separate clauses and repeated
the raw stalk object expression. This file should expose the two source-facing clauses as atomic
theorems, while stating the stalk condition through the canonical chapter bridge `sourcePointRing`.
-/

-- Proof sketch: apply the stalk functor at a point `p` to the canonical morphism
-- `\emptyset^\# \to \operatorname{Equalizer}(0,1 : * \to \mathcal O)`. The source stalk remains
-- initial, while the target stalk identifies with the equalizer of `0, 1 : PUnit ⟶ \mathcal O_p`,
-- which is empty exactly when `0 ≠ 1` in the stalk ring, i.e. exactly when the stalk is
-- nontrivial. This gives `(1) → (2)`. If `J` has enough points, then the stalk functors are
-- conservative on sheaves, so the converse follows by checking that the displayed map is an
-- isomorphism on every point stalk.

/-- Helper for Lemma 18.40.3: the canonical morphism from any sheaf to the terminal `Type`-valued
sheaf is pointwise the unique map into `PUnit`. -/
theorem sheaf_terminal_hom_eq
    {F : Sheaf J (Type (max u v))}
    (f : F ⟶ (Sheaf.terminal J Types.isTerminalPUnit : Sheaf J (Type (max u v))))
    (U : Cᵒᵖ) (x : F.obj.obj U) :
    f.hom.app U x = PUnit.unit := by
  -- Every section of the terminal sheaf is the unique element of `PUnit`.
  cases f.hom.app U x
  rfl

/-- Helper for Lemma 18.40.3: the terminal `Type`-valued sheaf is terminal in the sheaf
category. -/
noncomputable def sheaf_terminal_isTerminal :
    IsTerminal (Sheaf.terminal J Types.isTerminalPUnit : Sheaf J (Type (max u v))) :=
  IsTerminal.ofUniqueHom
    (fun F ↦
      { hom :=
          { app := fun U _ ↦ PUnit.unit
            naturality := fun _ _ _ ↦ rfl } })
    (fun F f ↦ by
      ext U x
      exact sheaf_terminal_hom_eq (J := J) f U x)

/-- Helper for Lemma 18.40.3: the `Type`-valued point fiber of the underlying sheaf agrees with
the carrier of the ring-valued point fiber. -/
noncomputable def point_ring_carrier_iso
    (p : GrothendieckTopology.Point.{max u v} J) :
    p.sheafFiber.obj ((sheafCompose J (forget CommRingCat.{max u v})).obj 𝒪) ≅
      (forget CommRingCat.{max u v}).obj (sourcePointRing 𝒪 p) :=
  (preservesColimitIso (forget CommRingCat.{max u v})
    (((Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π p.fiber).op).obj 𝒪.obj)).symm

/-- Helper for Lemma 18.40.3: the point fiber of the terminal `Type`-valued sheaf identifies with
the terminal object of `Type`. -/
noncomputable def point_terminal_iso
    (p : GrothendieckTopology.Point.{max u v} J) :
    p.sheafFiber.obj (Sheaf.terminal J Types.isTerminalPUnit) ≅ ⊤_ (Type (max u v)) :=
  (p.sheafFiber.mapIso (terminalIsoIsTerminal (sheaf_terminal_isTerminal (J := J)))).symm ≪≫
    PreservesTerminal.iso p.sheafFiber

/-- Helper for Lemma 18.40.3: the stalk of the sheafification of the empty presheaf is empty. -/
theorem point_fiber_empty_sheafification_isEmpty
    (p : GrothendieckTopology.Point.{max u v} J) :
    IsEmpty (p.sheafFiber.obj
      ((presheafToSheaf J (Type (max u v))).obj (⊥_ (Cᵒᵖ ⥤ Type (max u v))))) := by
  -- Compare with the raw presheaf fiber, then use that point fibers preserve the initial colimit.
  let e := (p.presheafToSheafCompSheafFiberIso (Type (max u v))).app
    (⊥_ (Cᵒᵖ ⥤ Type (max u v)))
  have hPresheafEmpty : IsEmpty (p.presheafFiber.obj (⊥_ (Cᵒᵖ ⥤ Type (max u v)))) := by
    let e₀ : p.presheafFiber.obj (⊥_ (Cᵒᵖ ⥤ Type (max u v))) ≅ ⊥_ (Type (max u v)) :=
      PreservesInitial.iso p.presheafFiber
    have hInitialEmpty : IsEmpty (⊥_ (Type (max u v))) :=
      (Types.initial_iff_empty _).1 ⟨initialIsInitial⟩
    exact ⟨fun x ↦ hInitialEmpty.false (e₀.hom x)⟩
  exact ⟨fun x ↦ hPresheafEmpty.false (e.hom x)⟩

/-- Helper for Lemma 18.40.3: after taking the point fiber, the zero section evaluates to the zero
element of the stalk ring carrier. -/
theorem point_fiber_zeroSection_apply_eq_zero
    (p : GrothendieckTopology.Point.{max u v} J)
    (t : p.sheafFiber.obj (Sheaf.terminal J Types.isTerminalPUnit)) :
    (point_ring_carrier_iso (𝒪 := 𝒪) p).hom
      (p.sheafFiber.map (zeroSection 𝒪) t) = 0 := by
  -- Represent the terminal-stalk element by a stage of the filtered colimit, then compute there.
  let t' : ToType (p.presheafFiber.obj (Sheaf.terminal J Types.isTerminalPUnit).obj) := t
  obtain ⟨X, x, z, rfl⟩ := p.toPresheafFiber_jointly_surjective
    (P := (Sheaf.terminal J Types.isTerminalPUnit).obj) t'
  cases z
  simp only [GrothendieckTopology.Point.sheafFiber, Functor.comp_obj, Functor.comp_map]
  have h := congrFun (p.toPresheafFiber_naturality
    ((sheafToPresheaf J (Type (max u v))).map (zeroSection 𝒪)) X x) PUnit.unit
  have hs :
      (point_ring_carrier_iso (𝒪 := 𝒪) p).hom
        ((((sheafToPresheaf J (Type (max u v))).map (zeroSection 𝒪)).app (op X) ≫
            p.toPresheafFiber X x
              ((sheafToPresheaf J (Type (max u v))).obj
                ((sheafCompose J (forget CommRingCat.{max u v})).obj 𝒪)))
          PUnit.unit) = 0 := by
    -- This is the image of `0` under the corresponding ring-colimit injection.
    change
      (preservesColimitIso (forget CommRingCat.{max u v})
          (((Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π p.fiber).op).obj 𝒪.obj)).inv
        (colimit.ι ((((Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π p.fiber).op).obj
            𝒪.obj) ⋙ forget CommRingCat.{max u v}) (op ⟨X, x⟩) 0) = 0
    have hι := congrFun (ι_preservesColimitIso_inv (forget CommRingCat.{max u v})
      (((Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π p.fiber).op).obj 𝒪.obj)
      (op ⟨X, x⟩)) 0
    have hι' :
        (preservesColimitIso (forget CommRingCat.{max u v})
            (((Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π p.fiber).op).obj
              𝒪.obj)).inv
          (colimit.ι ((((Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π p.fiber).op).obj
              𝒪.obj) ⋙ forget CommRingCat.{max u v}) (op ⟨X, x⟩) 0) =
        ((colimit.ι (((Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π p.fiber).op).obj
            𝒪.obj) (op ⟨X, x⟩)).hom) 0 := by
      simpa [CategoryTheory.types_comp_apply] using hι
    calc
      (preservesColimitIso (forget CommRingCat.{max u v})
          (((Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π p.fiber).op).obj 𝒪.obj)).inv
        (colimit.ι ((((Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π p.fiber).op).obj
            𝒪.obj) ⋙ forget CommRingCat.{max u v}) (op ⟨X, x⟩) 0)
          = ((colimit.ι (((Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π p.fiber).op).obj
                𝒪.obj) (op ⟨X, x⟩)).hom) 0 := hι'
      _ = 0 := by
        simpa using ((colimit.ι (((Functor.whiskeringLeft _ _ _).obj
          (CategoryOfElements.π p.fiber).op).obj 𝒪.obj) (op ⟨X, x⟩)).hom.map_zero)
  have h' := congrArg ((point_ring_carrier_iso (𝒪 := 𝒪) p).hom) h
  calc
    (point_ring_carrier_iso (𝒪 := 𝒪) p).hom
        (p.presheafFiber.map ((sheafToPresheaf J (Type (max u v))).map (zeroSection 𝒪))
          (p.toPresheafFiber X x (Sheaf.terminal J Types.isTerminalPUnit).obj PUnit.unit))
        = (point_ring_carrier_iso (𝒪 := 𝒪) p).hom
            ((((sheafToPresheaf J (Type (max u v))).map (zeroSection 𝒪)).app (op X) ≫
                p.toPresheafFiber X x
                  ((sheafToPresheaf J (Type (max u v))).obj
                    ((sheafCompose J (forget CommRingCat.{max u v})).obj 𝒪)))
              PUnit.unit) := by
            simpa [CategoryTheory.types_comp_apply] using h'
    _ = 0 := hs

/-- Helper for Lemma 18.40.3: after taking the point fiber, the unit section evaluates to the
unit element of the stalk ring carrier. -/
theorem point_fiber_oneSection_apply_eq_one
    (p : GrothendieckTopology.Point.{max u v} J)
    (t : p.sheafFiber.obj (Sheaf.terminal J Types.isTerminalPUnit)) :
    (point_ring_carrier_iso (𝒪 := 𝒪) p).hom
      (p.sheafFiber.map (oneSection 𝒪) t) = 1 := by
  -- Represent the terminal-stalk element by a stage of the filtered colimit, then compute there.
  let t' : ToType (p.presheafFiber.obj (Sheaf.terminal J Types.isTerminalPUnit).obj) := t
  obtain ⟨X, x, z, rfl⟩ := p.toPresheafFiber_jointly_surjective
    (P := (Sheaf.terminal J Types.isTerminalPUnit).obj) t'
  cases z
  simp only [GrothendieckTopology.Point.sheafFiber, Functor.comp_obj, Functor.comp_map]
  have h := congrFun (p.toPresheafFiber_naturality
    ((sheafToPresheaf J (Type (max u v))).map (oneSection 𝒪)) X x) PUnit.unit
  have hs :
      (point_ring_carrier_iso (𝒪 := 𝒪) p).hom
        ((((sheafToPresheaf J (Type (max u v))).map (oneSection 𝒪)).app (op X) ≫
            p.toPresheafFiber X x
              ((sheafToPresheaf J (Type (max u v))).obj
                ((sheafCompose J (forget CommRingCat.{max u v})).obj 𝒪)))
          PUnit.unit) = 1 := by
    -- This is the image of `1` under the corresponding ring-colimit injection.
    change
      (preservesColimitIso (forget CommRingCat.{max u v})
          (((Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π p.fiber).op).obj 𝒪.obj)).inv
        (colimit.ι ((((Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π p.fiber).op).obj
            𝒪.obj) ⋙ forget CommRingCat.{max u v}) (op ⟨X, x⟩) 1) = 1
    have hι := congrFun (ι_preservesColimitIso_inv (forget CommRingCat.{max u v})
      (((Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π p.fiber).op).obj 𝒪.obj)
      (op ⟨X, x⟩)) 1
    have hι' :
        (preservesColimitIso (forget CommRingCat.{max u v})
            (((Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π p.fiber).op).obj
              𝒪.obj)).inv
          (colimit.ι ((((Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π p.fiber).op).obj
              𝒪.obj) ⋙ forget CommRingCat.{max u v}) (op ⟨X, x⟩) 1) =
        ((colimit.ι (((Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π p.fiber).op).obj
            𝒪.obj) (op ⟨X, x⟩)).hom) 1 := by
      simpa [CategoryTheory.types_comp_apply] using hι
    calc
      (preservesColimitIso (forget CommRingCat.{max u v})
          (((Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π p.fiber).op).obj 𝒪.obj)).inv
        (colimit.ι ((((Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π p.fiber).op).obj
            𝒪.obj) ⋙ forget CommRingCat.{max u v}) (op ⟨X, x⟩) 1)
          = ((colimit.ι (((Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π p.fiber).op).obj
                𝒪.obj) (op ⟨X, x⟩)).hom) 1 := hι'
      _ = 1 := by
        simpa using ((colimit.ι (((Functor.whiskeringLeft _ _ _).obj
          (CategoryOfElements.π p.fiber).op).obj 𝒪.obj) (op ⟨X, x⟩)).hom.map_one)
  have h' := congrArg ((point_ring_carrier_iso (𝒪 := 𝒪) p).hom) h
  calc
    (point_ring_carrier_iso (𝒪 := 𝒪) p).hom
        (p.presheafFiber.map ((sheafToPresheaf J (Type (max u v))).map (oneSection 𝒪))
          (p.toPresheafFiber X x (Sheaf.terminal J Types.isTerminalPUnit).obj PUnit.unit))
        = (point_ring_carrier_iso (𝒪 := 𝒪) p).hom
            ((((sheafToPresheaf J (Type (max u v))).map (oneSection 𝒪)).app (op X) ≫
                p.toPresheafFiber X x
                  ((sheafToPresheaf J (Type (max u v))).obj
                    ((sheafCompose J (forget CommRingCat.{max u v})).obj 𝒪)))
              PUnit.unit) := by
            simpa [CategoryTheory.types_comp_apply] using h'
    _ = 1 := hs

/-- Helper for Lemma 18.40.3: the point fiber of the equalizer sheaf is inhabited exactly when
the stalk ring is subsingleton. -/
theorem point_fiber_zero_one_equalizer_nonempty_iff_subsingleton
    (p : GrothendieckTopology.Point.{max u v} J) :
    Nonempty (p.sheafFiber.obj (equalizer (zeroSection 𝒪) (oneSection 𝒪))) ↔
      Subsingleton (sourcePointRing 𝒪 p) := by
  -- Route correction: compute the target as a `Type` equalizer and read off the equality `0 = 1`.
  let eEq := PreservesEqualizer.iso p.sheafFiber (zeroSection 𝒪) (oneSection 𝒪)
  let t₀ := (point_terminal_iso (J := J) p).inv default
  constructor
  · rintro ⟨x⟩
    let y := (Types.equalizerIso (p.sheafFiber.map (zeroSection 𝒪))
      (p.sheafFiber.map (oneSection 𝒪))).hom (eEq.hom x)
    have h01 : (0 : sourcePointRing 𝒪 p) = 1 := by
      calc
        0 = (point_ring_carrier_iso (𝒪 := 𝒪) p).hom ((p.sheafFiber.map (zeroSection 𝒪)) y.1) := by
          simpa using (point_fiber_zeroSection_apply_eq_zero (𝒪 := 𝒪) p y.1).symm
        _ = (point_ring_carrier_iso (𝒪 := 𝒪) p).hom ((p.sheafFiber.map (oneSection 𝒪)) y.1) := by
          simpa using congrArg ((point_ring_carrier_iso (𝒪 := 𝒪) p).hom) y.2
        _ = 1 := by
          simpa using (point_fiber_oneSection_apply_eq_one (𝒪 := 𝒪) p y.1)
    exact (subsingleton_iff_zero_eq_one).1 h01
  · intro hSub
    have h01 : (0 : sourcePointRing 𝒪 p) = 1 :=
      (subsingleton_iff_zero_eq_one).2 hSub
    have hEq : (p.sheafFiber.map (zeroSection 𝒪)) t₀ = (p.sheafFiber.map (oneSection 𝒪)) t₀ := by
      apply (point_ring_carrier_iso (𝒪 := 𝒪) p).toEquiv.injective
      calc
        (point_ring_carrier_iso (𝒪 := 𝒪) p).hom ((p.sheafFiber.map (zeroSection 𝒪)) t₀) = 0 := by
          simpa using point_fiber_zeroSection_apply_eq_zero (𝒪 := 𝒪) p t₀
        _ = 1 := h01
        _ = (point_ring_carrier_iso (𝒪 := 𝒪) p).hom ((p.sheafFiber.map (oneSection 𝒪)) t₀) := by
          simpa using (point_fiber_oneSection_apply_eq_one (𝒪 := 𝒪) p t₀).symm
    exact ⟨eEq.inv ((Types.equalizerIso (p.sheafFiber.map (zeroSection 𝒪))
      (p.sheafFiber.map (oneSection 𝒪))).inv ⟨t₀, hEq⟩)⟩

/-- Helper for Lemma 18.40.3: after taking the stalk at a point, the canonical map from
`18.40.2.1` is an isomorphism exactly when the stalk ring is nontrivial. -/
theorem point_fiber_oneNeverZeroEqualizerMap_isIso_iff_nontrivial (p : J.Point) :
    IsIso (p.sheafFiber.map (oneNeverZeroEqualizerMap 𝒪)) ↔
      Nontrivial (sourcePointRing 𝒪 p) := by
  -- Compute the source as empty and the target as empty exactly when the stalk ring is nontrivial.
  have hSourceEmpty := point_fiber_empty_sheafification_isEmpty (J := J) p
  rw [isIso_iff_bijective]
  constructor
  · intro hBij
    have hTargetEmpty : IsEmpty (p.sheafFiber.obj (equalizer (zeroSection 𝒪) (oneSection 𝒪))) := by
      refine ⟨fun y ↦ ?_⟩
      obtain ⟨x, rfl⟩ := hBij.2 y
      exact hSourceEmpty.false x
    have hNotSub : ¬ Subsingleton (sourcePointRing 𝒪 p) := by
      intro hSub
      obtain ⟨y⟩ := (point_fiber_zero_one_equalizer_nonempty_iff_subsingleton (𝒪 := 𝒪) p).2 hSub
      exact hTargetEmpty.false y
    exact (not_subsingleton_iff_nontrivial).1 hNotSub
  · intro hNontrivial
    have hTargetEmpty : IsEmpty (p.sheafFiber.obj (equalizer (zeroSection 𝒪) (oneSection 𝒪))) := by
      refine ⟨fun y ↦ ?_⟩
      have hSub : Subsingleton (sourcePointRing 𝒪 p) :=
        (point_fiber_zero_one_equalizer_nonempty_iff_subsingleton (𝒪 := 𝒪) p).1 ⟨y⟩
      exact (not_subsingleton_iff_nontrivial.2 hNontrivial) hSub
    refine ⟨?_, ?_⟩
    · intro x x' _
      exact (hSourceEmpty.false x).elim
    · intro y
      exact (hTargetEmpty.false y).elim

/-- Lemma 18.40.3, forward direction: if the canonical morphism
`\emptyset^\# \to \operatorname{Equalizer}(0,1 : * \to \mathcal O)` from `18.40.2.1` is an
isomorphism, then every point stalk `\mathcal O_p` is nonzero. -/
theorem stalkwise_nontrivial_of_isIso_oneNeverZeroEqualizerMap
    (h : IsIso (oneNeverZeroEqualizerMap 𝒪)) (p : J.Point) :
    Nontrivial (sourcePointRing 𝒪 p) := by
  -- Apply the stalk functor and use the pointwise criterion proved above.
  have hPoint : IsIso (p.sheafFiber.map (oneNeverZeroEqualizerMap 𝒪)) :=
    Functor.map_isIso p.sheafFiber (oneNeverZeroEqualizerMap 𝒪)
  exact (point_fiber_oneNeverZeroEqualizerMap_isIso_iff_nontrivial (𝒪 := 𝒪) p).1 hPoint

/-- Lemma 18.40.3: if `(\mathcal C, J)` has enough points, then the canonical morphism
`\emptyset^\# \to \operatorname{Equalizer}(0,1 : * \to \mathcal O)` from `18.40.2.1` is an
isomorphism exactly when every point stalk `\mathcal O_p` is nonzero. -/
theorem isIso_oneNeverZeroEqualizerMap_iff_stalkwise_nontrivial
    [GrothendieckTopology.HasEnoughPoints.{max u v} J]
    :
    IsIso (oneNeverZeroEqualizerMap 𝒪) ↔
      ∀ p : J.Point,
        Nontrivial (sourcePointRing 𝒪 p) := by
  constructor
  · intro hIso p
    exact stalkwise_nontrivial_of_isIso_oneNeverZeroEqualizerMap (𝒪 := 𝒪) hIso p
  · intro hStalk
    -- Under enough points, it is enough to check the displayed map on a conservative family of
    -- point stalks.
    obtain ⟨P, -, hP⟩ := GrothendieckTopology.HasEnoughPoints.exists_objectProperty J
    refine (hP.jointlyReflectIsomorphisms_type.isIso_iff (oneNeverZeroEqualizerMap 𝒪)).2 ?_
    intro Φ
    exact (point_fiber_oneNeverZeroEqualizerMap_isIso_iff_nontrivial
      (𝒪 := 𝒪) Φ.obj).2 (hStalk Φ.obj)

end CategoryTheory
