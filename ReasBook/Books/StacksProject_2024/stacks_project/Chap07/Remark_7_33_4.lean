import Mathlib
import StacksProject_2024.Chap07.«7_32_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

open Limits
open GrothendieckTopology

variable {C : Type u} [Category.{v} C]
variable [HasTerminal C] [HasPullbacks C]

/-
Domain-style sampling for Remark 7.33.4:
- primary domain: points of sites and their underlying set-valued fiber functors;
- sampled owner API:
  `GrothendieckTopology.Point`,
  `GrothendieckTopology.Point.jointly_surjective`,
  `Functor.isCofiltered_elements`,
  `pullbackComparison`;
- source/core/bridge triage:
  `source-facing`: `TextbookPointAxioms`;
  `core/canonical`: `GrothendieckTopology.Point`;
  `bridge/view`: `textbookPointAxioms_of_point`.

Primitive data for the source-facing remark are exactly the three textbook clauses. The chapter’s
owner notion is `GrothendieckTopology.Point`; cofilteredness of `u.Elements` and the covering
surjectivity clause are owner-level data from which the terminal/pullback clauses are derived.
-/
/-- The three hypotheses appearing in Remark 7.33.4 for a set-valued functor on a site: the
terminal object is sent to a singleton, pullback-comparison maps are surjective, and covering
sieves act jointly surjectively on fibers. -/
def TextbookPointAxioms (J : GrothendieckTopology C) (u : C ⥤ Type w) : Prop :=
  (Subsingleton (u.obj (⊤_ C)) ∧ Nonempty (u.obj (⊤_ C))) ∧
    (∀ {U V W : C} (f : U ⟶ W) (g : V ⟶ W),
      Function.Surjective (pullbackComparison u f g)) ∧
    ∀ {U : C} (R : Sieve U) (_ : R ∈ J U) (x : u.obj U),
      ∃ (Y : C) (f : Y ⟶ U) (_ : R f) (y : u.obj Y), u.map f y = x

@[implicit_reducible] private noncomputable def unique_terminalFiberObj_of_isCofiltered
    (u : C ⥤ Type w) [IsCofiltered u.Elements] :
    Unique (u.obj (⊤_ C)) := by
  classical
  let x₀ : u.obj (⊤_ C) := by
    let z : u.Elements := Classical.choice (IsCofiltered.nonempty : Nonempty u.Elements)
    exact u.map (terminal.from z.1) z.2
  refine
    { default := x₀
      uniq := ?_ }
  intro x
  let z := IsCofiltered.min (u.elementsMk (⊤_ C) x₀) (u.elementsMk (⊤_ C) x)
  let q₁ : z ⟶ u.elementsMk (⊤_ C) x₀ := IsCofiltered.minToLeft _ _
  let q₂ : z ⟶ u.elementsMk (⊤_ C) x := IsCofiltered.minToRight _ _
  have hq : q₁.1 = q₂.1 := Subsingleton.elim _ _
  calc
    x = u.map q₂.1 z.2 := q₂.2.symm
    _ = u.map q₁.1 z.2 := by simp [hq]
    _ = x₀ := q₁.2

omit [HasTerminal C] in
private theorem pullbackComparison_surjective_of_isCofiltered
    (u : C ⥤ Type w) [IsCofiltered u.Elements] :
    ∀ {U V W : C} (f : U ⟶ W) (g : V ⟶ W),
      Function.Surjective (pullbackComparison u f g) := by
  intro U V W f g x
  refine Function.Surjective.of_comp_left (fun x ↦ ?_)
    (injective_of_mono (Types.pullbackIsoPullback (u.map f) (u.map g)).hom) x
  let α₁ : u.elementsMk U x.1.1 ⟶ u.elementsMk W (u.map f x.1.1) := ⟨f, rfl⟩
  let α₂ : u.elementsMk V x.1.2 ⟶ u.elementsMk W (u.map f x.1.1) := ⟨g, x.2.symm⟩
  obtain ⟨z, q₁, q₂, fac⟩ := IsCofiltered.cospan α₁ α₂
  rw [Subtype.ext_iff] at fac
  refine ⟨u.map (pullback.lift q₁.1 q₂.1 fac) z.2, ?_⟩
  ext
  · simp only [Function.comp_apply, Types.pullbackIsoPullback_hom_fst]
    have hfst := congr_fun
      (pullbackComparison_comp_fst u f g) (u.map (pullback.lift q₁.1 q₂.1 fac) z.2)
    change (pullbackComparison u f g ≫ pullback.fst (u.map f) (u.map g))
        (u.map (pullback.lift q₁.1 q₂.1 fac) z.2) = x.1.1
    refine hfst.trans ?_
    calc
      u.map (pullback.fst f g) (u.map (pullback.lift q₁.1 q₂.1 fac) z.2) =
          u.map (pullback.lift q₁.1 q₂.1 fac ≫ pullback.fst f g) z.2 := by
            rw [← FunctorToTypes.map_comp_apply]
      _ = u.map q₁.1 z.2 := by rw [pullback.lift_fst]
      _ = x.1.1 := q₁.2
  · simp only [Function.comp_apply, Types.pullbackIsoPullback_hom_snd]
    have hsnd := congr_fun
      (pullbackComparison_comp_snd u f g) (u.map (pullback.lift q₁.1 q₂.1 fac) z.2)
    change (pullbackComparison u f g ≫ pullback.snd (u.map f) (u.map g))
        (u.map (pullback.lift q₁.1 q₂.1 fac) z.2) = x.1.2
    refine hsnd.trans ?_
    calc
      u.map (pullback.snd f g) (u.map (pullback.lift q₁.1 q₂.1 fac) z.2) =
          u.map (pullback.lift q₁.1 q₂.1 fac ≫ pullback.snd f g) z.2 := by
            rw [← FunctorToTypes.map_comp_apply]
      _ = u.map q₂.1 z.2 := by rw [pullback.lift_snd]
      _ = x.1.2 := q₂.2
-- Proof sketch: the core owner theorem is that `p : J.Point` carries a fiber functor preserving
-- finite limits, while `p.jointly_surjective` is exactly the covering-surjectivity clause. The
-- three textbook axioms are therefore a source-facing bridge from the canonical point API.
/-- Any point of a site satisfies the three hypotheses appearing in Remark 7.33.4 on its
underlying fiber functor. -/
theorem textbookPointAxioms_of_point
    (J : GrothendieckTopology C)
    (p : J.Point) :
    TextbookPointAxioms J p.fiber := by
  letI := unique_terminalFiberObj_of_isCofiltered p.fiber
  refine ⟨⟨inferInstance, inferInstance⟩, pullbackComparison_surjective_of_isCofiltered p.fiber,
    ?_⟩
  intro U R hR x
  rcases p.jointly_surjective R hR x with ⟨Y, f, hf, y, hy⟩
  exact ⟨Y, f, hf, y, hy⟩

/-- The explicit two-object counterexample fiber functor from Remark 7.33.4, realized on the
preorder category `Bool` with `false ⟶ true`. The terminal object `true` is sent to a singleton
and `false` is sent to a two-point set. -/
noncomputable def textbookPointCounterexampleFiber : Bool ⥤ Type where
  obj
    | true => PUnit
    | false => Fin 2
  map {X Y} f := by
    cases X <;> cases Y
    · exact id
    · exact fun _ ↦ PUnit.unit
    · intro x
      have h : true = false := le_antisymm f.down.down (by decide)
      cases h
    · exact id
  map_id := by
    intro X
    sorry
  map_comp := by
    intro X Y Z f g
    sorry

/-- The presheaf on the two-object category `Bool` classified by a map `i : A → B`: it has value
`A` on `true`, value `B` on `false`, and its unique nonidentity restriction map is `i`. -/
noncomputable def twoObjectArrowPresheaf (A B : Type) (i : A ⟶ B) : Boolᵒᵖ ⥤ Type where
  obj X := Bool.rec B A X.unop
  map {X Y} f := by
    cases hX : X.unop <;> cases hY : Y.unop
    · simpa [hX, hY] using (id : B → B)
    · exfalso
      have hf : PLift (true ≤ false) := by
        simpa [hX, hY] using f.unop.down
      have h : true = false := le_antisymm hf.down (by decide)
      exact Bool.noConfusion h
    · simpa [hX, hY] using i
    · simpa [hX, hY] using (id : A → A)
  map_id := by
    intro X
    sorry
  map_comp := by
    intro X Y Z f g
    sorry

/-- A morphism between two arrow-presheaves on `Bool` is a commutative square between their
underlying maps. -/
noncomputable def twoObjectArrowPresheafHom
    {A B A' B' : Type} {i : A ⟶ B} {i' : A' ⟶ B'}
    (fA : A ⟶ A') (fB : B ⟶ B') (comm : i ≫ fB = fA ≫ i') :
    twoObjectArrowPresheaf A B i ⟶ twoObjectArrowPresheaf A' B' i' where
  app X := by
    cases hX : X.unop
    · simpa [twoObjectArrowPresheaf, hX] using fB
    · simpa [twoObjectArrowPresheaf, hX] using fA
  naturality := by
    intro X Y f
    sorry

/-- For the trivial Grothendieck topology on `Bool`, every presheaf is already a sheaf, so the
pair `(A, B, i)` defines a sheaf of sets. -/
noncomputable def twoObjectArrowSheaf (A B : Type) (i : A ⟶ B) :
    Sheaf (⊥ : GrothendieckTopology Bool) Type :=
  ⟨twoObjectArrowPresheaf A B i, Presheaf.isSheaf_bot _⟩

/-- The stalk functor attached to `textbookPointCounterexampleFiber`. Since the topology on `Bool`
is trivial, this is the restriction of the raw presheaf fiber functor. -/
noncomputable abbrev textbookPointCounterexampleStalkFunctor :
    Sheaf (⊥ : GrothendieckTopology Bool) Type ⥤ Type :=
  sheafToPresheaf (⊥ : GrothendieckTopology Bool) Type ⋙
    textbookPointCounterexampleFiber.presheafFiber

/-- For the counterexample fiber functor, the associated stalk functor sends an arrow
`i : A → B` to the pushout `B ⨿_A B`. -/
noncomputable def textbookPointCounterexampleStalkFunctorObjIso
    (A B : Type) (i : A ⟶ B) :
    textbookPointCounterexampleStalkFunctor.obj (twoObjectArrowSheaf A B i) ≅ pushout i i :=
  let F : Boolᵒᵖ ⥤ Type := (twoObjectArrowSheaf A B i).1
  let f : false ⟶ true := homOfLE (by decide)
  let x0 : textbookPointCounterexampleFiber.obj false :=
    show textbookPointCounterexampleFiber.obj false from (0 : Fin 2)
  let x1 : textbookPointCounterexampleFiber.obj false :=
    show textbookPointCounterexampleFiber.obj false from (1 : Fin 2)
  let xStar : textbookPointCounterexampleFiber.obj true :=
    show textbookPointCounterexampleFiber.obj true from PUnit.unit
  let φ : ∀ X, textbookPointCounterexampleFiber.obj X → (F.obj (Opposite.op X) ⟶ pushout i i) :=
    fun
    | false, x => Fin.cases (pushout.inl i i) (fun _ ↦ pushout.inr i i) x
    | true, _ => i ≫ pushout.inl i i
  let hφ :
      ∀ ⦃X Y : Bool⦄ (g : X ⟶ Y) (x : textbookPointCounterexampleFiber.obj X),
        F.map g.op ≫ φ X x = φ Y (textbookPointCounterexampleFiber.map g x) := by
    intro X Y g x
    cases X <;> cases Y
    · have hg : g = 𝟙 false := Subsingleton.elim _ _
      subst hg
      change Fin 2 at x
      fin_cases x <;> rfl
    · have hg : g = f := Subsingleton.elim _ _
      subst hg
      change Fin 2 at x
      fin_cases x
      · rfl
      · simpa [φ, F, f, xStar, twoObjectArrowSheaf, twoObjectArrowPresheaf] using
          (show i ≫ pushout.inr i i = i ≫ pushout.inl i i from pushout.condition.symm)
    · exfalso
      have h : true = false := le_antisymm g.down.down (by decide)
      exact Bool.noConfusion h
    · have hg : g = 𝟙 true := Subsingleton.elim _ _
      subst hg
      rfl
  let toPushout :
      textbookPointCounterexampleStalkFunctor.obj (twoObjectArrowSheaf A B i) ⟶ pushout i i :=
    textbookPointCounterexampleFiber.presheafFiberDesc φ hφ
  let hx0 :
      i ≫ textbookPointCounterexampleFiber.toPresheafFiber false x0 F =
        textbookPointCounterexampleFiber.toPresheafFiber true xStar F := by
    simpa [F, f, x0, xStar, twoObjectArrowSheaf, twoObjectArrowPresheaf] using
      (textbookPointCounterexampleFiber.toPresheafFiber_w f x0)
  let hx1 :
      i ≫ textbookPointCounterexampleFiber.toPresheafFiber false x1 F =
        textbookPointCounterexampleFiber.toPresheafFiber true xStar F := by
    simpa [F, f, x1, xStar, twoObjectArrowSheaf, twoObjectArrowPresheaf] using
      (textbookPointCounterexampleFiber.toPresheafFiber_w f x1)
  let hfrom :
      i ≫ textbookPointCounterexampleFiber.toPresheafFiber false x0 F =
        i ≫ textbookPointCounterexampleFiber.toPresheafFiber false x1 F :=
    hx0.trans hx1.symm
  let fromPushout :
      pushout i i ⟶ textbookPointCounterexampleStalkFunctor.obj (twoObjectArrowSheaf A B i) :=
    pushout.desc
      (textbookPointCounterexampleFiber.toPresheafFiber false x0 F)
      (textbookPointCounterexampleFiber.toPresheafFiber false x1 F)
      hfrom
  let hto0 :
      textbookPointCounterexampleFiber.toPresheafFiber false x0 F ≫ toPushout = pushout.inl i i := by
    simpa [toPushout, φ, x0] using
      (textbookPointCounterexampleFiber.toPresheafFiber_presheafFiberDesc φ hφ false x0)
  let hto1 :
      textbookPointCounterexampleFiber.toPresheafFiber false x1 F ≫ toPushout = pushout.inr i i := by
    simpa [toPushout, φ, x1] using
      (textbookPointCounterexampleFiber.toPresheafFiber_presheafFiberDesc φ hφ false x1)
  let htoStar :
      textbookPointCounterexampleFiber.toPresheafFiber true xStar F ≫ toPushout =
        i ≫ pushout.inl i i := by
    simpa [toPushout, φ, xStar] using
      (textbookPointCounterexampleFiber.toPresheafFiber_presheafFiberDesc φ hφ true xStar)
  { hom := toPushout
    inv := fromPushout
    hom_inv_id := by
      apply textbookPointCounterexampleFiber.presheafFiber_hom_ext
      intro X x
      cases X
      · change Fin 2 at x
        fin_cases x
        · refine (by
            have hA :
                textbookPointCounterexampleFiber.toPresheafFiber false x0 F ≫ toPushout ≫ fromPushout =
                  pushout.inl i i ≫ fromPushout := by
              simpa [Category.assoc] using congrArg (fun k ↦ k ≫ fromPushout) hto0
            have hB :
                pushout.inl i i ≫ fromPushout =
                  textbookPointCounterexampleFiber.toPresheafFiber false x0 F := by
              simpa [fromPushout] using
                (pushout.inl_desc
                  (textbookPointCounterexampleFiber.toPresheafFiber false x0 F)
                  (textbookPointCounterexampleFiber.toPresheafFiber false x1 F) hfrom)
            exact hA.trans hB)
        · refine (by
            have hA :
                textbookPointCounterexampleFiber.toPresheafFiber false x1 F ≫ toPushout ≫ fromPushout =
                  pushout.inr i i ≫ fromPushout := by
              simpa [Category.assoc] using congrArg (fun k ↦ k ≫ fromPushout) hto1
            have hB :
                pushout.inr i i ≫ fromPushout =
                  textbookPointCounterexampleFiber.toPresheafFiber false x1 F := by
              simpa [fromPushout] using
                (pushout.inr_desc
                  (textbookPointCounterexampleFiber.toPresheafFiber false x0 F)
                  (textbookPointCounterexampleFiber.toPresheafFiber false x1 F) hfrom)
            exact hA.trans hB)
      · cases x
        refine (by
          have hA :
              textbookPointCounterexampleFiber.toPresheafFiber true xStar F ≫ toPushout ≫ fromPushout =
                (i ≫ pushout.inl i i) ≫ fromPushout := by
            simpa [Category.assoc] using congrArg (fun k ↦ k ≫ fromPushout) htoStar
          have hB :
              (i ≫ pushout.inl i i) ≫ fromPushout =
                i ≫ textbookPointCounterexampleFiber.toPresheafFiber false x0 F := by
            simpa [Category.assoc, fromPushout] using
              congrArg (fun k ↦ i ≫ k)
                (pushout.inl_desc
                  (textbookPointCounterexampleFiber.toPresheafFiber false x0 F)
                  (textbookPointCounterexampleFiber.toPresheafFiber false x1 F) hfrom)
          exact hA.trans (hB.trans hx0))
    inv_hom_id := by
      refine pushout.hom_ext ?_ ?_
      · have hA :
            pushout.inl i i ≫ fromPushout ≫ toPushout =
              textbookPointCounterexampleFiber.toPresheafFiber false x0 F ≫ toPushout := by
          simpa [Category.assoc, fromPushout] using
            congrArg (fun k ↦ k ≫ toPushout)
              (pushout.inl_desc
                (textbookPointCounterexampleFiber.toPresheafFiber false x0 F)
                (textbookPointCounterexampleFiber.toPresheafFiber false x1 F) hfrom)
        simpa using hA.trans hto0
      · have hA :
            pushout.inr i i ≫ fromPushout ≫ toPushout =
              textbookPointCounterexampleFiber.toPresheafFiber false x1 F ≫ toPushout := by
          simpa [Category.assoc, fromPushout] using
            congrArg (fun k ↦ k ≫ toPushout)
              (pushout.inr_desc
                (textbookPointCounterexampleFiber.toPresheafFiber false x0 F)
                (textbookPointCounterexampleFiber.toPresheafFiber false x1 F) hfrom)
        simpa using hA.trans hto1 }

/-- The source object used in Remark 7.33.4: the arrow `∅ → *`, whose image under the
counterexample stalk functor is a two-point set. -/
noncomputable def textbookPointCounterexampleSourceSheaf :
    Sheaf (⊥ : GrothendieckTopology Bool) Type :=
  twoObjectArrowSheaf (Fin 0) (Fin 1) Fin.elim0

/-- The target object used in Remark 7.33.4: the identity arrow `* → *`, whose image under the
counterexample stalk functor is a singleton. -/
noncomputable def textbookPointCounterexampleTargetSheaf :
    Sheaf (⊥ : GrothendieckTopology Bool) Type :=
  twoObjectArrowSheaf (Fin 1) (Fin 1) (𝟙 _)

/-- The explicit injective morphism of sheaves used in Remark 7.33.4, corresponding to the
commutative square `∅ → *` over `* = *`. -/
noncomputable def textbookPointCounterexampleMono :
    textbookPointCounterexampleSourceSheaf ⟶ textbookPointCounterexampleTargetSheaf :=
  ⟨twoObjectArrowPresheafHom Fin.elim0 (𝟙 _) (by
      ext x
      exact Fin.elim0 x)⟩

/-- The morphism `textbookPointCounterexampleMono` is a monomorphism of sheaves. -/
theorem textbookPointCounterexampleMono_mono :
    Mono textbookPointCounterexampleMono := by
  sorry

/-- Under the counterexample stalk functor, the mono `textbookPointCounterexampleMono` becomes a
noninjective map `Fin 2 → Fin 1`. Hence this stalk functor is not left exact. -/
theorem textbookPointCounterexampleStalkFunctor_map_not_injective :
    ¬ Function.Injective
      (textbookPointCounterexampleStalkFunctor.map textbookPointCounterexampleMono) := by
  sorry

-- Proof sketch: evaluate the three clauses of `TextbookPointAxioms` directly on the explicit
-- two-object counterexample functor. The terminal fiber is `PUnit`, pullback-comparison maps are
-- checked case-by-case on `Bool`, and the trivial topology makes the covering clause vacuous.
/-- The explicit counterexample fiber functor satisfies the three textbook point axioms. -/
theorem textbookPointCounterexampleFiber_textbookPointAxioms :
    TextbookPointAxioms (⊥ : GrothendieckTopology Bool) textbookPointCounterexampleFiber := sorry

-- Proof sketch: use the explicit two-object site from the remark, with trivial topology,
-- terminal object `true`, and the fiber functor `textbookPointCounterexampleFiber`. Its
-- associated stalk functor on sheaves is `(A, B, A → B) ↦ B ⨿_A B`, which fails to preserve
-- monomorphisms, whereas any genuine point gives a left exact sheaf fiber functor.
/-- Remark 7.33.4: on the trivial Grothendieck topology of the two-object site `Bool`, the
functor `textbookPointCounterexampleFiber` satisfies the textbook axioms but is not the fiber
functor of any point. Concretely, its associated stalk functor sends `(A, B, i : A → B)` to the
pushout `B ⨿_A B` and takes the mono `textbookPointCounterexampleMono` to a noninjective map. -/
theorem textbookPointAxioms_do_not_imply_point :
    ¬ ∃ p : (⊥ : GrothendieckTopology Bool).Point, p.fiber = textbookPointCounterexampleFiber :=
  sorry

end CategoryTheory
