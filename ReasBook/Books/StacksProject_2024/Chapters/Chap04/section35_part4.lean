import Mathlib
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.Groupoid
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_4_35_10 (from Chap04) -/
open CategoryTheory
open CategoryTheory.Limits
open scoped CategoricalPullback

universe v u

namespace CategoryTheory

/-- Helper for Lemma 4.35.10: the canonical diagonal functor into the categorical self-pullback
of a functor. -/
private abbrev categorical_pullback_diagonal_local
    {A : Type (max u v)} {B : Type (max u v)}
    [Category.{v} A] [Category.{v} B]
    (F : A ⥤ B) :
    A ⥤ F ⊡ F :=
  (CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
      (F := F) (G := F) (X := A)).obj
    { fst := 𝟭 A
      snd := 𝟭 A
      iso := Iso.refl _ }

local notation "Δₚ" => categorical_pullback_diagonal_local

/-- Helper for Lemma 4.35.10: a fully faithful functor into a groupoid is essentially surjective
onto the objects of its categorical self-pullback diagonal. -/
private theorem diagonal_essSurj_of_fullyFaithful
    {A : Type (max u v)} {B : Type (max u v)}
    [Category.{v} A] [Category.{v} B] [IsGroupoid B]
    (F : A ⥤ B) (hF : Nonempty F.FullyFaithful) :
    (Δₚ F).EssSurj := by
  rcases hF with ⟨hFF⟩
  refine ⟨?_⟩
  intro P
  -- A pullback object is determined by an isomorphism `F.obj P.fst ≅ F.obj P.snd`; pull it back
  -- across full faithfulness to obtain a diagonal source.
  refine ⟨P.fst, ⟨?_⟩⟩
  refine
    CategoricalPullback.mkIso
      (show ((Δₚ F).obj P.fst).fst ≅ P.fst from Iso.refl P.fst)
      (show ((Δₚ F).obj P.fst).snd ≅ P.snd from hFF.preimageIso P.iso)
      ?_
  simpa using (hFF.map_preimage P.iso.hom).symm

/- Internal categorical bridge: on fibers, the target category is a groupoid, so the diagonal
captures exactly the full-faithfulness data of the functor. -/
private theorem fullyFaithful_iff_diagonal_to_self_pullback_isEquivalence
    {A : Type (max u v)} {B : Type (max u v)}
    [Category.{v} A] [Category.{v} B]
    [IsGroupoid B]
    (F : A ⥤ B) :
    Nonempty F.FullyFaithful ↔
      (Δₚ F).IsEquivalence := by
  constructor
  · intro hF
    rcases hF with ⟨hFF⟩
    have hBij :
        ∀ X Y : A, Function.Bijective
          ((Δₚ F).map : (X ⟶ Y) → ((Δₚ F).obj X ⟶ (Δₚ F).obj Y)) := by
      intro X Y
      refine ⟨?_, ?_⟩
      · intro f g hfg
        simpa [categorical_pullback_diagonal_local] using
          congrArg CategoricalPullback.Hom.fst hfg
      · intro φ
        -- A morphism between diagonal objects is a pair with equal images under `F`, hence the
        -- two components coincide by faithfulness of `F`.
        have hsame :
            (show X ⟶ Y from φ.fst) = (show X ⟶ Y from φ.snd) := by
          apply hFF.map_injective
          simpa [categorical_pullback_diagonal_local] using φ.w
        refine ⟨show X ⟶ Y from φ.fst, ?_⟩
        apply CategoricalPullback.hom_ext
        · simp [categorical_pullback_diagonal_local]
        · simpa [categorical_pullback_diagonal_local] using hsame
    -- Combine hom-set bijectivity with the objectwise preimage argument above.
    exact
      (Functor.isEquivalence_iff_full_faithful_essSurj (Δₚ F)).2
        ⟨hBij, diagonal_essSurj_of_fullyFaithful F ⟨hFF⟩⟩
  · intro hΔ
    have hDiag :=
      (Functor.isEquivalence_iff_full_faithful_essSurj (Δₚ F)).1 hΔ
    have hBij := hDiag.1
    have hEss := hDiag.2
    -- Route correction: the converse direction is not a generic pullback theorem. We extract
    -- morphisms in `A` from the diagonal equivalence using fullness on diagonal homs and
    -- essential surjectivity on pullback objects.
    rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
    intro X Y
    refine ⟨?_, ?_⟩
    · intro β₁ β₂ hβ
      let φ : (Δₚ F).obj X ⟶ (Δₚ F).obj Y :=
        ⟨show ((Δₚ F).obj X).fst ⟶ ((Δₚ F).obj Y).fst from β₁,
          show ((Δₚ F).obj X).snd ⟶ ((Δₚ F).obj Y).snd from β₂,
          by
            change F.map β₁ ≫ 𝟙 (F.obj Y) = 𝟙 (F.obj X) ≫ F.map β₂
            simpa using hβ⟩
      obtain ⟨γ, hγ⟩ := (hBij X Y).2 φ
      have hγfst : γ = β₁ := by
        simpa [φ, categorical_pullback_diagonal_local] using
          congrArg CategoricalPullback.Hom.fst hγ
      have hγsnd : γ = β₂ := by
        simpa [φ, categorical_pullback_diagonal_local] using
          congrArg CategoricalPullback.Hom.snd hγ
      exact hγfst.symm.trans hγsnd
    · intro α
      let P : F ⊡ F :=
        { fst := X
          snd := Y
          iso := asIso α }
      obtain ⟨Z, ⟨e⟩⟩ := hEss.mem_essImage P
      -- The chosen diagonal preimage produces `X ← Z → Y`; compose these legs to obtain a
      -- morphism in `A` whose image is exactly `α`.
      refine
        ⟨show X ⟶ Y from
            (show X ⟶ Z from e.inv.fst) ≫ (show Z ⟶ Y from e.hom.snd),
          ?_⟩
      have hInv :
          F.map (show X ⟶ Z from e.inv.fst) =
            α ≫ F.map (show Y ⟶ Z from e.inv.snd) := by
        simpa [P, categorical_pullback_diagonal_local] using e.inv.w
      have hCancel :
          F.map (show Y ⟶ Z from e.inv.snd) ≫
              F.map (show Z ⟶ Y from e.hom.snd) =
            𝟙 (F.obj Y) := by
        have hsnd : e.inv.snd ≫ e.hom.snd = 𝟙 P.snd := by
          exact congrArg CategoricalPullback.Hom.snd e.inv_hom_id
        simpa [Functor.map_comp] using congrArg (fun f => F.map f) hsnd
      calc
        F.map
              ((show X ⟶ Z from e.inv.fst) ≫
                (show Z ⟶ Y from e.hom.snd))
            = F.map (show X ⟶ Z from e.inv.fst) ≫
                F.map (show Z ⟶ Y from e.hom.snd) := by simp
        _ = (α ≫ F.map (show Y ⟶ Z from e.inv.snd)) ≫
              F.map (show Z ⟶ Y from e.hom.snd) := by rw [hInv]
        _ = α ≫ F.map (show Y ⟶ Z from e.inv.snd) ≫
              F.map (show Z ⟶ Y from e.hom.snd) := by
            simpa using
              (Category.assoc α
                (F.map (show Y ⟶ Z from e.inv.snd))
                (F.map (show Z ⟶ Y from e.hom.snd)))
        _ = α := by
          simpa [Category.assoc] using congrArg (fun f => α ≫ f) hCancel

section

variable {C : Type (max u v)} {S : Type (max u v)} {S' : Type (max u v)}
  [Category.{v} C] [Category.{v} S] [Category.{v} S']
variable {p : S ⥤ C} {p' : S' ⥤ C} [IsFibredInGroupoids p] [IsFibredInGroupoids p']
variable (F : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p')

local instance : IsFibredInGroupoids (BasedCategory.ofFunctor p).p := by
  simpa using (inferInstance : IsFibredInGroupoids p)

local instance : IsFibredInGroupoids (BasedCategory.ofFunctor p').p := by
  simpa using (inferInstance : IsFibredInGroupoids p')

/- Domain-style sampling for the auxiliary bridge layer of Lemma 4.35.10:
- primary domain: based functors between categories fibred in groupoids over a fixed base and the
  canonical diagonal functor over that base;
- sampled owner-level declarations:
  `FibredInGroupoidsMor`,
  `FibredInGroupoidsOver.twoFibreProduct`,
  `FibredInGroupoidsMor.diagonalMor`,
  `relativeDiagonalOver`,
  `FibredInGroupoidsMor.fullyFaithful_iff_fiberwise`;
- best owner abstraction for the final source-facing statement: `FibredInGroupoidsMor`; the raw
  `BasedFunctor` theorem here is the bridge/view used to prove that owner-level statement;
- primitive data at this bridge layer: only the based functor `F`;
- derived API: the diagonal equivalence-over-base criterion and its fiberwise restatement.

Source/core/bridge triage:
- `source-facing`: the bundled `FibredInGroupoidsMor` theorem stated below;
- `core/canonical`: `Nonempty F.FullyFaithful`,
  `F.relativeDiagonalOver.IsEquivalenceOverBase`;
- `bridge/view`: the comparison between the raw diagonal-over-base criterion and the diagonal of
  each fiber functor. -/

-- Proof sketch: apply Lemma `4.35.9` to the diagonal based functor over `C`, so the global
-- diagonal equivalence criterion reduces to equivalence on each fiber. On the fiber over `U`, the
-- owner-level relative diagonal `BasedFunctor.relativeDiagonalOver F` specializes to the
-- explicit self-`2`-fibre-product model from Lemma `4.35.7`. On each fiber over `U`, its induced
-- functor is the canonical diagonal `Δₚ (F.fiberFunctor U)`.
/-- Helper for Lemma 4.35.10: on a diagonal fiber object, the comparison isomorphism coming from
`fibreOfPullback_equiv_pullbackOfFibres` has identity underlying morphism. -/
private theorem relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_app_iso_hom
    (x : S) :
    Functor.Fiber.fiberInclusion.map
      (((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F (p.obj x)).functor.obj
          ((F.relativeDiagonalOver.fiberFunctor (p.obj x)).obj (Functor.Fiber.mk rfl))).iso.hom) =
        𝟙 (F.obj x) := by
  -- The diagonal object is sent to the same fibre isomorphism, so the comparison is literally
  -- the identity map in the ambient category.
  rfl

/-- Helper for Lemma 4.35.10: objectwise, the fiber of the owner-level relative diagonal matches
the canonical diagonal object in the categorical pullback of fibres. -/
private noncomputable abbrev relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_app_iso
    (U : C) (x : p.Fiber U) :
    ((((F.relativeDiagonalOver).fiberFunctor U) ⋙
          (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F U).functor).obj x) ≅
      ((Δₚ (F.fiberFunctor U)).obj x) := by
  -- Route correction: compare the two pullback objects by their projections instead of forcing a
  -- strict equality of functors through transport terms.
  cases x with
  | mk x hx =>
      cases hx
      refine CategoricalPullback.mkIso ?_ ?_ ?_
      · exact Iso.refl (Functor.Fiber.mk rfl)
      · exact Iso.refl (Functor.Fiber.mk rfl)
      -- The comparison iso in the explicit pullback model is the identity after forgetting back
      -- to the ambient fibre, so extensionality in the fibre closes the pullback compatibility.
      apply Functor.Fiber.hom_ext
      -- Both identity legs forget to `F.map (𝟙 x)`, while the diagonal structural map forgets to
      -- `𝟙 (F.obj x)`, so the compatibility reduces to the previously normalized comparison map.
      simp only [Functor.map_comp]
      have hleft :
          F.map
              (Functor.Fiber.fiberInclusion.map
                (𝟙 (Functor.Fiber.mk rfl : p.Fiber (p.obj x)))) =
            F.map (𝟙 x) := by
        rfl
      have hright :
          Functor.Fiber.fiberInclusion.map
              (((Δₚ (F.fiberFunctor (p.obj x))).obj (Functor.Fiber.mk rfl)).iso.hom) =
            𝟙 (F.obj x) := by
        rfl
      have hleft' :
          Functor.Fiber.fiberInclusion.map
              ((F.fiberFunctor (p.obj x)).map (Iso.refl (Functor.Fiber.mk rfl)).hom) =
            F.map (𝟙 x) := by
        rfl
      have h₁ :
          Functor.Fiber.fiberInclusion.map
              ((F.fiberFunctor (p.obj x)).map (Iso.refl (Functor.Fiber.mk rfl)).hom) ≫
            Functor.Fiber.fiberInclusion.map
              (((Δₚ (F.fiberFunctor (p.obj x))).obj (Functor.Fiber.mk rfl)).iso.hom) =
          F.map (𝟙 x) := by
        have h₁a :
            Functor.Fiber.fiberInclusion.map
                ((F.fiberFunctor (p.obj x)).map (Iso.refl (Functor.Fiber.mk rfl)).hom) ≫
              Functor.Fiber.fiberInclusion.map
                (((Δₚ (F.fiberFunctor (p.obj x))).obj (Functor.Fiber.mk rfl)).iso.hom) =
              F.map (𝟙 x) ≫
                Functor.Fiber.fiberInclusion.map
                  (((Δₚ (F.fiberFunctor (p.obj x))).obj (Functor.Fiber.mk rfl)).iso.hom) := by
          rw [hleft']
          rfl
        have h₁b :
            F.map (𝟙 x) ≫
                Functor.Fiber.fiberInclusion.map
                  (((Δₚ (F.fiberFunctor (p.obj x))).obj (Functor.Fiber.mk rfl)).iso.hom) =
              F.map (𝟙 x) := by
          simpa [hright]
        exact h₁a.trans h₁b
      have h₂ : F.map (𝟙 x) = 𝟙 (F.obj x) ≫ F.map (𝟙 x) := by
        simp
      have h₃ :
          𝟙 (F.obj x) ≫ F.map (𝟙 x) =
            Functor.Fiber.fiberInclusion.map
                (((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F (p.obj x)).functor.obj
                    ((F.relativeDiagonalOver.fiberFunctor (p.obj x)).obj
                      (Functor.Fiber.mk rfl))).iso.hom) ≫
              F.map (𝟙 x) := by
        rw [relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_app_iso_hom
          (F := F) x]
        rfl
      have h₄ :
          Functor.Fiber.fiberInclusion.map
              (((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F (p.obj x)).functor.obj
                  ((F.relativeDiagonalOver.fiberFunctor (p.obj x)).obj
                    (Functor.Fiber.mk rfl))).iso.hom) ≫
            F.map (𝟙 x) =
              Functor.Fiber.fiberInclusion.map
                (((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F (p.obj x)).functor.obj
                    ((F.relativeDiagonalOver.fiberFunctor (p.obj x)).obj
                      (Functor.Fiber.mk rfl))).iso.hom) ≫
                F.map
                  (Functor.Fiber.fiberInclusion.map
                    (𝟙 (Functor.Fiber.mk rfl : p.Fiber (p.obj x)))) := by
        simpa using
          congrArg
            (fun k =>
              Functor.Fiber.fiberInclusion.map
                  (((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F (p.obj x)).functor.obj
                      ((F.relativeDiagonalOver.fiberFunctor (p.obj x)).obj
                        (Functor.Fiber.mk rfl))).iso.hom) ≫
                k)
            hleft.symm
      exact h₁.trans (h₂.trans (h₃.trans h₄))

/-- Helper for Lemma 4.35.10: after passing to the explicit self-pullback model, the left
projection of the relative diagonal fiber is definitionally the identity fiber functor. -/
private theorem relativeDiagonalOver_fiberFunctor_comp_leftProjection
    (U : C) :
    ((F.relativeDiagonalOver).fiberFunctor U) ⋙
        (CategoryOver.explicitTwoFibreProductLeftProjection F F).fiberFunctor U =
      𝟭 (p.Fiber U) := by
  rfl

/-- Helper for Lemma 4.35.10: after passing to the explicit self-pullback model, the right
projection of the relative diagonal fiber is definitionally the identity fiber functor. -/
private theorem relativeDiagonalOver_fiberFunctor_comp_rightProjection
    (U : C) :
    ((F.relativeDiagonalOver).fiberFunctor U) ⋙
        (CategoryOver.explicitTwoFibreProductRightProjection F F).fiberFunctor U =
      𝟭 (p.Fiber U) := by
  rfl

/-- Helper for Lemma 4.35.10: the left projection of the transported owner-level diagonal fiber
is the identity functor on the source fiber. -/
private theorem relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_comp_pi₁
    (U : C) :
    ((F.relativeDiagonalOver).fiberFunctor U) ⋙
        (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F U).functor ⋙
        CategoricalPullback.π₁ (F.fiberFunctor U) (F.fiberFunctor U) =
      𝟭 (p.Fiber U) := by
  -- Compose the packaged pullback equivalence with its left projection formula, then observe
  -- that the relative diagonal remembers the left fibre coordinate definitionally.
  calc
    ((F.relativeDiagonalOver).fiberFunctor U) ⋙
        (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F U).functor ⋙
        CategoricalPullback.π₁ (F.fiberFunctor U) (F.fiberFunctor U)
        =
          ((F.relativeDiagonalOver).fiberFunctor U) ⋙
            (CategoryOver.explicitTwoFibreProductLeftProjection F F).fiberFunctor U := by
              simpa [Functor.assoc] using
                congrArg
                  (fun H =>
                    ((F.relativeDiagonalOver).fiberFunctor U) ⋙ H)
                  (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres_functor_comp_pi₁
                    (F := F) (G := F) U)
    _ = 𝟭 (p.Fiber U) :=
      relativeDiagonalOver_fiberFunctor_comp_leftProjection (F := F) U

/-- Helper for Lemma 4.35.10: the right projection of the transported owner-level diagonal fiber
is the identity functor on the source fiber. -/
private theorem relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_comp_pi₂
    (U : C) :
    ((F.relativeDiagonalOver).fiberFunctor U) ⋙
        (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F U).functor ⋙
        CategoricalPullback.π₂ (F.fiberFunctor U) (F.fiberFunctor U) =
      𝟭 (p.Fiber U) := by
  -- The same calculation with the right projection gives the symmetric identity functor.
  calc
    ((F.relativeDiagonalOver).fiberFunctor U) ⋙
        (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F U).functor ⋙
        CategoricalPullback.π₂ (F.fiberFunctor U) (F.fiberFunctor U)
        =
          ((F.relativeDiagonalOver).fiberFunctor U) ⋙
            (CategoryOver.explicitTwoFibreProductRightProjection F F).fiberFunctor U := by
              simpa [Functor.assoc] using
                congrArg
                  (fun H =>
                    ((F.relativeDiagonalOver).fiberFunctor U) ⋙ H)
                  (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres_functor_comp_pi₂
                    (F := F) (G := F) U)
    _ = 𝟭 (p.Fiber U) :=
      relativeDiagonalOver_fiberFunctor_comp_rightProjection (F := F) U

/-- Helper for Lemma 4.35.10: after projecting to the left fiber coordinate, the transported
owner-level diagonal agrees with the categorical diagonal. -/
private noncomputable abbrev
    relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_first_iso
    (U : C) :
    (((F.relativeDiagonalOver).fiberFunctor U) ⋙
        (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F U).functor ⋙
        CategoricalPullback.π₁ (F.fiberFunctor U) (F.fiberFunctor U)) ≅
      (Δₚ (F.fiberFunctor U)) ⋙
        CategoricalPullback.π₁ (F.fiberFunctor U) (F.fiberFunctor U) :=
  NatIso.ofComponents
    (fun x ↦
      eqToIso
        (congrArg
          (fun H =>
            H.obj x)
          (relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_comp_pi₁
            (F := F) U)))
    (fun {x y} f ↦ by
    -- Both projected functors are the identity on the source fiber, so the map comparison is
    -- exactly the functor-congruence statement for the left projection.
    erw [Functor.congr_hom
      (relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_comp_pi₁
        (F := F) U) f]
    simp [Category.assoc])

/-- Helper for Lemma 4.35.10: after projecting to the right fiber coordinate, the transported
owner-level diagonal agrees with the categorical diagonal. -/
private noncomputable abbrev
    relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso
    (U : C) :
    (((F.relativeDiagonalOver).fiberFunctor U) ⋙
        (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F U).functor ⋙
        CategoricalPullback.π₂ (F.fiberFunctor U) (F.fiberFunctor U)) ≅
      (Δₚ (F.fiberFunctor U)) ⋙
        CategoricalPullback.π₂ (F.fiberFunctor U) (F.fiberFunctor U) :=
  NatIso.ofComponents
    (fun x ↦
      eqToIso
        (congrArg
          (fun H =>
            H.obj x)
          (relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_comp_pi₂
            (F := F) U)))
    (fun {x y} f ↦ by
    -- The right projection is symmetric: both functors are again the identity on each fiber.
    erw [Functor.congr_hom
      (relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_comp_pi₂
        (F := F) U) f]
    simp [Category.assoc])

/-- Helper for Lemma 4.35.10: transporting a fiber object along an equality between an
endofunctor and the identity gives the corresponding transport morphism in the ambient category. -/
private theorem fiberInclusion_map_eqToHom_functor_obj
    {U : C} {J : p.Fiber U ⥤ p.Fiber U}
    (e : J = 𝟭 (p.Fiber U)) (x : p.Fiber U) :
    Functor.Fiber.fiberInclusion.map
      (eqToHom (congrArg (fun H => H.obj x) e)) =
        eqToHom
          (congrArg
            (fun H =>
              Functor.Fiber.fiberInclusion.obj (H.obj x))
            e) := by
  cases e
  rfl

/-- Helper for Lemma 4.35.10: after forgetting to the ambient category, the left projected
component of the comparison isomorphism is the identity map. -/
@[simp] private theorem
    relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_first_iso_app_hom
    (x : S) :
    Functor.Fiber.fiberInclusion.map
      (((relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_first_iso
          (F := F) (p.obj x)).hom.app
        (Functor.Fiber.mk rfl))) = 𝟙 x := by
  -- The component is the transport attached to the left projected functor equality.
  simpa [relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_first_iso] using
    fiberInclusion_map_eqToHom_functor_obj
      (p := p)
      (e :=
        relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_comp_pi₁
          (F := F) (p.obj x))
      (x := Functor.Fiber.mk rfl)

/-- Helper for Lemma 4.35.10: after forgetting to the ambient category, the right projected
component of the comparison isomorphism is the identity map. -/
@[simp] private theorem
    relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso_app_hom
    (x : S) :
    Functor.Fiber.fiberInclusion.map
      (((relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso
          (F := F) (p.obj x)).hom.app
        (Functor.Fiber.mk rfl))) = 𝟙 x := by
  -- The right projected component is the same transport shape, hence also forgets to the identity.
  simpa [relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso] using
    fiberInclusion_map_eqToHom_functor_obj
      (p := p)
      (e :=
        relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_comp_pi₂
          (F := F) (p.obj x))
      (x := Functor.Fiber.mk rfl)

/-- Helper for Lemma 4.35.10: after applying `F`, the left projected comparison component still
forgets to the identity on `F.obj x`. -/
@[simp] private theorem
    relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_first_iso_app_hom_map
    (x : S) :
    F.map
        (Functor.Fiber.fiberInclusion.map
          (((relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_first_iso
              (F := F) (p.obj x)).hom.app
            (Functor.Fiber.mk rfl)))) =
      𝟙 (F.obj x) := by
  rw [relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_first_iso_app_hom
    (F := F) x]
  exact F.map_id x

/-- Helper for Lemma 4.35.10: after applying `F`, the right projected comparison component still
forgets to the identity on `F.obj x`. -/
@[simp] private theorem
    relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso_app_hom_map
    (x : S) :
    F.map
        (Functor.Fiber.fiberInclusion.map
          (((relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso
              (F := F) (p.obj x)).hom.app
            (Functor.Fiber.mk rfl)))) =
      𝟙 (F.obj x) := by
  rw [relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso_app_hom
    (F := F) x]
  exact F.map_id x

/-- Helper for Lemma 4.35.10: the projected comparison isomorphisms satisfy the pullback
coherence relation needed to reconstruct the full comparison `NatIso`. -/
private theorem
    relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_projection_coherence
    (U : C) :
    Functor.whiskerRight
        (relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_first_iso
          (F := F) U).hom
        (F.fiberFunctor U) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft
          (Δₚ (F.fiberFunctor U))
          (CatCommSq.iso
            (CategoricalPullback.π₁ (F.fiberFunctor U) (F.fiberFunctor U))
            (CategoricalPullback.π₂ (F.fiberFunctor U) (F.fiberFunctor U))
            (F.fiberFunctor U) (F.fiberFunctor U)).hom ≫
        (Functor.associator _ _ _).inv =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft
          (((F.relativeDiagonalOver).fiberFunctor U) ⋙
            (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F U).functor)
          (CatCommSq.iso
            (CategoricalPullback.π₁ (F.fiberFunctor U) (F.fiberFunctor U))
            (CategoricalPullback.π₂ (F.fiberFunctor U) (F.fiberFunctor U))
            (F.fiberFunctor U) (F.fiberFunctor U)).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso
            (F := F) U).hom
          (F.fiberFunctor U) := by
  ext x
  cases x with
  | mk x hx =>
      cases hx
      -- The target diagonal carries the identity comparison, while the transported owner-level
      -- diagonal has the same underlying comparison map by the explicit pullback-of-fibres model.
      have hcomp :
          F.map
              (Functor.Fiber.fiberInclusion.map
                (((relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_first_iso
                    (F := F) (p.obj x)).hom.app
                  (Functor.Fiber.mk rfl)))) =
            Functor.Fiber.fiberInclusion.map
              (((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F (p.obj x)).functor.obj
                  ((F.relativeDiagonalOver.fiberFunctor (p.obj x)).obj
                    (Functor.Fiber.mk rfl))).iso.hom) ≫
              F.map
                (Functor.Fiber.fiberInclusion.map
                  (((relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso
                      (F := F) (p.obj x)).hom.app
                    (Functor.Fiber.mk rfl)))) := by
        rw [relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_first_iso_app_hom_map
          (F := F) x]
        have hright :
            Functor.Fiber.fiberInclusion.map
                (((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F (p.obj x)).functor.obj
                    ((F.relativeDiagonalOver.fiberFunctor (p.obj x)).obj
                      (Functor.Fiber.mk rfl))).iso.hom) =
              Functor.Fiber.fiberInclusion.map
                  (((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F (p.obj x)).functor.obj
                      ((F.relativeDiagonalOver.fiberFunctor (p.obj x)).obj
                        (Functor.Fiber.mk rfl))).iso.hom) ≫
                F.map
                  (Functor.Fiber.fiberInclusion.map
                    (((relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso
                        (F := F) (p.obj x)).hom.app
                      (Functor.Fiber.mk rfl)))) := by
          have hmap :=
            relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso_app_hom_map
              (F := F) x
          let mid :
              F.obj x ⟶ F.obj x :=
            Functor.Fiber.fiberInclusion.map
              (((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F (p.obj x)).functor.obj
                  ((F.relativeDiagonalOver.fiberFunctor (p.obj x)).obj
                    (Functor.Fiber.mk rfl))).iso.hom)
          have hmap' :
              F.map
                  (Functor.Fiber.fiberInclusion.map
                    (eqToHom
                      (congrArg
                        (fun H =>
                          H.obj (Functor.Fiber.mk rfl))
                        (relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_comp_pi₂
                          (F := F) (p.obj x))))) =
                𝟙 (F.obj x) := by
            simpa [relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso] using
              hmap
          calc
            mid = mid ≫ 𝟙 (F.obj x) := by
              simp [mid]
            _ = mid ≫
                  F.map
                    (Functor.Fiber.fiberInclusion.map
                      (((relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso
                          (F := F) (p.obj x)).hom.app
                        (Functor.Fiber.mk rfl)))) := by
                          simpa [mid] using congrArg (fun k => mid ≫ k) hmap.symm
        exact
          (relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_app_iso_hom
            (F := F) x).symm.trans hright
      simpa [NatTrans.comp_app, Functor.comp_map, Category.assoc] using hcomp

/-- Helper for Lemma 4.35.10: after transporting the fiber of the owner-level relative diagonal
across the canonical pullback-of-fibres equivalence, one obtains the categorical diagonal of the
fiber functor up to natural isomorphism. -/
private noncomputable abbrev relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_iso_diagonal
    (U : C) :
    ((F.relativeDiagonalOver).fiberFunctor U) ⋙
        (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F U).functor ≅
      Δₚ (F.fiberFunctor U) := by
  -- Route correction: package the comparison through the two pullback projections and then use
  -- the explicit pullback-of-fibres normalization to recover the full diagonal isomorphism.
  exact
    CategoricalPullback.mkNatIso
      (relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_first_iso
        (F := F) U)
      (relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso
        (F := F) U)
      (relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_projection_coherence
        (F := F) U)

/-- Helper for Lemma 4.35.10: the fiber of the owner-level relative diagonal is an equivalence
exactly when the categorical diagonal of the fiber functor is an equivalence. -/
private theorem relativeDiagonalOver_fiberFunctor_isEquivalence_iff_diagonal_isEquivalence
    (U : C) :
    ((F.relativeDiagonalOver).fiberFunctor U).IsEquivalence ↔
      (Δₚ (F.fiberFunctor U)).IsEquivalence := by
  let E := CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F U
  let e :
      ((F.relativeDiagonalOver).fiberFunctor U) ⋙ E.functor ≅
        Δₚ (F.fiberFunctor U) :=
    relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_iso_diagonal
      (F := F) U
  constructor
  · intro hDiagonal
    -- Compose the fiber functor with the canonical equivalence to move into the categorical
    -- pullback model used by the purely categorical diagonal criterion.
    letI : ((F.relativeDiagonalOver).fiberFunctor U).IsEquivalence := hDiagonal
    letI : E.functor.IsEquivalence := by infer_instance
    have hComp :
        (((F.relativeDiagonalOver).fiberFunctor U) ⋙ E.functor).IsEquivalence :=
      inferInstance
    exact (Functor.isEquivalence_iff_of_iso e).1 hComp
  · intro hDiagonal
    -- The converse transports the diagonal equivalence back across the same packaged
    -- equivalence, then cancels it from the right.
    letI : E.functor.IsEquivalence := by infer_instance
    have hComp :
        (((F.relativeDiagonalOver).fiberFunctor U) ⋙ E.functor).IsEquivalence := by
      exact (Functor.isEquivalence_iff_of_iso e).2 hDiagonal
    exact Functor.isEquivalence_of_comp_right ((F.relativeDiagonalOver).fiberFunctor U) E.functor

private theorem basedFunctor_diagonal_isEquivalenceOverBase_iff_fiberwise :
    F.relativeDiagonalOver.IsEquivalenceOverBase ↔
      ∀ U : C, (Δₚ (F.fiberFunctor U)).IsEquivalence := by
  constructor
  · intro hDiagonal U
    -- Lemma 4.35.9 reduces the owner-level equivalence-over-base condition to each fiber, and the
    -- fixed-fiber bridge above rewrites those fibers as the textbook diagonal functors.
    exact
      (relativeDiagonalOver_fiberFunctor_isEquivalence_iff_diagonal_isEquivalence
        (F := F) U).1
        (BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase
          F.relativeDiagonalOver hDiagonal U)
  · intro hFiber
    -- Package the diagonal as a morphism of categories fibred in groupoids and invoke the
    -- fiberwise equivalence criterion from Lemma 4.35.9.
    let ownerF :
        FibredInGroupoidsOver.ofFunctor (BasedCategory.ofFunctor p).p ⟶
          FibredInGroupoidsOver.ofFunctor (BasedCategory.ofFunctor p').p :=
      FibredInGroupoidsMor.ofBasedFunctor F
    letI :
        IsFibredInGroupoids (CategoryOver.explicitTwoFibreProduct F F).p :=
      by
        simpa [ownerF] using
          (FibredInGroupoidsMor.diagonalTargetProjection_isFibredInGroupoids
            (F := ownerF))
    let diagonalMor :
        FibredInGroupoidsOver.ofFunctor (BasedCategory.ofFunctor p).p ⟶
          FibredInGroupoidsOver.ofFunctor
            (CategoryOver.explicitTwoFibreProduct F F).p :=
      FibredInGroupoidsMor.ofBasedFunctor F.relativeDiagonalOver
    have hEq :
        (FibredInGroupoidsMor.G diagonalMor).IsEquivalence := by
      refine (FibredInGroupoidsMor.isEquivalence_iff_fiberwise (F := diagonalMor)).2 ?_
      intro U
      simpa [diagonalMor] using
        (relativeDiagonalOver_fiberFunctor_isEquivalence_iff_diagonal_isEquivalence
          (F := F) U).2 (hFiber U)
    simpa [diagonalMor] using
      (FibredInGroupoidsMor.isEquivalenceOverBase_of_isEquivalence
        (F := diagonalMor) hEq)

-- Proof sketch: the textbook statement is the global diagonal criterion in `Cat/C`, realized by
-- the explicit fibred `2`-fibre-product model from Lemma `4.35.7`.
end

namespace FibredInGroupoidsMor

section

open FibredInGroupoidsOver

variable {C : Type (max u v)} [Category.{v} C]
variable {X Y : FibredInGroupoidsOver.{v, max u v, max u v, v} C}
variable (F : X ⟶ Y)

/- Domain-style sampling for Lemma 4.35.10:
- primary domain: morphisms of categories fibred in groupoids over a fixed base together with
  their canonical diagonal into the fibred self-`2`-fibre product;
- sampled owner-level declarations:
  `FibredInGroupoidsMor`,
  `FibredInGroupoidsOver.twoFibreProduct`,
  `FibredInGroupoidsMor.diagonalMor`,
  `FibredInGroupoidsMor.fiberFunctor`,
  `FibredInGroupoidsMor.IsEquivalenceOverBase`;
- best owner abstraction: the morphism `F : FibredInGroupoidsMor X Y`, with the target owner
  `FibredInGroupoidsOver.twoFibreProduct F F` and the bundled canonical diagonal `F.diagonalMor`;
- primitive data: only the owner morphism `F`;
- derived API: the fully-faithful criterion expressed directly in terms of the canonical diagonal
  over-base equivalence predicate.

Source/core/bridge triage:
- `source-facing`: Lemma 4.35.10 on `FibredInGroupoidsMor`;
- `core/canonical`: `Nonempty F.FullyFaithful` and the owner predicate
  `F.diagonalMor.IsEquivalenceOverBase`;
- `bridge/view`: the raw `BasedFunctor` diagonal criterion above. -/

/-- Companion bridge: the owner-level diagonal of `F` is an equivalence over the base exactly
when the induced diagonal on every fiber is an equivalence. -/
theorem diagonal_isEquivalenceOverBase_iff_fiberwise :
    IsEquivalenceOverBase (diagonalMor F) ↔
      ∀ U : C, (Δₚ (fiberFunctor F U)).IsEquivalence := by
  simpa [FibredInGroupoidsMor.diagonalMor] using
    basedFunctor_diagonal_isEquivalenceOverBase_iff_fiberwise (toBasedFunctor F)

/-- Lemma 4.35.10: a morphism of categories fibred in groupoids over `C` is fully faithful if and
only if its canonical diagonal into the fibred self-`2`-fibre product is an equivalence over
`C`. The target is the chapter owner `FibredInGroupoidsOver.twoFibreProduct F F`, and the
diagonal is the bundled owner morphism `F.diagonalMor`.
-/
theorem fullyFaithful_iff_diagonal_isEquivalenceOverBase :
    Nonempty (toBasedFunctor F).FullyFaithful ↔ IsEquivalenceOverBase (diagonalMor F) := by
  rw [diagonal_isEquivalenceOverBase_iff_fiberwise, fullyFaithful_iff_fiberwise]
  constructor
  · intro hF U
    exact
      (fullyFaithful_iff_diagonal_to_self_pullback_isEquivalence (fiberFunctor F U)).mp (hF U)
  · intro hΔ U
    exact
      (fullyFaithful_iff_diagonal_to_self_pullback_isEquivalence (fiberFunctor F U)).mpr (hΔ U)

end

end FibredInGroupoidsMor

end CategoryTheory

/-! ### Lemma_4_35_11 (from Chap04) -/
universe u v

namespace CategoryTheory

open Bicategory
open FibredInGroupoidsMor
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {X₁ X₂ X₃ X₄ : FibredInGroupoidsOver C}

/- Domain-style sampling for Lemma 4.35.11:
- primary domain: bicategorical hom-categories of categories fibred in groupoids over a fixed
  base, with equivalences expressed on explicit morphisms over the base;
- inspected owner-level declarations:
  `FibredInGroupoidsOver C`,
  `BasedFunctor.IsEquivalenceOverBase`,
  `Bicategory.precomp`,
  `Bicategory.postcomp`,
  `Bicategory.associatorNatIsoRight`,
  `Bicategory.associatorNatIsoLeft`;
- best owner abstraction: the owner homs `X₁ ⟶ X₂` and `X₃ ⟶ X₄` in
  `FibredInGroupoidsOver C`, together with the owner predicate `IsEquivalenceOverBase`; the
  packaged bicategorical equivalence `X ≌ Y` is derived;
- primitive data: morphisms `φ : X₁ ⟶ X₂`, `ψ : X₃ ⟶ X₄` and proofs
  `IsEquivalenceOverBase φ`,
  `IsEquivalenceOverBase ψ`;
- derived API: the internal bicategorical equivalences built from those data, and the induced
  equivalences on hom-categories via `precomp`, `postcomp`, and their composite.

Source/core/bridge triage:
- `source-facing`: the explicit over-base morphisms `φ`, `ψ` and the induced end functor on the
  hom-categories;
- `core/canonical`: bicategorical hom-categories, `precomp`, `postcomp`, and `Functor.IsEquivalence`;
- `bridge/view`: `FibredInGroupoidsMor.exists_equivalence` and
  `FibredInGroupoidsOver.hom_isEquivalenceOverBase`. -/

namespace Bicategory

variable {B : Type u} [Bicategory B]
variable {a b c d : B}

/-- In any bicategory, whiskering on the right by an equivalence induces an equivalence on the
corresponding hom-category. -/
theorem precomp_isEquivalence (c : B) (e : a ≌ b) :
    Functor.IsEquivalence (precomp c e.hom) :=
  -- The quasi-inverse is given by whiskering with the inverse 1-morphism.
  Functor.IsEquivalence.mk'
    (precomp c e.inv)
    -- The counit is assembled from the bicategorical counit and the unitor/associator coherence.
    ((leftUnitorNatIso b c).symm ≪≫
      Functor.mapIso (precomposing b b c) e.counit.symm ≪≫
      associatorNatIsoRight e.inv e.hom c)
    -- The unit is the dual coherence built from the bicategorical unit of `e`.
    ((associatorNatIsoRight e.hom e.inv c).symm ≪≫
      Functor.mapIso (precomposing a a c) e.unit.symm ≪≫
      leftUnitorNatIso a c)

/-- In any bicategory, whiskering on the left by an equivalence induces an equivalence on the
corresponding hom-category. -/
theorem postcomp_isEquivalence (a : B) (e : c ≌ d) :
    Functor.IsEquivalence (postcomp a e.hom) :=
  -- The quasi-inverse is given by whiskering with the inverse 1-morphism.
  Functor.IsEquivalence.mk'
    (postcomp a e.inv)
    -- The counit uses the unit of `e` transported across the right unitor and associator.
    ((rightUnitorNatIso a c).symm ≪≫
      Functor.mapIso (postcomposing a c c) e.unit ≪≫
      (associatorNatIsoLeft a e.hom e.inv).symm)
    -- The unit uses the counit of `e` in the dual coherence pattern.
    (associatorNatIsoLeft a e.inv e.hom ≪≫
      Functor.mapIso (postcomposing a d d) e.counit ≪≫
      rightUnitorNatIso a d)

end Bicategory

/-- Lemma 4.35.11: if `𝒮₁`, `𝒮₂`, `𝒮₃`, and `𝒮₄` are categories fibred in groupoids over `C`,
and `φ : 𝒮₁ ⟶ 𝒮₂`, `ψ : 𝒮₃ ⟶ 𝒮₄` are equivalences over the base, then precomposition by `φ`
and postcomposition by `ψ` induce an equivalence
`Mor_{Cat/C}(𝒮₂, 𝒮₃) → Mor_{Cat/C}(𝒮₁, 𝒮₄)`. Via Definition 4.35.6, these hom-categories are
canonically `X₂ ⟶ X₃` and `X₁ ⟶ X₄`. -/
theorem prePostcomposeFunctorOfOverBaseEquivalences_isEquivalence
    (φ : X₁ ⟶ X₂) (ψ : X₃ ⟶ X₄)
    (hφ : IsEquivalenceOverBase φ) (hψ : IsEquivalenceOverBase ψ) :
    Functor.IsEquivalence (postcomp X₂ ψ ⋙ precomp X₄ φ) := by
  -- Replace the explicit over-base equivalences by packaged bicategorical equivalences.
  rcases exists_equivalence φ hφ with ⟨eφ, rfl⟩
  rcases exists_equivalence ψ hψ with ⟨eψ, rfl⟩
  -- Each whiskering functor is an equivalence on the corresponding hom-category.
  letI : Functor.IsEquivalence (postcomp X₂ eψ.hom) :=
    Bicategory.postcomp_isEquivalence X₂ eψ
  letI : Functor.IsEquivalence (precomp X₄ eφ.hom) :=
    Bicategory.precomp_isEquivalence X₄ eφ
  -- The target functor is the composite of those two equivalences.
  infer_instance

end CategoryTheory

/-! ### Lemma_4_35_12 (from Chap04) -/
universe v₁ u₁ u₂

namespace CategoryTheory

open CategoryOver Functor Functor.Fiber IsHomLift

variable {C : Type u₁} [Category.{v₁} C]

/- Domain-style sampling for Lemma 4.35.12:
- primary domain: relative/absolute inertia projections over a fixed base and the owner predicate
  `IsFibredInGroupoids`;
- inspected owner-level declarations:
  `relativeInertiaProjection`,
  `CategoryOver.absoluteInertiaOver`,
  `CategoryOver.absoluteInertiaProjection_isFibered`,
  `IsFibredInGroupoids`,
  `isFibredInGroupoids_of_isFibered_and_fiber_groupoid`,
  `RelativeInertiaHom.isIso_of_isIso`;
- best owner abstraction: the core theorem should live on the raw projection
  `relativeInertiaProjection p p`; the `Cat/C` theorem for `absoluteInertiaOver 𝒮` is only the
  source-facing bridge obtained by packaging the same owner;
- primitive data: only a functor `p : S ⥤ C` together with the existing
  `IsFibredInGroupoids p` structure;
- derived API: the bridge theorem and bundled instance for `absoluteInertiaOver`, obtained by
  reusing the existing fibredness owner theorem and checking that each inertia fiber is again a
  groupoid.

Source/core/bridge triage:
- `source-facing`: `absoluteInertiaProjection_isFibredInGroupoids`;
- `core/canonical`: `relativeInertiaProjection`, `Functor.Fiber`, and
  `IsFibredInGroupoids`;
- `bridge/view`: the definitional identification
  `(absoluteInertiaOver (BasedCategory.ofFunctor p)).p = relativeInertiaProjection p p`. -/

variable {S : Type u₂} [Category.{v₁} S]

section

variable (p : S ⥤ C) [IsFibredInGroupoids p]

/-- Helper for Lemma 4.35.12: every arrow of the identity functor on the base category is
strongly cartesian over itself. -/
private theorem idFunctor_isStronglyCartesian {R T : C} (f : R ⟶ T) :
    Functor.IsStronglyCartesian (𝟭 C) f f where
  -- The identity functor turns the displayed arrow into a tautological lift of itself.
  toIsHomLift := by
    simpa using
      (show Functor.IsHomLift (𝟭 C) ((𝟭 C).map f) f from inferInstance)
  universal_property' := by
    intro a g φ hφ
    -- Any competing lift over `g ≫ f` is definitionally the same composite.
    subst_hom_lift (𝟭 C) (g ≫ f) φ
    refine ⟨g, ?_, ?_⟩
    · constructor
      · simpa using
          (show Functor.IsHomLift (𝟭 C) ((𝟭 C).map g) g from inferInstance)
      · rfl
    · intro π hπ
      let _ := hπ.1
      subst_hom_lift (𝟭 C) g π
      rfl

/-- Helper for Lemma 4.35.12: the identity functor on the base category is fibered. -/
private theorem idFunctor_isFibered : (𝟭 C).IsFibered := by
  -- For a base arrow `f`, choose `f` itself as a strongly cartesian lift.
  apply Functor.IsFibered.of_exists_isStronglyCartesian
  intro a R f
  exact ⟨R, f, idFunctor_isStronglyCartesian (C := C) f⟩

omit [IsFibredInGroupoids p] in
/-- Helper for Lemma 4.35.12: a vertical automorphism of an inertia object pulls back along a
strongly cartesian lift of its source object. -/
private theorem pullback_automorphism_hom
    {X : RelativeInertiaObject p} {R : C} {y : S} {f : R ⟶ p.obj X.x}
    (a : y ⟶ X.x) [p.IsStronglyCartesian f a] :
    ∃ αy : y ⟶ y, p.IsHomLift (𝟙 R) αy ∧ αy ≫ a = a ≫ X.α.hom := by
  haveI : p.IsHomLift (𝟙 (p.obj X.x)) X.α.hom := by
    simpa [X.map_hom_eq_id] using
      (inferInstance : p.IsHomLift (p.map X.α.hom) X.α.hom)
  haveI : p.IsHomLift f (a ≫ X.α.hom) := by
    simpa using
      (inferInstance : p.IsHomLift (f ≫ 𝟙 (p.obj X.x)) (a ≫ X.α.hom))
  -- Factor `a ≫ X.α.hom` uniquely through the chosen strongly cartesian lift `a`.
  obtain ⟨αy, hαy, -⟩ :=
    Functor.IsStronglyCartesian.universal_property p f a (𝟙 R) f (Category.id_comp f).symm
      (a ≫ X.α.hom)
  exact ⟨αy, hαy.1, hαy.2⟩

omit [IsFibredInGroupoids p] in
/-- Helper for Lemma 4.35.12: the pulled-back vertical endomorphism is again an automorphism. -/
private theorem pullback_automorphism_iso
    {X : RelativeInertiaObject p} {R : C} {y : S} {f : R ⟶ p.obj X.x}
    (a : y ⟶ X.x) [p.IsStronglyCartesian f a] :
    ∃ e : y ≅ y, p.IsHomLift (𝟙 R) e.hom ∧ e.hom ≫ a = a ≫ X.α.hom := by
  obtain ⟨αh, hαh_lift, hαh_eq⟩ :=
    pullback_automorphism_hom (p := p) (X := X) (R := R) (y := y) (f := f) a
  let Xinv : RelativeInertiaObject p :=
    { x := X.x
      α := X.α.symm
      map_hom_eq_id := by
        simpa [X.map_hom_eq_id] using Functor.map_inv p X.α.hom }
  obtain ⟨αi, hαi_lift, hαi_eq⟩ :=
    pullback_automorphism_hom (p := p) (X := Xinv) (R := R) (y := y) (f := f) a
  have hαi_eq' : αi ≫ a = a ≫ X.α.inv := by
    simpa [Xinv] using hαi_eq
  have hαhαi : αh ≫ αi = 𝟙 y := by
    letI : p.IsHomLift (𝟙 R) αh := hαh_lift
    letI : p.IsHomLift (𝟙 R) αi := hαi_lift
    haveI : p.IsHomLift (𝟙 R) (𝟙 y) := by
      exact IsHomLift.id (IsHomLift.domain_eq p f a)
    -- Compare the two candidate vertical factorizations after postcomposing with `a`.
    apply Functor.IsStronglyCartesian.ext (p := p) (f := f) (φ := a) (g := 𝟙 R)
    calc
      (αh ≫ αi) ≫ a = αh ≫ (αi ≫ a) := by simp [Category.assoc]
      _ = αh ≫ (a ≫ X.α.inv) := by rw [hαi_eq']
      _ = (αh ≫ a) ≫ X.α.inv := by simp [Category.assoc]
      _ = (a ≫ X.α.hom) ≫ X.α.inv := by rw [hαh_eq]
      _ = a := by simp [Category.assoc]
      _ = (𝟙 y) ≫ a := by simp
  have hαiαh : αi ≫ αh = 𝟙 y := by
    letI : p.IsHomLift (𝟙 R) αh := hαh_lift
    letI : p.IsHomLift (𝟙 R) αi := hαi_lift
    haveI : p.IsHomLift (𝟙 R) (𝟙 y) := by
      exact IsHomLift.id (IsHomLift.domain_eq p f a)
    -- The inverse relation is proved by the same uniqueness argument through `a`.
    apply Functor.IsStronglyCartesian.ext (p := p) (f := f) (φ := a) (g := 𝟙 R)
    calc
      (αi ≫ αh) ≫ a = αi ≫ (αh ≫ a) := by simp [Category.assoc]
      _ = αi ≫ (a ≫ X.α.hom) := by rw [hαh_eq]
      _ = (αi ≫ a) ≫ X.α.hom := by simp [Category.assoc]
      _ = (a ≫ X.α.inv) ≫ X.α.hom := by rw [hαi_eq']
      _ = a := by simp [Category.assoc]
      _ = (𝟙 y) ≫ a := by simp
  exact ⟨⟨αh, αi, hαhαi, hαiαh⟩, hαh_lift, hαh_eq⟩

/-- Helper for Lemma 4.35.12: every base arrow into an inertia object admits a strongly
cartesian lift in the inertia projection. -/
private theorem relative_inertia_lift_isStronglyCartesian
    {X : RelativeInertiaObject p} {R : C} (f : R ⟶ p.obj X.x) :
    ∃ Y : RelativeInertiaObject p, ∃ φ : Y ⟶ X,
      (relativeInertiaProjection p p).IsStronglyCartesian f φ := by
  obtain ⟨y, a, ha_cart⟩ := IsPreFibered.exists_isCartesian p rfl f
  letI : p.IsCartesian f a := ha_cart
  letI : p.IsStronglyCartesian f a :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian p f a
  have hy : p.obj y = R := IsHomLift.domain_eq p f a
  obtain ⟨e, he_lift, he_eq⟩ :=
    pullback_automorphism_iso (p := p) (X := X) (R := R) (y := y) (f := f) a
  let Y : RelativeInertiaObject p :=
    { x := y
      α := e
      map_hom_eq_id := by
        letI : p.IsHomLift (𝟙 R) e.hom := he_lift
        subst hy
        simpa using (IsHomLift.eq_of_isHomLift p (𝟙 (p.obj y)) e.hom).symm }
  let φ : Y ⟶ X :=
    { φ := a
      comm := by
        simpa [Y] using he_eq }
  refine ⟨Y, φ, ?_⟩
  refine
    { toIsHomLift := by
        refine IsHomLift.of_fac' (relativeInertiaProjection p p) f φ ?_ rfl ?_
        · simpa [relativeInertiaProjection, Y] using hy
        · simpa [relativeInertiaProjection, φ, Y] using (IsHomLift.fac' p f a)
      universal_property' := ?_ }
  intro Z g ψ hψ
  have hψlift : p.IsHomLift (g ≫ f) ψ.φ := by
    letI : (relativeInertiaProjection p p).IsHomLift (g ≫ f) ψ := hψ
    refine IsHomLift.of_fac' p (g ≫ f) ψ.φ rfl rfl ?_
    simpa [relativeInertiaProjection] using
      (IsHomLift.fac' (p := relativeInertiaProjection p p) (f := g ≫ f) (φ := ψ))
  letI : p.IsHomLift (g ≫ f) ψ.φ := hψlift
  obtain ⟨χ0, hχ0, hχ0_uniq⟩ :=
    Functor.IsStronglyCartesian.universal_property p f a g (g ≫ f) rfl ψ.φ
  have hχ0_fac : χ0 ≫ a = ψ.φ := hχ0.2
  letI : p.IsHomLift g χ0 := hχ0.1
  have hχ0_comm : Z.α.hom ≫ χ0 = χ0 ≫ e.hom := by
    haveI : p.IsHomLift (𝟙 (p.obj Z.x)) Z.α.hom := by
      simpa [Z.map_hom_eq_id] using
        (inferInstance : p.IsHomLift (p.map Z.α.hom) Z.α.hom)
    haveI : p.IsHomLift g (Z.α.hom ≫ χ0) := by
      exact IsHomLift.comp_lift_id_left' (p := p) (p.obj Z.x) Z.α.hom g χ0
    haveI : p.IsHomLift (𝟙 R) e.hom := he_lift
    haveI : p.IsHomLift g (χ0 ≫ e.hom) := by
      exact IsHomLift.comp_lift_id_right' (p := p) g χ0 R e.hom
    -- Recover the inertia commutation relation by comparing both candidates after `a`.
    apply Functor.IsStronglyCartesian.ext (p := p) (f := f) (φ := a) (g := g)
    calc
      (Z.α.hom ≫ χ0) ≫ a = Z.α.hom ≫ (χ0 ≫ a) := by simp [Category.assoc]
      _ = Z.α.hom ≫ ψ.φ := by rw [hχ0_fac]
      _ = ψ.φ ≫ X.α.hom := by simpa using ψ.comm
      _ = (χ0 ≫ a) ≫ X.α.hom := by rw [hχ0_fac]
      _ = χ0 ≫ (a ≫ X.α.hom) := by simp [Category.assoc]
      _ = χ0 ≫ (e.hom ≫ a) := by rw [← he_eq]
      _ = (χ0 ≫ e.hom) ≫ a := by simp [Category.assoc]
  let χ : Z ⟶ Y :=
    { φ := χ0
      comm := by
        simpa [Y] using hχ0_comm }
  refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
  · refine IsHomLift.of_fac' (relativeInertiaProjection p p) g χ rfl ?_ ?_
    · simpa [relativeInertiaProjection, Y] using hy
    · simpa [relativeInertiaProjection, χ, Y] using (IsHomLift.fac' p g χ0)
  · apply RelativeInertiaHom.ext
    exact hχ0_fac
  · intro π hπ
    apply RelativeInertiaHom.ext
    have hπlift : p.IsHomLift g π.φ := by
      letI : (relativeInertiaProjection p p).IsHomLift g π := hπ.1
      refine IsHomLift.of_fac' p g π.φ rfl ?_ ?_
      · simpa [relativeInertiaProjection, Y] using hy
      · simpa [relativeInertiaProjection, Y] using
          (IsHomLift.fac' (relativeInertiaProjection p p) g π)
    have hπfac : π.φ ≫ a = ψ.φ := by
      simpa using congrArg RelativeInertiaHom.φ hπ.2
    exact hχ0_uniq π.φ ⟨hπlift, hπfac⟩

/-- Helper for Lemma 4.35.12: the raw absolute inertia projection `relativeInertiaProjection p p`
is fibered. -/
private theorem relativeInertiaProjection_isFibered_self :
    (relativeInertiaProjection p p).IsFibered := by
  -- Route correction: build the strongly cartesian lift directly in the inertia category, rather
  -- than passing through a homogeneous owner theorem that fixes the total-category universe.
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro X R f
  obtain ⟨Y, φ, hφ⟩ :=
    relative_inertia_lift_isStronglyCartesian (p := p) (X := X) (R := R) f
  exact ⟨Y, φ, hφ⟩

/-- Helper for Lemma 4.35.12: every morphism in a standard fiber of the absolute inertia
projection is an isomorphism. -/
private theorem relativeInertiaProjection_fiber_hom_isIso
    (U : C) {X Y : (relativeInertiaProjection p p).Fiber U} (φ : X ⟶ Y) :
    IsIso φ := by
  let q := relativeInertiaProjection p p
  letI : q.IsHomLift (𝟙 U) φ.1 := φ.2
  -- Forgetting the inertia structure shows that the underlying morphism lies in the fiber of `p`.
  letI : p.IsHomLift (𝟙 U) φ.1.φ := by
    refine of_fac' p (𝟙 U) φ.1.φ ?_ ?_ ?_
    · simpa [q, relativeInertiaProjection] using domain_eq q (𝟙 U) φ.1
    · simpa [q, relativeInertiaProjection] using codomain_eq q (𝟙 U) φ.1
    · simpa [q, relativeInertiaProjection] using fac' q (𝟙 U) φ.1
  -- The underlying vertical morphism is invertible in the fiber of `p`, hence also in `S`.
  letI : IsIso (homMk p U φ.1.φ) :=
    IsFibredInGroupoids.hom_isIso U (homMk p U φ.1.φ)
  letI : IsIso φ.1.φ := by
    simpa using
      (inferInstance : IsIso ((fiberInclusion : p.Fiber U ⥤ _).map (homMk p U φ.1.φ)))
  letI : IsIso φ.1 := RelativeInertiaHom.isIso_of_isIso φ.1
  -- The inverse of a vertical isomorphism still lies over the identity, so it defines the
  -- inverse in the inertia fiber.
  letI : q.IsHomLift (𝟙 U) (inv φ.1) := by
    simpa [q] using lift_id_inv_isIso q U φ.1
  refine ⟨?_⟩
  use ⟨inv φ.1, inferInstance⟩
  constructor
  · apply Fiber.hom_ext
    change φ.1 ≫ inv φ.1 = 𝟙 X.1
    simp
  · apply Fiber.hom_ext
    change inv φ.1 ≫ φ.1 = 𝟙 Y.1
    simp

/-- Helper for Lemma 4.35.12: each standard fiber of the absolute inertia projection is a
groupoid. -/
private instance relativeInertiaProjection_fiber_isGroupoid
    (U : C) :
    IsGroupoid ((relativeInertiaProjection p p).Fiber U) where
  all_isIso := relativeInertiaProjection_fiber_hom_isIso p U

-- Proof sketch: reuse the canonical owner theorem
-- `CategoryOver.absoluteInertiaProjection_isFibered` for the projection part, then apply
-- Lemma `4.35.2` and check directly that each inertia fiber is a groupoid because a morphism in
-- the inertia fiber is a vertical morphism in `S`, hence an isomorphism.
/-- Owner-level form of Lemma 4.35.12: if `p : S ⥤ C` is fibred in groupoids, then its absolute
inertia projection `relativeInertiaProjection p p : I_S ⥤ C` is again fibred in groupoids. The
source-facing `Cat/C` packaging is the companion theorem
`CategoryOver.absoluteInertiaProjection_isFibredInGroupoids`. -/
theorem relativeInertiaProjection_isFibredInGroupoids :
    IsFibredInGroupoids (relativeInertiaProjection p p) := by
  refine
    isFibredInGroupoids_of_isFibered_and_fiber_groupoid
      (relativeInertiaProjection p p)
      ?_
      ?_
  · simpa using
      relativeInertiaProjection_isFibered_self (p := p)
  · intro U
    infer_instance

end

-- Proof sketch: this is only the `Cat/C` bridge form of
-- `relativeInertiaProjection_isFibredInGroupoids`, since `(absoluteInertiaOver 𝒮).p` is
-- definitionally `relativeInertiaProjection 𝒮.p 𝒮.p`.
namespace CategoryOver

/-- Lemma 4.35.12: if `p : S ⥤ C` is fibred in groupoids, then the inertia fibred category
`I_S → C` is again fibred in groupoids over `C`. -/
theorem absoluteInertiaProjection_isFibredInGroupoids
    (𝒮 : BasedCategory.{v₁, u₁} C) [IsFibredInGroupoids 𝒮.p] :
    IsFibredInGroupoids (absoluteInertiaOver 𝒮).p := by
  simpa [absoluteInertiaOver] using relativeInertiaProjection_isFibredInGroupoids 𝒮.p

/-- The absolute inertia projection inherits the canonical `IsFibredInGroupoids` instance from
Lemma 4.35.12. -/
instance (𝒮 : BasedCategory.{v₁, u₁} C) [IsFibredInGroupoids 𝒮.p] :
    IsFibredInGroupoids (absoluteInertiaOver 𝒮).p :=
  absoluteInertiaProjection_isFibredInGroupoids 𝒮

end CategoryOver

end CategoryTheory

/-! ### Lemma_4_35_13 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open CategoryTheory.IsHomLift

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]

/- Domain-style sampling for Lemma 4.35.13:
- primary domain: fibred-in-groupoids structures on functors to a slice category.
- inspected owner-level declarations:
  `CategoryTheory.IsFibredInGroupoids`,
  `Functor.isFibered_of_comp_over_forget`,
  `Functor.isStronglyCartesian_of_comp_over_forget`,
  `IsFibredInGroupoids.isStronglyCartesian_map`.
- best owner abstraction: the source-facing statement should live directly on the owner class
  `IsFibredInGroupoids`; the slice-level structure is derived from the two transfer lemmas of
  Lemma `4.33.11`, not stored through a parallel local wrapper.
- primitive data: the fibred-in-groupoids structure on `p' ⋙ Over.forget U`.
- derived API: the induced `p'.IsFibered` instance from Lemma `4.33.11` and the resulting
  fibred-in-groupoids structure on `p'`.

Source/core/bridge triage:
- `source-facing`: `isFibredInGroupoids_of_comp_over_forget`.
- `core/canonical`: `IsFibredInGroupoids`, `Functor.IsFibered`, `Functor.IsStronglyCartesian`.
- `bridge/view`: the anonymous instance below derived from the source-facing theorem. -/

/-- Helper for Lemma 4.35.13: forgetting a vertical morphism in the slice gives a vertical
morphism in the underlying fiber over the source object. -/
theorem isHomLift_id_comp_over_forget {U : C} (p' : S ⥤ Over U)
    {A : Over U} {x y : S} {g : x ⟶ y} :
    p'.IsHomLift (𝟙 A) g → (p' ⋙ Over.forget U).IsHomLift (𝟙 A.left) g := by
  intro hg
  let q := p' ⋙ Over.forget U
  letI : p'.IsHomLift (𝟙 A) g := hg
  -- Taking underlying arrows in `C` turns the slice identity square into the base identity square.
  refine IsHomLift.of_fac' q (𝟙 A.left) g ?_ ?_ ?_
  · simpa [q] using congrArg (Over.forget U).obj (domain_eq p' (𝟙 A) g)
  · simpa [q] using congrArg (Over.forget U).obj (codomain_eq p' (𝟙 A) g)
  · simpa [q] using congrArg (Over.forget U).map (fac' p' (𝟙 A) g)

/-- Helper for Lemma 4.35.13: every morphism in a fiber of `p'` is invertible because it becomes a
morphism in the corresponding fiber of `p' ⋙ Over.forget U`, which is already a groupoid. -/
theorem fiber_hom_isIso_of_comp_over_forget {U : C} (p' : S ⥤ Over U)
    [IsFibredInGroupoids (p' ⋙ Over.forget U)] (A : Over U)
    {X Y : p'.Fiber A} (φ : X ⟶ Y) : IsIso φ := by
  let q := p' ⋙ Over.forget U
  letI : p'.IsHomLift (𝟙 A) φ.1 := φ.2
  -- View the slice-fiber morphism as a morphism in the underlying fiber over `A.left`.
  haveI : q.IsHomLift (𝟙 A.left) φ.1 :=
    isHomLift_id_comp_over_forget (p' := p') (A := A) (g := φ.1) inferInstance
  haveI : IsIso (Functor.Fiber.homMk q A.left φ.1) :=
    CategoryTheory.IsFibredInGroupoids.hom_isIso (p := q) A.left
      (Functor.Fiber.homMk q A.left φ.1)
  haveI : IsIso φ.1 := by
    simpa using
      (inferInstance :
        IsIso
          ((Functor.Fiber.fiberInclusion : q.Fiber A.left ⥤ S).map
            (Functor.Fiber.homMk q A.left φ.1)))
  let e := asIso φ.1
  -- The inverse of a vertical isomorphism is vertical over the same identity map.
  haveI : p'.IsHomLift (𝟙 A) e.inv := by
    simpa [e] using (IsHomLift.lift_id_inv_isIso (p := p') A φ.1)
  refine ⟨⟨⟨e.inv, inferInstance⟩, ?_, ?_⟩⟩
  · -- The fiber inverse has the expected underlying composite in `S`.
    apply Functor.Fiber.hom_ext
    change φ.1 ≫ e.inv = 𝟙 X.1
    simp [e]
  · -- The other composite is handled by the underlying inverse in `S`.
    apply Functor.Fiber.hom_ext
    change e.inv ≫ φ.1 = 𝟙 Y.1
    simp [e]

/-- Helper for Lemma 4.35.13: each fiber of `p'` is a groupoid once the fibers of the composed
functor `p' ⋙ Over.forget U` are groupoids. -/
instance fiber_isGroupoid_of_comp_over_forget {U : C} (p' : S ⥤ Over U)
    [IsFibredInGroupoids (p' ⋙ Over.forget U)] (A : Over U) :
    IsGroupoid (p'.Fiber A) where
  all_isIso := fiber_hom_isIso_of_comp_over_forget p' A

/-- Lemma 4.35.13: if a functor `p' : S ⥤ Over U` becomes fibred in groupoids after composing with
the forgetful functor `Over.forget U : Over U ⥤ C`, then `p'` is itself fibred in groupoids over
`Over U`. Equivalently, if a category fibred in groupoids over `C` factors through the slice
category `C/U`, then the induced functor to `C/U` is fibred in groupoids. -/
theorem isFibredInGroupoids_of_comp_over_forget {U : C} (p' : S ⥤ Over U)
    [IsFibredInGroupoids (p' ⋙ Over.forget U)] :
    IsFibredInGroupoids p' := by
  -- Route correction: follow the textbook proof through fiberedness plus groupoid fibers.
  have hp : p'.IsFibered := isFibered_of_comp_over_forget p'
  -- Each slice fiber inherits its groupoid structure from the corresponding underlying fiber.
  have hfiber : ∀ A : Over U, IsGroupoid (p'.Fiber A) := fun A ↦ by infer_instance
  -- Lemma 4.35.2 packages these two ingredients into the desired fibred-in-groupoids structure.
  exact CategoryTheory.isFibredInGroupoids_of_isFibered_and_fiber_groupoid p' hp hfiber

instance {U : C} (p' : S ⥤ Over U) [IsFibredInGroupoids (p' ⋙ Over.forget U)] :
    IsFibredInGroupoids p' :=
  isFibredInGroupoids_of_comp_over_forget p'

end CategoryTheory.Functor

/-! ### Lemma_4_35_14 (from Chap04) -/
universe uA uB uC vA vB vC

namespace CategoryTheory.Functor

open CategoryTheory.IsHomLift

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]

/- Domain-style sampling for Lemma 4.35.14:
- primary domain: fibered categories in groupoids and stability under functor composition;
- inspected owner-level declarations:
  `CategoryTheory.IsFibredInGroupoids`,
  `Functor.isFibered_comp`,
  `CategoryTheory.isFibredInGroupoids_of_isFibered_and_fiber_groupoid`,
  `Functor.IsStronglyCartesian.isIso_of_base_isIso`;
- best owner abstraction: the source-facing notion remains `IsFibredInGroupoids`, and the proof
  should pass through the fiberwise criterion of Lemma 4.35.2 rather than a direct composition
  argument for strongly cartesian morphisms;
- primitive data: the two input `IsFibredInGroupoids` instances on `F` and `G`;
- derived API: the induced `IsFibredInGroupoids` instance on the composite functor `F ⋙ G`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting that a composite of functors fibred in groupoids is
  again fibred in groupoids;
- `core/canonical`: `Functor.IsFibered`, `Functor.IsStronglyCartesian`, `Functor.Fiber`;
- `bridge/view`: the helper lemmas below, which implement the textbook sentence that a morphism in
  a composite fiber maps to an isomorphism in the intermediate fiber. -/

/-- Helper for Lemma 4.35.14: a morphism in the fiber of `F ⋙ G` over `U` maps under `F` to a
morphism in the fiber of `G` over `U`. -/
private theorem mapped_hom_in_target_fiber
    (F : A ⥤ B) (G : B ⥤ C)
    [IsFibredInGroupoids F] [IsFibredInGroupoids G]
    (U : C) {X Y : (F ⋙ G).Fiber U} (φ : X ⟶ Y) :
    G.IsHomLift (𝟙 U) (F.map φ.1) := by
  letI : (F ⋙ G).IsHomLift (𝟙 U) φ.1 := φ.2
  -- The underlying morphism of `φ` already lies over `𝟙 U` for the composite functor.
  -- Rewriting that lift equation for `F ⋙ G` exposes the needed lift condition for `G`.
  refine IsHomLift.of_fac' G (𝟙 U) (F.map φ.1) X.2 Y.2 ?_
  simpa [Functor.comp_map] using IsHomLift.fac' (p := F ⋙ G) (𝟙 U) φ.1

/-- Helper for Lemma 4.35.14: the underlying morphism of a morphism in the composite fiber is an
isomorphism in `A`. -/
private theorem composite_fiber_underlying_hom_isIso
    (F : A ⥤ B) (G : B ⥤ C)
    [IsFibredInGroupoids F] [IsFibredInGroupoids G]
    (U : C) {X Y : (F ⋙ G).Fiber U} (φ : X ⟶ Y) :
    IsIso φ.1 := by
  letI : G.IsHomLift (𝟙 U) (F.map φ.1) := mapped_hom_in_target_fiber F G U φ
  -- Inside the fiber `G_U`, every morphism is invertible because `G` is fibred in groupoids.
  haveI : IsIso (Functor.Fiber.homMk G U (F.map φ.1)) :=
    CategoryTheory.IsFibredInGroupoids.hom_isIso (p := G) U
      (Functor.Fiber.homMk G U (F.map φ.1))
  haveI : IsIso (F.map φ.1) := by
    simpa using
      (inferInstance :
        IsIso
          ((Functor.Fiber.fiberInclusion : G.Fiber U ⥤ B).map
            (Functor.Fiber.homMk G U (F.map φ.1))))
  -- The morphism `φ.1` is strongly cartesian for `F`, so Lemma 4.33.2 upgrades the base
  -- isomorphism `F.map φ.1` to an isomorphism upstairs in `A`.
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso F (F.map φ.1) φ.1

/-- Helper for Lemma 4.35.14: a morphism in the fiber of `F ⋙ G` over `U` is an isomorphism in the
fiber category itself. -/
private theorem composite_fiber_hom_isIso
    (F : A ⥤ B) (G : B ⥤ C)
    [IsFibredInGroupoids F] [IsFibredInGroupoids G]
    (U : C) {X Y : (F ⋙ G).Fiber U} (φ : X ⟶ Y) :
    IsIso φ := by
  letI : (F ⋙ G).IsHomLift (𝟙 U) φ.1 := φ.2
  haveI : IsIso φ.1 := composite_fiber_underlying_hom_isIso F G U φ
  let e := asIso φ.1
  -- The inverse of the ambient vertical isomorphism still lies over `𝟙 U`, so it defines the
  -- inverse morphism in the composite fiber.
  refine ⟨⟨⟨e.inv, ?_⟩, ?_, ?_⟩⟩
  · simpa [e] using IsHomLift.lift_id_inv_isIso (p := F ⋙ G) U φ.1
  · apply Functor.Fiber.hom_ext
    change φ.1 ≫ e.inv = 𝟙 X.1
    simp [e]
  · apply Functor.Fiber.hom_ext
    change e.inv ≫ φ.1 = 𝟙 Y.1
    simp [e]

/-- Helper for Lemma 4.35.14: every standard fiber of the composite functor `F ⋙ G` is a
groupoid. -/
private theorem composite_fiber_isGroupoid
    (F : A ⥤ B) (G : B ⥤ C)
    [IsFibredInGroupoids F] [IsFibredInGroupoids G]
    (U : C) :
    IsGroupoid ((F ⋙ G).Fiber U) := by
  -- Each morphism in the composite fiber is invertible by the previous helper.
  exact
    { all_isIso := fun φ ↦ composite_fiber_hom_isIso F G U φ }

-- Proof sketch: use Lemma 4.33.12 to obtain that `F ⋙ G` is fibred, then apply the criterion of
-- Lemma 4.35.2. A morphism in the composite fiber over `U` maps to a morphism in `G.Fiber U`,
-- hence is invertible there because `G` is fibred in groupoids. Since every morphism in `A` is
-- strongly cartesian for `F`, Lemma 4.33.2 upgrades that base isomorphism to an isomorphism in
-- `A`, and therefore the composite fiber is a groupoid.
/-- Lemma 4.35.14: if `F : A ⥤ B` is fibred in groupoids over `B` and `G : B ⥤ C` is fibred in
groupoids over `C`, then the composite functor `F ⋙ G : A ⥤ C` is fibred in groupoids over
`C`. -/
instance isFibredInGroupoids_comp
    (F : A ⥤ B) (G : B ⥤ C)
    [IsFibredInGroupoids F] [IsFibredInGroupoids G] :
    IsFibredInGroupoids (F ⋙ G) := by
  -- Route correction: follow the source proof through Lemma 4.35.2 instead of the direct
  -- strongly-cartesian composition argument.
  have hFibered : (F ⋙ G).IsFibered := inferInstance
  -- The fiberwise groupoid condition comes from the intermediate fiber `G_U` and Lemma 4.33.2.
  have hFiberGroupoid : ∀ U : C, IsGroupoid ((F ⋙ G).Fiber U) :=
    fun U ↦ composite_fiber_isGroupoid F G U
  -- Lemma 4.35.2 packages fiberedness plus groupoid fibers into the desired structure.
  exact
    CategoryTheory.isFibredInGroupoids_of_isFibered_and_fiber_groupoid
      (F ⋙ G) hFibered hFiberGroupoid

end CategoryTheory.Functor

/-! ### Lemma_4_35_15 (from Chap04) -/
open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

section

variable {C : Type u₁} [Category.{v₁} C]
variable {E : Type u₂} [Category.{v₂} E]

/- Domain-style sampling for Lemma 4.35.15:
- primary domain: fibred categories in groupoids and pullbacks in the total category;
- inspected owner-level declarations:
  `CategoryTheory.IsFibredInGroupoids`,
  `Functor.hasPullback_of_isStronglyCartesian`,
  `Functor.IsStronglyCartesian`,
  `Functor.IsPreFibered.pullbackMap`;
- best owner abstraction: `Functor.hasPullback_of_isStronglyCartesian`, which is the canonical
  pullback-existence theorem upstairs. The current file should stay only a source-facing
  specialization that discharges the strong-cartesianness hypothesis using
  `IsFibredInGroupoids.isStronglyCartesian_map`.
- primitive data: the functor `p`, the total-category morphisms `φ` and `ψ`, and the base
  pullback hypothesis on `p.map φ` and `p.map ψ`;
- derived API: the induced `HasPullback φ ψ` instance.

Source/core/bridge triage:
- `source-facing`: `hasPullback_of_isFibredInGroupoids`;
- `core/canonical`: `Functor.hasPullback_of_isStronglyCartesian`;
- `bridge/view`: the instance field `IsFibredInGroupoids.isStronglyCartesian_map`, which upgrades
  the source hypothesis to the canonical owner hypothesis. -/
-- Proof sketch: in a category fibred in groupoids, every morphism is strongly cartesian over its image in the base. The canonical owner theorem `hasPullback_of_isStronglyCartesian` then applies directly to `φ`.
/-- Lemma 4.35.15: if `p : E ⥤ C` is fibred in groupoids and the pullback of `p.map φ` and `p.map ψ` exists in the base, then `φ` and `ψ` admit a pullback in the total category. -/
theorem hasPullback_of_isFibredInGroupoids
    (p : E ⥤ C) [IsFibredInGroupoids p]
    {x y z : E} (φ : x ⟶ y) (ψ : z ⟶ y)
    [HasPullback (p.map φ) (p.map ψ)] :
    HasPullback φ ψ :=
  hasPullback_of_isStronglyCartesian p φ ψ

end

end CategoryTheory.Functor
