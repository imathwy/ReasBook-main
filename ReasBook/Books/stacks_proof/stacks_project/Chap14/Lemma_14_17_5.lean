import stacks_proof.stacks_project.Chap14.Lemma_14_13_3
import stacks_proof.stacks_project.Chap14.Lemma_14_17_4
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 14.17.5:
- primary domain: internal simplicial mapping objects and their contravariance in the source
  simplicial set, compared against pushouts and pullbacks in the functor category
  `SimplicialObject C`;
- sampled owner-style declarations:
  `simplicialHomPresheaf`,
  `simplicialHom`,
  `Functor.RepresentableBy.comp_homEquiv_symm`,
  `PullbackCone.IsLimit.equivPullbackObj`;
- best owner abstraction:
  the source-facing object `simplicialHom (pushout a b) T`, compared to the canonical pullback
  object of the precomposition maps
  `simplicial_hom_precomp a T` and `simplicial_hom_precomp b T`;
- primitive data:
  the precomposition morphisms on internal hom objects induced by simplicial-set maps;
- auxiliary existence route:
  under the chapter finiteness and eventual-degeneracy hypotheses, the required pushout-specific
  degreewise finiteness, `0`-simplex, and eventual-degeneracy facts are supplied below, while the
  owner-level coproduct and representability APIs are reused from earlier chapter files;
- derived API:
  the pushout closure bridge to
  `(simplicialHomPresheaf (pushout a b) T).IsRepresentable`, the pullback comparison morphism
  `simplicial_hom_pushout_to_pullback`, its `IsIso` theorem, and the companion hom-set bijection
  obtained by evaluating that pullback comparison at a test simplicial object.

Source/core/bridge triage:
- `source-facing`: `simplicialHom (pushout a b) T`, expressing that the internal hom out of a
  pushout is the expected mapping object from the source text;
- `core/canonical`: the pullback object
  `pullback (simplicial_hom_precomp a T) (simplicial_hom_precomp b T)` in `SimplicialObject C`;
- `bridge/view`: the explicit hom-set map into `Types.PullbackObj` for a test object `X`. -/

/-- Degreewise finiteness of the target legs induces degreewise finiteness of the simplicial
pushout. This is the source-facing finiteness bridge needed to apply Lemma `14.17.4` to
`pushout a b`. -/
instance degreewiseFinite_pushout
    {U V W : SSet.{w}}
    [∀ Δ : SimplexCategoryᵒᵖ, Finite (V.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, Finite (W.obj Δ)]
    (a : U ⟶ V) (b : U ⟶ W) :
    ∀ Δ : SimplexCategoryᵒᵖ, Finite ((pushout a b).obj Δ) := by
  intro Δ
  let e₁ := pushoutObjIso a b Δ
  let e₂ : pushout (a.app Δ) (b.app Δ) ≅ Types.Pushout (a.app Δ) (b.app Δ) :=
    IsColimit.coconePointUniqueUpToIso (pushout.isColimit (a.app Δ) (b.app Δ))
      (Types.Pushout.isColimitCocone (a.app Δ) (b.app Δ))
  letI : Finite (Types.Pushout (a.app Δ) (b.app Δ)) := by
    change Finite (Quot (Types.Pushout.Rel (a.app Δ) (b.app Δ)))
    infer_instance
  exact Finite.of_equiv (Types.Pushout (a.app Δ) (b.app Δ)) ((e₁ ≪≫ e₂).symm.toEquiv)

/-- A `0`-simplex in the left target leg induces a `0`-simplex in the simplicial pushout. This is
the source-facing nonemptiness bridge needed to apply Lemma `14.17.4` to `pushout a b`. -/
instance pushout_objZero_nonempty
    {U V W : SSet.{w}}
    [Nonempty (V _⦋0⦌)]
    (a : U ⟶ V) (b : U ⟶ W) :
    Nonempty ((pushout a b) _⦋0⦌) := by
  let e₁ := pushoutObjIso a b (op ⦋0⦌)
  let e₂ : pushout (a.app (op ⦋0⦌)) (b.app (op ⦋0⦌)) ≅
      Types.Pushout (a.app (op ⦋0⦌)) (b.app (op ⦋0⦌)) :=
    IsColimit.coconePointUniqueUpToIso (pushout.isColimit (a.app (op ⦋0⦌)) (b.app (op ⦋0⦌)))
      (Types.Pushout.isColimitCocone _ _)
  exact ⟨(e₁ ≪≫ e₂).inv (Types.Pushout.inl _ _ (Classical.choice inferInstance))⟩

/-- Helper for Lemma 14.17.5: the degree-`Δ` term of the simplicial pushout is canonically
identified with the type-theoretic pushout of the degreewise span. -/
private noncomputable def simplicial_pushout_eval_typesPushoutIso
    {U V W : SSet.{w}} (a : U ⟶ V) (b : U ⟶ W) (Δ : SimplexCategoryᵒᵖ) :
    (pushout a b).obj Δ ≅ Types.Pushout (a.app Δ) (b.app Δ) :=
  pushoutObjIso a b Δ ≪≫
    IsColimit.coconePointUniqueUpToIso
      (pushout.isColimit (a.app Δ) (b.app Δ))
      (Types.Pushout.isColimitCocone (a.app Δ) (b.app Δ))

/-- Helper for Lemma 14.17.5: the inverse of the degreewise pushout-to-`Types.Pushout`
isomorphism recovers the simplicial `V`-leg on representatives. -/
private theorem simplicial_pushout_eval_typesPushoutIso_inv_comp_inl
    {U V W : SSet.{w}} (a : U ⟶ V) (b : U ⟶ W) (Δ : SimplexCategoryᵒᵖ) :
    Types.Pushout.inl (a.app Δ) (b.app Δ) ≫
        (simplicial_pushout_eval_typesPushoutIso a b Δ).inv =
      (pushout.inl a b).app Δ := by
  let e₁ : (pushout a b).obj Δ ≅ pushout (a.app Δ) (b.app Δ) := pushoutObjIso a b Δ
  let e₂ : pushout (a.app Δ) (b.app Δ) ≅ Types.Pushout (a.app Δ) (b.app Δ) :=
    IsColimit.coconePointUniqueUpToIso
      (pushout.isColimit (a.app Δ) (b.app Δ))
      (Types.Pushout.isColimitCocone (a.app Δ) (b.app Δ))
  have he₂ :
      Types.Pushout.inl (a.app Δ) (b.app Δ) ≫ e₂.inv =
        pushout.inl (a.app Δ) (b.app Δ) := by
    simpa using
      IsColimit.comp_coconePointUniqueUpToIso_inv
        (pushout.isColimit (a.app Δ) (b.app Δ))
        (Types.Pushout.isColimitCocone (a.app Δ) (b.app Δ))
        WalkingSpan.left
  have he₁ :
      pushout.inl (a.app Δ) (b.app Δ) ≫ e₁.inv =
        (pushout.inl a b).app Δ := by
    simpa [e₁] using PreservesPushout.inl_iso_hom ((evaluation _ _).obj Δ) a b
  -- Proof comment: the comparison to `Types.Pushout` is the composite of the evaluation pushout
  -- comparison with the universal type-level pushout comparison, so the left leg is recovered by
  -- composing the two standard `inl` computation rules.
  calc
    Types.Pushout.inl (a.app Δ) (b.app Δ) ≫
        (simplicial_pushout_eval_typesPushoutIso a b Δ).inv =
      Types.Pushout.inl (a.app Δ) (b.app Δ) ≫ e₂.inv ≫ e₁.inv := by
        rfl
    _ = pushout.inl (a.app Δ) (b.app Δ) ≫ e₁.inv := by
          simpa [Category.assoc] using congrArg (fun k ↦ k ≫ e₁.inv) he₂
    _ = (pushout.inl a b).app Δ := he₁

/-- Helper for Lemma 14.17.5: the inverse of the degreewise pushout-to-`Types.Pushout`
isomorphism recovers the simplicial `W`-leg on representatives. -/
private theorem simplicial_pushout_eval_typesPushoutIso_inv_comp_inr
    {U V W : SSet.{w}} (a : U ⟶ V) (b : U ⟶ W) (Δ : SimplexCategoryᵒᵖ) :
    Types.Pushout.inr (a.app Δ) (b.app Δ) ≫
        (simplicial_pushout_eval_typesPushoutIso a b Δ).inv =
      (pushout.inr a b).app Δ := by
  let e₁ : (pushout a b).obj Δ ≅ pushout (a.app Δ) (b.app Δ) := pushoutObjIso a b Δ
  let e₂ : pushout (a.app Δ) (b.app Δ) ≅ Types.Pushout (a.app Δ) (b.app Δ) :=
    IsColimit.coconePointUniqueUpToIso
      (pushout.isColimit (a.app Δ) (b.app Δ))
      (Types.Pushout.isColimitCocone (a.app Δ) (b.app Δ))
  have he₂ :
      Types.Pushout.inr (a.app Δ) (b.app Δ) ≫ e₂.inv =
        pushout.inr (a.app Δ) (b.app Δ) := by
    simpa using
      IsColimit.comp_coconePointUniqueUpToIso_inv
        (pushout.isColimit (a.app Δ) (b.app Δ))
        (Types.Pushout.isColimitCocone (a.app Δ) (b.app Δ))
        WalkingSpan.right
  have he₁ :
      pushout.inr (a.app Δ) (b.app Δ) ≫ e₁.inv =
        (pushout.inr a b).app Δ := by
    simpa [e₁] using PreservesPushout.inr_iso_hom ((evaluation _ _).obj Δ) a b
  -- Proof comment: this is the symmetric `inr` computation through the two standard pushout
  -- comparison isomorphisms.
  calc
    Types.Pushout.inr (a.app Δ) (b.app Δ) ≫
        (simplicial_pushout_eval_typesPushoutIso a b Δ).inv =
      Types.Pushout.inr (a.app Δ) (b.app Δ) ≫ e₂.inv ≫ e₁.inv := by
        rfl
    _ = pushout.inr (a.app Δ) (b.app Δ) ≫ e₁.inv := by
          simpa [Category.assoc] using congrArg (fun k ↦ k ≫ e₁.inv) he₂
    _ = (pushout.inr a b).app Δ := he₁

/-- Helper for Lemma 14.17.5: degeneracy is preserved when a degenerate `V`-simplex is mapped
into the simplicial pushout through the left coprojection. -/
private theorem simplicial_pushout_inl_mem_degenerate
    {U V W : SSet.{w}} (a : U ⟶ V) (b : U ⟶ W) {n : ℕ}
    {x : V _⦋n⦌} (hx : x ∈ V.degenerate n) :
    (pushout.inl a b).app (op ⦋n⦌) x ∈ (pushout a b).degenerate n := by
  rw [SSet.mem_degenerate_iff] at hx ⊢
  rcases hx with ⟨m, hm, f, hf, y, rfl⟩
  refine ⟨m, hm, f, hf, ?_⟩
  refine Set.mem_range.2 ⟨(pushout.inl a b).app (op ⦋m⦌) y, ?_⟩
  -- Proof comment: naturality of the coprojection moves the simplicial reindexing map past the
  -- pushout inclusion, so the same degeneracy witness survives in the pushout.
  simpa using (congrFun ((pushout.inl a b).naturality f.op) y).symm

/-- Helper for Lemma 14.17.5: degeneracy is preserved when a degenerate `W`-simplex is mapped
into the simplicial pushout through the right coprojection. -/
private theorem simplicial_pushout_inr_mem_degenerate
    {U V W : SSet.{w}} (a : U ⟶ V) (b : U ⟶ W) {n : ℕ}
    {x : W _⦋n⦌} (hx : x ∈ W.degenerate n) :
    (pushout.inr a b).app (op ⦋n⦌) x ∈ (pushout a b).degenerate n := by
  rw [SSet.mem_degenerate_iff] at hx ⊢
  rcases hx with ⟨m, hm, f, hf, y, rfl⟩
  refine ⟨m, hm, f, hf, ?_⟩
  refine Set.mem_range.2 ⟨(pushout.inr a b).app (op ⦋m⦌) y, ?_⟩
  -- Proof comment: the right coprojection satisfies the same naturality argument as the left
  -- coprojection, so the degeneracy witness transports unchanged.
  simpa using (congrFun ((pushout.inr a b).naturality f.op) y).symm

/-- Eventual degeneracy is preserved by pushouts of simplicial sets once both target legs are
eventually degenerate. -/
theorem simplicialSetEventuallyDegenerate_pushout
    {U V W : SSet.{w}}
    (hV : ∃ d : ℕ, V.HasDimensionLE d)
    (hW : ∃ d : ℕ, W.HasDimensionLE d)
    (a : U ⟶ V) (b : U ⟶ W) :
    ∃ d : ℕ, (pushout a b).HasDimensionLE d := by
  rcases hV with ⟨dV, hdV⟩
  rcases hW with ⟨dW, hdW⟩
  letI : V.HasDimensionLT (dV + 1) := hdV
  letI : W.HasDimensionLT (dW + 1) := hdW
  refine ⟨max dV dW, ?_⟩
  change (pushout a b).HasDimensionLT (max dV dW + 1)
  refine SSet.HasDimensionLT.mk ?_
  intro n hn
  change (pushout a b).degenerate n = Set.univ
  rw [Set.eq_univ_iff_forall]
  intro x
  let e := simplicial_pushout_eval_typesPushoutIso a b (op ⦋n⦌)
  have hx_transport : e.inv (e.hom x) = x := by
    simpa using congrFun e.inv_hom_id x
  have hx_deg : e.inv (e.hom x) ∈ (pushout a b).degenerate n := by
    refine Quot.inductionOn (e.hom x) ?_
    intro z
    cases z with
    | inl v =>
        have hv_top : V.degenerate n = ⊤ := by
          rw [V.degenerate_eq_top_of_hasDimensionLT (dV + 1) n]
          exact le_trans (Nat.succ_le_succ (le_max_left dV dW)) hn
        have hv_deg : v ∈ V.degenerate n := by
          rw [hv_top]
          exact Set.mem_univ v
        change e.inv (Types.Pushout.inl (a.app (op ⦋n⦌)) (b.app (op ⦋n⦌)) v) ∈
          (pushout a b).degenerate n
        rw [show e.inv (Types.Pushout.inl (a.app (op ⦋n⦌)) (b.app (op ⦋n⦌)) v) =
            (pushout.inl a b).app (op ⦋n⦌) v by
              simpa [e] using
                congrFun (simplicial_pushout_eval_typesPushoutIso_inv_comp_inl a b (op ⦋n⦌)) v]
        exact simplicial_pushout_inl_mem_degenerate a b hv_deg
    | inr w =>
        have hw_top : W.degenerate n = ⊤ := by
          rw [W.degenerate_eq_top_of_hasDimensionLT (dW + 1) n]
          exact le_trans (Nat.succ_le_succ (le_max_right dV dW)) hn
        have hw_deg : w ∈ W.degenerate n := by
          rw [hw_top]
          exact Set.mem_univ w
        change e.inv (Types.Pushout.inr (a.app (op ⦋n⦌)) (b.app (op ⦋n⦌)) w) ∈
          (pushout a b).degenerate n
        rw [show e.inv (Types.Pushout.inr (a.app (op ⦋n⦌)) (b.app (op ⦋n⦌)) w) =
            (pushout.inr a b).app (op ⦋n⦌) w by
              simpa [e] using
                congrFun (simplicial_pushout_eval_typesPushoutIso_inv_comp_inr a b (op ⦋n⦌)) w]
        exact simplicial_pushout_inr_mem_degenerate a b hw_deg
  exact hx_transport ▸ hx_deg

/-- Under the chapter finiteness and eventual-degeneracy hypotheses on the two target legs, plus a
`0`-simplex in the left target leg, Lemma `14.17.4` applies to the simplicial pushout. This is the
public source-facing bridge from the hypotheses in the statement of Lemma `14.17.5` to the
owner-level internal-hom representability hypothesis on `pushout a b`. -/
theorem simplicialHomPresheaf_pushout_isRepresentable_of_eventually_degenerate
    [HasBinaryCoproducts C] [HasFiniteLimits C]
    {U V W : SSet.{w}}
    [∀ Δ : SimplexCategoryᵒᵖ, Finite (V.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, Finite (W.obj Δ)]
    [Nonempty (V _⦋0⦌)]
    (hV : ∃ d : ℕ, V.HasDimensionLE d)
    (hW : ∃ d : ℕ, W.HasDimensionLE d)
    (a : U ⟶ V) (b : U ⟶ W)
    (T : SimplicialObject C) :
    (simplicialHomPresheaf (pushout a b) T).IsRepresentable := by
  let _ := degreewiseFinite_pushout a b
  let _ := pushout_objZero_nonempty a b
  exact simplicialHomPresheaf_isRepresentable_of_eventually_degenerate (pushout a b) T
    (simplicialSetEventuallyDegenerate_pushout hV hW a b)

instance simplicialHomPresheaf_pushout_isRepresentable_of_fact_eventually_degenerate
    [HasBinaryCoproducts C] [HasFiniteLimits C]
    {U V W : SSet.{w}}
    [∀ Δ : SimplexCategoryᵒᵖ, Finite (V.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, Finite (W.obj Δ)]
    [Nonempty (V _⦋0⦌)]
    [Fact (∃ d : ℕ, V.HasDimensionLE d)]
    [Fact (∃ d : ℕ, W.HasDimensionLE d)]
    (a : U ⟶ V) (b : U ⟶ W)
    (T : SimplicialObject C) :
    (simplicialHomPresheaf (pushout a b) T).IsRepresentable :=
  simplicialHomPresheaf_pushout_isRepresentable_of_eventually_degenerate
    (Fact.out : ∃ d : ℕ, V.HasDimensionLE d)
    (Fact.out : ∃ d : ℕ, W.HasDimensionLE d) a b T

section Precomp

variable {U V : SSet.{w}} (a : U ⟶ V) (T : SimplicialObject C)
variable
    [∀ X : SimplicialObject C, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : U.obj Δ ↦ X.obj Δ)]
    [∀ X : SimplicialObject C, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : V.obj Δ ↦ X.obj Δ)]
    [Functor.IsRepresentable (simplicialHomPresheaf U T)]
    [Functor.IsRepresentable (simplicialHomPresheaf V T)]

/-- Precomposition by a simplicial-set morphism induces the corresponding morphism of internal
simplicial mapping objects. This is the minimal bridge from the owner-level representing
equivalences to the source-facing precomposition map. -/
def simplicial_hom_precomp : simplicialHom V T ⟶ simplicialHom U T :=
  let eU :
      (simplicialHom V T ⟶ simplicialHom U T) ≃
        (U × simplicialHom V T ⟶ T) :=
    (simplicialHomPresheaf U T).representableBy.homEquiv
  let eV :
      (simplicialHom V T ⟶ simplicialHom V T) ≃
        (V × simplicialHom V T ⟶ T) :=
    (simplicialHomPresheaf V T).representableBy.homEquiv
  eU.symm (simplicialCopowerIndexHom (simplicialHom V T) a ≫ eV (𝟙 _))

-- Proof sketch: unfold `simplicial_hom_precomp`, then apply the canonical naturality lemma
-- `Functor.RepresentableBy.comp_homEquiv_symm` for the owner equivalence
-- `(simplicialHomPresheaf U T).representableBy.homEquiv`.
/-- Under the representing equivalence, composition with `simplicial_hom_precomp` is
precomposition on the coproduct-indexed source simplicial set. -/
theorem simplicial_hom_homEquiv_precomp
    (X : SimplicialObject C) (f : X ⟶ simplicialHom V T) :
    (simplicialHomPresheaf U T).representableBy.homEquiv (f ≫ simplicial_hom_precomp a T) =
      simplicialCopowerIndexHom X a ≫
        (simplicialHomPresheaf V T).representableBy.homEquiv f := by
  -- Route correction: prove the owner naturality first before any pushout transport, so later
  -- pullback comparisons reduce to this explicit coproduct reindexing square.
  let eV :
      (simplicialHom V T ⟶ simplicialHom V T) ≃
        (V × simplicialHom V T ⟶ T) :=
    (simplicialHomPresheaf V T).representableBy.homEquiv
  -- First translate composition with `simplicial_hom_precomp` through the representing
  -- equivalence for `Hom(U, T)`.
  have hcomp :
      (simplicialHomPresheaf U T).representableBy.homEquiv (f ≫ simplicial_hom_precomp a T) =
        (simplicialHomPresheaf U T).map f.op
          ((simplicialHomPresheaf U T).representableBy.homEquiv
            (simplicial_hom_precomp a T)) := by
    simpa using
      ((simplicialHomPresheaf U T).representableBy.homEquiv_comp
        f (simplicial_hom_precomp a T))
  -- Next expand the defining source-side map for `simplicial_hom_precomp`.
  have hprecomp :
      (simplicialHomPresheaf U T).representableBy.homEquiv (simplicial_hom_precomp a T) =
        simplicialCopowerIndexHom (simplicialHom V T) a ≫ eV (𝟙 _) := by
    -- This is exactly how `simplicial_hom_precomp` was defined.
    change
      (simplicialHomPresheaf U T).representableBy.homEquiv
          ((simplicialHomPresheaf U T).representableBy.homEquiv.symm
            (simplicialCopowerIndexHom (simplicialHom V T) a ≫
              (simplicialHomPresheaf V T).representableBy.homEquiv (𝟙 (simplicialHom V T)))) =
        simplicialCopowerIndexHom (simplicialHom V T) a ≫ eV (𝟙 _)
    exact Equiv.apply_symm_apply _ _
  -- Finally identify the right-hand side by the coproduct reindexing naturality square.
  have hV :
      (simplicialHomPresheaf V T).representableBy.homEquiv f =
        simplicialCopowerHom V f ≫ eV (𝟙 _) := by
    -- The representing equivalence on `Hom(V, T)` sends `f` to the source-side coproduct map
    -- followed by the universal element.
    simpa [eV] using
      ((simplicialHomPresheaf V T).representableBy.homEquiv_comp
        f (𝟙 (simplicialHom V T)))
  calc
    (simplicialHomPresheaf U T).representableBy.homEquiv (f ≫ simplicial_hom_precomp a T)
        = (simplicialHomPresheaf U T).map f.op
            ((simplicialHomPresheaf U T).representableBy.homEquiv
              (simplicial_hom_precomp a T)) := hcomp
    _ = (simplicialHomPresheaf U T).map f.op
          (simplicialCopowerIndexHom (simplicialHom V T) a ≫ eV (𝟙 _)) := by
            exact congrArg ((simplicialHomPresheaf U T).map f.op) hprecomp
    _ = simplicialCopowerHom U f ≫ simplicialCopowerIndexHom (simplicialHom V T) a ≫ eV (𝟙 _) := by
          rfl
    _ = simplicialCopowerIndexHom X a ≫ simplicialCopowerHom V f ≫ eV (𝟙 _) := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ k ≫ eV (𝟙 _))
              ((simplicialCopowerIndexHom_naturality (X := X) (Y := simplicialHom V T) a f).w)
    _ = simplicialCopowerIndexHom X a ≫ (simplicialHomPresheaf V T).representableBy.homEquiv f := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ simplicialCopowerIndexHom X a ≫ k) hV.symm

end Precomp

section PushoutComparison

variable {U V W : SSet.{w}} (a : U ⟶ V) (b : U ⟶ W) (T : SimplicialObject C)
variable
    [∀ X : SimplicialObject C, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : U.obj Δ ↦ X.obj Δ)]
    [∀ X : SimplicialObject C, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : V.obj Δ ↦ X.obj Δ)]
    [∀ X : SimplicialObject C, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : W.obj Δ ↦ X.obj Δ)]
    [∀ X : SimplicialObject C, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : (pushout a b).obj Δ ↦ X.obj Δ)]
    [Functor.IsRepresentable (simplicialHomPresheaf U T)]
    [Functor.IsRepresentable (simplicialHomPresheaf V T)]
    [Functor.IsRepresentable (simplicialHomPresheaf W T)]
    [Functor.IsRepresentable (simplicialHomPresheaf (pushout a b) T)]

-- Proof sketch: both composites are induced by precomposition along the two maps
-- `U ⟶ pushout a b` obtained from the pushout cocone, and these agree because
-- `pushout.condition a b` gives the commutative square in the simplicial-set variable.
/-- Precomposition along the two structure maps of the simplicial pushout forms the canonical
commutative square over the two precomposition morphisms to `Hom(U, T)`. -/
theorem simplicial_hom_precomp_pushout_condition
    :
    CommSq
      (simplicial_hom_precomp (pushout.inl a b) T)
      (simplicial_hom_precomp (pushout.inr a b) T)
      (simplicial_hom_precomp a T)
      (simplicial_hom_precomp b T) := by
  let eU := (simplicialHomPresheaf U T).representableBy
  let ePushout := (simplicialHomPresheaf (pushout a b) T).representableBy
  refine ⟨?_⟩
  apply eU.homEquiv.injective
  -- Proof comment: after translating both composites through the representing equivalence for
  -- `Hom(U, T)`, they become the same source-side reindexing map because
  -- `a ≫ pushout.inl a b = b ≫ pushout.inr a b`.
  rw [simplicial_hom_homEquiv_precomp (a := a) (T := T)
    (X := simplicialHom (pushout a b) T)
    (f := simplicial_hom_precomp (pushout.inl a b) T)]
  rw [simplicial_hom_homEquiv_precomp (a := b) (T := T)
    (X := simplicialHom (pushout a b) T)
    (f := simplicial_hom_precomp (pushout.inr a b) T)]
  have hInl :
      (simplicialHomPresheaf V T).representableBy.homEquiv
          (simplicial_hom_precomp (pushout.inl a b) T) =
        simplicialCopowerIndexHom (simplicialHom (pushout a b) T) (pushout.inl a b) ≫
          ePushout.homEquiv (𝟙 _) := by
    simpa using
      (simplicial_hom_homEquiv_precomp (a := pushout.inl a b) (T := T)
        (X := simplicialHom (pushout a b) T) (f := 𝟙 _))
  have hInr :
      (simplicialHomPresheaf W T).representableBy.homEquiv
          (simplicial_hom_precomp (pushout.inr a b) T) =
        simplicialCopowerIndexHom (simplicialHom (pushout a b) T) (pushout.inr a b) ≫
          ePushout.homEquiv (𝟙 _) := by
    simpa using
      (simplicial_hom_homEquiv_precomp (a := pushout.inr a b) (T := T)
        (X := simplicialHom (pushout a b) T) (f := 𝟙 _))
  rw [hInl, hInr]
  rw [← Category.assoc, ← Category.assoc]
  rw [← simplicialCopowerIndexHom_comp (X := simplicialHom (pushout a b) T) a (pushout.inl a b)]
  rw [← simplicialCopowerIndexHom_comp (X := simplicialHom (pushout a b) T) b (pushout.inr a b)]
  simpa using congrArg
    (fun k ↦ simplicialCopowerIndexHom (simplicialHom (pushout a b) T) k ≫
      ePushout.homEquiv (𝟙 _))
    (pushout.condition (f := a) (g := b))

variable [HasPullback (simplicial_hom_precomp a T) (simplicial_hom_precomp b T)]

/-- Helper for Lemma 14.17.5: the fixed-`X` simplicial copower square over the span `a, b` is the
explicit cocone whose apex is `(pushout a b) × X`. -/
private noncomputable def simplicial_copower_pushout_cocone_aux
    (X : SimplicialObject C) :
    PushoutCocone (simplicialCopowerIndexHom X a) (simplicialCopowerIndexHom X b) :=
  PushoutCocone.mk
    (simplicialCopowerIndexHom X (pushout.inl a b))
    (simplicialCopowerIndexHom X (pushout.inr a b))
    (by
      -- Proof comment: reindexing by the two pushout coprojections agrees after precomposing by
      -- `a` and `b` because `a ≫ pushout.inl = b ≫ pushout.inr`.
      rw [← simplicialCopowerIndexHom_comp (X := X) a (pushout.inl a b)]
      rw [← simplicialCopowerIndexHom_comp (X := X) b (pushout.inr a b)]
      simpa using congrArg (simplicialCopowerIndexHom X) (pushout.condition (f := a) (g := b)))

/-- Helper for Lemma 14.17.5: evaluating the simplicial pushout of `a` and `b` at a simplex
produces a colimiting pushout cocone in `Type`. -/
private noncomputable def simplicial_pushout_eval_isColimit
    (Δ : SimplexCategoryᵒᵖ) :
    IsColimit
      (((evaluation _ _).obj Δ).mapCocone (pushout.cocone a b)) :=
  by
    letI : PreservesColimit (span a b) ((evaluation _ _).obj Δ) := by
      infer_instance
    -- Proof comment: the simplicial pushout is already a colimit cocone in the functor category,
    -- and evaluation preserves that colimit, so the degreewise cocone is the desired pushout.
    simpa using
      (Limits.isColimitOfPreserves ((evaluation _ _).obj Δ) (pushout.isColimit a b))

-- Route correction: evaluate the simplicial copower pushout degreewise, descend compatible
-- summand maps through the explicit `Types.Pushout` quotient, and only then repackage them into a
-- morphism from the actual evaluated pushout object.
/-- Helper for Lemma 14.17.5: precomposing the cocone condition with a `U`-summand injection gives
the compatibility relation needed to descend the two leg-families to the `Types.Pushout`
quotient. -/
private theorem simplicial_copower_pushout_eval_desc_compatible
    (X : SimplicialObject C) (Δ : SimplexCategoryᵒᵖ)
    (s : PushoutCocone
      ((simplicialCopowerIndexHom X a).app Δ)
      ((simplicialCopowerIndexHom X b).app Δ))
    (u : U.obj Δ) :
    Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) (a.app Δ u) ≫ s.inl =
      Sigma.ι (fun _ : W.obj Δ ↦ X.obj Δ) (b.app Δ u) ≫ s.inr := by
  have hleft :
      Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) (a.app Δ u) =
        Sigma.ι (fun _ : U.obj Δ ↦ X.obj Δ) u ≫ (simplicialCopowerIndexHom X a).app Δ := by
    -- Proof comment: the left leg of the evaluated simplicial copower square is just reindexing
    -- along `a.app Δ`, so the `U`-summand injection lands in the corresponding `V`-summand.
    simpa [simplicialCopowerIndexHom_app] using
      (Limits.Sigma.ι_comp_map' (p := a.app Δ) (q := fun _ : U.obj Δ ↦ 𝟙 (X.obj Δ)) u).symm
  have hright :
      Sigma.ι (fun _ : W.obj Δ ↦ X.obj Δ) (b.app Δ u) =
        Sigma.ι (fun _ : U.obj Δ ↦ X.obj Δ) u ≫ (simplicialCopowerIndexHom X b).app Δ := by
    -- Proof comment: the right leg is the same reindexing formula for `b.app Δ`.
    simpa [simplicialCopowerIndexHom_app] using
      (Limits.Sigma.ι_comp_map' (p := b.app Δ) (q := fun _ : U.obj Δ ↦ 𝟙 (X.obj Δ)) u).symm
  have hs := congrArg (fun k ↦ Sigma.ι (fun _ : U.obj Δ ↦ X.obj Δ) u ≫ k) s.condition
  calc
    Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) (a.app Δ u) ≫ s.inl =
      Sigma.ι (fun _ : U.obj Δ ↦ X.obj Δ) u ≫ (simplicialCopowerIndexHom X a).app Δ ≫ s.inl := by
        simpa [Category.assoc] using congrArg (fun k ↦ k ≫ s.inl) hleft
    _ = Sigma.ι (fun _ : U.obj Δ ↦ X.obj Δ) u ≫ (simplicialCopowerIndexHom X b).app Δ ≫ s.inr := by
          simpa [Category.assoc] using hs
    _ = Sigma.ι (fun _ : W.obj Δ ↦ X.obj Δ) (b.app Δ u) ≫ s.inr := by
          simpa [Category.assoc] using congrArg (fun k ↦ k ≫ s.inr) hright.symm

/-- Helper for Lemma 14.17.5: the summand families on `V.obj Δ` and `W.obj Δ` respect the
generating relation of the degreewise `Types.Pushout`, so they descend to a map out of the
quotient. -/
private theorem simplicial_copower_pushout_eval_desc_family_wellDefined
    (X : SimplicialObject C) (Δ : SimplexCategoryᵒᵖ)
    (s : PushoutCocone
      ((simplicialCopowerIndexHom X a).app Δ)
      ((simplicialCopowerIndexHom X b).app Δ)) :
    ∀ z₁ z₂ : V.obj Δ ⊕ W.obj Δ,
      Types.Pushout.Rel (a.app Δ) (b.app Δ) z₁ z₂ →
        Sum.elim
            (fun v : V.obj Δ ↦ Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) v ≫ s.inl)
            (fun w : W.obj Δ ↦ Sigma.ι (fun _ : W.obj Δ ↦ X.obj Δ) w ≫ s.inr)
            z₁ =
          Sum.elim
            (fun v : V.obj Δ ↦ Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) v ≫ s.inl)
            (fun w : W.obj Δ ↦ Sigma.ι (fun _ : W.obj Δ ↦ X.obj Δ) w ≫ s.inr)
            z₂ := by
  intro z₁ z₂ hrel
  cases hrel with
  | inl_inr u =>
      -- Proof comment: the only generating relation identifies the `a u` and `b u` summands,
      -- exactly the compatibility proved above.
      exact simplicial_copower_pushout_eval_desc_compatible
        (a := a) (b := b) (X := X) (Δ := Δ) s u

/-- Helper for Lemma 14.17.5: the compatible degreewise family on the two coproduct legs descends
to a family indexed by the type-theoretic pushout of `a.app Δ` and `b.app Δ`. -/
private noncomputable def simplicial_copower_pushout_eval_desc_family
    (X : SimplicialObject C) (Δ : SimplexCategoryᵒᵖ)
    (s : PushoutCocone
      ((simplicialCopowerIndexHom X a).app Δ)
      ((simplicialCopowerIndexHom X b).app Δ)) :
    Types.Pushout (a.app Δ) (b.app Δ) → (X.obj Δ ⟶ s.pt) :=
  Quot.lift
    (fun z : V.obj Δ ⊕ W.obj Δ ↦
      Sum.elim
        (fun v : V.obj Δ ↦ Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) v ≫ s.inl)
        (fun w : W.obj Δ ↦ Sigma.ι (fun _ : W.obj Δ ↦ X.obj Δ) w ≫ s.inr)
        z)
    (simplicial_copower_pushout_eval_desc_family_wellDefined
      (a := a) (b := b) (X := X) (Δ := Δ) s)

/-- Helper for Lemma 14.17.5: the descended family recovers the left summand morphism on
`Types.Pushout.inl` representatives. -/
@[simp] private theorem simplicial_copower_pushout_eval_desc_family_inl
    (X : SimplicialObject C) (Δ : SimplexCategoryᵒᵖ)
    (s : PushoutCocone
      ((simplicialCopowerIndexHom X a).app Δ)
      ((simplicialCopowerIndexHom X b).app Δ))
    (v : V.obj Δ) :
    simplicial_copower_pushout_eval_desc_family (a := a) (b := b) (X := X) (Δ := Δ) s
        (Types.Pushout.inl (a.app Δ) (b.app Δ) v) =
      Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) v ≫ s.inl :=
  rfl

/-- Helper for Lemma 14.17.5: the descended family recovers the right summand morphism on
`Types.Pushout.inr` representatives. -/
@[simp] private theorem simplicial_copower_pushout_eval_desc_family_inr
    (X : SimplicialObject C) (Δ : SimplexCategoryᵒᵖ)
    (s : PushoutCocone
      ((simplicialCopowerIndexHom X a).app Δ)
      ((simplicialCopowerIndexHom X b).app Δ))
    (w : W.obj Δ) :
    simplicial_copower_pushout_eval_desc_family (a := a) (b := b) (X := X) (Δ := Δ) s
        (Types.Pushout.inr (a.app Δ) (b.app Δ) w) =
      Sigma.ι (fun _ : W.obj Δ ↦ X.obj Δ) w ≫ s.inr :=
  rfl

/-- Helper for Lemma 14.17.5: applying the inverse of the degreewise pushout comparison to a
left `Types.Pushout` representative recovers the corresponding simplicial pushout simplex. -/
private theorem simplicial_pushout_eval_typesPushoutIso_inv_inl_apply
    (Δ : SimplexCategoryᵒᵖ) (v : V.obj Δ) :
    (simplicial_pushout_eval_typesPushoutIso a b Δ).inv
        (Types.Pushout.inl (a.app Δ) (b.app Δ) v) =
      (pushout.inl a b).app Δ v := by
  -- Proof comment: this is the elementwise form of the previously established `inl` composite
  -- identity for the inverse comparison map.
  simpa using
    congrFun (simplicial_pushout_eval_typesPushoutIso_inv_comp_inl a b Δ) v

/-- Helper for Lemma 14.17.5: applying the inverse of the degreewise pushout comparison to a
right `Types.Pushout` representative recovers the corresponding simplicial pushout simplex. -/
private theorem simplicial_pushout_eval_typesPushoutIso_inv_inr_apply
    (Δ : SimplexCategoryᵒᵖ) (w : W.obj Δ) :
    (simplicial_pushout_eval_typesPushoutIso a b Δ).inv
        (Types.Pushout.inr (a.app Δ) (b.app Δ) w) =
      (pushout.inr a b).app Δ w := by
  -- Proof comment: this is the symmetric elementwise computation for the right pushout leg.
  simpa using
    congrFun (simplicial_pushout_eval_typesPushoutIso_inv_comp_inr a b Δ) w

/-- Helper for Lemma 14.17.5: the descended family on the type-theoretic pushout packages into
the mediating morphism from the evaluated simplicial copower pushout. -/
private noncomputable def simplicial_copower_pushout_eval_desc
    (X : SimplicialObject C) (Δ : SimplexCategoryᵒᵖ)
    (s : PushoutCocone
      ((simplicialCopowerIndexHom X a).app Δ)
      ((simplicialCopowerIndexHom X b).app Δ)) :
    ((pushout a b) × X).obj Δ ⟶ s.pt :=
  Limits.Sigma.desc
    (fun p : (pushout a b).obj Δ ↦
      simplicial_copower_pushout_eval_desc_family
        (a := a) (b := b) (X := X) (Δ := Δ) s
        ((simplicial_pushout_eval_typesPushoutIso a b Δ).hom p))

/-- Helper for Lemma 14.17.5: the mediator out of the evaluated simplicial copower pushout agrees
with the left cocone leg on each `V`-summand. -/
private theorem simplicial_copower_pushout_eval_desc_fac_left
    (X : SimplicialObject C) (Δ : SimplexCategoryᵒᵖ)
    (s : PushoutCocone
      ((simplicialCopowerIndexHom X a).app Δ)
      ((simplicialCopowerIndexHom X b).app Δ)) :
    (simplicialCopowerIndexHom X (pushout.inl a b)).app Δ ≫
        simplicial_copower_pushout_eval_desc (a := a) (b := b) (X := X) (Δ := Δ) s =
      s.inl := by
  let e := simplicial_pushout_eval_typesPushoutIso a b Δ
  apply Sigma.hom_ext
  intro v
  have hmap :
      Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) v ≫
          (simplicialCopowerIndexHom X (pushout.inl a b)).app Δ =
        Sigma.ι (fun _ : (pushout a b).obj Δ ↦ X.obj Δ) ((pushout.inl a b).app Δ v) := by
    -- Proof comment: the left map of the evaluated pushout cocone is reindexing along the
    -- simplicial pushout inclusion.
    simpa [simplicialCopowerIndexHom_app] using
      (Limits.Sigma.ι_comp_map'
        (p := (pushout.inl a b).app Δ)
        (q := fun _ : V.obj Δ ↦ 𝟙 (X.obj Δ))
        v).symm
  have htransport :
      e.hom ((pushout.inl a b).app Δ v) =
        Types.Pushout.inl (a.app Δ) (b.app Δ) v := by
    -- Proof comment: transporting the simplicial pushout simplex to `Types.Pushout` lands on the
    -- corresponding left representative.
    calc
      e.hom ((pushout.inl a b).app Δ v) =
        e.hom (e.inv (Types.Pushout.inl (a.app Δ) (b.app Δ) v)) := by
          rw [← simplicial_pushout_eval_typesPushoutIso_inv_inl_apply
            (a := a) (b := b) (Δ := Δ) v]
      _ = Types.Pushout.inl (a.app Δ) (b.app Δ) v := by
            simpa using congrFun e.hom_inv_id (Types.Pushout.inl (a.app Δ) (b.app Δ) v)
  calc
    Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) v ≫
        ((simplicialCopowerIndexHom X (pushout.inl a b)).app Δ ≫
          simplicial_copower_pushout_eval_desc (a := a) (b := b) (X := X) (Δ := Δ) s) =
      Sigma.ι (fun _ : (pushout a b).obj Δ ↦ X.obj Δ) ((pushout.inl a b).app Δ v) ≫
        simplicial_copower_pushout_eval_desc (a := a) (b := b) (X := X) (Δ := Δ) s := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ k ≫ simplicial_copower_pushout_eval_desc
                (a := a) (b := b) (X := X) (Δ := Δ) s)
              hmap
    _ =
      simplicial_copower_pushout_eval_desc_family
        (a := a) (b := b) (X := X) (Δ := Δ) s
        (e.hom ((pushout.inl a b).app Δ v)) := by
          simpa [simplicial_copower_pushout_eval_desc] using
            (Limits.Sigma.ι_desc
              (fun p : (pushout a b).obj Δ ↦
                simplicial_copower_pushout_eval_desc_family
                  (a := a) (b := b) (X := X) (Δ := Δ) s
                  ((simplicial_pushout_eval_typesPushoutIso a b Δ).hom p))
              ((pushout.inl a b).app Δ v))
    _ =
      simplicial_copower_pushout_eval_desc_family
        (a := a) (b := b) (X := X) (Δ := Δ) s
        (Types.Pushout.inl (a.app Δ) (b.app Δ) v) := by
          rw [htransport]
    _ = Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) v ≫ s.inl := by
          exact simplicial_copower_pushout_eval_desc_family_inl
            (a := a) (b := b) (X := X) (Δ := Δ) s v

/-- Helper for Lemma 14.17.5: the mediator out of the evaluated simplicial copower pushout agrees
with the right cocone leg on each `W`-summand. -/
private theorem simplicial_copower_pushout_eval_desc_fac_right
    (X : SimplicialObject C) (Δ : SimplexCategoryᵒᵖ)
    (s : PushoutCocone
      ((simplicialCopowerIndexHom X a).app Δ)
      ((simplicialCopowerIndexHom X b).app Δ)) :
    (simplicialCopowerIndexHom X (pushout.inr a b)).app Δ ≫
        simplicial_copower_pushout_eval_desc (a := a) (b := b) (X := X) (Δ := Δ) s =
      s.inr := by
  let e := simplicial_pushout_eval_typesPushoutIso a b Δ
  apply Sigma.hom_ext
  intro w
  have hmap :
      Sigma.ι (fun _ : W.obj Δ ↦ X.obj Δ) w ≫
          (simplicialCopowerIndexHom X (pushout.inr a b)).app Δ =
        Sigma.ι (fun _ : (pushout a b).obj Δ ↦ X.obj Δ) ((pushout.inr a b).app Δ w) := by
    -- Proof comment: this is the symmetric reindexing formula for the right pushout inclusion.
    simpa [simplicialCopowerIndexHom_app] using
      (Limits.Sigma.ι_comp_map'
        (p := (pushout.inr a b).app Δ)
        (q := fun _ : W.obj Δ ↦ 𝟙 (X.obj Δ))
        w).symm
  have htransport :
      e.hom ((pushout.inr a b).app Δ w) =
        Types.Pushout.inr (a.app Δ) (b.app Δ) w := by
    -- Proof comment: transporting the simplicial pushout simplex to `Types.Pushout` lands on the
    -- corresponding right representative.
    calc
      e.hom ((pushout.inr a b).app Δ w) =
        e.hom (e.inv (Types.Pushout.inr (a.app Δ) (b.app Δ) w)) := by
          rw [← simplicial_pushout_eval_typesPushoutIso_inv_inr_apply
            (a := a) (b := b) (Δ := Δ) w]
      _ = Types.Pushout.inr (a.app Δ) (b.app Δ) w := by
            simpa using congrFun e.hom_inv_id (Types.Pushout.inr (a.app Δ) (b.app Δ) w)
  calc
    Sigma.ι (fun _ : W.obj Δ ↦ X.obj Δ) w ≫
        ((simplicialCopowerIndexHom X (pushout.inr a b)).app Δ ≫
          simplicial_copower_pushout_eval_desc (a := a) (b := b) (X := X) (Δ := Δ) s) =
      Sigma.ι (fun _ : (pushout a b).obj Δ ↦ X.obj Δ) ((pushout.inr a b).app Δ w) ≫
        simplicial_copower_pushout_eval_desc (a := a) (b := b) (X := X) (Δ := Δ) s := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ k ≫ simplicial_copower_pushout_eval_desc
                (a := a) (b := b) (X := X) (Δ := Δ) s)
              hmap
    _ =
      simplicial_copower_pushout_eval_desc_family
        (a := a) (b := b) (X := X) (Δ := Δ) s
        (e.hom ((pushout.inr a b).app Δ w)) := by
          simpa [simplicial_copower_pushout_eval_desc] using
            (Limits.Sigma.ι_desc
              (fun p : (pushout a b).obj Δ ↦
                simplicial_copower_pushout_eval_desc_family
                  (a := a) (b := b) (X := X) (Δ := Δ) s
                  ((simplicial_pushout_eval_typesPushoutIso a b Δ).hom p))
              ((pushout.inr a b).app Δ w))
    _ =
      simplicial_copower_pushout_eval_desc_family
        (a := a) (b := b) (X := X) (Δ := Δ) s
        (Types.Pushout.inr (a.app Δ) (b.app Δ) w) := by
          rw [htransport]
    _ = Sigma.ι (fun _ : W.obj Δ ↦ X.obj Δ) w ≫ s.inr := by
          exact simplicial_copower_pushout_eval_desc_family_inr
            (a := a) (b := b) (X := X) (Δ := Δ) s w

/-- Helper for Lemma 14.17.5: any morphism out of the evaluated simplicial copower pushout is
determined by its restrictions to the `V`- and `W`-summands. -/
private theorem simplicial_copower_pushout_eval_desc_hom_ext
    (X : SimplicialObject C) (Δ : SimplexCategoryᵒᵖ)
    (s : PushoutCocone
      ((simplicialCopowerIndexHom X a).app Δ)
      ((simplicialCopowerIndexHom X b).app Δ))
    (m : ((pushout a b) × X).obj Δ ⟶ s.pt)
    (hleft : (simplicialCopowerIndexHom X (pushout.inl a b)).app Δ ≫ m = s.inl)
    (hright : (simplicialCopowerIndexHom X (pushout.inr a b)).app Δ ≫ m = s.inr) :
    m = simplicial_copower_pushout_eval_desc (a := a) (b := b) (X := X) (Δ := Δ) s := by
  let e := simplicial_pushout_eval_typesPushoutIso a b Δ
  apply Sigma.hom_ext
  intro p
  let q : Types.Pushout (a.app Δ) (b.app Δ) := e.hom p
  have hp : e.inv q = p := by
    -- Proof comment: every pushout simplex is the inverse image of its transported
    -- `Types.Pushout` class under the comparison isomorphism.
    simpa [q] using congrFun e.inv_hom_id p
  rw [← hp]
  refine Quot.inductionOn q ?_
  intro z
  cases z with
  | inl v =>
      have hmap :
          Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) v ≫
              (simplicialCopowerIndexHom X (pushout.inl a b)).app Δ =
            Sigma.ι (fun _ : (pushout a b).obj Δ ↦ X.obj Δ)
              (e.inv (Types.Pushout.inl (a.app Δ) (b.app Δ) v)) := by
        -- Proof comment: replace the target index by the inverse image of the left quotient
        -- representative and use the standard coproduct reindexing identity.
        calc
          Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) v ≫
              (simplicialCopowerIndexHom X (pushout.inl a b)).app Δ =
            Sigma.ι (fun _ : (pushout a b).obj Δ ↦ X.obj Δ) ((pushout.inl a b).app Δ v) := by
              simpa [simplicialCopowerIndexHom_app] using
                (Limits.Sigma.ι_comp_map'
                  (p := (pushout.inl a b).app Δ)
                  (q := fun _ : V.obj Δ ↦ 𝟙 (X.obj Δ))
                  v).symm
          _ =
            Sigma.ι (fun _ : (pushout a b).obj Δ ↦ X.obj Δ)
              (e.inv (Types.Pushout.inl (a.app Δ) (b.app Δ) v)) := by
                rw [simplicial_pushout_eval_typesPushoutIso_inv_inl_apply
                  (a := a) (b := b) (Δ := Δ) v]
      calc
        Sigma.ι (fun _ : (pushout a b).obj Δ ↦ X.obj Δ)
            (e.inv (Types.Pushout.inl (a.app Δ) (b.app Δ) v)) ≫ m =
          Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) v ≫ s.inl := by
            calc
              Sigma.ι (fun _ : (pushout a b).obj Δ ↦ X.obj Δ)
                  (e.inv (Types.Pushout.inl (a.app Δ) (b.app Δ) v)) ≫ m =
                Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) v ≫
                  (simplicialCopowerIndexHom X (pushout.inl a b)).app Δ ≫ m := by
                    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ m) hmap.symm
              _ = Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) v ≫ s.inl := by
                    simpa [Category.assoc] using congrArg
                      (fun k ↦ Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) v ≫ k) hleft
        _ =
          Sigma.ι (fun _ : (pushout a b).obj Δ ↦ X.obj Δ)
              (e.inv (Types.Pushout.inl (a.app Δ) (b.app Δ) v)) ≫
            simplicial_copower_pushout_eval_desc (a := a) (b := b) (X := X) (Δ := Δ) s := by
              symm
              calc
                Sigma.ι (fun _ : (pushout a b).obj Δ ↦ X.obj Δ)
                    (e.inv (Types.Pushout.inl (a.app Δ) (b.app Δ) v)) ≫
                    simplicial_copower_pushout_eval_desc
                      (a := a) (b := b) (X := X) (Δ := Δ) s =
                  Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) v ≫
                    (simplicialCopowerIndexHom X (pushout.inl a b)).app Δ ≫
                      simplicial_copower_pushout_eval_desc
                        (a := a) (b := b) (X := X) (Δ := Δ) s := by
                          simpa [Category.assoc] using congrArg
                            (fun k ↦ k ≫ simplicial_copower_pushout_eval_desc
                              (a := a) (b := b) (X := X) (Δ := Δ) s) hmap.symm
                _ = Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) v ≫ s.inl := by
                      simpa [Category.assoc] using congrArg
                        (fun k ↦ Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) v ≫ k)
                        (simplicial_copower_pushout_eval_desc_fac_left
                          (a := a) (b := b) (X := X) (Δ := Δ) s)
  | inr w =>
      have hmap :
          Sigma.ι (fun _ : W.obj Δ ↦ X.obj Δ) w ≫
              (simplicialCopowerIndexHom X (pushout.inr a b)).app Δ =
            Sigma.ι (fun _ : (pushout a b).obj Δ ↦ X.obj Δ)
              (e.inv (Types.Pushout.inr (a.app Δ) (b.app Δ) w)) := by
        -- Proof comment: this is the symmetric summand identification for the right quotient
        -- representative.
        calc
          Sigma.ι (fun _ : W.obj Δ ↦ X.obj Δ) w ≫
              (simplicialCopowerIndexHom X (pushout.inr a b)).app Δ =
            Sigma.ι (fun _ : (pushout a b).obj Δ ↦ X.obj Δ) ((pushout.inr a b).app Δ w) := by
              simpa [simplicialCopowerIndexHom_app] using
                (Limits.Sigma.ι_comp_map'
                  (p := (pushout.inr a b).app Δ)
                  (q := fun _ : W.obj Δ ↦ 𝟙 (X.obj Δ))
                  w).symm
          _ =
            Sigma.ι (fun _ : (pushout a b).obj Δ ↦ X.obj Δ)
              (e.inv (Types.Pushout.inr (a.app Δ) (b.app Δ) w)) := by
                rw [simplicial_pushout_eval_typesPushoutIso_inv_inr_apply
                  (a := a) (b := b) (Δ := Δ) w]
      calc
        Sigma.ι (fun _ : (pushout a b).obj Δ ↦ X.obj Δ)
            (e.inv (Types.Pushout.inr (a.app Δ) (b.app Δ) w)) ≫ m =
          Sigma.ι (fun _ : W.obj Δ ↦ X.obj Δ) w ≫ s.inr := by
            calc
              Sigma.ι (fun _ : (pushout a b).obj Δ ↦ X.obj Δ)
                  (e.inv (Types.Pushout.inr (a.app Δ) (b.app Δ) w)) ≫ m =
                Sigma.ι (fun _ : W.obj Δ ↦ X.obj Δ) w ≫
                  (simplicialCopowerIndexHom X (pushout.inr a b)).app Δ ≫ m := by
                    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ m) hmap.symm
              _ = Sigma.ι (fun _ : W.obj Δ ↦ X.obj Δ) w ≫ s.inr := by
                    simpa [Category.assoc] using congrArg
                      (fun k ↦ Sigma.ι (fun _ : W.obj Δ ↦ X.obj Δ) w ≫ k) hright
        _ =
          Sigma.ι (fun _ : (pushout a b).obj Δ ↦ X.obj Δ)
              (e.inv (Types.Pushout.inr (a.app Δ) (b.app Δ) w)) ≫
            simplicial_copower_pushout_eval_desc (a := a) (b := b) (X := X) (Δ := Δ) s := by
              symm
              calc
                Sigma.ι (fun _ : (pushout a b).obj Δ ↦ X.obj Δ)
                    (e.inv (Types.Pushout.inr (a.app Δ) (b.app Δ) w)) ≫
                    simplicial_copower_pushout_eval_desc
                      (a := a) (b := b) (X := X) (Δ := Δ) s =
                  Sigma.ι (fun _ : W.obj Δ ↦ X.obj Δ) w ≫
                    (simplicialCopowerIndexHom X (pushout.inr a b)).app Δ ≫
                      simplicial_copower_pushout_eval_desc
                        (a := a) (b := b) (X := X) (Δ := Δ) s := by
                          simpa [Category.assoc] using congrArg
                            (fun k ↦ k ≫ simplicial_copower_pushout_eval_desc
                              (a := a) (b := b) (X := X) (Δ := Δ) s) hmap.symm
                _ = Sigma.ι (fun _ : W.obj Δ ↦ X.obj Δ) w ≫ s.inr := by
                      simpa [Category.assoc] using congrArg
                        (fun k ↦ Sigma.ι (fun _ : W.obj Δ ↦ X.obj Δ) w ≫ k)
                        (simplicial_copower_pushout_eval_desc_fac_right
                          (a := a) (b := b) (X := X) (Δ := Δ) s)

private noncomputable def simplicial_copower_pushout_eval_isColimit_aux
    (X : SimplicialObject C) (Δ : SimplexCategoryᵒᵖ) :
    IsColimit
      (((evaluation _ _).obj Δ).mapCocone
        (simplicial_copower_pushout_cocone_aux (a := a) (b := b) X)) := by
  let cΔ : PushoutCocone
      ((simplicialCopowerIndexHom X a).app Δ)
      ((simplicialCopowerIndexHom X b).app Δ) :=
    PushoutCocone.mk
      ((simplicialCopowerIndexHom X (pushout.inl a b)).app Δ)
      ((simplicialCopowerIndexHom X (pushout.inr a b)).app Δ)
      (by
        -- Proof comment: evaluating the simplicial cocone condition at `Δ` produces the
        -- corresponding degreewise pushout relation.
        simpa using congrArg
          (fun k => k.app Δ)
          (simplicial_copower_pushout_cocone_aux (a := a) (b := b) X).condition)
  have hc : IsColimit cΔ := by
  -- Route correction: instead of forcing the small-universe `Type` pushout eliminator to land in
  -- the larger hom-type `X.obj Δ ⟶ s.pt`, descend the compatible family explicitly along the
  -- `Types.Pushout` quotient and then repackage it with `Sigma.desc`.
    refine CategoryTheory.Limits.PushoutCocone.IsColimit.mk
      (C := C)
      (f := (simplicialCopowerIndexHom X a).app Δ)
      (g := (simplicialCopowerIndexHom X b).app Δ)
      (inl := (simplicialCopowerIndexHom X (pushout.inl a b)).app Δ)
      (inr := (simplicialCopowerIndexHom X (pushout.inr a b)).app Δ)
      cΔ.condition ?_ ?_ ?_ ?_
    · intro s
      -- Proof comment: the mediating morphism is built by transporting degreewise pushout
      -- representatives to `Types.Pushout` and evaluating the descended family there.
      exact simplicial_copower_pushout_eval_desc (a := a) (b := b) (X := X) (Δ := Δ) s
    · intro s
      -- Proof comment: the mediator agrees with the left cocone leg by checking each coproduct
      -- summand separately.
      exact simplicial_copower_pushout_eval_desc_fac_left
        (a := a) (b := b) (X := X) (Δ := Δ) s
    · intro s
      -- Proof comment: the right factorization is the same argument on the other family of
      -- summands.
      exact simplicial_copower_pushout_eval_desc_fac_right
        (a := a) (b := b) (X := X) (Δ := Δ) s
    · intro s m hleft hright
      -- Proof comment: uniqueness follows because a morphism out of a coproduct is determined by
      -- its values on each summand, and every pushout summand comes from either a left or a right
      -- `Types.Pushout` representative.
      exact simplicial_copower_pushout_eval_desc_hom_ext
        (a := a) (b := b) (X := X) (Δ := Δ) s m hleft hright
  let cIso :
      cΔ ≅
        (((evaluation _ _).obj Δ).mapCocone
          (simplicial_copower_pushout_cocone_aux (a := a) (b := b) X)) :=
    Cocone.ext (Iso.refl _) (by
      intro j
      cases j <;> rfl)
  exact IsColimit.ofIsoColimit hc cIso

/-- Helper for Lemma 14.17.5: the fixed-`X` simplicial copower square over the span `a, b` is the
explicit cocone whose apex is `(pushout a b) × X`. -/
private noncomputable def simplicial_copower_pushout_cocone
    (X : SimplicialObject C) :
    PushoutCocone (simplicialCopowerIndexHom X a) (simplicialCopowerIndexHom X b) :=
  simplicial_copower_pushout_cocone_aux (a := a) (b := b) X

/-- Helper for Lemma 14.17.5: after evaluating at a simplex `Δ`, the fixed-`X` simplicial
copower cocone is the pointwise coproduct-over-pushout cocone, hence colimiting. -/
private noncomputable def simplicial_copower_pushout_eval_isColimit
    (X : SimplicialObject C) (Δ : SimplexCategoryᵒᵖ) :
    IsColimit
      (((evaluation _ _).obj Δ).mapCocone
        (simplicial_copower_pushout_cocone (a := a) (b := b) X)) :=
  simplicial_copower_pushout_eval_isColimit_aux (a := a) (b := b) (X := X) (Δ := Δ)

/-- Helper for Lemma 14.17.5: for every test simplicial object `X`, the explicit cocone on
`simplicialCopowerIndexHom X a` and `simplicialCopowerIndexHom X b` with apex `(pushout a b) × X`
is colimiting. -/
private noncomputable def simplicial_copower_pushout_isColimit
    (X : SimplicialObject C) :
    IsColimit (simplicial_copower_pushout_cocone (a := a) (b := b) X) :=
  -- Proof comment: colimits in simplicial objects are detected degreewise by evaluation, so the
  -- degreewise pushout witnesses package into the desired functor-category colimit.
  evaluationJointlyReflectsColimits
    (simplicial_copower_pushout_cocone (a := a) (b := b) X) fun Δ ↦ by
      simpa using simplicial_copower_pushout_eval_isColimit (a := a) (b := b) (X := X) Δ

/-- The canonical comparison morphism from the internal hom out of a simplicial pushout to the
pullback of the two precomposition morphisms. -/
def simplicial_hom_pushout_to_pullback
    :
    simplicialHom (pushout a b) T ⟶
      pullback (simplicial_hom_precomp a T) (simplicial_hom_precomp b T) :=
  pullback.lift
    (simplicial_hom_precomp (pushout.inl a b) T)
    (simplicial_hom_precomp (pushout.inr a b) T)
    (simplicial_hom_precomp_pushout_condition a b T).w

section HomPullbackComparisonPreTarget

variable (X : SimplicialObject C)

local notation "homPullbackIsLimit" =>
  isLimitOfHasPullbackOfPreservesLimit (coyoneda.obj (op X))
    (simplicial_hom_precomp a T) (simplicial_hom_precomp b T)

local notation "homPullbackEquiv" => PullbackCone.IsLimit.equivPullbackObj homPullbackIsLimit

/-- Helper for Lemma 14.17.5: postcomposition with the canonical comparison morphism from
`Hom(V ⨿[U] W, T)` to the pullback object yields the expected map on `Hom(X, -)`. -/
private noncomputable def simplicial_hom_pushout_postcomp_map
    :
    (X ⟶ simplicialHom (pushout a b) T) →
      Types.PullbackObj
        (fun f : X ⟶ simplicialHom V T ↦ f ≫ simplicial_hom_precomp a T)
        (fun g : X ⟶ simplicialHom W T ↦ g ≫ simplicial_hom_precomp b T) :=
  -- Proof comment: this is the direct hom-set map induced by the canonical comparison morphism,
  -- written using the pullback universal-property equivalence on `Hom(X, -)`.
  fun h ↦ homPullbackEquiv (h ≫ simplicial_hom_pushout_to_pullback a b T)

/-- Helper for Lemma 14.17.5: the first pullback projection of the pre-target hom-set comparison
map is composition with the `V`-leg precomposition morphism. -/
private theorem simplicial_hom_pushout_postcomp_map_fst
    (h : X ⟶ simplicialHom (pushout a b) T) :
    (simplicial_hom_pushout_postcomp_map (a := a) (b := b) (T := T) X h).1.1 =
      h ≫ simplicial_hom_precomp (pushout.inl a b) T := by
  -- Proof comment: unpack the pullback-hom equivalence and read off its first projection.
  simpa [simplicial_hom_pushout_postcomp_map, simplicial_hom_pushout_to_pullback, Category.assoc,
    pullback.lift_fst]
    using
      (PullbackCone.IsLimit.equivPullbackObj_apply_fst homPullbackIsLimit
        (h ≫ simplicial_hom_pushout_to_pullback a b T))

/-- Helper for Lemma 14.17.5: the second pullback projection of the pre-target hom-set comparison
map is composition with the `W`-leg precomposition morphism. -/
private theorem simplicial_hom_pushout_postcomp_map_snd
    (h : X ⟶ simplicialHom (pushout a b) T) :
    (simplicial_hom_pushout_postcomp_map (a := a) (b := b) (T := T) X h).1.2 =
      h ≫ simplicial_hom_precomp (pushout.inr a b) T := by
  -- Proof comment: the second projection is computed the same way with `pullback.snd`.
  simpa [simplicial_hom_pushout_postcomp_map, simplicial_hom_pushout_to_pullback, Category.assoc,
    pullback.lift_snd]
    using
      (PullbackCone.IsLimit.equivPullbackObj_apply_snd homPullbackIsLimit
        (h ≫ simplicial_hom_pushout_to_pullback a b T))

/-- Helper for Lemma 14.17.5: the pullback of hom-sets into `Hom(V, T)` and `Hom(W, T)` is
canonically equivalent to the pullback of the corresponding source-side copower morphism sets. -/
private noncomputable def simplicial_hom_precomp_pullback_equiv
    :
    Types.PullbackObj
      (fun f : X ⟶ simplicialHom V T ↦ f ≫ simplicial_hom_precomp a T)
      (fun g : X ⟶ simplicialHom W T ↦ g ≫ simplicial_hom_precomp b T) ≃
    Types.PullbackObj
      (fun f : V × X ⟶ T ↦ simplicialCopowerIndexHom X a ≫ f)
      (fun g : W × X ⟶ T ↦ simplicialCopowerIndexHom X b ≫ g) where
  toFun := by
    intro p
    let eU : (X ⟶ simplicialHom U T) ≃ (U × X ⟶ T) :=
      (simplicialHomPresheaf U T).representableBy.homEquiv
    let eV : (X ⟶ simplicialHom V T) ≃ (V × X ⟶ T) :=
      (simplicialHomPresheaf V T).representableBy.homEquiv
    let eW : (X ⟶ simplicialHom W T) ≃ (W × X ⟶ T) :=
      (simplicialHomPresheaf W T).representableBy.homEquiv
    refine ⟨⟨eV p.1.1, eW p.1.2⟩, ?_⟩
    -- Proof comment: transport the pullback relation across the representing equivalence using
    -- the source-side precomposition formula proved in `simplicial_hom_homEquiv_precomp`.
    calc
      simplicialCopowerIndexHom X a ≫ eV p.1.1
          = eU (p.1.1 ≫ simplicial_hom_precomp a T) := by
              simpa [eU, eV] using
                (simplicial_hom_homEquiv_precomp (a := a) (T := T) (X := X) (f := p.1.1)).symm
      _ = eU (p.1.2 ≫ simplicial_hom_precomp b T) := by
            simpa [p.2]
      _ = simplicialCopowerIndexHom X b ≫ eW p.1.2 := by
            simpa [eU, eW] using
              (simplicial_hom_homEquiv_precomp (a := b) (T := T) (X := X) (f := p.1.2))
  invFun := by
    intro p
    let eU : (X ⟶ simplicialHom U T) ≃ (U × X ⟶ T) :=
      (simplicialHomPresheaf U T).representableBy.homEquiv
    let eV : (X ⟶ simplicialHom V T) ≃ (V × X ⟶ T) :=
      (simplicialHomPresheaf V T).representableBy.homEquiv
    let eW : (X ⟶ simplicialHom W T) ≃ (W × X ⟶ T) :=
      (simplicialHomPresheaf W T).representableBy.homEquiv
    refine ⟨⟨eV.symm p.1.1, eW.symm p.1.2⟩, ?_⟩
    -- Proof comment: apply the representing equivalence for `Hom(U, T)` and rewrite both sides
    -- by the same precomposition formula; the target pullback equality is exactly `p.2`.
    apply eU.injective
    calc
      eU (eV.symm p.1.1 ≫ simplicial_hom_precomp a T)
          = simplicialCopowerIndexHom X a ≫ eV (eV.symm p.1.1) := by
              simpa [eU, eV] using
                (simplicial_hom_homEquiv_precomp (a := a) (T := T) (X := X) (f := eV.symm p.1.1))
      _ = simplicialCopowerIndexHom X a ≫ p.1.1 := by
            simpa using
              congrArg (fun k ↦ simplicialCopowerIndexHom X a ≫ k)
                (Equiv.apply_symm_apply eV p.1.1)
      _ = simplicialCopowerIndexHom X b ≫ p.1.2 := p.2
      _ = simplicialCopowerIndexHom X b ≫ eW (eW.symm p.1.2) := by
            simpa using
              congrArg (fun k ↦ simplicialCopowerIndexHom X b ≫ k)
                (Equiv.apply_symm_apply eW p.1.2).symm
      _ = eU (eW.symm p.1.2 ≫ simplicial_hom_precomp b T) := by
            simpa [eU, eW] using
              (simplicial_hom_homEquiv_precomp (a := b) (T := T) (X := X) (f := eW.symm p.1.2)).symm
  left_inv := by
    intro p
    -- Proof comment: both components are recovered by applying the inverse representing
    -- equivalence after the forward one.
    apply Subtype.ext
    apply Prod.ext
    · exact Equiv.symm_apply_apply _ _
    · exact Equiv.symm_apply_apply _ _
  right_inv := by
    intro p
    -- Proof comment: the inverse followed by the forward map is the identity by the forward
    -- representing equivalence on each pullback component.
    apply Subtype.ext
    apply Prod.ext
    · exact Equiv.apply_symm_apply _ _
    · exact Equiv.apply_symm_apply _ _

/-- Helper for Lemma 14.17.5: the Yoneda equivalence coming from the fixed-`X` copower pushout
identifies `Hom(X, Hom(V ⨿[U] W, T))` with the expected pullback of hom-sets. -/
private noncomputable def simplicial_hom_pushout_pullback_equiv
    :
    (X ⟶ simplicialHom (pushout a b) T) ≃
      Types.PullbackObj
        (fun f : X ⟶ simplicialHom V T ↦ f ≫ simplicial_hom_precomp a T)
      (fun g : X ⟶ simplicialHom W T ↦ g ≫ simplicial_hom_precomp b T) := by
  let ePushout : (X ⟶ simplicialHom (pushout a b) T) ≃ ((pushout a b) × X ⟶ T) :=
    (simplicialHomPresheaf (pushout a b) T).representableBy.homEquiv
  let eCopower :
      ((pushout a b) × X ⟶ T) ≃
        Types.PullbackObj
          (fun f : V × X ⟶ T ↦ simplicialCopowerIndexHom X a ≫ f)
          (fun g : W × X ⟶ T ↦ simplicialCopowerIndexHom X b ≫ g) :=
    PullbackCone.IsLimit.equivPullbackObj
      ((simplicial_copower_pushout_cocone (a := a) (b := b) X).isColimitYonedaEquiv.toFun
        (simplicial_copower_pushout_isColimit (a := a) (b := b) (X := X)) T)
  -- Proof comment: compose the representing equivalence for `Hom(V ⨿[U] W, T)` with the Yoneda
  -- pullback equivalence for the fixed-`X` copower pushout, then translate back to hom-sets.
  exact ePushout.trans (eCopower.trans
    (simplicial_hom_precomp_pullback_equiv (a := a) (b := b) (T := T) X).symm)

/-- Helper for Lemma 14.17.5: the Yoneda pullback equivalence has the same first projection as
the explicit postcomposition map. -/
private theorem simplicial_hom_pushout_pullback_equiv_fst
    (h : X ⟶ simplicialHom (pushout a b) T) :
    (simplicial_hom_pushout_pullback_equiv (a := a) (b := b) (T := T) X h).1.1 =
      h ≫ simplicial_hom_precomp (pushout.inl a b) T := by
  let ePushout : (X ⟶ simplicialHom (pushout a b) T) ≃ ((pushout a b) × X ⟶ T) :=
    (simplicialHomPresheaf (pushout a b) T).representableBy.homEquiv
  let eV : (X ⟶ simplicialHom V T) ≃ (V × X ⟶ T) :=
    (simplicialHomPresheaf V T).representableBy.homEquiv
  let hYoneda :
      IsLimit
        ((simplicial_copower_pushout_cocone (a := a) (b := b) X).op.map (yoneda.obj T)) :=
    (simplicial_copower_pushout_cocone (a := a) (b := b) X).isColimitYonedaEquiv.toFun
      (simplicial_copower_pushout_isColimit (a := a) (b := b) (X := X)) T
  let p :
      Types.PullbackObj
        (fun f : V × X ⟶ T ↦ simplicialCopowerIndexHom X a ≫ f)
        (fun g : W × X ⟶ T ↦ simplicialCopowerIndexHom X b ≫ g) :=
    (PullbackCone.IsLimit.equivPullbackObj hYoneda) (ePushout h)
  -- Proof comment: compute the first projection via the Yoneda pullback equivalence, then use
  -- the representing equivalence for `Hom(V, T)` to recognize precomposition by `pushout.inl`.
  apply eV.injective
  calc
    eV ((simplicial_hom_pushout_pullback_equiv (a := a) (b := b) (T := T) X h).1.1)
        = p.1.1 := by
            change eV (eV.symm p.1.1) = p.1.1
            exact Equiv.apply_symm_apply _ _
    _ = simplicialCopowerIndexHom X (pushout.inl a b) ≫ ePushout h := by
          simpa [p] using
            (PullbackCone.IsLimit.equivPullbackObj_apply_fst hYoneda (ePushout h))
    _ = eV (h ≫ simplicial_hom_precomp (pushout.inl a b) T) := by
          simpa [eV, ePushout] using
            (simplicial_hom_homEquiv_precomp (a := pushout.inl a b) (T := T)
              (X := X) (f := h)).symm

/-- Helper for Lemma 14.17.5: the Yoneda pullback equivalence has the same second projection as
the explicit postcomposition map. -/
private theorem simplicial_hom_pushout_pullback_equiv_snd
    (h : X ⟶ simplicialHom (pushout a b) T) :
    (simplicial_hom_pushout_pullback_equiv (a := a) (b := b) (T := T) X h).1.2 =
      h ≫ simplicial_hom_precomp (pushout.inr a b) T := by
  let ePushout : (X ⟶ simplicialHom (pushout a b) T) ≃ ((pushout a b) × X ⟶ T) :=
    (simplicialHomPresheaf (pushout a b) T).representableBy.homEquiv
  let eW : (X ⟶ simplicialHom W T) ≃ (W × X ⟶ T) :=
    (simplicialHomPresheaf W T).representableBy.homEquiv
  let hYoneda :
      IsLimit
        ((simplicial_copower_pushout_cocone (a := a) (b := b) X).op.map (yoneda.obj T)) :=
    (simplicial_copower_pushout_cocone (a := a) (b := b) X).isColimitYonedaEquiv.toFun
      (simplicial_copower_pushout_isColimit (a := a) (b := b) (X := X)) T
  let p :
      Types.PullbackObj
        (fun f : V × X ⟶ T ↦ simplicialCopowerIndexHom X a ≫ f)
        (fun g : W × X ⟶ T ↦ simplicialCopowerIndexHom X b ≫ g) :=
    (PullbackCone.IsLimit.equivPullbackObj hYoneda) (ePushout h)
  -- Proof comment: the second projection is computed identically, now using the `W`-leg of the
  -- fixed-`X` copower pushout.
  apply eW.injective
  calc
    eW ((simplicial_hom_pushout_pullback_equiv (a := a) (b := b) (T := T) X h).1.2)
        = p.1.2 := by
            change eW (eW.symm p.1.2) = p.1.2
            exact Equiv.apply_symm_apply _ _
    _ = simplicialCopowerIndexHom X (pushout.inr a b) ≫ ePushout h := by
          simpa [p] using
            (PullbackCone.IsLimit.equivPullbackObj_apply_snd hYoneda (ePushout h))
    _ = eW (h ≫ simplicial_hom_precomp (pushout.inr a b) T) := by
          simpa [eW, ePushout] using
            (simplicial_hom_homEquiv_precomp (a := pushout.inr a b) (T := T)
              (X := X) (f := h)).symm

/-- Helper for Lemma 14.17.5: the explicit postcomposition map on `Hom(X, -)` agrees with the
Yoneda pullback equivalence coming from the fixed-`X` copower pushout. -/
private theorem simplicial_hom_pushout_postcomp_map_eq_pullback_equiv
    :
    simplicial_hom_pushout_postcomp_map (a := a) (b := b) (T := T) X =
      (simplicial_hom_pushout_pullback_equiv (a := a) (b := b) (T := T) X).toFun := by
  funext h
  apply Subtype.ext
  apply Prod.ext
  · exact (simplicial_hom_pushout_postcomp_map_fst (a := a) (b := b) (T := T) (X := X) h).trans
      (simplicial_hom_pushout_pullback_equiv_fst (a := a) (b := b) (T := T) (X := X) h).symm
  · exact (simplicial_hom_pushout_postcomp_map_snd (a := a) (b := b) (T := T) (X := X) h).trans
      (simplicial_hom_pushout_pullback_equiv_snd (a := a) (b := b) (T := T) (X := X) h).symm

/-- Helper for Lemma 14.17.5: for every test simplicial object `X`, postcomposition with the
canonical comparison morphism induces a bijection on `Hom(X, -)`. -/
private theorem simplicial_hom_pushout_postcomp_bijective
    :
    Function.Bijective (simplicial_hom_pushout_postcomp_map (a := a) (b := b) (T := T) X) := by
  -- Proof comment: after identifying the explicit map with the Yoneda pullback equivalence, the
  -- result is immediate from bijectivity of an equivalence.
  simpa [simplicial_hom_pushout_postcomp_map_eq_pullback_equiv (a := a) (b := b) (T := T) (X := X)]
    using (simplicial_hom_pushout_pullback_equiv (a := a) (b := b) (T := T) X).bijective

end HomPullbackComparisonPreTarget

/-- Lemma 14.17.5 in owner form: the internal hom out of a simplicial pushout is canonically the
pullback of the two precomposition morphisms. -/
@[stacks 017N]
theorem simplicial_hom_pushout_to_pullback_isIso
    :
    IsIso (simplicial_hom_pushout_to_pullback a b T) := by
  -- Proof comment: by Yoneda, it suffices to check that postcomposition with the comparison map
  -- is bijective on `Hom(X, -)` for every test simplicial object `X`.
  refine isIso_of_yoneda_map_bijective (simplicial_hom_pushout_to_pullback a b T) ?_
  intro X
  let hlim :=
    isLimitOfHasPullbackOfPreservesLimit (coyoneda.obj (op X))
      (simplicial_hom_precomp a T) (simplicial_hom_precomp b T)
  let e := PullbackCone.IsLimit.equivPullbackObj hlim
  have hbij := simplicial_hom_pushout_postcomp_bijective (a := a) (b := b) (T := T) (X := X)
  refine ⟨?_, ?_⟩
  · intro f g hfg
    apply hbij.1
    change e (f ≫ simplicial_hom_pushout_to_pullback a b T) =
      e (g ≫ simplicial_hom_pushout_to_pullback a b T)
    exact congrArg e hfg
  · intro y
    obtain ⟨x, hx⟩ := hbij.2 (e y)
    refine ⟨x, ?_⟩
    have hx' := hx
    change e (x ≫ simplicial_hom_pushout_to_pullback a b T) = e y at hx'
    exact e.injective hx'

section HomPullbackComparison

variable (X : SimplicialObject C)

local notation "homPullbackIsLimit" =>
  isLimitOfHasPullbackOfPreservesLimit (coyoneda.obj (op X))
    (simplicial_hom_precomp a T) (simplicial_hom_precomp b T)

local notation "homPullbackEquiv" => PullbackCone.IsLimit.equivPullbackObj homPullbackIsLimit

/-- Evaluating the canonical pushout-to-pullback comparison isomorphism and then applying the
pullback universal-property equivalence on hom-sets. -/
noncomputable def simplicial_hom_pushout_hom_to_pullback
    :
    (X ⟶ simplicialHom (pushout a b) T) →
      Types.PullbackObj
        (fun f : X ⟶ simplicialHom V T ↦ f ≫ simplicial_hom_precomp a T)
        (fun g : X ⟶ simplicialHom W T ↦ g ≫ simplicial_hom_precomp b T) :=
  -- Proof comment: this is the direct source-facing hom-set map induced by the canonical
  -- comparison `Hom(V ⨿[U] W, T) ⟶ Hom(V, T) ×_{Hom(U, T)} Hom(W, T)`, before any use of
  -- bijectivity or invertibility.
  fun h ↦ homPullbackEquiv (h ≫ simplicial_hom_pushout_to_pullback a b T)

/-- Helper for Lemma 14.17.5: the first pullback projection of the induced hom-set map is
composition with the `V`-leg precomposition morphism. -/
theorem simplicial_hom_pushout_hom_to_pullback_fst
    (h : X ⟶ simplicialHom (pushout a b) T) :
    (simplicial_hom_pushout_hom_to_pullback a b T X h).1.1 =
      h ≫ simplicial_hom_precomp (pushout.inl a b) T := by
  -- Proof comment: unpack the hom-level comparison through the canonical pullback-hom
  -- equivalence, whose first projection is composition with `pullback.fst`.
  simpa [simplicial_hom_pushout_hom_to_pullback, simplicial_hom_pushout_to_pullback,
    Category.assoc, pullback.lift_fst] using
    (PullbackCone.IsLimit.equivPullbackObj_apply_fst homPullbackIsLimit
      (h ≫ simplicial_hom_pushout_to_pullback a b T))

/-- Helper for Lemma 14.17.5: the second pullback projection of the induced hom-set map is
composition with the `W`-leg precomposition morphism. -/
theorem simplicial_hom_pushout_hom_to_pullback_snd
    (h : X ⟶ simplicialHom (pushout a b) T) :
    (simplicial_hom_pushout_hom_to_pullback a b T X h).1.2 =
      h ≫ simplicial_hom_precomp (pushout.inr a b) T := by
  -- Proof comment: the second pullback projection is computed by composition with
  -- `pullback.snd`, which is the `W`-leg of the comparison morphism.
  simpa [simplicial_hom_pushout_hom_to_pullback, simplicial_hom_pushout_to_pullback,
    Category.assoc, pullback.lift_snd] using
    (PullbackCone.IsLimit.equivPullbackObj_apply_snd homPullbackIsLimit
      (h ≫ simplicial_hom_pushout_to_pullback a b T))

-- Proof sketch: for every test simplicial object `X`, use `simplicial_hom_homEquiv_precomp` to
-- identify morphisms `X ⟶ Hom(V ⨿[U] W, T)` with maps
-- `X × (V ⨿[U] W) ⟶ T`, then apply the pushout universal property from `Lemma 14.8.2` to rewrite
-- these as a pullback of the two mapping sets out of `X × V` and `X × W`.
/-- Lemma 14.17.5 in bridge form: once the internal mapping objects out of `U`, `V`, `W`, and the
simplicial pushout `V ⨿[U] W` exist and the pullback of the two precomposition morphisms exists,
the canonical map
`Hom(X, Hom(V ⨿[U] W, T)) → Hom(X, Hom(V, T)) ×_{Hom(X, Hom(U, T))} Hom(X, Hom(W, T))`
is bijective for every simplicial object `X`. Thus `Hom(V ⨿[U] W, T)` represents the fibre
product `Hom(V, T) ×_{Hom(U, T)} Hom(W, T)`. -/
-- Proof sketch: for every test simplicial object `X`, use `simplicial_hom_homEquiv_precomp` to
-- identify morphisms `X ⟶ Hom(V ⨿[U] W, T)` with maps
-- `X × (V ⨿[U] W) ⟶ T`, then apply the pushout universal property from `Lemma 14.8.2` to rewrite
-- these as a pullback of the two mapping sets out of `X × V` and `X × W`.
theorem simplicial_hom_pushout_hom_to_pullback_bijective
    :
    Function.Bijective (simplicial_hom_pushout_hom_to_pullback a b T X) := by
  let e := homPullbackEquiv
  let _ := simplicial_hom_pushout_to_pullback_isIso a b T
  let i := asIso (simplicial_hom_pushout_to_pullback a b T)
  change Function.Bijective (fun h ↦ e (h ≫ simplicial_hom_pushout_to_pullback a b T))
  -- Proof comment: once the comparison morphism is known to be an isomorphism, the induced
  -- hom-set map is just postcomposition by that isomorphism followed by the pullback-hom
  -- equivalence.
  change Function.Bijective (fun h ↦ e (h ≫ i.hom))
  refine e.bijective.comp ?_
  refine ⟨?_, ?_⟩
  · intro f g hfg
    have := congrArg (fun k ↦ k ≫ i.inv) hfg
    simpa [Category.assoc] using this
  · intro h
    refine ⟨h ≫ i.inv, ?_⟩
    simp [Category.assoc]

end HomPullbackComparison

end PushoutComparison

end CategoryTheory
