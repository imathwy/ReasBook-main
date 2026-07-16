import StacksProject_2024.stacks_project.Chap06.Lemma_6_31_7
import StacksProject_2024.stacks_project.Chap06.Definition_6_7_4
import StacksProject_2024.stacks_project.Chap20.ConstantIntegerSheaf
import Mathlib.Topology.LocallyConstant.Algebra

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open scoped TopCat

noncomputable section

universe u

section

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/-
Domain-style sampling for Lemma 20.20.6:
- primary domain: subobjects of abelian sheaves on a topological space, their restriction to an
  open subset, and the canonical constant sheaves with values `ℤ` and `dℤ`;
- sampled owner declarations:
  `constantIntegerSheaf`,
  sheaf restriction `↾` and `↾ₘ`,
  `CategoryTheory.Subobject.restrict`,
  `CategoryTheory.Subobject.mk`,
  `CategoryTheory.Subobject.arrow`,
  `constantSheaf`;
- best owner abstraction: the core owners are the sheaf restriction functor `↾` and the canonical
  subsheaf restriction owner `CategoryTheory.Subobject.restrict`, used via the canonical
  function surface `Subobject.restrict ℋ U : Subobject (𝒢 ↾ U)`;
- primitive data: the integer `d` and the subgroup inclusion `dℤ ↪ ℤ`;
- derived API: the ambient subobject `integerMultiplesSubobject X d`.
- source/core/bridge triage:
  `source-facing`: the existence of a nonempty open restriction on which `ℋ` agrees with
  `integerMultiplesSubobject X d`;
  `core/canonical`: `constantIntegerSheaf`, sheaf restriction `↾`, and
  `CategoryTheory.Subobject.restrict`;
  `bridge/view`: the concrete constant sheaf on `AddSubgroup.zmultiples d` and its induced
  monomorphism into `constantIntegerSheaf`, which should stay internal to the file because the
  reusable public owner is the ambient subobject. 
-/

/-- The constant abelian sheaf with value the subgroup `dℤ ⊆ ℤ`. -/
private abbrev integerMultiplesSheaf (Y : TopCat.{u}) (d : ℤ) :
    Y.Sheaf AddCommGrpCat.{u} :=
  ((constantSheaf
      (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ↥(AddSubgroup.zmultiples d))) : Y.Sheaf AddCommGrpCat.{u})

/-- The coefficient inclusion `ULift (dℤ) ⟶ ULift ℤ`. -/
private def integerMultiplesCoefficientInclusion (d : ℤ) :
    AddCommGrpCat.of (ULift.{u} ↥(AddSubgroup.zmultiples d)) ⟶ AddCommGrpCat.of (ULift.{u} ℤ) :=
  AddCommGrpCat.ofHom
    { toFun := fun n ↦ ⟨n.down.1⟩
      map_zero' := rfl
      map_add' := by
        intro a b
        rfl }

/-- The canonical inclusion of the constant sheaf with value `dℤ` into `constantIntegerSheaf Y`. -/
private def integerMultiplesSheafInclusion (Y : TopCat.{u}) (d : ℤ) :
    integerMultiplesSheaf Y d ⟶ constantIntegerSheaf Y :=
  (constantSheaf
      (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}).map <|
    integerMultiplesCoefficientInclusion d

private theorem integerMultiplesSheafInclusion_mono (Y : TopCat.{u}) (d : ℤ) :
    Mono (integerMultiplesSheafInclusion Y d) := by
  let f := integerMultiplesCoefficientInclusion d
  have hf : Mono f := by
    dsimp [f]
    refine (AddCommGrpCat.mono_iff_injective _).2 ?_
    rintro ⟨a⟩ ⟨b⟩ hab
    apply ULift.ext
    apply Subtype.ext
    exact congrArg ULift.down hab
  let F := constantSheaf
    (Opens.grothendieckTopology Y)
    AddCommGrpCat.{u}
  have hF : PreservesLimitsOfShape WalkingCospan F := by
    dsimp [F, CategoryTheory.constantSheaf]
    infer_instance
  letI : PreservesLimitsOfShape WalkingCospan F := hF
  simpa [integerMultiplesSheafInclusion, f, F] using
    (Functor.map_mono F f : Mono (F.map f))

/-- The canonical subobject of `constantIntegerSheaf Y` with sections in `dℤ`. -/
abbrev integerMultiplesSubobject (Y : TopCat.{u}) (d : ℤ) :
    Subobject (constantIntegerSheaf Y) :=
  letI := integerMultiplesSheafInclusion_mono Y d
  Subobject.mk (integerMultiplesSheafInclusion Y d)

omit [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] in
/-- Helper for Lemma 20.20.6: every nonempty open subspace of an irreducible space is itself
irreducible. -/
private theorem irreducibleSpaceOfOpenNeBot [IrreducibleSpace X]
    (U : Opens X) (hU : U ≠ ⊥) :
    IrreducibleSpace U := by
  -- Restrict the ambient irreducible set `Set.univ` to the open subset `U`.
  refine Subtype.irreducibleSpace ?_
  refine ⟨U.ne_bot_iff_nonempty.mp hU, ?_⟩
  simpa [Set.inter_univ] using
    (IrreducibleSpace.isIrreducible_univ X).isPreirreducible.open_subset U.2 (by simp)

/-- Helper for Lemma 20.20.6: every additive subgroup of `ℤ` is `nℤ` for some natural number
generator `n`. -/
private theorem exists_natGenerator_intSubgroup (H : AddSubgroup ℤ) :
    ∃ n : ℕ, H = AddSubgroup.zmultiples (n : ℤ) := by
  -- Normalize the cyclic generator from `Int.subgroup_cyclic` to its natural absolute value.
  rcases Int.subgroup_cyclic H with ⟨a, ha⟩
  refine ⟨a.natAbs, ?_⟩
  calc
    H = AddSubgroup.closure {a} := ha
    _ = AddSubgroup.zmultiples a := by
      simp [AddSubgroup.zmultiples_eq_closure]
    _ = AddSubgroup.zmultiples (a.natAbs : ℤ) := by
      simpa using (Int.zmultiples_natAbs a).symm

/-- Helper for Lemma 20.20.6: a strict enlargement of `nℤ` inside `ℤ` has a strictly smaller
positive natural generator. -/
private theorem natGenerator_lt_of_zmultiples_lt_zmultiples
    {n m : ℕ} (hn : n ≠ 0)
    (h : AddSubgroup.zmultiples (n : ℤ) < AddSubgroup.zmultiples (m : ℤ)) :
    m < n := by
  -- Membership of `n` in the larger subgroup records the divisibility `m ∣ n`.
  have hmn_mem : (n : ℤ) ∈ AddSubgroup.zmultiples (m : ℤ) := by
    exact h.1 (by simp)
  have hmn_dvd : m ∣ n := by
    rw [Int.mem_zmultiples_iff] at hmn_mem
    exact Int.natCast_dvd_natCast.mp hmn_mem
  have hmn_le : m ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hmn_dvd
  have hmn_ne : m ≠ n := by
    intro hmn_eq
    apply h.2
    subst hmn_eq
    rfl
  exact lt_of_le_of_ne hmn_le hmn_ne

/-- Helper for Lemma 20.20.6: on a nonempty irreducible open, evaluation at a point classifies
locally constant `ULift ℤ`-valued sections by the corresponding integer. -/
private noncomputable def locallyConstantIntegerEquivInt [IrreducibleSpace X]
    (U : Opens X) (hU : Nonempty U) :
    ↑((locallyConstantSheaf X (ULift.{u} ℤ)).1.obj (Opposite.op U)) ≃ ℤ where
  toFun s := (s.1 (Classical.choice hU)).down
  invFun n := ⟨fun _ ↦ (⟨n⟩ : ULift.{u} ℤ), IsLocallyConstant.const (⟨n⟩ : ULift.{u} ℤ)⟩
  left_inv s := by
    -- Every locally constant function on a nonempty irreducible open is constant.
    apply Subtype.ext
    funext x
    let x₀ : U := Classical.choice hU
    have hU_ne_bot : U ≠ ⊥ := by
      rw [U.ne_bot_iff_nonempty]
      exact ⟨x₀.1, x₀.2⟩
    have hconst : s.1 x = s.1 x₀ := by
      letI : IrreducibleSpace U :=
        irreducibleSpaceOfOpenNeBot (X := X) U hU_ne_bot
      simpa [x₀] using s.2.apply_eq_of_preconnectedSpace x x₀
    simpa [x₀] using hconst.symm
  right_inv n := by
    rfl

/-- Helper for Lemma 20.20.6: raw sections of `locallyConstantSheaf` are the usual
`LocallyConstant` functions on the open. -/
private def locallyConstantSectionEquivLocallyConstant
    (U : Opens X) :
    ↑((locallyConstantSheaf X (ULift.{u} ℤ)).1.obj (Opposite.op U)) ≃
      LocallyConstant U (ULift.{u} ℤ) where
  toFun s := ⟨s.1, s.2⟩
  invFun s := ⟨s, s.isLocallyConstant⟩
  left_inv s := rfl
  right_inv s := by
    ext x
    rfl

/-- Helper for Lemma 20.20.6: under `locallyConstantSectionEquivLocallyConstant`, evaluation at a
point is just evaluation of the underlying raw section. -/
private theorem locallyConstantSectionEquivLocallyConstant_apply
    (U : Opens X)
    (s : ↑((locallyConstantSheaf X (ULift.{u} ℤ)).1.obj (Opposite.op U)))
    (x : U) :
    locallyConstantSectionEquivLocallyConstant (X := X) U s x = s.1 x := rfl

/-- Helper for Lemma 20.20.6: transport the additive structure on locally constant functions to
raw sections of `locallyConstantSheaf`. -/
private noncomputable instance locallyConstantSectionAddCommGroup
    (U : Opens X) :
    AddCommGroup ↑((locallyConstantSheaf X (ULift.{u} ℤ)).1.obj (Opposite.op U)) :=
  Equiv.addCommGroup (locallyConstantSectionEquivLocallyConstant (X := X) U)

/-- Helper for Lemma 20.20.6: after identifying raw locally constant sections with
`LocallyConstant`, evaluation at a point is additive. -/
private noncomputable def locallyConstantIntegerAddEquivInt [IrreducibleSpace X]
    (U : Opens X) (hU : Nonempty U) :
    ↑((locallyConstantSheaf X (ULift.{u} ℤ)).1.obj (Opposite.op U)) ≃+ ℤ := by
  let x₀ : U := Classical.choice hU
  let eLC :
      LocallyConstant U (ULift.{u} ℤ) ≃+ ℤ :=
    { toFun := fun s ↦ (s x₀).down
      invFun := fun n ↦ LocallyConstant.const U (⟨n⟩ : ULift.{u} ℤ)
      left_inv := by
        intro s
        -- Proof comment: irreducibility forces every locally constant function on `U` to be
        -- constant, so evaluation at `x₀` recovers the whole section.
        ext x
        have hU_ne_bot : U ≠ ⊥ := by
          rw [U.ne_bot_iff_nonempty]
          exact ⟨x₀.1, x₀.2⟩
        letI : IrreducibleSpace U := irreducibleSpaceOfOpenNeBot (X := X) U hU_ne_bot
        simpa [x₀] using (s.isLocallyConstant.apply_eq_of_preconnectedSpace x x₀).symm
      right_inv := by
        intro n
        rfl
      map_add' := by
        intro s t
        rfl }
  -- Proof comment: convert the raw sheaf sections to the standard locally constant owner first,
  -- then evaluate there additively.
  exact (Equiv.addEquiv (locallyConstantSectionEquivLocallyConstant (X := X) U)).trans eLC

/-- Helper for Lemma 20.20.6: sections of `constantIntegerSheaf X` over a nonempty open are
classified by the integer they define there. -/
private noncomputable def constantIntegerSectionEquivInt [IrreducibleSpace X]
    (U : Opens X) (hU : Nonempty U) :
    ↑((constantIntegerSheaf X).1.obj (Opposite.op U)) ≃ ℤ := by
  let JX := Opens.grothendieckTopology X
  let A : AddCommGrpCat.{u} := AddCommGrpCat.of (ULift.{u} ℤ)
  let A' : Type u := ULift.{u} ℤ
  let E := constantCommuteCompose JX (forget AddCommGrpCat.{u})
  let eForgetU :
      (((CategoryTheory.sheafForget JX).obj (constantIntegerSheaf X)).1.obj (Opposite.op U)) ≅
        (((constantSheaf JX (Type u)).obj A').1.obj (Opposite.op U)) :=
    ((sheafToPresheaf JX (Type u)).mapIso (E.app A)).app (Opposite.op U)
  let eForgetEqv :
      ((constantIntegerSheaf X).1.obj (Opposite.op U)) ≃
        (((constantSheaf JX (Type u)).obj A').1.obj (Opposite.op U)) := by
    simpa [constantIntegerSheaf, CategoryTheory.sheafForget, TopCat.Sheaf.forget] using
      eForgetU.toEquiv
  let eTypeEqv :
      (((constantSheaf JX (Type u)).obj A').1.obj (Opposite.op U)) ≃
        ((locallyConstantSheaf X A').1.obj (Opposite.op U)) := by
    letI := constantSheafToLocallyConstantSheaf_app_isIso X A' U
    simpa using
      (asIso ((constantSheafToLocallyConstantSheaf X A').hom.app (Opposite.op U))).toEquiv
  exact Equiv.trans eForgetEqv
    (Equiv.trans eTypeEqv (locallyConstantIntegerEquivInt (X := X) U hU))

/-- Helper for Lemma 20.20.6: restricting a section of `constantIntegerSheaf X` to a smaller
nonempty open does not change the classified integer. -/
private theorem constantIntegerSectionEquivInt_naturality [IrreducibleSpace X]
    {U V : Opens X} (i : V ⟶ U) (hU : Nonempty U) (hV : Nonempty V)
    (s : ↑((constantIntegerSheaf X).1.obj (Opposite.op U))) :
    constantIntegerSectionEquivInt (X := X) V hV (((constantIntegerSheaf X).1.map i.op) s) =
      constantIntegerSectionEquivInt (X := X) U hU s := by
  let JX := Opens.grothendieckTopology X
  let A : AddCommGrpCat.{u} := AddCommGrpCat.of (ULift.{u} ℤ)
  let A' : Type u := ULift.{u} ℤ
  let E := constantCommuteCompose JX (forget AddCommGrpCat.{u})
  let eForgetU :
      (((CategoryTheory.sheafForget JX).obj (constantIntegerSheaf X)).1.obj (Opposite.op U)) ≅
        (((constantSheaf JX (Type u)).obj A').1.obj (Opposite.op U)) :=
    ((sheafToPresheaf JX (Type u)).mapIso (E.app A)).app (Opposite.op U)
  let eForgetV :
      (((CategoryTheory.sheafForget JX).obj (constantIntegerSheaf X)).1.obj (Opposite.op V)) ≅
        (((constantSheaf JX (Type u)).obj A').1.obj (Opposite.op V)) :=
    ((sheafToPresheaf JX (Type u)).mapIso (E.app A)).app (Opposite.op V)
  let eForgetU' :
      ((constantIntegerSheaf X).1.obj (Opposite.op U)) ≃
        (((constantSheaf JX (Type u)).obj A').1.obj (Opposite.op U)) := by
    simpa [constantIntegerSheaf, CategoryTheory.sheafForget, TopCat.Sheaf.forget] using
      eForgetU.toEquiv
  let eForgetV' :
      ((constantIntegerSheaf X).1.obj (Opposite.op V)) ≃
        (((constantSheaf JX (Type u)).obj A').1.obj (Opposite.op V)) := by
    simpa [constantIntegerSheaf, CategoryTheory.sheafForget, TopCat.Sheaf.forget] using
      eForgetV.toEquiv
  let eTypeU :
      (((constantSheaf JX (Type u)).obj A').1.obj (Opposite.op U)) ≃
        ((locallyConstantSheaf X A').1.obj (Opposite.op U)) := by
    letI := constantSheafToLocallyConstantSheaf_app_isIso X A' U
    simpa using
      (asIso ((constantSheafToLocallyConstantSheaf X A').hom.app (Opposite.op U))).toEquiv
  let eTypeV :
      (((constantSheaf JX (Type u)).obj A').1.obj (Opposite.op V)) ≃
        ((locallyConstantSheaf X A').1.obj (Opposite.op V)) := by
    letI := constantSheafToLocallyConstantSheaf_app_isIso X A' V
    simpa using
      (asIso ((constantSheafToLocallyConstantSheaf X A').hom.app (Opposite.op V))).toEquiv
  have hForget :
      eForgetV' (((constantIntegerSheaf X).1.map i.op) s) =
        (((constantSheaf JX (Type u)).obj A').1.map i.op) (eForgetU' s) := by
    -- Proof comment: first commute restriction past the `sheafForget` comparison.
    simpa [eForgetU, eForgetV, eForgetU', eForgetV', CategoryTheory.sheafForget,
      TopCat.Sheaf.forget] using
      congrFun (((sheafToPresheaf JX (Type u)).mapIso (E.app A)).hom.naturality i.op) s
  have hType :
      eTypeV ((((constantSheaf JX (Type u)).obj A').1.map i.op) (eForgetU' s)) =
        ((locallyConstantSheaf X A').1.map i.op) (eTypeU (eForgetU' s)) := by
    -- Proof comment: then commute the same restriction through the locally constant comparison.
    change
      ((constantSheafToLocallyConstantSheaf X A').hom.app (Opposite.op V))
          ((((constantSheaf JX (Type u)).obj A').1.map i.op) (eForgetU' s)) =
        ((locallyConstantSheaf X A').1.map i.op)
          (((constantSheafToLocallyConstantSheaf X A').hom.app (Opposite.op U)) (eForgetU' s))
    exact congrFun ((constantSheafToLocallyConstantSheaf X A').hom.naturality i.op) (eForgetU' s)
  have hLocallyConstant :
      locallyConstantIntegerEquivInt (X := X) V hV
          (((locallyConstantSheaf X A').1.map i.op) (eTypeU (eForgetU' s))) =
        locallyConstantIntegerEquivInt (X := X) U hU (eTypeU (eForgetU' s)) := by
    let xV : V := Classical.choice hV
    let xU : U := Classical.choice hU
    have hValue :
        (eTypeU (eForgetU' s)).1 ⟨xV.1, i.le xV.2⟩ = (eTypeU (eForgetU' s)).1 xU := by
      -- Proof comment: a locally constant function on the irreducible open `U` is constant.
      have hU_ne_bot : U ≠ ⊥ := by
        rw [U.ne_bot_iff_nonempty]
        exact ⟨xU.1, xU.2⟩
      letI : IrreducibleSpace U := irreducibleSpaceOfOpenNeBot (X := X) U hU_ne_bot
      simpa [xU] using (eTypeU (eForgetU' s)).2.apply_eq_of_preconnectedSpace
        ⟨xV.1, i.le xV.2⟩ xU
    change (((((locallyConstantSheaf X A').1.map i.op) (eTypeU (eForgetU' s))).1 xV).down) =
      (((eTypeU (eForgetU' s)).1 xU).down)
    simpa [xV] using congrArg ULift.down hValue
  -- Proof comment: after both transport steps are normalized, the classifier reduces to the
  -- obvious locally constant naturality statement.
  change
    locallyConstantIntegerEquivInt (X := X) V hV
        (eTypeV (eForgetV' (((constantIntegerSheaf X).1.map i.op) s))) =
      locallyConstantIntegerEquivInt (X := X) U hU (eTypeU (eForgetU' s))
  rw [hForget]
  rw [hType]
  exact hLocallyConstant

/-- Helper for Lemma 20.20.6: restriction from the top open to a nonempty open is bijective on
sections of `constantIntegerSheaf X`. -/
private theorem constantIntegerSectionRestriction_bijective [IrreducibleSpace X]
    (U : Opens X) (hU : Nonempty U)
    :
    Function.Bijective
      (((constantIntegerSheaf X).1.map
        (show U ⟶ (⊤ : Opens X) from homOfLE (by intro x _; trivial)).op)) := by
  let i : U ⟶ (⊤ : Opens X) := homOfLE (by intro x _; trivial)
  have hTop : Nonempty (⊤ : Opens X) := by
    rcases (IrreducibleSpace.toNonempty : Nonempty X) with ⟨x⟩
    exact ⟨⟨x, by trivial⟩⟩
  constructor
  · intro s t hst
    -- Proof comment: equal restrictions have the same classified integer, hence coincide already
    -- on the top open.
    apply (constantIntegerSectionEquivInt (X := X) ⊤ hTop).injective
    rw [← constantIntegerSectionEquivInt_naturality (X := X) i hTop hU s]
    rw [← constantIntegerSectionEquivInt_naturality (X := X) i hTop hU t]
    simpa [hst]
  · intro s
    -- Proof comment: choose the unique top section with the same classified integer as `s`.
    let sTop : ↑((constantIntegerSheaf X).1.obj (Opposite.op (⊤ : Opens X))) :=
      (constantIntegerSectionEquivInt (X := X) ⊤ hTop).symm
        (constantIntegerSectionEquivInt (X := X) U hU s)
    refine ⟨sTop, ?_⟩
    apply (constantIntegerSectionEquivInt (X := X) U hU).injective
    rw [constantIntegerSectionEquivInt_naturality (X := X) i hTop hU sTop]
    simp [sTop]

/-- Helper for Lemma 20.20.6: the restriction map from the top open to a nonempty open transports
sections of `constantIntegerSheaf X` additively. -/
private noncomputable def constantIntegerSectionRestrictionAddEquiv [IrreducibleSpace X]
    (U : Opens X) (hU : Nonempty U) :
    ↑((constantIntegerSheaf X).1.obj (Opposite.op (⊤ : Opens X))) ≃+
      ↑((constantIntegerSheaf X).1.obj (Opposite.op U)) := by
  let i : U ⟶ (⊤ : Opens X) := homOfLE (by intro x _; trivial)
  -- Proof comment: the top restriction map already has a bijectivity proof, so `AddEquiv` can
  -- package the same transport without any new section-level calculations.
  exact AddEquiv.ofBijective (ConcreteCategory.hom ((constantIntegerSheaf X).1.map i.op))
    (constantIntegerSectionRestriction_bijective (X := X) U hU)

/-- Helper for Lemma 20.20.6: the ambient section classifier should be upgraded to an additive
equivalence before forming local subgroups. -/
private noncomputable def constantIntegerSectionValueAddEquiv [IrreducibleSpace X]
    (U : Opens X) (hU : Nonempty U) :
    ↑((constantIntegerSheaf X).1.obj (Opposite.op U)) ≃+ ℤ where
  toEquiv := constantIntegerSectionEquivInt (X := X) U hU
  map_add' := by
    -- Route correction: the bad route was to keep unfolding the arbitrary-open
    -- `constantSheafToLocallyConstantSheaf` transport here. The remaining missing step is a single
    -- owner-level theorem that this transport preserves addition on ambient integer sections.
    -- TODO: replace this placeholder with the top-open additive bridge and transport back to `U`,
    -- or prove directly that the section map of `constantSheafToLocallyConstantSheaf` is additive
    -- after the `constantCommuteCompose` comparison.
    sorry

/-- Helper for Lemma 20.20.6: on a nonempty irreducible open, the section classifier for
`constantIntegerSheaf X` is additive. -/
private noncomputable def constantIntegerSectionValueHom [IrreducibleSpace X]
    (U : Opens X) (hU : Nonempty U) :
    ↑((constantIntegerSheaf X).1.obj (Opposite.op U)) →+ ℤ :=
  (constantIntegerSectionValueAddEquiv (X := X) U hU).toAddMonoidHom

/-- Helper for Lemma 20.20.6: shrinking a nonempty open does not change the classified integer of
an ambient section. -/
private theorem constantIntegerSectionValueHom_naturality [IrreducibleSpace X]
    {U V : Opens X} (i : V ⟶ U) (hU : Nonempty U) (hV : Nonempty V)
    (s : ↑((constantIntegerSheaf X).1.obj (Opposite.op U))) :
    constantIntegerSectionValueHom (X := X) V hV (((constantIntegerSheaf X).1.map i.op) s) =
      constantIntegerSectionValueHom (X := X) U hU s :=
  constantIntegerSectionEquivInt_naturality (X := X) i hU hV s

/-- Helper for Lemma 20.20.6: the integers realized by sections of `ℋ` on a nonempty open form an
additive subgroup of `ℤ`. -/
private def localSectionSubgroup [IrreducibleSpace X]
    (ℋ : Subobject (constantIntegerSheaf X)) (U : Opens X) (hU : Nonempty U) : AddSubgroup ℤ where
  carrier :=
    { z : ℤ |
        ∃ t : ↑((Subobject.underlying.obj ℋ).1.obj (Opposite.op U)),
          constantIntegerSectionValueHom (X := X) U hU
              (((ℋ.arrow.hom.app (Opposite.op U)).hom) t) = z }
  zero_mem' := by
    -- Proof comment: the zero section of the subsheaf realizes the integer `0`.
    refine ⟨0, ?_⟩
    calc
      constantIntegerSectionValueHom (X := X) U hU (((ℋ.arrow.hom.app (Opposite.op U)).hom) 0)
          = constantIntegerSectionValueHom (X := X) U hU 0 := by
              rw [map_zero]
      _ = 0 := (constantIntegerSectionValueHom (X := X) U hU).map_zero
  add_mem' := by
    intro a b ha hb
    rcases ha with ⟨sa, hsa⟩
    rcases hb with ⟨sb, hsb⟩
    -- Proof comment: the subobject arrow is additive on sections, so sums of witnesses remain
    -- witnesses.
    refine ⟨sa + sb, ?_⟩
    calc
      constantIntegerSectionValueHom (X := X) U hU (((ℋ.arrow.hom.app (Opposite.op U)).hom) (sa + sb))
          = constantIntegerSectionValueHom (X := X) U hU
              ((((ℋ.arrow.hom.app (Opposite.op U)).hom) sa) +
                (((ℋ.arrow.hom.app (Opposite.op U)).hom) sb)) := by
                  rw [map_add]
      _ = constantIntegerSectionValueHom (X := X) U hU (((ℋ.arrow.hom.app (Opposite.op U)).hom) sa) +
            constantIntegerSectionValueHom (X := X) U hU (((ℋ.arrow.hom.app (Opposite.op U)).hom) sb) := by
              rw [(constantIntegerSectionValueHom (X := X) U hU).map_add]
      _ = a + b := by rw [hsa, hsb]
  neg_mem' := by
    intro a ha
    rcases ha with ⟨sa, hsa⟩
    -- Proof comment: the additive inverse of a witnessing section realizes the negative integer.
    refine ⟨-sa, ?_⟩
    calc
      constantIntegerSectionValueHom (X := X) U hU (((ℋ.arrow.hom.app (Opposite.op U)).hom) (-sa))
          = constantIntegerSectionValueHom (X := X) U hU (-(((ℋ.arrow.hom.app (Opposite.op U)).hom) sa)) := by
              rw [map_neg]
      _ = -(constantIntegerSectionValueHom (X := X) U hU (((ℋ.arrow.hom.app (Opposite.op U)).hom) sa)) := by
            rw [(constantIntegerSectionValueHom (X := X) U hU).map_neg]
      _ = -a := by rw [hsa]

/-- Helper for Lemma 20.20.6: realized integer subgroups enlarge when the open set shrinks. -/
private theorem localSectionSubgroup_mono [IrreducibleSpace X]
    (ℋ : Subobject (constantIntegerSheaf X)) {U V : Opens X} (i : V ⟶ U)
    (hU : Nonempty U) (hV : Nonempty V) :
    localSectionSubgroup (X := X) ℋ U hU ≤ localSectionSubgroup (X := X) ℋ V hV := by
  intro z hz
  rcases hz with ⟨t, ht⟩
  refine ⟨((Subobject.underlying.obj ℋ).val.map i.op) t, ?_⟩
  -- Proof comment: restrict the witnessing section through the subsheaf and then use naturality of
  -- the integer classifier.
  rw [← ht]
  have hArrow :
      (((ℋ.arrow.hom.app (Opposite.op V)).hom) (((Subobject.underlying.obj ℋ).val.map i.op) t)) =
        ((constantIntegerSheaf X).1.map i.op) ((((ℋ.arrow.hom.app (Opposite.op U)).hom) t)) := by
    simpa using congrArg (fun g ↦ g.hom t) (ℋ.arrow.hom.naturality i.op)
  rw [hArrow]
  simpa using
    constantIntegerSectionValueHom_naturality (X := X) i hU hV
      ((((ℋ.arrow.hom.app (Opposite.op U)).hom) t))

/-- Helper for Lemma 20.20.6: every realized subgroup on a nonempty irreducible open is some
`nℤ`. -/
private theorem localSectionSubgroup_eq_zmultiples [IrreducibleSpace X]
    (ℋ : Subobject (constantIntegerSheaf X)) (U : Opens X) (hU : Nonempty U) :
    ∃ n : ℕ, localSectionSubgroup (X := X) ℋ U hU = AddSubgroup.zmultiples (n : ℤ) := by
  -- Proof comment: once the local integer values form an additive subgroup of `ℤ`, cyclicity of
  -- integer subgroups provides the generator.
  exact exists_natGenerator_intSubgroup (localSectionSubgroup (X := X) ℋ U hU)

/-- Helper for Lemma 20.20.6: a minimal positive generator on `U` forces the same subgroup on
every smaller nonempty open. -/
private theorem localSectionSubgroup_eq_zmultiples_of_minimalPositive [IrreducibleSpace X]
    (ℋ : Subobject (constantIntegerSheaf X)) {U : Opens X} (hU : Nonempty U)
    {n : ℕ} (hn : n ≠ 0)
    (hLocal : localSectionSubgroup (X := X) ℋ U hU = AddSubgroup.zmultiples (n : ℤ))
    (hMinimal :
      ∀ {V : Opens X} (hV : Nonempty V) {m : ℕ},
        localSectionSubgroup (X := X) ℋ V hV = AddSubgroup.zmultiples (m : ℤ) →
          n ≤ m)
    {V : Opens X} (i : V ⟶ U) (hV : Nonempty V) :
    localSectionSubgroup (X := X) ℋ V hV = AddSubgroup.zmultiples (n : ℤ) := by
  rcases localSectionSubgroup_eq_zmultiples (X := X) ℋ V hV with ⟨m, hm⟩
  have hnm : n ≤ m := hMinimal hV hm
  have hle : AddSubgroup.zmultiples (n : ℤ) ≤ AddSubgroup.zmultiples (m : ℤ) := by
    simpa [hLocal, hm] using localSectionSubgroup_mono (X := X) ℋ i hU hV
  -- Proof comment: a strict enlargement would force a strictly smaller positive generator on `V`,
  -- contradicting minimality of `n`.
  by_cases hEq : AddSubgroup.zmultiples (n : ℤ) = AddSubgroup.zmultiples (m : ℤ)
  · simpa [hm] using hEq.symm
  · have hlt : AddSubgroup.zmultiples (n : ℤ) < AddSubgroup.zmultiples (m : ℤ) :=
      lt_of_le_of_ne hle hEq
    have hm_lt_n : m < n :=
      natGenerator_lt_of_zmultiples_lt_zmultiples hn hlt
    exact False.elim ((Nat.not_lt_of_ge hnm) hm_lt_n)

-- Proof sketch: on an irreducible space, every nonempty open subset has only constant sections in
-- `constantIntegerSheaf X`. The subgroup cut out by `ℋ` on a nonempty open is therefore some
-- `nℤ`, and if this subgroup is not yet locally constant one can
-- shrink to a smaller nonempty open with strictly smaller positive generator; well-foundedness of
-- the positive integers forces this process to stop.
/-- Lemma 20.20.6: for a subobject `ℋ` of `constantIntegerSheaf X` on an irreducible space, there
is a nonempty open subset on which the restricted subobject agrees with the restriction of
`integerMultiplesSubobject X d` for some integer `d`. -/
@[stacks 02UY]
theorem exists_nonempty_open_restrict_eq_integerMultiplesSubobject
    [IrreducibleSpace X] (ℋ : Subobject (constantIntegerSheaf X)) :
    ∃ (U : Opens X) (hU : Nonempty U) (d : ℤ),
      Subobject.restrict ℋ U = Subobject.restrict (integerMultiplesSubobject X d) U := by
  classical
  have hTop : Nonempty (⊤ : Opens X) := by
    rcases (IrreducibleSpace.toNonempty : Nonempty X) with ⟨x⟩
    exact ⟨⟨x, by trivial⟩⟩
  by_cases hPositive :
      ∃ n : ℕ, 0 < n ∧
        ∃ (U : Opens X) (hU : Nonempty U),
          localSectionSubgroup (X := X) ℋ U hU = AddSubgroup.zmultiples (n : ℤ)
  · let positiveWitnesses : Set ℕ :=
      { n : ℕ |
          0 < n ∧
            ∃ (U : Opens X) (hU : Nonempty U),
              localSectionSubgroup (X := X) ℋ U hU = AddSubgroup.zmultiples (n : ℤ) }
    have hPositiveWitnesses : ∃ n, n ∈ positiveWitnesses := by
      rcases hPositive with ⟨n, hn, U, hU, hLocal⟩
      exact ⟨n, hn, U, hU, hLocal⟩
    let n : ℕ := Nat.find hPositiveWitnesses
    rcases Nat.find_spec hPositiveWitnesses with ⟨hnPos, U, hU, hLocal⟩
    have hn_ne_zero : n ≠ 0 := Nat.pos_iff_ne_zero.mp hnPos
    have hMinimal :
        ∀ {V : Opens X} (hV : Nonempty V) {m : ℕ},
          localSectionSubgroup (X := X) ℋ V hV = AddSubgroup.zmultiples (m : ℤ) →
            0 < m → n ≤ m := by
      intro V hV m hm hmPos
      exact Nat.find_min' hPositiveWitnesses ⟨hmPos, V, hV, hm⟩
    have hStableOnSmaller :
        ∀ {V : Opens X} (i : V ⟶ U) (hV : Nonempty V),
          localSectionSubgroup (X := X) ℋ V hV = AddSubgroup.zmultiples (n : ℤ) := by
      intro V i hV
      rcases localSectionSubgroup_eq_zmultiples (X := X) ℋ V hV with ⟨m, hm⟩
      have hle : AddSubgroup.zmultiples (n : ℤ) ≤ AddSubgroup.zmultiples (m : ℤ) := by
        simpa [hLocal, hm] using localSectionSubgroup_mono (X := X) ℋ i hU hV
      by_cases hmZero : m = 0
      · have hn_zero : (n : ℤ) = 0 := by
          simpa [hmZero] using hle (by simp : (n : ℤ) ∈ AddSubgroup.zmultiples (n : ℤ))
        exact False.elim (hn_ne_zero (by simpa using hn_zero))
      · have hnm : n ≤ m :=
          hMinimal (V := V) hV hm (Nat.pos_iff_ne_zero.mpr hmZero)
        by_cases hEq : AddSubgroup.zmultiples (n : ℤ) = AddSubgroup.zmultiples (m : ℤ)
        · simpa [hm] using hEq.symm
        · have hlt : AddSubgroup.zmultiples (n : ℤ) < AddSubgroup.zmultiples (m : ℤ) :=
            lt_of_le_of_ne hle hEq
          have hm_lt_n := natGenerator_lt_of_zmultiples_lt_zmultiples hn_ne_zero hlt
          exact False.elim ((Nat.not_lt_of_ge hnm) hm_lt_n)
    refine ⟨U, hU, (n : ℤ), ?_⟩
    -- Proof comment: the positive-generator branch now has the right stabilized invariant.
    -- TODO: use `hStableOnSmaller` together with the restriction bridge and the computation for
    -- `integerMultiplesSubobject X (n : ℤ)` to convert the stable local subgroup `nℤ` into
    -- equality of the two restricted subobjects.
    sorry
  · have hAllZero :
        ∀ (U : Opens X) (hU : Nonempty U),
          localSectionSubgroup (X := X) ℋ U hU = AddSubgroup.zmultiples (0 : ℤ) := by
      intro U hU
      rcases localSectionSubgroup_eq_zmultiples (X := X) ℋ U hU with ⟨n, hn⟩
      by_cases hnZero : n = 0
      · simpa [hnZero] using hn
      · exfalso
        apply hPositive
        exact ⟨n, Nat.pos_iff_ne_zero.mpr hnZero, U, hU, hn⟩
    refine ⟨⊤, hTop, 0, ?_⟩
    -- Proof comment: the zero branch now isolates the genuine remaining bridge.
    -- TODO: compare `Subobject.restrict ℋ ⊤` with the zero multiple subsheaf using `hAllZero`,
    -- after normalizing restricted local sections against the ambient subgroup invariant.
    sorry

/-- Lemma `20.20.6` in conjunction form: on some nonempty open, the restricted subobject `ℋ`
agrees with the restriction of `integerMultiplesSubobject X d` for a suitable integer `d`. -/
theorem exists_nonempty_open_and_restrict_eq_integerMultiplesSubobject
    [IrreducibleSpace X] (ℋ : Subobject (constantIntegerSheaf X)) :
    ∃ U : Opens X, Nonempty U ∧
      ∃ d : ℤ,
        Subobject.restrict ℋ U = Subobject.restrict (integerMultiplesSubobject X d) U := by
  rcases exists_nonempty_open_restrict_eq_integerMultiplesSubobject ℋ with
    ⟨U, hU, d, hd⟩
  exact ⟨U, hU, d, hd⟩

end
