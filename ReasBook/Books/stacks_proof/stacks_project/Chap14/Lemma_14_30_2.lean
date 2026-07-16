import Mathlib
import stacks_proof.stacks_project.Chap14.Lemma_14_21_7
import stacks_proof.stacks_project.Chap14.Definition_14_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MorphismProperty Opposite Simplicial
open SSet.modelCategoryQuillen

universe u

section

variable {X Y : SSet.{u}} {f : X ⟶ Y}

/- Domain-style sampling for Lemma 14.30.2:
- primary domain: simplicial-set lifting properties and monomorphisms in the Quillen model
  structure;
- sampled owner declarations:
  `SSet.modelCategoryQuillen.I.rlp`,
  `CategoryTheory.MorphismProperty.monomorphisms`,
  `CategoryTheory.MorphismProperty.rlp`,
  `CategoryTheory.HasLiftingProperty`;
- best owner abstraction: `(monomorphisms SSet).rlp`;
- primitive data: the morphism `f` together with the owner property `I.rlp f` from
  Definition 14.30.1;
- derived API: the pointwise lifting statement `HasLiftingProperty i f` for a chosen monomorphism
  `i`.

Source/core/bridge triage:
- `source-facing`: a trivial Kan fibration lifts against every monomorphism of simplicial sets;
- `core/canonical`: `(monomorphisms SSet).rlp f`;
- `bridge/view`: evaluation of that owner property on a particular monomorphism `i`. -/

-- Proof sketch: reinterpret a trivial Kan fibration via
-- `I.rlp`, identify termwise injective maps of
-- simplicial sets with monomorphisms, and then use the standard closure argument to upgrade the
-- owner property from the generating boundary inclusions to all monomorphisms.
/-- Helper for Lemma 14.30.2: lifting against a monomorphism is equivalent to lifting against the
canonical inclusion of its simplicial-image subcomplex. -/
lemma range_inclusion_hasLiftingProperty_iff {Z W : SSet.{u}} (i : Z ⟶ W) [Mono i] :
    HasLiftingProperty i f ↔ HasLiftingProperty (SSet.Subcomplex.range i).ι f := by
  -- The range factorization identifies `i` with the inclusion of its image, so we transport the
  -- lifting property across that arrow isomorphism.
  have hIso : IsIso (SSet.Subcomplex.toRange i) := by
    -- The map to the range is pointwise bijective once `i` is pointwise injective.
    rw [NatTrans.isIso_iff_isIso_app]
    intro Δ
    rw [isIso_iff_bijective]
    constructor
    · rw [← mono_iff_injective]
      infer_instance
    · rw [← epi_iff_surjective]
      infer_instance
  obtain ⟨inv, hinv, invh⟩ := hIso.out
  let eLeft : Z ≅ (SSet.Subcomplex.range i).toSSet :=
    { hom := SSet.Subcomplex.toRange i
      inv := inv
      hom_inv_id := hinv
      inv_hom_id := invh }
  let e : Arrow.mk i ≅ Arrow.mk (SSet.Subcomplex.range i).ι :=
    Arrow.isoMk eLeft (Iso.refl _) rfl
  exact HasLiftingProperty.iff_of_arrow_iso_left e f

/-- Helper for Lemma 14.30.2: it is enough to solve lifting problems for inclusions of simplicial
subcomplexes that arise as the range of a monomorphism. -/
lemma monomorphisms_rlp_iff_range_inclusions :
    (monomorphisms SSet).rlp f ↔
      ∀ ⦃Z W : SSet.{u}⦄ (i : Z ⟶ W) [Mono i],
        HasLiftingProperty (SSet.Subcomplex.range i).ι f := by
  constructor
  · intro h Z W i _
    -- Evaluate the owner predicate on `i`, then transport the lift to the range inclusion.
    exact (range_inclusion_hasLiftingProperty_iff (f := f) i).1 (h i inferInstance)
  · intro h Z W i _
    -- Conversely, a lift for the range inclusion transports back to a lift for `i`.
    exact (range_inclusion_hasLiftingProperty_iff (f := f) i).2 (h i)

/-- Helper for Lemma 14.30.2: a partial lift of a square over the range inclusion of a
monomorphism consists of a supporting subcomplex of the target together with a compatible lift on
that subcomplex. -/
structure PartialLift {Z W : SSet.{u}} (i : Z ⟶ W) [Mono i]
    (a : W ⟶ Y) (b : (SSet.Subcomplex.range i : SSet) ⟶ X) where
  A : W.Subcomplex
  hrange : SSet.Subcomplex.range i ≤ A
  lift : (A : SSet) ⟶ X
  fac_base : SSet.Subcomplex.homOfLE hrange ≫ lift = b
  fac_target : lift ≫ f = A.ι ≫ a

namespace PartialLift

/-- Helper for Lemma 14.30.2: partial lifts are ordered by enlarging the supporting subcomplex
while restricting the larger lift back to the smaller one. -/
instance instPreorder {Z W : SSet.{u}} (i : Z ⟶ W) [Mono i]
    {a : W ⟶ Y} {b : (SSet.Subcomplex.range i : SSet) ⟶ X} :
    Preorder (PartialLift (f := f) i a b) where
  le p q := ∃ hA : p.A ≤ q.A, SSet.Subcomplex.homOfLE hA ≫ q.lift = p.lift
  le_refl p := by
    -- The support does not change, so the restriction map is the identity.
    refine ⟨le_rfl, ?_⟩
    simp
  le_trans p q r hpq hqr := by
    rcases hpq with ⟨hpqA, hpqeq⟩
    rcases hqr with ⟨hqrA, hqreq⟩
    refine ⟨hpqA.trans hqrA, ?_⟩
    -- Restricting twice is the same as restricting once along the composite inclusion.
    have hcomp :
        SSet.Subcomplex.homOfLE (hpqA.trans hqrA) =
          SSet.Subcomplex.homOfLE hpqA ≫ SSet.Subcomplex.homOfLE hqrA := by
      ext Δ x
      rfl
    calc
      SSet.Subcomplex.homOfLE (hpqA.trans hqrA) ≫ r.lift =
          (SSet.Subcomplex.homOfLE hpqA ≫ SSet.Subcomplex.homOfLE hqrA) ≫ r.lift := by
            rw [hcomp]
      _ = SSet.Subcomplex.homOfLE hpqA ≫ (SSet.Subcomplex.homOfLE hqrA ≫ r.lift) := by
            simp [Category.assoc]
      _ = SSet.Subcomplex.homOfLE hpqA ≫ q.lift := by
            rw [hqreq]
      _ = p.lift := hpqeq

/-- Helper for Lemma 14.30.2: unpacking the preorder relation gives the support inclusion and the
restriction identity for the larger lift. -/
lemma le_def {Z W : SSet.{u}} (i : Z ⟶ W) [Mono i]
    {a : W ⟶ Y} {b : (SSet.Subcomplex.range i : SSet) ⟶ X}
    {p q : PartialLift (f := f) i a b} :
    p ≤ q ↔ ∃ hA : p.A ≤ q.A, SSet.Subcomplex.homOfLE hA ≫ q.lift = p.lift :=
  Iff.rfl

/-- Helper for Lemma 14.30.2: a larger partial lift restricts to a smaller one along the stored
support inclusion. -/
lemma restriction_eq {Z W : SSet.{u}} (i : Z ⟶ W) [Mono i]
    {a : W ⟶ Y} {b : (SSet.Subcomplex.range i : SSet) ⟶ X}
    {p q : PartialLift (f := f) i a b} (h : p ≤ q) :
    SSet.Subcomplex.homOfLE h.1 ≫ q.lift = p.lift :=
  h.2

/-- Helper for Lemma 14.30.2: along a chain of partial lifts, two lifts agree on any simplex that
lies in both supporting subcomplexes. -/
lemma chain_value_eq_of_overlap {Z W : SSet.{u}} (i : Z ⟶ W) [Mono i]
    {a : W ⟶ Y} {b : (SSet.Subcomplex.range i : SSet) ⟶ X}
    {c : Set (PartialLift (f := f) i a b)}
    (hc : IsChain (fun p q : PartialLift (f := f) i a b => p ≤ q) c)
    {p q : PartialLift (f := f) i a b} (hp : p ∈ c) (hq : q ∈ c)
    {Δ : SimplexCategoryᵒᵖ} {w : W.obj Δ}
    (hw_p : w ∈ p.A.obj Δ) (hw_q : w ∈ q.A.obj Δ) :
    p.lift.app Δ ⟨w, hw_p⟩ = q.lift.app Δ ⟨w, hw_q⟩ := by
  rcases hc.total hp hq with hpq | hqp
  · -- Compare by restricting the larger partial lift down to `p`.
    have hrest := restriction_eq (f := f) i hpq
    have happ := congrArg (fun k ↦ k.app Δ ⟨w, hw_p⟩) hrest
    simpa using happ.symm
  · -- The symmetric comparison gives the same conclusion when `q ≤ p`.
    have hrest := restriction_eq (f := f) i hqp
    have happ := congrArg (fun k ↦ k.app Δ ⟨w, hw_q⟩) hrest
    simpa using happ

/-- Helper for Lemma 14.30.2: the support of a family of partial lifts is the supremum of their
supporting subcomplexes. -/
abbrev chainSupport {Z W : SSet.{u}} (i : Z ⟶ W) [Mono i]
    {a : W ⟶ Y} {b : (SSet.Subcomplex.range i : SSet) ⟶ X}
    (c : Set (PartialLift (f := f) i a b)) : W.Subcomplex :=
  ⨆ p : c, (p : PartialLift (f := f) i a b).A

/-- Helper for Lemma 14.30.2: a simplex lies in the support of a family of partial lifts exactly
when it lies in the support of one stage in the family. -/
lemma chain_support_obj {Z W : SSet.{u}} (i : Z ⟶ W) [Mono i]
    {a : W ⟶ Y} {b : (SSet.Subcomplex.range i : SSet) ⟶ X}
    (c : Set (PartialLift (f := f) i a b))
    {Δ : SimplexCategoryᵒᵖ} {w : W.obj Δ} :
    w ∈ (chainSupport (f := f) i c).obj Δ ↔
      ∃ p : c, w ∈ p.1.A.obj Δ := by
  -- Proof comment: the support is a subtype-indexed supremum, so objectwise membership is exactly
  -- `Set.mem_iUnion`.
  simp only [chainSupport, Subfunctor.iSup_obj, Set.mem_iUnion]

/-- Helper for Lemma 14.30.2: if one stage in the family contains a simplex, then the family
support also contains it. -/
lemma mem_chainSupport_of_mem {Z W : SSet.{u}} (i : Z ⟶ W) [Mono i]
    {a : W ⟶ Y} {b : (SSet.Subcomplex.range i : SSet) ⟶ X}
    {c : Set (PartialLift (f := f) i a b)}
    {p : c} {Δ : SimplexCategoryᵒᵖ} {w : W.obj Δ}
    (hw : w ∈ p.1.A.obj Δ) :
    w ∈ (chainSupport (f := f) i c).obj Δ := by
  -- Proof comment: insert the chosen stage as the witness in the pointwise union description.
  exact (chain_support_obj (f := f) i c).2 ⟨p, hw⟩

/-- Helper for Lemma 14.30.2: the range inclusion of the original monomorphism lands in the
support of any nonempty family of partial lifts. -/
lemma range_le_chainSupport {Z W : SSet.{u}} (i : Z ⟶ W) [Mono i]
    {a : W ⟶ Y} {b : (SSet.Subcomplex.range i : SSet) ⟶ X}
    {c : Set (PartialLift (f := f) i a b)}
    (hc : c.Nonempty) :
    SSet.Subcomplex.range i ≤ chainSupport (f := f) i c := by
  rcases hc with ⟨p, hp⟩
  intro Δ w hw
  -- Proof comment: every partial lift support contains the original range, so one nonempty stage
  -- already places the range inside the union support.
  exact mem_chainSupport_of_mem (f := f) i (p := ⟨p, hp⟩) (p.hrange _ hw)

/-- Helper for Lemma 14.30.2: every stage in a family of partial lifts maps into the family
support. -/
lemma le_chainSupport_of_mem {Z W : SSet.{u}} (i : Z ⟶ W) [Mono i]
    {a : W ⟶ Y} {b : (SSet.Subcomplex.range i : SSet) ⟶ X}
    {c : Set (PartialLift (f := f) i a b)}
    {r : PartialLift (f := f) i a b} (hr : r ∈ c) :
    r.A ≤ chainSupport (f := f) i c := by
  intro Δ w hw
  -- Proof comment: include the chosen stage `r` as a witness in the objectwise union support.
  exact mem_chainSupport_of_mem (f := f) i (p := ⟨r, hr⟩) hw

/-- Helper for Lemma 14.30.2: a nonempty chain of compatible partial lifts carries a canonical
lift on the union of its supporting subcomplexes. -/
lemma chain_support_lift {Z W : SSet.{u}} (i : Z ⟶ W) [Mono i]
    {a : W ⟶ Y} {b : (SSet.Subcomplex.range i : SSet) ⟶ X}
    {c : Set (PartialLift (f := f) i a b)}
    (hc : c.Nonempty)
    (hchain : IsChain (fun p q : PartialLift (f := f) i a b => p ≤ q) c) :
    ∃ ell : (chainSupport (f := f) i c : SSet) ⟶ X,
      SSet.Subcomplex.homOfLE (range_le_chainSupport (f := f) i hc) ≫ ell = b ∧
      (∀ ⦃r : PartialLift (f := f) i a b⦄ (hr : r ∈ c),
        SSet.Subcomplex.homOfLE (le_chainSupport_of_mem (f := f) i hr) ≫ ell = r.lift) ∧
      ell ≫ f = (chainSupport (f := f) i c).ι ≫ a := by
  classical
  let stage :
      ∀ {Δ : SimplexCategoryᵒᵖ}, (chainSupport (f := f) i c).obj Δ → c :=
    fun s ↦ Classical.choose ((chain_support_obj (f := f) i c).1 s.2)
  let stage_mem :
      ∀ {Δ : SimplexCategoryᵒᵖ} (s : (chainSupport (f := f) i c).obj Δ),
        s.1 ∈ (stage s).1.A.obj Δ :=
    fun s ↦ Classical.choose_spec ((chain_support_obj (f := f) i c).1 s.2)
  refine ⟨
    { app := fun Δ s ↦ (stage s).1.lift.app Δ ⟨s.1, stage_mem s⟩
      naturality := ?_ },
    ?_,
    ?_,
    ?_⟩
  · intro Δ Δ' θ
    ext s
    let s' : (chainSupport (f := f) i c).obj Δ' :=
      ((chainSupport (f := f) i c : SSet).map θ s)
    have hs'_mem : s'.1 ∈ (stage s).1.A.obj Δ' := by
      -- Proof comment: the chosen stage for `s` also contains the transported simplex because a
      -- subcomplex is closed under face and degeneracy maps.
      exact (stage s).1.A.map θ (stage_mem s)
    have hoverlap :
        (stage s').1.lift.app Δ' ⟨s'.1, stage_mem s'⟩ =
          (stage s).1.lift.app Δ' ⟨s'.1, hs'_mem⟩ := by
      -- Proof comment: chain comparability shows that two candidate stages agree on overlaps.
      exact chain_value_eq_of_overlap (f := f) i hchain (stage s').2 (stage s).2
        (stage_mem s') hs'_mem
    have hnat :
        (stage s).1.lift.app Δ' ⟨s'.1, hs'_mem⟩ =
          X.map θ ((stage s).1.lift.app Δ ⟨s.1, stage_mem s⟩) := by
      -- Proof comment: after fixing one stage, naturality is exactly the naturality of its stored
      -- lift map.
      simpa [s'] using congrFun ((stage s).1.lift.naturality θ) ⟨s.1, stage_mem s⟩
    exact hoverlap.trans hnat
  · ext Δ x
    let sx : (chainSupport (f := f) i c).obj Δ :=
      ⟨x.1, range_le_chainSupport (f := f) i hc _ x.2⟩
    have hbase :
        (stage sx).1.lift.app Δ ⟨x.1, (stage sx).1.hrange _ x.2⟩ = b.app Δ x := by
      -- Proof comment: any stage containing the chosen range simplex already restricts to `b`.
      simpa using congrArg (fun k ↦ k.app Δ x) (stage sx).1.fac_base
    simpa [sx] using hbase
  · intro r hr
    ext Δ x
    let sx : (chainSupport (f := f) i c).obj Δ :=
      ⟨x.1, le_chainSupport_of_mem (f := f) i hr _ x.2⟩
    have hoverlap :
        r.lift.app Δ x = (stage sx).1.lift.app Δ ⟨x.1, stage_mem sx⟩ := by
      -- Proof comment: the chosen stage for `sx` and the prescribed stage `r` coincide on the
      -- common simplex `x`.
      exact chain_value_eq_of_overlap (f := f) i hchain hr (stage sx).2 x.2 (stage_mem sx)
    simpa [sx] using hoverlap.symm
  · ext Δ x
    have htarget :
        f.app Δ ((stage x).1.lift.app Δ ⟨x.1, stage_mem x⟩) = a.app Δ x.1 := by
      -- Proof comment: once the simplex is assigned to a concrete stage, the target condition is
      -- the stored factorization of that stage.
      simpa using congrArg (fun k ↦ k.app Δ ⟨x.1, stage_mem x⟩) (stage x).1.fac_target
    simpa using htarget

/-- Helper for Lemma 14.30.2: a nonempty chain of partial lifts has an upper bound supported on
the union of the supporting subcomplexes. -/
lemma partial_lift_chain_upper_bound {Z W : SSet.{u}} (i : Z ⟶ W) [Mono i]
    {a : W ⟶ Y} {b : (SSet.Subcomplex.range i : SSet) ⟶ X}
    {c : Set (PartialLift (f := f) i a b)}
    (hc : c.Nonempty)
    (hchain : IsChain (fun p q : PartialLift (f := f) i a b => p ≤ q) c) :
    ∃ q : PartialLift (f := f) i a b,
      q.A = chainSupport (f := f) i c ∧
        ∀ r ∈ c, r ≤ q := by
  obtain ⟨ell, hbase, hrestrict, htarget⟩ := chain_support_lift (f := f) i hc hchain
  refine ⟨
    { A := chainSupport (f := f) i c
      hrange := range_le_chainSupport (f := f) i hc
      lift := ell
      fac_base := hbase
      fac_target := htarget },
    rfl,
    ?_⟩
  intro r hr
  refine ⟨le_chainSupport_of_mem (f := f) i hr, ?_⟩
  simpa using hrestrict hr

/-- Helper for Lemma 14.30.2: every commutative square over the range inclusion gives the initial
partial lift supported on the range itself. -/
lemma initial_fac_base {Z W : SSet.{u}} (i : Z ⟶ W) [Mono i]
    {a : W ⟶ Y} {b : (SSet.Subcomplex.range i : SSet) ⟶ X}
    (_sq : CommSq b (SSet.Subcomplex.range i).ι f a) :
    SSet.Subcomplex.homOfLE (show SSet.Subcomplex.range i ≤ SSet.Subcomplex.range i from le_rfl) ≫ b = b := by
  -- At the initial stage the support subcomplex is exactly the range, so the restriction map is
  -- the identity.
  simp

/-- Helper for Lemma 14.30.2: the initial partial lift already lies over the original bottom map
because the starting square commutes. -/
lemma initial_fac_target {Z W : SSet.{u}} (i : Z ⟶ W) [Mono i]
    {a : W ⟶ Y} {b : (SSet.Subcomplex.range i : SSet) ⟶ X}
    (sq : CommSq b (SSet.Subcomplex.range i).ι f a) :
    b ≫ f = (SSet.Subcomplex.range i).ι ≫ a := by
  -- The initial partial lift stores precisely the commutativity of the original square.
  simpa using sq.w

/-- Helper for Lemma 14.30.2: every commutative square over the range inclusion gives the initial
partial lift supported on the range itself. -/
def initial {Z W : SSet.{u}} (i : Z ⟶ W) [Mono i]
    {a : W ⟶ Y} {b : (SSet.Subcomplex.range i : SSet) ⟶ X}
    (sq : CommSq b (SSet.Subcomplex.range i).ι f a) :
    PartialLift (f := f) i a b :=
    { A := SSet.Subcomplex.range i
      hrange := le_rfl
      lift := b
      fac_base := initial_fac_base (f := f) i sq
      fac_target := initial_fac_target (f := f) i sq }

/-- Helper for Lemma 14.30.2: once a partial lift is supported on the top subcomplex, it gives an
actual lift of the original square. -/
lemma hasLift_of_eq_top {Z W : SSet.{u}} (i : Z ⟶ W) [Mono i]
    {a : W ⟶ Y} {b : (SSet.Subcomplex.range i : SSet) ⟶ X}
    (sq : CommSq b (SSet.Subcomplex.range i).ι f a)
    (p : PartialLift (f := f) i a b) (hA : p.A = ⊤) :
    sq.HasLift := by
  -- After identifying the support with `⊤`, the stored map is a genuine filler on all of `W`.
  cases p with
  | mk A hrange lift fac_base fac_target =>
      cases hA
      change SSet.Subcomplex.range i ≤ (⊤ : W.Subcomplex) at hrange
      change lift ≫ f = (⊤ : W.Subcomplex).ι ≫ a at fac_target
      have hrestrict :
          (SSet.Subcomplex.range i).ι ≫ (SSet.Subcomplex.topIso W).inv =
            SSet.Subcomplex.homOfLE hrange := by
        -- Both maps are the tautological inclusion of the range subcomplex into the top one.
        ext Δ x
        rfl
      refine ⟨?_⟩
      refine ⟨(SSet.Subcomplex.topIso W).inv ≫ lift, ?_, ?_⟩
      · -- The filler restricts to the original left edge because the top inclusion is the identity.
        calc
          (SSet.Subcomplex.range i).ι ≫ (SSet.Subcomplex.topIso W).inv ≫ lift =
              SSet.Subcomplex.homOfLE hrange ≫ lift := by
                simpa [Category.assoc] using congrArg (fun k ↦ k ≫ lift) hrestrict
          _ = b := fac_base
      · -- The filler lies over `a` because the stored partial lift already does.
        calc
          ((SSet.Subcomplex.topIso W).inv ≫ lift) ≫ f =
              (SSet.Subcomplex.topIso W).inv ≫ (lift ≫ f) := by
                simp [Category.assoc]
          _ = (SSet.Subcomplex.topIso W).inv ≫ ((⊤ : W.Subcomplex).ι ≫ a) := by
                rw [fac_target]
          _ = a := by
                simp

/-- Helper for Lemma 14.30.2: Zorn's lemma yields a maximal compatible partial lift for every
commutative square over the range inclusion of a monomorphism. -/
lemma exists_maximal {Z W : SSet.{u}} (i : Z ⟶ W) [Mono i]
    {a : W ⟶ Y} {b : (SSet.Subcomplex.range i : SSet) ⟶ X}
    (sq : CommSq b (SSet.Subcomplex.range i).ι f a) :
    ∃ p : PartialLift (f := f) i a b, Maximal (fun _ : PartialLift (f := f) i a b => True) p := by
  let p₀ : PartialLift (f := f) i a b := initial (f := f) i sq
  obtain ⟨m, -, hm⟩ := zorn_le_nonempty₀
    (s := (Set.univ : Set (PartialLift (f := f) i a b)))
    (fun c _ hchain y hy ↦ by
      -- Proof comment: the new union-support construction packages the standard chain upper bound
      -- needed by Zorn's lemma.
      obtain ⟨q, -, hq⟩ := partial_lift_chain_upper_bound (f := f) i ⟨y, hy⟩ hchain
      exact ⟨q, trivial, fun z hz ↦ hq z hz⟩)
    p₀
    trivial
  exact ⟨m, hm⟩

/-- Helper for Lemma 14.30.2: to prove lifting against a range inclusion, it suffices to show
that every square admits a partial lift whose support grows to the top subcomplex. -/
lemma hasLiftingProperty_of_exists_top_stage {Z W : SSet.{u}} (i : Z ⟶ W) [Mono i]
    (hexists :
      ∀ {a : W ⟶ Y} {b : (SSet.Subcomplex.range i : SSet) ⟶ X}
        (_sq : CommSq b (SSet.Subcomplex.range i).ι f a),
          ∃ p : PartialLift (f := f) i a b, p.A = ⊤) :
    HasLiftingProperty (SSet.Subcomplex.range i).ι f := by
  -- The global theorem reduces to producing a top-stage partial lift for each square.
  refine ⟨?_⟩
  intro b a sq
  obtain ⟨p, hp⟩ := hexists sq
  exact hasLift_of_eq_top (f := f) i sq p hp

end PartialLift

/-- Helper for Lemma 14.30.2: if no missing nondegenerate simplices remain, then the support
subcomplex is already all of the ambient simplicial set. -/
lemma eq_top_of_isEmpty_missing_nondegenerate
    {W : SSet.{u}} (A : W.Subcomplex) (h : IsEmpty A.N) :
    A = ⊤ := by
  -- Every nondegenerate simplex of `W` already lies in `A`, so the subcomplex is top.
  rw [A.eq_top_iff_contains_nonDegenerate]
  intro n x hx
  by_contra hxA
  exact h.false (SSet.Subcomplex.N.mk x hx hxA)

/-- Helper for Lemma 14.30.2: a proper subcomplex has a missing nondegenerate simplex of minimal
dimension. -/
lemma exists_minimal_missing_simplex
    {W : SSet.{u}} (A : W.Subcomplex) (hA : A ≠ ⊤) :
    ∃ x : A.N, ∀ y : A.N, y.dim < x.dim → False := by
  classical
  have hnonempty : Nonempty A.N := by
    by_contra hAempty
    exact hA (eq_top_of_isEmpty_missing_nondegenerate A (not_nonempty_iff.mp hAempty))
  let hExists : ∃ n : ℕ, ∃ x : A.N, x.dim = n := by
    rcases hnonempty with ⟨x⟩
    exact ⟨x.dim, x, rfl⟩
  let n : ℕ := Nat.find hExists
  obtain ⟨x, hx⟩ := Nat.find_spec hExists
  refine ⟨x, ?_⟩
  intro y hy
  have hx' : x.dim = n := by
    simpa [n] using hx
  have hy' : y.dim < n := by
    simpa [hx'] using hy
  exact (Nat.find_min hExists hy') ⟨y, rfl⟩

/-- Helper for Lemma 14.30.2: a codimension-one face of a minimal missing simplex already lies in
the old subcomplex. -/
lemma minimal_missing_simplex_face_mem
    {W : SSet.{u}} {A : W.Subcomplex} {x : A.N}
    (hmin : ∀ y : A.N, y.dim < x.dim → False)
    {n : ℕ} (hdim : x.dim = n + 1) (i : Fin (n + 2)) :
    W.δ i (x.cast hdim).simplex ∈ A.obj _ := by
  -- A missing face would produce a strictly smaller missing nondegenerate simplex.
  by_contra hxface
  obtain ⟨y, f, hf, hy⟩ := SSet.Subcomplex.existsN (A := A)
    (W.δ i (x.cast hdim).simplex) hxface
  have hle : y.dim ≤ n := SimplexCategory.le_of_epi f
  have hylt : y.dim < x.dim := by
    rw [hdim]
    exact Nat.lt_succ_of_le hle
  exact hmin y hylt

/-- Helper for Lemma 14.30.2: the boundary of a minimal missing simplex already lands in the old
subcomplex. -/
lemma minimal_missing_simplex_boundary_range_le
    {W : SSet.{u}} {A : W.Subcomplex} (x : A.N)
    (hmin : ∀ y : A.N, y.dim < x.dim → False) :
    x.boundary_range_le := by
  obtain ⟨d, sx, hsx, hsx_not, rfl⟩ := x.mk_surjective
  cases d with
  | zero =>
      intro m y hy
      -- In degree `0` the boundary is empty, so there is no simplex to check.
      have _ : Subsingleton (Fin (0 + 1)) := by
        simpa using (inferInstance : Subsingleton (Fin 1))
      have hy' := hy
      simp only [SSet.Subcomplex.range, CategoryTheory.Subfunctor.range_obj, Set.mem_range,
        SSet.boundary, Function.Surjective, SSet.Subcomplex.N.mk_dim] at hy'
      rcases hy' with ⟨⟨a, ha⟩, hval⟩
      apply False.elim
      apply ha
      intro b
      refine ⟨0, ?_⟩
      exact Subsingleton.elim _ _
  | succ n =>
      intro m y hy
      -- Any boundary simplex factors through some face `δ i`, and minimality places that face in
      -- the subcomplex already.
      have hy' := hy
      simp only [SSet.Subcomplex.range, CategoryTheory.Subfunctor.range_obj, Set.mem_range] at hy'
      rcases hy' with ⟨⟨z, hz⟩, rfl⟩
      obtain ⟨θ, rfl⟩ := SSet.stdSimplex.objEquiv.symm.surjective z
      change W.map θ.op sx ∈ A.obj _
      change ¬ Function.Surjective θ.toOrderHom at hz
      obtain ⟨i, θ', hθ⟩ := SimplexCategory.eq_comp_δ_of_not_surjective θ hz
      simpa [hθ, op_comp, Functor.map_comp] using
        A.map θ'.op (minimal_missing_simplex_face_mem hmin rfl i)

/-- Helper for Lemma 14.30.2: when a partial lift support is enlarged by adjoining one missing
simplex, the old lift transports canonically to the range copy of the old support inside the new
ambient subcomplex. -/
lemma partial_lift_adjoin_transport {Z W : SSet.{u}} (i : Z ⟶ W) [Mono i]
    {a : W ⟶ Y} {b : (SSet.Subcomplex.range i : SSet) ⟶ X}
    (p : PartialLift (f := f) i a b) (x : p.A.N) :
    let B : W.Subcomplex := p.A ⊔ SSet.Subcomplex.ofSimplex x.simplex
    let j : (p.A : SSet) ⟶ (B : SSet) :=
      SSet.Subcomplex.homOfLE (show p.A ≤ B from le_sup_left)
    let U : (B : SSet).Subcomplex := SSet.Subcomplex.range j
    ∃ uLift : (U : SSet) ⟶ X,
      SSet.Subcomplex.toRange j ≫ uLift = p.lift ∧
      uLift ≫ f = U.ι ≫ B.ι ≫ a := by
  intro B j U
  let e : (p.A : SSet) ≅ (U : SSet) := asIso (SSet.Subcomplex.toRange j)
  let uLift : (U : SSet) ⟶ X := e.inv ≫ p.lift
  have htransport :
      e.inv ≫ p.A.ι = U.ι ≫ B.ι := by
    -- Proof comment: both composites are the inclusion of the range copy of `p.A` into `W`.
    calc
      e.inv ≫ p.A.ι = e.inv ≫ (j ≫ B.ι) := by
        rw [SSet.Subcomplex.homOfLE_ι]
      _ = e.inv ≫ (SSet.Subcomplex.toRange j ≫ U.ι ≫ B.ι) := by
        change e.inv ≫ (j ≫ B.ι) = e.inv ≫ ((SSet.Subcomplex.toRange j ≫ U.ι) ≫ B.ι)
        rw [SSet.Subcomplex.toRange_ι]
      _ = (e.inv ≫ SSet.Subcomplex.toRange j) ≫ U.ι ≫ B.ι := by
        simp [Category.assoc]
      _ = U.ι ≫ B.ι := by
        simp [e]
  refine ⟨uLift, ?_, ?_⟩
  · -- Proof comment: transporting along the range isomorphism recovers the original lift.
    simp [uLift, e]
  · -- Proof comment: the transported lift still lies over `a`, now viewed through the ambient
    -- support `B`.
    calc
      uLift ≫ f = e.inv ≫ (p.lift ≫ f) := by
        simp [uLift, Category.assoc]
      _ = e.inv ≫ (p.A.ι ≫ a) := by
        rw [p.fac_target]
      _ = (e.inv ≫ p.A.ι) ≫ a := by
        simp [Category.assoc]
      _ = (U.ι ≫ B.ι) ≫ a := by
        rw [htransport]
      _ = U.ι ≫ B.ι ≫ a := by
        simp [Category.assoc]

/-- Helper for Lemma 14.30.2: membership in the range copy of a subcomplex inclusion is exactly
membership in the original subcomplex. -/
lemma range_copy_mem_iff
    {W : SSet.{u}} {A B : W.Subcomplex} (hAB : A ≤ B)
    {Δ : SimplexCategoryᵒᵖ} (y : B.obj Δ) :
    y ∈ (SSet.Subcomplex.range (SSet.Subcomplex.homOfLE hAB)).obj Δ ↔ y.1 ∈ A.obj Δ := by
  constructor
  · intro hy
    -- Proof comment: an element of the range copy comes from an actual simplex of `A`.
    simp only [SSet.Subcomplex.range, CategoryTheory.Subfunctor.range_obj] at hy
    rcases hy with ⟨z, rfl⟩
    exact z.2
  · intro hy
    -- Proof comment: the original simplex of `A` itself is the witness for the range copy.
    simp only [SSet.Subcomplex.range, CategoryTheory.Subfunctor.range_obj]
    refine ⟨⟨y.1, hy⟩, ?_⟩
    apply Subtype.ext
    rfl

/-- Helper for Lemma 14.30.2: the missing simplex can be transported into the range copy of the
old support inside the adjoined ambient subcomplex, where its boundary still lands in the copied
support and adjoining it generates the whole ambient subcomplex. -/
lemma partial_lift_adjoin_missing_simplex {Z W : SSet.{u}} (i : Z ⟶ W) [Mono i]
    {a : W ⟶ Y} {b : (SSet.Subcomplex.range i : SSet) ⟶ X}
    (p : PartialLift (f := f) i a b) (x : p.A.N)
    (hxboundary : x.boundary_range_le) :
    let B : W.Subcomplex := p.A ⊔ SSet.Subcomplex.ofSimplex x.simplex
    let j : (p.A : SSet) ⟶ (B : SSet) :=
      SSet.Subcomplex.homOfLE (show p.A ≤ B from le_sup_left)
    let U : (B : SSet).Subcomplex := SSet.Subcomplex.range j
    ∃ xB : U.N,
      xB.boundary_range_le ∧
      U ⊔ SSet.Subcomplex.ofSimplex xB.simplex = ⊤ := by
  intro B j U
  let x0 : B.obj (op ⦋x.dim⦌) :=
    ⟨x.simplex, Or.inr (SSet.Subcomplex.mem_ofSimplex_obj x.simplex)⟩
  have hx0_nonDegenerate : x0 ∈ (B : SSet).nonDegenerate x.dim := by
    -- Proof comment: the ambient copy of the missing simplex stays nondegenerate in the larger
    -- support because subcomplex inclusion does not change nondegeneracy.
    simpa [x0] using ((B.mem_nonDegenerate_iff x0).2 x.nonDegenerate)
  have hx0_not_mem : x0 ∉ U.obj (op ⦋x.dim⦌) := by
    -- Proof comment: if the copied simplex already lay in the range copy `U`, its underlying
    -- simplex would already lie in the old support `p.A`, contradicting that `x` is missing.
    intro hxU
    exact x.notMem ((range_copy_mem_iff (show p.A ≤ B from le_sup_left) x0).1 hxU)
  let xB : U.N := SSet.Subcomplex.N.mk x0 hx0_nonDegenerate hx0_not_mem
  refine ⟨xB, ?_, ?_⟩
  · intro m y hy
    -- Proof comment: membership in the boundary range of `xB` becomes boundary membership for the
    -- original simplex in `W`, and `hxboundary` then places it back in `p.A`, hence in `U`.
    apply (range_copy_mem_iff (show p.A ≤ B from le_sup_left) y).2
    have hyW :
        y.1 ∈
          (SSet.Subcomplex.range (∂Δ[x.dim].ι ≫ SSet.yonedaEquiv.symm x.simplex)).obj m := by
      simp only [SSet.Subcomplex.range, CategoryTheory.Subfunctor.range_obj, Set.mem_range] at hy ⊢
      rcases hy with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      simpa [xB, x0] using congrArg Subtype.val hz
    exact hxboundary _ hyW
  · apply le_antisymm
    · exact sup_le le_top le_top
    · intro Δ y hyTop
      rcases y.2 with hyA | hyx
      · exact Or.inl ((range_copy_mem_iff (show p.A ≤ B from le_sup_left) y).2 hyA)
      · have hyxB : y ∈ (SSet.Subcomplex.ofSimplex xB.simplex).obj Δ := by
          rcases (SSet.Subcomplex.mem_ofSimplex_obj_iff x.simplex y.1).1 hyx with ⟨θ, hθ⟩
          refine (SSet.Subcomplex.mem_ofSimplex_obj_iff xB.simplex y).2 ?_
          refine ⟨θ, ?_⟩
          apply Subtype.ext
          simpa [xB, x0] using hθ
        exact Or.inr hyxB

/-- Helper for Lemma 14.30.2: a partial lift extends across a minimal missing simplex once the
boundary-filling property against boundary inclusions is available. -/
lemma extend_partial_lift_across_minimal_missing_simplex {Z W : SSet.{u}} (i : Z ⟶ W) [Mono i]
    (hf : I.rlp f)
    {a : W ⟶ Y} {b : (SSet.Subcomplex.range i : SSet) ⟶ X}
    (p : PartialLift (f := f) i a b) (x : p.A.N)
    (hxboundary : x.boundary_range_le) :
    ∃ q : PartialLift (f := f) i a b,
      p ≤ q ∧ q.A = p.A ⊔ SSet.Subcomplex.ofSimplex x.simplex := by
  let B : W.Subcomplex := p.A ⊔ SSet.Subcomplex.ofSimplex x.simplex
  let j : (p.A : SSet) ⟶ (B : SSet) :=
    SSet.Subcomplex.homOfLE (show p.A ≤ B from le_sup_left)
  let U : (B : SSet).Subcomplex := SSet.Subcomplex.range j
  obtain ⟨uLift, hu_base, hu_target⟩ :=
    partial_lift_adjoin_transport (f := f) (i := i) p x
  obtain ⟨xB, hxBboundary, hxBtop⟩ :=
    partial_lift_adjoin_missing_simplex (f := f) (i := i) p x hxboundary
  let hsq :
      CommSq
        (U.lift (∂Δ[xB.dim].ι ≫ SSet.yonedaEquiv.symm xB.simplex) hxBboundary ≫ uLift)
        (∂Δ[xB.dim].ι) f
        (SSet.yonedaEquiv.symm xB.simplex ≫ B.ι ≫ a) := by
    refine CommSq.mk ?_
    calc
      (U.lift (∂Δ[xB.dim].ι ≫ SSet.yonedaEquiv.symm xB.simplex) hxBboundary ≫ uLift) ≫ f =
          U.lift (∂Δ[xB.dim].ι ≫ SSet.yonedaEquiv.symm xB.simplex) hxBboundary ≫ (uLift ≫ f) := by
            simp [Category.assoc]
      _ =
          U.lift (∂Δ[xB.dim].ι ≫ SSet.yonedaEquiv.symm xB.simplex) hxBboundary ≫
            (U.ι ≫ B.ι ≫ a) := by
              rw [hu_target]
      _ =
          (U.lift (∂Δ[xB.dim].ι ≫ SSet.yonedaEquiv.symm xB.simplex) hxBboundary ≫ U.ι) ≫
            B.ι ≫ a := by
              simp [Category.assoc]
      _ = (∂Δ[xB.dim].ι ≫ SSet.yonedaEquiv.symm xB.simplex) ≫ B.ι ≫ a := by
            rw [U.lift_ι]
      _ = ∂Δ[xB.dim].ι ≫ (SSet.yonedaEquiv.symm xB.simplex ≫ B.ι ≫ a) := by
            simp [Category.assoc]
  let _ : hsq.HasLift :=
    (boundaryInclusions_rlp_hasLiftingProperty (f := f) xB.dim hf).sq_hasLift hsq
  let β : Δ[xB.dim] ⟶ X := hsq.lift
  have hβ_left :
      ∂Δ[xB.dim].ι ≫ β =
        U.lift (∂Δ[xB.dim].ι ≫ SSet.yonedaEquiv.symm xB.simplex) hxBboundary ≫ uLift := by
    simpa [β] using (CommSq.fac_left (sq := hsq)).symm
  have hβ_right : β ≫ f = SSet.yonedaEquiv.symm xB.simplex ≫ B.ι ≫ a := by
    simpa [β] using (CommSq.fac_right (sq := hsq))
  let hpush :
      IsPushout
        ∂Δ[xB.dim].ι
        (U.lift (∂Δ[xB.dim].ι ≫ SSet.yonedaEquiv.symm xB.simplex) hxBboundary)
        (SSet.yonedaEquiv.symm xB.simplex)
        U.ι :=
    SSet.isPushout_of_subcomplex_adjoin_simplex U xB hxBboundary hxBtop
  obtain ⟨ell, hell_left, hell_right⟩ := hpush.exists_desc β uLift hβ_left
  refine ⟨
    { A := B
      hrange := p.hrange.trans (show p.A ≤ B from le_sup_left)
      lift := ell
      fac_base := ?_
      fac_target := ?_ },
    ?_,
    rfl⟩
  · -- Proof comment: restrict the glued lift first to `U`, then back along the range copy to the
    -- original support, where it is exactly `p.lift`.
    have hj :
        j = SSet.Subcomplex.toRange j ≫ U.ι := by
      simpa [U] using (SSet.Subcomplex.toRange_ι j).symm
    have hhrange :
        SSet.Subcomplex.homOfLE (p.hrange.trans (show p.A ≤ B from le_sup_left)) =
          SSet.Subcomplex.homOfLE p.hrange ≫ j := by
      ext Δ z
      rfl
    calc
      SSet.Subcomplex.homOfLE (p.hrange.trans (show p.A ≤ B from le_sup_left)) ≫ ell =
          (SSet.Subcomplex.homOfLE p.hrange ≫ j) ≫ ell := by
            rw [hhrange]
      _ =
          SSet.Subcomplex.homOfLE p.hrange ≫ (j ≫ ell) := by
            simp [Category.assoc]
      _ =
          SSet.Subcomplex.homOfLE p.hrange ≫
            (SSet.Subcomplex.toRange j ≫ U.ι ≫ ell) := by
              simpa [hj, Category.assoc]
      _ =
          SSet.Subcomplex.homOfLE p.hrange ≫ (SSet.Subcomplex.toRange j ≫ uLift) := by
            simpa [Category.assoc] using congrArg
              (fun k ↦ SSet.Subcomplex.homOfLE p.hrange ≫ (SSet.Subcomplex.toRange j ≫ k))
              hell_right
      _ = SSet.Subcomplex.homOfLE p.hrange ≫ p.lift := by
            rw [hu_base]
      _ = b := p.fac_base
  · -- Proof comment: the glued map agrees with the target map on both pushout legs, so by the
    -- pushout universal property it lies over `a` on all of `B`.
    apply hpush.hom_ext
    · calc
        SSet.yonedaEquiv.symm xB.simplex ≫ (ell ≫ f) =
            (SSet.yonedaEquiv.symm xB.simplex ≫ ell) ≫ f := by
              simp [Category.assoc]
        _ = β ≫ f := by
              rw [hell_left]
        _ = SSet.yonedaEquiv.symm xB.simplex ≫ B.ι ≫ a := hβ_right
        _ = SSet.yonedaEquiv.symm xB.simplex ≫ (B.ι ≫ a) := by
              simp
    · calc
        U.ι ≫ (ell ≫ f) = (U.ι ≫ ell) ≫ f := by
          simp [Category.assoc]
        _ = uLift ≫ f := by
          rw [hell_right]
        _ = U.ι ≫ B.ι ≫ a := hu_target
        _ = U.ι ≫ (B.ι ≫ a) := by
          simp
  · refine ⟨show p.A ≤ B from le_sup_left, ?_⟩
    -- Proof comment: the new support extends `p.A`, and the glued lift restricts there to the
    -- original partial lift via the transported map on the range copy.
    have hj :
        j = SSet.Subcomplex.toRange j ≫ U.ι := by
      simpa [U] using (SSet.Subcomplex.toRange_ι j).symm
    calc
      SSet.Subcomplex.homOfLE (show p.A ≤ B from le_sup_left) ≫ ell =
          j ≫ ell := rfl
      _ = SSet.Subcomplex.toRange j ≫ U.ι ≫ ell := by
            simpa [hj, Category.assoc]
      _ = SSet.Subcomplex.toRange j ≫ uLift := by
            simpa [Category.assoc] using congrArg (fun k ↦ SSet.Subcomplex.toRange j ≫ k)
              hell_right
      _ = p.lift := hu_base

/-- Lemma 14.30.2: a trivial Kan fibration of simplicial sets has the right lifting property with
respect to any monomorphism of simplicial sets, i.e. canonically with respect to any termwise
injective map. -/
@[stacks 08NM]
theorem boundaryInclusions_rlp_monomorphisms (hf : I.rlp f) :
    (monomorphisms SSet).rlp f := by
  -- The verified reduction step replaces an arbitrary mono by the inclusion of its image.
  rw [monomorphisms_rlp_iff_range_inclusions (f := f)]
  intro Z W i _
  -- Route correction: the earlier filtration-only route reduced to range inclusions correctly, but
  -- it did not package the global compatibility data needed to assemble infinitely many local
  -- extensions. The source proof instead uses maximal compatible partial lifts.
  refine PartialLift.hasLiftingProperty_of_exists_top_stage (f := f) i ?_
  intro a b sq
  obtain ⟨p, hpmax⟩ := PartialLift.exists_maximal (f := f) i sq
  by_cases hA : p.A = ⊤
  · exact ⟨p, hA⟩
  obtain ⟨x, hxmin⟩ := exists_minimal_missing_simplex p.A hA
  have hxboundary : x.boundary_range_le := minimal_missing_simplex_boundary_range_le x hxmin
  obtain ⟨q, hpq, hqA⟩ :=
    extend_partial_lift_across_minimal_missing_simplex (f := f) (i := i) hf p x hxboundary
  have hqp : q ≤ p := hpmax.2 trivial hpq
  have hpAeq : p.A = p.A ⊔ SSet.Subcomplex.ofSimplex x.simplex := by
    apply le_antisymm
    · exact le_sup_left
    · simpa [hqA] using hqp.1
  have hxMemSup : x.simplex ∈ (p.A ⊔ SSet.Subcomplex.ofSimplex x.simplex).obj (op ⦋x.dim⦌) := by
    exact Or.inr (SSet.Subcomplex.mem_ofSimplex_obj x.simplex)
  have hxMemA : x.simplex ∈ p.A.obj (op ⦋x.dim⦌) := by
    rw [← hpAeq] at hxMemSup
    exact hxMemSup
  exact False.elim (x.notMem hxMemA)

/-- Companion owner-level reformulation of Lemma 14.30.2: for simplicial sets, lifting against the
boundary inclusions is equivalent to lifting against all monomorphisms. The forward implication is
the source-facing content of the lemma; the reverse implication is the generic monotonicity of
`MorphismProperty.rlp` applied to `I_le_monomorphisms`. -/
theorem boundaryInclusions_rlp_iff_monomorphisms_rlp :
    I.rlp f ↔ (monomorphisms SSet).rlp f :=
  ⟨boundaryInclusions_rlp_monomorphisms,
    fun hmono ↦
      (show (monomorphisms SSet).rlp ≤ I.rlp from antitone_rlp I_le_monomorphisms) f hmono⟩

end
