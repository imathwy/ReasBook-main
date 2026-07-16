import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.Sites.Precoverage
import stacks_proof.stacks_project.Chap04.Lemma_4_33_4
import stacks_proof.stacks_project.Chap04.Lemma_4_33_13
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

open CategoryTheory.Limits

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]

/- Domain-style sampling for Lemma 8.10.1:
- primary domain: source-facing sites presented by `Precoverage` together with fibred categories and
  strongly cartesian morphisms;
- sampled owner API:
  `CategoryTheory.Precoverage`,
  `CategoryTheory.Precoverage.HasIsos`,
  `CategoryTheory.Functor.IsFibered`,
  `CategoryTheory.Functor.IsStronglyCartesian`;
- best owner abstraction: the source-facing owner here is still `Precoverage`; the site axioms are
  derived typeclass API on that owner, while fibredness and strong cartesianness come from the
  canonical fibered-category owner API on the functor `p`.

Source/core/bridge triage:
- `source-facing`: the inherited covering families `stronglyCartesianLiftPrecoverage J p`;
- `core/canonical`: the four `Precoverage` site-axiom typeclasses and the owner predicates
  `Functor.IsFibered` and `Functor.IsStronglyCartesian`;
- `bridge/view`: no separate bundled "is a site" wrapper is kept, since the textbook sentence is
  carried canonically by the four site-axiom instances on `stronglyCartesianLiftPrecoverage J p`;
  downstream files should use those instances directly.

Primitive-vs-derived split:
- primitive data: a base precoverage `J`, a functor `p : S ⥤ C`, and the defining condition that a
  family in `S` is covering when each arrow is strongly cartesian and its image family is
  `J`-covering;
- derived API: the membership characterization for represented families and the four site-axiom
  instances on the inherited precoverage. -/

/-- Lemma 8.10.1: the inherited precoverage on the total category of a fibred category, whose
covering families are the strongly cartesian families whose images in the base form a covering
family. -/
@[stacks 06NU]
def stronglyCartesianLiftPrecoverage (J : Precoverage C) (p : S ⥤ C) : Precoverage S where
  coverings x :=
    { R | ∃ (ι : Type (max u₂ v₂)) (X : ι → S) (f : ∀ i, X i ⟶ x),
        R = Presieve.ofArrows X f ∧
          (∀ i, p.IsStronglyCartesian (p.map (f i)) (f i)) ∧
          Presieve.ofArrows (p.obj ∘ X) (fun i ↦ p.map (f i)) ∈ J (p.obj x) }

variable (J : Precoverage C) (p : S ⥤ C)

/-- Helper for Lemma 8.10.1: a pullback square in the base lifts to a pullback square upstairs
when both vertical arrows are strongly cartesian over the corresponding base maps. -/
private theorem total_square_isPullback_of_base_pullback
    (p : S ⥤ C)
    {x y z w : S} {R : C} {f : R ⟶ p.obj x} {g : R ⟶ p.obj z}
    {φ : x ⟶ y} {ψ : z ⟶ y} {χ : w ⟶ x}
    (hbase : IsPullback f g (p.map φ) (p.map ψ))
    (a : w ⟶ z)
    [p.IsHomLift f χ] [p.IsStronglyCartesian (p.map φ) φ] [p.IsStronglyCartesian g a]
    (hχ : χ ≫ φ = a ≫ ψ) :
    IsPullback χ a φ ψ := by
  exact
    Functor.isPullback_of_isPullback_of_isStronglyCartesian
      (p := p) (φ := φ) (ψ := ψ) (hbase := hbase) (a := a) hχ

/-- Helper for Lemma 8.10.1: a strongly cartesian morphism has pullbacks along any map whose base
change exists downstairs. -/
private theorem hasPullback_of_stronglyCartesian
    (p : S ⥤ C) [p.IsFibered]
    {x y z : S} (φ : x ⟶ y) (ψ : z ⟶ y)
    [HasPullback (p.map φ) (p.map ψ)] [p.IsStronglyCartesian (p.map φ) φ] :
    HasPullback φ ψ := by
  exact Functor.hasPullback_of_isStronglyCartesian (p := p) (φ := φ) (ψ := ψ)

-- Proof sketch: unfold `stronglyCartesianLiftPrecoverage`. One direction is immediate from the
-- defining existential package. For the converse, rewrite the represented presieve by the given
-- family and read off the strong cartesianness and the covering condition downstairs.
/-- A family belongs to the inherited precoverage exactly when each arrow is strongly cartesian and
its image family is covering in the base precoverage. -/
@[simp]
theorem ofArrows_mem_stronglyCartesianLiftPrecoverage_iff
    {x : S} {ι : Type (max u₂ v₂)} (X : ι → S) (f : ∀ i, X i ⟶ x) :
    Presieve.ofArrows X f ∈ stronglyCartesianLiftPrecoverage J p x ↔
      (∀ i, p.IsStronglyCartesian (p.map (f i)) (f i)) ∧
        Presieve.ofArrows (p.obj ∘ X) (fun i ↦ p.map (f i)) ∈ J (p.obj x) := by
  constructor
  · intro h
    rcases h with ⟨κ, Y, g, hR, hstrong, hcover⟩
    refine ⟨?_, ?_⟩
    · intro i
      -- Read the strong-cartesian witness for `f i` off the represented presieve equality.
      have hi : Presieve.ofArrows Y g (f i) := by
        rw [← hR]
        exact Presieve.ofArrows.mk i
      obtain ⟨j, hij, hfi⟩ := Presieve.ofArrows_surj g (f i) hi
      have hj :
          p.IsStronglyCartesian
            (p.map (eqToHom hij.symm) ≫ p.map (g j))
            (eqToHom hij.symm ≫ g j) := by
        let _ : p.IsStronglyCartesian (p.map (g j)) (g j) := hstrong j
        infer_instance
      simpa [Functor.map_comp, hfi] using hj
    · -- Map the presieve equality along `p` to identify the covering family downstairs.
      have hmap :
          Presieve.ofArrows (p.obj ∘ X) (fun i ↦ p.map (f i)) =
            Presieve.ofArrows (p.obj ∘ Y) (fun i ↦ p.map (g i)) := by
        simpa using congrArg (fun R ↦ Presieve.map p R) hR
      simpa [hmap] using hcover
  · intro h
    obtain ⟨hstrong, hcover⟩ := h
    exact ⟨ι, X, f, rfl, hstrong, hcover⟩

/-- Helper for Lemma 8.10.1: if each arrow in an indexed family is strongly cartesian and the
image family is `J`-covering, then the represented presieve has pullbacks along any morphism. -/
theorem ofArrows_hasPullbacks_of_stronglyCartesian
    [J.HasPullbacks] [p.IsFibered]
    {x y : S} {ι : Type w} (X : ι → S) (f : ∀ i, X i ⟶ x)
    (hstrong : ∀ i, p.IsStronglyCartesian (p.map (f i)) (f i))
    (hcover : Presieve.ofArrows (p.obj ∘ X) (fun i ↦ p.map (f i)) ∈ J (p.obj x))
    (g : y ⟶ x) :
    (Presieve.ofArrows X f).HasPullbacks g := by
  refine ⟨fun {Z} h hh ↦ ?_⟩
  obtain ⟨i⟩ := hh
  -- Pull back the corresponding base arrow and lift that pullback through the strong-cartesian map.
  have hbase :
      HasPullback (p.map (f i)) (p.map g) :=
    (J.hasPullbacks_of_mem (p.map g) hcover).hasPullback (Presieve.ofArrows.mk i)
  let _ : HasPullback (p.map (f i)) (p.map g) := hbase
  let _ : p.IsStronglyCartesian (p.map (f i)) (f i) := hstrong i
  exact hasPullback_of_stronglyCartesian p (f i) g

-- Proof sketch: verify the four site axioms for the inherited precoverage.
-- Singleton isomorphisms are strongly cartesian, compositions of strongly cartesian arrows stay
-- strongly cartesian, and pullbacks of covering families are obtained from fibred pullbacks and
-- the pullback axiom for the site downstairs.
/-- The inherited precoverage contains singleton isomorphism covering families. -/
instance [J.HasIsos] :
    (stronglyCartesianLiftPrecoverage J p).HasIsos where
  mem_coverings_of_isIso := by
    intro S T f _
    -- Prove the represented-family version of the singleton cover and then simplify it back.
    have hfamily :
        Presieve.ofArrows (fun _ : ULift.{max u₂ v₂, 0} PUnit ↦ S) (fun _ ↦ f) ∈
          stronglyCartesianLiftPrecoverage J p T := by
      rw [ofArrows_mem_stronglyCartesianLiftPrecoverage_iff]
      refine ⟨?_, ?_⟩
      · intro _
        simpa using (inferInstance : p.IsStronglyCartesian (p.map f) f)
      · have hsingleton :
            Presieve.ofArrows (p.obj ∘ fun _ : ULift.{max u₂ v₂, 0} PUnit ↦ S)
              (fun _ : ULift.{max u₂ v₂, 0} PUnit ↦ p.map f) =
              Presieve.singleton (p.map f) := by
          simpa [Function.comp] using
            (Presieve.ofArrows_of_unique
              (Y := fun _ : ULift.{max u₂ v₂, 0} PUnit ↦ p.obj S)
              (f := fun _ : ULift.{max u₂ v₂, 0} PUnit ↦ p.map f))
        rw [hsingleton]
        exact (J.mem_coverings_of_isIso (p.map f) :
          Presieve.singleton (p.map f) ∈ J (p.obj T))
    have hsingleton :
        Presieve.ofArrows (fun _ : ULift.{max u₂ v₂, 0} PUnit ↦ S)
          (fun _ : ULift.{max u₂ v₂, 0} PUnit ↦ f) =
          Presieve.singleton f := by
      simpa using
        (Presieve.ofArrows_of_unique
          (Y := fun _ : ULift.{max u₂ v₂, 0} PUnit ↦ S)
          (f := fun _ : ULift.{max u₂ v₂, 0} PUnit ↦ f))
    rw [hsingleton] at hfamily
    exact hfamily

-- Proof sketch: use fibred pullbacks over base pullbacks. The pullback axiom downstairs gives the
-- required pullback square of the image family, and fibredness lifts that square to the total
-- category with strongly cartesian comparison maps.
/-- The inherited precoverage admits pullbacks of its covering families. -/
instance [J.HasPullbacks] [p.IsFibered] :
    (stronglyCartesianLiftPrecoverage J p).HasPullbacks where
  hasPullbacks_of_mem g hR := by
    rcases hR with ⟨ι, X, f, rfl, hstrong, hcover⟩
    -- Reduce to the represented-family pullback package proved above.
    exact ofArrows_hasPullbacks_of_stronglyCartesian (J := J) (p := p) X f hstrong hcover g

/-- Helper for Lemma 8.10.1: any lift of `k ≫ p.map χ` through the pullback square factors across
the strongly cartesian right leg `φ`. -/
private theorem pullback_factor_through_strong_right_leg
    {t x y z w : S} {φ : x ⟶ y} {g : z ⟶ y} {χ : w ⟶ z} {a : w ⟶ x}
    (hφ : p.IsStronglyCartesian (p.map φ) φ)
    (h : IsPullback χ a g φ)
    {k : p.obj t ⟶ p.obj w} {τ : t ⟶ z}
    (hτ : p.IsHomLift (k ≫ p.map χ) τ) :
    ∃ a' : t ⟶ x, p.IsHomLift (k ≫ p.map a) a' ∧ a' ≫ φ = τ ≫ g := by
  letI : p.IsStronglyCartesian (p.map φ) φ := hφ
  letI : p.IsHomLift (k ≫ p.map χ) τ := hτ
  have hk :
      (k ≫ p.map χ) ≫ p.map g = (k ≫ p.map a) ≫ p.map φ := by
    -- Map the pullback identity to the base and then postcompose with the test arrow `k`.
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun m ↦ k ≫ p.map m) h.w
  let a' : t ⟶ x :=
    Functor.IsStronglyCartesian.map p (p.map φ) φ hk (τ ≫ g)
  refine ⟨a', inferInstance, ?_⟩
  -- The chosen factorization through `φ` is exactly the universal-property comparison map.
  exact Functor.IsStronglyCartesian.fac p (p.map φ) φ hk (τ ≫ g)

/-- Helper for Lemma 8.10.1: mapping a pullback square upstairs along a strongly cartesian arrow
produces a pullback square in the base category. -/
private theorem base_pullback_mediator_of_total_pullback
    [p.IsFibered]
    {x y z w : S} {φ : x ⟶ y} {g : z ⟶ y} {χ : w ⟶ z} {a : w ⟶ x}
    (hφ : p.IsStronglyCartesian (p.map φ) φ)
    (h : IsPullback χ a g φ)
    (s : PullbackCone (p.map g) (p.map φ)) :
    ∃ n : s.pt ⟶ p.obj w, n ≫ p.map χ = s.fst ∧ n ≫ p.map a = s.snd := by
  let u := Functor.IsPreFibered.pullbackObj (p := p) rfl s.fst
  let τ : u ⟶ z := Functor.IsPreFibered.pullbackMap (p := p) rfl s.fst
  letI : p.IsStronglyCartesian s.fst τ :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian p s.fst τ
  let α : u ⟶ x :=
    Functor.IsStronglyCartesian.map p (p.map φ) φ s.condition (τ ≫ g)
  have hα_fac : α ≫ φ = τ ≫ g := by
    -- The strongly cartesian right leg turns the second projection of the base cone into the
    -- upstairs arrow needed for the total pullback square.
    exact Functor.IsStronglyCartesian.fac p (p.map φ) φ s.condition (τ ≫ g)
  let m : u ⟶ w := h.lift τ α hα_fac.symm
  have hu : p.obj u = s.pt := IsHomLift.domain_eq p s.fst τ
  let n : s.pt ⟶ p.obj w := eqToHom hu.symm ≫ p.map m
  refine ⟨n, ?_, ?_⟩
  · -- The chosen mediator lands on the first cone projection after normalizing the domain object.
    calc
      n ≫ p.map χ = eqToHom hu.symm ≫ p.map (m ≫ χ) := by
        simp [n, Functor.map_comp, Category.assoc]
      _ = eqToHom hu.symm ≫ p.map τ := by rw [h.lift_fst τ α hα_fac.symm]
      _ = s.fst := by
        calc
          eqToHom hu.symm ≫ p.map τ = eqToHom hu.symm ≫ (eqToHom hu ≫ s.fst) := by
            simpa [hu, Category.assoc] using congrArg (fun k ↦ eqToHom hu.symm ≫ k)
              (IsHomLift.fac' p s.fst τ)
          _ = s.fst := by simp
  · -- The same normalization identifies the second projection with the second cone leg.
    calc
      n ≫ p.map a = eqToHom hu.symm ≫ p.map (m ≫ a) := by
        simp [n, Functor.map_comp, Category.assoc]
      _ = eqToHom hu.symm ≫ p.map α := by rw [h.lift_snd τ α hα_fac.symm]
      _ = s.snd := by
        calc
          eqToHom hu.symm ≫ p.map α = eqToHom hu.symm ≫ (eqToHom hu ≫ s.snd) := by
            simpa [hu, Category.assoc] using congrArg (fun k ↦ eqToHom hu.symm ≫ k)
              (IsHomLift.fac' p s.snd α)
          _ = s.snd := by simp

/-- Helper for Lemma 8.10.1: two base mediators for the same descended cone agree. -/
private theorem candidate_lift_factors_through_pullback_mediator
    [p.IsFibered]
    {x y z w u uq : S} {φ : x ⟶ y} {g : z ⟶ y} {χ : w ⟶ z} {a : w ⟶ x}
    (hφ : p.IsStronglyCartesian (p.map φ) φ)
    (h : IsPullback χ a g φ)
    {s : PullbackCone (p.map g) (p.map φ)}
    {τ : u ⟶ z} [p.IsHomLift s.fst τ] [p.IsStronglyCartesian s.fst τ]
    {α : u ⟶ x} [p.IsHomLift s.snd α] (hα_fac : α ≫ φ = τ ≫ g)
    {m : u ⟶ w} (hm_fst : m ≫ χ = τ) (hm_snd : m ≫ a = α)
    {q : s.pt ⟶ p.obj w} {μ : uq ⟶ w} [p.IsHomLift q μ]
    (hqχ : q ≫ p.map χ = s.fst) (hqa : q ≫ p.map a = s.snd) :
    ∃ e : uq ⟶ u, p.IsHomLift (𝟙 s.pt) e ∧ μ = e ≫ m := by
  letI : p.IsStronglyCartesian (p.map φ) φ := hφ
  have hμχ : p.IsHomLift s.fst (μ ≫ χ) := by
    rw [← hqχ]
    infer_instance
  letI : p.IsHomLift s.fst (μ ≫ χ) := hμχ
  let e : uq ⟶ u := Functor.IsCartesian.map p s.fst τ (μ ≫ χ)
  letI : p.IsHomLift (𝟙 s.pt) e := inferInstance
  have he_fac : e ≫ τ = μ ≫ χ := by
    -- The comparison map is defined by the Cartesian universal property of `τ`.
    simpa [e] using Functor.IsCartesian.fac p s.fst τ (μ ≫ χ)
  have hμa : p.IsHomLift s.snd (μ ≫ a) := by
    rw [← hqa]
    infer_instance
  letI : p.IsHomLift s.snd (e ≫ α) := inferInstance
  letI : p.IsHomLift s.snd (μ ≫ a) := hμa
  have hea : e ≫ α = μ ≫ a := by
    -- The two second legs lift the same base arrow and agree after composing with `φ`.
    apply Functor.IsStronglyCartesian.ext p (p.map φ) φ (g := s.snd)
    calc
      (e ≫ α) ≫ φ = e ≫ (α ≫ φ) := by simp [Category.assoc]
      _ = e ≫ (τ ≫ g) := by rw [hα_fac]
      _ = (e ≫ τ) ≫ g := by simp [Category.assoc]
      _ = (μ ≫ χ) ≫ g := by rw [he_fac]
      _ = μ ≫ (χ ≫ g) := by simp [Category.assoc]
      _ = μ ≫ (a ≫ φ) := by rw [h.w]
      _ = (μ ≫ a) ≫ φ := by simp [Category.assoc]
  refine ⟨e, inferInstance, ?_⟩
  -- Equality in the total pullback follows from equality of the two projections.
  apply h.hom_ext
  · calc
      μ ≫ χ = e ≫ τ := by rw [he_fac]
      _ = e ≫ (m ≫ χ) := by rw [hm_fst]
      _ = (e ≫ m) ≫ χ := by simp [Category.assoc]
  · calc
      μ ≫ a = e ≫ α := by rw [hea]
      _ = e ≫ (m ≫ a) := by rw [hm_snd]
      _ = (e ≫ m) ≫ a := by simp [Category.assoc]

/-- Helper for Lemma 8.10.1: an upstairs factorization through the canonical mediator descends to
the corresponding base mediator. -/
private theorem base_mediator_eq_of_upstairs_comparison
    {u uq w : S} {R : C} {q : R ⟶ p.obj w} {μ : uq ⟶ w} {e : uq ⟶ u} {m : u ⟶ w}
    (hu : p.obj u = R)
    [p.IsHomLift q μ] [p.IsHomLift (𝟙 R) e]
    (hμ : μ = e ≫ m) :
    q = eqToHom hu.symm ≫ p.map m := by
  have hq : p.obj uq = R := IsHomLift.domain_eq p q μ
  -- Normalize the lifted comparison upstairs, then collapse the identity lift on `e`.
  calc
    q = eqToHom hq.symm ≫ p.map μ := by
      simpa [Category.assoc] using (IsHomLift.fac p q μ)
    _ = eqToHom hq.symm ≫ p.map (e ≫ m) := by rw [hμ]
    _ = (eqToHom hq.symm ≫ p.map e) ≫ p.map m := by
      simp only [Functor.map_comp, Category.assoc]
    _ = eqToHom hu.symm ≫ p.map m := by
      have he :
          eqToHom hq.symm ≫ p.map e = eqToHom hu.symm := by
        simpa [Category.assoc] using
          congrArg (fun k ↦ eqToHom hq.symm ≫ k) (IsHomLift.fac' p (𝟙 R) e)
      rw [he]

/-- Helper for Lemma 8.10.1: two base mediators for the same descended cone agree. -/
private theorem base_pullback_mediator_unique_of_total_pullback
    [p.IsFibered]
    {x y z w : S} {φ : x ⟶ y} {g : z ⟶ y} {χ : w ⟶ z} {a : w ⟶ x}
    (hφ : p.IsStronglyCartesian (p.map φ) φ)
    (h : IsPullback χ a g φ)
    (s : PullbackCone (p.map g) (p.map φ))
    {n n' : s.pt ⟶ p.obj w}
    (hnχ : n ≫ p.map χ = s.fst) (hna : n ≫ p.map a = s.snd)
    (hn'χ : n' ≫ p.map χ = s.fst) (hn'a : n' ≫ p.map a = s.snd) :
    n = n' := by
  let u := Functor.IsPreFibered.pullbackObj (p := p) rfl s.fst
  let τ : u ⟶ z := Functor.IsPreFibered.pullbackMap (p := p) rfl s.fst
  letI : p.IsStronglyCartesian s.fst τ :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian p s.fst τ
  let α : u ⟶ x :=
    Functor.IsStronglyCartesian.map p (p.map φ) φ s.condition (τ ≫ g)
  letI : p.IsHomLift s.snd α := inferInstance
  have hα_fac : α ≫ φ = τ ≫ g := by
    -- The canonical second leg upstairs comes from the strong-cartesian factorization through `φ`.
    exact Functor.IsStronglyCartesian.fac p (p.map φ) φ s.condition (τ ≫ g)
  let m : u ⟶ w := h.lift τ α hα_fac.symm
  have hm_fst : m ≫ χ = τ := by
    -- The total pullback mediator recovers the canonical first leg.
    simpa [m] using h.lift_fst τ α hα_fac.symm
  have hm_snd : m ≫ a = α := by
    -- The same mediator recovers the canonical second leg.
    simpa [m] using h.lift_snd τ α hα_fac.symm
  have hu : p.obj u = s.pt := IsHomLift.domain_eq p s.fst τ
  let canonical : s.pt ⟶ p.obj w := eqToHom hu.symm ≫ p.map m
  let un := Functor.IsPreFibered.pullbackObj (p := p) rfl n
  let μn : un ⟶ w := Functor.IsPreFibered.pullbackMap (p := p) rfl n
  obtain ⟨en, hen, hfactor_n⟩ :=
    candidate_lift_factors_through_pullback_mediator
      (p := p) (hφ := hφ) (h := h) (s := s) (τ := τ) (α := α) (hα_fac := hα_fac)
      (m := m) hm_fst hm_snd (μ := μn) hnχ hna
  letI : p.IsHomLift (𝟙 s.pt) en := hen
  have hn_canonical : n = canonical := by
    -- Every candidate mediator descends from the same canonical upstairs mediator.
    simpa [canonical] using
      base_mediator_eq_of_upstairs_comparison (p := p) (u := u) (uq := un)
        (w := w) (R := s.pt) (q := n) (μ := μn) (e := en) (m := m) hu hfactor_n
  let un' := Functor.IsPreFibered.pullbackObj (p := p) rfl n'
  let μn' : un' ⟶ w := Functor.IsPreFibered.pullbackMap (p := p) rfl n'
  obtain ⟨en', hen', hfactor_n'⟩ :=
    candidate_lift_factors_through_pullback_mediator
      (p := p) (hφ := hφ) (h := h) (s := s) (τ := τ) (α := α) (hα_fac := hα_fac)
      (m := m) hm_fst hm_snd (μ := μn') hn'χ hn'a
  letI : p.IsHomLift (𝟙 s.pt) en' := hen'
  have hn'_canonical : n' = canonical := by
    -- The same normalization applies to any other mediator with the same projection equations.
    simpa [canonical] using
      base_mediator_eq_of_upstairs_comparison (p := p) (u := u) (uq := un')
        (w := w) (R := s.pt) (q := n') (μ := μn') (e := en') (m := m) hu hfactor_n'
  exact hn_canonical.trans hn'_canonical.symm

/-- Helper for Lemma 8.10.1: mapping a pullback square upstairs along a strongly cartesian arrow
produces a pullback square in the base category. -/
private theorem mapped_square_isPullback_aux
    [p.IsFibered]
    {x y z w : S} {φ : x ⟶ y} {g : z ⟶ y} {χ : w ⟶ z} {a : w ⟶ x}
    (hφ : p.IsStronglyCartesian (p.map φ) φ)
    (h : IsPullback χ a g φ) :
    IsPullback (p.map χ) (p.map a) (p.map g) (p.map φ) := by
  -- Route correction: keep the original `IsPullback.mk'` route, but use the canonical-mediator
  -- normalization above instead of a monolithic transport-heavy uniqueness proof.
  refine IsPullback.mk' ?_ ?_ ?_
  · -- The base square commutes because `p` preserves composition.
    simpa [Functor.map_comp] using congrArg (Functor.map p) h.w
  · intro t n n' hnχ hn'a
    let s : PullbackCone (p.map g) (p.map φ) :=
      PullbackCone.mk (n ≫ p.map χ) (n ≫ p.map a) <| by
        simpa only [Functor.map_comp, Category.assoc] using
          congrArg (fun m ↦ n ≫ p.map m) h.w
    -- Uniqueness of descended mediators is exactly the repaired helper above.
    exact base_pullback_mediator_unique_of_total_pullback
      (p := p) (hφ := hφ) (h := h) (s := s) rfl rfl hnχ.symm hn'a.symm
  · intro t b c hbc
    let s : PullbackCone (p.map g) (p.map φ) := PullbackCone.mk b c hbc
    -- The existence half is already provided by the upstairs pullback mediator.
    exact base_pullback_mediator_of_total_pullback (p := p) (hφ := hφ) (h := h) s

/-- Helper for Lemma 8.10.1: in a pullback square above a strongly cartesian arrow, the first leg
is strongly cartesian over its image in the base. -/
theorem pullback_first_leg_isStronglyCartesian
    [p.IsFibered]
    {x y z w : S} {φ : x ⟶ y} {g : z ⟶ y} {χ : w ⟶ z} {a : w ⟶ x}
    (hφ : p.IsStronglyCartesian (p.map φ) φ)
    (h : IsPullback χ a g φ) :
    p.IsStronglyCartesian (p.map χ) χ := by
  letI : p.IsStronglyCartesian (p.map φ) φ := hφ
  refine { universal_property' := ?_ }
  intro t k τ hτ
  letI : p.IsHomLift (k ≫ p.map χ) τ := hτ
  have hk :
      (k ≫ p.map χ) ≫ p.map g = (k ≫ p.map a) ≫ p.map φ := by
    -- Mapping the pullback identity downstairs identifies the two base factorizations of `τ ≫ g`.
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun m ↦ k ≫ p.map m) h.w
  obtain ⟨a', ha', ha'_fac⟩ :=
    pullback_factor_through_strong_right_leg (p := p) (hφ := hφ) (h := h) hτ
  letI : p.IsHomLift (k ≫ p.map a) a' := ha'
  let m : t ⟶ w := h.lift τ a' ha'_fac.symm
  have hm : p.IsHomLift k m := by
    -- The mapped square is a pullback in the base, so equality of the two projections forces the
    -- pullback mediator to lie over the prescribed base arrow `k`.
    have hbase :
        IsPullback (p.map χ) (p.map a) (p.map g) (p.map φ) :=
      mapped_square_isPullback_aux (p := p) (hφ := hφ) (h := h)
    have hmχ : p.map m ≫ p.map χ = k ≫ p.map χ := by
      calc
        p.map m ≫ p.map χ = p.map (m ≫ χ) := by rw [Functor.map_comp]
        _ = p.map τ := by
          simpa [m] using congrArg (Functor.map p) (h.lift_fst τ a' ha'_fac.symm)
        _ = k ≫ p.map χ := by
          symm
          exact IsHomLift.eq_of_isHomLift p (k ≫ p.map χ) τ
    have hma : p.map m ≫ p.map a = k ≫ p.map a := by
      calc
        p.map m ≫ p.map a = p.map (m ≫ a) := by rw [Functor.map_comp]
        _ = p.map a' := by
          simpa [m] using congrArg (Functor.map p) (h.lift_snd τ a' ha'_fac.symm)
        _ = k ≫ p.map a := by
          symm
          exact IsHomLift.eq_of_isHomLift p (k ≫ p.map a) a'
    have hmapm : p.map m = k := by
      apply hbase.hom_ext
      · exact hmχ
      · exact hma
    exact IsHomLift.of_fac' p k m rfl rfl (by simpa using hmapm)
  refine ⟨m, ⟨hm, ?_⟩, ?_⟩
  · -- The pullback mediator was chosen to recover `τ` along the first leg.
    simpa [m] using h.lift_fst τ a' ha'_fac.symm
  · intro n hn
    rcases hn with ⟨hn_over, hn_fac⟩
    letI : p.IsHomLift k n := hn_over
    have hna_to_map :
        n ≫ a =
          Functor.IsStronglyCartesian.map p (p.map φ) φ hk (τ ≫ g) := by
      exact
        Functor.IsStronglyCartesian.map_uniq p (p.map φ) φ hk (τ ≫ g) (n ≫ a) <| by
          calc
            (n ≫ a) ≫ φ = n ≫ (a ≫ φ) := by simp [Category.assoc]
            _ = n ≫ (χ ≫ g) := by rw [← h.w]
            _ = (n ≫ χ) ≫ g := by simp only [Category.assoc]
            _ = τ ≫ g := by rw [hn_fac]
    have ha'_to_map :
        a' = Functor.IsStronglyCartesian.map p (p.map φ) φ hk (τ ≫ g) := by
      exact Functor.IsStronglyCartesian.map_uniq p (p.map φ) φ hk (τ ≫ g) a' ha'_fac
    have hna : n ≫ a = a' := by
      rw [hna_to_map, ha'_to_map]
    -- Equality in the pullback follows from equality of both projections.
    apply h.hom_ext
    · simpa [m, hn_fac] using h.lift_fst τ a' ha'_fac.symm
    · simpa [m, hna] using h.lift_snd τ a' ha'_fac.symm

/-- Helper for Lemma 8.10.1: mapping a pullback square upstairs along a strongly cartesian arrow
produces a pullback square in the base category. -/
theorem mapped_square_isPullback_of_isPullback_of_isStronglyCartesian
    [p.IsFibered]
    {x y z w : S} {φ : x ⟶ y} {g : z ⟶ y} {χ : w ⟶ z} {a : w ⟶ x}
    (hφ : p.IsStronglyCartesian (p.map φ) φ)
    (h : IsPullback χ a g φ) :
    IsPullback (p.map χ) (p.map a) (p.map g) (p.map φ) := by
  -- The private helper establishes the base pullback without assuming the first leg is already
  -- strongly cartesian, so the public statement is now just the reusable wrapper.
  exact mapped_square_isPullback_aux (p := p) (hφ := hφ) (h := h)

/-- Helper for Lemma 8.10.1: in a pullback square above a strongly cartesian arrow, the left leg
is again strongly cartesian. -/
theorem pullback_left_leg_isStronglyCartesian_of_isPullback
    [p.IsFibered]
    {x y z w : S} {φ : x ⟶ y} {g : z ⟶ y} {χ : w ⟶ z} {a : w ⟶ x}
    (hφ : p.IsStronglyCartesian (p.map φ) φ)
    (h : IsPullback χ a g φ) :
    p.IsStronglyCartesian (p.map χ) χ := by
  -- The strong-cartesian lift property of the first leg was already established directly above.
  exact pullback_first_leg_isStronglyCartesian (p := p) (hφ := hφ) (h := h)

-- Proof sketch: pull back a strongly cartesian covering family along a map in `S`. Fibredness
-- produces the pullback objects upstairs, their projections remain strongly cartesian, and the
-- image family downstairs is a base change of a `J`-covering family.
/-- The inherited precoverage is stable under base change. -/
instance [J.IsStableUnderBaseChange] [p.IsFibered] :
    (stronglyCartesianLiftPrecoverage J p).IsStableUnderBaseChange where
  mem_coverings_of_isPullback := by
    intro ι x X f hf y g P p₁ p₂ h
    rw [ofArrows_mem_stronglyCartesianLiftPrecoverage_iff] at hf
    refine (ofArrows_mem_stronglyCartesianLiftPrecoverage_iff
      (J := J) (p := p) (X := P) p₁).2 ?_
    refine ⟨?_, ?_⟩
    · intro i
      -- Each first pullback leg is strongly cartesian over its image in the base.
      exact pullback_left_leg_isStronglyCartesian_of_isPullback
        (p := p) (hφ := hf.1 i) (h := h i)
    · -- The image family downstairs is a base change of the original covering family.
      exact J.mem_coverings_of_isPullback
        (fun i ↦ p.map (f i))
        hf.2
        (p.map g)
        (fun i ↦ p.map (p₁ i))
        (fun i ↦ p.map (p₂ i))
        (fun i ↦ mapped_square_isPullback_of_isPullback_of_isStronglyCartesian
          (p := p) (hφ := hf.1 i) (h := h i))

-- Proof sketch: compose two inherited covering families. Strong cartesianness is preserved by
-- composition, and the image family downstairs is a composite covering family for `J`.
/-- The inherited precoverage is stable under composition of covering families. -/
instance [J.IsStableUnderComposition] :
    (stronglyCartesianLiftPrecoverage J p).IsStableUnderComposition where
  comp_mem_coverings := by
    intro ι x X f hf σ Y g hg
    rw [ofArrows_mem_stronglyCartesianLiftPrecoverage_iff] at hf
    refine (ofArrows_mem_stronglyCartesianLiftPrecoverage_iff
      (J := J) (p := p) (X := fun x : Σ i, σ i ↦ Y x.1 x.2)
      (fun x ↦ g x.1 x.2 ≫ f x.1)).2 ?_
    refine ⟨?_, ?_⟩
    · rintro ⟨i, j⟩
      have hgi :
          (∀ j, p.IsStronglyCartesian (p.map (g i j)) (g i j)) ∧
            Presieve.ofArrows (p.obj ∘ Y i) (fun j ↦ p.map (g i j)) ∈ J (p.obj (X i)) :=
        (ofArrows_mem_stronglyCartesianLiftPrecoverage_iff
          (J := J) (p := p) (X := Y i) (g i)).1 (hg i)
      let _ : p.IsStronglyCartesian (p.map (g i j)) (g i j) := hgi.1 j
      let _ : p.IsStronglyCartesian (p.map (f i)) (f i) := hf.1 i
      simpa [Functor.map_comp] using
        (inferInstance :
          p.IsStronglyCartesian (p.map (g i j) ≫ p.map (f i)) (g i j ≫ f i))
    · -- The image family downstairs is exactly the composite covering family for `J`.
      simpa [Functor.map_comp] using
        J.comp_mem_coverings
          (f := fun i ↦ p.map (f i))
          hf.2
          (g := fun i j ↦ p.map (g i j))
          (fun i ↦
            (ofArrows_mem_stronglyCartesianLiftPrecoverage_iff
              (J := J) (p := p) (X := Y i) (g i)).1 (hg i) |>.2)

end

end CategoryTheory
