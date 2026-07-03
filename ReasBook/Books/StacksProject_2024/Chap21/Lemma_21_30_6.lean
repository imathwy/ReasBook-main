import Mathlib

open CategoryTheory CategoryTheory.Limits

universe u v w

noncomputable section

/-- A source-facing abstraction of the setup used to compare `τ`- and `τ'`-cohomology. -/
structure ComparingCohomologySituation (C : Type u) [Category.{v} C] [HasPullbacks C] where
  tau : GrothendieckTopology C
  tauPrime : GrothendieckTopology C
  P : MorphismProperty C
  coeff : C → Type w
  cohomology : ∀ {Y : C}, ℕ → coeff Y → Over Y → Type w
  cohomologyGroup : ∀ {Y : C} (n : ℕ) (F : coeff Y) (U : Over Y),
    AddCommGroup (cohomology n F U)
  map : ∀ {Y : C} (n : ℕ) (F : coeff Y) {U V : Over Y}, (U ⟶ V) →
    cohomology n F V → cohomology n F U

attribute [instance] ComparingCohomologySituation.cohomologyGroup

/-- The object of `Over Y` corresponding to the base change `X ×_Y Z → Y`. -/
abbrev baseChangeOver {C : Type u} [Category.{v} C] [HasPullbacks C] {X Y Z : C}
    (f : X ⟶ Y) (g : Z ⟶ Y) : Over Y :=
  Over.mk (pullback.fst f g ≫ f)

/-- The structure map of `baseChangeOver f g` is the first pullback projection followed by `f`. -/
-- Proof sketch: unfold `baseChangeOver` and `Over.mk`.
theorem baseChangeOver_hom {C : Type u} [Category.{v} C] [HasPullbacks C] {X Y Z : C}
    (f : X ⟶ Y) (g : Z ⟶ Y) :
    (baseChangeOver f g).hom = pullback.fst f g ≫ f := sorry

/-- In the self-pullback of `f`, the second projection composed with `f` equals the first. -/
-- Proof sketch: this is the pullback commutativity relation for the square defined by `f`.
theorem self_pullback_snd_comp_eq {C : Type u} [Category.{v} C] [HasPullbacks C] {X Y : C}
    (f : X ⟶ Y) :
    pullback.snd f f ≫ f = pullback.fst f f ≫ f := sorry

/-- Lemma 21.30.6: if a class in `H^(n + 1)(X, F')` has equal pullbacks to `X ×_Y X`, then after
some `τ'`-covering of `Y` its pullback to each `Yᵢ ×_Y X` vanishes. -/
-- Proof sketch: reinterpret `θ` as a section of the higher direct image on `Y`, use the equality
-- on `X ×_Y X` to show its pullback to `X` is zero, and then apply the `τ`-sheaf property together
-- with trivial base change to obtain a `τ'`-covering on which the class vanishes.
theorem equalizer_class_vanishes_after_tauPrime_cover
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    (S : ComparingCohomologySituation C) {X Y : C} (f : X ⟶ Y)
    (hfP : S.P f)
    (hfcover : Sieve.generateFamily (fun _ : PUnit ↦ X) (fun _ ↦ f) ∈ S.tau Y)
    (F : S.coeff Y) (n : ℕ)
    (θ : S.cohomology (n + 1) F (Over.mk f))
    (hθ :
      S.map (n + 1) F
          (((Over.homMk (pullback.fst f f)) : baseChangeOver f f ⟶ Over.mk f)) θ =
        S.map (n + 1) F
          (((Over.homMk (pullback.snd f f) (self_pullback_snd_comp_eq f)) :
              baseChangeOver f f ⟶ Over.mk f)) θ) :
    ∃ (ι : Type (max u v w)) (Yᵢ : ι → C) (π : ∀ i, Yᵢ i ⟶ Y),
      Sieve.generateFamily Yᵢ π ∈ S.tauPrime Y ∧
      ∀ i,
        S.map (n + 1) F
            (((Over.homMk (pullback.fst f (π i))) : baseChangeOver f (π i) ⟶ Over.mk f)) θ = 0 :=
  sorry
