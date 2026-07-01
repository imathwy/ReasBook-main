import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open Limits CategoricalPullback

universe uC uD uS vC vD vS

namespace CategoryTheory

section

/- Domain-style sampling for Lemma 8.12.1:
- primary domain: fibred categories and categorical pullbacks of functors.
- inspected owner-level declarations:
  `Functor.IsFibered`,
  `Functor.IsFibered.of_exists_isStronglyCartesian`,
  `CategoricalPullback`,
  `CategoricalPullback.π₁`.
- best owner abstraction: the canonical owner predicate is `Functor.IsFibered`, applied to the
  pullback projection `π₁ u p`; `CategoricalPullback u p` is the canonical pullback model.
- primitive data: a functor `u : C ⥤ D`, a fibred functor `p : S ⥤ D`, and the pullback category
  `CategoricalPullback u p`.
- derived API: the induced fibred structure on `π₁ u p`.

Source/core/bridge triage:
- `source-facing`: `pullback_projection_is_fibered`.
- `core/canonical`: `Functor.IsFibered` and `CategoricalPullback`.
- `bridge/view`: the instance on `π₁ u p`, derived from the source-facing theorem without adding a
  parallel owner. -/

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]
variable (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]

/-- Lemma 8.12.1: if `p : S ⥤ D` is a fibred category over `D` and `u : C ⥤ D`, then the
pullback category `u^p S`, modeled by the categorical pullback `CategoricalPullback u p`, is a
fibred category over `C` via the first projection. -/
-- Proof sketch: for an arrow `a : U ⟶ U'` in `C` and an object of the pullback category over
-- `U'`, choose a strongly cartesian lift in `S` of `u.map a`; pairing it with `a` gives a lift in
-- the pullback category. Strong-cartesianness in the pullback is detected on the second
-- component, so the existence of such lifts in `S` upgrades to fibredness of the first
-- projection.
theorem pullback_projection_is_fibered
    : (π₁ u p).IsFibered := by
  refine IsFibered.of_exists_isStronglyCartesian ?_
  intro x R f
  let baseMap : u.obj R ⟶ p.obj x.snd := u.map f ≫ x.iso.hom
  obtain ⟨y, ψ, hψcart⟩ := IsPreFibered.exists_isCartesian p rfl baseMap
  letI : p.IsCartesian baseMap ψ := hψcart
  letI : p.IsStronglyCartesian baseMap ψ :=
    IsFibered.isStronglyCartesian_of_isCartesian p baseMap ψ
  have hy : p.obj y = u.obj R := IsHomLift.domain_eq p baseMap ψ
  let y' : CategoricalPullback u p :=
    { fst := R
      snd := y
      iso := eqToIso hy.symm }
  let φ : y' ⟶ x :=
    { fst := f
      snd := ψ
      w := by
        dsimp [y', baseMap]
        have hψfac : p.map ψ = eqToHom hy ≫ baseMap := by
          simpa [baseMap] using (IsHomLift.fac' p baseMap ψ)
        calc
          baseMap = eqToHom hy.symm ≫ (eqToHom hy ≫ baseMap) := by simp
          _ = eqToHom hy.symm ≫ p.map ψ := by rw [hψfac] }
  refine ⟨y', φ, ?_⟩
  change (π₁ u p).IsStronglyCartesian f φ
  refine
    { toIsHomLift := by
        simpa [φ] using
          (show (π₁ u p).IsHomLift ((π₁ u p).map φ) φ from inferInstance)
      universal_property' := ?_ }
  intro z g θ hθ
  have hθfst : g ≫ f = θ.fst := IsHomLift.eq_of_isHomLift (π₁ u p) (g ≫ f) θ
  have hθsnd : p.map θ.snd = (z.iso.inv ≫ u.map g) ≫ baseMap := by
    calc
      p.map θ.snd = z.iso.inv ≫ (z.iso.hom ≫ p.map θ.snd) := by simp
      _ = z.iso.inv ≫ (u.map θ.fst ≫ x.iso.hom) := by rw [θ.w]
      _ = z.iso.inv ≫ u.map g ≫ u.map f ≫ x.iso.hom := by
        rw [← hθfst]
        simp [Functor.map_comp, Category.assoc]
      _ = (z.iso.inv ≫ u.map g) ≫ baseMap := by
        simp [baseMap, Category.assoc]
  letI : p.IsHomLift ((z.iso.inv ≫ u.map g) ≫ baseMap) θ.snd :=
    IsHomLift.of_fac' p (((z.iso.inv ≫ u.map g) ≫ baseMap)) θ.snd rfl rfl (by
      simpa using hθsnd)
  obtain ⟨χ, hχ, hχuniq⟩ :=
    IsStronglyCartesian.universal_property p baseMap ψ (z.iso.inv ≫ u.map g)
      (((z.iso.inv ≫ u.map g) ≫ baseMap)) rfl θ.snd
  letI : p.IsHomLift (z.iso.inv ≫ u.map g) χ := hχ.1
  let χ' : z ⟶ y' :=
    { fst := g
      snd := χ
      w := by
        have hχfac : p.map χ = eqToHom rfl ≫ (z.iso.inv ≫ u.map g) ≫ eqToHom hy.symm := by
          simpa using (IsHomLift.fac' p (z.iso.inv ≫ u.map g) χ)
        dsimp [y']
        calc
          u.map g ≫ eqToHom hy.symm = z.iso.hom ≫ (z.iso.inv ≫ u.map g) ≫ eqToHom hy.symm := by
            simp [Category.assoc]
          _ = z.iso.hom ≫ p.map χ := by
            rw [hχfac]
            simp [Category.assoc] }
  refine ⟨χ', ⟨by
    simpa [χ'] using
      (show (π₁ u p).IsHomLift ((π₁ u p).map χ') χ' from inferInstance), ?_⟩, ?_⟩
  · ext
    · simpa [χ', φ] using hθfst
    · exact hχ.2
  · intro τ hτ
    have hτfst : g = τ.fst := by
      simpa using
        (@IsHomLift.eq_of_isHomLift _ _ _ _ (π₁ u p) _ _ g τ hτ.1)
    apply CategoricalPullback.hom_ext
    · simpa [χ'] using hτfst.symm
    · have hτsnd : p.map τ.snd = z.iso.inv ≫ u.map g ≫ eqToHom hy.symm := by
        calc
          p.map τ.snd = z.iso.inv ≫ (z.iso.hom ≫ p.map τ.snd) := by simp
          _ = z.iso.inv ≫ (u.map τ.fst ≫ y'.iso.hom) := by
            rw [← τ.w]
          _ = z.iso.inv ≫ (u.map τ.fst ≫ eqToHom hy.symm) := by
            dsimp [y']
          _ = z.iso.inv ≫ u.map g ≫ eqToHom hy.symm := by
            simp [hτfst]
      letI : p.IsHomLift (z.iso.inv ≫ u.map g) τ.snd :=
        IsHomLift.of_fac' p (z.iso.inv ≫ u.map g) τ.snd rfl hy (by
          simpa using hτsnd)
      have hτcomp : τ.snd ≫ ψ = θ.snd := by
        simpa using congrArg CategoricalPullback.Hom.snd hτ.2
      exact hχuniq τ.snd ⟨inferInstance, hτcomp⟩

instance
    : (π₁ u p).IsFibered :=
  pullback_projection_is_fibered u p

end

end CategoryTheory
