import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.CategoryTheory.Shift.ShiftedHom
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap22.Definition_22_25_3

open scoped DirectSum

noncomputable section

universe w v u

namespace CategoryTheory

section

variable (C : Type u) [Category.{v} C]

/- Source/core/bridge triage for Remark 22.25.7:
- source-facing: the graded category `C^gr` with the same objects as `C` and total Hom groups
  `⨁ n : ℤ, ShiftedHom X Y n`;
- core/canonical: `ShiftedHom`, `ShiftedHom.comp`, and `ShiftedHom.homEquiv`;
- bridge/view: the `GradedCategory` instance on `C^gr`, the inherited shift functors, the target
  shift equivalence on degree pieces, and the degree-zero recovery `(C^gr)^0 = C`. -/

/-- Remark 22.25.7: if `C` has shifts by `ℤ`, then `C^gr` is the category with the same objects as
`C` and total Hom from `X` to `Y` given by the direct sum of the shifted-Hom groups
`⨁ n : ℤ, (X ⟶ Y⟦n⟧)`. Under the additional linearity hypotheses below, this becomes the graded
category attached to `C` in the sense of Chapter 22. -/
@[stacks 09P3]
structure ShiftedHomCategory where
  obj : C

namespace ShiftedHomCategory

scoped notation:max C:max "^gr" => ShiftedHomCategory C

instance : CoeTC (C^gr) C where
  coe X := X.obj

omit [Category.{v} C] in
@[simp] theorem coe_mk (X : C) : ((⟨X⟩ : C^gr) : C) = X :=
  rfl

section Basic

open scoped ShiftedHomCategory
open scoped GradedCategory

variable [Preadditive C] [HasShift C ℤ]
variable [∀ n : ℤ, (shiftFunctor C n).Additive]

/-- The homogeneous degree-`n` morphisms in `C^gr`. -/
private abbrev shiftedHom (X Y : C^gr) (n : ℤ) : Type v :=
  ShiftedHom (X : C) (Y : C) n

/-- Remark 22.25.7: the total Hom in `C^gr` is the direct sum of the shifted-Hom groups. -/
@[stacks 09P3]
abbrev homSpace (X Y : C^gr) :=
  ⨁ n : ℤ, ShiftedHom (X : C) (Y : C) n

omit [∀ n : ℤ, (shiftFunctor C n).Additive] in
/-- `homSpace` is definitionally the direct sum of the shifted-Hom groups. -/
theorem homSpace_def (X Y : C^gr) :
    homSpace C X Y = ⨁ n : ℤ, ShiftedHom (X : C) (Y : C) n :=
  rfl

/-- The degree-`0` identity in `C^gr`, viewed as a shifted morphism. -/
def idHom (X : C^gr) : ShiftedHom (X : C) (X : C) (0 : ℤ) :=
  ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 (X : C))

/-- The identity morphism in `C^gr` is concentrated in degree `0`. -/
def idSpace (X : C^gr) : homSpace C X X :=
  DirectSum.of (fun n ↦ shiftedHom C X X n) 0 (idHom C X)

/- The canonical composition owner for Remark 22.25.7 is `ShiftedHom.comp`. -/
recall ShiftedHom.comp

/-- Remark 22.25.7: composing a degree-`m` morphism with a degree-`n` morphism in `C^gr`
produces a degree-`n + m` morphism. -/
@[stacks 09P3]
abbrev compHomDegree
    {X Y Z : C^gr} {m n : ℤ}
    (g : ShiftedHom (Y : C) (Z : C) m)
    (f : ShiftedHom (X : C) (Y : C) n) :
    ShiftedHom (X : C) (Z : C) (n + m) :=
  ShiftedHom.comp f g (add_comm m n)

/- `compHomDegree` is the source-facing `n + m` specialization of `ShiftedHom.comp`. -/
omit [Preadditive C] in
theorem compHomDegree_def
    {X Y Z : C^gr} {m n : ℤ}
    (g : ShiftedHom (Y : C) (Z : C) m)
    (f : ShiftedHom (X : C) (Y : C) n) :
    compHomDegree C g f =
      ShiftedHom.comp f g (by simpa [add_comm]) :=
  rfl

@[simp] theorem compHomDegree_add_left
    {X Y Z : C^gr} {m n : ℤ}
    (g₁ g₂ : ShiftedHom (Y : C) (Z : C) m)
    (f : ShiftedHom (X : C) (Y : C) n) :
    compHomDegree C (g₁ + g₂) f =
      compHomDegree C g₁ f + compHomDegree C g₂ f := by
  simpa [compHomDegree] using ShiftedHom.comp_add f g₁ g₂ (add_comm m n)

omit [∀ n : ℤ, (shiftFunctor C n).Additive] in
@[simp] theorem compHomDegree_add_right
    {X Y Z : C^gr} {m n : ℤ}
    (g : ShiftedHom (Y : C) (Z : C) m)
    (f₁ f₂ : ShiftedHom (X : C) (Y : C) n) :
    compHomDegree C g (f₁ + f₂) =
      compHomDegree C g f₁ + compHomDegree C g f₂ := by
  simpa [compHomDegree] using ShiftedHom.add_comp f₁ f₂ g (add_comm m n)

@[simp] theorem compHomDegree_smul_left
    {X Y Z : C^gr} {m n : ℤ}
    (r : ℤ) (g : ShiftedHom (Y : C) (Z : C) m)
    (f : ShiftedHom (X : C) (Y : C) n) :
    compHomDegree C (r • g) f = r • compHomDegree C g f := by
  simpa [compHomDegree] using ShiftedHom.comp_smul r f g (add_comm m n)

omit [∀ n : ℤ, (shiftFunctor C n).Additive] in
@[simp] theorem compHomDegree_smul_right
    {X Y Z : C^gr} {m n : ℤ}
    (r : ℤ) (g : ShiftedHom (Y : C) (Z : C) m)
    (f : ShiftedHom (X : C) (Y : C) n) :
    compHomDegree C g (r • f) = r • compHomDegree C g f := by
  simpa [compHomDegree] using ShiftedHom.smul_comp r f g (add_comm m n)

private def compHomLinear
    {X Y Z : C^gr} {m n : ℤ}
    (g : shiftedHom C X Y m) :
    shiftedHom C Z X n →ₗ[ℤ] shiftedHom C Z Y (n + m) where
  toFun := compHomDegree C g
  map_add' := by
    intro f₁ f₂
    simpa using compHomDegree_add_right C g f₁ f₂
  map_smul' := by
    intro r f
    simpa using compHomDegree_smul_right C r g f

private def postcomposeHom
    {X Y Z : C^gr} {m : ℤ}
    (g : shiftedHom C Y Z m) :
    homSpace C X Y →ₗ[ℤ] homSpace C X Z :=
  DirectSum.toModule ℤ ℤ (homSpace C X Z)
    (fun n ↦
      (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Z i) (n + m)).comp
        (compHomLinear C g))

private def composeByDegree
    {X Y Z : C^gr} (m : ℤ) :
    shiftedHom C Y Z m →ₗ[ℤ] homSpace C X Y →ₗ[ℤ] homSpace C X Z :=
  { toFun := fun g ↦ postcomposeHom C g
    map_add' := by
      intro g₁ g₂
      apply DirectSum.linearMap_ext
      intro n
      apply LinearMap.ext
      intro f
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      change
        postcomposeHom C (g₁ + g₂)
            ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Y i) n) f) =
          postcomposeHom C g₁
              ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Y i) n) f) +
            postcomposeHom C g₂
              ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Y i) n) f)
      change
        DirectSum.toModule ℤ ℤ (homSpace C X Z)
            (fun k ↦
              (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Z i) (k + m)).comp
                (compHomLinear C (g₁ + g₂)))
            ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Y i) n) f) =
          DirectSum.toModule ℤ ℤ (homSpace C X Z)
              (fun k ↦
                (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Z i) (k + m)).comp
                  (compHomLinear C g₁))
              ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Y i) n) f) +
            DirectSum.toModule ℤ ℤ (homSpace C X Z)
              (fun k ↦
                (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Z i) (k + m)).comp
                  (compHomLinear C g₂))
              ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Y i) n) f)
      repeat rw [DirectSum.toModule_lof]
      change
        (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Z i) (n + m))
            (compHomDegree C (g₁ + g₂) f) =
          (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Z i) (n + m))
            (compHomDegree C g₁ f) +
              (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Z i) (n + m))
                (compHomDegree C g₂ f)
      simpa using
        congrArg
          (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Z i) (n + m))
          (compHomDegree_add_left C g₁ g₂ f)
    map_smul' := by
      intro r g
      apply DirectSum.linearMap_ext
      intro n
      apply LinearMap.ext
      intro f
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      change
        postcomposeHom C (r • g)
            ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Y i) n) f) =
          (((RingHom.id ℤ) r) • postcomposeHom C g)
            ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Y i) n) f)
      change
        DirectSum.toModule ℤ ℤ (homSpace C X Z)
            (fun k ↦
              (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Z i) (k + m)).comp
                (compHomLinear C (r • g)))
            ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Y i) n) f) =
          (((RingHom.id ℤ) r) •
              DirectSum.toModule ℤ ℤ (homSpace C X Z)
                (fun k ↦
                  (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Z i) (k + m)).comp
                    (compHomLinear C g)))
            ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Y i) n) f)
      change
        DirectSum.toModule ℤ ℤ (homSpace C X Z)
            (fun k ↦
              (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Z i) (k + m)).comp
                (compHomLinear C (r • g)))
            ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Y i) n) f) =
          r •
            DirectSum.toModule ℤ ℤ (homSpace C X Z)
              (fun k ↦
                (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Z i) (k + m)).comp
                  (compHomLinear C g))
              ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Y i) n) f)
      repeat rw [DirectSum.toModule_lof]
      change
        (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Z i) (n + m))
            (compHomDegree C (r • g) f) =
          r •
            (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Z i) (n + m))
              (compHomDegree C g f)
      simpa using
        congrArg
          (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Z i) (n + m))
          (compHomDegree_smul_left C r g f) }

private def compLinear
    {X Y Z : C^gr} :
    homSpace C Y Z →ₗ[ℤ] homSpace C X Y →ₗ[ℤ] homSpace C X Z :=
  DirectSum.toModule ℤ ℤ (homSpace C X Y →ₗ[ℤ] homSpace C X Z) (composeByDegree C)

/-- Composition in `C^gr` is induced by composition on the homogeneous shifted-Hom pieces. -/
def compSpace
    {X Y Z : C^gr}
    (g : homSpace C Y Z) (f : homSpace C X Y) :
    homSpace C X Z :=
  compLinear C g f

@[simp] private theorem compSpace_lof_lof'
    {X Y Z : C^gr} {m n : ℤ}
    (g : ShiftedHom (Y : C) (Z : C) m)
    (f : ShiftedHom (X : C) (Y : C) n) :
    compSpace C
        ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (Y : C) (Z : C) i) m) g)
        ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (X : C) (Y : C) i) n) f) =
      (DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (X : C) (Z : C) i) (n + m))
        (compHomDegree C g f) := by
  rw [compSpace, compLinear]
  have hcompose :
      ((DirectSum.toModule ℤ ℤ (homSpace C X Y →ₗ[ℤ] homSpace C X Z)
          (composeByDegree C)
          ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (Y : C) (Z : C) i) m) g))) =
        composeByDegree C m g := by
    simpa using
      (@DirectSum.toModule_lof ℤ _ ℤ (shiftedHom C Y Z) _ _ _
        (homSpace C X Y →ₗ[ℤ] homSpace C X Z) _ _ (composeByDegree C) m g)
  have happ :
      ((DirectSum.toModule ℤ ℤ (homSpace C X Y →ₗ[ℤ] homSpace C X Z)
          (composeByDegree C)
          ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (Y : C) (Z : C) i) m) g)))
        ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (X : C) (Y : C) i) n) f) =
      (composeByDegree C m g)
        ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (X : C) (Y : C) i) n) f) := by
    exact
      congrArg
        (fun T : homSpace C X Y →ₗ[ℤ] homSpace C X Z ↦
          T ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (X : C) (Y : C) i) n) f))
        hcompose
  calc
    ((DirectSum.toModule ℤ ℤ (homSpace C X Y →ₗ[ℤ] homSpace C X Z)
        (composeByDegree C)
        ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (Y : C) (Z : C) i) m) g)))
      ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (X : C) (Y : C) i) n) f) =
        (composeByDegree C m g)
          ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (X : C) (Y : C) i) n) f) := happ
    _ = (DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (X : C) (Z : C) i) (n + m))
          (compHomDegree C g f) := by
      exact
        (@DirectSum.toModule_lof ℤ _ ℤ (shiftedHom C X Y) _ _ _ (homSpace C X Z) _ _
          (fun n ↦
            (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Z i) (n + m)).comp
              (compHomLinear C g))
          n f)

/-- Helper for Remark 22.25.7: `compSpace` on direct-sum generators is the generator attached to
the homogeneous composite. -/
@[simp] private theorem compSpace_of_of
    {X Y Z : C^gr} {m n : ℤ}
    (g : ShiftedHom (Y : C) (Z : C) m)
    (f : ShiftedHom (X : C) (Y : C) n) :
    compSpace C
        (DirectSum.of (fun i ↦ ShiftedHom (Y : C) (Z : C) i) m g)
        (DirectSum.of (fun i ↦ ShiftedHom (X : C) (Y : C) i) n f) =
      (DirectSum.of (fun i ↦ ShiftedHom (X : C) (Z : C) i) (n + m))
        (compHomDegree C g f) := by
  -- Proof comment: rewrite the source-facing `DirectSum.of` generators to `lof` so the computed
  -- homogeneous-composition formula applies directly.
  simpa [DirectSum.lof_eq_of] using compSpace_lof_lof' C g f

@[simp] theorem compSpace_lof_lof
    {X Y Z : C^gr} {m n : ℤ}
    (g : ShiftedHom (Y : C) (Z : C) m)
    (f : ShiftedHom (X : C) (Y : C) n) :
    compSpace C
        ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (Y : C) (Z : C) i) m) g)
        ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (X : C) (Y : C) i) n) f) =
      (DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (X : C) (Z : C) i) (n + m))
        (compHomDegree C g f) := by
  exact compSpace_lof_lof' C g f

@[simp] theorem compSpace_zero_left
    {X Y Z : C^gr} (f : homSpace C X Y) :
    compSpace C (0 : homSpace C Y Z) f = 0 := by
  simpa [compSpace] using
    ((compLinear C : homSpace C Y Z →ₗ[ℤ] homSpace C X Y →ₗ[ℤ] homSpace C X Z).map_zero f)

@[simp] theorem compSpace_zero_right
    {X Y Z : C^gr} (g : homSpace C Y Z) :
    compSpace C g (0 : homSpace C X Y) = 0 := by
  simpa [compSpace] using
    ((compLinear C : homSpace C Y Z →ₗ[ℤ] homSpace C X Y →ₗ[ℤ] homSpace C X Z) g).map_zero

@[simp] theorem compSpace_add_left
    {X Y Z : C^gr} (g₁ g₂ : homSpace C Y Z) (f : homSpace C X Y) :
    compSpace C (g₁ + g₂) f = compSpace C g₁ f + compSpace C g₂ f := by
  simpa [compSpace] using
    ((compLinear C : homSpace C Y Z →ₗ[ℤ] homSpace C X Y →ₗ[ℤ] homSpace C X Z)
      .map_add g₁ g₂ f)

@[simp] theorem compSpace_add_right
    {X Y Z : C^gr} (g : homSpace C Y Z) (f₁ f₂ : homSpace C X Y) :
    compSpace C g (f₁ + f₂) = compSpace C g f₁ + compSpace C g f₂ := by
  simpa [compSpace] using
    ((compLinear C : homSpace C Y Z →ₗ[ℤ] homSpace C X Y →ₗ[ℤ] homSpace C X Z) g)
      .map_add f₁ f₂

@[simp] theorem compSpace_smul_left
    {X Y Z : C^gr} (r : ℤ) (g : homSpace C Y Z) (f : homSpace C X Y) :
    compSpace C (r • g) f = r • compSpace C g f := by
  simpa [compSpace] using
    ((compLinear C : homSpace C Y Z →ₗ[ℤ] homSpace C X Y →ₗ[ℤ] homSpace C X Z)
      .map_smul r g f)

@[simp] theorem compSpace_smul_right
    {X Y Z : C^gr} (r : ℤ) (g : homSpace C Y Z) (f : homSpace C X Y) :
    compSpace C g (r • f) = r • compSpace C g f := by
  simpa [compSpace] using
    ((compLinear C : homSpace C Y Z →ₗ[ℤ] homSpace C X Y →ₗ[ℤ] homSpace C X Z) g)
      .map_smul r f

/-- Helper for Remark 22.25.7: if a homogeneous element transports along an equality of degrees to
another homogeneous element, then their direct-sum generators agree. -/
private theorem directSumOf_eq_of_transport
    {β : ℤ → Type v} [∀ i, AddCommMonoid (β i)]
    {i j : ℤ} (hij : i = j) (x : β i) (y : β j)
    (hxy : hij ▸ x = y) :
    DirectSum.of β i x = DirectSum.of β j y := by
  -- Proof comment: after eliminating the index equality, the dependent transport disappears and
  -- the claim reduces to ordinary congruence in one fixed direct-sum summand.
  cases hij
  simpa using congrArg (DirectSum.of β i) hxy

omit [Preadditive C] in
/-- Helper for Remark 22.25.7: transporting a homogeneous composite along an equality of output
degrees agrees with recomputing the same composite in the transported degree. -/
private theorem shiftedHomComp_transport
    {X Y Z : C} {a b c c' : ℤ}
    (f : ShiftedHom X Y a) (g : ShiftedHom Y Z b)
    (h : b + a = c) (hc : c = c') :
    hc ▸ ShiftedHom.comp f g h = ShiftedHom.comp f g (h.trans hc) := by
  -- Proof comment: the only dependence on `hc` is in the codomain degree, so a single `cases`
  -- computes the transport exactly.
  cases hc
  rfl

omit [Preadditive C] in
/-- Helper for Remark 22.25.7: once the target degree is fixed, the witness of that degree
equality does not affect the corresponding shifted composite. -/
private theorem shiftedHomComp_eq
    {X Y Z : C} {a b c : ℤ}
    (f : ShiftedHom X Y a) (g : ShiftedHom Y Z b)
    (h₁ h₂ : b + a = c) :
    ShiftedHom.comp f g h₁ = ShiftedHom.comp f g h₂ := by
  -- Proof comment: the proof argument lives in a proposition, so proof irrelevance identifies the
  -- two homogeneous composites.
  cases Subsingleton.elim h₁ h₂
  rfl

omit [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] in
/-- Helper for Remark 22.25.7: composing with the degree-`0` source identity agrees with the
original homogeneous map after normalizing the output degree. -/
private theorem compHomDegree_idSource_cast
    {X Y : C^gr} {n : ℤ}
    (f : ShiftedHom (X : C) (Y : C) n) :
    (zero_add n) ▸ compHomDegree C f (idHom C X) = f := by
  -- Route correction: normalize only the degree witness and then invoke the shifted-Hom identity
  -- lemma, rather than unfolding the composite itself.
  calc
    (zero_add n) ▸ compHomDegree C f (idHom C X) =
        ShiftedHom.comp (idHom C X) f ((add_comm n 0).trans (zero_add n)) := by
          -- Proof comment: move the transport from the ambient type onto the proof that records
          -- the output degree.
          simpa only [compHomDegree] using
            shiftedHomComp_transport (f := idHom C X) (g := f)
              (h := add_comm n 0) (hc := zero_add n)
    _ = f := by
      -- Proof comment: once the degree witness is normalized to `n + 0 = n`, the standard
      -- shifted-Hom source-identity lemma applies.
      simpa only [idHom] using
        (ShiftedHom.mk₀_id_comp (f := f) (m₀ := (0 : ℤ)) (hm₀ := rfl))

/-- Helper for Remark 22.25.7: the direct-sum generator obtained by composing with the degree-`0`
identity on the source agrees with the original generator. -/
@[simp] private theorem compHomDegree_idSource_of
    {X Y : C^gr} {n : ℤ}
    (f : ShiftedHom (X : C) (Y : C) n) :
    DirectSum.of (fun i ↦ ShiftedHom (X : C) (Y : C) i) (0 + n)
        (compHomDegree C f (idHom C X)) =
      DirectSum.of (fun i ↦ ShiftedHom (X : C) (Y : C) i) n f := by
  -- Proof comment: package the normalized homogeneous identity as an equality in the direct-sum
  -- owner used for the total Hom space.
  exact directSumOf_eq_of_transport (β := fun i ↦ ShiftedHom (X : C) (Y : C) i)
    (hij := zero_add n) _ _ (compHomDegree_idSource_cast (C := C) (X := X) (Y := Y) f)

omit [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] in
/-- Helper for Remark 22.25.7: composing with the degree-`0` target identity agrees with the
original homogeneous map after normalizing the output degree. -/
private theorem compHomDegree_idTarget_cast
    {X Y : C^gr} {n : ℤ}
    (f : ShiftedHom (X : C) (Y : C) n) :
    (add_zero n) ▸ compHomDegree C (idHom C Y) f = f := by
  -- Route correction: keep the transport only in the degree arithmetic and then use the
  -- shifted-Hom right-identity lemma.
  calc
    (add_zero n) ▸ compHomDegree C (idHom C Y) f =
        ShiftedHom.comp f (idHom C Y) ((add_comm 0 n).trans (add_zero n)) := by
          -- Proof comment: as on the source side, transport is absorbed into the degree witness
          -- of the homogeneous composite.
          simpa only [compHomDegree] using
            shiftedHomComp_transport (f := f) (g := idHom C Y)
              (h := add_comm 0 n) (hc := add_zero n)
    _ = f := by
      -- Proof comment: with the degree normalized to `0 + n = n`, the shifted-Hom target
      -- identity lemma closes the goal.
      simpa only [idHom] using
        (ShiftedHom.comp_mk₀_id (f := f) (m₀ := (0 : ℤ)) (hm₀ := rfl))

/-- Helper for Remark 22.25.7: the direct-sum generator obtained by composing with the degree-`0`
identity on the target agrees with the original generator. -/
@[simp] private theorem compHomDegree_idTarget_of
    {X Y : C^gr} {n : ℤ}
    (f : ShiftedHom (X : C) (Y : C) n) :
    DirectSum.of (fun i ↦ ShiftedHom (X : C) (Y : C) i) (n + 0)
        (compHomDegree C (idHom C Y) f) =
      DirectSum.of (fun i ↦ ShiftedHom (X : C) (Y : C) i) n f := by
  -- Proof comment: compare the two generators by transporting along `add_zero n`.
  exact directSumOf_eq_of_transport (β := fun i ↦ ShiftedHom (X : C) (Y : C) i)
    (hij := add_zero n) _ _ (compHomDegree_idTarget_cast (C := C) (X := X) (Y := Y) f)

omit [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] in
/-- Helper for Remark 22.25.7: homogeneous composition is associative after reassociating the
total degree. -/
private theorem compHomDegree_assoc_cast
    {W X Y Z : C^gr} {l m n : ℤ}
    (χ : ShiftedHom (Y : C) (Z : C) l)
    (ψ : ShiftedHom (X : C) (Y : C) m)
    (φ : ShiftedHom (W : C) (X : C) n) :
    (add_assoc n m l) ▸ compHomDegree C χ (compHomDegree C ψ φ) =
      compHomDegree C (compHomDegree C χ ψ) φ := by
  -- Route correction: stay in the `ShiftedHom.comp_assoc` spelling and normalize only the degree
  -- arithmetic, instead of expanding the large composite term.
  calc
    (add_assoc n m l) ▸ compHomDegree C χ (compHomDegree C ψ φ) =
        ShiftedHom.comp (compHomDegree C ψ φ) χ
          ((add_comm l (n + m)).trans (add_assoc n m l)) := by
            -- Proof comment: transport the outer composite to the final degree
            -- `n + (m + l)` before invoking associativity.
            simpa only [compHomDegree] using
              shiftedHomComp_transport (f := compHomDegree C ψ φ) (g := χ)
                (h := add_comm l (n + m)) (hc := add_assoc n m l)
    _ = ShiftedHom.comp (compHomDegree C ψ φ) χ
          (show l + (n + m) = n + (m + l) by
            simpa [add_assoc, add_comm, add_left_comm]) := by
              -- Proof comment: once the target degree is fixed, the witness proof is irrelevant.
              apply shiftedHomComp_eq
    _ = compHomDegree C (compHomDegree C χ ψ) φ := by
      -- Proof comment: the canonical `ShiftedHom.comp_assoc` lemma now matches the normalized
      -- degree bookkeeping exactly.
      simpa only [compHomDegree, add_assoc, add_comm, add_left_comm] using
        (ShiftedHom.comp_assoc (a := n + (m + l)) φ ψ χ (add_comm m n) (add_comm l m)
          (by simpa [add_assoc, add_comm, add_left_comm]))

/-- Helper for Remark 22.25.7: on homogeneous generators, graded composition is associative after
normalizing the total degree. -/
private theorem compHomDegree_assoc_of
    {W X Y Z : C^gr} {l m n : ℤ}
    (χ : ShiftedHom (Y : C) (Z : C) l)
    (ψ : ShiftedHom (X : C) (Y : C) m)
    (φ : ShiftedHom (W : C) (X : C) n) :
    DirectSum.of (fun i ↦ ShiftedHom (W : C) (Z : C) i) ((n + m) + l)
        (compHomDegree C χ (compHomDegree C ψ φ)) =
      DirectSum.of (fun i ↦ ShiftedHom (W : C) (Z : C) i) (n + (m + l))
        (compHomDegree C (compHomDegree C χ ψ) φ) := by
  -- Proof comment: convert the cast-normalized associativity bridge into an equality of the
  -- direct-sum generators in the total Hom object.
  exact directSumOf_eq_of_transport (β := fun i ↦ ShiftedHom (W : C) (Z : C) i)
    (hij := add_assoc n m l) _ _
    (compHomDegree_assoc_cast (C := C) (χ := χ) (ψ := ψ) (φ := φ))

instance instCategory : Category (C^gr) where
  Hom X Y := homSpace C X Y
  id := idSpace C
  comp f g := compSpace C g f
  id_comp := by
    intro X Y f
    -- Proof comment: reduce left identity to homogeneous generators of the direct sum.
    refine DirectSum.induction_on f ?_ ?_ ?_
    · simp
    · intro n φ
      -- Proof comment: on a generator, the direct-sum composition formula collapses to the
      -- degree-`0` identity bridge.
      rw [idSpace, compSpace_of_of]
      simpa using compHomDegree_idSource_of (C := C) (X := X) (Y := Y) (n := n) φ
    · intro x y hx hy
      -- Proof comment: additivity in the first composition slot propagates the induction step.
      simpa [compSpace_add_left, hx, hy]
  comp_id := by
    intro X Y f
    -- Proof comment: reduce right identity to homogeneous generators of the direct sum.
    refine DirectSum.induction_on f ?_ ?_ ?_
    · simp
    · intro n φ
      -- Proof comment: on a generator, the direct-sum composition formula collapses to the
      -- degree-`0` target-identity bridge.
      rw [idSpace, compSpace_of_of]
      simpa using compHomDegree_idTarget_of (C := C) (X := X) (Y := Y) (n := n) φ
    · intro x y hx hy
      -- Proof comment: additivity in the second composition slot propagates the induction step.
      simpa [compSpace_add_right, hx, hy]
  assoc := by
    intro W X Y Z f g h
    -- Proof comment: reduce associativity successively to homogeneous generators in each direct
    -- sum so that only the generator-level shifted-Hom associativity remains.
    refine DirectSum.induction_on h ?_ ?_ ?_
    · simp
    · intro l χ
      refine DirectSum.induction_on g ?_ ?_ ?_
      · simp
      · intro m ψ
        refine DirectSum.induction_on f ?_ ?_ ?_
        · simp
        · intro n φ
          -- Proof comment: on triple generators, associativity is exactly the normalized
          -- homogeneous associativity bridge.
          rw [compSpace_of_of, compSpace_of_of, compSpace_of_of, compSpace_of_of]
          simpa using compHomDegree_assoc_of (C := C) (χ := χ) (ψ := ψ) (φ := φ)
        · intro x y hx hy
          -- Proof comment: additivity in the innermost variable propagates the induction step.
          simpa [compSpace_add_right, hx, hy]
      · intro x y hx hy
        -- Proof comment: additivity in the middle variable uses bilinearity in both slots.
        simpa [compSpace_add_left, compSpace_add_right, hx, hy]
    · intro x y hx hy
      -- Proof comment: additivity in the outermost variable propagates the induction step.
      simpa [compSpace_add_left, hx, hy]

instance instPreadditive : Preadditive (C^gr) where
  homGroup X Y := by
    change AddCommGroup (homSpace C X Y)
    infer_instance
  add_comp := by
    intro X Y Z f g h
    let f' : homSpace C X Y := f
    let g' : homSpace C X Y := g
    let h' : homSpace C Y Z := h
    change compSpace C h' (f' + g') = compSpace C h' f' + compSpace C h' g'
    simpa [compSpace] using
      ((compLinear C : homSpace C Y Z →ₗ[ℤ] homSpace C X Y →ₗ[ℤ] homSpace C X Z) h')
        .map_add f' g'
  comp_add := by
    intro X Y Z f g h
    let f' : homSpace C X Y := f
    let g' : homSpace C Y Z := g
    let h' : homSpace C Y Z := h
    change compSpace C (g' + h') f' = compSpace C g' f' + compSpace C h' f'
    simpa [compSpace] using
      ((compLinear C : homSpace C Y Z →ₗ[ℤ] homSpace C X Y →ₗ[ℤ] homSpace C X Z)
        .map_add g' h' f')

/-- The object `X[n]` of `C^gr`, obtained by shifting the underlying object of `C`. -/
abbrev shiftObj (X : C^gr) (n : ℤ) : C^gr :=
  ⟨(X : C)⟦n⟧⟩

private def shiftHomLinear
    {X Y : C^gr} (n i : ℤ) :
    shiftedHom C X Y i →ₗ[ℤ] shiftedHom C (shiftObj C X n) (shiftObj C Y n) i where
  toFun f := (shiftFunctor C n).map f ≫ (shiftFunctorComm C i n).hom.app (Y : C)
  map_add' := by
    intro f g
    -- Proof comment: the shift functor is additive, so the induced map on each homogeneous piece
    -- preserves addition termwise.
    simpa [ShiftedHom.map] using
      (ShiftedHom.map_add f g (shiftFunctor C n))
  map_smul' := by
    intro r f
    -- Proof comment: additive functors are canonically `ℤ`-linear, so the homogeneous shift map
    -- preserves scalar multiplication by integers.
    simpa [ShiftedHom.map] using
      (ShiftedHom.map_smul (R := ℤ) r f (shiftFunctor C n))

private def shiftMap
    {X Y : C^gr} (n : ℤ) :
    homSpace C X Y →ₗ[ℤ] homSpace C (shiftObj C X n) (shiftObj C Y n) :=
  DirectSum.toModule ℤ ℤ (homSpace C (shiftObj C X n) (shiftObj C Y n))
    (fun i ↦
      (DirectSum.lof ℤ ℤ
          (fun j ↦ shiftedHom C (shiftObj C X n) (shiftObj C Y n) j) i).comp
        (shiftHomLinear C n i))

@[simp] theorem shiftMap_lof
    {X Y : C^gr} (n i : ℤ) (f : ShiftedHom (X : C) (Y : C) i) :
    shiftMap C n
        ((DirectSum.lof ℤ ℤ (fun j ↦ shiftedHom C X Y j) i) f) =
      (DirectSum.lof ℤ ℤ
          (fun j ↦ shiftedHom C (shiftObj C X n) (shiftObj C Y n) j) i)
        ((shiftFunctor C n).map f ≫ (shiftFunctorComm C i n).hom.app (Y : C)) := by
  -- Proof comment: `shiftMap` is defined by `DirectSum.toModule`, so evaluating it on a single
  -- direct-sum generator is exactly `DirectSum.toModule_lof`.
  exact
    (@DirectSum.toModule_lof ℤ _ ℤ (shiftedHom C X Y) _ _ _
      (homSpace C (shiftObj C X n) (shiftObj C Y n)) _ _
      (fun i ↦
        (DirectSum.lof ℤ ℤ
            (fun j ↦ shiftedHom C (shiftObj C X n) (shiftObj C Y n) j) i).comp
          (shiftHomLinear C n i))
      i f)

/-- Helper for Remark 22.25.7: `shiftMap` sends a direct-sum generator to the corresponding
shifted homogeneous generator. -/
@[simp] private theorem shiftMap_of
    {X Y : C^gr} (n i : ℤ) (f : ShiftedHom (X : C) (Y : C) i) :
    shiftMap C n (DirectSum.of (fun j ↦ shiftedHom C X Y j) i f) =
      DirectSum.of (fun j ↦ shiftedHom C (shiftObj C X n) (shiftObj C Y n) j) i
        ((shiftFunctor C n).map f ≫ (shiftFunctorComm C i n).hom.app (Y : C)) := by
  -- Proof comment: rewrite the source-facing generator from `of` to `lof` and apply the computed
  -- `shiftMap` formula on generators.
  simpa [DirectSum.lof_eq_of] using shiftMap_lof (C := C) (n := n) (i := i) f

/-- Helper for Remark 22.25.7: shifting the degree-`0` identity produces the degree-`0` identity
on the shifted object. -/
@[simp] private theorem shiftIdHom
    {X : C^gr} (n : ℤ) :
    (shiftFunctor C n).map (idHom C X) ≫ (shiftFunctorComm C 0 n).hom.app (X : C) =
      idHom C (shiftObj C X n) := by
  -- Proof comment: expand the degree-`0` generator and rewrite the remaining comparison map with
  -- the standard `shiftFunctorZero` compatibility on shifted objects.
  dsimp [idHom, ShiftedHom.mk₀, shiftObj]
  rw [Functor.map_comp, Functor.map_id, Category.id_comp]
  have hcomm : (shiftFunctorComm C 0 n).hom.app (X : C) =
      (shiftFunctorComm C n 0).inv.app (X : C) := by
    simpa using
      (congrArg (fun e => e.hom.app (X : C)) (shiftFunctorComm_symm C n 0)).symm
  rw [hcomm]
  simpa [shiftFunctorZero'] using
    (shiftFunctorZero_inv_app_shift (C := C) (A := ℤ) (X := (X : C)) (n := n)).symm

/-- Helper for Remark 22.25.7: normalize the inverse `shiftFunctorAdd'` tail that remains after
rewriting the shifted homogeneous composite into the `ShiftedHom.comp` normal form. -/
@[simp] private theorem shiftIsoAddTail_normalize
    {Z : C} (n m i : ℤ) :
    (shiftFunctor C n).map ((shiftFunctorAdd' C m i (i + m) (add_comm m i)).inv.app Z) ≫
        (Functor.CommShift.isoAdd' (F := shiftFunctor C n) (h := add_comm m i)
          (shiftFunctorComm C m n) (shiftFunctorComm C i n)).hom.app Z =
      (shiftFunctorComm C i n).hom.app (Z⟦m⟧) ≫
        ((shiftFunctorComm C m n).hom.app Z)⟦i⟧' ≫
        (shiftFunctorAdd' C m i (i + m) (add_comm m i)).inv.app (Z⟦n⟧) := by
  -- Proof comment: the generic `isoAdd'` formula already gives the right tail once we precompose
  -- by the mapped inverse `shiftFunctorAdd'` comparison and cancel that inverse/hom pair.
  rw [Functor.CommShift.isoAdd'_hom_app]
  rw [← Iso.app_inv (shiftFunctorAdd' C m i (i + m) (add_comm m i)) Z]
  simpa [Category.assoc] using
    (CategoryTheory.Iso.map_inv_hom_id_assoc
      ((shiftFunctorAdd' C m i (i + m) (add_comm m i)).app Z)
      (shiftFunctor C n)
      ((shiftFunctorComm C i n).hom.app (Z⟦m⟧) ≫
        ((shiftFunctorComm C m n).hom.app Z)⟦i⟧' ≫
        (shiftFunctorAdd' C m i (i + m) (add_comm m i)).inv.app (Z⟦n⟧)))

/-- Helper for Remark 22.25.7: normalize the inverse `shiftFunctorAdd'` tail that remains after
rewriting the shifted homogeneous composite into the `ShiftedHom.comp` normal form. -/
private theorem shiftFunctorComm_hom_app_mapShiftFunctorAddInvTail
    (n m i : ℤ) (X : C) :
    (shiftFunctorComm C n (m + i)).hom.app X ≫
        (shiftFunctor C n).map ((shiftFunctorAdd C m i).hom.app X) ≫
        (shiftFunctor C n).map ((shiftFunctorAdd' C m i (i + m) (add_comm m i)).inv.app X) =
      (shiftFunctorAdd C m i).hom.app ((shiftFunctor C n).obj X) ≫
        (shiftFunctor C i).map ((shiftFunctorComm C n m).hom.app X) ≫
        (shiftFunctorComm C n i).hom.app ((shiftFunctor C m).obj X) ≫
        (shiftFunctor C n).map ((shiftFunctorAdd' C m i (i + m) (add_comm m i)).inv.app X) := by
  -- Proof comment: specialize the owner-level `[reassoc]` coherence theorem and keep the final
  -- mapped `shiftFunctorAdd'` inverse tail explicit; this is the verified frontier for the
  -- remaining `i + m` versus `m + i` transport.
  exact
    shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd_hom_app_assoc (C := C)
      (m₁ := n) (m₂ := m) (m₃ := i) (X := X)
      (h := (shiftFunctor C n).map
        ((shiftFunctorAdd' C m i (i + m) (add_comm m i)).inv.app X))

/-- Helper for Remark 22.25.7: normalize the inverse `shiftFunctorAdd'` tail that remains after
rewriting the shifted homogeneous composite into the `ShiftedHom.comp` normal form. -/
private theorem shiftFunctorComm_eq_isoAdd'
    (n m i : ℤ) :
    shiftFunctorComm C (i + m) n =
      Functor.CommShift.isoAdd' (F := shiftFunctor C n) (h := add_comm m i)
        (shiftFunctorComm C m n) (shiftFunctorComm C i n) := by
  -- Route correction: the symmetric `isoAdd'` formula is already reduced to the helper above.
  -- TODO: cancel the remaining mapped `shiftFunctorAdd` hom/inv tail to pass from that helper to
  -- the bare comparison isomorphism.
  sorry

/-- Helper for Remark 22.25.7: normalize the inverse `shiftFunctorAdd'` tail that remains after
rewriting the shifted homogeneous composite into the `ShiftedHom.comp` normal form. -/
@[simp] private theorem shiftCompTail_normalize
    {Z : C} (n m i : ℤ) :
    (shiftFunctor C n).map ((shiftFunctorAdd' C m i (i + m) (add_comm m i)).inv.app Z) ≫
        (shiftFunctorComm C (i + m) n).hom.app Z =
      (shiftFunctorComm C i n).hom.app (Z⟦m⟧) ≫
        ((shiftFunctorComm C m n).hom.app Z)⟦i⟧' ≫
        (shiftFunctorAdd' C m i (i + m) (add_comm m i)).inv.app (Z⟦n⟧) := by
  -- Proof comment: rewrite the left comparison map to the canonical `isoAdd'` spelling, so the
  -- already-proved inverse-tail normalization lemma applies verbatim.
  rw [shiftFunctorComm_eq_isoAdd' (C := C) (n := n) (m := m) (i := i)]
  simpa using shiftIsoAddTail_normalize (C := C) (Z := Z) (n := n) (m := m) (i := i)

/-- Helper for Remark 22.25.7: shifting a homogeneous composite agrees with composing the shifted
homogeneous generators. -/
@[simp] private theorem shiftCompHomDegree_eq
    {X Y Z : C^gr} (n m i : ℤ)
    (g : ShiftedHom (Y : C) (Z : C) m)
    (f : ShiftedHom (X : C) (Y : C) i) :
    (shiftFunctor C n).map (compHomDegree C g f) ≫ (shiftFunctorComm C (i + m) n).hom.app (Z : C) =
      compHomDegree C
        (((shiftFunctor C n).map g) ≫ (shiftFunctorComm C m n).hom.app (Z : C))
        (((shiftFunctor C n).map f) ≫ (shiftFunctorComm C i n).hom.app (Y : C)) := by
  -- Route correction: the previous route kept the final `shiftFunctorComm`/`shiftFunctorAdd'`
  -- transport inside one large normalization. Rewrite the shifted `g` term once, then the
  -- remaining tail is exactly `shiftCompTail_normalize`.
  simp only [compHomDegree, ShiftedHom.comp, Functor.map_comp, Category.assoc]
  have hshift :
      (shiftFunctorComm C i n).hom.app (Y : C) ≫
          (shiftFunctor C i).map ((shiftFunctor C n).map g) ≫
          (shiftFunctor C i).map ((shiftFunctorComm C m n).hom.app (Z : C)) ≫
          (shiftFunctorAdd' C m i (i + m) (add_comm m i)).inv.app ((Z : C)⟦n⟧) =
        (shiftFunctor C n).map ((shiftFunctor C i).map g) ≫
          (shiftFunctorComm C i n).hom.app ((Z : C)⟦m⟧) ≫
          (shiftFunctor C i).map ((shiftFunctorComm C m n).hom.app (Z : C)) ≫
          (shiftFunctorAdd' C m i (i + m) (add_comm m i)).inv.app ((Z : C)⟦n⟧) := by
    -- Proof comment: this is the single reassociation step that moves the shifted `g` term into
    -- the normal form required by the tail lemma.
    simpa [shiftComm, Category.assoc] using
      (shiftComm_hom_comp_assoc (X := (Y : C)) (Y := ((Z : C)⟦m⟧)) (f := g) (i := i) (j := n)
        (h := (shiftFunctor C i).map ((shiftFunctorComm C m n).hom.app (Z : C)) ≫
          (shiftFunctorAdd' C m i (i + m) (add_comm m i)).inv.app ((Z : C)⟦n⟧)))
  -- Proof comment: after the `g`-term rewrite, both sides differ only by the canonical tail
  -- comparison between shifting a `shiftFunctorAdd'` inverse and commuting the shifts.
  calc
    (shiftFunctor C n).map f ≫
        (shiftFunctor C n).map ((shiftFunctor C i).map g) ≫
        (shiftFunctor C n).map ((shiftFunctorAdd' C m i (i + m) (add_comm m i)).inv.app (Z : C)) ≫
          (shiftFunctorComm C (i + m) n).hom.app (Z : C) =
      (shiftFunctor C n).map f ≫
        (shiftFunctor C n).map ((shiftFunctor C i).map g) ≫
        (shiftFunctorComm C i n).hom.app ((Z : C)⟦m⟧) ≫
          (shiftFunctor C i).map ((shiftFunctorComm C m n).hom.app (Z : C)) ≫
          (shiftFunctorAdd' C m i (i + m) (add_comm m i)).inv.app ((Z : C)⟦n⟧) := by
      simpa [Category.assoc] using
        congrArg
          (fun t ↦
            (shiftFunctor C n).map f ≫
              (shiftFunctor C n).map ((shiftFunctor C i).map g) ≫
              t)
          (shiftCompTail_normalize (C := C) (Z := (Z : C)) (n := n) (m := m) (i := i))
    _ =
      (shiftFunctor C n).map f ≫
        (shiftFunctorComm C i n).hom.app (Y : C) ≫
          (shiftFunctor C i).map ((shiftFunctor C n).map g) ≫
            (shiftFunctor C i).map ((shiftFunctorComm C m n).hom.app (Z : C)) ≫
              (shiftFunctorAdd' C m i (i + m) (add_comm m i)).inv.app ((Z : C)⟦n⟧) := by
      simpa [Category.assoc] using
        congrArg (fun t ↦ (shiftFunctor C n).map f ≫ t) hshift.symm

/-- Helper for Remark 22.25.7: shifting commutes with graded composition on homogeneous
generators. -/
@[simp] private theorem shiftMap_comp_of_of
    {X Y Z : C^gr} (n m i : ℤ)
    (g : ShiftedHom (Y : C) (Z : C) m)
    (f : ShiftedHom (X : C) (Y : C) i) :
    shiftMap C n
        (compSpace C
          (DirectSum.of (fun j ↦ shiftedHom C Y Z j) m g)
          (DirectSum.of (fun j ↦ shiftedHom C X Y j) i f)) =
      compSpace C
        (shiftMap C n (DirectSum.of (fun j ↦ shiftedHom C Y Z j) m g))
        (shiftMap C n (DirectSum.of (fun j ↦ shiftedHom C X Y j) i f)) := by
  -- Proof comment: evaluate both sides on the direct-sum generators once, reducing the claim to
  -- the homogeneous compatibility bridge for `ShiftedHom.comp`.
  simp only [compSpace_of_of, shiftMap_of]
  simpa using
    congrArg
      (DirectSum.of (fun j ↦ shiftedHom C (shiftObj C X n) (shiftObj C Z n) j) (i + m))
      (shiftCompHomDegree_eq (C := C) (X := X) (Y := Y) (Z := Z) (n := n) (m := m) (i := i)
        g f)

/-- The inherited shift functor `[n]` on `C^gr`, acting on objects by the ambient shift on `C`. -/
def shift (n : ℤ) : C^gr ⥤ C^gr where
  obj X := shiftObj C X n
  map f := shiftMap C n f
  map_id := by
    intro X
    -- Proof comment: the identity is the degree-`0` generator `idSpace`, so `shiftMap_of`
    -- reduces the goal to the homogeneous identity bridge `shiftIdHom`.
    change shiftMap C n (idSpace C X) = idSpace C (shiftObj C X n)
    rw [idSpace, shiftMap_of, idSpace]
    simpa using
      congrArg
        (DirectSum.of (fun j ↦ shiftedHom C (shiftObj C X n) (shiftObj C X n) j) 0)
        (shiftIdHom (C := C) (X := X) n)
  map_comp := by
    intro X Y Z f g
    -- Proof comment: reduce composition successively to homogeneous generators in the two direct
    -- sums, so the generator case is exactly `shiftMap_comp_of_of`.
    change shiftMap C n (compSpace C g f) = compSpace C (shiftMap C n g) (shiftMap C n f)
    refine DirectSum.induction_on g ?_ ?_ ?_
    · simp
    · intro m g
      refine DirectSum.induction_on f ?_ ?_ ?_
      · simp
      · intro i f
        simpa using
          shiftMap_comp_of_of (C := C) (X := X) (Y := Y) (Z := Z) (n := n) (m := m) (i := i)
            g f
      · intro f₁ f₂ hf₁ hf₂
        -- Proof comment: additivity in the source morphism slot propagates the homogeneous case.
        rw [compSpace_add_right, (shiftMap C n).map_add, (shiftMap C n).map_add,
          compSpace_add_right]
        simpa [hf₁, hf₂]
    · intro g₁ g₂ hg₁ hg₂
      -- Proof comment: additivity in the target morphism slot propagates the induction step.
      rw [compSpace_add_left, (shiftMap C n).map_add, (shiftMap C n).map_add,
        compSpace_add_left]
      simpa [hg₁, hg₂]

@[simp] theorem shift_obj (n : ℤ) (X : C^gr) :
    ((shift C n).obj X : C) = (X : C)⟦n⟧ :=
  rfl

end Basic

section Linear

open scoped ShiftedHomCategory

variable (R : Type w) [Ring R]
variable [Preadditive C] [Linear R C] [HasShift C ℤ]
variable [∀ n : ℤ, (shiftFunctor C n).Additive]
variable [∀ n : ℤ, Functor.Linear R (shiftFunctor C n)]

/- The degree-zero bridge for Remark 22.25.7 is the canonical `ShiftedHom.homEquiv`. -/
recall ShiftedHom.homEquiv

/-- The `R`-linear structure on `C^gr` is induced from the direct-sum `R`-module structure on the
shifted-Hom summands. -/
instance instLinear : Linear R (C^gr) where
  homModule X Y := by
    change Module R (homSpace C X Y)
    infer_instance
  smul_comp := by
    intro X Y Z r f g
    let f' : homSpace C X Y := f
    let g' : homSpace C Y Z := g
    change compSpace C g' (r • f') = r • compSpace C g' f'
    -- Proof comment: reduce both variables to homogeneous generators; the generator case is the
    -- `ShiftedHom.smul_comp` compatibility on one homogeneous composite.
    refine DirectSum.induction_on g' ?_ ?_ ?_
    · simp
    · intro m g
      refine DirectSum.induction_on f' ?_ ?_ ?_
      · simp
      · intro i f
        rw [← DirectSum.of_smul, compSpace_of_of, compSpace_of_of]
        rw [show compHomDegree C g (r • f) = r • compHomDegree C g f by
          simpa [compHomDegree] using
            (ShiftedHom.smul_comp (r := r) (α := f) (β := g) (h := add_comm m i))]
        exact DirectSum.of_smul (R := R) (M := fun j ↦ shiftedHom C X Z j) (i + m) r
          (compHomDegree C g f)
      · intro f₁ f₂ hf₁ hf₂
        -- Proof comment: additivity in the source slot turns the scalar-compatibility statement
        -- into the sum of the induction hypotheses.
        rw [smul_add, compSpace_add_right, compSpace_add_right, smul_add]
        simpa [hf₁, hf₂]
    · intro g₁ g₂ hg₁ hg₂
      -- Proof comment: additivity in the target slot propagates the induction step.
      rw [compSpace_add_left, compSpace_add_left, smul_add]
      simpa [hg₁, hg₂]
  comp_smul := by
    intro X Y Z f r g
    let f' : homSpace C X Y := f
    let g' : homSpace C Y Z := g
    change compSpace C (r • g') f' = r • compSpace C g' f'
    -- Proof comment: reduce both variables to homogeneous generators; the generator case is the
    -- `ShiftedHom.comp_smul` compatibility on one homogeneous composite.
    refine DirectSum.induction_on g' ?_ ?_ ?_
    · simp
    · intro m g
      refine DirectSum.induction_on f' ?_ ?_ ?_
      · simp
      · intro i f
        rw [← DirectSum.of_smul, compSpace_of_of, compSpace_of_of]
        rw [show compHomDegree C (r • g) f = r • compHomDegree C g f by
          simpa [compHomDegree] using
            (ShiftedHom.comp_smul (r := r) (α := f) (β := g) (h := add_comm m i))]
        exact DirectSum.of_smul (R := R) (M := fun j ↦ shiftedHom C X Z j) (i + m) r
          (compHomDegree C g f)
      · intro f₁ f₂ hf₁ hf₂
        -- Proof comment: additivity in the source slot propagates the induction step.
        rw [compSpace_add_right, compSpace_add_right, smul_add]
        simpa [hf₁, hf₂]
    · intro g₁ g₂ hg₁ hg₂
      -- Proof comment: additivity in the target slot turns the scalar-compatibility statement
      -- into the sum of the induction hypotheses.
      rw [smul_add, compSpace_add_left, compSpace_add_left, smul_add]
      simpa [hg₁, hg₂]

/-- The degree-`n` graded piece of `C^gr` is the `n`-th direct-summand submodule inside the total
Hom module. -/
private abbrev gradedHomDegree (X Y : C^gr) (n : ℤ) : Submodule R (X ⟶ Y) :=
  (DirectSum.lof R ℤ (fun i ↦ ShiftedHom (X : C) (Y : C) i) n).range

private def gradedHomDegreeOf (X Y : C^gr) (n : ℤ) :
    ShiftedHom (X : C) (Y : C) n →ₗ[R] gradedHomDegree C R X Y n where
  toFun f := ⟨DirectSum.lof R ℤ (fun i ↦ ShiftedHom (X : C) (Y : C) i) n f, ⟨f, rfl⟩⟩
  map_add' := by
    intro f g
    apply Subtype.ext
    exact (DirectSum.lof R ℤ (fun i ↦ ShiftedHom (X : C) (Y : C) i) n).map_add f g
  map_smul' := by
    intro r f
    apply Subtype.ext
    exact (DirectSum.lof R ℤ (fun i ↦ ShiftedHom (X : C) (Y : C) i) n).map_smul r f

/-- The `n`-th shifted-Hom group is canonically the degree-`n` graded summand of the total Hom
module in `C^gr`. -/
private def gradedHomDegreeEquiv (X Y : C^gr) (n : ℤ) :
    ShiftedHom (X : C) (Y : C) n ≃ₗ[R] gradedHomDegree C R X Y n where
  toFun := gradedHomDegreeOf C R X Y n
  invFun x := DirectSum.component R ℤ (fun i ↦ ShiftedHom (X : C) (Y : C) i) n x.1
  left_inv := by
    intro f
    simp [gradedHomDegreeOf]
  right_inv := by
    intro x
    rcases x.2 with ⟨f, hf⟩
    have hx : x = gradedHomDegreeOf C R X Y n f := by
      apply Subtype.ext
      exact hf.symm
    rw [hx]
    ext
    simp [gradedHomDegreeOf]
  map_add' := by
    intro x y
    exact (gradedHomDegreeOf C R X Y n).map_add x y
  map_smul' := by
    intro r x
    exact (gradedHomDegreeOf C R X Y n).map_smul r x

@[simp] private theorem gradedHomDegreeEquiv_apply
    (X Y : C^gr) (n : ℤ) (f : ShiftedHom (X : C) (Y : C) n) :
    ((gradedHomDegreeEquiv C R X Y n f : gradedHomDegree C R X Y n) : X ⟶ Y) =
      DirectSum.lof R ℤ (fun i ↦ ShiftedHom (X : C) (Y : C) i) n f :=
  rfl

private def homSpaceDecompose (X Y : C^gr) :
    homSpace C X Y →ₗ[R] ⨁ n : ℤ, gradedHomDegree C R X Y n :=
  DirectSum.toModule R ℤ (⨁ n : ℤ, gradedHomDegree C R X Y n)
    (fun n ↦
      (DirectSum.lof R ℤ (fun i ↦ gradedHomDegree C R X Y i) n).comp
        (gradedHomDegreeEquiv C R X Y n).toLinearMap)

private instance instHomSpaceDecomposition (X Y : C^gr) :
    DirectSum.Decomposition (gradedHomDegree C R X Y) :=
  DirectSum.Decomposition.ofLinearMap (gradedHomDegree C R X Y) (homSpaceDecompose C R X Y)
    (by
      apply DirectSum.linearMap_ext
      intro n
      apply LinearMap.ext
      intro f
      change
        DirectSum.coeLinearMap (gradedHomDegree C R X Y)
            (DirectSum.toModule R ℤ (⨁ k : ℤ, gradedHomDegree C R X Y k)
              (fun k ↦
                (DirectSum.lof R ℤ (fun i ↦ gradedHomDegree C R X Y i) k).comp
                  (gradedHomDegreeEquiv C R X Y k).toLinearMap)
              ((DirectSum.lof R ℤ (fun i ↦ ShiftedHom (X : C) (Y : C) i) n) f)) =
          (DirectSum.lof R ℤ (fun i ↦ ShiftedHom (X : C) (Y : C) i) n) f
      rw [DirectSum.toModule_lof]
      simpa [gradedHomDegreeEquiv_apply])
    (by
      apply DirectSum.linearMap_ext
      intro n
      apply LinearMap.ext
      intro x
      rcases x.2 with ⟨f, hf⟩
      have hx : x = gradedHomDegreeOf C R X Y n f := by
        apply Subtype.ext
        exact hf.symm
      rw [hx]
      change
        homSpaceDecompose C R X Y
            (DirectSum.coeLinearMap (gradedHomDegree C R X Y)
              ((DirectSum.lof R ℤ (fun i ↦ gradedHomDegree C R X Y i) n)
                (gradedHomDegreeOf C R X Y n f))) =
          (DirectSum.lof R ℤ (fun i ↦ gradedHomDegree C R X Y i) n)
            (gradedHomDegreeOf C R X Y n f)
      rw [DirectSum.coeLinearMap_lof]
      change
        DirectSum.toModule R ℤ (⨁ k : ℤ, gradedHomDegree C R X Y k)
            (fun k ↦
              (DirectSum.lof R ℤ (fun i ↦ gradedHomDegree C R X Y i) k).comp
                (gradedHomDegreeEquiv C R X Y k).toLinearMap)
            ((DirectSum.lof R ℤ (fun i ↦ ShiftedHom (X : C) (Y : C) i) n) f) =
          (DirectSum.lof R ℤ (fun i ↦ gradedHomDegree C R X Y i) n)
            (gradedHomDegreeOf C R X Y n f)
      rw [DirectSum.toModule_lof]
      rfl)

/-- Remark 22.25.7: under the ambient `R`-linearity and shift-linearity hypotheses, `C^gr`
inherits the canonical `GradedCategory` structure whose degree-`n` piece is the `n`-th
shifted-Hom summand. -/
@[stacks 09P3, reducible]
def gradedCategory : GradedCategory R (C^gr) where
  homDegree := gradedHomDegree C R
  homDecomposition := instHomSpaceDecomposition C R
  id_mem_homDegree_zero := by
    intro X
    exact ⟨idHom C X, rfl⟩
  comp_mem := by
    intro X Y Z i j f g hf hg
    rcases hf with ⟨f', rfl⟩
    rcases hg with ⟨g', rfl⟩
    exact ⟨compHomDegree C g' f', (compSpace_lof_lof C g' f').symm⟩

variable (X Y : C^gr)
variable (n : ℤ)

/-- The degree-`n` piece `Hom^n(X, Y)` of `C^gr` is canonically the shifted-Hom group
`X ⟶ Y⟦n⟧`. -/
@[stacks 09P3]
def homDegreeEquivShiftedHom :
    ((gradedCategory C R).homDegree X Y n : Submodule R (X ⟶ Y)) ≃ₗ[R]
      ShiftedHom (X : C) (Y : C) n :=
  (gradedHomDegreeEquiv C R X Y n).symm

@[simp] theorem homDegreeEquivShiftedHom_apply_lof
    (f : ShiftedHom (X : C) (Y : C) n) :
    homDegreeEquivShiftedHom C R X Y n
        ⟨DirectSum.lof R ℤ (fun i ↦ ShiftedHom (X : C) (Y : C) i) n f, ⟨f, rfl⟩⟩ = f := by
  simp [homDegreeEquivShiftedHom, gradedHomDegreeEquiv, gradedHomDegreeOf]

@[simp] theorem homDegreeEquivShiftedHom_symm_apply
    (f : ShiftedHom (X : C) (Y : C) n) :
    (((homDegreeEquivShiftedHom C R X Y n).symm f : (gradedCategory C R).homDegree X Y n) :
        X ⟶ Y) =
      DirectSum.lof R ℤ (fun i ↦ ShiftedHom (X : C) (Y : C) i) n f := by
  rfl

/-- The degree-`0` piece `Hom^0(X, Y)` of `C^gr` recovers the ordinary morphisms of `C`. -/
abbrev degreeZeroHomEquiv (X Y : C^gr) :
    ((gradedCategory C R).homDegree X Y 0 : Submodule R (X ⟶ Y)) ≃ₗ[R] ((X : C) ⟶ Y) :=
  (homDegreeEquivShiftedHom C R X Y 0).trans
    (Linear.homCongr R (Iso.refl (X : C)) ((shiftFunctorZero' C (0 : ℤ) rfl).app (Y : C)))

/-- Remark 22.25.7: shifting the target object of `C^gr` by `n` translates the grading by `n`. -/
@[stacks 09P3]
abbrev homDegreeShiftObjEquiv
    (X Y : C^gr) (i n : ℤ) :
    (((gradedCategory C R).homDegree X (shiftObj C Y n) i) :
      Submodule R (X ⟶ shiftObj C Y n)) ≃ₗ[R]
      (((gradedCategory C R).homDegree X Y (n + i)) : Submodule R (X ⟶ Y)) :=
  ((homDegreeEquivShiftedHom C R X (shiftObj C Y n) i).trans
    (Linear.homCongr R (Iso.refl (X : C)) (shiftAdd (Y : C) n i).symm)).trans
    (homDegreeEquivShiftedHom C R X Y (n + i)).symm

end Linear

end ShiftedHomCategory

end

end CategoryTheory
