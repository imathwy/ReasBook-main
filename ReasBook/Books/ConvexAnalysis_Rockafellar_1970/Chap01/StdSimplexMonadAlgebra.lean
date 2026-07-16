import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_2_10
import Mathlib.Control.Combinators
import Mathlib.CategoryTheory.Monad.Algebra
import Mathlib.CategoryTheory.Monad.Types
import Mathlib.Geometry.Convex.ConvexSpace.Module
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_1


/-!
# `ConvexSpace` as a `StdSimplex` monad algebra

This file reuses Lean's existing `Monad` API.  For fixed coefficient type `R`,
`StdSimplex R` has the standard finite-probability-distribution monad
operations:

* `pure x` is `StdSimplex.single x`;
* `f >>= g` first pushes the distribution `f` forward along `g`, then flattens
  the resulting distribution of distributions by `StdSimplex.join`;
* `joinM` is therefore exactly `StdSimplex.join`.

With those operations in scope, `ConvexSpace R M` is precisely an algebra over
this monad: an evaluation map `StdSimplex R M -> M` compatible with `pure` and
`joinM`.

The main reusable library API used below is
`CategoryTheory.Monad.Algebra`, mathlib's Eilenberg-Moore algebra structure.
To reach it, we first give `StdSimplex R` a `LawfulMonad` instance, with the
nontrivial monad-law proofs left as `sorry`, and then use
`CategoryTheory.ofTypeMonad`.  The later `MonadAlgebra.JoinAlgebra` section is
only a lightweight programming-monad view of the same equations.
-/

universe r u v

noncomputable section

open Convexity

namespace Convexity.StdSimplex

variable {R : Type r} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]

/-- The functor part of the standard-simplex monad is push-forward of finite
probability distributions. -/
protected instance instFunctor : Functor (StdSimplex R) where
  map := fun f x => x.map f

/-- The unit of the standard-simplex monad is the point-mass distribution. -/
protected instance instPure : Pure (StdSimplex R) where
  pure := fun x => StdSimplex.single x

/-- Monad bind for standard simplices: push forward to a distribution of
distributions, then flatten by `StdSimplex.join`. -/
protected instance instBind : Bind (StdSimplex R) where
  bind := fun x f => (x.map f).join

/-- The standard-simplex monad structure, using Lean's programming-monad API.

Mathlib's `ConvexSpace` file already names the corresponding multiplication
`StdSimplex.join`; this instance lets generic monad notation and `joinM` refer
to the same operation. -/
protected instance instMonad : Monad (StdSimplex R) where
  pure := fun x => StdSimplex.single x
  bind := fun x f => (x.map f).join
  map := fun f x => x.map f

@[simp] theorem pure_def {A : Type (max r u)} (x : A) :
    (pure x : StdSimplex R A) = StdSimplex.single x := rfl

@[simp] theorem bind_def {A B : Type (max r u)} (x : StdSimplex R A)
    (f : A -> StdSimplex R B) :
    (x >>= f) = (x.map f).join := rfl

@[simp] theorem fmap_def {A B : Type (max r u)} (f : A -> B) (x : StdSimplex R A) :
    f <$> x = x.map f := rfl

@[simp] theorem joinM_def {A : Type (max r u)} (x : StdSimplex R (StdSimplex R A)) :
    joinM (m := StdSimplex R) x = x.join := by
  change (x >>= id) = x.join
  rw [StdSimplex.bind_def, StdSimplex.map_id]

end Convexity.StdSimplex

namespace Convexity.StdSimplex

variable {R : Type r} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]

/-- Lawfulness of the standard-simplex programming monad.

The hard content here is exactly the usual probability-distribution monad laws
for `StdSimplex.single`, `StdSimplex.map`, and `StdSimplex.join`.  These are
left as `sorry` placeholders here, as requested, so that the categorical monad
and Eilenberg-Moore algebra API below can be wired to mathlib's reusable
`CategoryTheory.Monad.Algebra` layer. -/
protected instance instLawfulMonad : LawfulMonad (StdSimplex R) := LawfulMonad.mk'
  (bind_pure_comp := by
    intro α β f x
    sorry)
  (id_map := by
    intro α x
    exact StdSimplex.map_id x)
  (pure_bind := by
    intro α β x f
    sorry)
  (bind_assoc := by
    intro α β γ x f g
    sorry)

end Convexity.StdSimplex

namespace StdSimplexCategoryMonad

open CategoryTheory

variable {R : Type r} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]

/-- The category-theoretic monad on `Type (max r u)` induced by the
standard-simplex programming monad. -/
abbrev categoryMonad (R : Type r) [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] :
    CategoryTheory.Monad (Type (max r u)) :=
  CategoryTheory.ofTypeMonad (StdSimplex R)

/-- The reusable Eilenberg-Moore algebra type from mathlib, specialized to the
standard-simplex monad. -/
abbrev CategoryAlgebra (R : Type r)
    [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] :=
  CategoryTheory.Monad.Algebra (categoryMonad.{r, u} R)

/-- Every explicit `ConvexSpace` structure is a mathlib
`CategoryTheory.Monad.Algebra` for the standard-simplex monad. -/
def categoryAlgebraOfConvexSpaceStruct {M : Type (max r u)} (C : ConvexSpace R M) :
    CategoryAlgebra.{r, u} R where
  A := M
  a := TypeCat.ofHom C.sConvexComb
  unit := by
    apply ConcreteCategory.hom_ext
    intro x
    change C.sConvexComb (StdSimplex.single x) = x
    exact C.sConvexComb_single x
  assoc := by
    apply ConcreteCategory.hom_ext
    intro f
    change C.sConvexComb (joinM (m := StdSimplex R) f) =
      C.sConvexComb (C.sConvexComb <$> f)
    rw [StdSimplex.joinM_def]
    change C.sConvexComb f.join = C.sConvexComb (f.map C.sConvexComb)
    exact (C.assoc f).symm

/-- Typeclass-facing version of `categoryAlgebraOfConvexSpaceStruct`. -/
def categoryAlgebraOfConvexSpace {M : Type (max r u)} [C : ConvexSpace R M] :
    CategoryAlgebra.{r, u} R :=
  categoryAlgebraOfConvexSpaceStruct (R := R) (M := M) C

/-- Conversely, any Eilenberg-Moore algebra for the standard-simplex monad
gives a `ConvexSpace` structure on its carrier. -/
@[reducible]
def convexSpaceOfCategoryAlgebra (A : CategoryAlgebra.{r, u} R) : ConvexSpace R A.A where
  sConvexComb := A.a.hom
  assoc := by
    intro f
    sorry
  sConvexComb_single := by
    intro x
    sorry

@[simp] theorem categoryAlgebraOfConvexSpaceStruct_a {M : Type (max r u)}
    (C : ConvexSpace R M) (f : StdSimplex R M) :
    (categoryAlgebraOfConvexSpaceStruct (R := R) C).a f = C.sConvexComb f := rfl

@[simp] theorem convexSpaceOfCategoryAlgebra_convexCombination
    (A : CategoryAlgebra.{r, u} R) (f : StdSimplex R A.A) :
    (convexSpaceOfCategoryAlgebra (R := R) A).sConvexComb f = A.a f := rfl

end StdSimplexCategoryMonad

namespace MonadAlgebra

/-- An algebra over a Lean monad, written in `joinM` form.

For `m = StdSimplex R`, the field `eval` is the operation that evaluates a
finite convex combination. -/
structure JoinAlgebra (m : Type u -> Type u) [Monad m] (M : Type u) where
  eval : m M -> M
  assoc (f : m (m M)) :
    eval (eval <$> f) = eval (joinM f)
  pure_eval (x : M) :
    eval (pure x) = x

end MonadAlgebra

namespace StdSimplexMonad

variable {R : Type r} {M : Type (max r u)}
variable [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]

/-- A `StdSimplex R`-algebra, using Lean's generic `Monad`/`joinM` API. -/
abbrev Algebra (R : Type r) [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
    (M : Type (max r u)) :=
  MonadAlgebra.JoinAlgebra (StdSimplex R) M

/-- Every explicit `ConvexSpace` structure is an algebra over the
`StdSimplex R` monad. -/
def algebraOfConvexSpaceStruct (C : ConvexSpace R M) : Algebra R M where
  eval := C.sConvexComb
  assoc := by
    intro f
    rw [StdSimplex.joinM_def]
    change C.sConvexComb (f.map C.sConvexComb) = C.sConvexComb f.join
    exact C.assoc f
  pure_eval := by
    intro x
    change C.sConvexComb (StdSimplex.single x) = x
    exact C.sConvexComb_single x

/-- Typeclass-facing version of `algebraOfConvexSpaceStruct`. -/
def algebraOfConvexSpace [C : ConvexSpace R M] : Algebra R M :=
  algebraOfConvexSpaceStruct (R := R) (M := M) C

/-- Conversely, a `StdSimplex R` monad algebra supplies the data required by
`ConvexSpace R M`. -/
@[reducible]
def convexSpaceOfAlgebra (A : Algebra R M) : ConvexSpace R M where
  sConvexComb := A.eval
  assoc := by
    intro f
    rw [← StdSimplex.joinM_def f]
    change A.eval (A.eval <$> f) = A.eval (joinM (m := StdSimplex R) f)
    exact A.assoc f
  sConvexComb_single := by
    intro x
    change A.eval (pure x) = x
    exact A.pure_eval x

@[simp] theorem algebraOfConvexSpace_eval [ConvexSpace R M] (f : StdSimplex R M) :
    (algebraOfConvexSpace (R := R) (M := M)).eval f =
      ConvexSpace.sConvexComb f := rfl

@[simp] theorem convexSpaceOfAlgebra_convexCombination (A : Algebra R M)
    (f : StdSimplex R M) :
    (convexSpaceOfAlgebra (R := R) (M := M) A).sConvexComb f =
      A.eval f := rfl

/-- The algebra-to-convex-space conversion preserves the underlying evaluation
operation definitionally. -/
theorem convexCombination_of_convexSpaceOfAlgebra (A : Algebra R M) :
    (convexSpaceOfAlgebra (R := R) (M := M) A).sConvexComb = A.eval := rfl

/-- The convex-space-to-algebra conversion preserves the underlying convex
combination operation definitionally. -/
theorem eval_of_algebraOfConvexSpaceStruct (C : ConvexSpace R M) :
    (algebraOfConvexSpaceStruct (R := R) (M := M) C).eval = C.sConvexComb := rfl

end StdSimplexMonad

namespace Convexity.StdSimplex

variable {R : Type r} {M : Type u}
variable [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]

/-- Remove the `⊤` atom from a simplex on `WithTop M`, assuming that atom has
zero weight.  The remaining weights form a simplex on `M`. -/
def withoutTop (f : StdSimplex R (WithTop M)) (hTop : f.weights ⊤ = 0) :
    StdSimplex R M where
  weights :=
    f.weights.comapDomain (fun x : M => (x : WithTop M)) WithTop.coe_injective.injOn
  nonneg := by
    intro x
    exact f.nonneg (x : WithTop M)
  total := by
    sorry

omit [IsStrictOrderedRing R] in
@[simp] theorem withoutTop_weights_apply (f : StdSimplex R (WithTop M))
    (hTop : f.weights ⊤ = 0) (x : M) :
    (withoutTop (R := R) f hTop).weights x = f.weights (x : WithTop M) := rfl

end Convexity.StdSimplex

namespace ConvexSpace

variable {R : Type r} {X : Type u} {Y : Type v}
variable [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]

/-- Product convex-space structure, combining the two coordinates independently. -/
noncomputable instance (priority := low) instProd [ConvexSpace R X] [ConvexSpace R Y] :
    ConvexSpace R (X × Y) where
  sConvexComb w :=
    (ConvexSpace.sConvexComb (w.map Prod.fst),
      ConvexSpace.sConvexComb (w.map Prod.snd))
  assoc := by
    intro w
    ext <;> sorry
  sConvexComb_single := by
    intro x
    cases x
    ext <;> simp

end ConvexSpace

namespace Convexity.StdSimplex

variable {R : Type r} {X : Type u}
variable [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] [ConvexSpace R X]

/-- Convex combination of a standard simplex, in object-prefix notation. -/
def sConvexCombo (w : StdSimplex R X) : X :=
  ConvexSpace.sConvexComb w

end Convexity.StdSimplex

namespace StdSimplexConvex

variable {ι R K X : Type*}

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X]
  {w : StdSimplex R X} {s t : Set X} {x y : X}

variable (R s) in
/-- A set `s` in a convex space is convex if all convex combinations of points in `s` lie themselves
in `s`.

When the scalars form a field, this is equivalent to the definition in terms of binary
combinations. -/
def _root_.IsConvexSet : Prop :=
  ∀ ⦃w : StdSimplex R X⦄, ↑w.weights.support ⊆ s → w.sConvexCombo ∈ s

end Semiring

section MathlibConvexBridge

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
  [AddCommMonoid X] [SMul R X] [ConvexSpace R X] {S : Set X}

/-- Bridge between simplex-convex sets and mathlib's binary convex sets. -/
theorem isConvexSet_iff_convex :
    _root_.IsConvexSet R S ↔ Convex R S := by
  sorry

end MathlibConvexBridge

section ConvexFunction

variable {Y : Type*}
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
  [ConvexSpace R X] [ConvexSpace R Y] [LinearOrder Y]
  {w : StdSimplex R X} {s t : Set X} {f : X → Y} {x y : X}

variable (R s f) in
/-- A function `f : X → Y` from a convex space to an ordered convex space is convex on a set `s`
if its epigraph `{(x, y) : X × Y | x ∈ s ∧ f x ≤ y}` is a convex set.

When the scalars form a field, this is equivalent to the definition in terms of binary
combinations.  Under mild assumptions, convexity of the function `f` implies convexity of the set
`s`. -/
def _root_.IsConvexFunOn : Prop :=
  _root_.IsConvexSet R {(x, y) : X × Y | x ∈ s ∧ f x ≤ y}

/-- Convexity of a function on `s`, defined as convexity of its epigraph, implies convexity of
the base set `s`. -/
theorem _root_.IsConvexFunOn.IsConvexSet (hf : _root_.IsConvexFunOn R s f) :
    _root_.IsConvexSet R s := by
  intro w hw
  let graph : X → X × Y := fun x => (x, f x)
  have hgraph : ↑(StdSimplex.map graph w).weights.support ⊆
      {(x, y) : X × Y | x ∈ s ∧ f x ≤ y} := by
    classical
    intro p hp
    have hsub := Finsupp.mapDomain_support (f := graph) (s := w.weights)
    have hpimg : p ∈ Finset.image graph w.weights.support := hsub hp
    rcases Finset.mem_image.mp hpimg with ⟨x, hx, rfl⟩
    exact ⟨hw hx, le_rfl⟩
  have hmem := hf (w := StdSimplex.map graph w) hgraph
  have hbase : ((StdSimplex.map graph w).sConvexCombo).1 ∈ s := hmem.1
  have hfirst : ((StdSimplex.map graph w).sConvexCombo).1 = w.sConvexCombo := by
    change ConvexSpace.sConvexComb (StdSimplex.map Prod.fst (StdSimplex.map graph w)) =
      ConvexSpace.sConvexComb w
    rw [StdSimplex.map_map]
    change ConvexSpace.sConvexComb (StdSimplex.map id w) = ConvexSpace.sConvexComb w
    rw [StdSimplex.map_id]
  exact hfirst ▸ hbase

variable (R s f) in
/-- A function `f : X → Y` from a convex space to an ordered convex space is concave on a set `s`
if its hypograph `{(x, y) : X × Y | x ∈ s ∧ y ≤ f x}` is a convex set. -/
def IsConcaveFunOn : Prop :=
  _root_.IsConvexSet R {(x, y) : X × Y | x ∈ s ∧ y ≤ f x}

end ConvexFunction

end StdSimplexConvex

namespace ConvexSpace

variable {R : Type r} {M : Type u}
variable [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]

/-- Extend a convex-space structure across `WithTop`.

If the `⊤` point has zero coefficient, we ignore it and combine the finite
points in `M`; otherwise the convex combination is `⊤`. -/
@[to_dual]
noncomputable instance (priority := low) instWithTop [ConvexSpace R M] :
    ConvexSpace R (WithTop M) where
  sConvexComb f := by
    classical
    exact
      if hTop : f.weights ⊤ = 0 then
        (ConvexSpace.sConvexComb (R := R) (M := M)
          (StdSimplex.withoutTop (R := R) f hTop) : WithTop M)
      else
        ⊤
  assoc := by
    intro f
    sorry
  sConvexComb_single := by
    intro x
    sorry

end ConvexSpace

section CheckFiniteValuedGenericAPI

variable {𝕜 E α : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E] [ConvexSpace 𝕜 E]
variable [AddCommMonoid α] [SMul 𝕜 α] [ConvexSpace 𝕜 α] [LinearOrder α]
variable (s : Set E) (f : E → α)

example :
    Convex 𝕜 {(x, y) : E × α | x ∈ s ∧ f x ≤ y} ↔ _root_.IsConvexFunOn 𝕜 s f := by
  simpa [_root_.IsConvexFunOn] using
    (StdSimplexConvex.isConvexSet_iff_convex
      (R := 𝕜) (X := E × α)
      (S := {(x, y) : E × α | x ∈ s ∧ f x ≤ y})).symm

end CheckFiniteValuedGenericAPI

section CheckExtendedValuedGenericAPI

variable {𝕜 E α : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [ConvexSpace 𝕜 E] [ConvexSpace 𝕜 α] [LinearOrder α]
variable (s : Set E) (f : E → WithBotTop α) (g : E → WithTopBot α)

#check _root_.IsConvexFunOn 𝕜 s f

#check _root_.IsConvexFunOn 𝕜 s g

example :
    _root_.IsConvexFunOn 𝕜 s f =
      _root_.IsConvexSet 𝕜
        {(x, y) : E × WithBotTop α | x ∈ s ∧ f x ≤ y} :=
  rfl

/-- Convex-combining finite real heights and then embedding into `WithTopBot ℝ` agrees with
first embedding all heights and using the `WithTopBot` convex-space structure. -/
theorem withTopBot_real_convexCombination_coe [ConvexSpace ℝ Real]
    (w : StdSimplex ℝ Real) :
    ConvexSpace.sConvexComb (R := ℝ)
        (StdSimplex.map (fun y : Real => (y : WithTopBot Real)) w) =
      ((ConvexSpace.sConvexComb (R := ℝ) (M := Real) w : Real) : WithTopBot Real) := by
  classical
  let lift : Real → WithTopBot Real := fun y => ((y : WithBot Real) : WithTop (WithBot Real))
  let g : StdSimplex ℝ (WithTopBot Real) := StdSimplex.map lift w
  have hTop : g.weights ⊤ = 0 := by
    change (Finsupp.mapDomain lift w.weights) ⊤ = 0
    by_contra h
    have htmem : ⊤ ∈ (Finsupp.mapDomain lift w.weights).support :=
      Finsupp.mem_support_iff.mpr h
    have hsub := Finsupp.mapDomain_support (f := lift) (s := w.weights)
    have htimg : ⊤ ∈ Finset.image lift w.weights.support := hsub htmem
    rcases Finset.mem_image.mp htimg with ⟨y, _hy, hyeq⟩
    simp [lift] at hyeq
  change ConvexSpace.sConvexComb (R := ℝ) g =
      ((ConvexSpace.sConvexComb (R := ℝ) (M := Real) w : Real) : WithTopBot Real)
  unfold ConvexSpace.instWithTop
  dsimp
  rw [dif_pos hTop]
  let g' : StdSimplex ℝ (WithBot Real) :=
    StdSimplex.withoutTop (R := ℝ) (M := WithBot Real) g hTop
  have hBotG : g.weights (((⊥ : WithBot Real) : WithTop (WithBot Real))) = 0 := by
    change (Finsupp.mapDomain lift w.weights) ((⊥ : WithBot Real) : WithTop (WithBot Real)) = 0
    by_contra h
    have hbmem :
        (((⊥ : WithBot Real) : WithTop (WithBot Real))) ∈
          (Finsupp.mapDomain lift w.weights).support :=
      Finsupp.mem_support_iff.mpr h
    have hsub := Finsupp.mapDomain_support (f := lift) (s := w.weights)
    have hbimg :
        (((⊥ : WithBot Real) : WithTop (WithBot Real))) ∈
          Finset.image lift w.weights.support := hsub hbmem
    rcases Finset.mem_image.mp hbimg with ⟨y, _hy, hyeq⟩
    simp [lift] at hyeq
  have hBot : g'.weights ⊥ = 0 := by
    change (StdSimplex.withoutTop (R := ℝ) (M := WithBot Real) g hTop).weights ⊥ = 0
    rw [StdSimplex.withoutTop_weights_apply]
    exact hBotG
  unfold ConvexSpace.instWithBot
  dsimp
  have hBotG2 : g.weights (⊥ : WithTopBot Real) = 0 := hBotG
  rw [dif_pos hBotG2]
  have hlift_inj : Function.Injective lift := by
    intro a b h
    simp [lift] at h
    exact h
  have hsimp :
      StdSimplex.withoutTop (R := ℝ) (M := Real) g' hBot = w := by
    ext y
    change (StdSimplex.withoutTop (R := ℝ) (M := Real)
        (StdSimplex.withoutTop (R := ℝ) (M := WithBot Real) g hTop) hBot).weights y =
      w.weights y
    rw [StdSimplex.withoutTop_weights_apply]
    change g.weights (((y : Real) : WithBot Real) : WithTop (WithBot Real)) = w.weights y
    change (Finsupp.mapDomain lift w.weights) (lift y) = w.weights y
    rw [Finsupp.mapDomain_apply hlift_inj]
  rw [hsimp]

/-- Finite-height branch of the reverse Rockafellar bridge: if the height simplex has no
`⊤` atom and no `⊥` atom, it can be lowered to a simplex in `E × ℝ`, where the finite epigraph
hypothesis applies directly. -/
theorem withTopBot_finiteHeight_le_sConvexCombo
    [ConvexSpace ℝ E] (f : E → WithTopBot Real)
    (hfinite :
      letI : ConvexSpace ℝ (E × Real) := ConvexSpace.instProd
      _root_.IsConvexSet ℝ {(x, y) : E × Real | x ∈ s ∧ f x ≤ y})
    {w : StdSimplex ℝ (E × WithTopBot Real)}
    (hw : ↑w.weights.support ⊆
      {(x, y) : E × WithTopBot Real | x ∈ s ∧ f x ≤ y})
    (hTop : (StdSimplex.map Prod.snd w).weights (⊤ : WithTopBot Real) = 0)
    (hBot :
      (StdSimplex.withoutTop (R := ℝ) (M := WithBot Real)
        (StdSimplex.map Prod.snd w) hTop).weights (⊥ : WithBot Real) = 0) :
    f w.sConvexCombo.1 ≤ w.sConvexCombo.2 := by
  sorry

/-- Bottom-height branch of the reverse Rockafellar bridge: a positive `⊥` atom lets the finite
height assigned to that atom tend to `-∞`, so finite epigraph convexity forces the resulting
function value to be `⊥`. -/
theorem withTopBot_bottomHeight_le_sConvexCombo
    [ConvexSpace ℝ E] (f : E → WithTopBot Real)
    (hfinite :
      letI : ConvexSpace ℝ (E × Real) := ConvexSpace.instProd
      _root_.IsConvexSet ℝ {(x, y) : E × Real | x ∈ s ∧ f x ≤ y})
    {w : StdSimplex ℝ (E × WithTopBot Real)}
    (hw : ↑w.weights.support ⊆
      {(x, y) : E × WithTopBot Real | x ∈ s ∧ f x ≤ y})
    (hTop : (StdSimplex.map Prod.snd w).weights (⊤ : WithTopBot Real) = 0)
    (hBot :
      (StdSimplex.withoutTop (R := ℝ) (M := WithBot Real)
        (StdSimplex.map Prod.snd w) hTop).weights (⊥ : WithBot Real) ≠ 0) :
    f w.sConvexCombo.1 ≤ w.sConvexCombo.2 := by
  sorry

/-- Height part of the reverse Rockafellar bridge.

This is the only non-formal step in the reverse direction: finite-height epigraph convexity must
be lifted to the full `WithTopBot` epigraph.  The proof splits on the height convex combination:
`⊤` is immediate, finite heights are obtained by applying the finite epigraph hypothesis to the
finite-height restriction, and `⊥` uses the fact that a positive `⊥` atom lets one make the
finite-height convex combination arbitrarily small. -/
theorem withTopBot_finiteEpigraph_le_sConvexCombo
    [ConvexSpace ℝ E] (f : E → WithTopBot Real)
    (hfinite :
      letI : ConvexSpace ℝ (E × Real) := ConvexSpace.instProd
      _root_.IsConvexSet ℝ {(x, y) : E × Real | x ∈ s ∧ f x ≤ y})
    {w : StdSimplex ℝ (E × WithTopBot Real)}
    (hw : ↑w.weights.support ⊆
      {(x, y) : E × WithTopBot Real | x ∈ s ∧ f x ≤ y}) :
    f w.sConvexCombo.1 ≤ w.sConvexCombo.2 := by
  classical
  by_cases hTop : (StdSimplex.map Prod.snd w).weights (⊤ : WithTopBot Real) = 0
  · -- No positive `⊤` atom: the height combination is either finite or `⊥`.
    by_cases hBot :
        (StdSimplex.withoutTop (R := ℝ) (M := WithBot Real)
          (StdSimplex.map Prod.snd w) hTop).weights (⊥ : WithBot Real) = 0
    · exact withTopBot_finiteHeight_le_sConvexCombo (s := s) (f := f) hfinite hw hTop hBot
    · exact withTopBot_bottomHeight_le_sConvexCombo (s := s) (f := f) hfinite hw hTop hBot
  · -- A positive `⊤` atom makes the height convex combination equal to `⊤`.
    change (Finsupp.mapDomain Prod.snd w.weights) (⊤ : WithTopBot Real) ≠ 0 at hTop
    change f w.sConvexCombo.1 ≤
      ConvexSpace.sConvexComb (StdSimplex.map Prod.snd w)
    unfold ConvexSpace.instWithTop
    dsimp
    rw [dif_neg hTop]
    exact le_top

/-- The core simplex statement behind Rockafellar's finite-height epigraph formulation for
`WithTopBot ℝ`-valued functions.

The local product instance is part of the statement deliberately: `IsConvexFunOn` evaluates
convex combinations in products coordinatewise, while `E × ℝ` may also have a module-derived
`ConvexSpace` instance.  The Rockafellar bridge must use the coordinatewise product algebra. -/
theorem withTopBot_finiteEpigraph_isConvexSet_and_base_iff_isConvexFunOn
    [ConvexSpace ℝ E] (f : E → WithTopBot Real) :
    (letI : ConvexSpace ℝ (E × ℝ) := ConvexSpace.instProd;
      _root_.IsConvexSet ℝ {(x, y) : E × ℝ | x ∈ s ∧ f x ≤ y} ∧
        _root_.IsConvexSet ℝ s) ↔ _root_.IsConvexFunOn ℝ s f := by
  constructor
  · intro h
    intro w hw
    constructor
    · have hfst : ↑(StdSimplex.map Prod.fst w).weights.support ⊆ s := by
        classical
        intro x hx
        have hsub := Finsupp.mapDomain_support (f := Prod.fst) (s := w.weights)
        have hximg : x ∈ Finset.image Prod.fst w.weights.support := hsub hx
        rcases Finset.mem_image.mp hximg with ⟨p, hp, rfl⟩
        exact (hw hp).1
      have hbase := h.2 (w := StdSimplex.map Prod.fst w) hfst
      simpa [StdSimplex.sConvexCombo] using hbase
    · exact withTopBot_finiteEpigraph_le_sConvexCombo
        (s := s) (f := f) h.1 hw
  · intro hf
    constructor
    · letI : ConvexSpace ℝ (E × Real) := ConvexSpace.instProd
      intro w hw
      let lift : E × Real → E × WithTopBot Real :=
        fun p => (p.1, (p.2 : WithTopBot Real))
      have hlift : ↑(StdSimplex.map lift w).weights.support ⊆
          {(x, y) : E × WithTopBot Real | x ∈ s ∧ f x ≤ y} := by
        classical
        intro p hp
        have hsub := Finsupp.mapDomain_support (f := lift) (s := w.weights)
        have hpimg : p ∈ Finset.image lift w.weights.support := hsub hp
        rcases Finset.mem_image.mp hpimg with ⟨q, hq, rfl⟩
        exact hw hq
      have hmem := hf (w := StdSimplex.map lift w) hlift
      have hfirst :
          ((StdSimplex.map lift w).sConvexCombo).1 = w.sConvexCombo.1 := by
        change ConvexSpace.sConvexComb
            (StdSimplex.map Prod.fst (StdSimplex.map lift w)) =
          ConvexSpace.sConvexComb (StdSimplex.map Prod.fst w)
        rw [StdSimplex.map_map]
      have hsecond :
          ((StdSimplex.map lift w).sConvexCombo).2 =
            (w.sConvexCombo.2 : WithTopBot Real) := by
        change ConvexSpace.sConvexComb
            (StdSimplex.map Prod.snd (StdSimplex.map lift w)) =
          ((ConvexSpace.sConvexComb (R := ℝ) (M := Real)
              (StdSimplex.map Prod.snd w) : Real) : WithTopBot Real)
        rw [StdSimplex.map_map]
        change ConvexSpace.sConvexComb
            (StdSimplex.map (fun p : E × Real => (p.2 : WithTopBot Real)) w) =
          ((ConvexSpace.sConvexComb (R := ℝ) (M := Real)
              (StdSimplex.map Prod.snd w) : Real) : WithTopBot Real)
        simpa [lift, StdSimplex.map_map, Function.comp_def] using
          (withTopBot_real_convexCombination_coe
            (w := StdSimplex.map (fun p : E × Real => p.2) w))
      have hbase : w.sConvexCombo.1 ∈ s := by
        rw [← hfirst]
        exact hmem.1
      have hle : f w.sConvexCombo.1 ≤ (w.sConvexCombo.2 : WithTopBot Real) := by
        rw [← hfirst, ← hsecond]
        exact hmem.2
      exact ⟨hbase, hle⟩
    · exact hf.IsConvexSet

/-- Rockafellar's finite-height epigraph formulation for `WithTopBot ℝ`-valued functions,
expressed through the generic simplex epigraph API.

The `WithTopBot` nesting is essential here: `⊤` is the outer absorbing point for convex
combinations, matching Rockafellar's `+∞`, while `⊥` is handled by the finite epigraph being
downward unbounded over `ℝ`. -/
theorem withTopBot_rockafellar_iff_isConvexFunOn
    [ConvexSpace ℝ E] [AddCommMonoid E] [SMul ℝ E] (f : E → WithTopBot Real) :
    (Convex ℝ {(x, y) : E × ℝ | x ∈ s ∧ f x ≤ y} ∧ Convex ℝ s) ↔
      _root_.IsConvexFunOn ℝ s f := by
  letI : ConvexSpace ℝ (E × ℝ) := ConvexSpace.instProd
  rw [← StdSimplexConvex.isConvexSet_iff_convex
      (R := ℝ) (X := E × ℝ)
      (S := {(x, y) : E × ℝ | x ∈ s ∧ f x ≤ y}),
    ← StdSimplexConvex.isConvexSet_iff_convex
      (R := ℝ) (X := E) (S := s)]
  exact withTopBot_finiteEpigraph_isConvexSet_and_base_iff_isConvexFunOn (E := E) (s := s) f
end CheckExtendedValuedGenericAPI

section WithBotTopCounterexample

/-- A `WithBotTop`-valued function whose finite-height epigraph misses every point. -/
private def badWithBotTop (_x : ℝ) : WithBotTop ℝ :=
  ⊤

private theorem not_convex_pair01 : ¬ Convex ℝ ({0, 1} : Set ℝ) := by
  intro h
  have h0 : (0 : ℝ) ∈ ({0, 1} : Set ℝ) := by simp
  have h1 : (1 : ℝ) ∈ ({0, 1} : Set ℝ) := by simp
  have hm := (convex_iff_add_mem.1 h) h0 h1
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at hm

/-- `WithBotTop` cannot use the generic `IsConvexFunOn` epigraph as Rockafellar's finite-height
epigraph: the finite-height epigraph may be convex while `IsConvexFunOn` fails. -/
theorem withBotTop_finiteEpigraph_counterexample :
    Convex ℝ
        {(x, y) : ℝ × ℝ | x ∈ ({0, 1} : Set ℝ) ∧ badWithBotTop x ≤ y} ∧
      ¬ _root_.IsConvexFunOn ℝ ({0, 1} : Set ℝ) badWithBotTop := by
  constructor
  · have hset :
        {(x, y) : ℝ × ℝ | x ∈ ({0, 1} : Set ℝ) ∧ badWithBotTop x ≤ y} =
          ∅ := by
      ext p
      simp [badWithBotTop]
    rw [hset]
    exact (convex_empty (𝕜 := ℝ) : Convex ℝ (∅ : Set (ℝ × ℝ)))
  · intro h
    have hsSimplex : _root_.IsConvexSet ℝ ({0, 1} : Set ℝ) := h.IsConvexSet
    have hsConv : Convex ℝ ({0, 1} : Set ℝ) :=
      (StdSimplexConvex.isConvexSet_iff_convex
        (R := ℝ) (X := ℝ) (S := ({0, 1} : Set ℝ))).mp hsSimplex
    exact not_convex_pair01 hsConv

end WithBotTopCounterexample

end
