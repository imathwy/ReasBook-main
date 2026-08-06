import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.DirectSum.Module
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Definition_22_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_7_2

open CategoryTheory
open scoped BigOperators DirectSum SteenrodAlgebra

noncomputable section

universe u w

-- Semantic recall via `lean_leansearch` did not surface a verified upstream prespectrum-level
-- cohomology owner with a Steenrod-algebra action in the current environment. Following local
-- Chapter 25 precedent, this file therefore uses the source-facing prespectrum cohomology owner
-- `presentation.HStar T = H^*(T; ZMod 2)`, and records the Steenrod action as extra `Sq^i` data
-- over that fixed cohomology presentation.

/-- The target degree of the `k`th Adem summand agrees with the target degree of
`Sq^i ∘ Sq^j` on the graded cohomology of a prespectrum. -/
theorem prespectrumSteenrodAdemTargetDegree
    (i j : ℕ) (q : ℤ) (k : Fin (i / 2 + 1)) :
    (q + (k : ℤ)) + ((i + j - k : ℕ) : ℤ) = (q + (j : ℤ)) + i := sorry

/-- The target degree of `Sq^0` on the graded cohomology of a prespectrum is the original degree.
-/
theorem prespectrumSteenrodZeroTargetDegree (q : ℤ) :
    q + (0 : ℕ) = q := sorry

/-- A chosen source-facing presentation of the total mod-`2` cohomology object `H^*(T; ZMod 2)`
of prespectra, together with its pullback maps along prespectrum morphisms and the canonical
underlying `ZMod 2`-module structure on that total cohomology object. -/
structure PrespectrumModTwoCohomologyPresentation where
  /-- The graded mod-`2` cohomology groups `H^q(T; ZMod 2)` of prespectra. -/
  cohomology : Prespectrum.{u, w} → ℤ → AddCommGrpCat
  /-- Pullback on total mod-`2` cohomology along a map of prespectra. -/
  pullback :
    ∀ {T U : Prespectrum.{u, w}}, (T ⟶ U) →
      (⨁ q : ℤ, cohomology U q) →+ ⨁ q : ℤ, cohomology T q
  /-- The canonical `ZMod 2`-module structure on the chosen total cohomology object
  `H^*(T; ZMod 2)`. -/
  hStarModule :
    ∀ T : Prespectrum.{u, w}, Module (ZMod 2) (⨁ q : ℤ, cohomology T q)

namespace PrespectrumModTwoCohomologyPresentation

/-- The total mod-`2` cohomology object `H^*(T; ZMod 2)` of a prespectrum `T` in a chosen
source-facing presentation. -/
abbrev HStar
    (presentation : PrespectrumModTwoCohomologyPresentation)
    (T : Prespectrum.{u, w}) : Type _ :=
  ⨁ q : ℤ, presentation.cohomology T q

/-- `presentation.HStar T` is definitionally the direct sum of the graded cohomology groups
`presentation.cohomology T q`. -/
theorem hStar_def
    (presentation : PrespectrumModTwoCohomologyPresentation)
    (T : Prespectrum.{u, w}) :
    presentation.HStar T = (⨁ q : ℤ, presentation.cohomology T q) :=
  rfl

/-- Pullback along a map of prespectra on the chosen total mod-`2` cohomology owner
`presentation.HStar`. -/
abbrev hStarPullback
    (presentation : PrespectrumModTwoCohomologyPresentation)
    {T U : Prespectrum.{u, w}} (f : T ⟶ U) :
    presentation.HStar U →+ presentation.HStar T :=
  presentation.pullback f

/-- `presentation.hStarPullback f` is definitionally the stored pullback map of the chosen
prespectrum mod-`2` cohomology presentation. -/
theorem hStarPullback_def
    (presentation : PrespectrumModTwoCohomologyPresentation)
    {T U : Prespectrum.{u, w}} (f : T ⟶ U) :
    presentation.hStarPullback f = presentation.pullback f :=
  rfl

/-- The chosen cohomology presentation supplies the canonical `ZMod 2`-module structure on
`presentation.HStar T`. -/
instance hStarModuleInst
    (presentation : PrespectrumModTwoCohomologyPresentation)
    (T : Prespectrum.{u, w}) :
    Module (ZMod 2) (presentation.HStar T) :=
  presentation.hStarModule T

/-- The explicit `ZMod 2`-module structure on `presentation.HStar T` carried by the chosen
cohomology presentation. -/
abbrev baseModule
    (presentation : PrespectrumModTwoCohomologyPresentation)
    (T : Prespectrum.{u, w}) :
    Module (ZMod 2) (presentation.HStar T) :=
  presentation.hStarModule T

end PrespectrumModTwoCohomologyPresentation

/-- A chosen Steenrod action on a fixed source-facing prespectrum cohomology presentation,
recorded by the actual `ModTwoSteenrodAlgebra`-module structure on `presentation.HStar T`
together with the degreewise `Sq^i` formulas used later in Chapter 25. -/
structure PrespectrumModTwoSteenrodAction
    (presentation : PrespectrumModTwoCohomologyPresentation) where
  /-- The scalar action of `ModTwoSteenrodAlgebra` on `presentation.HStar T`. -/
  module :
    ∀ T : Prespectrum.{u, w}, Module ModTwoSteenrodAlgebra (presentation.HStar T)
  /-- The degreewise Steenrod generator `Sq^i : H^q(T; ZMod 2) → H^(q + i)(T; ZMod 2)`. -/
  sq :
    ∀ (T : Prespectrum.{u, w}) (i : ℕ) (q : ℤ),
      presentation.cohomology T q ⟶ presentation.cohomology T (q + i)
  /-- On the total direct sum, the generator `Sq^i ∈ ModTwoSteenrodAlgebra` acts by the
  corresponding degreewise Steenrod square. -/
  generator_smul :
    ∀ (T : Prespectrum.{u, w}) (i : ℕ) (q : ℤ) (x : presentation.cohomology T q),
      -- Local instance justification (proof-local temporary data): the chosen Steenrod action
      -- stores the
      -- specific `ModTwoSteenrodAlgebra`-module structure on `presentation.HStar T` used to
      -- interpret `•` in this source-facing compatibility field.
      letI := module T
      (Sq^i) •
          (DirectSum.lof ℤ ℤ (fun n ↦ presentation.cohomology T n) q x :
            presentation.HStar T) =
        (DirectSum.lof ℤ ℤ (fun n ↦ presentation.cohomology T n) (q + i) (sq T i q x) :
          presentation.HStar T)
  /-- The degreewise Steenrod generator `Sq^0` acts as the identity. -/
  sq_zero :
    ∀ (T : Prespectrum.{u, w}) (q : ℤ) (x : presentation.cohomology T q),
      sq T 0 q x =
        cast
          (congrArg
            (fun m ↦ ((presentation.cohomology T m) : Type _))
            (prespectrumSteenrodZeroTargetDegree q).symm)
          x
  /-- The degreewise Steenrod generators satisfy the standard mod-`2` Adem relations. -/
  adem :
    ∀ (T : Prespectrum.{u, w}) (i j : ℕ) (q : ℤ) (_ : i < 2 * j)
      (x : presentation.cohomology T q),
      sq T i (q + j) (sq T j q x) =
        ∑ k : Fin (i / 2 + 1),
          if Nat.choose (j - k - 1) (i - 2 * k) % 2 = 1 then
            cast
              (congrArg
                (fun m ↦ ((presentation.cohomology T m) : Type _))
                (prespectrumSteenrodAdemTargetDegree i j q k))
              (sq T (i + j - k) (q + k) (sq T k q x))
          else 0
  /-- Pullback along a map of prespectra is `ModTwoSteenrodAlgebra`-linear. -/
  naturality :
    ∀ {T U : Prespectrum.{u, w}} (f : T ⟶ U) (a : ModTwoSteenrodAlgebra)
      (x : presentation.HStar U),
      -- Local instance justification (proof-local temporary data): `a • x` uses the chosen
      -- action's
      -- module structure on the source cohomology object `presentation.HStar U`.
      letI := module U
      -- Local instance justification (proof-local temporary data): the target of pullback carries
      -- the
      -- chosen action's module structure on `presentation.HStar T`.
      letI := module T
      presentation.hStarPullback f (a • x) = a • presentation.hStarPullback f x

/-- Lemma 25.4.3. The total mod-`2` cohomology of prespectra carries a natural action of the
Steenrod algebra: for the fixed source-facing cohomology presentation there exists a simultaneous
module structure on every `H^*(T; ZMod 2)`, with the correct degreewise squares, Adem relations,
and pullback naturality.  This existence assertion is the lemma's conclusion. -/
theorem exists_prespectrumModTwoSteenrodAction
    (presentation : PrespectrumModTwoCohomologyPresentation) :
    Nonempty (PrespectrumModTwoSteenrodAction presentation) := by
  sorry

/-- A chosen prespectrum Steenrod action supplies the module instance on a particular
prespectrum. -/
instance prespectrumModTwoCohomologyModule
    (presentation : PrespectrumModTwoCohomologyPresentation)
    (action : PrespectrumModTwoSteenrodAction presentation)
    (T : Prespectrum.{u, w}) :
    Module ModTwoSteenrodAlgebra (presentation.HStar T) :=
  action.module T

namespace PrespectrumModTwoSteenrodAction

variable {presentation : PrespectrumModTwoCohomologyPresentation}

/-- The explicit action hom of `ModTwoSteenrodAlgebra` on `presentation.HStar T`
carried by a chosen prespectrum Steenrod action. -/
abbrev actionHom
    (action : PrespectrumModTwoSteenrodAction presentation)
    (T : Prespectrum.{u, w}) :
    ModTwoSteenrodAlgebra →+* AddMonoid.End (presentation.HStar T) :=
  @Module.toAddMonoidEnd ModTwoSteenrodAlgebra (presentation.HStar T)
    inferInstance inferInstance (action.module T)

/-- The Steenrod generator `Sq^i ∈ ModTwoSteenrodAlgebra` acts on homogeneous classes in
`H^*(T; ZMod 2)` by the corresponding degreewise Steenrod square. -/
theorem smul_generator_eq_sq
    (action : PrespectrumModTwoSteenrodAction presentation)
    (T : Prespectrum.{u, w}) (i : ℕ) (q : ℤ) (x : presentation.cohomology T q) :
    -- Local instance justification (proof-local temporary data): this theorem spells `•`
    -- using the specific module structure chosen by `action` on `presentation.HStar T`.
    letI := action.module T
    (Sq^i) •
        (DirectSum.lof ℤ ℤ (fun n ↦ presentation.cohomology T n) q x : presentation.HStar T) =
      (DirectSum.lof ℤ ℤ (fun n ↦ presentation.cohomology T n) (q + i) (action.sq T i q x) :
        presentation.HStar T) :=
  action.generator_smul T i q x

/-- The degreewise Steenrod generator `Sq^0` acts as the identity on `H^q(T; ZMod 2)`. -/
theorem sq_zero_apply
    (action : PrespectrumModTwoSteenrodAction presentation)
    (T : Prespectrum.{u, w}) (q : ℤ) (x : presentation.cohomology T q) :
    action.sq T 0 q x =
      cast
        (congrArg
          (fun m ↦ ((presentation.cohomology T m) : Type _))
          (prespectrumSteenrodZeroTargetDegree q).symm)
        x :=
  action.sq_zero T q x

/-- The degreewise Steenrod generators satisfy the standard mod-`2` Adem relations. -/
theorem adem_apply
    (action : PrespectrumModTwoSteenrodAction presentation)
    (T : Prespectrum.{u, w}) (i j : ℕ) (q : ℤ) (h : i < 2 * j)
    (x : presentation.cohomology T q) :
    action.sq T i (q + j) (action.sq T j q x) =
      ∑ k : Fin (i / 2 + 1),
        if Nat.choose (j - k - 1) (i - 2 * k) % 2 = 1 then
          cast
            (congrArg
              (fun m ↦ ((presentation.cohomology T m) : Type _))
              (prespectrumSteenrodAdemTargetDegree i j q k))
            (action.sq T (i + j - k) (q + k) (action.sq T k q x))
        else 0 :=
  action.adem T i j q h x

end PrespectrumModTwoSteenrodAction

/-- Pullback along a prespectrum morphism is `ModTwoSteenrodAlgebra`-linear for the chosen
Steenrod action on `presentation.HStar`. -/
theorem prespectrumModTwoCohomology_pullback_smul
    (presentation : PrespectrumModTwoCohomologyPresentation)
    (action : PrespectrumModTwoSteenrodAction presentation)
    {T U : Prespectrum.{u, w}} (f : T ⟶ U) (a : ModTwoSteenrodAlgebra)
    (x : presentation.HStar U) :
    -- Local instance justification (proof-local temporary data): the source term `a • x`
    -- uses the chosen action's module structure on `presentation.HStar U`.
    letI := action.module U
    -- Local instance justification (proof-local temporary data): the target of pullback uses
    -- the chosen action's module structure on `presentation.HStar T`.
    letI := action.module T
    presentation.hStarPullback f (a • x) =
      a • presentation.hStarPullback f x := by
  simpa using action.naturality f a x
