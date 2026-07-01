import Mathlib
import stacks_project.Chap21.Lemma_21_10_4

open CategoryTheory Opposite TopologicalSpace TopCat
open scoped BigOperators

noncomputable section

universe u uι

section

variable {X : TopCat.{u}} {ι : Type uι}

/-- The intersection of the opens indexed by a finite Čech tuple. -/
def cech_intersection (U : ι → Opens X) {n : ℕ} (I : Fin n → ι) : Opens X :=
  iInf fun j ↦ U (I j)

-- Proof sketch: the full intersection is contained in every partial intersection obtained by
-- omitting one index, since membership in the former gives membership in each constituent open.
/-- Omitting one index from a Čech intersection enlarges the open set. -/
theorem cech_intersection_le_succAboveEmb (U : ι → Opens X) {n : ℕ}
    (I : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    cech_intersection U I ≤ cech_intersection U (I ∘ j.succAboveEmb) := sorry

/-- The degree-`p` Čech cochains of a presheaf on a family of opens. -/
abbrev cech_cochains (U : ι → Opens X) (F : X.Presheaf AddCommGrpCat) (p : ℕ) :=
  ∀ I : Fin (p + 1) → ι, F.obj (op (cech_intersection U I))

/-- The restriction map from a partial Čech intersection to the full intersection. -/
def cech_restriction (U : ι → Opens X) (F : X.Presheaf AddCommGrpCat) {n : ℕ}
    (I : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    F.obj (op (cech_intersection U (I ∘ j.succAboveEmb))) ⟶
      F.obj (op (cech_intersection U I)) :=
  F.map (homOfLE (cech_intersection_le_succAboveEmb U I j)).op

/-- The underlying function of the Čech coboundary in degree `p`. -/
def cech_differential_fun (U : ι → Opens X) (F : X.Presheaf AddCommGrpCat) (p : ℕ) :
    cech_cochains U F p → cech_cochains U F (p + 1) :=
  fun s I ↦
    ∑ j : Fin (p + 2),
      (-1 : ℤ) ^ (j : ℕ) • (cech_restriction U F I j) (s (I ∘ j.succAboveEmb))

-- Proof sketch: evaluate both sides on an index tuple and use additivity of each restriction map
-- together with additivity of the finite sum in the target abelian group.
/-- The Čech coboundary is additive on cochains. -/
theorem cech_differential_fun_map_add (U : ι → Opens X) (F : X.Presheaf AddCommGrpCat)
    (p : ℕ) (s t : cech_cochains U F p) :
    cech_differential_fun U F p (s + t) =
      cech_differential_fun U F p s + cech_differential_fun U F p t := sorry

/-- The Čech coboundary in degree `p` as a morphism of abelian groups. -/
def cech_differential (U : ι → Opens X) (F : X.Presheaf AddCommGrpCat) (p : ℕ) :
    AddCommGrpCat.of (cech_cochains U F p) ⟶ AddCommGrpCat.of (cech_cochains U F (p + 1)) :=
  AddCommGrpCat.ofHom <|
    AddMonoidHom.mk' (cech_differential_fun U F p)
      (cech_differential_fun_map_add U F p)

-- Proof sketch: compare the contribution of a double omission `(a, b)` with the contribution of
-- the transposed omission `(b, a)`; the alternating signs make these terms cancel pairwise.
/-- Two successive Čech coboundaries compose to zero. -/
theorem cech_differential_sq (U : ι → Opens X) (F : X.Presheaf AddCommGrpCat) (p : ℕ) :
    cech_differential U F p ≫ cech_differential U F (p + 1) = 0 := sorry

/-- The Čech complex of an abelian presheaf on the indexed family of opens `U`. -/
noncomputable def cech_complex (U : ι → Opens X) (F : X.Presheaf AddCommGrpCat) :
    CochainComplex AddCommGrpCat ℕ :=
  CochainComplex.of (fun p ↦ AddCommGrpCat.of (cech_cochains U F p))
    (cech_differential U F) (cech_differential_sq U F)

/-- The degree-`i` Čech cohomology group of the covering `U` with coefficients in `F`. -/
noncomputable abbrev cech_cohomology (U : ι → Opens X) (F : X.Presheaf AddCommGrpCat) (i : ℕ) :
    AddCommGrpCat :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) i).obj
    (cech_complex U F)

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u + 1} (X.Sheaf AddCommGrpCat.{u})]

-- Proof sketch: represent a torsor class trivial on the cover by local sections on each `U i`,
-- take their pairwise differences to obtain a Čech `1`-cocycle, and check that changing the local
-- sections alters the cocycle by a coboundary. Conversely, glue the trivial torsors on the cover
-- using a Čech cocycle; the quotient condition defining `IsTrivialOnCover` makes the resulting
-- class independent of choices. This is exactly the subset identified inside `H¹(X, ℋ)` via the
-- torsor classification of Lemma `20.4.3`.
/-- Lemma 20.11.3: via the torsor classification of Lemma 20.4.3, the degree-one Čech cohomology
of the covering `U` is identified with the isomorphism classes of `ℋ`-torsors on `X` whose
restriction to every `U i` is trivial, equivalently whose underlying sheaf admits a section over
every `U i`. -/
theorem cech_H1_equiv_torsorIsoClass_isTrivialOnCover (U : ι → Opens X)
    (ℋ : X.Sheaf AddCommGrpCat.{u}) :
    Nonempty ((cech_cohomology U ℋ.presheaf 1) ≃
      { c : CategoryTheory.AbelianSheafTorsor.IsoClasses ℋ // c.IsTrivialOnCover U }) := sorry

end
