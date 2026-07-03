import Mathlib
import StacksProject_2024.Chap13.Definition_13_33_1
import StacksProject_2024.Chap15.Lemma_15_87_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.SequentialInverseSystem
open Opposite

noncomputable section

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/- Domain-style sampling for Lemma 15.87.7:
- primary domain: triangulated-category homotopy colimits and the Milnor inverse-limit sequence
  for represented contravariant Hom functors;
- sampled owner declarations:
  `CategoryTheory.IsHomotopyColimitOf`,
  `preadditiveYoneda.obj`,
  `Functor.ofSequence`,
  `SequentialInverseSystem.firstDerivedLimit`,
  `CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₁₂`;
- best owner abstraction:
  `source-facing`: the Milnor short exact sequence attached to the owner predicate
    `IsHomotopyColimitOf (Functor.ofSequence f) Khocolim`;
  `core/canonical`: the represented functor `preadditiveYoneda.obj L`, its inverse-system image
    `(Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L`, together with
    `SequentialInverseSystem.firstDerivedLimit`;
  `bridge/view`: the comparison morphism
    `Hom_D(Khocolim, L) ⟶ \varprojlim_n Hom_D(K_n, L)` attached to that chosen telescope
    presentation.
- primitive data: the sequential system `K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯` together with the owner hypothesis
  `IsHomotopyColimitOf (Functor.ofSequence f) Khocolim`;
- derived API: the represented inverse system `(Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L`,
  its canonical owner-level `firstDerivedLimit`, and the presentation-dependent bridge
  `homFromHomotopyColimitComparison`.

Source/core/bridge triage:
- `source-facing`: the Milnor short exact sequence for `Hom_D(-, L)` evaluated on an object
  equipped with `IsHomotopyColimitOf (Functor.ofSequence f)`;
- `core/canonical`: `preadditiveYoneda.obj L`, `(Functor.ofSequence f).op`, and
  `SequentialInverseSystem.firstDerivedLimit`;
- `bridge/view`: `homFromHomotopyColimitComparison`, the comparison map supplied by that chosen
  telescope presentation. -/

private theorem homFromHomotopyColimitCone_naturality
    (L : D) {K : ℕ → D} (f : ∀ n, K n ⟶ K (n + 1))
    [HasCoproduct (Functor.ofSequence f).obj]
    {Khocolim : D} (g : ∐ (Functor.ofSequence f).obj ⟶ Khocolim)
    (h : Khocolim ⟶ (∐ (Functor.ofSequence f).obj)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D)
    (n : ℕ) :
    (preadditiveYoneda.obj L).map (op (Sigma.ι (Functor.ofSequence f).obj (n + 1) ≫ g)) ≫
      ((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L).map (homOfLE (Nat.le_succ n)).op =
    (preadditiveYoneda.obj L).map (op (Sigma.ι (Functor.ofSequence f).obj n ≫ g)) := by
  sorry

private def homFromHomotopyColimitCone
    (L : D) {K : ℕ → D} (f : ∀ n, K n ⟶ K (n + 1))
    [HasCoproduct (Functor.ofSequence f).obj]
    {Khocolim : D} (g : ∐ (Functor.ofSequence f).obj ⟶ Khocolim)
    (h : Khocolim ⟶ (∐ (Functor.ofSequence f).obj)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) :
    Cone ((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L) where
  pt := (preadditiveYoneda.obj L).obj (op Khocolim)
  π := NatTrans.ofOpSequence
    (fun n ↦ (preadditiveYoneda.obj L).map (op (Sigma.ι (Functor.ofSequence f).obj n ≫ g)))
    (fun n ↦ (homFromHomotopyColimitCone_naturality L f g h hKhocolim n).symm)

/-- The comparison morphism
`Hom_D(Khocolim, L) ⟶ \varprojlim_n Hom_D(K_n, L)` induced by a chosen distinguished telescope
triangle presenting `Khocolim` as a homotopy colimit of the sequence
`K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯`. -/
private def homFromHomotopyColimitComparison
    (L : D) {K : ℕ → D} (f : ∀ n, K n ⟶ K (n + 1))
    [HasCoproduct (Functor.ofSequence f).obj]
    {Khocolim : D} (g : ∐ (Functor.ofSequence f).obj ⟶ Khocolim)
    (h : Khocolim ⟶ (∐ (Functor.ofSequence f).obj)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) :
    (preadditiveYoneda.obj L).obj (op Khocolim) ⟶
      limit ((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L) :=
  limit.lift _ (homFromHomotopyColimitCone L f g h hKhocolim)

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D] [IsTriangulated D]

-- Proof sketch: apply the contravariant Hom functor `Hom_D(-, L)` to the opposite of the
-- distinguished telescope triangle presenting `Khocolim`. Lemma 13.4.2 identifies this as a
-- homological functor, so one gets a long exact sequence. The two terms
-- `Hom_D(\bigoplus_n K_n, L)` and `Hom_D(\bigoplus_n K_n, L⟦-1⟧)` identify with the products of
-- `Hom_D(K_n, L)` and `Hom_D(K_n, L⟦-1⟧)`, and Lemma 15.87.1 identifies the kernel and cokernel
-- of the Milnor difference maps with `\varprojlim` and `R^1 \!\varprojlim`. The left term is
-- therefore best exposed through the owner
-- `firstDerivedLimit ((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj _)`, not as
-- a raw cokernel of `derivedLimitDifferenceMap`.
/-- The bridge-level Milnor short exact sequence attached to a chosen distinguished telescope
triangle. The chosen presentation stays internal; the public source-facing theorem below is
phrased only over `IsHomotopyColimitOf (Functor.ofSequence f) Khocolim`. -/
private theorem hom_from_homotopyColimit_shortExact_of_triangle
    (L : D) {K : ℕ → D} (f : ∀ n, K n ⟶ K (n + 1))
    [HasCoproduct (Functor.ofSequence f).obj]
    {Khocolim : D} (g : ∐ (Functor.ofSequence f).obj ⟶ Khocolim)
    (h : Khocolim ⟶ (∐ (Functor.ofSequence f).obj)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) :
    ∃ (ι :
        firstDerivedLimit ((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj (L⟦(-1 : ℤ)⟧)) ⟶
          (preadditiveYoneda.obj L).obj (op Khocolim))
      (hι :
        ι ≫ homFromHomotopyColimitComparison L f g h hKhocolim = 0),
      (ShortComplex.mk ι (homFromHomotopyColimitComparison L f g h hKhocolim) hι).ShortExact :=
  sorry

/-- Lemma 15.87.7: if `Khocolim` is a homotopy colimit of a sequential system
`K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯`, then for every `L` there is a short exact sequence
`0 ⟶ R^1 \!\varprojlim Hom_D(K_n, L⟦-1⟧) ⟶ Hom_D(Khocolim, L) ⟶
\varprojlim_n Hom_D(K_n, L) ⟶ 0`. -/
theorem hom_from_homotopyColimit_shortExact
    (L : D) {K : ℕ → D} (f : ∀ n, K n ⟶ K (n + 1))
    [HasCoproduct (Functor.ofSequence f).obj]
    {Khocolim : D} (hKhocolim : IsHomotopyColimitOf (Functor.ofSequence f) Khocolim) :
    ∃ (ι :
        firstDerivedLimit ((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj (L⟦(-1 : ℤ)⟧)) ⟶
          (preadditiveYoneda.obj L).obj (op Khocolim))
      (π :
        (preadditiveYoneda.obj L).obj (op Khocolim) ⟶
          limit ((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L))
      (h :
        ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  obtain ⟨g, hδ, htriangle⟩ := hKhocolim
  rcases hom_from_homotopyColimit_shortExact_of_triangle L f g hδ htriangle with
    ⟨ι, hι, hshort⟩
  exact ⟨ι, homFromHomotopyColimitComparison L f g hδ htriangle, hι, hshort⟩

end

end CategoryTheory
