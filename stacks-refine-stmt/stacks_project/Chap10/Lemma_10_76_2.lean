import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

-- Proof sketch: compute `Tor_n^R(-, N)` from a projective resolution of `N`. Tensoring that fixed
-- resolution termwise with the filtered diagram `F` commutes with filtered colimits by Lemma
-- `10.12.9`, and homology commutes with filtered colimits by Lemma `10.8.8`, so the canonical
-- comparison map is an isomorphism.
/-- Lemma 10.76.2: for a filtered diagram `i ↦ M_i` of `R`-modules and a fixed `R`-module `N`,
the canonical map
`\mathop{\mathrm{colim}}_i \operatorname{Tor}_n^R(M_i, N) \to
\operatorname{Tor}_n^R(\mathop{\mathrm{colim}}_i M_i, N)`
is an isomorphism. -/
theorem tor_filteredColimitComparison_isIso
    {R : Type u} [CommRing R]
    {J : Type v} [Category.{v} J] [IsFiltered J] [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R)
    (N : ModuleCat.{u} R) (n : ℕ) :
    IsIso (colimit.post F ((Tor (ModuleCat.{u} R) n).flip.obj N)) := sorry
