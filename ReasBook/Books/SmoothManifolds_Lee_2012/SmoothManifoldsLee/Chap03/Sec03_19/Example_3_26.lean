import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

/- Mathlib models several of Lee's standard categories by the canonical expressions below:
`Type u` for sets, `TopCat` for topological spaces, `GrpCat` for groups, `Ab` for abelian groups,
`RingCat` for rings, `CommRingCat` for commutative rings, and `ModuleCat ℝ` / `ModuleCat ℂ`
for real and complex vector spaces. -/
#check (Type u)
#check TopCat
#check GrpCat
#check Ab
#check RingCat
#check CommRingCat
#check ModuleCat ℝ
#check ModuleCat ℂ

/- The category of pointed sets is mathlib's canonical category `Pointed`. -/
recall Pointed

-- Proof sketch: a morphism in `Pointed` is a function together with the single axiom that it sends
-- the distinguished point of the source to the distinguished point of the target; conversely, any
-- such function packages into a `Pointed.Hom`.
/-- Example 3.26: a map between pointed sets is a pointed map exactly when it is the underlying
function of a morphism in the category `Pointed`. -/
theorem pointed_map_iff_exists_hom {X Y : Type u} (p : X) (p' : Y) (f : X → Y) :
    f p = p' ↔ ∃ F : Pointed.of p ⟶ Pointed.of p', ⇑F = f := by
  constructor
  · intro hf
    exact ⟨⟨f, hf⟩, rfl⟩
  · rintro ⟨F, rfl⟩
    exact F.map_point
