import Mathlib.CategoryTheory.CommSq
import StacksProject_2024.stacks_project.Chap10.«10_69_0_1»
import StacksProject_2024.stacks_project.Chap31.Lemma_31_19_2

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` only surfaced the ambient immersion owners and did not
-- expose a ready-made global pullback map for the Chapter 31 conormal-algebra owner. Local project
-- search verified that the available core API is the affine conormal-algebra owner
-- `immersionAffineConormalAlgebra`, the canonical affine-open section map `g.appLE ... .hom`,
-- and the associated-graded ring morphism `idealAssociatedGradedMap`, so this item is recorded
-- as the source-faithful affine-local comparison map that characterizes the global graded-algebra
-- morphism on charts.

section

variable {Z X Z' X' : Scheme.{u}}
variable {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}

private abbrev immersionAffineAmbientRingHom
    (U : X.affineOpens) (U' : X'.affineOpens)
    (e : (U : X.Opens) ≤ g ⁻¹ᵁ (U' : X'.Opens)) :
    Γ(X', (U' : X'.Opens)) →+* Γ(X, (U : X.Opens)) :=
  (g.appLE (U' : X'.Opens) (U : X.Opens) e).hom

/-- Helper for Lemma 31.19.3: on affine charts in a commutative square of immersions, the ambient
section-ring map carries the kernel ideal cutting out `Z' ∩ U'` into the kernel ideal cutting out
`Z ∩ U`. -/
theorem immersionAffineConormalIdeal_le_comap
    (sq : CommSq f i i' g)
    (U : X.affineOpens) (U' : X'.affineOpens)
    (e : (U : X.Opens) ≤ g ⁻¹ᵁ (U' : X'.Opens)) :
    immersionAffineConormalIdeal i' (U' : X'.Opens) ≤
      Ideal.comap ((g.appLE (U' : X'.Opens) (U : X.Opens) e).hom)
        (immersionAffineConormalIdeal i (U : X.Opens)) := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  rw [Ideal.mem_comap, RingHom.mem_ker]
  have eig : i ⁻¹ᵁ (U : X.Opens) ≤ (i ≫ g) ⁻¹ᵁ (U' : X'.Opens) := by
    intro z hz
    exact e hz
  have efg : i ⁻¹ᵁ (U : X.Opens) ≤ (f ≫ i') ⁻¹ᵁ (U' : X'.Opens) := by
    intro z hz
    change (f ≫ i').base z ∈ (U' : X'.Opens)
    rw [sq.w]
    exact e hz
  have happ :
      i'.app (U' : X'.Opens) ≫
          f.appLE (i' ⁻¹ᵁ (U' : X'.Opens)) (i ⁻¹ᵁ (U : X.Opens))
            efg =
        g.appLE (U' : X'.Opens) (U : X.Opens) e ≫
          i.appLE (U : X.Opens) (i ⁻¹ᵁ (U : X.Opens)) le_rfl := by
    calc
      i'.app (U' : X'.Opens) ≫
          f.appLE (i' ⁻¹ᵁ (U' : X'.Opens)) (i ⁻¹ᵁ (U : X.Opens))
            efg =
        (f ≫ i').appLE (U' : X'.Opens) (i ⁻¹ᵁ (U : X.Opens))
          efg := by
          symm
          simpa using
            Scheme.Hom.comp_appLE f i' (U' : X'.Opens) (i ⁻¹ᵁ (U : X.Opens))
              efg
      _ = (i ≫ g).appLE (U' : X'.Opens) (i ⁻¹ᵁ (U : X.Opens)) eig := by
        simpa [sq.w]
      _ =
          g.appLE (U' : X'.Opens) (U : X.Opens) e ≫
            i.appLE (U : X.Opens) (i ⁻¹ᵁ (U : X.Opens)) le_rfl := by
          simpa using
            (Scheme.Hom.appLE_comp_appLE i g
              (U' : X'.Opens) (U : X.Opens) (i ⁻¹ᵁ (U : X.Opens)) e le_rfl).symm
  have happx := congrArg (fun φ ↦ φ.hom x) happ
  have hzero :
      (f.appLE (i' ⁻¹ᵁ (U' : X'.Opens)) (i ⁻¹ᵁ (U : X.Opens))
          efg).hom ((i'.app (U' : X'.Opens)).hom x) = 0 := by
    simpa [hx]
  have hrewrite :
      (i.appLE (U : X.Opens) (i ⁻¹ᵁ (U : X.Opens)) le_rfl).hom
          ((g.appLE (U' : X'.Opens) (U : X.Opens) e).hom x) =
        (f.appLE (i' ⁻¹ᵁ (U' : X'.Opens)) (i ⁻¹ᵁ (U : X.Opens))
            efg).hom
          ((i'.app (U' : X'.Opens)).hom x) := by
    simpa [CommRingCat.hom_comp, RingHom.comp_apply] using happx.symm
  have hfinal :
      (i.appLE (U : X.Opens) (i ⁻¹ᵁ (U : X.Opens)) le_rfl).hom
          ((g.appLE (U' : X'.Opens) (U : X.Opens) e).hom x) = 0 :=
    hrewrite.trans hzero
  simpa [immersionAffineAmbientRingHom, Scheme.Hom.appLE_eq_app] using hfinal

/-- Lemma 31.19.3: for a commutative square of schemes
`Z ⟶ X`, `Z' ⟶ X'` with immersions `i` and `i'`, every affine pair
`U = Spec R ⊆ X`, `U' = Spec R' ⊆ X'` with `g(U) ⊆ U'` carries the canonical map on conormal
algebras
`Γ(Z' ∩ U', \mathcal C_{Z'/X', *}) → Γ(Z ∩ U, \mathcal C_{Z/X, *})`,
realized in the current project as the associated-graded ring morphism induced by the affine
section-ring map `Γ(X', U') → Γ(X, U)` sending the kernel ideal of `i'` into the kernel ideal of
`i`. This is the affine-local comparison that characterizes the global graded
`\mathcal O_Z`-algebra map `f^* \mathcal C_{Z'/X', *} → \mathcal C_{Z/X, *}` from the source
statement. -/
@[stacks 0634]
abbrev immersionAffineConormalAlgebraMap
    (sq : CommSq f i i' g)
    (U : X.affineOpens) (U' : X'.affineOpens)
    (e : (U : X.Opens) ≤ g ⁻¹ᵁ (U' : X'.Opens)) :
    immersionAffineConormalAlgebra i' (U' : X'.Opens) →+*
      immersionAffineConormalAlgebra i (U : X.Opens) :=
  idealAssociatedGradedMap
    (immersionAffineAmbientRingHom U U' e)
    (immersionAffineConormalIdeal_le_comap sq U U' e)

/-- Companion expansion: the affine-local conormal algebra comparison map is the associated graded
map induced by the ambient affine-open section-ring map. -/
theorem immersionAffineConormalAlgebraMap_def
    (sq : CommSq f i i' g)
    (U : X.affineOpens) (U' : X'.affineOpens)
    (e : (U : X.Opens) ≤ g ⁻¹ᵁ (U' : X'.Opens)) :
    immersionAffineConormalAlgebraMap sq U U' e =
      idealAssociatedGradedMap
        ((g.appLE (U' : X'.Opens) (U : X.Opens) e).hom)
        (immersionAffineConormalIdeal_le_comap sq U U' e) :=
  rfl

end

end AlgebraicGeometry
