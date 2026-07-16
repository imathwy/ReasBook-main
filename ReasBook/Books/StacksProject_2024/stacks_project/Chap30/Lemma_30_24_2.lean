import StacksProject_2024.stacks_project.Chap30.Lemma_30_19_3
import StacksProject_2024.stacks_project.Chap30.Lemma_30_23_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- Semantic recall: `lean_leansearch` surfaced the canonical `IsProper` morphism owner,
`Scheme.IdealSheafData.ofIdealTop` for ideal sheaves on affine schemes, and the local Chapter 30
owners `Scheme.CoherentFormalModules`, `schemeModuleCohomology`, and
`schemeModuleTwistByTensorPower`. For the affine base `Spec(A)`, `Scheme.ΓSpecIso` identifies top
sections with `A`, so the source ideal `I : Ideal A` can be transported explicitly before applying
`IdealSheafData.ofIdealTop` and comapping along `f`. -/

/-- The ideal sheaf on `Spec(A)` associated to an ideal `I ⊆ A`, expressed by transporting `I`
across the canonical global-sections isomorphism for `Spec(A)`. -/
abbrev idealSheafDataOfIdealOnSpec {A : Type u} [CommRing A] (I : Ideal A) :
    (Spec (CommRingCat.of A)).IdealSheafData :=
  IdealSheafData.ofIdealTop
    (I.comap (CommRingCat.Hom.hom (ΓSpecIso (CommRingCat.of A)).hom))

namespace Modules

/-- Lemma 30.24.2: let `A` be a Noetherian ring, let `I` be an ideal on the affine base
`Spec(A)`, let `f : X ⟶ Spec(A)` be proper, and let `L` be the ample invertible sheaf representing
the source's `f`-ample invertible sheaf over the affine base. For an object `(F_n)` of
`Coh(X, I \mathcal O_X)`, the first cohomology of every transition kernel twisted by all
sufficiently high tensor powers of `L` vanishes, uniformly in `n`. -/
@[stacks 0884]
theorem properAmpleCoherentFormalModule_transitionKernel_twist_H1_eventually_isZero
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (I : Ideal A)
    [MonoidalCategory X.Modules] (L : X.Modules) [Invertible L] [IsAmple L]
    (F : CoherentFormalModules X ((idealSheafDataOfIdealOnSpec I).comap f)) :
    ∃ d0 : ℤ, ∀ n : ℕ, ∀ d : ℤ, d0 ≤ d →
      IsZero (schemeModuleCohomology
        (schemeModuleTwistByTensorPower L (kernel (((F.obj).stepMap n).hom)) d) 1) := sorry

end Modules

end AlgebraicGeometry.Scheme
