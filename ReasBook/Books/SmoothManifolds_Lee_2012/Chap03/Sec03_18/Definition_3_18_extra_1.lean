import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Sheaf.Smooth

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open TopologicalSpace CategoryTheory

open scoped ContDiff Manifold

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M]

local notation "𝒪∞" => smoothSheafCommRing I 𝓘(ℝ) M ℝ

/-- The germ ring of smooth real-valued functions at `p`, identified with the canonical stalk of
`smoothSheafCommRing I 𝓘(ℝ) M ℝ` at `p`. -/
abbrev smoothGermRing (I : ModelWithCorners ℝ E H) (p : M) :=
  ↑((smoothSheafCommRing I 𝓘(ℝ) M ℝ).presheaf.stalk p)

set_option quotPrecheck false in
scoped[Manifold] notation "C^∞_[" x "](" IM ")" =>
  smoothGermRing IM x

/- Definition 3.18-extra-1 (core/canonical recall): the textbook germ ring `C_p^∞(M)` is the
canonical stalk `(smoothSheafCommRing I 𝓘(ℝ) M ℝ).presheaf.stalk p`, written `C^∞_[p](I)` in the
`Manifold` scope. -/
#check (smoothSheafCommRing I 𝓘(ℝ) M ℝ).presheaf.stalk

/-- Constant smooth functions endow `C_p^∞(M)` with its natural `ℝ`-algebra structure. -/
instance smooth_function_germs_at_algebra (p : M) :
    Algebra ℝ C^∞_[p](I) :=
  letI : Algebra ℝ C^∞⟮I, (⊤ : Opens M); 𝓘(ℝ), ℝ⟯ := inferInstance
  RingHom.toAlgebra
    ((𝒪∞.presheaf.Γgerm p).hom.comp (algebraMap ℝ C^∞⟮I, (⊤ : Opens M); 𝓘(ℝ), ℝ⟯))

namespace smoothSheafCommRing

-- Proof sketch: use `TopCat.Presheaf.germ_eq` to pass from equality in the stalk to equality after
-- restricting to a smaller open neighborhood, and use `TopCat.Presheaf.germ_ext` for the converse.
/-- Two smooth local functions determine the same element of `C^∞_[p](I)` exactly when their
restrictions agree on some smaller neighborhood of `p`. -/
theorem germ_eq_iff {p : M} {U V : Opens M} (hpU : p ∈ U) (hpV : p ∈ V)
    (f : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯) (g : C^∞⟮I, V; 𝓘(ℝ), ℝ⟯) :
    𝒪∞.presheaf.germ U p hpU f = 𝒪∞.presheaf.germ V p hpV g ↔
      ∃ (W : Opens M) (_ : p ∈ W) (iWU : W ⟶ U) (iWV : W ⟶ V),
        𝒪∞.presheaf.map iWU.op f = 𝒪∞.presheaf.map iWV.op g := by
  constructor
  · intro h
    exact 𝒪∞.presheaf.germ_eq p hpU hpV f g h
  · rintro ⟨W, hpW, iWU, iWV, hfg⟩
    exact 𝒪∞.presheaf.germ_ext W hpW iWU iWV hfg

end smoothSheafCommRing
