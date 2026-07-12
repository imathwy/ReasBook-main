import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}} [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]

-- Semantic recall: `lean_leansearch` surfaced the existing open-immersion/restriction owners,
-- so the source extension statement is recorded directly on subobjects of `F.restrict j` with
-- finite-type and quasi-coherent hypotheses on the restricted subsheaf.

/-- Lemma 28.22.2: let `X` be a quasi-compact and quasi-separated scheme, let `U ⟶ X` be a
quasi-compact open immersion, let `\mathcal F` be a quasi-coherent `\mathcal O_X`-module, and
let `\mathcal G \subset \mathcal F|_U` be a finite type quasi-coherent `\mathcal O_U`-submodule.
Then there exists a finite type quasi-coherent submodule `\mathcal G' \subset \mathcal F` whose
restriction to `U` is `\mathcal G`. -/
@[stacks 01PF]
theorem exists_finiteTypeQuasiCoherentSubsheafExtension
    (j : U ⟶ X) [IsOpenImmersion j] (hj : QuasiCompact j)
    (F : X.Modules) (G : Subobject (F.restrict j))
    (hGqc : ((G : U.Modules)).IsQuasicoherent)
    (hGft : ((G : U.Modules)).IsFiniteType) :
    ∃ (H : Subobject F) (_ : ((H : X.Modules)).IsQuasicoherent)
      (_ : ((H : X.Modules)).IsFiniteType),
      ∃ e : ((H : X.Modules).restrict j) ≅ (G : U.Modules),
        e.hom ≫ G.arrow = (restrictFunctor j).map H.arrow := sorry

end AlgebraicGeometry.Scheme.Modules
