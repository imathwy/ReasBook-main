import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Restrict

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall:
Semantic search was unavailable in this repair session; previous recall recorded only generic
projective-spectrum/open-cover API for this shape. Local Chapter 29 precedent fixes the intended
source-facing owners as `RelativelyAmple`, `ProjectiveSpaceOver`,
`ProjectiveSpaceOver.tautologicalSheaf`, and `Scheme.Modules.Invertible.tensorPow`, but importing
those owners currently forces Lake to rebuild non-dependency-closed Chapter 29 files before this
target elaborates. This item therefore records the source lemma as a labeled recall block without
introducing fake replacements for relative ampleness or projective space. The Stacks tag evidence
is consistent: item tag `02NR` and source URL `https://stacks.math.columbia.edu/tag/02NR`.
-/

/- Lemma 29.39.7 (Stacks tag `02NR`): let `f : X ⟶ S` be a finite-type morphism of schemes
and let `\mathcal L` be an invertible sheaf on `X`. Then `\mathcal L` is `f`-relatively ample
if and only if there is an open cover `S = ⋃ V_j` such that, for every `j`, there are integers
`d_j ≥ 1` and `n_j ≥ 0` and an immersion
`i_j : X_j = f^{-1}(V_j) = V_j ×_S X ⟶ \mathbf P^{n_j}_{V_j}` over `V_j` with
`\mathcal L^{\otimes d_j}|_{X_j} ≅ i_j^*\mathcal O_{\mathbf P^{n_j}_{V_j}}(1)`.

When the Chapter 29 relative-ampleness and projective-space owners are dependency-closed, the
intended source-facing theorem is the equivalence between `RelativelyAmple f L` and an
open-cover family of positive tensor powers, relative projective spaces `ProjectiveSpaceOver
(V j).toScheme n`, immersions over `V j`, and tautological-sheaf pullback isomorphisms.
-/
#check fun {X S : Scheme.{u}} (f : X ⟶ S) ↦ LocallyOfFiniteType f
#check fun {X S : Scheme.{u}} (f : X ⟶ S) ↦ QuasiCompact f
#check fun {S : Scheme.{u}} ↦ Scheme.OpenCover.{u} S
#check Scheme.OpenCover.isOpenCover_opensRange
#check fun {X S : Scheme.{u}} (f : X ⟶ S) (𝒰 : Scheme.OpenCover.{u} S) (j : 𝒰.I₀) ↦
  f ∣_ ((𝒰.f j).opensRange)
#check fun {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) ↦ pullback.fst f g
#check fun {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) ↦ pullback.snd f g
#check fun {X P : Scheme.{u}} (i : X ⟶ P) ↦ IsImmersion i
#check fun {X P : Scheme.{u}} (i : X ⟶ P) (M : P.Modules) ↦
  (Scheme.Modules.pullback i).obj M

end AlgebraicGeometry
