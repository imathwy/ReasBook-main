import Mathlib
import Mathlib.Algebra.Category.Ring.Limits

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CommRingCat

universe u v

section

variable {J : Type v} [Preorder J]
variable (F : Jᵒᵖ ⥤ CommRingCat.{u})
variable (I : ∀ j : Jᵒᵖ, Ideal (F.obj j))
variable [UnivLE.{v, u}]

/- Domain-style sampling:
- primary domain: inverse limits of henselian pairs in commutative algebra;
- sampled same-domain owner declarations:
  `HenselianRing`,
  `HenselianRing.is_henselian`,
  `henselianRing_pi_iff`,
  `directedSystem_directLimit_henselianRing`;
- best owner abstraction: the public conclusion should stay the canonical owner
  `HenselianRing ((limit F : CommRingCat.{u}) : Type u)
    (⨅ j, Ideal.comap ((limit.π F j).hom) (I j))`; there is no separate inverse-system wrapper
  notion to introduce here;
- primitive data: the inverse system `F`, the ideal family `I`, and the compatibility maps `hI`;
- derived API: the limit object is supplied canonically by the owner instance
  `CommRingCat.hasLimitsOfSize`, activated here by `[UnivLE.{v, u}]`, and the conclusion is the
  induced henselian-pair instance on that limit ring with the canonical inverse-limit ideal.

Source/core/bridge triage:
- `source-facing`: closure of compatible inverse systems of henselian pairs under inverse limits;
- `core/canonical`: the owner class `HenselianRing`;
- `bridge/view`: the inverse-limit ring `limit F` and the limit ideal
  `⨅ j, Ideal.comap ((limit.π F j).hom) (I j)`.
-/

-- Proof sketch: by Categories, Lemma `4.14.11`, it is enough to treat products and equalizers.
-- The product case is Lemma `15.11.11`. For equalizers, use Gabber's criterion from
-- Lemma `15.11.6`: units in `1 + I` are detected after mapping to the ambient henselian pair, so
-- `I` lies in the Jacobson radical by Lemma `10.19.1`; then a Gabber polynomial has a unique root
-- in each ambient henselian pair, and uniqueness forces the lifted roots to agree in the
-- equalizer, producing the desired root in the limit pair.
/-- Lemma 15.11.12: if `F : Jᵒᵖ ⥤ CommRingCat` is an inverse system of commutative rings over a
preordered set and `I j` is a compatible inverse system of henselian ideals on the stages, then
the inverse-limit ring `limit F`, equipped with the limit ideal
`⨅ j, Ideal.comap ((limit.π F j).hom) (I j)`, is a henselian pair. -/
instance inverseSystem_limit_henselianRing
    (hI : ∀ ⦃j k : Jᵒᵖ⦄ (f : j ⟶ k), Ideal.map (F.map f).hom (I j) ≤ I k)
    [∀ j, HenselianRing (F.obj j) (I j)] :
    HenselianRing ((limit F : CommRingCat.{u}) : Type u)
      (⨅ j, Ideal.comap ((limit.π F j).hom) (I j)) := sorry

end
