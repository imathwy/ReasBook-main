import SmoothManifolds_Lee_2012.Chap08.Sec08_60.Notation_8_60_extra_6
import SmoothManifolds_Lee_2012.Chap08.Sec08_61.Definition_8_61_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold ContDiff ContMDiffMonoidMorphism

-- Domain sampling pass:
-- * primary domain: smooth Lie-group homomorphisms, their induced maps on `GroupLieAlgebra`, and
--   the associated left-invariant vector fields;
-- * sampled owner-style declarations in this domain:
--   `GroupLieAlgebra`, `mulInvariantVectorField`, and the chapter owner
--   `ContMDiffMonoidMorphism.inducedLieAlgebraHomomorphism`, together with its derived theorem
--   `ContMDiffMonoidMorphism.inducedLieAlgebraHomomorphism_related`;
-- * source/core/bridge split here:
--   part (1) is source-facing, asserting existence and uniqueness of the `F`-related
--   left-invariant field on the target;
--   part (2) is a core/canonical recall of the induced Lie algebra homomorphism owner;
-- * primitive data is the induced Lie algebra homomorphism itself; the `f_related` statement is
--   derived API and should not be repackaged as new primitive structure in this file.

section LieGroupHomomorphisms

universe u𝕜 uEG uHG uG uEH uHH uH

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH]
variable {HH : Type uHH} [TopologicalSpace HH]
variable {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {H : Type uH} [Group H] [TopologicalSpace H] [ChartedSpace HH H]
variable [IsManifold I (∞ : ℕ∞ω) G] [IsManifold J (∞ : ℕ∞ω) H]

/-- Theorem 8.44 (1) (Induced Lie Algebra Homomorphisms): for a Lie group homomorphism
`F : G → H` and a left-invariant vector field `Xᴸ` on `G`, there is a unique left-invariant
vector field `Yᴸ` on `H`, represented by some `Y : GroupLieAlgebra J H`, that is `F`-related to
`Xᴸ`. -/
theorem existsUnique_induced_group_lie_algebra_element
    (F : ContMDiffMonoidMorphism I J ∞ G H) (X : GroupLieAlgebra I G) :
    ∃! Y : GroupLieAlgebra J H, VectorField.f_related F Xᴸ Yᴸ := sorry

section InducedLieAlgebraRecall

variable [CompleteSpace EG] [CompleteSpace EH]
variable [LieGroup I (minSmoothness 𝕜 3) G] [LieGroup J (minSmoothness 𝕜 3) H]

/- Theorem 8.44 (2) (Induced Lie Algebra Homomorphisms): the derivative at the identity of a Lie
group homomorphism is the induced Lie algebra homomorphism `F_* : 𝔤 → 𝔥`. -/
variable (F : ContMDiffMonoidMorphism I J ∞ G H)

#check ((F)_*)

/- The corresponding left-invariant vector field `F_* X` on `H` is `F`-related to `Xᴸ` on `G`. -/
variable (X : GroupLieAlgebra I G)

#check ContMDiffMonoidMorphism.inducedLieAlgebraHomomorphism_related F X

end InducedLieAlgebraRecall

end LieGroupHomomorphisms
