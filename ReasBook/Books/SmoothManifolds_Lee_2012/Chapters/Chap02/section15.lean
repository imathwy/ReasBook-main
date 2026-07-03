import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_2_15 (from Chap02/Sec02_09) -/
open scoped Manifold ContDiff

noncomputable section

section Composition

universe u𝕜 uE uF uG uH uH' uH'' uM uN uP

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {P : Type uP} [TopologicalSpace P] [ChartedSpace H'' P]
variable {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'} {K : ModelWithCorners 𝕜 G H''}

/- Recall for part (a): composition of diffeomorphisms is the canonical constructor
`Diffeomorph.trans`. -/
#check Diffeomorph.trans

end Composition

namespace Diffeomorph

section Pi

universe u𝕜 uι uE uF uH uG uM uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {ι : Type uι} [Fintype ι]
variable {E : ι → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
variable {F : ι → Type uF} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
variable {H : ι → Type uH} [∀ i, TopologicalSpace (H i)]
variable {G : ι → Type uG} [∀ i, TopologicalSpace (G i)]
variable {M : ι → Type uM} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)]
variable {N : ι → Type uN} [∀ i, TopologicalSpace (N i)] [∀ i, ChartedSpace (G i) (N i)]
variable {I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)}
variable {J : ∀ i, ModelWithCorners 𝕜 (F i) (G i)}

/-- The coordinatewise product map associated to a finite family of diffeomorphisms is bijective. -/
-- Proof sketch: the inverse is the coordinatewise product of the inverse diffeomorphisms, so
-- injectivity and surjectivity both reduce to the corresponding pointwise identities.
theorem pi_bijective (Φ : ∀ i, M i ≃ₘ⟮I i, J i⟯ N i) :
    Function.Bijective (fun x : ∀ i, M i ↦ fun i ↦ Φ i (x i)) := sorry

/-- Proposition 2.15 (1): part (b), the coordinatewise product of a finite family of
diffeomorphisms is a diffeomorphism of product manifolds. -/
def pi (Φ : ∀ i, M i ≃ₘ⟮I i, J i⟯ N i) :
    (∀ i, M i) ≃ₘ⟮ModelWithCorners.pi I, ModelWithCorners.pi J⟯ (∀ i, N i) :=
  IsLocalDiffeomorph.diffeomorphOfBijective
    (isLocalDiffeomorph_pi fun i ↦ (Φ i).isLocalDiffeomorph)
    (pi_bijective Φ)

end Pi

section RestrictOpen

universe u𝕜 uE uF uH uH' uM uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {n : ℕ∞ω}

/-- The image of an open subset under a diffeomorphism is open. -/
-- Proof sketch: reinterpret the diffeomorphism as a homeomorphism and apply the standard theorem
-- that homeomorphisms are open maps.
theorem restrictOpen_image_isOpen (Φ : M ≃ₘ^n⟮I, J⟯ N) (U : TopologicalSpace.Opens M) :
    IsOpen (Set.range fun x : U ↦ Φ x) := sorry

/-- The open image of an open subset under a diffeomorphism. -/
abbrev restrictOpenImage (Φ : M ≃ₘ^n⟮I, J⟯ N) (U : TopologicalSpace.Opens M) :
    TopologicalSpace.Opens N :=
  ⟨Set.range fun x : U ↦ Φ x, restrictOpen_image_isOpen Φ U⟩

/-- The restricted map from an open subset to its image under a diffeomorphism. -/
def restrictOpenMap (Φ : M ≃ₘ^n⟮I, J⟯ N) (U : TopologicalSpace.Opens M) :
    U → restrictOpenImage Φ U :=
  Set.rangeFactorization fun x : U ↦ Φ x

/-- The restricted map to the image is bijective. -/
-- Proof sketch: `Set.rangeFactorization` is always surjective onto the range, and injectivity comes
-- from the injectivity of the ambient diffeomorphism.
theorem restrictOpenMap_bijective (Φ : M ≃ₘ^n⟮I, J⟯ N) (U : TopologicalSpace.Opens M) :
    Function.Bijective (restrictOpenMap Φ U) := sorry

/-- The restricted map to the image is a local diffeomorphism. -/
-- Proof sketch: restrict the ambient local diffeomorphism `Φ.isLocalDiffeomorph` along the open
-- inclusion `U ↪ M`, and then transport the codomain to the open image subtype.
theorem restrictOpenMap_isLocalDiffeomorph (Φ : M ≃ₘ^n⟮I, J⟯ N) (U : TopologicalSpace.Opens M) :
    IsLocalDiffeomorph I J n (restrictOpenMap Φ U) := sorry

/-- Proposition 2.15 (2): part (d), in the canonical `C^n` form used downstream, restricting a
diffeomorphism to an open submanifold yields a diffeomorphism onto its image. The source smooth
statement is the specialization `n = ∞`. -/
def restrictOpen (Φ : M ≃ₘ^n⟮I, J⟯ N) (U : TopologicalSpace.Opens M) :
    U ≃ₘ^n⟮I, J⟯ restrictOpenImage Φ U :=
  (restrictOpenMap_isLocalDiffeomorph Φ U).diffeomorphOfBijective (restrictOpenMap_bijective Φ U)

/-- The restricted diffeomorphism acts by the ambient diffeomorphism on underlying points. -/
@[simp] theorem restrictOpen_apply (Φ : M ≃ₘ^n⟮I, J⟯ N) (U : TopologicalSpace.Opens M)
    (x : U) : ((Φ.restrictOpen U x : Φ.restrictOpenImage U) : N) = Φ x :=
  rfl

end RestrictOpen

end Diffeomorph

section Homeomorphisms

universe u𝕜 uE uF uH uH' uM uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}

/- Recall for part (c): every diffeomorphism is a homeomorphism via
`Diffeomorph.toHomeomorph`. -/
#check Diffeomorph.toHomeomorph

-- Proof sketch: pass from the diffeomorphism to its underlying homeomorphism and use that every
-- homeomorphism is an open map.
/-- Proposition 2.15 (3): part (c), every diffeomorphism is an open map. -/
theorem diffeomorph_isOpenMap (Φ : M ≃ₘ⟮I, J⟯ N) : IsOpenMap Φ := sorry

end Homeomorphisms

section DiffeomorphicRelation

universe u𝕜 uE uF uG uH uH' uH'' uM uN uP

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'} {K : ModelWithCorners 𝕜 G H''}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (∞ : ℕ∞ω) M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J (∞ : ℕ∞ω) N]
variable {P : Type uP} [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K (∞ : ℕ∞ω) P]

-- Proof sketch: use the identity diffeomorphism `Diffeomorph.refl`.
/-- Proposition 2.15 (4): part (e), every smooth manifold is diffeomorphic to itself. -/
theorem diffeomorphic_refl : Nonempty (M ≃ₘ⟮I, I⟯ M) := sorry

-- Proof sketch: reverse a chosen diffeomorphism using `Diffeomorph.symm`.
/-- Proposition 2.15 (5): part (e), diffeomorphic smooth manifolds remain diffeomorphic after
swapping source and target. -/
theorem diffeomorphic_symm (h : Nonempty (M ≃ₘ⟮I, J⟯ N)) :
    Nonempty (N ≃ₘ⟮J, I⟯ M) := sorry

-- Proof sketch: compose chosen diffeomorphisms using `Diffeomorph.trans`.
/-- Proposition 2.15 (6): part (e), diffeomorphism is transitive on smooth manifolds. -/
theorem diffeomorphic_trans (hMN : Nonempty (M ≃ₘ⟮I, J⟯ N))
    (hNP : Nonempty (N ≃ₘ⟮J, K⟯ P)) : Nonempty (M ≃ₘ⟮I, K⟯ P) := sorry

end DiffeomorphicRelation
