import stacks_proof.stacks_project.Chap10.Definition_10_50_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]

local notation "Γ" => (ValuationRing.ValueGroup A (FractionRing A))ˣ

/- Lemma 10.50.12: the value group from Definition 10.50.13, namely `Γ = Kˣ / Aˣ`, is a totally
ordered abelian group. The owner object is the with-zero value group
`ValuationRing.ValueGroup A (FractionRing A)`; the source-facing ordered abelian group structure
on `Γ` is given by the canonical owner-derived instances on units. -/
#check (inferInstance : CommGroup Γ)
#check (inferInstance : LinearOrder Γ)
#check (inferInstance : IsOrderedMonoid Γ)

end
