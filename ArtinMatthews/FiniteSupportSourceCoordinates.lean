module

public import ArtinMatthews.FiniteSupportChoiceProduct


set_option backward.privateInPublic true
@[expose] public section

/-! The exact source index is one Boolean prime exponent and three
unrestricted nonnegative prime exponents. No disjointness is imposed. -/
namespace ArtinMatthews.SourceEuler
open scoped Classical
noncomputable section
variable (P : Type)

abbrev SourceCoordinates :=
  {c : P →₀ ℕ // ∀ p, c p ≤ 1} × (P →₀ ℕ) × (P →₀ ℕ) × (P →₀ ℕ)

def sourceCoordinateEquiv : (P →₀ Fin 2 × ℕ × ℕ × ℕ) ≃ SourceCoordinates P :=
  finsuppPairEquiv.trans (Equiv.prodCongr finsuppFinTwoEquiv
    (finsuppPairEquiv.trans (Equiv.prodCongr (Equiv.refl _) finsuppPairEquiv)))

theorem sourceCoordinateEquiv_apply (a : P →₀ Fin 2 × ℕ × ℕ × ℕ) (p : P) :
    ((sourceCoordinateEquiv P a).1.val p,
      (sourceCoordinateEquiv P a).2.1 p,
      (sourceCoordinateEquiv P a).2.2.1 p,
      (sourceCoordinateEquiv P a).2.2.2 p) =
        ((a p).1.val, (a p).2.1, (a p).2.2.1, (a p).2.2.2) := rfl

theorem sourceCoordinateEquiv_symm_apply (a : SourceCoordinates P) (p : P) :
    ((sourceCoordinateEquiv P).symm a p).1.val = a.1.val p ∧
    ((sourceCoordinateEquiv P).symm a p).2.1 = a.2.1 p ∧
    ((sourceCoordinateEquiv P).symm a p).2.2.1 = a.2.2.1 p ∧
    ((sourceCoordinateEquiv P).symm a p).2.2.2 = a.2.2.2 p :=
  ⟨rfl, rfl, rfl, rfl⟩

end
end ArtinMatthews.SourceEuler
