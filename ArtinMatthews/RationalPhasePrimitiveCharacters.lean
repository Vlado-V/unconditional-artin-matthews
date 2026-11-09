module

public import ArtinMatthews.RationalPhaseCharacters
public import ArtinMatthews.DirichletPrimitiveExpansion


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {r Q : ℕ} [NeZero r]

def rationalPhasePrimitiveCoefficient (hQr : r ≤ Q) (u : ℤ)
    (ψ : IdealPrimitiveCharacters Q) : ℂ :=
  dirichletPrimitiveCoefficient hQr (rationalPhaseCharacterCoefficient r u) ψ

theorem rationalPhasePrimitiveCoefficient_l1_le (hQr : r ≤ Q) (u : ℤ) :
    (∑ ψ : IdealPrimitiveCharacters Q, ‖rationalPhasePrimitiveCoefficient hQr u ψ‖) ≤
      Real.sqrt (r.totient : ℝ) :=
  (dirichletPrimitiveCoefficient_l1_le hQr _).trans
    (rationalPhaseCharacterCoefficient_l1_le r u)

theorem rationalPhase_bilinear_primitive_sum (hQr : r ≤ Q) (u : ℤ)
    (n m : ℕ) (hn : n.Coprime r) (hm : m.Coprime r) :
    (Real.fourierChar ((u : ℝ) * (n : ℝ) * (m : ℝ) / (r : ℝ)) : ℂ) =
      ∑ ψ : IdealPrimitiveCharacters Q,
        rationalPhasePrimitiveCoefficient hQr u ψ *
          idealPrimitiveCharacterValue ψ n * idealPrimitiveCharacterValue ψ m := by
  rw [rationalPhase_bilinear_character_sum r u n m hn hm]
  symm
  have h := dirichletPrimitiveCoefficient_sum hQr
    (rationalPhaseCharacterCoefficient r u)
    (fun ψ => idealPrimitiveCharacterValue ψ n * idealPrimitiveCharacterValue ψ m)
  simpa only [rationalPhasePrimitiveCoefficient, mul_assoc,
    dirichletPrimitiveRepresentative_value hQr _ n hn,
    dirichletPrimitiveRepresentative_value hQr _ m hm] using h

theorem rationalPhase_primitive_expansion (hQr : r ≤ Q) (u : ℤ) :
    ∃ a : IdealPrimitiveCharacters Q → ℂ,
      (∑ ψ : IdealPrimitiveCharacters Q, ‖a ψ‖) ≤ Real.sqrt (r.totient : ℝ) ∧
      ∀ n m : ℕ, n.Coprime r → m.Coprime r →
        (Real.fourierChar ((u : ℝ) * (n : ℝ) * (m : ℝ) / (r : ℝ)) : ℂ) =
          ∑ ψ : IdealPrimitiveCharacters Q,
            a ψ * idealPrimitiveCharacterValue ψ n * idealPrimitiveCharacterValue ψ m :=
  ⟨rationalPhasePrimitiveCoefficient hQr u,
    rationalPhasePrimitiveCoefficient_l1_le hQr u,
    rationalPhase_bilinear_primitive_sum hQr u⟩

end
end ArtinMatthews
