module

public import ArtinMatthews.PositiveDensityCubicRamification
public import ArtinMatthews.CubicGaloisFourier


set_option backward.privateInPublic true
@[expose] public section

/-! The trace at a genuine unramified split rational prime, with the
discriminant exclusion retained in the definition. -/

noncomputable section
namespace ArtinMatthews

open scoped BigOperators
attribute [local instance] Classical.propDecidable

def giantCubicTraceAtPrime (S : Finset ℤ)
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) (p : ℕ) : ℂ := by
  classical
  exact if hp : p.Prime then
    if hp₃ : p % 3 = 1 then
      if p ∉ giantCubicRamifiedPrimes S then
        let D := Classical.choice (exists_integralFrobeniusData (integerCubicField S) hp)
        cubicTrace (χ (Additive.ofMul (@relativeCubicFrobenius S p ⟨hp⟩ D hp₃)))
      else 0
    else 0
  else 0

theorem giantCubicFrobeniusSelection_trace_expansion {S : Finset ℤ} {p : ℕ}
    (hp : p.Prime) (hp₃ : p % 3 = 1) (ha₀ : ∀ a ∈ S, (a : ZMod p) ≠ 0)
    (hgood : p ∉ giantCubicRamifiedPrimes S) :
    (if giantCubicFrobeniusSelection S p then (1 : ℂ) else 0) =
      (cubicConditionDensity S : ℂ) +
        ∑ χ ∈ characterPairReps (H := Additive (integerCubicGaloisGroup S)),
          ((indicatorFourierCoeff (cubicConditionFinset S) χ).re : ℂ) *
            giantCubicTraceAtPrime S χ p := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let D := Classical.choice (exists_integralFrobeniusData (integerCubicField S) hp)
  have hgate : giantCubicFrobeniusSelection S p ↔ ∀ a ∈ S, ¬ IsCubeMod p a :=
    (giantCubicFrobeniusSelection_iff hp hp₃ ha₀).trans (by simp [giantCubicSieveSelection, hgood])
  have h := cubicFrobenius_indicator_trace_expansion D hp₃ ha₀
  have hconst : (cubicConditionDensity S : ℂ) =
      ((cubicConditionFinset S).card : ℂ) / Fintype.card (Additive (integerCubicGaloisGroup S)) := by
    push_cast [cubicConditionDensity]
    rw [Fintype.card_additive]
  simpa only [hgate, hconst, giantCubicTraceAtPrime, dite_eq_left hp, dite_eq_left hp₃,
    ite_eq_left hgood, D] using h

end ArtinMatthews
