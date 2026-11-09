module

public import ArtinMatthews.PositiveDensityCubicTraceSum


set_option backward.privateInPublic true
@[expose] public section

/-! The actual cubic Frobenius mean follows from the ordinary mean and
the normalized limits of the finitely many nontrivial trace statistics. -/

noncomputable section
namespace ArtinMatthews

open Filter MeasureTheory
open scoped BigOperators Topology

theorem giantCubicFrobenius_mean_of_trace_limits {S : Finset ℤ}
    (hS : AdmissibleBases S) {M : ℕ} (h₃ : 3 ∣ M) (U : Finset (ZMod M)ˣ)
    (hU₃ : ∀ v ∈ U, ZMod.castHom h₃ (ZMod 3) (v : ZMod M) = 1)
    (ε : ℝ) (Φ : ℝ → ℝ) (hΦ : ∀ t, 0 ≤ Φ t ∧ Φ t ≤ 1)
    {T : ℝ} (hT₁ : 1 < T) (hT₂ : T < 2) (hs : Function.support Φ ⊆ Set.Ioo 1 T)
    (hordinary : Tendsto (fun x : ℝ => ((Real.log x / x : ℝ) : ℂ) *
      giantUncenteredPrimeTest U ε Φ T x) atTop
      (𝓝 (((U.card : ℝ) / Nat.totient M *
        (giantPrimeConstant ε * ∫ t : ℝ, Φ t) : ℝ) : ℂ)))
    (htrace : ∀ χ ∈ characterPairReps (H := Additive (integerCubicGaloisGroup S)),
      Tendsto (fun x : ℝ => ((Real.log x / x : ℝ) : ℂ) *
        giantCubicTracePrimeTest U S χ ε Φ T x) atTop (𝓝 0)) :
    Tendsto (fun x : ℝ => ((Real.log x / x : ℝ) : ℂ) *
      giantSelectedPrimeTest U (giantCubicFrobeniusSelection S) ε Φ T x) atTop
      (𝓝 (((U.card : ℝ) / Nat.totient M *
        (cubicConditionDensity S * (giantPrimeConstant ε * ∫ t : ℝ, Φ t)) : ℝ) : ℂ)) := by
  let R := characterPairReps (H := Additive (integerCubicGaloisGroup S))
  let c (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) : ℂ :=
    ((indicatorFourierCoeff (cubicConditionFinset S) χ).re : ℂ)
  let scale (x : ℝ) : ℂ := ((Real.log x / x : ℝ) : ℂ)
  let d := (cubicConditionDensity S : ℂ)
  let κ := (U.card : ℝ) / Nat.totient M * (giantPrimeConstant ε * ∫ t : ℝ, Φ t)
  have htraceSum : Tendsto (fun x : ℝ =>
      ∑ χ ∈ R, c χ * (scale x * giantCubicTracePrimeTest U S χ ε Φ T x)) atTop (𝓝 0) := by
    have h := tendsto_finsetSum R (fun χ hχ =>
      (tendsto_const_nhds (x := c χ)).mul (htrace χ hχ))
    simpa only [mul_zero, Finset.sum_const_zero] using h
  have hmain : Tendsto (fun x : ℝ => d * (scale x * giantUncenteredPrimeTest U ε Φ T x))
      atTop (𝓝 (d * (κ : ℂ))) :=
    tendsto_const_nhds.mul hordinary
  have hlim := hmain.add htraceSum
  have hconstant : d * (κ : ℂ) + 0 =
      (((U.card : ℝ) / Nat.totient M *
        (cubicConditionDensity S * (giantPrimeConstant ε * ∫ t : ℝ, Φ t)) : ℝ) : ℂ) := by
    simp only [add_zero, d, κ]
    push_cast
    ring
  rw [hconstant] at hlim
  apply hlim.congr'
  filter_upwards [giantSelectedPrimeTest_cubic_trace_expansion_eventually hS h₃ U hU₃
    ε Φ hΦ hT₁ hT₂ hs] with x hx
  change d * (scale x * giantUncenteredPrimeTest U ε Φ T x) +
      (∑ χ ∈ R, c χ * (scale x * giantCubicTracePrimeTest U S χ ε Φ T x)) =
    scale x * giantSelectedPrimeTest U (giantCubicFrobeniusSelection S) ε Φ T x
  rw [hx, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro χ _hχ
    change c χ * (scale x * giantCubicTracePrimeTest U S χ ε Φ T x) =
      scale x * (c χ * giantCubicTracePrimeTest U S χ ε Φ T x)
    ring

end ArtinMatthews
