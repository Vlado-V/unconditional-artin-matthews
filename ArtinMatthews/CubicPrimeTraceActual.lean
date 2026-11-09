module

public import ArtinMatthews.CubicSamplingActualProposition61
public import ArtinMatthews.CubicSievePrimeTraceMean


set_option backward.privateInPublic true
@[expose] public section

/-! Each nontrivial Frobenius trace has zero normalized mean on the
actual candidate progression. Its supported cubic numerator uses the
constructed bilinear estimate. -/

noncomputable section
namespace ArtinMatthews

open Filter Set MeasureTheory OAI
open scoped ContDiff Topology

theorem cubicSieve_actual_trace_mean {S : Finset ℤ} (hS : AdmissibleBases S)
    {M : ℕ} [NeZero M] (h₃ : 3 ∣ M) (U : Finset (ZMod M)ˣ)
    (hU₃ : ∀ v ∈ U, ZMod.castHom h₃ (ZMod 3) (v : ZMod M) = 1)
    {ε T : ℝ} (hε : 0 < ε) (hεq : ε < 1/4) (hT₁ : 1 < T) (hT₂ : T < 2)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦ₀ : ∀ t, 0 ≤ Φ t) (hΦ₁ : ∀ t, ‖Φ t‖ ≤ 1)
    (hs : Function.support Φ ⊆ Ioo 1 T)
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ)
    (hχ : χ ∈ characterPairReps (H := Additive (integerCubicGaloisGroup S))) :
    Tendsto (fun x : ℝ => ((Real.log x/x : ℝ) : ℂ)*giantCubicTracePrimeTest U S χ ε Φ T x)
      atTop (𝓝 0) := by
  have hs₂ : Function.support Φ ⊆ Icc (1 : ℝ) 2 :=
    hs.trans fun _ ht => ⟨ht.1.le,(ht.2.trans hT₂).le⟩
  exact cubicSieve_actual_trace_source_mean hS h₃ U hU₃ hε hεq hT₁ hT₂ Φ hΦ hΦ₀ hΦ₁ hs
    (fun A hA _ hnoncube => cubicNumerator_shiftedBilinearBound_eventually A hA hnoncube
      Φ hΦ hs₂ (div_pos hε (by norm_num))) χ hχ

theorem giantCubicFrobenius_mean_of_ordinary_mean {S : Finset ℤ} (hS : AdmissibleBases S)
    {M : ℕ} [NeZero M] (h₃ : 3 ∣ M) (U : Finset (ZMod M)ˣ)
    (hU₃ : ∀ v ∈ U, ZMod.castHom h₃ (ZMod 3) (v : ZMod M) = 1)
    {ε T : ℝ} (hε : 0 < ε) (hεq : ε < 1/4) (hT₁ : 1 < T) (hT₂ : T < 2)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦrange : ∀ t, 0 ≤ Φ t ∧ Φ t ≤ 1)
    (hs : Function.support Φ ⊆ Ioo 1 T)
    (hordinary : Tendsto (fun x : ℝ => ((Real.log x/x : ℝ) : ℂ)*
      giantUncenteredPrimeTest U ε Φ T x) atTop
      (𝓝 (((U.card : ℝ)/Nat.totient M*(giantPrimeConstant ε*∫ t : ℝ, Φ t) : ℝ) : ℂ))) :
    Tendsto (fun x : ℝ => ((Real.log x/x : ℝ) : ℂ)*
      giantSelectedPrimeTest U (giantCubicFrobeniusSelection S) ε Φ T x) atTop
      (𝓝 (((U.card : ℝ)/Nat.totient M*
        (cubicConditionDensity S*(giantPrimeConstant ε*∫ t : ℝ, Φ t)) : ℝ) : ℂ)) := by
  have hΦ₀ (t : ℝ) : 0 ≤ Φ t := (hΦrange t).1
  have hΦ₁ (t : ℝ) : ‖Φ t‖ ≤ 1 := by
    simpa only [Real.norm_of_nonneg (hΦ₀ t)] using (hΦrange t).2
  exact giantCubicFrobenius_mean_of_trace_limits hS h₃ U hU₃ ε Φ hΦrange hT₁ hT₂ hs
    hordinary (fun χ hχ => cubicSieve_actual_trace_mean hS h₃ U hU₃ hε hεq hT₁ hT₂
      Φ hΦ hΦ₀ hΦ₁ hs χ hχ)

end ArtinMatthews
