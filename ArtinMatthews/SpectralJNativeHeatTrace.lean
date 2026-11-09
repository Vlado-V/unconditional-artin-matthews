module

public import ArtinMatthews.SpectralForwardNativeTrace
public import ArtinMatthews.SpectralJRegularizedHeat
public import ArtinMatthews.SpectralABLOrderMultiplier


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Complex
open scoped MatrixGroups ContDiff ComplexConjugate
noncomputable section

private theorem regularized_order
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioi (0 : ℝ)) (L : ℝ) (hL : 0 ≤ L) (l : Ici (0 : ℝ)) :
    spectralJRegularizedWeight f L
      (-Complex.I * Complex.sqrt (1 / 4 - ((l : ℝ) : ℂ))) =
        spectralJRegularizedEnergyTest f hf hc hs L hL l := by
  rw [spectralJRegularizedEnergyTest_apply]
  exact (spectralEven_eq_of_square_eq _ (spectralJRegularizedWeight_even f L) _ _
    (spectralSourceParameter_order_square l)).symm

theorem gamma0JHeatSource_inequivalent_physical
    (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (hneq : ¬ gamma0EisensteinCuspsEquivalent N r s)
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioi (0 : ℝ)) (hreal : ∀ x : ℝ, conj (f x) = f x)
    (L R : ℝ) (hL : 0 ≤ L) (hR : 0 < R) :
    gamma0HeatSourceSpectralSide N (spectralJRegularizedEnergyTest f hf hc hs L hL)
      r s Y hY m n hm hn R =
      (1 / 4 : ℂ) * ∑' c : Ioi (0 : ℕ), gamma0TrueWidthPhysicalFibre N r s c m n
        (spectralKLWeightedHeatProfile (spectralJRegularizedWeight f L) R)
        (spectralKLHeatProfile R) := by
  exact gamma0HeatSource_inequivalent_physical N r s hneq Y hY m n hm hn R hR _
    (spectralJRegularizedHeatProfile_properties f hf hc hs L R hL hR)
    (spectralKLWeightedHeatProfile_nonpositive_zero _ R)
    (spectralJRegularizedHeatProfile_real f hf.continuous hc hs hreal L R)
    _ _ (spectralJRegularizedEnergyTest_real f hf hc hs hreal L hL)
    (regularized_order f hf hc hs L hL)
    (fun t => (spectralJRegularizedEnergyTest_continuous_symbol f hf hc hs L hL t).symm)
    (spectralJRegularizedHeatProfile_continued_transform f hf hc hs L R hL hR)

theorem gamma0JHeatSource_sameCusp_physical
    (N : ℕ) [NeZero N] (r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioi (0 : ℝ)) (hreal : ∀ x : ℝ, conj (f x) = f x)
    (L R : ℝ) (hL : 0 ≤ L) (hR : 0 < R) :
    let G := spectralKLWeightedHeatProfile (spectralJRegularizedWeight f L) R
    let F := spectralKLHeatProfile R
    gamma0HeatSourceSpectralSide N (spectralJRegularizedEnergyTest f hf hc hs L hL)
      r r Y hY m n hm hn R =
      (1 / 4 : ℂ) * ((if m = n then (gamma0CuspTrueWidth N r : ℂ) *
        (cuspFourierHeightPairing
          (fun y => Real.sqrt (y / (gamma0CuspTrueWidth N r : ℝ)) *
            (F ((|cuspFourierFrequency 1 m| / (gamma0CuspTrueWidth N r : ℝ)) * y)).re)
          (fun y => Real.sqrt (y / (gamma0CuspTrueWidth N r : ℝ)) *
            (G ((|cuspFourierFrequency 1 n| / (gamma0CuspTrueWidth N r : ℝ)) * y)).re) : ℂ)
        else 0) +
        ∑' c : Ioi (0 : ℕ), gamma0TrueWidthPhysicalFibre N r r c m n G F) := by
  dsimp only
  exact gamma0HeatSource_sameCusp_physical N r Y hY m n hm hn R hR _
    (spectralJRegularizedHeatProfile_properties f hf hc hs L R hL hR)
    (spectralKLWeightedHeatProfile_nonpositive_zero _ R)
    (spectralJRegularizedHeatProfile_real f hf.continuous hc hs hreal L R)
    _ _ (spectralJRegularizedEnergyTest_real f hf hc hs hreal L hL)
    (regularized_order f hf hc hs L hL)
    (fun t => (spectralJRegularizedEnergyTest_continuous_symbol f hf hc hs L hL t).symm)
    (spectralJRegularizedHeatProfile_continued_transform f hf hc hs L R hL hR)

end
end ArtinMatthews
