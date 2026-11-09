module

public import ArtinMatthews.SpectralJNativeHeatTrace
public import ArtinMatthews.SpectralJNativeHeatKernel


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set Complex
open scoped MatrixGroups ContDiff ComplexConjugate
noncomputable section

theorem gamma0JHeatSource_inequivalent_trace
    (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (hneq : ¬ gamma0EisensteinCuspsEquivalent N r s)
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : 0 < m * n)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (hreal : ∀ x : ℝ, conj (f x) = f x)
    (L R : ℝ) (hL : 0 ≤ L) (hR : 0 < R) :
    gamma0HeatSourceSpectralSide N (spectralJRegularizedEnergyTest f hf hc hp L hL)
      r s Y hY m n hm hn R =
      (1 / 4 : ℂ) * ∑' c : Ioi (0 : ℕ),
        gamma0TrueWidthHeatFibre N r s c m n (spectralJRegularizedWeight f L) R := by
  rw [gamma0JHeatSource_inequivalent_physical N r s hneq Y hY m n hm hn
    f hf hc hp hreal L R hL hR]
  congr 1
  exact tsum_congr (fun c =>
    gamma0TrueWidthJRegularizedHeatFibre N r s c m n hm hn hmn f hf hc hp L R hL hR)

theorem gamma0JHeatSource_sameCusp_trace
    (N : ℕ) [NeZero N] (r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : 0 < m * n)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (hreal : ∀ x : ℝ, conj (f x) = f x)
    (L R : ℝ) (hL : 0 ≤ L) (hR : 0 < R) :
    gamma0HeatSourceSpectralSide N (spectralJRegularizedEnergyTest f hf hc hp L hL)
      r r Y hY m n hm hn R =
      (1 / 4 : ℂ) *
        ((if m = n then spectralABLHeatDiagonal (spectralJRegularizedWeight f L) R else 0) +
        ∑' c : Ioi (0 : ℕ),
          gamma0TrueWidthHeatFibre N r r c m n (spectralJRegularizedWeight f L) R) := by
  have he := gamma0JHeatSource_sameCusp_physical N r Y hY m n hm hn
    f hf hc hp hreal L R hL hR
  dsimp only at he
  have hsum : (∑' c : Ioi (0 : ℕ), gamma0TrueWidthPhysicalFibre N r r c m n
      (spectralKLWeightedHeatProfile (spectralJRegularizedWeight f L) R)
      (spectralKLHeatProfile R)) =
      ∑' c : Ioi (0 : ℕ), gamma0TrueWidthHeatFibre N r r c m n
        (spectralJRegularizedWeight f L) R := tsum_congr (fun c =>
    gamma0TrueWidthJRegularizedHeatFibre N r r c m n hm hn hmn f hf hc hp L R hL hR)
  rw [hsum] at he
  by_cases hmnEq : m = n
  · subst n
    simpa only [ite_eq_left (rfl : m = m),
      gamma0JHeat_diagonal N r m hm f hf hc hp hreal L R hL hR] using he
  · simpa only [ite_eq_right hmnEq] using he

end
end ArtinMatthews
