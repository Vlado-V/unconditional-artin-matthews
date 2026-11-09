module

public import ArtinMatthews.SpectralHeatCuspidalSplit
public import ArtinMatthews.SpectralGaussianTsumLimit


set_option backward.privateInPublic true
@[expose] public section

/-! The principal diagonal bounds control the actual bare cuspidal
series. The finite complementary terms retain their full heat factors. -/
namespace ArtinMatthews

open Filter
open scoped MatrixGroups BigOperators Topology

noncomputable section

theorem spectralHeatEnergyWeight_nat_add_one_eq_gaussian (k : ℕ) (eig : ℝ) :
    spectralHeatEnergyWeight ((k : ℝ) + 1) eig =
      (spectralGaussianCutoff k (2 * (eig - 1 / 4)) : ℂ) := by
  rw [spectralHeatEnergyWeight_real, spectralGaussianCutoff,
    show 2 * (1 / 4 - eig) = -(2 * (eig - 1 / 4)) by ring]

theorem gamma0HeatPrincipalCuspidalDiagonal_limit (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m : ℤ) (hm : m ≠ 0)
    (hpos : ∀ i : Gamma0HeatPrincipalCuspidalIndex N,
      ‖gamma0CuspidalTestSymbol N h i.val‖ = (gamma0CuspidalTestSymbol N h i.val).re)
    (C : ℝ) (hC : ∀ k : ℕ,
      gamma0HeatPrincipalCuspidalDiagonal N h r Y hY m hm ((k : ℝ) + 1) ≤ C) :
    Summable (fun i : Gamma0HeatPrincipalCuspidalIndex N =>
      gamma0BareCuspidalDiagonalDensity N h r Y hY m hm i.val) ∧
    (∑' i : Gamma0HeatPrincipalCuspidalIndex N,
      gamma0BareCuspidalDiagonalDensity N h r Y hY m hm i.val) ≤ C ∧
    Tendsto (fun k : ℕ => gamma0HeatPrincipalCuspidalDiagonal N h r Y hY m hm ((k : ℝ) + 1))
      atTop (𝓝 (∑' i : Gamma0HeatPrincipalCuspidalIndex N,
        gamma0BareCuspidalDiagonalDensity N h r Y hY m hm i.val)) := by
  let D (i : Gamma0HeatPrincipalCuspidalIndex N) := gamma0BareCuspidalDiagonalDensity N h r Y hY m hm i.val
  let τ (i : Gamma0HeatPrincipalCuspidalIndex N) := 2 * (gamma0AllHeightGradientSpectralValue N i.val - 1 / 4)
  have hD0 (i : Gamma0HeatPrincipalCuspidalIndex N) : 0 ≤ D i := by
    dsimp only [D, gamma0BareCuspidalDiagonalDensity]
    rw [← hpos i]
    exact mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hτ0 (i : Gamma0HeatPrincipalCuspidalIndex N) : 0 ≤ τ i :=
    mul_nonneg (by norm_num) (sub_nonneg.mpr i.property)
  have hS (k : ℕ) : Summable (fun i : Gamma0HeatPrincipalCuspidalIndex N =>
      gamma0HeatCuspidalTerm N h r r Y hY m m hm hm ((k : ℝ) + 1) i.val) :=
    (gamma0HeatCuspidalTerm_summable N h r r Y hY m m hm hm ((k : ℝ) + 1) (by positivity)).subtype _
  have hterm (k : ℕ) (i : Gamma0HeatPrincipalCuspidalIndex N) :
      (gamma0HeatCuspidalTerm N h r r Y hY m m hm hm ((k : ℝ) + 1) i.val).re =
        D i * spectralGaussianCutoff k (τ i) := by
    simpa only [D, τ, spectralHeatEnergyWeight_nat_add_one_eq_gaussian, Complex.ofReal_re] using
      gamma0HeatCuspidalTerm_diagonal_re N h r Y hY m hm ((k : ℝ) + 1) i.val
  have hSreal (k : ℕ) : Summable (fun i => D i * spectralGaussianCutoff k (τ i)) :=
    (Complex.hasSum_re (hS k).hasSum).summable.congr (hterm k)
  have hsum (k : ℕ) : gamma0HeatPrincipalCuspidalDiagonal N h r Y hY m hm ((k : ℝ) + 1) =
      ∑' i, D i * spectralGaussianCutoff k (τ i) := by
    unfold gamma0HeatPrincipalCuspidalDiagonal
    rw [Complex.re_tsum (hS k)]
    exact tsum_congr (hterm k)
  have hbound (k : ℕ) : (∑' i, D i * spectralGaussianCutoff k (τ i)) ≤ C :=
    (hsum k).symm.le.trans (hC k)
  obtain ⟨hsummable, hle, hlimit⟩ := spectralGaussianCutoff_tsum_monotone_limit
    D τ hD0 hτ0 C hSreal hbound
  exact ⟨hsummable, hle, by simpa only [hsum] using hlimit⟩

theorem gamma0BareCuspidalTerm_norm_le_diagonals (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (i : Gamma0HeatPrincipalCuspidalIndex N)
    (hpos : ‖gamma0CuspidalTestSymbol N h i.val‖ = (gamma0CuspidalTestSymbol N h i.val).re) :
    ‖gamma0BareCuspidalTerm N h r s Y hY m n hm hn i.val‖ ≤
      (gamma0BareCuspidalDiagonalDensity N h r Y hY m hm i.val +
        gamma0BareCuspidalDiagonalDensity N h s Y hY n hn i.val) / 2 := by
  let z := gamma0CuspidalTestSymbol N h i.val
  let a := gamma0BareCuspidalAmplitude N i.val r Y hY m hm
  let b := gamma0BareCuspidalAmplitude N i.val s Y hY n hn
  change ‖z‖ = z.re at hpos
  have hz : 0 ≤ z.re := hpos ▸ norm_nonneg z
  have hstar : ‖star b‖ = ‖b‖ := by
    simpa only [Complex.star_def] using Complex.norm_conj b
  change ‖z * (a * star b)‖ ≤ (z.re * ‖a‖ ^ 2 + z.re * ‖b‖ ^ 2) / 2
  rw [norm_mul, norm_mul, hstar, hpos]
  have hab : ‖a‖ * ‖b‖ ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  calc
    _ ≤ z.re * ((‖a‖ ^ 2 + ‖b‖ ^ 2) / 2) := mul_le_mul_of_nonneg_left hab hz
    _ = _ := by ring

theorem gamma0HeatCuspidal_tendsto_bare (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hpos : ∀ i : Gamma0HeatPrincipalCuspidalIndex N,
      ‖gamma0CuspidalTestSymbol N h i.val‖ = (gamma0CuspidalTestSymbol N h i.val).re)
    (Cr Cs : ℝ)
    (hr : ∀ k : ℕ, gamma0HeatPrincipalCuspidalDiagonal N h r Y hY m hm ((k : ℝ) + 1) ≤ Cr)
    (hs : ∀ k : ℕ, gamma0HeatPrincipalCuspidalDiagonal N h s Y hY n hn ((k : ℝ) + 1) ≤ Cs) :
    Summable (gamma0BareCuspidalTerm N h r s Y hY m n hm hn) ∧
    Summable (fun i => ‖gamma0BareCuspidalTerm N h r s Y hY m n hm hn i‖) ∧
    Tendsto (fun k : ℕ => ∑' i, gamma0HeatCuspidalTerm N h r s Y hY m n hm hn ((k : ℝ) + 1) i)
      atTop (𝓝 (∑' i, gamma0BareCuspidalTerm N h r s Y hY m n hm hn i)) := by
  let F := gamma0BareCuspidalTerm N h r s Y hY m n hm hn
  have hDr := (gamma0HeatPrincipalCuspidalDiagonal_limit N h r Y hY m hm hpos Cr hr).1
  have hDs := (gamma0HeatPrincipalCuspidalDiagonal_limit N h s Y hY n hn hpos Cs hs).1
  have hprincipal : Summable (fun i : Gamma0HeatPrincipalCuspidalIndex N => ‖F i.val‖) :=
    ((hDr.add hDs).div_const 2).of_nonneg_of_le (fun _ => norm_nonneg _) (fun i =>
      gamma0BareCuspidalTerm_norm_le_diagonals N h r s Y hY m n hm hn i (hpos i))
  have hsum : Summable (fun i => ‖F i‖) :=
    gamma0HeatCuspidal_summable_of_principal N _ hprincipal
  refine ⟨hsum.of_norm, hsum, ?_⟩
  apply tendsto_tsum_of_dominated_convergence (hsum.mul_left (Real.exp (1 / 2 : ℝ)))
  · intro i
    have hw := (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp
      (spectralGaussianCutoff_tendsto (2 * (gamma0AllHeightGradientSpectralValue N i - 1 / 4)))
    have hweight : Tendsto (fun k : ℕ =>
        spectralHeatEnergyWeight ((k : ℝ) + 1) (gamma0AllHeightGradientSpectralValue N i)) atTop (𝓝 1) := by
      simpa only [spectralHeatEnergyWeight_nat_add_one_eq_gaussian, Function.comp_def,
        Complex.ofReal_one] using hw
    simpa only [gamma0HeatCuspidalTerm, mul_one, F] using hweight.const_mul (F i)
  · exact Eventually.of_forall fun k i =>
      gamma0HeatCuspidalTerm_norm_le N h r s Y hY m n hm hn
        (le_add_of_nonneg_left (Nat.cast_nonneg k)) i

end
end ArtinMatthews
