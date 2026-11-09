module

public import ArtinMatthews.SpectralABLBareKernel
public import Mathlib.Analysis.Normed.Group.Tannery


set_option backward.privateInPublic true
@[expose] public section

/-! The actual true-width modulus sum admits Gaussian removal from a
uniform positive-power kernel bound. The majorant uses the proved
reduced-matrix count and retains the exact cusp widths. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups Topology
namespace ArtinMatthews

def gamma0TrueWidthBareFibre (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (c : Ioi (0 : ℕ)) (m n : ℤ) (H : ℂ → ℂ) : ℂ :=
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  let a := |cuspFourierFrequency 1 m|
  let b := |cuspFourierFrequency 1 n|
  let C := gamma0TrueWidthModulus N r s (c.val : ℝ)
  gamma0TrueWidthKloostermanSum N r s c.val m n*((Real.sqrt (a*b)/C^2 : ℝ) : ℂ)*
    spectralABLBareKernel H m n (Real.sqrt (a*b)*(2/C))

theorem gamma0TrueWidthHeatFibre_tendsto_bare (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (c : Ioi (0 : ℕ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (H : ℂ → ℂ)
    (hH : Integrable (fun t : ℝ => H (t : ℂ)) spectralKLSpectralMeasure) :
    Tendsto (fun R : ℝ => gamma0TrueWidthHeatFibre N r s c m n H R) atTop
      (𝓝 (gamma0TrueWidthBareFibre N r s c m n H)) := by
  have ha := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one m hm)
  have hb := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)
  have hC := gamma0TrueWidthModulus_pos N r s (Nat.cast_pos.mpr c.property)
  have hX : 0 < Real.sqrt (|cuspFourierFrequency 1 m| * |cuspFourierFrequency 1 n|)*
      (2/gamma0TrueWidthModulus N r s (c.val : ℝ)) := by positivity
  exact tendsto_const_nhds.mul (spectralABLHeatKernel_tendsto_bare H hH m n hX)

theorem gamma0TrueWidthHeatFibre_uniform_bare_bound (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (H : ℂ → ℂ)
    (hK : ∀ X₀ : ℝ, 0 < X₀ → ∃ D : ℝ, 0 ≤ D ∧
      ∀ R : ℝ, 1 ≤ R → ∀ X : ℝ, 0 < X → X ≤ X₀ →
        ‖spectralABLHeatKernel H R m n X‖ ≤ D*X^(1/4 : ℝ)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ R : ℝ, 1 ≤ R → ∀ c : Ioi (0 : ℕ),
      ‖gamma0TrueWidthHeatFibre N r s c m n H R‖ ≤ L/(c.val : ℝ)^(5/4 : ℝ) := by
  let a := |cuspFourierFrequency 1 m|
  let b := |cuspFourierFrequency 1 n|
  let K := Real.sqrt (a*b)
  let W := Real.sqrt (gamma0CuspTrueWidth N r : ℝ)*Real.sqrt (gamma0CuspTrueWidth N s : ℝ)
  have ha : 0 < a := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one m hm)
  have hb : 0 < b := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)
  have hKpos : 0 < K := Real.sqrt_pos.mpr (mul_pos ha hb)
  have hw₁ : 0 < (gamma0CuspTrueWidth N r : ℝ) := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have hw₂ : 0 < (gamma0CuspTrueWidth N s : ℝ) := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N s)
  have hW : 0 < W := mul_pos (Real.sqrt_pos.mpr hw₁) (Real.sqrt_pos.mpr hw₂)
  have hWsq : W^2 = (gamma0CuspTrueWidth N r : ℝ)*gamma0CuspTrueWidth N s := by
    dsimp only [W]
    rw [mul_pow,Real.sq_sqrt hw₁.le,Real.sq_sqrt hw₂.le]
  obtain ⟨D,hD,hDbd⟩ := hK (K*(2/W)) (mul_pos hKpos (div_pos two_pos hW))
  refine ⟨K*D*(2*K/W)^(1/4 : ℝ),by positivity,?_⟩
  intro R hR c
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  have hc : 0 < (c.val : ℝ) := Nat.cast_pos.mpr c.property
  have hc1 : 1 ≤ (c.val : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr c.property)
  have hC : 0 < (c.val : ℝ)*W := mul_pos hc hW
  have hX : 0 < K*(2/((c.val : ℝ)*W)) := mul_pos hKpos (div_pos two_pos hC)
  have hXle : K*(2/((c.val : ℝ)*W)) ≤ K*(2/W) := by
    apply mul_le_mul_of_nonneg_left _ hKpos.le
    apply div_le_div_of_nonneg_left two_pos.le hW
    exact le_mul_of_one_le_left hW.le hc1
  have hF := hDbd R hR _ hX hXle
  have hS : ‖gamma0TrueWidthKloostermanSum N r s c.val m n‖ ≤ W^2*(c.val : ℝ) := by
    rw [hWsq]
    exact gamma0TrueWidthKloostermanSum_linear_bound N r s c.val m n
  have hmod : gamma0TrueWidthModulus N r s (c.val : ℝ) = (c.val : ℝ)*W := by
    dsimp only [gamma0TrueWidthModulus,W]
    ring
  change ‖gamma0TrueWidthKloostermanSum N r s c.val m n*
      ((K/(gamma0TrueWidthModulus N r s (c.val : ℝ))^2 : ℝ) : ℂ)*
      spectralABLHeatKernel H R m n (K*(2/gamma0TrueWidthModulus N r s (c.val : ℝ)))‖ ≤ _
  rw [hmod,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (W^2*(c.val : ℝ))*(K/((c.val : ℝ)*W)^2)*
        (D*(K*(2/((c.val : ℝ)*W)))^(1/4 : ℝ)) := by gcongr
    _ = _ := by
      convert spectralWeyl_modulus_power_factor hc hKpos hW (5/8 : ℝ) D using 1 <;> norm_num

theorem gamma0TrueWidthHeatSeries_tendsto_bare (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (H : ℂ → ℂ)
    (hH : Integrable (fun t : ℝ => H (t : ℂ)) spectralKLSpectralMeasure)
    (hK : ∀ X₀ : ℝ, 0 < X₀ → ∃ D : ℝ, 0 ≤ D ∧
      ∀ R : ℝ, 1 ≤ R → ∀ X : ℝ, 0 < X → X ≤ X₀ →
        ‖spectralABLHeatKernel H R m n X‖ ≤ D*X^(1/4 : ℝ)) :
    Summable (fun c : Ioi (0 : ℕ) => gamma0TrueWidthBareFibre N r s c m n H) ∧
      Tendsto (fun R : ℝ => ∑' c : Ioi (0 : ℕ), gamma0TrueWidthHeatFibre N r s c m n H R) atTop
        (𝓝 (∑' c : Ioi (0 : ℕ), gamma0TrueWidthBareFibre N r s c m n H)) := by
  obtain ⟨L,_,hL⟩ := gamma0TrueWidthHeatFibre_uniform_bare_bound N r s m n hm hn H hK
  have hp : Summable (fun c : ℕ => 1/(c : ℝ)^(5/4 : ℝ)) := Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have hs := (hp.mul_left L).subtype (Ioi (0 : ℕ))
  have hS : Summable (fun c : Ioi (0 : ℕ) => L/(c.val : ℝ)^(5/4 : ℝ)) := by
    simpa only [mul_one_div,Function.comp_def] using! hs
  have hlim c := gamma0TrueWidthHeatFibre_tendsto_bare N r s c m n hm hn H hH
  have hev : ∀ᶠ R : ℝ in atTop, ∀ c : Ioi (0 : ℕ),
      ‖gamma0TrueWidthHeatFibre N r s c m n H R‖ ≤ L/(c.val : ℝ)^(5/4 : ℝ) :=
    (eventually_ge_atTop (1 : ℝ)).mono (fun R hR => hL R hR)
  refine ⟨hS.of_norm_bounded ?_,tendsto_tsum_of_dominated_convergence hS hlim hev⟩
  intro c
  exact le_of_tendsto ((continuous_norm.tendsto _).comp (hlim c)) (hev.mono fun R hR => hR c)

end ArtinMatthews
