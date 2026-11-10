module

public import ArtinMatthews.SourceTraceFourierDecay
public import ArtinMatthews.SourceComplexProductFourier
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory
open scoped SchwartzMap FourierTransform BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem source_complex_product_one_add_norm (y : ι → ℂ) :
    1 + ‖y‖ ≤ ∏ i, (1 + ‖y i‖) := by
  have hp : 1 ≤ ∏ i, (1 + ‖y i‖) := Finset.one_le_prod₀ (fun i _ => le_add_of_nonneg_right (norm_nonneg _))
  have hnorm : ‖y‖ ≤ (∏ i, (1 + ‖y i‖)) - 1 := by
    apply (pi_norm_le_iff_of_nonneg (sub_nonneg.mpr hp)).mpr
    intro i
    have hi := Finset.le_prod_max_one (Finset.mem_univ i) (fun j => 1 + ‖y j‖)
    have hs (j : ι) : max (1 + ‖y j‖) 1 = 1 + ‖y j‖ := max_eq_left (le_add_of_nonneg_right (norm_nonneg _))
    simp only [hs] at hi
    linarith
  linarith

theorem source_complex_product_fourier_rapid_decay
    (f : ι → 𝓢(ℂ, ℂ)) (n : ℕ) (y : ι → ℂ) :
    (1 + ‖y‖) ^ n *
      ‖sourceComplexProductFourier (fun x : ι → ℂ => ∏ i, f i (x i)) y‖ ≤
        ∏ i, sourceComplexTraceDecayConstant (f i) n := by
  rw [source_complex_product_fourier_tensor, norm_prod]
  calc
    _ ≤ (∏ i, (1 + ‖y i‖)) ^ n * ∏ i, ‖sourceComplexTraceFourier (f i) (y i)‖ := by
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (source_complex_product_one_add_norm y) n)
          (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    _ = ∏ i, (1 + ‖y i‖) ^ n * ‖sourceComplexTraceFourier (f i) (y i)‖ := by
      rw [← Finset.prod_pow, Finset.prod_mul_distrib]
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => by positivity)
      (fun i _ => source_complex_trace_fourier_rapid_decay (f i) n (y i))

def sourceArchimedeanFourierDecayConstant (ι : Type*) [Fintype ι] (n : ℕ) : ℝ :=
  sourceComplexTraceDecayConstant sourceAnnularSchwartzTest n ^ Fintype.card ι

theorem sourceComplexProductTest_fourier_rapid_decay (n : ℕ) (y : ι → ℂ) :
    (1 + ‖y‖) ^ n * ‖sourceComplexProductFourier sourceComplexProductTest y‖ ≤
      sourceArchimedeanFourierDecayConstant ι n := by
  change (1 + ‖y‖) ^ n * ‖sourceComplexProductFourier
    (fun x : ι → ℂ => ∏ i, sourceAnnularSchwartzTest (x i)) y‖ ≤ _
  simpa only [sourceArchimedeanFourierDecayConstant,
    Finset.prod_const, Finset.card_univ] using
      source_complex_product_fourier_rapid_decay (fun _ : ι => sourceAnnularSchwartzTest) n y

theorem sourceComplexProductTest_fourier_decay (n : ℕ) (y : ι → ℂ) :
    ‖sourceComplexProductFourier sourceComplexProductTest y‖ ≤
      sourceArchimedeanFourierDecayConstant ι n / (1 + ‖y‖) ^ n := by
  apply (le_div_iff₀ (pow_pos (by positivity) _)).mpr
  simpa only [mul_comm] using sourceComplexProductTest_fourier_rapid_decay n y

end
end ArtinMatthews.VaryingKummerAnalytic
