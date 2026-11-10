module

public import ArtinMatthews.CubicThetaCoefficients
public import ArtinMatthews.CubicThetaSeries
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
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

/-! Absolute convergence and regrouping of the actual ideal-indexed theta series. -/
noncomputable section
open scoped BigOperators
open OAI.SevenEighths

namespace ArtinMatthews
open HeckeFamily

/-- Every ideal lies in precisely the finite fiber indexed by its norm. -/
def idealNormFiberEquiv : (Σ n : ℕ, ↥(idealsOfNorm n)) ≃ Ideal O where
  toFun p := p.2.1
  invFun I := ⟨I.absNorm, ⟨I, mem_idealsOfNorm.mpr rfl⟩⟩
  left_inv := by
    rintro ⟨n, I, hI⟩
    have hn := mem_idealsOfNorm.mp hI
    subst n
    rfl
  right_inv _ := rfl

/-- The contribution of a finite ideal-norm fiber is its defining coefficient. -/
theorem sum_idealNormFiber (χ : Character) (q : ℂ) (n : ℕ) :
    (∑ I ∈ idealsOfNorm n, thetaIdealCharacter χ I * q ^ I.absNorm) =
      idealThetaCoeff χ n * q ^ n := by
  simp only [idealThetaCoeff, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro I hI
  rw [mem_idealsOfNorm.mp hI]

/-- The absolute sum over one norm fiber has a proved polynomial-geometric
majorant. No analytic estimate is assumed here. -/
theorem sum_norm_idealNormFiber_le (χ : Character) (q : ℂ) (n : ℕ) :
    (∑ I ∈ idealsOfNorm n, ‖thetaIdealCharacter χ I * q ^ I.absNorm‖) ≤
      64 * ((n : ℝ) + 1) * ‖q‖ ^ n := by
  calc
    _ ≤ ∑ _I ∈ idealsOfNorm n, ‖q‖ ^ n := by
      apply Finset.sum_le_sum
      intro I hI
      rw [norm_mul, norm_pow, mem_idealsOfNorm.mp hI]
      exact mul_le_of_le_one_left (by positivity) (thetaIdealCharacter_norm_le_one χ I)
    _ = ((idealsOfNorm n).card : ℝ) * ‖q‖ ^ n := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast idealsOfNorm_card_le n) (by positivity)

/-- The ideal-indexed theta series converges absolutely throughout the unit disk. -/
theorem idealTheta_summable_norm (χ : Character) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun I : Ideal O => ‖thetaIdealCharacter χ I * q ^ I.absNorm‖) := by
  rw [← idealNormFiberEquiv.summable_iff]
  apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  have hmaj : Summable (fun n : ℕ => 64 * ((n : ℝ) + 1) * ‖q‖ ^ n) := by
    simpa only [pow_one] using theta_geometric_majorant_summable 64 1 (norm_nonneg q) hq
  apply hmaj.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _)
  intro n
  change (∑' I : ↥(idealsOfNorm n), ‖thetaIdealCharacter χ I * q ^ (I : Ideal O).absNorm‖) ≤ _
  rw [tsum_fintype, Finset.sum_coe_sort (idealsOfNorm n)
    (fun I : Ideal O => ‖thetaIdealCharacter χ I * q ^ I.absNorm‖)]
  exact sum_norm_idealNormFiber_le χ q n

/-- Regrouping the convergent ideal theta series by its finite norm fibers. -/
theorem idealTheta_tsum_eq_coefficients (χ : Character) {q : ℂ} (hq : ‖q‖ < 1) :
    (∑' I : Ideal O, thetaIdealCharacter χ I * q ^ I.absNorm) =
      thetaPowerSeries (idealThetaCoeff χ) q := by
  have hsum := (idealTheta_summable_norm χ hq).of_norm
  rw [← idealNormFiberEquiv.tsum_eq]
  have hsigma := idealNormFiberEquiv.summable_iff.mpr hsum
  have htsum := Summable.tsum_sigma' (fun n => (hasSum_fintype _).summable) hsigma
  simp only [Function.comp_def] at htsum
  rw [htsum]
  unfold thetaPowerSeries
  apply tsum_congr
  intro n
  change (∑' I : ↥(idealsOfNorm n), thetaIdealCharacter χ I * q ^ (I : Ideal O).absNorm) = _
  rw [tsum_fintype, Finset.sum_coe_sort (idealsOfNorm n)
    (fun I : Ideal O => thetaIdealCharacter χ I * q ^ I.absNorm)]
  exact sum_idealNormFiber χ q n

end ArtinMatthews
