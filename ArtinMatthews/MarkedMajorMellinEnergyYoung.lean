module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Integral.Prod
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

namespace ArtinMatthews
open MeasureTheory
noncomputable section

/-- Weighted two-endpoint energy from actual translated square means. The final
bound contains no interval-length or frequency-scale factor. -/
theorem markedMajor_weighted_endpoint_energy
    (wt ws : ℝ → ℝ) (ht : Integrable wt) (hs : Integrable ws)
    (ht0 : ∀ t, 0 ≤ wt t) (hs0 : ∀ s, 0 ≤ ws s)
    (Q Q' : ℝ → ℂ) (hQ : Continuous Q) (hQ' : Continuous Q')
    {B B' M : ℝ} (hB : ∀ t, ‖Q t‖ ≤ B) (hB' : ∀ t, ‖Q' t‖ ≤ B')
    (hm : (∫ t, wt t*‖Q t‖^2) ≤ M)
    (hm' : ∀ s, (∫ t, wt t*‖Q' (s-t)‖^2) ≤ M) :
    Integrable (fun p : ℝ × ℝ => wt p.1*ws p.2*(‖Q p.1‖*‖Q' (p.2-p.1)‖)) ∧
      (∫ p : ℝ × ℝ, wt p.1*ws p.2*(‖Q p.1‖*‖Q' (p.2-p.1)‖)) ≤ M*(∫ s, ws s) := by
  have hB0 : 0 ≤ B := (norm_nonneg (Q 0)).trans (hB 0)
  have hB0' : 0 ≤ B' := (norm_nonneg (Q' 0)).trans (hB' 0)
  have hb := ht.mul_prod hs
  let f₁ := fun p : ℝ × ℝ => wt p.1*ws p.2*‖Q p.1‖^2
  let f₂ := fun p : ℝ × ℝ => wt p.1*ws p.2*‖Q' (p.2-p.1)‖^2
  have hi₁ : Integrable f₁ := by
    apply hb.mul_bdd (c := B^2)
    · exact ((hQ.comp continuous_fst).norm.pow 2).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun p => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hB p.1) 2)
  have hi₂ : Integrable f₂ := by
    apply hb.mul_bdd (c := B'^2)
    · exact ((hQ'.comp (continuous_snd.sub continuous_fst)).norm.pow 2).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun p => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hB' (p.2-p.1)) 2)
  have hip : Integrable (fun p : ℝ × ℝ => wt p.1*ws p.2*(‖Q p.1‖*‖Q' (p.2-p.1)‖)) := by
    apply hb.mul_bdd (c := B*B')
    · exact ((hQ.comp continuous_fst).norm.mul
        (hQ'.comp (continuous_snd.sub continuous_fst)).norm).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun p => by
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
        exact mul_le_mul (hB _) (hB' _) (norm_nonneg _) hB0)
  refine ⟨hip,?_⟩
  have hmass : 0 ≤ ∫ s, ws s := integral_nonneg hs0
  have h₁ : (∫ p, f₁ p) ≤ M*(∫ s, ws s) := by
    calc
      _ = ∫ p : ℝ × ℝ, (wt p.1*‖Q p.1‖^2)*ws p.2 := by
        apply integral_congr_ae
        filter_upwards with p
        dsimp [f₁]
        ring
      _ = (∫ t, wt t*‖Q t‖^2)*(∫ s, ws s) := by
        exact integral_prod_mul (fun t => wt t*‖Q t‖^2) ws
      _ ≤ _ := mul_le_mul_of_nonneg_right hm hmass
  have h₂ : (∫ p, f₂ p) ≤ M*(∫ s, ws s) := by
    have he (s : ℝ) : (∫ t, f₂ (t,s)) = ws s*(∫ t, wt t*‖Q' (s-t)‖^2) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      dsimp [f₂]
      ring
    calc
      _ = ∫ s, ∫ t, f₂ (t,s) := integral_prod_symm _ hi₂
      _ ≤ ∫ s, ws s*M := integral_mono hi₂.integral_prod_right (hs.mul_const M) (fun s => by
        rw [he]
        exact mul_le_mul_of_nonneg_left (hm' s) (hs0 s))
      _ = _ := by rw [integral_mul_const]; ring
  have hpoint (p : ℝ × ℝ) : wt p.1*ws p.2*(‖Q p.1‖*‖Q' (p.2-p.1)‖) ≤
      (f₁ p+f₂ p)/2 := by
    have h := mul_le_mul_of_nonneg_left
      (show ‖Q p.1‖*‖Q' (p.2-p.1)‖ ≤ (‖Q p.1‖^2+‖Q' (p.2-p.1)‖^2)/2 by
        nlinarith [sq_nonneg (‖Q p.1‖-‖Q' (p.2-p.1)‖)]) (mul_nonneg (ht0 p.1) (hs0 p.2))
    convert h using 1
    dsimp [f₁,f₂]
    ring
  have H := integral_mono hip ((hi₁.add hi₂).div_const 2) hpoint
  rw [integral_div] at H
  simp only [Pi.add_apply] at H
  rw [integral_add hi₁ hi₂] at H
  linarith

end
end ArtinMatthews
