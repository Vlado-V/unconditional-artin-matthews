module

public import ArtinMatthews.MarkedMajorFourierWeightPlane
public import ArtinMatthews.MarkedMajorFourierSeparation
public import ArtinMatthews.MarkedMajorMellinEnergyYoung
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
open MeasureTheory Set
noncomputable section

theorem markedMajorFourierWeight_frequency {W X : ℝ} (hX : 0 < X) (n : ℕ) (t : ℝ) :
    markedMajorFourierWeight W n (t/X) = markedMajorFourierWeight (W*X) n t := by
  simp only [markedMajorFourierWeight,abs_div,abs_of_pos hX,div_div,mul_comm]

theorem markedMajor_reflected_weighted_mean (Q : ℝ → ℂ) (Z s : ℝ) :
    (∫ t, markedMajorFourierWeight Z 2 t*‖Q (s-t)‖^2) =
      ∫ t, markedMajorFourierWeight Z 2 (t-s)*‖Q t‖^2 := by
  simpa only [markedMajorFourierWeight,sub_sub_cancel_left,abs_neg] using
    integral_sub_left_eq_self (fun t => markedMajorFourierWeight Z 2 (t-s)*‖Q t‖^2) volume s

theorem markedMajor_scaled_endpoint_integrable (F : SchwartzMap (ℝ × ℝ) ℂ)
    {X : ℝ} (hX : 0 < X) (Q Q' : ℝ → ℂ) (hQ : Continuous Q) (hQ' : Continuous Q')
    {B B' : ℝ} (hB : ∀ t, ‖Q t‖ ≤ B) (hB' : ∀ t, ‖Q' t‖ ≤ B') :
    Integrable (fun p : ℝ × ℝ => F (p.1/X,p.2)*(Q p.1*Q' (p.2-p.1))) := by
  let G : SchwartzMap (ℝ × ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (markedMajorMellinFrequencyScale X hX.ne') F
  have hi : Integrable (fun p : ℝ × ℝ => F (p.1/X,p.2)) := by
    convert G.integrable (μ := volume) using 1
    funext p
    change _ = F (markedMajorMellinFrequencyScale X hX.ne' p)
    rw [markedMajorMellinFrequencyScale_apply]
  apply hi.mul_bdd (c := B*B')
  · exact ((hQ.comp continuous_fst).mul (hQ'.comp (continuous_snd.sub continuous_fst))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun p => by
      rw [norm_mul]
      exact mul_le_mul (hB _) (hB' _) (norm_nonneg _) ((norm_nonneg (Q 0)).trans (hB 0)))

/-- The tail is estimated by translated weighted energy, so no factor X is lost. -/
theorem markedMajor_scaled_endpoint_tail
    (F : SchwartzMap (ℝ × ℝ) ℂ) {W X T C M : ℝ}
    (hW : 0 < W) (hX : 0 < X) (hT : 0 ≤ T) (hC : 0 ≤ C) (n : ℕ)
    (hF : ∀ p, ‖F p‖ ≤ C*markedMajorFourierPlaneWeight W (n+2) p)
    (Q Q' : ℝ → ℂ) (hQ : Continuous Q) (hQ' : Continuous Q')
    {B B' : ℝ} (hB : ∀ t, ‖Q t‖ ≤ B) (hB' : ∀ t, ‖Q' t‖ ≤ B')
    (hm : ∀ c, (∫ t, markedMajorFourierWeight (W*X) 2 (t-c)*‖Q t‖^2) ≤ M)
    (hm' : ∀ c, (∫ t, markedMajorFourierWeight (W*X) 2 (t-c)*‖Q' t‖^2) ≤ M) :
    (∫ p : ℝ × ℝ in {p | T ≤ |p.1/X| ∨ T ≤ |p.2|},
      ‖F (p.1/X,p.2)*(Q p.1*Q' (p.2-p.1))‖) ≤
      C*((1+T/W)^n)⁻¹*M*(W*markedMajorFourierWeightMass) := by
  let D : ℝ := ((1+T/W)^n)⁻¹
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let wt := markedMajorFourierWeight (W*X) 2
  let ws := markedMajorFourierWeight W 2
  have hwt : Integrable wt := markedMajorFourierWeight_integrable_two (mul_pos hW hX)
  have hws : Integrable ws := markedMajorFourierWeight_integrable_two hW
  have hwt0 : ∀ t, 0 ≤ wt t := markedMajorFourierWeight_nonneg (mul_pos hW hX) 2
  have hws0 : ∀ s, 0 ≤ ws s := markedMajorFourierWeight_nonneg hW 2
  have hmean : (∫ t, wt t*‖Q t‖^2) ≤ M := by simpa only [sub_zero] using hm 0
  have hmean' : ∀ s, (∫ t, wt t*‖Q' (s-t)‖^2) ≤ M := fun s =>
    (markedMajor_reflected_weighted_mean Q' (W*X) s).trans_le (hm' s)
  obtain ⟨hi,hbound⟩ := markedMajor_weighted_endpoint_energy wt ws hwt hws hwt0 hws0
    Q Q' hQ hQ' hB hB' hmean hmean'
  let H := fun p : ℝ × ℝ => wt p.1*ws p.2*(‖Q p.1‖*‖Q' (p.2-p.1)‖)
  let S : Set (ℝ × ℝ) := {p | T ≤ |p.1/X| ∨ T ≤ |p.2|}
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_const (continuous_abs.comp (continuous_fst.div_const X)).measurable).union
      (measurableSet_le measurable_const (continuous_abs.comp continuous_snd).measurable)
  have hH0 : ∀ p, 0 ≤ H p := fun p =>
    mul_nonneg (mul_nonneg (hwt0 _) (hws0 _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hpoint (p : ℝ × ℝ) (hp : p ∈ S) :
      ‖F (p.1/X,p.2)*(Q p.1*Q' (p.2-p.1))‖ ≤ (C*D)*H p := by
    have htail := markedMajorFourierPlaneWeight_tail_pointwise hW hT n (p := (p.1/X,p.2)) hp
    have hf := (hF (p.1/X,p.2)).trans (mul_le_mul_of_nonneg_left htail hC)
    rw [norm_mul,norm_mul]
    have Hle := mul_le_mul_of_nonneg_right hf (mul_nonneg (norm_nonneg (Q p.1))
      (norm_nonneg (Q' (p.2-p.1))))
    convert Hle using 1
    dsimp [H,wt,ws,D]
    unfold markedMajorFourierPlaneWeight
    rw [markedMajorFourierWeight_frequency hX]
    ring
  calc
    _ ≤ ∫ p in S, (C*D)*H p :=
      setIntegral_mono_on (markedMajor_scaled_endpoint_integrable F hX Q Q' hQ hQ' hB hB').norm.integrableOn
        (hi.const_mul (C*D)).integrableOn hS hpoint
    _ ≤ ∫ p, (C*D)*H p :=
      setIntegral_le_integral (hi.const_mul (C*D))
        (Filter.Eventually.of_forall (fun p => mul_nonneg (mul_nonneg hC hD) (hH0 p)))
    _ = (C*D)*(∫ p, H p) := integral_const_mul _ _
    _ ≤ (C*D)*(M*(∫ s, ws s)) := mul_le_mul_of_nonneg_left hbound (mul_nonneg hC hD)
    _ = _ := by rw [markedMajorFourierWeight_integral_two hW]; dsimp [D]; ring

end
end ArtinMatthews
