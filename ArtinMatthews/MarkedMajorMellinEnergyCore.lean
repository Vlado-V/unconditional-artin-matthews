module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
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

theorem markedMajor_reflected_core_mean (Q : ℝ → ℂ) (hQ : Continuous Q)
    {X T s M : ℝ} (hX : 1 ≤ X) (hT : 0 ≤ T) (hs : s ∈ Icc (-T) T)
    (hmean : (∫ t in Icc (-(2*X*T)) (2*X*T), ‖Q t‖^2) ≤ M) :
    (∫ t in Icc (-(X*T)) (X*T), ‖Q (s-t)‖^2) ≤ M := by
  have hXT : 0 ≤ X*T := mul_nonneg (by linarith) hT
  have hTX : T ≤ X*T := by nlinarith
  have he : (∫ t in Icc (-(X*T)) (X*T), ‖Q (s-t)‖^2) =
      ∫ t in Icc (s-X*T) (s+X*T), ‖Q t‖^2 := by
    rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -(X*T) ≤ X*T),
      ← intervalIntegral.integral_of_le (by linarith : s-X*T ≤ s+X*T)]
    rw [intervalIntegral.integral_comp_sub_left (fun t => ‖Q t‖^2)]
    congr 1
    ring
  rw [he]
  apply le_trans ?_ hmean
  exact setIntegral_mono_set ((hQ.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
    (Filter.Eventually.of_forall (fun t => sq_nonneg ‖Q t‖))
    (Filter.Eventually.of_forall (fun t ht => by constructor <;> nlinarith [ht.1,ht.2,hs.1,hs.2]))

/-- Compact frequency energy uses the actual enlarged endpoint square means. -/
theorem markedMajor_endpoint_core_energy (Q Q' : ℝ → ℂ)
    (hQ : Continuous Q) (hQ' : Continuous Q') {X T M : ℝ}
    (hX : 1 ≤ X) (hT : 0 ≤ T)
    (hm : (∫ t in Icc (-(2*X*T)) (2*X*T), ‖Q t‖^2) ≤ M)
    (hm' : (∫ t in Icc (-(2*X*T)) (2*X*T), ‖Q' t‖^2) ≤ M) :
    (∫ p : ℝ × ℝ in Icc (-(X*T)) (X*T) ×ˢ Icc (-T) T,
      ‖Q p.1‖*‖Q' (p.2-p.1)‖) ≤ 2*T*M := by
  have hXT : 0 ≤ X*T := mul_nonneg (by linarith) hT
  have hsmall : (∫ t in Icc (-(X*T)) (X*T), ‖Q t‖^2) ≤ M := by
    apply le_trans ?_ hm
    exact setIntegral_mono_set ((hQ.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
      (Filter.Eventually.of_forall (fun t => sq_nonneg ‖Q t‖))
      (Filter.Eventually.of_forall (fun t ht => by constructor <;> nlinarith [ht.1,ht.2]))
  let f := fun p : ℝ × ℝ => ‖Q p.1‖*‖Q' (p.2-p.1)‖
  have hf : Continuous f := (hQ.comp continuous_fst).norm.mul
    (hQ'.comp (continuous_snd.sub continuous_fst)).norm
  have hin (s : ℝ) (hs : s ∈ Icc (-T) T) :
      (∫ t in Icc (-(X*T)) (X*T), f (t,s)) ≤ M := by
    have h₁ := (hQ.norm.pow 2).continuousOn.integrableOn_compact (μ := volume) (K := Icc (-(X*T)) (X*T)) isCompact_Icc
    have h₂ := ((hQ'.comp ((continuous_const (y := s)).sub continuous_id)).norm.pow 2).continuousOn.integrableOn_compact
      (μ := volume) (K := Icc (-(X*T)) (X*T)) isCompact_Icc
    have hp := (hQ.norm.mul (hQ'.comp ((continuous_const (y := s)).sub continuous_id)).norm).continuousOn.integrableOn_compact
      (μ := volume) (K := Icc (-(X*T)) (X*T)) isCompact_Icc
    have H := integral_mono hp ((h₁.add h₂).div_const 2) (fun t =>
      show ‖Q t‖*‖Q' (s-t)‖ ≤ (‖Q t‖^2+‖Q' (s-t)‖^2)/2 by
        nlinarith [sq_nonneg (‖Q t‖-‖Q' (s-t)‖)])
    rw [integral_div] at H
    simp only [Pi.add_apply] at H
    rw [integral_add h₁ h₂] at H
    simp only [Pi.mul_apply,Pi.pow_apply,Function.comp_apply,Pi.sub_apply,id_eq] at H
    have Hr := markedMajor_reflected_core_mean Q' hQ' hX hT hs hm'
    dsimp [f]
    linarith
  have hswap : IntegrableOn (fun p : ℝ × ℝ => f (p.2,p.1))
      (Icc (-T) T ×ˢ Icc (-(X*T)) (X*T)) :=
    (hf.comp continuous_swap).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have houter : IntegrableOn (fun s => ∫ t in Icc (-(X*T)) (X*T), f (t,s)) (Icc (-T) T) := by
    have hh : Integrable (fun p : ℝ × ℝ => f (p.2,p.1))
      ((volume.restrict (Icc (-T) T)).prod (volume.restrict (Icc (-(X*T)) (X*T)))) := by
      simpa only [IntegrableOn,Measure.prod_restrict,← Measure.volume_eq_prod] using hswap
    exact hh.integral_prod_left
  calc
    _ = ∫ s in Icc (-T) T, ∫ t in Icc (-(X*T)) (X*T), f (t,s) := by
      change (∫ p in Icc (-(X*T)) (X*T) ×ˢ Icc (-T) T, f p) = _
      rw [Measure.volume_eq_prod,← setIntegral_prod_swap _ _ f]
      exact setIntegral_prod (μ := (volume : Measure ℝ)) (ν := volume) _
        ((hf.comp continuous_swap).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
    _ ≤ ∫ s in Icc (-T) T, M :=
      setIntegral_mono_on houter (integrableOn_const isCompact_Icc.measure_ne_top) measurableSet_Icc hin
    _ = _ := by
      rw [setIntegral_const,Real.volume_real_Icc_of_le (by linarith : -T ≤ T)]
      simp only [smul_eq_mul]
      ring

end
end ArtinMatthews
