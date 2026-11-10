module

public import ArtinMatthews.SpectralResidualProbeProfile
public import ArtinMatthews.SpectralEisensteinCompactExponential
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine compact positive-height Mellin transform and an entire
real-bump transform used to distinguish the incoming channels. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BoundedContinuousFunction InnerProductSpace
namespace ArtinMatthews

def spectralCompactCuspMellin (ρ : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ y in Ioi (0:ℝ),(y^(-2:ℤ)) • inner ℂ (ρ y) ((y:ℂ)^s)

def gamma0ProbeMellin (s : ℂ) : ℂ :=
  spectralCompactCuspMellin (fun y => (gamma0ResidualProbeBump y:ℂ)) s

theorem gamma0ProbeBump_bounds {y : ℝ} (hy : gamma0ResidualProbeBump y≠0) : y∈Icc (1:ℝ) 3 := by
  have hmem : y∈tsupport gamma0ResidualProbeBump := subset_closure hy
  rw [gamma0ResidualProbeBump.tsupport_eq,Metric.mem_closedBall,Real.dist_eq] at hmem
  change |y-2|≤1/2 at hmem
  constructor <;> linarith [(abs_le.mp hmem).1,(abs_le.mp hmem).2]

def gamma0ProbeMellinLog : ℝ →ᵇ ℂ :=
  spectralBoundedHeightLog (fun y : ℝ => max y 1)
    (continuous_id.max continuous_const) (fun y => zero_lt_one.trans_le (le_max_right y 1))
    3 (by norm_num)

def gamma0ProbeMellinWeight (y : ℝ) : ℂ :=
  (gamma0ResidualProbeBump y/(max y 1)^2:ℝ)

theorem gamma0ProbeMellinWeight_continuous : Continuous gamma0ProbeMellinWeight :=
  Complex.continuous_ofReal.comp (gamma0ResidualProbeBump.continuous.div
    ((continuous_id.max continuous_const).pow 2)
    (fun y => pow_ne_zero _ (ne_of_gt (zero_lt_one.trans_le (le_max_right y 1)))))

theorem gamma0ProbeMellinWeight_compact : HasCompactSupport gamma0ProbeMellinWeight := by
  apply gamma0ResidualProbeBump.hasCompactSupport.mono'
  intro y hy
  by_contra hout
  have hb := image_eq_zero_of_notMem_tsupport hout
  exact hy (by simp only [gamma0ProbeMellinWeight,hb,zero_div,Complex.ofReal_zero])

theorem gamma0ProbeMellinWeight_conj (y : ℝ) :
    (starRingEnd ℂ) (gamma0ProbeMellinWeight y)=gamma0ProbeMellinWeight y :=
  Complex.conj_ofReal _

theorem gamma0ProbeMellin_exp_eq (s : ℂ) {y : ℝ} (hy : y∈Icc (1:ℝ) 3) :
    spectralBoundedExponential gamma0ProbeMellinLog s y=(y:ℂ)^s := by
  have hp : 0<y := zero_lt_one.trans_le hy.1
  have he : gamma0ProbeMellinLog y=(Real.log y:ℂ) := by
    have h := spectralBoundedHeightLog_eq (fun t : ℝ => max t 1)
      (continuous_id.max continuous_const) (fun t => zero_lt_one.trans_le (le_max_right t 1))
      3 (by norm_num) y
      (by simpa only [max_eq_left hy.1] using hy)
    simpa only [gamma0ProbeMellinLog,max_eq_left hy.1] using h
  rw [spectralBoundedExponential_apply,he,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
    ← Complex.ofReal_log hp.le,mul_comm]

theorem gamma0ProbeMellin_integrand (s : ℂ) (y : ℝ) :
    (y^(-2:ℤ)) • inner ℂ (gamma0ResidualProbeBump y:ℂ) ((y:ℂ)^s)=
      spectralBoundedExponential gamma0ProbeMellinLog s y*gamma0ProbeMellinWeight y := by
  by_cases hb : gamma0ResidualProbeBump y=0
  · simp only [hb,Complex.ofReal_zero,inner_zero_left,smul_zero,gamma0ProbeMellinWeight,zero_div,mul_zero]
  · have hy := gamma0ProbeBump_bounds hb
    rw [gamma0ProbeMellin_exp_eq s hy,gamma0ProbeMellinWeight,max_eq_left hy.1,
      RCLike.inner_apply,Complex.conj_ofReal,Complex.real_smul]
    have hz : y^(-2:ℤ)=(y^2)⁻¹ := by simp
    rw [hz,Complex.ofReal_inv,Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_pow]
    ring

theorem gamma0ProbeMellin_integral (s : ℂ) :
    gamma0ProbeMellin s=∫ y,spectralBoundedExponential gamma0ProbeMellinLog s y*gamma0ProbeMellinWeight y := by
  unfold gamma0ProbeMellin spectralCompactCuspMellin
  simp_rw [gamma0ProbeMellin_integrand]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hb : gamma0ResidualProbeBump y=0 := by
    by_contra hn
    exact hy (zero_lt_one.trans_le (gamma0ProbeBump_bounds hn).1)
  simp only [gamma0ProbeMellinWeight,hb,zero_div,Complex.ofReal_zero,mul_zero]

theorem gamma0ProbeMellin_integrand_integrable (s : ℂ) :
    Integrable (fun y => (y^(-2:ℤ)) • inner ℂ (gamma0ResidualProbeBump y:ℂ) ((y:ℂ)^s)) := by
  simp_rw [gamma0ProbeMellin_integrand]
  have hc := (spectralBoundedExponential gamma0ProbeMellinLog s).continuous.mul gamma0ProbeMellinWeight_continuous
  exact hc.integrable_of_hasCompactSupport (gamma0ProbeMellinWeight_compact.mul_left)

theorem gamma0ProbeMellin_analyticAt (s : ℂ) : AnalyticAt ℂ gamma0ProbeMellin s := by
  let μ : Measure ℝ := volume.restrict (Icc (1:ℝ) 3)
  let _ : IsFiniteMeasure μ := by dsimp [μ];infer_instance
  have hf : MemLp gamma0ProbeMellinWeight 2 μ :=
    (memLp_two_iff_integrable_sq_norm gamma0ProbeMellinWeight_continuous.aestronglyMeasurable).mpr
      ((gamma0ProbeMellinWeight_continuous.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
  let f : Lp ℂ 2 μ := hf.toLp gamma0ProbeMellinWeight
  let L : (ℝ →ᵇ ℂ) →L[ℂ] ℂ := (innerSL ℂ f).comp (BoundedContinuousFunction.toLp 2 μ ℂ)
  have he (w : ℂ) : gamma0ProbeMellin w=L (spectralBoundedExponential gamma0ProbeMellinLog w) := by
    rw [gamma0ProbeMellin_integral]
    calc
      _ = ∫ y in Icc (1:ℝ) 3,
          spectralBoundedExponential gamma0ProbeMellinLog w y*gamma0ProbeMellinWeight y := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro y hy
        have hb : gamma0ResidualProbeBump y=0 := by
          by_contra hn
          exact hy (gamma0ProbeBump_bounds hn)
        simp only [gamma0ProbeMellinWeight,hb,zero_div,Complex.ofReal_zero,mul_zero]
      _ = _ := by
        change _=inner ℂ f (BoundedContinuousFunction.toLp 2 μ ℂ
          (spectralBoundedExponential gamma0ProbeMellinLog w))
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hf.coeFn_toLp,BoundedContinuousFunction.coeFn_toLp 2 μ ℂ
          (spectralBoundedExponential gamma0ProbeMellinLog w)] with y hfy hgy
        change _=inner ℂ (f y) _
        rw [hfy,hgy,RCLike.inner_apply,gamma0ProbeMellinWeight_conj]
  rw [show gamma0ProbeMellin=(fun w => L (spectralBoundedExponential gamma0ProbeMellinLog w)) from funext he]
  exact (L.analyticAt _).comp (spectralBoundedExponential_analyticAt gamma0ProbeMellinLog s)

end ArtinMatthews
