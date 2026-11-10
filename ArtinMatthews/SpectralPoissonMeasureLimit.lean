module

public import ArtinMatthews.SpectralPoissonApproximation
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import ArtinMatthews.SpectralKLPoissonBilinear
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
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
public import Mathlib.Topology.UniformSpace.Uniformizable


set_option backward.privateInPublic true
@[expose] public section

/-! Scalar Stone inversion against compact real tests. The actual Poisson
approximate identity is integrated against an arbitrary finite measure. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology CompactlySupported
namespace ArtinMatthews

def spectralPoissonMeasureTransform (μ : Measure ℝ) (ε x : ℝ) : ℝ :=
  ∫ t, spectralPoissonPeak ε (x-t) ∂μ

theorem spectralPoissonPeak_nonnegative {ε : ℝ} (hε : 0<ε) (x : ℝ) :
    0 ≤ spectralPoissonPeak ε x := by
  unfold spectralPoissonPeak
  positivity

theorem spectralPoissonPeak_le_inv {ε : ℝ} (hε : 0<ε) (x : ℝ) :
    spectralPoissonPeak ε x≤ε⁻¹ := by
  unfold spectralPoissonPeak
  calc
    ε/(ε^2+x^2)≤ε/ε^2 :=
      div_le_div_of_nonneg_left hε.le (sq_pos_of_pos hε) (le_add_of_nonneg_right (sq_nonneg x))
    _=ε⁻¹ := by field_simp

theorem spectralPoissonPeak_continuous {ε : ℝ} (hε : 0<ε) :
    Continuous (spectralPoissonPeak ε) := by
  unfold spectralPoissonPeak
  exact continuous_const.div (continuous_const.add (continuous_id.pow 2))
    (fun x => ne_of_gt (by positivity))

theorem spectralPoissonCompactTest_bound (f : C_c(ℝ,ℝ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ x : ℝ,‖f x‖≤C := by
  obtain ⟨M,hM⟩ := f.hasCompactSupport.exists_bound_of_continuousOn f.continuous.continuousOn
  refine ⟨max M 0,le_max_right _ _,fun x => ?_⟩
  by_cases hx : x∈tsupport f
  · exact (hM x hx).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx,norm_zero]
    exact le_max_right _ _

theorem spectralPoissonCompactTest_fubini (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : C_c(ℝ,ℝ)) {ε : ℝ} (hε : 0<ε) :
    (∫ x : ℝ, spectralPoissonMeasureTransform μ ε x*f x)=
      ∫ t, (∫ x : ℝ,spectralPoissonPeak ε (x-t)*f x) ∂μ := by
  let F (p : ℝ×ℝ) := spectralPoissonPeak ε (p.1-p.2)*f p.1
  have hF : Continuous F :=
    ((spectralPoissonPeak_continuous hε).comp (continuous_fst.sub continuous_snd)).mul
      (f.continuous.comp continuous_fst)
  have hDom : Integrable (fun p : ℝ×ℝ => ε⁻¹*‖f p.1‖) (volume.prod μ) :=
    (f.integrable.norm.const_mul ε⁻¹).comp_fst μ
  have hi : Integrable F (volume.prod μ) := hDom.mono' hF.aestronglyMeasurable
    (Eventually.of_forall fun p => by
      change ‖spectralPoissonPeak ε (p.1-p.2)*f p.1‖≤ε⁻¹*‖f p.1‖
      rw [norm_mul,Real.norm_of_nonneg (spectralPoissonPeak_nonnegative hε _)]
      exact mul_le_mul_of_nonneg_right (spectralPoissonPeak_le_inv hε _) (norm_nonneg _))
  simp_rw [spectralPoissonMeasureTransform,← integral_mul_const]
  exact integral_integral_swap hi

theorem spectralPoissonCompactTest_pointwise (f : C_c(ℝ,ℝ)) (t : ℝ) :
    Tendsto (fun ε : ℝ => ∫ x : ℝ,spectralPoissonPeak ε (x-t)*f x)
      (𝓝[>] (0:ℝ)) (𝓝 (Real.pi*f t)) := by
  obtain ⟨C,_,hC⟩ := spectralPoissonCompactTest_bound f
  let G (p : ℝ×ℝ) : ℂ := (f p.2:ℂ)
  have hG : Continuous G := Complex.continuous_ofReal.comp (f.continuous.comp continuous_snd)
  have h := spectralPoissonPeak_approximation t G hG.continuousAt
    (Eventually.of_forall fun ε =>
      (Complex.continuous_ofReal.comp (f.continuous.comp (continuous_const.add (continuous_const.mul continuous_id)))).aestronglyMeasurable)
    C (Eventually.of_forall fun ε x => by simpa only [G,Complex.norm_real] using hC x)
  have he := Complex.continuous_re.continuousAt.tendsto.comp h
  simpa only [Function.comp_def,G,Complex.real_smul,← Complex.ofReal_mul,integral_complex_ofReal,
    Complex.ofReal_re] using he

theorem spectralPoissonCompactTest_limit (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : C_c(ℝ,ℝ)) :
    Tendsto (fun ε : ℝ => Real.pi⁻¹*(∫ x : ℝ,spectralPoissonMeasureTransform μ ε x*f x))
      (𝓝[>] (0:ℝ)) (𝓝 (∫ t,f t ∂μ)) := by
  obtain ⟨C,hC,hCf⟩ := spectralPoissonCompactTest_bound f
  let I (ε t : ℝ) := ∫ x : ℝ,spectralPoissonPeak ε (x-t)*f x
  have hI : Tendsto (fun ε => ∫ t,I ε t ∂μ) (𝓝[>] (0:ℝ)) (𝓝 (∫ t,Real.pi*f t ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => Real.pi*C)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hF : Continuous (fun p : ℝ×ℝ => spectralPoissonPeak ε (p.1-p.2)*f p.1) :=
        ((spectralPoissonPeak_continuous hε).comp (continuous_fst.sub continuous_snd)).mul
          (f.continuous.comp continuous_fst)
      exact hF.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact Eventually.of_forall fun t => by
        have hi := (spectralPoissonPeak_integrable ε t hε).mul_const C
        calc
          ‖I ε t‖≤∫ x : ℝ,spectralPoissonPeak ε (x-t)*C :=
            norm_integral_le_of_norm_le hi (Eventually.of_forall fun x => by
              change ‖spectralPoissonPeak ε (x-t)*f x‖ ≤ spectralPoissonPeak ε (x-t)*C
              rw [norm_mul,Real.norm_of_nonneg (spectralPoissonPeak_nonnegative hε _)]
              exact mul_le_mul_of_nonneg_left (hCf x) (spectralPoissonPeak_nonnegative hε _))
          _=Real.pi*C := by rw [integral_mul_const,spectralPoissonPeak_real_integral ε t hε]
    · exact integrable_const _
    · exact Eventually.of_forall (spectralPoissonCompactTest_pointwise f)
  have hlim := tendsto_const_nhds.mul hI (a:=Real.pi⁻¹)
  rw [integral_const_mul,← mul_assoc,inv_mul_cancel₀ Real.pi_ne_zero,one_mul] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact congrArg (fun x : ℝ => Real.pi⁻¹*x) (spectralPoissonCompactTest_fubini μ f hε).symm

end ArtinMatthews
