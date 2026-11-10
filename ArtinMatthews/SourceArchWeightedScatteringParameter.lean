module

public import ArtinMatthews.SourceArchScatteringKernel
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Holomorphy and joint continuity for the Fourier transform of the
normalized archimedean spherical kernel. The phase need only be
continuous and bounded by one. -/
namespace ArtinMatthews.SourceArchJacquet

open ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory Filter
open scoped Topology
noncomputable section

local notation "traceMeasure" => sourceComplexTraceMeasure
local notation "J" => sourceArchScatteringKernel
local notation "q" => (fun x : ℂ => (1 + ‖x‖ ^ 2 : ℝ))

def sourceArchScatteringParameterDerivative (s x : ℂ) : ℂ :=
  J s x * ((Real.log (q x) : ℂ) * (-2))

theorem sourceArchScatteringKernel_hasDerivAt (s x : ℂ) :
    HasDerivAt (fun z => J z x) (sourceArchScatteringParameterDerivative s x) s := by
  have hq : 0 < q x := by positivity
  have hq0 : (q x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have he := ((((hasDerivAt_id s).const_mul (2 : ℂ)).add_const (1 : ℂ)).neg).const_cpow
    (c := (q x : ℂ)) (Or.inl hq0)
  simpa only [sourceArchScatteringKernel,sourceArchScatteringParameterDerivative,
    id_eq,Pi.neg_apply,mul_one,Complex.ofReal_log hq.le,mul_assoc] using he

theorem sourceArchScatteringKernel_jointContinuous :
    Continuous (fun p : ℂ × ℂ => J p.1 p.2) := by
  unfold sourceArchScatteringKernel
  apply Continuous.cpow (Complex.continuous_ofReal.comp
    (continuous_const.add (continuous_snd.norm.pow 2)))
    ((continuous_fst.const_mul (2 : ℂ)).add_const 1).neg
  intro p
  change (q p.2 : ℂ) ∈ Complex.slitPlane
  exact Complex.ofReal_mem_slitPlane.mpr (show 0 < q p.2 by positivity)

theorem sourceArchScatteringParameterDerivative_jointContinuous :
    Continuous (fun p : ℂ × ℂ => sourceArchScatteringParameterDerivative p.1 p.2) := by
  have hq : Continuous (fun p : ℂ × ℂ => q p.2) :=
    continuous_const.add (continuous_snd.norm.pow 2)
  have hlog : Continuous (fun p : ℂ × ℂ => Real.log (q p.2)) :=
    hq.log (fun p => (show 0 < q p.2 by positivity).ne')
  exact sourceArchScatteringKernel_jointContinuous.mul
    ((Complex.continuous_ofReal.comp hlog).mul continuous_const)

theorem sourceArchScatteringKernel_norm_le_of_re_ge {δ : ℝ} (hδ : 0 < δ) {s : ℂ}
    (hs : δ ≤ s.re) (x : ℂ) :
    ‖J s x‖ ≤ ‖J (δ/2 : ℝ) x‖ := by
  rw [sourceArchScatteringKernel_norm,sourceArchScatteringKernel_norm,Complex.ofReal_re]
  exact Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (sq_nonneg ‖x‖)) (by linarith)

theorem sourceArchScatteringParameterDerivative_norm_le {δ : ℝ} (hδ : 0 < δ) {s : ℂ}
    (hs : δ ≤ s.re) (x : ℂ) :
    ‖sourceArchScatteringParameterDerivative s x‖ ≤ (2/δ) * ‖J (δ/2 : ℝ) x‖ := by
  have hq : 1 ≤ q x := le_add_of_nonneg_right (sq_nonneg _)
  have hq' : 0 < q x := zero_lt_one.trans_le hq
  rw [sourceArchScatteringParameterDerivative,norm_mul,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (Real.log_nonneg hq),norm_neg,Complex.norm_ofNat,
    sourceArchScatteringKernel_norm,sourceArchScatteringKernel_norm,Complex.ofReal_re]
  change q x ^ (-(2*s.re+1)) * (Real.log (q x)*2) ≤
    (2/δ)*q x ^ (-(2*(δ/2)+1))
  calc
    _ ≤ q x ^ (-(2*s.re+1)) * ((q x ^ δ / δ)*2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (Real.log_le_rpow_div hq'.le hδ) (by norm_num)) (Real.rpow_nonneg hq'.le _)
    _ = (2/δ) * q x ^ (-(2*s.re+1)+δ) := by rw [Real.rpow_add hq']; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hq (by linarith)) (by positivity)

def sourceArchWeightedScattering (ψ : ℂ → ℂ) (s a : ℂ) : ℂ :=
  ∫ x : ℂ, ψ (a*x)*J s x ∂traceMeasure

def sourceArchWeightedScatteringDerivative (ψ : ℂ → ℂ) (s a : ℂ) : ℂ :=
  ∫ x : ℂ, ψ (a*x)*sourceArchScatteringParameterDerivative s x ∂traceMeasure

set_option diagnostics true in
theorem sourceArchWeightedScattering_hasDerivAt (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hψ₁ : ∀ x, ‖ψ x‖ ≤ 1) {s : ℂ} (hs : 0 < s.re) (a : ℂ) :
    HasDerivAt (fun z => sourceArchWeightedScattering ψ z a)
      (sourceArchWeightedScatteringDerivative ψ s a) s := by
  trace "WS start"
  let δ := s.re/2
  have hδ : 0 < δ := half_pos hs
  have hδs : δ < s.re := half_lt_self hs
  let D := fun x : ℂ => (2/δ)*‖J (δ/2 : ℝ) x‖
  have hD : Integrable D traceMeasure := ((sourceArchScatteringKernel_integrable
    (s := (δ/2 : ℝ)) (by simpa only [Complex.ofReal_re] using half_pos hδ)).norm).const_mul _
  trace "WS integrable bound"
  let W := fun x : ℂ => ψ (a*x)
  have hW : Continuous W := hψ.comp (continuous_const.mul continuous_id)
  let F : ℂ → ℂ → ℂ := fun z x => W x * J z x
  let F' : ℂ → ℂ → ℂ := fun z x => W x * sourceArchScatteringParameterDerivative z x
  let U := {z : ℂ | δ < z.re}
  have hU : U ∈ 𝓝 s := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hδs
  have hF (z : ℂ) : AEStronglyMeasurable (F z) traceMeasure :=
    (hW.mul (sourceArchScatteringKernel_continuous z)).aestronglyMeasurable
  trace "WS measurable"
  have hpair : Continuous (fun x : ℂ => (s,x)) := continuous_const.prodMk continuous_id
  have hJ' : Continuous (sourceArchScatteringParameterDerivative s) := by
    have hc := sourceArchScatteringParameterDerivative_jointContinuous.comp hpair
    simpa only [Function.comp_def] using hc
  have hF' : AEStronglyMeasurable (F' s) traceMeasure := (hW.mul hJ').aestronglyMeasurable
  have hi : Integrable (F s) traceMeasure :=
    (sourceArchScatteringKernel_integrable hs).bdd_mul (c := 1) hW.aestronglyMeasurable
      (Eventually.of_forall fun x => hψ₁ _)
  trace "WS integrable F"
  have hb : ∀ x : ℂ, ∀ z ∈ U, ‖F' z x‖ ≤ D x := by
    intro x z hz
    change δ < z.re at hz
    change ‖W x * sourceArchScatteringParameterDerivative z x‖ ≤ D x
    rw [norm_mul]
    calc
      _ ≤ 1*‖sourceArchScatteringParameterDerivative z x‖ :=
        mul_le_mul_of_nonneg_right (hψ₁ _) (norm_nonneg _)
      _ ≤ D x := by rw [one_mul]; exact sourceArchScatteringParameterDerivative_norm_le hδ hz.le x
  trace "WS bounded derivative"
  have hd (x z : ℂ) : HasDerivAt (fun t => F t x) (F' z x) z :=
    (sourceArchScatteringKernel_hasDerivAt z x).const_mul (W x)
  trace "WS point derivative"
  have ht := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℂ) (μ := traceMeasure) (x₀ := s) (s := U) (F := F) (F' := F') (bound := D) hU (Eventually.of_forall hF)
    hi hF' (Eventually.of_forall hb) hD (Eventually.of_forall (fun x z _ => hd x z))
  trace "WS integral derivative"
  change HasDerivAt (fun z => ∫ x, F z x ∂traceMeasure) (∫ x, F' s x ∂traceMeasure) s
  exact ht.2

private theorem sourceArchWeightedScattering_continuousAt_aux (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hψ₁ : ∀ x, ‖ψ x‖ ≤ 1) (G : ℂ → ℂ → ℂ)
    (hG : Continuous (fun p : ℂ × ℂ => G p.1 p.2))
    (hbound : ∀ δ : ℝ, 0 < δ → ∃ D : ℂ → ℝ, Integrable D traceMeasure ∧
      ∀ s : ℂ, δ ≤ s.re → ∀ x, ‖G s x‖ ≤ D x)
    (p : ℂ × ℂ) (hp : 0 < p.1.re) :
    ContinuousAt (fun p : ℂ × ℂ => ∫ x : ℂ, ψ (p.2*x)*G p.1 x ∂traceMeasure) p := by
  let δ := p.1.re/2
  obtain ⟨D,hD,hb⟩ := hbound δ (half_pos hp)
  have hev : ∀ᶠ r : ℂ × ℂ in 𝓝 p, δ < r.1.re :=
    (Complex.continuous_re.comp continuous_fst).continuousAt.tendsto
      (Ioi_mem_nhds (half_lt_self hp))
  refine continuousAt_of_dominated
    (Eventually.of_forall fun r =>
      ((hψ.comp (continuous_const.mul continuous_id)).mul
        (hG.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable)
    (hev.mono fun r hr => Eventually.of_forall fun x => ?_) hD
    (Eventually.of_forall fun x =>
      ((hψ.comp (continuous_snd.mul continuous_const)).mul
        (hG.comp (continuous_fst.prodMk continuous_const))).continuousAt)
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (hψ₁ _) (norm_nonneg _)).trans
    (by rw [one_mul]; exact hb r.1 hr.le x)

theorem sourceArchWeightedScattering_continuousAt (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hψ₁ : ∀ x, ‖ψ x‖ ≤ 1) (p : ℂ × ℂ) (hp : 0 < p.1.re) :
    ContinuousAt (fun p : ℂ × ℂ => sourceArchWeightedScattering ψ p.1 p.2) p := by
  apply sourceArchWeightedScattering_continuousAt_aux ψ hψ hψ₁ J
    sourceArchScatteringKernel_jointContinuous _ p hp
  intro δ hδ
  refine ⟨fun x => ‖J (δ/2 : ℝ) x‖, (sourceArchScatteringKernel_integrable
    (s := (δ/2 : ℝ)) (by simpa only [Complex.ofReal_re] using half_pos hδ)).norm, ?_⟩
  exact fun s hs x => sourceArchScatteringKernel_norm_le_of_re_ge hδ hs x

theorem sourceArchWeightedScatteringDerivative_continuousAt (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hψ₁ : ∀ x, ‖ψ x‖ ≤ 1) (p : ℂ × ℂ) (hp : 0 < p.1.re) :
    ContinuousAt (fun p : ℂ × ℂ => sourceArchWeightedScatteringDerivative ψ p.1 p.2) p := by
  apply sourceArchWeightedScattering_continuousAt_aux ψ hψ hψ₁
    sourceArchScatteringParameterDerivative sourceArchScatteringParameterDerivative_jointContinuous _ p hp
  intro δ hδ
  refine ⟨fun x => (2/δ)*‖J (δ/2 : ℝ) x‖, ((sourceArchScatteringKernel_integrable
    (s := (δ/2 : ℝ)) (by simpa only [Complex.ofReal_re] using half_pos hδ)).norm).const_mul _, ?_⟩
  exact fun s hs x => sourceArchScatteringParameterDerivative_norm_le hδ hs x

theorem sourceArchWeightedScattering_analyticOnNhd (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hψ₁ : ∀ x, ‖ψ x‖ ≤ 1) (a : ℂ) :
    AnalyticOnNhd ℂ (fun z => sourceArchWeightedScattering ψ z a) {z : ℂ | 0 < z.re} := by
  apply DifferentiableOn.analyticOnNhd _
    (isOpen_lt continuous_const Complex.continuous_re)
  exact fun s hs => (sourceArchWeightedScattering_hasDerivAt ψ hψ hψ₁ hs a).differentiableAt.differentiableWithinAt

end
end ArtinMatthews.SourceArchJacquet
