module

public import ArtinMatthews.SpectralKLUnitary
public import ArtinMatthews.SpectralWeylPhysicalBilinearGaussian
public import ArtinMatthews.SpectralKLAnalysisCalibration
public import ArtinMatthews.SpectralKLBoundedPairing
public import ArtinMatthews.SpectralKLCutoffCalibration
public import ArtinMatthews.SpectralWeylBoundedOrder
public import ArtinMatthews.SpectralWeylCutoffCompact
public import ArtinMatthews.SpectralWeylNoncompactKL
public import ArtinMatthews.SpectralWeylTwoProfileCutoff
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! Strong KL convergence and the actual second physical cutoff give
J/K identities with two noncompact physical profiles. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace ArtinMatthews

theorem spectralKLBoundedKernel_pair_right_tendsto (M : ℝ → ℂ) (hM : Measurable M) (C : ℝ)
    (hb : ∀ t, 0 < t → ‖M t‖ ≤ C) (F : Lp ℂ 2 spectralKLSpectralMeasure)
    (G : ℕ → Lp ℂ 2 spectralKLSpectralMeasure) (g : Lp ℂ 2 spectralKLSpectralMeasure)
    (hG : Tendsto G atTop (𝓝 g)) :
    Tendsto (fun k => ∫ t, M t*F t*star (G k t) ∂spectralKLSpectralMeasure) atTop
      (𝓝 (∫ t, M t*F t*star (g t) ∂spectralKLSpectralMeasure)) := by
  have hs := spectralKLBoundedKernel_pair_tendsto (fun t => star (M t))
    (continuous_star.measurable.comp hM) C (fun t ht => by simpa only [norm_star] using hb t ht)
    G g F hG
  have he (U V : Lp ℂ 2 spectralKLSpectralMeasure) :
      star (∫ t, star (M t)*V t*star (U t) ∂spectralKLSpectralMeasure) =
        ∫ t, M t*U t*star (V t) ∂spectralKLSpectralMeasure := by
    change (starRingEnd ℂ) (∫ t, star (M t)*V t*star (U t) ∂spectralKLSpectralMeasure) = _
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards with t
    change star (star (M t)*V t*star (U t)) = _
    simp only [star_mul,star_star]
    ring
  have hc := (continuous_star.tendsto _).comp hs
  simpa only [Function.comp_def,he] using hc

theorem spectralWeylPhysicalBilinear_same_J_two_noncompact {a X B M : ℝ}
    (ha : 0 < a) (hX : 0 < X) (hB : 0 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M)
    (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) (hst : s*t = 1)
    (f g : ℝ → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hfc : ContinuousOn f (Ioi (0 : ℝ))) (hgc : ContinuousOn g (Ioi (0 : ℝ)))
    (hfL : MemLp f 2 spectralKLPhysicalMeasure) (hgL : MemLp g 2 spectralKLPhysicalMeasure)
    (hMoment : Integrable (fun x : ℝ => x^(-B)*‖g x‖) spectralKLPhysicalMeasure)
    (hf : ∀ z, 0 < z → ‖f z‖ ≤ M*z^B) :
    spectralWeylPhysicalBilinear s t f g X =
      ∫ r, spectralWeylJMultiplier r X*(spectralKLAnalysis (hfL.toLp f)) r*
        star ((spectralKLAnalysis (hgL.toLp g)) r) ∂spectralKLSpectralMeasure := by
  let F := spectralKLAnalysis (hfL.toLp f)
  let G (K : ℕ) := spectralKLAnalysis (spectralWeylCutoffLp a K (hgL.toLp g))
  let G₀ := spectralKLAnalysis (hgL.toLp g)
  have hstep (K : ℕ) : spectralWeylPhysicalBilinear s t f (spectralWeylProfileCutoff a K g) X =
      ∫ r, spectralWeylJMultiplier r X*F r*star (G K r) ∂spectralKLSpectralMeasure := by
    have hc := spectralWeylProfileCutoff_continuous ha K g hgc
    have hcp := spectralWeylProfileCutoff_compact ha K g
    have hp := spectralWeylProfileCutoff_positive ha K g
    rw [spectralWeylPhysicalBilinear_same_J_noncompact zero_lt_one hX hB hB₁ hM
      s t hs ht hst f _ hfm hfc hfL hc hcp hp hf]
    apply integral_congr_ae
    filter_upwards [spectralKLAnalysis_height_cutoff_ae ha K g hgc hgL,
      spectralKLAnalysis_compact_ae (spectralWeylProfileCutoff a K g) hc hcp hp] with r hseq hcompact
    change _ = spectralWeylJMultiplier r X*F r*
      star ((spectralKLAnalysis (spectralWeylCutoffLp a K (hgL.toLp g))) r)
    rw [hseq,hcompact]
  have hleft := spectralWeylPhysicalBilinear_cutoff_right_tendsto ha hX hB hB₁ hM
    s t f g hfm hgm hMoment hf
  rw [funext hstep] at hleft
  obtain ⟨C,_,hbound⟩ := spectralWeylJMultiplier_bounded_positive hX
  exact tendsto_nhds_unique hleft (spectralKLBoundedKernel_pair_right_tendsto
    (fun r => spectralWeylJMultiplier r X)
    (spectralWeylJMultiplier_measurable.comp (measurable_id.prodMk measurable_const)) C hbound F G G₀
    (spectralKLAnalysis_cutoff_tendsto ha (hgL.toLp g)))

theorem spectralWeylPhysicalBilinear_opposite_K_two_noncompact {a X B M : ℝ}
    (ha : 0 < a) (hX : 0 < X) (hB : 0 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M)
    (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) (hst : s*t = -1)
    (f g : ℝ → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hfc : ContinuousOn f (Ioi (0 : ℝ))) (hgc : ContinuousOn g (Ioi (0 : ℝ)))
    (hfL : MemLp f 2 spectralKLPhysicalMeasure) (hgL : MemLp g 2 spectralKLPhysicalMeasure)
    (hMoment : Integrable (fun x : ℝ => x^(-B)*‖g x‖) spectralKLPhysicalMeasure)
    (hf : ∀ z, 0 < z → ‖f z‖ ≤ M*z^B) :
    spectralWeylPhysicalBilinear s t f g X =
      ∫ r, spectralWeylKMultiplier r X*(spectralKLAnalysis (hfL.toLp f)) r*
        star ((spectralKLAnalysis (hgL.toLp g)) r) ∂spectralKLSpectralMeasure := by
  let F := spectralKLAnalysis (hfL.toLp f)
  let G (K : ℕ) := spectralKLAnalysis (spectralWeylCutoffLp a K (hgL.toLp g))
  let G₀ := spectralKLAnalysis (hgL.toLp g)
  have hstep (K : ℕ) : spectralWeylPhysicalBilinear s t f (spectralWeylProfileCutoff a K g) X =
      ∫ r, spectralWeylKMultiplier r X*F r*star (G K r) ∂spectralKLSpectralMeasure := by
    have hc := spectralWeylProfileCutoff_continuous ha K g hgc
    have hcp := spectralWeylProfileCutoff_compact ha K g
    have hp := spectralWeylProfileCutoff_positive ha K g
    rw [spectralWeylPhysicalBilinear_opposite_K_noncompact zero_lt_one hX hB hB₁ hM
      s t hs ht hst f _ hfm hfc hfL hc hcp hp hf]
    apply integral_congr_ae
    filter_upwards [spectralKLAnalysis_height_cutoff_ae ha K g hgc hgL,
      spectralKLAnalysis_compact_ae (spectralWeylProfileCutoff a K g) hc hcp hp] with r hseq hcompact
    change _ = spectralWeylKMultiplier r X*F r*
      star ((spectralKLAnalysis (spectralWeylCutoffLp a K (hgL.toLp g))) r)
    rw [hseq,hcompact]
  have hleft := spectralWeylPhysicalBilinear_cutoff_right_tendsto ha hX hB hB₁ hM
    s t f g hfm hgm hMoment hf
  rw [funext hstep] at hleft
  obtain ⟨C,_,hbound⟩ := spectralWeylKMultiplier_bounded_positive hX
  exact tendsto_nhds_unique hleft (spectralKLBoundedKernel_pair_right_tendsto
    (fun r => spectralWeylKMultiplier r X)
    (spectralWeylKMultiplier_measurable.comp (measurable_id.prodMk measurable_const)) C hbound F G G₀
    (spectralKLAnalysis_cutoff_tendsto ha (hgL.toLp g)))

end ArtinMatthews
