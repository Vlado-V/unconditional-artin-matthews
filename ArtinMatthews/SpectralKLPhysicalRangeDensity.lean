module

public import ArtinMatthews.SpectralKLExponentialQuotient
public import ArtinMatthews.SpectralKLExponentialPolynomial
public import ArtinMatthews.SpectralComplexPolynomialApproximation
public import ArtinMatthews.SpectralKLPhysicalTestDensity
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

/-! Actual physical range density from compact positive tests and proved
Weierstrass approximation, with q(x)^2 as the integrable error weight. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

def spectralKLAnchorLp : Lp ℂ 2 spectralKLPhysicalMeasure :=
  spectralKLExponentialAnchor_memLp.toLp (fun x : ℝ => (spectralKLExponentialAnchor x : ℂ))

theorem spectralKLAnchorLp_norm_sq :
    ‖spectralKLAnchorLp‖^2 = ∫ x : ℝ, (spectralKLExponentialAnchor x)^2 ∂spectralKLPhysicalMeasure := by
  unfold spectralKLAnchorLp
  rw [spectral_toLp_norm_sq]
  apply integral_congr_ae
  filter_upwards with x
  rw [Complex.norm_real,Real.norm_eq_abs,sq_abs]

theorem spectralKLExponentialPolynomial_approximation_bound (f : ℝ → ℂ)
    (hf : MemLp f 2 spectralKLPhysicalMeasure) (P : Polynomial ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hP : ∀ t ∈ Icc (0 : ℝ) 1, ‖P.eval (t : ℂ)-spectralKLExponentialQuotient f t‖ ≤ δ) :
    ‖spectralKLExponentialPolynomialToLp P-hf.toLp f‖ ≤ δ*‖spectralKLAnchorLp‖ := by
  have hpoint (x : ℝ) (hx : 0 < x) :
      ‖spectralKLExponentialPolynomial P x-f x‖ ≤ δ*spectralKLExponentialAnchor x := by
    have hr : Real.exp (-x) ∈ Icc (0 : ℝ) 1 :=
      ⟨(Real.exp_pos _).le,(Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)).le⟩
    rw [← spectralKLExponentialQuotient_recover f hx]
    rw [show spectralKLExponentialPolynomial P x-
        (spectralKLExponentialAnchor x : ℂ)*spectralKLExponentialQuotient f (Real.exp (-x)) =
      (spectralKLExponentialAnchor x : ℂ)*(P.eval (Real.exp (-x) : ℂ)-
        spectralKLExponentialQuotient f (Real.exp (-x))) by unfold spectralKLExponentialPolynomial; ring]
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (spectralKLExponentialAnchor_pos hx).le]
    exact (mul_le_mul_of_nonneg_left (hP _ hr) (spectralKLExponentialAnchor_pos hx).le).trans_eq (mul_comm _ _)
  have hsq : ‖spectralKLExponentialPolynomialToLp P-hf.toLp f‖^2 ≤ δ^2*‖spectralKLAnchorLp‖^2 := by
    unfold spectralKLExponentialPolynomialToLp
    rw [← MemLp.toLp_sub,spectral_toLp_norm_sq,spectralKLAnchorLp_norm_sq]
    have hi := (memLp_two_iff_integrable_sq_norm
      ((spectralKLExponentialPolynomial_memLp P).sub hf).aestronglyMeasurable).mp
      ((spectralKLExponentialPolynomial_memLp P).sub hf)
    calc
      _ ≤ ∫ x : ℝ, δ^2*(spectralKLExponentialAnchor x)^2 ∂spectralKLPhysicalMeasure := by
        apply integral_mono_ae hi (spectralKLExponentialAnchor_square_integrable.const_mul (δ^2))
        filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx
        dsimp only [Pi.sub_apply]
        calc
          _ ≤ (δ*spectralKLExponentialAnchor x)^2 :=
            (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hδ (spectralKLExponentialAnchor_pos hx).le)).mpr (hpoint x hx)
          _ = _ := by ring
      _ = _ := integral_const_mul _ _
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hδ (norm_nonneg _))).mp
  simpa only [mul_pow] using hsq

theorem spectralKLCompletedSynthesis_denseRange : DenseRange spectralKLCompletedSynthesis := by
  have hs : {u : Lp ℂ 2 spectralKLPhysicalMeasure | ∃ f : ℝ → ℂ,
      u =ᵐ[spectralKLPhysicalMeasure] f ∧ HasCompactSupport f ∧ Continuous f ∧ tsupport f ⊆ Ioi (0 : ℝ)} ⊆
      closure (Set.range spectralKLCompletedSynthesis) := by
    intro u hu
    obtain ⟨f,huf,hfc,hcont,hfp⟩ := hu
    have hfm : MemLp f 2 spectralKLPhysicalMeasure := (memLp_congr_ae huf).mp (Lp.memLp u)
    have hflp : hfm.toLp f = u := by
      apply Lp.ext
      exact hfm.coeFn_toLp.trans huf.symm
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let δ : ℝ := ε/(‖spectralKLAnchorLp‖+1)
    have hδ : 0 < δ := div_pos hε (by positivity)
    have hden : ‖spectralKLAnchorLp‖+1 ≠ 0 := ne_of_gt (by positivity)
    have hδeq : δ*(‖spectralKLAnchorLp‖+1) = ε := by dsimp [δ]; field_simp
    obtain ⟨P,hP⟩ := spectral_complex_polynomial_approximation (spectralKLExponentialQuotient f)
      (spectralKLExponentialQuotient_continuous f hcont hfc hfp).continuousOn δ hδ
    refine ⟨spectralKLExponentialPolynomialToLp P,spectralKLExponentialPolynomialToLp_mem_range P,?_⟩
    have hn := spectralKLExponentialPolynomial_approximation_bound f hfm P δ hδ.le (fun t ht => (hP t ht).le)
    have hclose : ‖spectralKLExponentialPolynomialToLp P-u‖ < ε := by
      rw [hflp] at hn
      have hscale : δ*‖spectralKLAnchorLp‖ < ε := by nlinarith
      exact hn.trans_lt hscale
    rw [dist_comm,dist_eq_norm]
    exact hclose
  intro u
  exact (closure_minimal hs isClosed_closure) (spectralKLPhysicalMeasure_dense_compact_positive u)

theorem spectralKLCompletedSynthesis_surjective : Function.Surjective spectralKLCompletedSynthesis := by
  have hc : IsClosed (Set.range spectralKLCompletedSynthesis) :=
    spectralKLCompletedSynthesis.isometry.isClosedEmbedding.isClosed_range
  intro u
  have hu := spectralKLCompletedSynthesis_denseRange u
  rwa [hc.closure_eq] at hu

end ArtinMatthews
