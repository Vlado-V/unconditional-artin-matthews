module

public import ArtinMatthews.SpectralKLAnalysisIntegral
public import ArtinMatthews.SpectralKLUnitary
public import ArtinMatthews.SpectralKLCompactAdjoint
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
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
public import Mathlib.Order.CompletePartialOrder
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

/-! The completed inverse is the literal K transform on physical compact
positive tests. Distribution uniqueness is applied only after the actual
adjoint/Fubini identity and local integrability have been proved. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace ArtinMatthews

theorem spectralKLAnalysis_compact_ae (f : ℝ → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ)) :
    spectralKLAnalysis ((spectralKLPhysical_compact_memLp f hf hfc hfp).toLp f) =ᵐ[spectralKLSpectralMeasure]
      spectralKLPhysicalAnalysisIntegral f := by
  let F : Lp ℂ 2 spectralKLPhysicalMeasure := (spectralKLPhysical_compact_memLp f hf hfc hfp).toLp f
  have hA : LocallyIntegrable (spectralKLPhysicalAnalysisIntegral f) spectralKLSpectralMeasure :=
    (spectralKLPhysicalAnalysisIntegral_continuous f hf hfc hfp).locallyIntegrable
  have hL : LocallyIntegrable (spectralKLAnalysis F) spectralKLSpectralMeasure :=
    (Lp.memLp _).locallyIntegrable (by norm_num)
  have hz : ∀ᵐ t ∂spectralKLSpectralMeasure, t ∈ Ioi (0 : ℝ) →
      spectralKLPhysicalAnalysisIntegral f t-spectralKLAnalysis F t = 0 := by
    apply isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hA.sub hL).locallyIntegrableOn _)
    intro g hg hgc hgp
    have hgs : tsupport (fun t : ℝ => (g t : ℂ)) ⊆ tsupport g := by
      unfold tsupport
      apply closure_mono
      intro t ht
      have ht' : (g t : ℂ) ≠ 0 := ht
      exact fun hg0 => ht' (by simp [hg0])
    let G : spectralKLTestSubmodule := ⟨(fun t : ℝ => (g t : ℂ)),
      Complex.ofRealCLM.contDiff.comp hg,hgc.comp_left Complex.ofReal_zero,hgs.trans hgp⟩
    have hi : inner ℂ (spectralKLTestToLp G) (spectralKLAnalysis F) =
        inner ℂ (spectralKLTestSynthesis G) F := by
      have h := spectralKLUnitary.inner_map_map (spectralKLTestToLp G) (spectralKLAnalysis F)
      simpa only [spectralKLUnitary_apply,spectralKLCompletedSynthesis_test,spectralKLSynthesis_analysis] using h.symm
    have hleft : inner ℂ (spectralKLTestToLp G) (spectralKLAnalysis F) =
        ∫ t : ℝ, (g t : ℂ)*spectralKLAnalysis F t ∂spectralKLSpectralMeasure := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [spectralKLTestToLp_coe G] with t ht
      rw [RCLike.inner_apply,ht]
      simp only [G,Complex.conj_ofReal]
      ring
    have hadj := spectralKL_compact_adjoint f hf hfc hfp G
    have heq : (∫ t : ℝ, (g t : ℂ)*spectralKLPhysicalAnalysisIntegral f t ∂spectralKLSpectralMeasure) =
        ∫ t : ℝ, (g t : ℂ)*spectralKLAnalysis F t ∂spectralKLSpectralMeasure := by
      have hright : (∫ t : ℝ, (starRingEnd ℂ) (G.val t)*spectralKLPhysicalAnalysisIntegral f t ∂spectralKLSpectralMeasure) =
          ∫ t : ℝ, (g t : ℂ)*spectralKLPhysicalAnalysisIntegral f t ∂spectralKLSpectralMeasure := by
        apply integral_congr_ae
        filter_upwards with t
        simp only [G,Complex.conj_ofReal]
      rw [hright] at hadj
      exact hadj.symm.trans (hi.symm.trans hleft)
    have htest : (∫ t : ℝ, g t • spectralKLPhysicalAnalysisIntegral f t ∂spectralKLSpectralMeasure) =
        ∫ t : ℝ, g t • spectralKLAnalysis F t ∂spectralKLSpectralMeasure := by
      simpa only [Complex.real_smul] using heq
    simp only [Pi.sub_apply,smul_sub]
    rw [integral_sub (hA.integrable_smul_left_of_hasCompactSupport hg.continuous hgc)
      (hL.integrable_smul_left_of_hasCompactSupport hg.continuous hgc),htest,sub_self]
  filter_upwards [hz,spectralKLPositiveWeightMeasure_ae_pos spectralKLPlancherelWeight] with t ht hp
  exact (sub_eq_zero.mp (ht hp)).symm

theorem spectralKLPhysicalAnalysisIntegral_memLp (f : ℝ → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ)) :
    MemLp (spectralKLPhysicalAnalysisIntegral f) 2 spectralKLSpectralMeasure :=
  (memLp_congr_ae (spectralKLAnalysis_compact_ae f hf hfc hfp)).mp (Lp.memLp _)

theorem spectralKLPhysicalAnalysisIntegral_synthesis (f : ℝ → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ)) :
    spectralKLCompletedSynthesis ((spectralKLPhysicalAnalysisIntegral_memLp f hf hfc hfp).toLp
      (spectralKLPhysicalAnalysisIntegral f)) = (spectralKLPhysical_compact_memLp f hf hfc hfp).toLp f := by
  have hLp : (spectralKLPhysicalAnalysisIntegral_memLp f hf hfc hfp).toLp (spectralKLPhysicalAnalysisIntegral f) =
      spectralKLAnalysis ((spectralKLPhysical_compact_memLp f hf hfc hfp).toLp f) := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp _).trans (spectralKLAnalysis_compact_ae f hf hfc hfp).symm
  rw [hLp,spectralKLSynthesis_analysis]

end ArtinMatthews
