module

public import ArtinMatthews.SpectralKFrameLogWindow
public import ArtinMatthews.SpectralKLWeightedMeasures
public import ArtinMatthews.SpectralCuspFourierProjection
public import ArtinMatthews.SpectralKFrameRetainedModes
public import ArtinMatthews.SpectralKFrameTransform
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

/-! A finite family of actual compact real profiles retains a uniform
principal K moment on each dyadic band. -/

noncomputable section
open Set MeasureTheory OAI.CubicEisenstein
open scoped ContDiff BigOperators
namespace ArtinMatthews

def spectralCompactRealKTransform (F : ℝ → ℝ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, (F x : ℂ)*schlafliBesselK ((t : ℂ)*Complex.I) x ∂spectralKLPhysicalMeasure

def spectralKFrameProfileBound (T : ℝ) (F : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ tsupport F ⊆ Ici (T/16) ∧
    (∫ x : ℝ, (F x)^2 ∂spectralKLPhysicalMeasure) ≤ spectralKFrameLength

theorem spectralKFrame_exists_compact_phase_profiles :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, (1/2 : ℝ) ≤ T →
      ∃ modes : Finset ℤ, ∃ F G : ℤ → ℝ → ℝ, (modes.card : ℝ) ≤ C*T ∧
        (∀ m : ℤ, spectralKFrameProfileBound T (F m) ∧ spectralKFrameProfileBound T (G m)) ∧
        ∀ t : ℝ, T ≤ 1+|t| → 1+|t| ≤ 2*T →
          (Real.pi^2*spectralKFrameLength/5184)/(T*Real.cosh (Real.pi*t)) ≤
            ∑ m ∈ modes, (‖spectralCompactRealKTransform (F m) t‖^2+
              ‖spectralCompactRealKTransform (G m) t‖^2) := by
  let L := spectralKFrameLength
  have hL : 0 < L := spectralKFrameLength_pos
  obtain ⟨ψ,D,_,hψ,hSupp,h01,hOne,hDψ⟩ := spectralKFrameWindow_exists
  obtain ⟨C,hC,hframe⟩ := spectralKFrameLogTest_exists_retained_modes ψ hψ hSupp h01 hOne hDψ
  refine ⟨C,hC,?_⟩
  intro T hhalf
  have hT : 0 < T := by linarith
  obtain ⟨modes,hcard,hretained⟩ := hframe T hhalf
  let χr (m : ℤ) (x : ℝ) := (cuspFourierPhase L m x).re
  let χi (m : ℤ) (x : ℝ) := (cuspFourierPhase L m x).im
  let F (m : ℤ) := spectralKFramePhysicalTest ψ (χr m) T
  let G (m : ℤ) := spectralKFramePhysicalTest ψ (χi m) T
  refine ⟨modes,F,G,hcard,?_,?_⟩
  · intro m
    have hProfile (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχ1 : ∀ x, |χ x| ≤ 1) :
        spectralKFrameProfileBound T (spectralKFramePhysicalTest ψ χ T) :=
      ⟨spectralKFramePhysicalTest_contDiff ψ χ hψ hχ hSupp T hT,
        spectralKFramePhysicalTest_compact ψ χ hSupp T hT,
        fun _ hx => (spectralKFramePhysicalTest_support ψ χ hSupp T hT hx).1,
        spectralKFramePhysicalTest_mass_le ψ χ hψ hχ hSupp h01 hχ1 T hT⟩
    exact ⟨hProfile _ (Complex.reCLM.contDiff.comp (cuspFourierPhase_contDiff L m))
      (fun x => (Complex.abs_re_le_norm _).trans_eq (cuspFourierPhase_norm L m x)),
      hProfile _ (Complex.imCLM.contDiff.comp (cuspFourierPhase_contDiff L m))
      (fun x => (Complex.abs_im_le_norm _).trans_eq (cuspFourierPhase_norm L m x))⟩
  · intro t ht₁ ht₂
    let c (m : ℤ) := fourierCoeffOn spectralKFrameLength_pos
      (fun u => (spectralKFrameLogTest ψ T t u : ℂ)) m
    have heq :
        (∑ m ∈ modes, (‖spectralCompactRealKTransform (F m) t‖^2+
          ‖spectralCompactRealKTransform (G m) t‖^2)) =
        L^2*(∑ m ∈ modes, ‖c m‖^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      exact spectralKFramePhysicalTest_principal_phase_sq ψ hψ hSupp T t hT m
    rw [heq]
    calc
      _ = L^2*(spectralKSquareMoment 0 t/(1296*L*T)) := by
        rw [spectralKSquareMoment_zero]
        change (Real.pi^2*L/5184)/(T*Real.cosh (Real.pi*t)) = _
        field_simp [hL.ne',hT.ne',(Real.cosh_pos _).ne']
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hretained t ht₁ ht₂) (sq_nonneg _)

end ArtinMatthews
