module

public import OAI.NumberTheory.EgyptianFractions.RealPhaseEnvelope
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! The actual smooth determinant cutoff is separated by Fourier inversion.
Its Fourier tail is bounded by genuine Schwartz moments, not by an assumed
rapid-decay estimate. -/
namespace ArtinMatthews
open MeasureTheory
open scoped FourierTransform

/-- Fourier inversion gives precisely the shifted determinant frequency in
PD (mem:cutoff-fourier), with the source `2π` convention. -/
theorem marked_minor_cutoff_fourier (ψ : SchwartzMap ℝ ℂ) (θ z Y : ℝ) :
    ψ (z/Y) * OAI.Problem337.RealPhase.phase (θ*z) =
      ∫ u : ℝ, (𝓕 ψ) u * OAI.Problem337.RealPhase.phase ((θ+u/Y)*z) := by
  have hfun := ψ.continuous.fourierInv_fourier_eq ψ.integrable (𝓕 ψ).integrable
  have hinv := congrFun hfun (z/Y)
  rw [Real.fourierInv_eq'] at hinv
  have hphase (u : ℝ) : Complex.exp
      ((2*Real.pi*inner ℝ u (z/Y) : ℝ) * Complex.I) =
      OAI.Problem337.RealPhase.phase (u*(z/Y)) := by
    unfold OAI.Problem337.RealPhase.phase
    congr 1
    simp only [RCLike.inner_apply,conj_trivial]
    push_cast
    ring
  simp only [hphase,smul_eq_mul] at hinv
  rw [← SchwartzMap.fourier_coe ψ] at hinv
  calc
    _ = (∫ u : ℝ, OAI.Problem337.RealPhase.phase (u*(z/Y))*(𝓕 ψ) u) *
        OAI.Problem337.RealPhase.phase (θ*z) := by rw [hinv]
    _ = ∫ u : ℝ, (OAI.Problem337.RealPhase.phase (u*(z/Y))*(𝓕 ψ) u) *
        OAI.Problem337.RealPhase.phase (θ*z) := (integral_mul_const _ _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [mul_right_comm,← OAI.Problem337.RealPhase.phase_add,mul_comm]
      congr 1
      congr 1
      ring

/-- The finite weighted Fourier moment of the actual fixed cutoff. -/
noncomputable def markedMinorCutoffMoment (ψ : SchwartzMap ℝ ℂ) (n : ℕ) : ℝ :=
  ∫ u : ℝ, ‖u‖^n*‖(𝓕 ψ) u‖

/-- The Fourier tail of the actual cutoff has every integral power saving. -/
theorem marked_minor_cutoff_tail (ψ : SchwartzMap ℝ ℂ) (n : ℕ) {R : ℝ} (hR : 0 < R) :
    (∫ u : ℝ in {u | R < ‖u‖}, ‖(𝓕 ψ) u‖) ≤
      (R^n)⁻¹ * markedMinorCutoffMoment ψ n := by
  let F : SchwartzMap ℝ ℂ := 𝓕 ψ
  let S : Set ℝ := {u | R < ‖u‖}
  have hS : MeasurableSet S := measurableSet_lt measurable_const measurable_norm
  have hF : Integrable (fun u : ℝ => ‖F u‖) := F.integrable.norm
  have hW := F.integrable_pow_mul volume n
  have hscale := hW.const_mul ((R^n)⁻¹)
  have hpoint (u : ℝ) (hu : u ∈ S) :
      ‖F u‖ ≤ (R^n)⁻¹*(‖u‖^n*‖F u‖) := by
    have hRn : 0 < R^n := pow_pos hR n
    have hp := pow_le_pow_left₀ hR.le hu.le n
    have hm := mul_le_mul_of_nonneg_right hp (norm_nonneg (F u))
    calc
      _ = ((R^n)*‖F u‖)/(R^n) := by field_simp
      _ ≤ (‖u‖^n*‖F u‖)/(R^n) := div_le_div_of_nonneg_right hm hRn.le
      _ = _ := by ring
  calc
    _ ≤ ∫ u : ℝ in S, (R^n)⁻¹*(‖u‖^n*‖F u‖) :=
      setIntegral_mono_on hF.integrableOn hscale.integrableOn hS hpoint
    _ ≤ ∫ u : ℝ, (R^n)⁻¹*(‖u‖^n*‖F u‖) :=
      setIntegral_le_integral hscale (Filter.Eventually.of_forall (fun u => by positivity))
    _ = _ := by rw [integral_const_mul]; rfl

end ArtinMatthews
