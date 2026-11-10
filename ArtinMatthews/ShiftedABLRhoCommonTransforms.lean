module

public import ArtinMatthews.ShiftedABLRhoScale
public import ArtinMatthews.ShiftedABLSourceBudget
public import ArtinMatthews.SpectralJForwardTransform
public import ArtinMatthews.SpectralJHolomorphicCoefficient
public import ArtinMatthews.SpectralJLogConductor
public import ArtinMatthews.SpectralJLogHolomorphicBounds
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

/-! The common compact test from the exact rho separation has genuine
principal, complementary and odd-order transform bounds. -/

noncomputable section
open Set OAI
open scoped ContDiff
namespace ArtinMatthews

theorem shiftedABLRhoCommonTest_eq_oscillatory (a u : ℝ) :
    shiftedABLRhoCommonTest a u =
      spectralJOscillatoryLogProfile (fun v => (shiftedABLRhoPlateau v : ℂ))
        (fun v => 2*Real.pi*v) a u := by
  funext x
  unfold shiftedABLRhoCommonTest spectralJOscillatoryLogProfile spectralJLogProfile
  split_ifs with hx
  · unfold markedOscillatoryFamily markedOscillatoryPhase markedRealOscillator FourierBridge.logPhase
    push_cast
    congr 2
    ring
  · rfl

theorem shiftedABLRhoPlateau_complex_properties :
    ContDiff ℝ ∞ (fun v => (shiftedABLRhoPlateau v : ℂ)) ∧
      tsupport (fun v => (shiftedABLRhoPlateau v : ℂ)) ⊆ Icc (-Real.log 3) (Real.log 2) := by
  refine ⟨Complex.ofRealCLM.contDiff.comp shiftedABLRhoPlateau_properties.1, ?_⟩
  apply Subset.trans _ shiftedABLRhoPlateau_properties.2.2.1
  apply closure_mono
  intro v hv hv₀
  exact hv (by simp [hv₀])

theorem shiftedABLRhoBlockScale_eq_abl {F L n r : ℕ} (hF : 0 < F) (R : ℝ) :
    shiftedABLRhoBlockScale L n r R =
      4*Real.pi*ablTheorem24BesselScale (3*(L : ℝ)/(F : ℝ)) R n r F := by
  have hF₀ : (F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hF.ne'
  unfold shiftedABLRhoBlockScale ablTheorem24BesselScale
  rw [show (F : ℝ)*Real.sqrt (r : ℝ)*(3*(L : ℝ)/(F : ℝ)) =
      Real.sqrt (r : ℝ)*(3*(L : ℝ)) by field_simp [hF₀]]
  ring

theorem shiftedABLRhoCommonTest_conductor_estimates (Rmax δ : ℝ)
    (hRmax : 0 ≤ Rmax) (hδ : 0 < δ) (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a u Z P : ℝ, 0 < a → a ≤ Rmax → 1+|u| ≤ Z →
      1 ≤ P → P⁻¹ ≤ a →
      (∀ t : ℝ, ‖spectralJForwardTransform (shiftedABLRhoCommonTest a u) (t : ℂ)‖ ≤
        C*P^δ/(1+|t|/Z)^J) ∧
      (∀ κ : ℝ, 0 ≤ κ → κ ≤ 1/4 →
        ‖spectralJForwardTransform (shiftedABLRhoCommonTest a u) ((κ : ℂ)*Complex.I)‖ ≤
          C*P^δ*a^(-2*κ)) := by
  have hB : ContDiff ℝ ∞ (fun v : ℝ => 2*Real.pi*v) := by fun_prop
  obtain ⟨C,hC,h⟩ := spectralJOscillatoryLogProfile_conductor_estimates _ _
    shiftedABLRhoPlateau_complex_properties.1 hB shiftedABLRhoPlateau_complex_properties.2
    Rmax hRmax δ hδ J
  refine ⟨C,hC,?_⟩
  intro a u Z P ha haR hZ hP hPa
  rw [shiftedABLRhoCommonTest_eq_oscillatory]
  exact h a u Z P ha haR hZ hP hPa

theorem shiftedABLRhoCommonTest_holomorphic_factorial (Rmax : ℝ) (hRmax : 0 ≤ Rmax) :
    ∃ C : ℝ, 0 < C ∧ ∀ a u : ℝ, 0 < a → a ≤ Rmax → ∀ k : ℕ, 2 ≤ k →
      ‖spectralJHolomorphicCoefficient (shiftedABLRhoCommonTest a u) k‖ ≤
        C*a^(k-1)/((k-2).factorial : ℝ) := by
  have hB : ContDiff ℝ ∞ (fun v : ℝ => 2*Real.pi*v) := by fun_prop
  obtain ⟨C,hC,h⟩ := spectralJOscillatoryLogProfile_holomorphic_factorial _ _
    shiftedABLRhoPlateau_complex_properties.1 hB shiftedABLRhoPlateau_complex_properties.2
    Rmax hRmax
  refine ⟨C,hC,?_⟩
  intro a u ha haR k hk
  rw [shiftedABLRhoCommonTest_eq_oscillatory]
  have hb : a*Real.exp (Real.log 2)/2 = a := by
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    ring
  simpa only [hb] using h a u ha haR k hk

end ArtinMatthews
