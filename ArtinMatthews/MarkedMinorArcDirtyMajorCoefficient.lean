module

public import ArtinMatthews.MarkedMinorArcRawEdgeDetector
public import ArtinMatthews.MarkedMinorArcDirtyMajorSupport
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

/-! Actual major comparison coefficient contraction, retaining the true
remaining-memory damping and every old/fresh indexed choice. -/
noncomputable section
namespace ArtinMatthews

theorem markedDirtyMajor_detector_norm_le (ψ : ℝ → ℂ) {Q Y : ℝ}
    (hQ : 0 ≤ Q) (hY : 0 < Y) {W : ℝ} (hW : 0 ≤ W) (hψ : ∀ t, ‖ψ t‖ ≤ W)
    (b a t : ℤ) : ‖markedRawEdgeMajorDetector ψ Q Y b a t‖ ≤ W*(4*Q^3/Y) := by
  unfold markedRawEdgeMajorDetector
  rw [norm_mul]
  exact mul_le_mul (hψ _) (markedBanMajorKernel_norm_le hQ hY _) (norm_nonneg _) hW

theorem markedDirtyMajor_coefficient_norm_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ η : ℝ → ℂ) (d₀ : ℝ) {Y Q : ℝ} (hY : 0 < Y) (hQ : 0 ≤ Q)
    {ρ H W : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hH : 0 ≤ H) (hW : 0 ≤ W)
    (hη : ∀ t, ‖η t‖ ≤ H) (hψ : ∀ t, ‖ψ t‖ ≤ W)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (hχ : ∀ s, ‖χ s‖ ≤ 1)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedRawEdgeChoice hZ s) :
    ‖markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeMajorDetector ψ Q Y) s choice‖ ≤
      H^2*(W*(4*Q^3/Y))*ρ^(markedRawPendingHits (markedRawEdgeTargetMemory hZ s choice)
        choice.target.1 (hZ _ choice.target.2)) := by
  classical
  by_cases hn : markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeMajorDetector ψ Q Y) s choice=0
  · rw [hn,norm_zero]
    positivity
  have hs := markedRawEdgeChoiceDetectorCoefficient_support hZ η d₀ Y ρ χ _ s choice hn
  have hD : 0 < (markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1:ℝ) := by
    exact_mod_cast markedRawCopiedProduct_pos ((markedRawActiveSplit pads) s.2.1).1
  have hd₀ : 0 ≤ d₀ := by linarith [hs.1.2]
  have hscale : ‖((d₀/(markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1:ℝ):ℝ):ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_of_nonneg (div_nonneg hd₀ hD.le)]
    exact (div_le_one hD).mpr hs.1.1
  have hsource := markedRawPendingDamping_norm_le s.2.2 s.1.1 (hZ _ s.1.2) hρ₀ hρ₁
  have hsourceEndpoint := markedRawEndpointFactor_norm_le hZ (by norm_num : (0:ℝ)≤1) le_rfl χ hχ s
  have htargetEndpoint := markedRawEndpointFactor_norm_le hZ (by norm_num : (0:ℝ)≤1) le_rfl χ hχ
    (markedRawEdgeTargetState hZ s choice)
  have htarget : ‖((ρ^(markedRawPendingHits (markedRawEdgeTargetState hZ s choice).2.2
      (markedRawEdgeTargetState hZ s choice).1.1 (hZ _ (markedRawEdgeTargetState hZ s choice).1.2)):ℝ):ℂ)‖ =
      ρ^(markedRawPendingHits (markedRawEdgeTargetMemory hZ s choice) choice.target.1 (hZ _ choice.target.2)) := by
    rw [Complex.norm_real,Real.norm_of_nonneg (pow_nonneg hρ₀ _)]
    rfl
  have hdiv : (markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1:ℤ) ∣
      markedMinorIntegerDet s.1.1 (markedRawEdgeTargetState hZ s choice).1.1 := hs.2.1
  unfold markedRawEdgeChoiceDetectorCoefficient
  dsimp only
  rw [ite_eq_left hs.1,ite_eq_left hdiv,ite_eq_right hs.2.2.1]
  simp only [norm_mul,htarget]
  calc
    _ ≤ 1*1*1*H*H*(W*(4*Q^3/Y))*(ρ^(markedRawPendingHits (markedRawEdgeTargetMemory hZ s choice)
          choice.target.1 (hZ _ choice.target.2)))*1 := by
      gcongr <;> first
        | exact hscale
        | exact hsource
        | exact hsourceEndpoint
        | exact htargetEndpoint
        | apply hη
        | exact markedDirtyMajor_detector_norm_le ψ hQ hY hW hψ _ _ _
    _ = _ := by ring

end ArtinMatthews
