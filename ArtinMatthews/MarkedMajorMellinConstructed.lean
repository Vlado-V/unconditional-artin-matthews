module

public import ArtinMatthews.MarkedMajorMellinCutoff
public import ArtinMatthews.MarkedMajorFourierSeparationBase
public import ArtinMatthews.MarkedMajorMellinKernel
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.MarkedMajorMellinKernelSeparation
public import ArtinMatthews.MarkedMajorMellinUniform
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

/-! The literal source Mellin coefficient using constructed positive-support cutoffs. -/
namespace ArtinMatthews
open Set MeasureTheory Complex
noncomputable section

def markedMajorConstructedKernel (ψ : SchwartzMap ℝ ℂ) {a b R X : ℝ}
    (ha : 0 < a) (hab : a < b) (hψ : tsupport ψ ⊆ Icc (-R) R)
    (hX : 0 < X) (theta : ℝ) : SchwartzMap (ℝ × ℝ) ℂ :=
  markedMajorMellinKernel (majorMellinPositiveCutoff a b ha hab)
    (majorMellinPositiveCutoff a b ha hab) ψ (half_pos ha) hX
    (majorMellinPositiveCutoff_tsupport a b ha hab)
    (majorMellinPositiveCutoff_tsupport a b ha hab) hψ theta

def markedMajorConstructedCoefficient (ψ : SchwartzMap ℝ ℂ) {a b R X : ℝ}
    (ha : 0 < a) (hab : a < b) (hψ : tsupport ψ ⊆ Icc (-R) R)
    (hX : 0 < X) (theta : ℝ) : SchwartzMap (ℝ × ℝ) ℂ :=
  markedMajorFourierCoefficient (markedMajorConstructedKernel ψ ha hab hψ hX theta)

theorem markedMajor_constructed_mellin_separation (ψ : SchwartzMap ℝ ℂ)
    {a b R X w w' : ℝ} (ha : 0 < a) (hab : a < b)
    (hψ : tsupport ψ ⊆ Icc (-R) R) (hX : 0 < X) (theta : ℝ)
    (hw : w ∈ Icc a b) (hw' : w' ∈ Icc a b) :
    ψ (X*(w-w'))*OAI.Problem337.RealPhase.phase (theta*(X*(w-w'))) =
      (X : ℂ)⁻¹ * ∫ t : ℝ, ∫ s : ℝ,
        markedMajorConstructedCoefficient ψ ha hab hψ hX theta (t/X,s) *
          (Complex.exp (I*(t : ℂ)*(Real.log w : ℂ)) *
            Complex.exp (I*((s-t : ℝ) : ℂ)*(Real.log w' : ℂ))) :=
  markedMajor_actual_mellin_separation _ _ ψ (half_pos ha) hX
    (majorMellinPositiveCutoff_tsupport a b ha hab)
    (majorMellinPositiveCutoff_tsupport a b ha hab) hψ theta (ha.trans_le hw.1) (ha.trans_le hw'.1)
    (majorMellinPositiveCutoff_plateau a b ha hab hw)
    (majorMellinPositiveCutoff_plateau a b ha hab hw')

theorem markedMajor_constructed_mellin_integrable (ψ : SchwartzMap ℝ ℂ)
    {a b R X w w' : ℝ} (ha : 0 < a) (hab : a < b)
    (hψ : tsupport ψ ⊆ Icc (-R) R) (hX : 0 < X) (theta : ℝ)
    (hw : w ∈ Icc a b) (hw' : w' ∈ Icc a b) :
    Integrable (fun p : ℝ × ℝ =>
      markedMajorConstructedCoefficient ψ ha hab hψ hX theta (p.1/X,p.2) *
        (Complex.exp (I*(p.1 : ℂ)*(Real.log w : ℂ)) *
          Complex.exp (I*((p.2-p.1 : ℝ) : ℂ)*(Real.log w' : ℂ)))) :=
  markedMajor_actual_mellin_integrable _ _ ψ (half_pos ha) hX
    (majorMellinPositiveCutoff_tsupport a b ha hab)
    (majorMellinPositiveCutoff_tsupport a b ha hab) hψ theta (ha.trans_le hw.1) (ha.trans_le hw'.1)

theorem markedMajorConstructedKernel_uniform_L1_bounds (ψ : SchwartzMap ℝ ℂ)
    {a b R : ℝ} (ha : 0 < a) (hab : a < b)
    (hψ : tsupport ψ ⊆ Icc (-R) R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k ≤ n, ∀ X ≥ 1, ∀ hX : 0 < X, ∀ theta : ℝ,
      (∫ p : ℝ × ℝ, ‖iteratedFDeriv ℝ k
        (markedMajorConstructedKernel ψ ha hab hψ hX theta) p‖) ≤ C*(1+|theta|)^k := by
  obtain ⟨C,hC,hb⟩ := markedMajorMellinKernel_uniform_L1_bounds
    (majorMellinPositiveCutoff a b ha hab) (majorMellinPositiveCutoff a b ha hab) ψ (half_pos ha)
    (majorMellinPositiveCutoff_tsupport a b ha hab)
    (majorMellinPositiveCutoff_tsupport a b ha hab) hψ n
  exact ⟨C,hC,fun k hk X hX _ theta => hb k hk X hX theta⟩

end
end ArtinMatthews
