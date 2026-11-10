module

public import ArtinMatthews.MarkedMajorMellinKernel
public import ArtinMatthews.MarkedMajorFourierSeparationBase
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.MarkedMajorFourierSeparationExp
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

namespace ArtinMatthews
open MeasureTheory Complex
noncomputable section

theorem markedMajor_actual_mellin_separation (ρ ρ' ψ : SchwartzMap ℝ ℂ)
    {a b R X w w' : ℝ} (ha : 0 < a) (hX : 0 < X)
    (hρ : tsupport ρ ⊆ Set.Icc a b) (hρ' : tsupport ρ' ⊆ Set.Icc a b)
    (hψ : tsupport ψ ⊆ Set.Icc (-R) R) (theta : ℝ)
    (hw : 0 < w) (hw' : 0 < w') (hwρ : ρ w = 1) (hwρ' : ρ' w' = 1) :
    ψ (X*(w-w'))*OAI.Problem337.RealPhase.phase (theta*(X*(w-w'))) =
      (X : ℂ)⁻¹ * ∫ t : ℝ, ∫ s : ℝ,
        markedMajorFourierCoefficient (markedMajorMellinKernel ρ ρ' ψ ha hX hρ hρ' hψ theta) (t/X,s) *
          (Complex.exp (I*(t : ℂ)*(Real.log w : ℂ)) *
            Complex.exp (I*((s-t : ℝ) : ℂ)*(Real.log w' : ℂ))) := by
  rw [← markedMajorMellinKernel_on_source ρ ρ' ψ hX.ne' hw hw' hwρ hwρ' theta]
  exact markedMajor_mellin_separation_exp
    (markedMajorMellinKernel ρ ρ' ψ ha hX hρ hρ' hψ theta) hX hw hw'

theorem markedMajor_actual_mellin_integrable (ρ ρ' ψ : SchwartzMap ℝ ℂ)
    {a b R X w w' : ℝ} (ha : 0 < a) (hX : 0 < X)
    (hρ : tsupport ρ ⊆ Set.Icc a b) (hρ' : tsupport ρ' ⊆ Set.Icc a b)
    (hψ : tsupport ψ ⊆ Set.Icc (-R) R) (theta : ℝ)
    (hw : 0 < w) (hw' : 0 < w') :
    Integrable (fun p : ℝ × ℝ =>
      markedMajorFourierCoefficient (markedMajorMellinKernel ρ ρ' ψ ha hX hρ hρ' hψ theta) (p.1/X,p.2) *
        (Complex.exp (I*(p.1 : ℂ)*(Real.log w : ℂ)) *
          Complex.exp (I*((p.2-p.1 : ℝ) : ℂ)*(Real.log w' : ℂ)))) :=
  markedMajor_mellin_separated_exp_integrable
    (markedMajorMellinKernel ρ ρ' ψ ha hX hρ hρ' hψ theta) hX hw hw'

end
end ArtinMatthews
