module

public import ArtinMatthews.SourceKPAdelicDefectRadialFormula
public import ArtinMatthews.SourceKPFiniteLevelTopology
public import ArtinMatthews.SourceAdelicHeightFibers
public import ArtinMatthews.SourceKPAdelicSectionParameterContinuity
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

/-! Joint continuity of the actual radial defect summands in the
spectral parameter and an arbitrary archimedean fiber. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField AdeleRing MatrixGroups ContDiff
noncomputable section

theorem sourceKPAdelicDefectCoefficient_continuous (T : ℝ) :
    Continuous (fun p : ℂ × ℝ => sourceKPAdelicDefectCoefficient T p.1 p.2) := by
  have hφ : ContDiff (ℝ) (2 : ℕ∞ω) (sourceKPAdelicHeightCutoff T) :=
    (sourceKPAdelicHeightCutoff_contDiff T).of_le (by simp)
  have hφ₁ : ContDiff (ℝ) (1 : ℕ∞ω) (deriv (sourceKPAdelicHeightCutoff T)) := hφ.deriv'
  have hφ₂ : ContDiff (ℝ) (0 : ℕ∞ω) (deriv (deriv (sourceKPAdelicHeightCutoff T))) := hφ₁.deriv'
  have h₁ := hφ₁.continuous
  have h₂ := hφ₂.continuous
  unfold sourceKPAdelicDefectCoefficient
  fun_prop

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicRationalHeight_arch_continuous
    (qf : SourceKPFiniteAdeleProjective K hζ) (c : SourceKPRationalBorelCoset K) :
    Continuous (fun a : PGL(2,InfiniteAdeleRing K) =>
      sourceKPAdelicRationalHeight K hζ (a,qf) c) := by
  induction c using Quotient.inductionOn with
  | _ γ =>
    change Continuous (fun a : PGL(2,InfiniteAdeleRing K) => sourceKPAdelicCoverHeight K hζ
      ((sourceKPAdelicProjectiveRationalLift K hζ γ).1*a,
       (sourceKPAdelicProjectiveRationalLift K hζ γ).2*qf))
    exact (sourceKPAdelicCoverHeight_arch_continuous K hζ _).comp
      (continuous_const.mul continuous_id)

theorem sourceKPAdelicRationalScalar_joint_arch_continuous
    (qf : SourceKPFiniteAdeleProjective K hζ) (c : SourceKPRationalBorelCoset K) :
    Continuous (fun p : ℂ × PGL(2,InfiniteAdeleRing K) =>
      sourceKPAdelicRationalSummand K hζ
        (sourceKPAdelicPrincipalSeriesScalar K hζ p.1 (sourceKPAdelicCompactSection K hζ p.1))
        (p.2,qf) c) := by
  induction c using Quotient.inductionOn with
  | _ γ =>
    change Continuous (fun p : ℂ × PGL(2,InfiniteAdeleRing K) => sourceKPAdelicCompactScalar K hζ p.1
      ((sourceKPAdelicProjectiveRationalLift K hζ γ).1*p.2,
       (sourceKPAdelicProjectiveRationalLift K hζ γ).2*qf))
    exact (sourceKPAdelicCompactScalar_joint_arch_continuous K hζ _).comp
      (continuous_fst.prodMk (continuous_const.mul continuous_snd))

theorem sourceKPAdelicDefectTerm_joint_arch_continuous (T : ℝ)
    (qf : SourceKPFiniteAdeleProjective K hζ) (c : SourceKPRationalBorelCoset K) :
    Continuous (fun p : ℂ × PGL(2,InfiniteAdeleRing K) =>
      sourceKPAdelicDefectTerm K hζ T p.1 (p.2,qf) c) :=
  ((sourceKPAdelicDefectCoefficient_continuous T).comp
    (continuous_fst.prodMk ((sourceKPAdelicRationalHeight_arch_continuous K hζ qf c).comp continuous_snd))).mul
      (sourceKPAdelicRationalScalar_joint_arch_continuous K hζ qf c)

end
end ArtinMatthews
