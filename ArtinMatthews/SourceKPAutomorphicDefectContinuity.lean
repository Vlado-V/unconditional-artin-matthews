module

public import ArtinMatthews.SourceKPAdelicDefectParameterJoint
public import ArtinMatthews.SourceKPAutomorphicCompactDefect
public import ArtinMatthews.SourceKPAdelicDefectJointContinuity
public import ArtinMatthews.SourceKPAutomorphicParametricContinuity
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

/-! Joint parameter continuity of the actual compact-quotient defect and
its literal complex derivative. -/

namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAutomorphicCompactDefectParameterDerivative {T : ℝ} (hT : 0 < T)
    (s : ℂ) (x : SourceKPAutomorphicCompactLevel K hζ) : ℂ :=
  deriv (fun z => sourceKPAutomorphicCompactCutoffDefect K hζ hT z x) s

theorem sourceKPAutomorphicCompactCutoffDefect_hasDerivAt {T : ℝ} (hT : 0 < T)
    (s : ℂ) (x : SourceKPAutomorphicCompactLevel K hζ) :
    HasDerivAt (fun z => sourceKPAutomorphicCompactCutoffDefect K hζ hT z x)
      (sourceKPAutomorphicCompactDefectParameterDerivative K hζ hT s x) s :=
  (sourceKPAutomorphicCompactCutoffDefect_entire K hζ hT x s).hasDerivAt

theorem sourceKPAutomorphicCompactDefectParameterDerivative_adelic {T : ℝ} (hT : 0 < T)
    (s : ℂ) (q : SourceKPAdelicProjective K hζ) :
    sourceKPAutomorphicCompactDefectParameterDerivative K hζ hT s
      (sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ q)) =
        sourceKPAdelicCutoffDefectParameterDerivative K hζ T s q := rfl

theorem sourceKPAutomorphicCompactCutoffDefect_joint_continuous {T : ℝ} (hT : 0 < T) :
    Continuous (fun p : ℂ × SourceKPAutomorphicCompactLevel K hζ =>
      sourceKPAutomorphicCompactCutoffDefect K hζ hT p.1 p.2) := by
  apply sourceKPAutomorphicCompactFamily_continuous_of_matrices
  intro qf
  exact sourceKPAdelicCutoffCasimirDefect_joint_matrix_continuous K hζ hT qf

theorem sourceKPAutomorphicCompactDefectParameterDerivative_joint_continuous
    {T : ℝ} (hT : 0 < T) :
    Continuous (fun p : ℂ × SourceKPAutomorphicCompactLevel K hζ =>
      sourceKPAutomorphicCompactDefectParameterDerivative K hζ hT p.1 p.2) := by
  apply sourceKPAutomorphicCompactFamily_continuous_of_matrices
  intro qf
  exact sourceKPAdelicCutoffDefectParameterDerivative_joint_matrix_continuous K hζ hT qf

theorem sourceKPAutomorphicCompactDefectParameterDerivative_support {T : ℝ}
    (hT : 1 ≤ T) (s : ℂ) :
    Function.support (sourceKPAutomorphicCompactDefectParameterDerivative K hζ
      (lt_of_lt_of_le zero_lt_one hT) s) ⊆
        {x | sourceKPAutomorphicCompactOrbitHeight K hζ x ≤ 2*T} := by
  intro x hx
  by_contra houtside
  have hz (z : ℂ) : sourceKPAutomorphicCompactCutoffDefect K hζ
      (lt_of_lt_of_le zero_lt_one hT) z x = 0 := by
    by_contra hne
    exact houtside (sourceKPAutomorphicCompactCutoffDefect_support K hζ hT z hne)
  have he : (fun z => sourceKPAutomorphicCompactCutoffDefect K hζ
      (lt_of_lt_of_le zero_lt_one hT) z x) = fun _ => 0 := funext hz
  apply hx
  change deriv (fun z => sourceKPAutomorphicCompactCutoffDefect K hζ
    (lt_of_lt_of_le zero_lt_one hT) z x) s = 0
  rw [he]
  exact deriv_const s 0

end
end ArtinMatthews
