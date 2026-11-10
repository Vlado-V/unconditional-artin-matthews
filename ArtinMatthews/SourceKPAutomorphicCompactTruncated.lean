module

public import ArtinMatthews.SourceKPAutomorphicCompactCutoff
public import ArtinMatthews.SourceKPAutomorphicCompactEisenstein
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

/-! The literal difference E_s-P_s on the actual compact quotient. -/
namespace ArtinMatthews
open NumberField
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAutomorphicCompactTruncatedEisenstein (T : ℝ) (s : ℂ)
    (x : SourceKPAutomorphicCompactLevel K hζ) : ℂ :=
  sourceKPAutomorphicCompactEisenstein K hζ s x-
    sourceKPAutomorphicCompactCutoffEisenstein K hζ T s x

theorem sourceKPAutomorphicCompactTruncatedEisenstein_mk (T : ℝ) (s : ℂ)
    (x : SourceKPAutomorphicLevel K hζ) :
    sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s (sourceKPAutomorphicCompactMk K hζ x) =
      sourceKPAutomorphicEisenstein K hζ s x-sourceKPAutomorphicCutoffEisenstein K hζ T s x := rfl

theorem sourceKPAutomorphicCompactTruncatedEisenstein_adelic (T : ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) :
    sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s
      (sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ q)) =
        sourceKPAdelicCompactEisenstein K hζ s q-sourceKPAdelicCutoffEisenstein K hζ T s q := rfl

theorem sourceKPAutomorphicCompactTruncatedEisenstein_center (T : ℝ) (s : ℂ)
    (z : rootsOfUnity 3 K) (x : SourceKPAutomorphicCompactLevel K hζ) :
    sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s (z • x) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ)*
        sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s x := by
  unfold sourceKPAutomorphicCompactTruncatedEisenstein
  rw [sourceKPAutomorphicCompactEisenstein_center,sourceKPAutomorphicCompactCutoffEisenstein_center,
    mul_sub]

theorem sourceKPAutomorphicCompactTruncatedEisenstein_holomorphic {T : ℝ} (hT : 0 < T)
    (x : SourceKPAutomorphicCompactLevel K hζ) :
    DifferentiableOn ℂ (fun s => sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s x)
      {s : ℂ | ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) < 2*s.re+1} :=
  (sourceKPAutomorphicCompactEisenstein_holomorphic K hζ x).sub
    (sourceKPAutomorphicCompactCutoffEisenstein_entire K hζ hT x).differentiableOn

end
end ArtinMatthews
