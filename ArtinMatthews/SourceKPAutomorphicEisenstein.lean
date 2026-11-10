module

public import ArtinMatthews.SourceKPFiniteLevelDescent
public import ArtinMatthews.SourceKPAdelicEisensteinHolomorphic
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

/-! The actual compact-section Eisenstein series descends to the actual
rational quotient at its finite level. Analytic statements below retain the
proved initial half-plane. -/

namespace ArtinMatthews
open NumberField Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCompactScalar_finite_right (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (k : sourceKPFiniteDeepMatrixGroup K) :
    sourceKPAdelicCompactScalar K hζ s (g * sourceKPFiniteDeepCoverLift K hζ k) =
      sourceKPAdelicCompactScalar K hζ s g := by
  have he := sourceKPAdelicCompactSection_finite_fixed K hζ s k
  rw [← sourceKPFiniteDeepCoverLift_eq] at he
  exact congrArg (fun f : SourceKPAdelicPrincipalSeries K hζ s => (f.val g).val 1) he

theorem sourceKPAdelicCompactEisenstein_finite_right (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (k : sourceKPFiniteDeepMatrixGroup K) :
    sourceKPAdelicCompactEisenstein K hζ s (g * sourceKPFiniteDeepCoverLift K hζ k) =
      sourceKPAdelicCompactEisenstein K hζ s g := by
  unfold sourceKPAdelicCompactEisenstein sourceKPAdelicEisensteinSum sourceKPAdelicRationalSum
  apply tsum_congr
  intro q
  induction q using Quotient.inductionOn with
  | _ a =>
    change sourceKPAdelicCompactScalar K hζ s
      (sourceKPAdelicProjectiveRationalLift K hζ a * (g * sourceKPFiniteDeepCoverLift K hζ k)) = _
    rw [← mul_assoc]
    exact sourceKPAdelicCompactScalar_finite_right K hζ s _ k

theorem sourceKPAdelicCompactEisenstein_rational_invariant (s : ℂ)
    (γ : PGL(2, K)) (g : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicProjectiveRationalLift K hζ γ * g) =
      sourceKPAdelicCompactEisenstein K hζ s g :=
  sourceKPAdelicRationalSum_automorphy K hζ
    (sourceKPAdelicPrincipalSeriesScalar K hζ s (sourceKPAdelicCompactSection K hζ s)) γ g

def sourceKPAutomorphicEisenstein (s : ℂ) : SourceKPAutomorphicLevel K hζ → ℂ :=
  sourceKPAutomorphicLevelDescend K hζ (sourceKPAdelicCompactEisenstein K hζ s)
    (sourceKPAdelicCompactEisenstein_finite_right K hζ s)
    (sourceKPAdelicCompactEisenstein_rational_invariant K hζ s)

theorem sourceKPAutomorphicEisenstein_mk (s : ℂ) (g : SourceKPAdelicProjective K hζ) :
    sourceKPAutomorphicEisenstein K hζ s (sourceKPAutomorphicLevelMk K hζ g) =
      sourceKPAdelicCompactEisenstein K hζ s g := rfl

theorem sourceKPAutomorphicEisenstein_holomorphic (x : SourceKPAutomorphicLevel K hζ) :
    DifferentiableOn ℂ (fun s => sourceKPAutomorphicEisenstein K hζ s x)
      {s : ℂ | ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) < 2*s.re+1} := by
  obtain ⟨g,rfl⟩ := sourceKPAutomorphicLevelMk_surjective K hζ x
  exact sourceKPAdelicCompactEisenstein_holomorphic K hζ g

end
end ArtinMatthews
