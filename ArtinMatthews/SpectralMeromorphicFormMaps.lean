module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Meromorphic.Basic
public import ArtinMatthews.SpectralEisensteinContinuation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Actual Banach-valued meromorphic operations used by the compact
truncated-form resolvent and its holomorphic forcing. -/
noncomputable section
namespace ArtinMatthews

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem spectralMeromorphicAt_comp_clm (A : E →L[ℂ] F) {f : ℂ → E} {z : ℂ}
    (hf : MeromorphicAt f z) : MeromorphicAt (fun w => A (f w)) z := by
  obtain ⟨n,hn⟩ := hf
  refine ⟨n,?_⟩
  simpa only [Function.comp_def,map_smul] using (A.analyticAt _).comp hn

theorem spectralMeromorphicAt_clmApply (A : ℂ → E →L[ℂ] F) (u : ℂ → E) (z : ℂ)
    (hA : MeromorphicAt A z) (hu : AnalyticAt ℂ u z) :
    MeromorphicAt (fun w => A w (u w)) z := by
  obtain ⟨n,hn⟩ := hA
  refine ⟨n,?_⟩
  simpa only [smul_apply] using
    spectralAnalytic_clmApply (fun w => (w-z)^n • A w) u z hn hu

def spectralOperatorSandwichLinear (J : E →L[ℂ] F) (K : F →L[ℂ] E) :
    (E →L[ℂ] E) →L[ℂ] (F →L[ℂ] F) :=
  (ContinuousLinearMap.compL ℂ F E F J).comp
    (ContinuousLinearMap.flip (E := E →L[ℂ] E) (F := F →L[ℂ] E) (G := F →L[ℂ] E)
      (σ₁₃ := RingHom.id ℂ) (σ₂₃ := RingHom.id ℂ) (ContinuousLinearMap.compL ℂ F E E) K)

theorem spectralOperatorSandwich_meromorphicAt (T : ℂ → E →L[ℂ] E) (z : ℂ)
    (hT : MeromorphicAt T z) (J : E →L[ℂ] F) (K : F →L[ℂ] E) :
    MeromorphicAt (fun w => J.comp ((T w).comp K)) z :=
  spectralMeromorphicAt_comp_clm (spectralOperatorSandwichLinear J K) hT

end
end ArtinMatthews
