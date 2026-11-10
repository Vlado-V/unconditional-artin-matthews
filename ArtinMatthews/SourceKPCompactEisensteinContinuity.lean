module

public import ArtinMatthews.SourceKPAutomorphicCompactTruncated
public import ArtinMatthews.SourceKPAdelicEisensteinProductC1
public import ArtinMatthews.SourceKPCompactCutoffContinuity
public import ArtinMatthews.SourceKPCompactEisensteinChart
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

/-! The literal compact-quotient Eisenstein function and its truncated
version are continuous in the proved initial region. -/

namespace ArtinMatthews
open NumberField MeasureTheory Filter OAI.CubicEisenstein SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAutomorphicCompactEisenstein_continuous {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1) :
    Continuous (sourceKPAutomorphicCompactEisenstein K hζ s) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨b,p,rfl⟩ := sourceKPUpperToCompact_cover K hζ x
  obtain ⟨qf,rfl⟩ := Quotient.exists_rep b
  let m := sourceKPUpperToCompact K hζ (QuotientGroup.mk qf)
  let f := sourceKPAutomorphicCompactEisenstein K hζ s
  have hpositive (q : SourceKPArchUpperHalfSpace K) :
      sourceKPArchUpperEuclideanMap K q ∈ productUpper (InfinitePlace K) :=
    fun v _ => sourceKPArchUpperEuclidean_positive K q v
  have hchart := (sourceKPAdelicEisensteinProductChart_contDiffOn K hζ hs (1,qf)).continuousOn
  have hcont := hchart.comp_continuous (sourceKPArchUpperEuclideanMap_continuous K) hpositive
  have he : f ∘ m = sourceKPAdelicEisensteinProductChart K hζ s (1,qf) ∘
      sourceKPArchUpperEuclideanMap K := by
    funext q
    exact sourceKPAutomorphicCompactEisenstein_upper_chart K hζ s qf q
  have hm : Continuous (f ∘ m) := he.symm ▸ hcont
  have hn : Filter.map m (𝓝 p) = 𝓝 (m p) :=
    (sourceKPUpperToCompact_isOpenMap K hζ (QuotientGroup.mk qf)).map_nhds_eq
      (sourceKPUpperToCompact_continuous K hζ (QuotientGroup.mk qf)).continuousAt
  change Tendsto f (𝓝 (m p)) (𝓝 (f (m p)))
  rw [← hn,tendsto_map'_iff]
  exact hm.continuousAt

theorem sourceKPAutomorphicCompactTruncatedEisenstein_continuous {T : ℝ} (hT : 0 < T)
    {s : ℂ} (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1) :
    Continuous (sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s) := by
  have hm : Continuous (fun x : SourceKPAutomorphicCompactLevel K hζ => (s,x)) :=
    continuous_const.prodMk continuous_id
  have hP : Continuous (sourceKPAutomorphicCompactCutoffEisenstein K hζ T s) := by
    simpa only [Function.comp_def] using
      (sourceKPAutomorphicCompactCutoffEisenstein_joint_continuous K hζ hT).comp hm
  exact (sourceKPAutomorphicCompactEisenstein_continuous K hζ hs).sub hP

theorem sourceKPAutomorphicCompactTruncatedEisenstein_measurable {T : ℝ} (hT : 0 < T)
    {s : ℂ} (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1) :
    Measurable (sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s) :=
  (sourceKPAutomorphicCompactTruncatedEisenstein_continuous K hζ hT hs).measurable

end
end ArtinMatthews
