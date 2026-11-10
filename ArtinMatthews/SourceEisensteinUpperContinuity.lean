module

public import ArtinMatthews.SourceEisensteinNonconstant
public import ArtinMatthews.SourceKPAdelicKernelCompactBound
public import ArtinMatthews.SourceKPAdelicKernelContinuity
public import ArtinMatthews.SourceKPRationalHeightComplex
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

/-! The genuine full adelic unipotent orbit is continuous, by locally uniform
convergence of the checked rational periodization. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCompactEisenstein_upper_continuous {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (g : SourceKPAdelicProjective K hζ) :
    Continuous (fun y : 𝔸[K] => sourceKPAdelicCompactEisenstein K hζ s
      (sourceKPAdelicUpperLift K hζ y * g)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  obtain ⟨C,hC,hCy⟩ := exists_compact_mem_nhds y
  obtain ⟨B,_hB,hbound⟩ := sourceKPAdelicIntertwiningKernel_compact_bound K hζ hs g C hC
  have hterms (x : K) : Continuous (fun a : 𝔸[K] =>
      sourceKPAdelicIntertwiningKernel K hζ s g (algebraMap K 𝔸[K] x + a)) :=
    (sourceKPAdelicIntertwiningKernel_continuous K hζ s g).comp (continuous_const.add continuous_id)
  have hsum := continuousOn_tsum (fun x => (hterms x).continuousOn)
    ((sourceKPRationalHeight_rpow_summable K hs).mul_left B)
    (fun x a ha => hbound a ha x)
  have hc : ContinuousAt (fun a : 𝔸[K] => sourceKPAdelicCompactScalar K hζ s g +
      ∑' x : K, sourceKPAdelicIntertwiningKernel K hζ s g (algebraMap K 𝔸[K] x + a)) y :=
    continuousAt_const.add (hsum.continuousAt hCy)
  exact hc.congr (Filter.Eventually.of_forall
    (fun a => (sourceKPAdelicCompactEisenstein_upper_periodization K hζ hs g a).symm))

theorem sourceKPAdelicNonconstantEisenstein_upper_continuous {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (g : SourceKPAdelicProjective K hζ) :
    Continuous (fun y : 𝔸[K] => sourceKPAdelicNonconstantEisenstein K hζ s
      (sourceKPAdelicUpperLift K hζ y * g)) := by
  have hc := (sourceKPAdelicCompactEisenstein_upper_continuous K hζ hs g).sub
    (continuous_const : Continuous (fun _ : 𝔸[K] =>
      sourceKPAdelicCompactScalar K hζ s g + sourceKPAdelicTraceIntertwiner K hζ s g))
  exact hc.congr (fun y => (sourceKPAdelicNonconstantEisenstein_upper K hζ s g y).symm)

end
end ArtinMatthews
