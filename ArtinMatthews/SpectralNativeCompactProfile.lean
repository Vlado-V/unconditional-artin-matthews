module

public import ArtinMatthews.SpectralKLHeightPhysicalTest
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! The physical profile of an actual compact smooth height test is a
compact smooth real-valued input for the inverse-KL construction. -/

noncomputable section
open Set Filter
open scoped ContDiff
namespace ArtinMatthews

theorem spectralKLHeightPhysicalTest_contDiff {q : ℝ} (hq : 0 < q)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) : ContDiff ℝ ∞ (spectralKLHeightPhysicalTest q ρ) := by
  have hsupport := (spectralKLHeightPhysicalTest_properties hq ρ hρ.continuous hcρ hpρ).2.2
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : 0 < x
  · have hy : 0 < x/q := div_pos hx hq
    have harg : ContDiffAt ℝ ∞ (fun y : ℝ => y/q) x := by fun_prop
    have hr : ContDiffAt ℝ ∞ (fun y : ℝ => ρ (y/q)*Real.sqrt (y/q)/(y/q)) x :=
      ((hρ.contDiffAt.comp x harg).mul (harg.sqrt hy.ne')).div harg hy.ne'
    have hc : ContDiffAt ℝ ∞ (fun y : ℝ => ((ρ (y/q)*Real.sqrt (y/q)/(y/q) : ℝ) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hr
    change ContDiffAt ℝ ∞ (fun y : ℝ =>
      ((ρ (y/q)*Real.sqrt (y/q) : ℝ) : ℂ)/((y/q : ℝ) : ℂ)) x
    convert hc using 1
    funext y
    simp only [Complex.ofReal_div]
  · have hn : x ∉ tsupport (spectralKLHeightPhysicalTest q ρ) := fun h => hx (hsupport h)
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hn)

theorem spectralKLHeightPhysicalTest_conj (q : ℝ) (ρ : ℝ → ℝ) (x : ℝ) :
    star (spectralKLHeightPhysicalTest q ρ x) = spectralKLHeightPhysicalTest q ρ x := by
  simp [spectralKLHeightPhysicalTest,spectralKLHeightBaseTest]

end ArtinMatthews
