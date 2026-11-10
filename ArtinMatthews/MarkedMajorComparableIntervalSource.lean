module

public import ArtinMatthews.MarkedMajorComparableMajorSaving
public import ArtinMatthews.MarkedMajorClosedIntervalSplit
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

/-! Exact source identification for independent intervals at comparable
product scales. The two original coefficient endpoints remain separate. -/
namespace ArtinMatthews
open Finset ComplexConjugate
noncomputable section

 theorem markedMajor_comparable_interval_source_eq {J : Type} [Fintype J]
    {cfg : MarkedMajorLabelEnergyConfig} {L X X' : ℝ}
    (z : MarkedMajorLabelEnergyData J cfg L X) (z' : MarkedMajorLabelEnergyData J cfg L X')
    (hb : z'.allBands=z.allBands) (hm : z'.modulation=z.modulation)
    (hl : z'.l=z.l) (hr : z'.r=z.r) (hβ : z'.β=z.β)
    (cutoff : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (Q : ℝ) :
    z.comparableMajorSource z'.conjugateBeta cutoff ψ Q =
      markedMajorIntervalPairSum z.allBands cutoff ψ Q z.Y (Real.exp (L^(6/25:ℝ)))
        z.modulation (Ioc ⌊z.u⌋₊ ⌊z.v⌋₊) (Ioc ⌊z'.u⌋₊ ⌊z'.v⌋₊) z.l z.r z.β := by
  classical
  unfold MarkedMajorLabelEnergyData.comparableMajorSource
  simp only [MarkedMajorLabelEnergyData.conjugateBeta]
  change markedMajorKernelSource
    (markedMajorLabelTripleSet z.allBands z.u z.v z.l z.r)
    (markedMajorLabelTripleSet z'.allBands z'.u z'.v z'.l z'.r)
    (markedMajorBareTripleCoefficient z.allBands cutoff z.Y (Real.exp (L^(6/25:ℝ))) z.modulation z.β)
    (markedMajorBareConjugateTripleCoefficient z'.allBands cutoff z.Y (Real.exp (L^(6/25:ℝ)))
      z'.modulation (fun n => conj (z'.β n))) ψ Q z.Y = _
  rw [hb,hm,hl,hr,hβ]
  unfold markedMajorKernelSource markedMajorIntervalPairSum markedMajorLabelTripleSet
  simp only [sum_product,mul_sum]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro m _
  apply sum_congr rfl
  intro n _
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro r' _
  apply sum_congr rfl
  intro s _
  unfold markedMajorBareTripleCoefficient markedMajorBareConjugateTripleCoefficient
  dsimp only
  ring

end
end ArtinMatthews
