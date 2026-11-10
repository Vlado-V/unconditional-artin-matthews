module

public import ArtinMatthews.MarkedMajorArcMajorSaving
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

/-! Literal PD05 source: two independently summed label products, the squared
band normalizer, and the actual α_m conjugate(α_r) β_n conjugate(β_s). -/
namespace ArtinMatthews
open Finset ComplexConjugate
noncomputable section
namespace MarkedMajorLabelEnergyData
variable {J : Type} {cfg : MarkedMajorLabelEnergyConfig} {L X : ℝ}

 def conjugateBeta (z : MarkedMajorLabelEnergyData J cfg L X) :
    MarkedMajorLabelEnergyData J cfg L X :=
  { z with
    β := fun n => conj (z.β n)
    coefficient_bound := fun n hn => by simpa only [RCLike.norm_conj] using z.coefficient_bound n hn }

end MarkedMajorLabelEnergyData

 def markedMajorDeterminantPaperSum {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ)
    (Q Y W modulation u v : ℝ) (l r : ℕ) (β : ℕ → ℂ) : ℂ :=
  (markedMajorLabelMass bands:ℂ)^2*
    ∑ b ∈ markedMajorLabelSet bands,∑ m ∈ Ioc ⌊u⌋₊ ⌊v⌋₊,∑ n ∈ Icc l r,
    ∑ a ∈ markedMajorLabelSet bands,∑ r' ∈ Ioc ⌊u⌋₊ ⌊v⌋₊,∑ s ∈ Icc l r,
      cutoff ((b:ℝ)/Y)*cutoff ((a:ℝ)/Y)*
      markedMajorCenteredCoefficient W modulation m*conj (markedMajorCenteredCoefficient W modulation r')*
      β n*conj (β s)*ψ ((markedMajorIntegerDeterminant (b,m,n) (a,r',s):ℝ)/Y)*
      markedBanMajorKernel Q Y (markedMajorIntegerDeterminant (b,m,n) (a,r',s)-(b:ℤ)+(a:ℤ))

 theorem markedMajor_paper_source_eq {J : Type} [Fintype J]
    {cfg : MarkedMajorLabelEnergyConfig} {L X : ℝ}
    (z : MarkedMajorLabelEnergyData J cfg L X) (cutoff : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (Q : ℝ) :
    z.majorSource z.conjugateBeta cutoff ψ Q =
      markedMajorDeterminantPaperSum z.allBands cutoff ψ Q z.Y (Real.exp (L^(6/25:ℝ)))
        z.modulation z.u z.v z.l z.r z.β := by
  classical
  unfold MarkedMajorLabelEnergyData.majorSource markedMajorKernelSource
    MarkedMajorLabelEnergyData.conjugateBeta
  change markedMajorKernelSource
    (markedMajorLabelTripleSet z.allBands z.u z.v z.l z.r)
    (markedMajorLabelTripleSet z.allBands z.u z.v z.l z.r)
    (markedMajorBareTripleCoefficient z.allBands cutoff z.Y (Real.exp (L^(6/25:ℝ))) z.modulation z.β)
    (markedMajorBareConjugateTripleCoefficient z.allBands cutoff z.Y (Real.exp (L^(6/25:ℝ))) z.modulation (fun n => conj (z.β n)))
    ψ Q z.Y = _
  unfold markedMajorKernelSource markedMajorDeterminantPaperSum markedMajorLabelTripleSet
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
