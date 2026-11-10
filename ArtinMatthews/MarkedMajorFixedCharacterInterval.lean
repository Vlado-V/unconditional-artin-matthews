module

public import ArtinMatthews.MarkedMajorFixedCharacterMajorSaving
public import ArtinMatthews.MarkedMajorArcPaperSource
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
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! The literal scalar fixed-character major sum. The original centered
coefficient is retained and both closed lower endpoints are counted. -/
namespace ArtinMatthews
open Finset ComplexConjugate
noncomputable section

def markedMajorFixedIntervalPairSum {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) {Mχ : ℕ} (ξ : DirichletCharacter ℂ Mχ)
    (cutoff : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ)
    (Q Y W modulation : ℝ) (S T : Finset ℕ) (l r : ℕ) (β : ℕ → ℂ) : ℂ :=
  (markedMajorLabelMass bands:ℂ)^2*
    ∑ b ∈ markedMajorLabelSet bands,∑ m ∈ S,∑ n ∈ Icc l r,
    ∑ a ∈ markedMajorLabelSet bands,∑ r' ∈ T,∑ s ∈ Icc l r,
      cutoff ((b:ℝ)/Y)*cutoff ((a:ℝ)/Y)*
      markedMajorCenteredCoefficient W modulation m*conj (markedMajorCenteredCoefficient W modulation r')*
      β n*conj (β s)*ξ (m*n)*conj (ξ (r'*s))*
      ψ ((markedMajorIntegerDeterminant (b,m,n) (a,r',s):ℝ)/Y)*
      markedBanMajorKernel Q Y (markedMajorIntegerDeterminant (b,m,n) (a,r',s)-(b:ℤ)+(a:ℤ))

theorem markedMajorFixedIntervalPairSum_closed_split {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) {Mχ : ℕ} (ξ : DirichletCharacter ℂ Mχ)
    (cutoff : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ)
    (Q Y W modulation : ℝ) (M N : ℕ) (hMN : M ≤ N) (l r : ℕ) (β : ℕ → ℂ) :
    markedMajorFixedIntervalPairSum bands ξ cutoff ψ Q Y W modulation (Icc M N) (Icc M N) l r β =
      markedMajorFixedIntervalPairSum bands ξ cutoff ψ Q Y W modulation (Ioc M N) (Ioc M N) l r β +
      markedMajorFixedIntervalPairSum bands ξ cutoff ψ Q Y W modulation {M} (Ioc M N) l r β +
      markedMajorFixedIntervalPairSum bands ξ cutoff ψ Q Y W modulation (Ioc M N) {M} l r β +
      markedMajorFixedIntervalPairSum bands ξ cutoff ψ Q Y W modulation {M} {M} l r β := by
  simp only [markedMajorFixedIntervalPairSum,Icc_eq_cons_Ioc hMN,sum_cons,sum_singleton,
    sum_add_distrib,mul_add]
  ring

theorem markedMajor_fixed_comparable_interval_source_eq {J : Type} [Fintype J]
    {cfg : MarkedMajorLabelEnergyConfig} {L X X' : ℝ}
    (z : MarkedMajorLabelEnergyData J cfg L X) (z' : MarkedMajorLabelEnergyData J cfg L X')
    (hb : z'.allBands=z.allBands) (hm : z'.modulation=z.modulation)
    (hl : z'.l=z.l) (hr : z'.r=z.r) (hβ : z'.β=z.β)
    {Mχ : ℕ} (ξ : DirichletCharacter ℂ Mχ)
    (cutoff : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (Q : ℝ) :
    z.fixedComparableMajorSource z'.conjugateBeta ξ (star ξ) cutoff ψ Q =
      markedMajorFixedIntervalPairSum z.allBands ξ cutoff ψ Q z.Y (Real.exp (L^(6/25:ℝ)))
        z.modulation (Ioc ⌊z.u⌋₊ ⌊z.v⌋₊) (Ioc ⌊z'.u⌋₊ ⌊z'.v⌋₊) z.l z.r z.β := by
  classical
  unfold MarkedMajorLabelEnergyData.fixedComparableMajorSource
  simp only [MarkedMajorLabelEnergyData.conjugateBeta]
  change markedMajorKernelSource
    (markedMajorLabelTripleSet z.allBands z.u z.v z.l z.r)
    (markedMajorLabelTripleSet z'.allBands z'.u z'.v z'.l z'.r)
    (markedMajorFixedBareTripleCoefficient z.allBands cutoff z.Y (Real.exp (L^(6/25:ℝ))) z.modulation z.β ξ)
    (markedMajorFixedBareConjugateTripleCoefficient z'.allBands cutoff z.Y (Real.exp (L^(6/25:ℝ)))
      z'.modulation (fun n => conj (z'.β n)) (star ξ)) ψ Q z.Y = _
  rw [hb,hm,hl,hr,hβ]
  unfold markedMajorKernelSource markedMajorFixedIntervalPairSum markedMajorLabelTripleSet
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
  unfold markedMajorFixedBareTripleCoefficient markedMajorFixedBareConjugateTripleCoefficient
    markedMajorBareTripleCoefficient markedMajorBareConjugateTripleCoefficient
  dsimp only
  rw [MulChar.star_apply,Complex.star_def]
  ring

end
end ArtinMatthews
