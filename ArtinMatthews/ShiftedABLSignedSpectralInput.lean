module

public import ArtinMatthews.ShiftedABLMellinCircle
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

/-! The exact pointwise signed spectral input consumed by source
correlation. The unrestricted Mellin heights have a fixed polynomial cost. -/

noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators
namespace ArtinMatthews

def ShiftedABLSignedSpectralInput : Prop :=
  ∀ B ν : ℝ, 0 < B → 0 < ν → ∃ (J : ℕ) (C : ℝ), 0 < C ∧
    ∀ (χ : HeckeFamily.Character) (D m3 m4 F L : ℕ) [NeZero F] [NeZero D],
      0 < m3 → 0 < m4 → m3 ≠ m4 → (m3*m4).Coprime F → 0 < L →
      (F : ℝ) ≤ 3*(L : ℝ) → ∀ (d : ℕ × ℕ) (i : ℕ × Bool),
      let r := m3*m4
      let n := shiftedABLFirstIndex m3 m4
      let R : ℝ := 2^i.1
      let Q : ℝ := 3*(L : ℝ)
      let X := Real.sqrt (R*(n : ℝ))/(Real.sqrt (r : ℝ)*Q)
      let G := Real.sqrt ((n : ℝ)*(((r*F).gcd n : ℕ) : ℝ))
      let P₀ := Q*R*(n : ℝ)*(r : ℝ)
      X ≤ B → ∀ V : ℝ, 1 ≤ V → (n : ℝ)*X ≤ V*G → ∀ z : ℝ × ℝ,
      ‖shiftedABLMellinSignedSum χ D m3 m4 F r L d i z‖ ≤
        C*(F : ℝ)*Real.sqrt r*P₀^ν*Real.sqrt V*(1+|z.1|+|z.2|)^J *
          Real.sqrt (∑ ρ ∈ (shiftedABLDualFrequencies m3 m4 d).filter
            (fun ρ => shiftedABLSignedFrequencyIndex ρ=i),
            ‖shiftedABLMellinRhoCoefficient χ D m3 m4 d ρ z‖^2) *
          Real.sqrt (1+R/((r : ℝ)*(F : ℝ))) *
          Real.sqrt (1+G/(X*(r : ℝ)*(F : ℝ)))

end ArtinMatthews
