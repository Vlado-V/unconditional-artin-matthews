module

public import ArtinMatthews.MarkedMemorySourceBoundary
public import ArtinMatthews.MarkedMemoryHistoryChronological
public import ArtinMatthews.MarkedMemoryMeasureRescale
public import ArtinMatthews.MarkedMemoryChronologicalRescale
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The empty-memory boundary contributes its initial atom normalization
outside W. Combined with the literal n edge factors this is the exact
constant V normalization of each guarded signed memory history. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (hV : ∀ j,V j≠0)

include hV

theorem markedMemoryRawActiveMass_rescale {M : ℕ} (a : MarkedRawActive P M) :
    markedRawActiveMass ν a=(∏ j,(V j)⁻¹)^M*
      markedRawActiveMass (markedMemoryScaledAtoms ν V) a := by
  calc
    _ = ∏ j,∏ k,(V j)⁻¹*markedMemoryScaledAtoms ν V j (a j k) := by
      unfold markedRawActiveMass
      apply Finset.prod_congr rfl
      intro j _
      apply Finset.prod_congr rfl
      intro k _
      simp [markedMemoryScaledAtoms,hV j]
    _ = _ := by
      simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
        Finset.prod_pow,markedRawActiveMass]

variable {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (z₀ : Z) (a : MarkedRawActive P (pads+1))

local notation "s" => markedMemoryBoundarySource (B := B) z₀ a

theorem markedMemoryBoundarySource_mass_rescale :
    markedRawStateMass ν s=(∏ j,(V j)⁻¹)^(pads+1)*markedRawStateMass (markedMemoryScaledAtoms ν V) s := by
  rw [markedMemoryBoundarySource_mass,markedMemoryBoundarySource_mass]
  exact markedMemoryRawActiveMass_rescale ν V hV a

variable (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
  (qStage : ℕ → ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)

theorem markedMemoryBoundaryHistory_rescale (n k : ℕ) (H : MarkedMemoryChronologicalHistory hZ n s) :
    (markedRawStateMass ν s:ℂ)*markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n k H=
      (((∏ j,(V j)⁻¹:ℝ):ℂ)^(pads+1+n))*(markedRawStateMass (markedMemoryScaledAtoms ν V) s:ℂ)*
        markedMemoryChronologicalWeight (markedMemoryScaledAtoms ν V) (fun _ => 1)
          hZ ψ η d₀ Y Q ρ qStage χ n k H := by
  rw [markedMemoryBoundarySource_mass_rescale ν V hV z₀ a,
    markedMemoryChronologicalWeight_rescale ν V hV]
  push_cast
  rw [pow_add]
  ring

theorem markedMemoryBoundaryHistory_guarded_rescale (n k : ℕ)
    (keep : MarkedMemoryChronologicalHistory hZ n s → Prop)
    (f : MarkedRawState P (pads+1) B Z → ℂ) :
    (markedRawStateMass ν s:ℂ)*
      (∑ H : MarkedMemoryChronologicalHistory hZ n s,
        if keep H then markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n k H*
          f (markedMemoryChronologicalTarget hZ H) else 0)=
      (((∏ j,(V j)⁻¹:ℝ):ℂ)^(pads+1+n))*(markedRawStateMass (markedMemoryScaledAtoms ν V) s:ℂ)*
        (∑ H : MarkedMemoryChronologicalHistory hZ n s,
          if keep H then markedMemoryChronologicalWeight (markedMemoryScaledAtoms ν V) (fun _ => 1)
            hZ ψ η d₀ Y Q ρ qStage χ n k H*f (markedMemoryChronologicalTarget hZ H) else 0) := by
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H _
  by_cases hh : keep H
  · simp only [ite_eq_left hh]
    rw [← mul_assoc,markedMemoryBoundaryHistory_rescale ν V hV hZ z₀ a ψ η d₀ Y Q ρ qStage χ n k H]
    ring
  · simp only [ite_eq_right hh,mul_zero]

end
end ArtinMatthews
