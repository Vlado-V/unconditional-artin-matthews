module

public import ArtinMatthews.IdealKernelTranspose
public import ArtinMatthews.IdealCharacterUniformNorm
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

/-! The actual transpose bound is uniform over the finite selected-slot
carrier before the asymptotic source parameter is chosen. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
universe u

theorem idealCharacterCellTranspose_uniform (a c d X v₀ : ℝ)
    (ha : 0 ≤ a) (hc : 0 < c) (hd : 0 ≤ d) (hX : 0 ≤ X) (hv₀ : 0 < v₀) :
    ∀ᶠ L : ℝ in atTop,∀ (I : Type u) [Fintype I] [DecidableEq I],
      ∀ (Q : ℕ),(Q:ℝ) ≤ L^a →
      ∀ (P : I → Finset ℕ),(∀ i p,p∈P i → p.Prime) →
      (∀ i,0 < bandReciprocalMass (P i)) →
      (∀ i p,p∈P i → Real.exp (L^c) ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp (L^d)) →
      ∀ i : I,IdealPrimeInterval (P i) → v₀ ≤ bandReciprocalMass (P i) →
      ∀ h : ℝ,0 < h → ∀ f : IdealSelectedLabels P → ℂ,
        idealFrameEnergy (idealSelectedMass P) (idealCharacterCellTranspose P Q h (L^(-X)) f) ≤
          4*idealFrameEnergy (idealSelectedMass P) f := by
  filter_upwards [idealCharacterCellApply_uniform.{u} a c d X v₀ ha hc hd hX hv₀] with L hL
  intro I _ _ Q hQ P hP hV hbounds i hinterval hVlo h hh f
  exact idealCharacterCellTranspose_energy P Q h (L^(-X))
    (hL I Q hQ P hP hV hbounds i hinterval hVlo h hh) f

end
end ArtinMatthews
