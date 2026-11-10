module

public import ArtinMatthews.SpectralCuspPrincipalMoment
public import ArtinMatthews.SpectralKFrameFinset
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The compact K frame acts on the genuine finite cusp moment. -/
noncomputable section
open scoped MatrixGroups BigOperators
namespace ArtinMatthews

theorem gamma0CuspPrincipalMoment_frame_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N]
      (u : Finset (Gamma0AllHeightSpectralIndex N)) (b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
      (n : ℤ) (hn : n ≠ 0) (T V : ℝ), 1/2 ≤ T → 0 ≤ V →
      (∀ i ∈ u, 1/4 ≤ gamma0AllHeightGradientSpectralValue N i) →
      (∀ i ∈ u, T ≤ 1+|gamma0CuspPrincipalParameter N i| ∧ 1+|gamma0CuspPrincipalParameter N i| ≤ 2*T) →
      (∀ F : ℝ → ℝ, spectralKFrameProfileBound T F →
        gamma0CuspPhysicalBesselMoment N u b Y hY n hn F ≤ V*spectralKFrameLength) →
      gamma0CuspPrincipalMoment N u b Y hY n hn ≤ C*T^2*V := by
  obtain ⟨C,hC,hFrame⟩ := spectralKFrame_principal_finset_bound
  refine ⟨C,hC,?_⟩
  intro N inst u b Y hY n hn T V hT hV hPrincipal hBand hMoment
  let A (i : Gamma0AllHeightSpectralIndex N) : ℝ := ‖gamma0CuspUnitAmplitude N i b Y hY n hn‖^2
  apply hFrame u (gamma0CuspPrincipalParameter N) A T V hT hV (fun i _ => sq_nonneg _) hBand
  intro F hF
  have h := hMoment F hF
  rw [gamma0CuspPhysicalBesselMoment_principal_eq N u b Y hY n hn F hPrincipal] at h
  exact h

end ArtinMatthews
