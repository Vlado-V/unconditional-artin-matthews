module

public import ArtinMatthews.MarkedMinorArcBanKernel
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact circle detector and adjoint identities for the ban coefficient. -/
noncomputable section
namespace ArtinMatthews

open MeasureTheory
open scoped ComplexConjugate

local instance : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩

theorem markedBan_fourier_integral (k : ℤ) :
    (∫ θ : AddCircle (1:ℝ), fourier k θ ∂AddCircle.haarAddCircle) = if k=0 then 1 else 0 := by
  classical
  by_cases hk : k=0
  · simp [hk]
  · rw [ite_eq_right hk]
    exact integral_eq_zero_of_add_right_eq_neg (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index hk (by norm_num : (0:ℝ)<1))

theorem markedBan_minor_integral (Q Y : ℝ) (k : ℤ) :
    (∫ θ : AddCircle (1:ℝ) in (markedMinorCircleMajor Q Y)ᶜ,
      fourier k θ ∂AddCircle.haarAddCircle) =
      (if k=0 then 1 else 0)-markedBanMajorKernel Q Y k := by
  classical
  have hi : Integrable (fun θ : AddCircle (1:ℝ) => fourier k θ) AddCircle.haarAddCircle :=
    (fourier k).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hh := integral_add_compl (markedMinorCircleMajor_measurable Q Y) hi
  rw [markedBan_fourier_integral] at hh
  unfold markedBanMajorKernel
  linear_combination hh

theorem markedBan_edge_minor_identity (ψ : ℝ → ℂ) (Q Y : ℝ) (b a l : ℤ) :
    ψ ((l:ℝ)/Y)*(∫ θ : AddCircle (1:ℝ) in (markedMinorCircleMajor Q Y)ᶜ,
      fourier (l-b+a) θ ∂AddCircle.haarAddCircle) = markedBanEdgeKernel ψ Q Y b a l := by
  classical
  rw [markedBan_minor_integral]
  have he : l-b+a=0 ↔ l=b-a := by omega
  simp only [he,markedBanEdgeKernel]

theorem markedBanMajorKernel_neg (Q Y : ℝ) (k : ℤ) :
    markedBanMajorKernel Q Y (-k) = (starRingEnd ℂ) (markedBanMajorKernel Q Y k) := by
  unfold markedBanMajorKernel
  simp_rw [fourier_neg]
  exact integral_conj

def markedBanAdjointCutoff (ψ : ℝ → ℂ) (u : ℝ) : ℂ := (starRingEnd ℂ) (ψ (-u))

theorem markedBanEdgeKernel_adjoint (ψ : ℝ → ℂ) (Q Y : ℝ) (b a l : ℤ) :
    markedBanEdgeKernel (markedBanAdjointCutoff ψ) Q Y a b (-l) =
      (starRingEnd ℂ) (markedBanEdgeKernel ψ Q Y b a l) := by
  classical
  have he : -l-a+b = -(l-b+a) := by ring
  have hi : -l=a-b ↔ l=b-a := by omega
  unfold markedBanEdgeKernel markedBanAdjointCutoff
  rw [he,markedBanMajorKernel_neg]
  simp only [Int.cast_neg,neg_div,neg_neg,hi,map_mul,map_sub]
  split_ifs <;> simp

theorem markedBanAdjointCutoff_bounds (ψ : ℝ → ℂ) {A W : ℝ}
    (hψ : ∀ u, ‖ψ u‖ ≤ W) (hsupp : ∀ u, ψ u ≠ 0 → |u| ≤ A) :
    (∀ u, ‖markedBanAdjointCutoff ψ u‖ ≤ W) ∧
      (∀ u, markedBanAdjointCutoff ψ u ≠ 0 → |u| ≤ A) := by
  constructor
  · intro u
    simpa only [markedBanAdjointCutoff,RCLike.norm_conj] using hψ (-u)
  · intro u hu
    have hn : ψ (-u) ≠ 0 := fun hh => hu (by simp only [markedBanAdjointCutoff,hh,map_zero])
    simpa only [abs_neg] using hsupp (-u) hn

end ArtinMatthews
