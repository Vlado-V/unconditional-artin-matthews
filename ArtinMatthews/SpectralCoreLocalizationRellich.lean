module

public import ArtinMatthews.SpectralCoreLocalization
public import ArtinMatthews.SpectralRellichHyperbolic
public import ArtinMatthews.SpectralSectionEnergy
public import ArtinMatthews.SpectralCoreLocalizationEnergy
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The actual compactly localized hyperbolic sections satisfy the
already proved local Rellich theorem from their actual chart energy. -/

namespace ArtinMatthews
noncomputable section

open MeasureTheory Set
open scoped ContDiff

theorem spectralCoreLocalization_rellich_hyperbolic {J : Type*}
    (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b) (F : J → UpperHalfPlane → ℂ)
    (hF : ∀ j, ContDiffOn ℝ ∞ (fun w : ℂ => F j (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im})
    (hi : ∀ j, IntegrableOn (fun z : UpperHalfPlane => ‖F j z‖^2+h2SectionEnergy (F j) z)
      {z | (z.re,z.im) ∈ spectralPlaneRectangle A a b})
    {B : ℝ} (hB : 0 ≤ B)
    (henergy : ∀ j, (∫ z : UpperHalfPlane in {z | (z.re,z.im) ∈ spectralPlaneRectangle A a b},
      ‖F j z‖^2+h2SectionEnergy (F j) z) ≤ B) :
    IsCompact (closure (range (fun j => spectralHyperbolicRectangleLp ha hab
      (spectralCoreLocalization φ ha hφ (F j) (hF j))
      (spectralCoreLocalization_support φ ha hφ (F j) (hF j))))) := by
  obtain ⟨C,hC,hbound⟩ := spectralCoreLocalization_energy_bound φ ha hφ
  apply spectral_rellich_hyperbolic_rectangle_compact_closure A a b ha hab
    (fun j => spectralCoreLocalization φ ha hφ (F j) (hF j))
    (fun j => spectralCoreLocalization_support φ ha hφ (F j) (hF j)) (mul_nonneg hC.le hB)
  intro j
  exact (hbound (F j) (hF j) (hi j)).trans (mul_le_mul_of_nonneg_left (henergy j) hC.le)

end
end ArtinMatthews
