module

public import ArtinMatthews.SpectralSectionCuspEnergy
public import ArtinMatthews.SpectralGamma0EnergyGraph
public import ArtinMatthews.SpectralGamma0CuspEnergy
public import ArtinMatthews.SpectralSectionPullback
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Genuine Γ₀ compact seeds supply the actual cusp value/derivative graph. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

def gamma0CuspSection (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (r : SL(2, ℤ)) (z : UpperHalfPlane) : ℂ := gamma0PoincareSeed N ψ.val (r⁻¹ • z)

theorem gamma0CuspSection_smooth (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (r : SL(2, ℤ)) :
    ContDiffOn ℝ ∞ (fun v : ℂ => gamma0CuspSection N ψ r (UpperHalfPlane.ofComplex v))
      {v : ℂ | 0 < v.im} :=
  spectralSection_smooth_pullback (gamma0PoincareSeed N ψ.val)
    (gamma0SmoothSeed_representative_smooth N ψ)
    (Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹) (by simp)

theorem gamma0CuspSection_energy (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (r : SL(2, ℤ)) (z : UpperHalfPlane) :
    h2SectionEnergy (gamma0CuspSection N ψ r) z =
      h2SectionEnergy (gamma0PoincareSeed N ψ.val) (r⁻¹ • z) :=
  h2SectionEnergy_pullback (gamma0PoincareSeed N ψ.val)
    (gamma0SmoothSeed_representative_smooth N ψ)
    (Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹) (by simp) z

theorem gamma0CuspSection_energy_integrable_bound (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) :
    IntegrableOn (h2SectionEnergy (gamma0CuspSection N ψ r)) (hyperbolicCuspStrip (N : ℝ) 1) ∧
    (∫ z in hyperbolicCuspStrip (N : ℝ) 1, h2SectionEnergy (gamma0CuspSection N ψ r) z) ≤
      ((N : ℝ)+1) * ‖gamma0EnergyTest N ψ‖^2 := by
  have ht := gamma0_cusp_strip_energy_bound N ψ r
  have he : (fun z : UpperHalfPlane =>
      ‖gamma0PoincareSeed N ψ.val (r⁻¹ • z)‖^2+h2SectionEnergy (gamma0PoincareSeed N ψ.val) (r⁻¹ • z)) =
      (fun z => ‖gamma0CuspSection N ψ r z‖^2+h2SectionEnergy (gamma0CuspSection N ψ r) z) := by
    funext z
    rw [gamma0CuspSection_energy]
    rfl
  rw [he] at ht
  have hi : IntegrableOn (h2SectionEnergy (gamma0CuspSection N ψ r))
      (hyperbolicCuspStrip (N : ℝ) 1) := by
    apply ht.1.mono' (h2SectionEnergy_continuous _ (gamma0CuspSection_smooth N ψ r)).aestronglyMeasurable
    apply Eventually.of_forall
    intro z
    rw [Real.norm_of_nonneg (h2SectionEnergy_nonneg _ _)]
    exact le_add_of_nonneg_left (sq_nonneg _)
  refine ⟨hi,le_trans ?_ ht.2⟩
  exact integral_mono hi ht.1 (fun z => le_add_of_nonneg_left (sq_nonneg _))

/-- The generator is the literal smooth height extension of the actual cusp
section; its finite horizontal energy is derived from the global energy. -/
def gamma0CuspSmoothCore (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (r : SL(2, ℤ)) : SpectralCuspSmoothCore (N : ℝ) 1 :=
  spectralSectionCuspSmoothCore (gamma0CuspSection N ψ r) (gamma0CuspSection_smooth N ψ r)
    (Nat.cast_pos.mpr (NeZero.pos N)) zero_lt_one
    (gamma0CuspSection_energy_integrable_bound N ψ r).1

theorem gamma0CuspSmoothCore_energy_bound (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) :
    (∫ y in Ioi (1 : ℝ), cuspHorizontalEnergy (gamma0CuspSmoothCore N ψ r).toFun (N : ℝ) y) ≤
      ((N : ℝ)+1) * ‖gamma0EnergyTest N ψ‖^2 :=
  (spectralSectionSmoothExtension_cusp_energy (gamma0CuspSection N ψ r)
    (gamma0CuspSection_smooth N ψ r) (Nat.cast_pos.mpr (NeZero.pos N)) zero_lt_one
    (gamma0CuspSection_energy_integrable_bound N ψ r).1).2.trans
      (gamma0CuspSection_energy_integrable_bound N ψ r).2

end ArtinMatthews
