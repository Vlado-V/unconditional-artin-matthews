module

public import ArtinMatthews.SpectralResidualEigenbasis
public import ArtinMatthews.SpectralEisensteinAmbientResolution
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

/-! The actual finite residual basis satisfies Bessel's inequality in the
ambient mass norm. -/

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace BigOperators
namespace ArtinMatthews

local instance spectralResidualBessel_cuspInner (N : ℕ) [NeZero N] :
    InnerProductSpace ℂ (gamma0AllHeightCuspidalMassSpace N) :=
  Submodule.innerProductSpace (𝕜 := ℂ) (E := Gamma0RegionL2 N) (gamma0AllHeightCuspidalMassSpace N)

theorem gamma0ResidualEigenbasis_pairing_sq_sum_le (N : ℕ) [NeZero N] (P : Gamma0RegionL2 N) :
    (∑ l ∈ gamma0ResidualEnergyWindow N, ∑ j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l)),
      ‖inner ℂ P (gamma0ResidualEigenbasis N l j).val‖^2) ≤ ‖P‖^2 := by
  let U := gamma0CuspidalProjection N P
  let V := gamma0EisensteinAnalysis N P
  have h := congrArg Complex.re (gamma0AmbientEisenstein_spectral_pairing N P P)
  have hInner (z : ℂ) : (z*star z).re = ‖z‖^2 := by
    have h := Complex.mul_conj' z
    simpa only [Complex.star_def,← Complex.ofReal_pow,Complex.ofReal_re] using congrArg Complex.re h
  have hTerm (l : Ici (0 : ℝ))
      (j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l))) :
      (inner ℂ P (gamma0ResidualEigenbasis N l j).val*
        inner ℂ (gamma0ResidualEigenbasis N l j).val P).re =
          ‖inner ℂ P (gamma0ResidualEigenbasis N l j).val‖^2 := by
    rw [← inner_conj_symm (gamma0ResidualEigenbasis N l j).val P]
    exact hInner _
  rw [gamma0ResidualProjection_inner,gamma0StoneResidualPair_eq_finite_eigenbasis] at h
  simp only [Complex.add_re,Complex.re_sum,hTerm] at h
  change (inner ℂ P P).re = (inner ℂ U U).re+((inner ℂ V V).re+_) at h
  have hP : (inner ℂ P P).re = ‖P‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) P
  have hU : (inner ℂ U U).re = ‖U‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) U
  have hV : (inner ℂ V V).re = ‖V‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) V
  rw [hP,hU,hV] at h
  linarith only [h,sq_nonneg ‖U‖,sq_nonneg ‖V‖]

end ArtinMatthews
