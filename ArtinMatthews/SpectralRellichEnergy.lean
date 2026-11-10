module

public import ArtinMatthews.SpectralRellichSupported
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Order.CompletePartialOrder
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

/-! Actual coordinate Dirichlet energy controls the proved Rellich compactness. -/
namespace ArtinMatthews

open MeasureTheory Set OAI.BFSSRellich
open scoped ENNReal NNReal

noncomputable def spectralCoordinateDerivative (f : SpectralEuclidean → ℂ) (i : Fin 2)
    (x : SpectralEuclidean) : ℂ := fderiv ℝ f x (EuclideanSpace.single i 1)

noncomputable def spectralEuclideanH1Energy (f : SpectralEuclidean → ℂ) : ℝ :=
  (∫ x, ‖f x‖^2) + ∫ x, (‖spectralCoordinateDerivative f 0 x‖^2+
    ‖spectralCoordinateDerivative f 1 x‖^2)

theorem spectralCoordinateDerivative_continuous {f : SpectralEuclidean → ℂ}
    (hf : ContDiff ℝ 1 f) (i : Fin 2) : Continuous (spectralCoordinateDerivative f i) :=
  (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem spectralCoordinateDerivative_compactSupport {f : SpectralEuclidean → ℂ}
    (hc : HasCompactSupport f) (i : Fin 2) : HasCompactSupport (spectralCoordinateDerivative f i) :=
  (hc.fderiv ℝ).comp_left (g := fun T : SpectralEuclidean →L[ℝ] ℂ => T (EuclideanSpace.single i 1))
    (by simp)

/-- The actual full differential energy is bounded by twice the two actual
coordinate derivative energies, with the operator norm correctly retained. -/
theorem spectral_fderiv_energy_le {f : SpectralEuclidean → ℂ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (∫ x, ‖fderiv ℝ f x‖^2) ≤
      2*∫ x, (‖spectralCoordinateDerivative f 0 x‖^2+‖spectralCoordinateDerivative f 1 x‖^2) := by
  have hp (i : Fin 2) : Integrable (fun x => ‖spectralCoordinateDerivative f i x‖^2) :=
    continuous_norm_sq_integrable (spectralCoordinateDerivative_continuous hf i)
      (spectralCoordinateDerivative_compactSupport hc i)
  calc
    _ ≤ ∫ x, 2*(‖spectralCoordinateDerivative f 0 x‖^2+‖spectralCoordinateDerivative f 1 x‖^2) := by
      apply integral_mono (derivative_norm_sq_integrable hf hc) ((hp 0 |>.add (hp 1)).const_mul 2)
      intro x
      change ‖fderiv ℝ f x‖^2 ≤
        2*(‖spectralCoordinateDerivative f 0 x‖^2+‖spectralCoordinateDerivative f 1 x‖^2)
      simpa [Fin.sum_univ_two,spectralCoordinateDerivative] using
        opNorm_sq_le_coordinate_sum (fderiv ℝ f x)
    _ = _ := integral_const_mul _ _

/-- A family with actual bounded L2 plus coordinate Dirichlet energy and
fixed compact support is totally bounded in the actual complex L2 space. -/
theorem spectral_rellich_energy_bounded {J : Type*} (K : Set SpectralEuclidean) (hK : IsCompact K)
    (f : J → SpectralEuclidean → ℂ) (hf : ∀ j, ContDiff ℝ 1 (f j))
    (hs : ∀ j, tsupport (f j) ⊆ K) {B : ℝ} (hB : 0 ≤ B)
    (henergy : ∀ j, spectralEuclideanH1Energy (f j) ≤ B) :
    let hc : ∀ j, HasCompactSupport (f j) := fun j => hK.of_isClosed_subset (isClosed_tsupport _) (hs j)
    TotallyBounded (range (fun j => spectralEuclideanLp (f j) (hf j).continuous (hc j))) := by
  let hc : ∀ j, HasCompactSupport (f j) := fun j => hK.of_isClosed_subset (isClosed_tsupport _) (hs j)
  have hvalue (j : J) : (∫ x, ‖f j x‖^2) ≤ B := by
    have hh := henergy j
    unfold spectralEuclideanH1Energy at hh
    have hn : 0 ≤ ∫ x, (‖spectralCoordinateDerivative (f j) 0 x‖^2+
        ‖spectralCoordinateDerivative (f j) 1 x‖^2) := integral_nonneg (by intro x; positivity)
    linarith
  have hcoordinate (j : J) : (∫ x, (‖spectralCoordinateDerivative (f j) 0 x‖^2+
      ‖spectralCoordinateDerivative (f j) 1 x‖^2)) ≤ B := by
    have hh := henergy j
    unfold spectralEuclideanH1Energy at hh
    have hn : 0 ≤ ∫ x, ‖f j x‖^2 := integral_nonneg (by intro x; positivity)
    linarith
  let A : ℝ≥0 := ⟨Real.sqrt (2*B),Real.sqrt_nonneg _⟩
  let C : ℝ≥0 := ⟨volume.real K+B,by positivity⟩
  apply spectral_rellich_supported K hK f hf hs A C
  · intro j
    change _ ≤ (Real.sqrt (2*B))^2
    rw [Real.sq_sqrt (by positivity)]
    exact (spectral_fderiv_energy_le (hf j) (hc j)).trans
      (mul_le_mul_of_nonneg_left (hcoordinate j) (by norm_num))
  · intro j
    exact (integral_norm_le_volume_add_square (hf j).continuous (hc j) hK
      ((subset_tsupport _).trans (hs j))).trans (by
        change volume.real K+(∫ x, ‖f j x‖^2) ≤ volume.real K+B
        linarith [hvalue j])

theorem spectral_rellich_energy_compact_closure {J : Type*}
    (K : Set SpectralEuclidean) (hK : IsCompact K)
    (f : J → SpectralEuclidean → ℂ) (hf : ∀ j, ContDiff ℝ 1 (f j))
    (hs : ∀ j, tsupport (f j) ⊆ K) {B : ℝ} (hB : 0 ≤ B)
    (henergy : ∀ j, spectralEuclideanH1Energy (f j) ≤ B) :
    let hc : ∀ j, HasCompactSupport (f j) := fun j => hK.of_isClosed_subset (isClosed_tsupport _) (hs j)
    IsCompact (closure (range (fun j => spectralEuclideanLp (f j) (hf j).continuous (hc j)))) := by
  exact (spectral_rellich_energy_bounded K hK f hf hs hB henergy).closure.isCompact_of_isClosed isClosed_closure

end ArtinMatthews
