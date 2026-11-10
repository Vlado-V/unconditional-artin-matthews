module

public import ArtinMatthews.SpectralGamma0EllipticEnergy
public import OAI.Analysis.PDE.Weak.Elliptic.H1
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
public import OAI.Analysis.PDE.Weak.Elliptic.H1Subspace


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compactly localized scalar function and its actual derivatives
form a native H1Pair in the closed graph used by InteriorH2. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff
open OAI.Analysis.PDE.Weak OAI.Analysis.PDE.Variational

namespace ArtinMatthews

theorem spectralEllipticScalar_add (L : ℂ →L[ℝ] ℝ)
    (F G : SchwartzMap (ℝ × ℝ) ℂ) :
    spectralEllipticScalar L (F+G) = spectralEllipticScalar L F + spectralEllipticScalar L G := by
  funext x
  simp only [spectralEllipticScalar,map_add,Pi.add_apply]

theorem spectralEllipticScalar_smul (L : ℂ →L[ℝ] ℝ) (c : ℝ)
    (F : SchwartzMap (ℝ × ℝ) ℂ) :
    spectralEllipticScalar L (c • F) = c • spectralEllipticScalar L F := by
  funext x
  simp only [spectralEllipticScalar,map_smul,Pi.smul_apply]

def spectralEllipticSmoothPair (L : ℂ →L[ℝ] ℝ)
    (F : SchwartzMap (ℝ × ℝ) ℂ) (hc : HasCompactSupport F) : H1Pair 1 :=
  smoothH1Pair (spectralEllipticScalar L F)
    (spectralEllipticScalar_contDiff L F (F.smooth (⊤ : ℕ∞)))
    (spectralEllipticScalar_compact L F hc)

theorem spectralEllipticSmoothPair_value_ae (L : ℂ →L[ℝ] ℝ)
    (F : SchwartzMap (ℝ × ℝ) ℂ) (hc : HasCompactSupport F) :
    (spectralEllipticSmoothPair L F hc).1 =ᵐ[volume] spectralEllipticScalar L F :=
  smoothH1Pair_value_ae _ _ _

theorem spectralEllipticSmoothPair_gradient_ae (L : ℂ →L[ℝ] ℝ)
    (F : SchwartzMap (ℝ × ℝ) ℂ) (hc : HasCompactSupport F) :
    (spectralEllipticSmoothPair L F hc).2 =ᵐ[volume]
      fun x => WithLp.toLp 2 (fun i : Fin 2 =>
        L (fderiv ℝ F (spectralEllipticCoordinates x) (spectralPlaneDirection i))) := by
  apply (smoothH1Pair_gradient_ae _ _ _).trans
  apply Filter.Eventually.of_forall
  intro x
  ext i
  exact spectralEllipticScalar_derivative L F (F.smooth (⊤ : ℕ∞)) x i

theorem spectralEllipticSmoothPair_mem_H1Zero (L : ℂ →L[ℝ] ℝ)
    (F : SchwartzMap (ℝ × ℝ) ℂ) (hc : HasCompactSupport F) :
    spectralEllipticSmoothPair L F hc ∈ H1Zero (univ : Set (Fin 2 → ℝ)) :=
  smoothH1Pair_mem_H1Zero _ _ _ (subset_univ _)

theorem spectralEllipticSmoothPair_value_norm_sq (L : ℂ →L[ℝ] ℝ)
    (F : SchwartzMap (ℝ × ℝ) ℂ) (hc : HasCompactSupport F) :
    ‖(spectralEllipticSmoothPair L F hc).1‖^2 =
      ∫ x : Fin 2 → ℝ, ‖spectralEllipticScalar L F x‖^2 := by
  unfold spectralEllipticSmoothPair smoothH1Pair
  exact norm_sq_toLp_eq_integral
    ((spectralEllipticScalar_contDiff L F (F.smooth (⊤ : ℕ∞))).continuous.memLp_of_hasCompactSupport
      (spectralEllipticScalar_compact L F hc))

theorem spectralEllipticSmoothPair_energy (L : ℂ →L[ℝ] ℝ)
    (F : SchwartzMap (ℝ × ℝ) ℂ) (hc : HasCompactSupport F) :
    ‖(spectralEllipticSmoothPair L F hc).1‖^2 +
      ‖(spectralEllipticSmoothPair L F hc).2‖^2 = spectralEllipticScalarEnergy L F := by
  unfold spectralEllipticSmoothPair smoothH1Pair
  rw [norm_sq_toLp_eq_integral,norm_sq_toLp_eq_integral]
  simp only [EuclideanSpace.norm_sq_eq,cellGradient_apply,spectralEllipticScalarEnergy]

theorem spectralEllipticSmoothPair_norm_sq_le_energy (L : ℂ →L[ℝ] ℝ)
    (F : SchwartzMap (ℝ × ℝ) ℂ) (hc : HasCompactSupport F) :
    ‖spectralEllipticSmoothPair L F hc‖^2 ≤ spectralEllipticScalarEnergy L F := by
  rw [← spectralEllipticSmoothPair_energy L F hc]
  let p := spectralEllipticSmoothPair L F hc
  change ‖p‖^2 ≤ ‖p.1‖^2+‖p.2‖^2
  rw [Prod.norm_def]
  rcases le_total ‖p.1‖ ‖p.2‖ with h | h
  · rw [max_eq_right h]
    exact le_add_of_nonneg_left (sq_nonneg _)
  · rw [max_eq_left h]
    exact le_add_of_nonneg_right (sq_nonneg _)

theorem spectralEllipticSmoothPair_norm_sq_le (L : ℂ →L[ℝ] ℝ)
    (F : SchwartzMap (ℝ × ℝ) ℂ) (hc : HasCompactSupport F) :
    ‖spectralEllipticSmoothPair L F hc‖^2 ≤
      ‖L‖^2 * ((∫ p, ‖F p‖^2)+∫ p, h2DirichletDensity F F p) :=
  (spectralEllipticSmoothPair_norm_sq_le_energy L F hc).trans
    (spectralEllipticScalarEnergy_le L F hc)

theorem spectralEllipticSmoothPair_add (L : ℂ →L[ℝ] ℝ)
    (F G : SchwartzMap (ℝ × ℝ) ℂ) (hcF : HasCompactSupport F) (hcG : HasCompactSupport G) :
    spectralEllipticSmoothPair L (F+G) (hcF.add hcG) =
      spectralEllipticSmoothPair L F hcF + spectralEllipticSmoothPair L G hcG := by
  have he := spectralEllipticScalar_add L F G
  simpa only [spectralEllipticSmoothPair,FunLike.coe_add,← he] using
    smoothH1Pair_add (spectralEllipticScalar L F) (spectralEllipticScalar L G)
      (spectralEllipticScalar_contDiff L F (F.smooth (⊤ : ℕ∞)))
      (spectralEllipticScalar_contDiff L G (G.smooth (⊤ : ℕ∞)))
      (spectralEllipticScalar_compact L F hcF) (spectralEllipticScalar_compact L G hcG)

theorem spectralEllipticSmoothPair_smul (L : ℂ →L[ℝ] ℝ) (c : ℝ)
    (F : SchwartzMap (ℝ × ℝ) ℂ) (hc : HasCompactSupport F) :
    spectralEllipticSmoothPair L (c • F) hc.smul_left =
      c • spectralEllipticSmoothPair L F hc := by
  have he := spectralEllipticScalar_smul L c F
  simpa only [spectralEllipticSmoothPair,FunLike.coe_smul,← he] using
    smoothH1Pair_smul c (spectralEllipticScalar L F)
      (spectralEllipticScalar_contDiff L F (F.smooth (⊤ : ℕ∞)))
      (spectralEllipticScalar_compact L F hc)

end ArtinMatthews
