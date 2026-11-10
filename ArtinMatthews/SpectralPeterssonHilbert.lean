module

public import ArtinMatthews.SpectralPeterssonPairingUnfold
public import ArtinMatthews.SpectralPeterssonWeightedBound
public import ArtinMatthews.SpectralPeterssonHeckePairingLimit
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

/-! The literal Petersson integral is the inner product of the actual
weight-corrected L² vectors on the native Gamma0 region. -/

noncomputable section
open MeasureTheory UpperHalfPlane Filter
open scoped InnerProductSpace ComplexConjugate

namespace ArtinMatthews

def spectralPeterssonHilbertProfile (k : ℕ) (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  ((z.im^((k : ℝ)/2) : ℝ) : ℂ)*F z

theorem spectralPeterssonHilbertProfile_norm (k : ℕ) (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    ‖spectralPeterssonHilbertProfile k F z‖ = spectralPeterssonWeightedNorm k F z := by
  unfold spectralPeterssonHilbertProfile spectralPeterssonWeightedNorm
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg z.im_pos.le _),mul_comm]

theorem gamma0PeterssonHilbertProfile_memLp (N : ℕ) [NeZero N] (k : ℕ) (F : UpperHalfPlane → ℂ)
    (hF : Continuous F) (M : ℝ) (hM : ∀ z, spectralPeterssonWeightedNorm k F z ≤ M) :
    MemLp (spectralPeterssonHilbertProfile k F) 2 (volume.restrict (gamma0InteriorRegion N)) := by
  let _ : IsFiniteMeasure (volume.restrict (gamma0InteriorRegion N)) := ⟨by
    simpa using gamma0InteriorRegion_volume_lt_top N⟩
  have h : Continuous (spectralPeterssonHilbertProfile k F) :=
    (Complex.continuous_ofReal.comp (continuous_im.rpow_const (fun z => Or.inl z.im_ne_zero))).mul hF
  exact MemLp.of_bound h.aestronglyMeasurable M (Eventually.of_forall fun z => by
    rw [spectralPeterssonHilbertProfile_norm]; exact hM z)

theorem gamma0PeterssonInner_eq_hilbert (N k : ℕ) (F G : UpperHalfPlane → ℂ)
    (hf : MemLp (spectralPeterssonHilbertProfile k F) 2 (volume.restrict (gamma0InteriorRegion N)))
    (hg : MemLp (spectralPeterssonHilbertProfile k G) 2 (volume.restrict (gamma0InteriorRegion N))) :
    ⟪hf.toLp (spectralPeterssonHilbertProfile k F), hg.toLp (spectralPeterssonHilbertProfile k G)⟫_ℂ =
      gamma0PeterssonInner N k F G := by
  rw [MeasureTheory.L2.inner_def]
  unfold gamma0PeterssonInner
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with z hfz hgz
  rw [hfz,hgz]
  let y := z.im
  let p := y^((k : ℝ)/2)
  have hy : 0 < y := z.im_pos
  have hp : p*p = y^k := by
    dsimp only [p]
    rw [← Real.rpow_add hy,show (k : ℝ)/2+(k : ℝ)/2=k by ring,Real.rpow_natCast]
  have hpC : (p : ℂ)*(p : ℂ) = (y : ℂ)^k := by exact_mod_cast hp
  rw [RCLike.inner_apply]
  change ((p : ℂ)*G z)*conj ((p : ℂ)*F z) = _
  unfold UpperHalfPlane.petersson
  simp only [map_mul,Complex.conj_ofReal,zpow_natCast]
  calc
    _ = conj (F z)*G z*((p : ℂ)*(p : ℂ)) := by ring
    _ = _ := by rw [hpC]

theorem gamma0PeterssonHilbert_diagonal_norm (N k : ℕ) (F : UpperHalfPlane → ℂ)
    (hF : MemLp (spectralPeterssonHilbertProfile k F) 2 (volume.restrict (gamma0InteriorRegion N))) :
    ‖hF.toLp (spectralPeterssonHilbertProfile k F)‖^2 = (gamma0PeterssonInner N k F F).re := by
  rw [← gamma0PeterssonInner_eq_hilbert N k F F hF hF]
  exact @norm_sq_eq_re_inner ℂ _ _ _ _ _

end ArtinMatthews
