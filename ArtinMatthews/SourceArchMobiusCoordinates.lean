module

public import OAI.NumberTheory.DirichletL.CubicSieve.RowCaps
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine Mobius action in normed Cartesian coordinates and its generators. -/
namespace ArtinMatthews.SourceArchJacquet
open Matrix OAI.CubicEisenstein
open scoped MatrixGroups
noncomputable section

def sourceArchMobiusEuclidean (g : SL(2, ℂ)) (p : EuclideanSpatial) : EuclideanSpatial :=
  WithLp.toLp 2 (mobiusSpatial g p.ofLp)

lemma sourceArchMobiusEuclidean_positive (g : SL(2, ℂ)) (p : EuclideanSpatial)
    (hp : 0 < p 2) : 0 < sourceArchMobiusEuclidean g p 2 :=
  mobiusSpatial_positive g p.ofLp hp

lemma sourceArchMobiusEuclidean_coordinates (g : SL(2, ℂ)) (p : EuclideanSpatial)
    (hp : 0 < p 2) :
    sourceArchMobiusEuclidean g p = WithLp.toLp 2
      (hyperbolicSpatialCoordinates (g • upperPoint (spatialHorizontal p.ofLp) (p 2) hp)) :=
  congrArg (WithLp.toLp 2) (mobiusSpatial_coordinates g p.ofLp hp).symm

lemma sourceArchMobiusEuclidean_mul (g h : SL(2, ℂ)) (p : EuclideanSpatial)
    (hp : 0 < p 2) :
    sourceArchMobiusEuclidean (g * h) p =
      sourceArchMobiusEuclidean g (sourceArchMobiusEuclidean h p) := by
  apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
  change mobiusSpatial (g * h) p.ofLp = mobiusSpatial g (mobiusSpatial h p.ofLp)
  rw [← mobiusSpatial_coordinates (g * h) p.ofLp hp, mul_smul,
    mobiusSpatial_coordinates_global, mobiusSpatial_coordinates h p.ofLp hp]

lemma sourceArchMobiusEuclidean_translation (b : ℂ) (p : EuclideanSpatial) (hp : 0 < p 2) :
    sourceArchMobiusEuclidean (complexTranslation b) p = p + euclideanHorizontalTranslation b := by
  rw [sourceArchMobiusEuclidean_coordinates _ p hp, complexTranslation_action]
  ext j
  fin_cases j <;>
    simp [hyperbolicSpatialCoordinates, hyperbolicHorizontal_upperPoint, hyperbolicHeight_upperPoint,
      spatialHorizontal, euclideanHorizontalTranslation]

lemma sourceArchMobiusEuclidean_diagonal (b : ℂ) (hb : b ≠ 0)
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    sourceArchMobiusEuclidean (complexDiagonal b hb) p = euclideanComplexDilation b p := by
  rw [sourceArchMobiusEuclidean_coordinates _ p hp, complexDiagonal_action]
  simp only [hyperbolicSpatialCoordinates, hyperbolicHorizontal_upperPoint, hyperbolicHeight_upperPoint]
  obtain ⟨h0, h1, h2⟩ := euclideanComplexDilation_apply b p
  ext j
  fin_cases j
  · change (b ^ 2 * spatialHorizontal p.ofLp).re = euclideanComplexDilation b p 0
    rw [h0]
    simp [spatialHorizontal, Complex.mul_re, Complex.mul_im]
  · change (b ^ 2 * spatialHorizontal p.ofLp).im = euclideanComplexDilation b p 1
    rw [h1]
    simp [spatialHorizontal, Complex.mul_re, Complex.mul_im]
    ring
  · exact h2.symm

lemma sourceArchMobiusEuclidean_weyl (p : EuclideanSpatial) (hp : 0 < p 2) :
    sourceArchMobiusEuclidean complexWeyl p = euclideanWeylAction p := by
  rw [sourceArchMobiusEuclidean_coordinates _ p hp, complexWeyl_action]
  simp only [hyperbolicSpatialCoordinates, hyperbolicHorizontal_upperPoint, hyperbolicHeight_upperPoint]
  have hz : ‖spatialHorizontal p.ofLp‖ ^ 2 + (p 2) ^ 2 = ‖p‖ ^ 2 := by
    simpa [spatialHorizontal, mul_comm] using euclidean_complex_norm_sq p
  rw [hz]
  have hn := norm_ne_zero_iff.mpr (euclideanUpperHalf_ne_zero p hp)
  have hzr : (spatialHorizontal p.ofLp).re = p 0 := by simp [spatialHorizontal]
  have hzi : (spatialHorizontal p.ofLp).im = p 1 := by simp [spatialHorizontal]
  obtain ⟨h0, h1, h2⟩ := euclideanWeylAction_apply p
  ext j
  fin_cases j
  · change (-star (spatialHorizontal p.ofLp) / ((‖p‖ ^ 2 : ℝ) : ℂ)).re =
      euclideanWeylAction p 0
    rw [h0]
    rw [Complex.div_ofReal_re, Complex.neg_re, Complex.star_def, Complex.conj_re, hzr]
    field_simp [hn]
  · change (-star (spatialHorizontal p.ofLp) / ((‖p‖ ^ 2 : ℝ) : ℂ)).im =
      euclideanWeylAction p 1
    rw [h1]
    rw [Complex.div_ofReal_im, Complex.neg_im, Complex.star_def, Complex.conj_im, neg_neg, hzi]
    field_simp [hn]
  · change p 2 / ‖p‖ ^ 2 = euclideanWeylAction p 2
    rw [h2]
    field_simp [hn]

end
end ArtinMatthews.SourceArchJacquet
