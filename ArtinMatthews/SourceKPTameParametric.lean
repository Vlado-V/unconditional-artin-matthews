module

public import ArtinMatthews.SourceKPTameSpherical
public import ArtinMatthews.SourceKPTameBorelValues
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine parameter family of local induced representations on the
actual tame cubic projective cover. The fixed staged model has parameter
`-1/6`. Twisting by `s+1/6` gives normalized inducing exponents `s,-s`. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "ν₀" => sourceKPFiniteVal K P
local notation "Q₀" => (Ideal.absNorm P.asIdeal : ℝ)

def sourceKPTameNormalizedBorelTwist (s : ℂ) : SourceFiniteKPNormalizedBorel K hζ P →* ℂ where
  toFun b := Complex.exp (-(s+1/6) *
    (sourceKPValuationOrder ν₀ (sourceFiniteKPNormalizedBorelBase K hζ P b) : ℂ) *
    (Real.log Q₀ : ℂ))
  map_one' := by
    rw [map_one, sourceKPValuationOrder_one]
    simp
  map_mul' b c := by
    rw [map_mul, sourceKPValuationOrder_mul, Int.cast_add]
    rw [show -(s+1/6) * ((sourceKPValuationOrder ν₀ (sourceFiniteKPNormalizedBorelBase K hζ P b) : ℂ) +
        (sourceKPValuationOrder ν₀ (sourceFiniteKPNormalizedBorelBase K hζ P c) : ℂ)) *
        (Real.log Q₀ : ℂ) =
      -(s+1/6) * (sourceKPValuationOrder ν₀ (sourceFiniteKPNormalizedBorelBase K hζ P b) : ℂ) *
          (Real.log Q₀ : ℂ) +
        -(s+1/6) * (sourceKPValuationOrder ν₀ (sourceFiniteKPNormalizedBorelBase K hζ P c) : ℂ) *
          (Real.log Q₀ : ℂ) by ring, Complex.exp_add]

def sourceKPTameBorelTwist (s : ℂ) : SourceFiniteKPProjectiveBorel K hζ P →* ℂ :=
  (sourceKPTameNormalizedBorelTwist K hζ P s).comp
    (sourceFiniteKPProjectiveBorelEquiv K hζ P).symm.toMonoidHom

theorem sourceKPTameBorelTwist_normalized (s : ℂ) (b : SourceFiniteKPNormalizedBorel K hζ P) :
    sourceKPTameBorelTwist K hζ P s (sourceFiniteKPProjectiveBorelEquiv K hζ P b) =
      sourceKPTameNormalizedBorelTwist K hζ P s b := by
  change sourceKPTameNormalizedBorelTwist K hζ P s
    ((sourceFiniteKPProjectiveBorelEquiv K hζ P).symm (sourceFiniteKPProjectiveBorelEquiv K hζ P b)) = _
  rw [MulEquiv.symm_apply_apply]

theorem sourceKPTameBorelTwist_diagonal (s : ℂ) (y : Lˣ) :
    sourceKPTameBorelTwist K hζ P s (sourceFiniteKPProjectiveBorelDiagonal K hζ P y) =
      Complex.exp (-(s+1/6) * (sourceKPValuationOrder ν₀ y : ℂ) * (Real.log Q₀ : ℂ)) := by
  rw [sourceFiniteKPProjectiveBorelDiagonal, sourceKPTameBorelTwist_normalized]
  change Complex.exp (-(s+1/6) * (sourceKPValuationOrder ν₀
    (GeneralLinearGroup.det (sourceGL2Diagonal y)) : ℂ) * (Real.log Q₀ : ℂ)) = _
  rw [sourceGL2Diagonal_det]

variable (h6 : (6 : 𝓞 K) ∉ P.asIdeal) (uniformizer : (P.adicCompletion K)ˣ)
    (hUniformizer : sourceKPFiniteVal K P (uniformizer : P.adicCompletion K) = WithZero.exp (-1 : ℤ))

def sourceKPTameParametricBorelRepresentation (s : ℂ) :
    Representation ℂ (SourceFiniteKPProjectiveBorel K hζ P) (ZMod 3 → ℂ) where
  toFun b := sourceKPTameBorelTwist K hζ P s b • sourceKPTameBorelRepresentation K hζ P h6 uniformizer hUniformizer b
  map_one' := by rw [map_one, map_one, one_smul]
  map_mul' b c := by
    change sourceKPTameBorelTwist K hζ P s (b*c) •
      sourceKPTameBorelRepresentation K hζ P h6 uniformizer hUniformizer (b*c) = _
    have hρ := (sourceKPTameBorelRepresentation K hζ P h6 uniformizer hUniformizer).map_mul b c
    have hσ := (sourceKPTameBorelTwist K hζ P s).map_mul b c
    rw [hρ, hσ]
    exact (smul_mul_smul_comm _ _ _ _).symm

theorem sourceKPTameParametricBorel_uniformizer_basis (s : ℂ) (j : ℤ) (i : ZMod 3) :
    sourceKPTameParametricBorelRepresentation K hζ P h6 uniformizer hUniformizer s
      (sourceFiniteKPProjectiveBorelDiagonal K hζ P (uniformizer^j)) (sourceJacquetBasis i) =
        Complex.exp (-(s+1/2)*(j : ℂ)*(Real.log Q₀ : ℂ)) • sourceJacquetBasis (i+(j : ZMod 3)) := by
  change sourceKPTameBorelTwist K hζ P s
    (sourceFiniteKPProjectiveBorelDiagonal K hζ P (uniformizer^j)) •
      sourceKPTameBorelRepresentation K hζ P h6 uniformizer hUniformizer
        (sourceFiniteKPProjectiveBorelDiagonal K hζ P (uniformizer^j)) (sourceJacquetBasis i) = _
  have horder := (sourceKPValuationOrder_eq ν₀ uniformizer 1).mpr hUniformizer
  rw [sourceKPTameBorelTwist_diagonal, sourceKPValuationOrder_zpow, horder, mul_one,
    sourceKPTameBorelRepresentation_uniformizer_basis, smul_smul]
  congr 1
  rw [sourceJacquetScale, Real.rpow_def_of_pos
    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot))),
    Complex.ofReal_exp, ← Complex.exp_add]
  push_cast
  congr 1
  ring

theorem sourceKPTameBorelTwist_compact (s : ℂ) (b : SourceFiniteKPProjectiveBorel K hζ P)
    (k : SourceFiniteKP2ProjectiveCompact K hζ P h6) (hbk : b.val = k.val) :
    sourceKPTameBorelTwist K hζ P s b = 1 := by
  obtain ⟨k₀, hk₀⟩ := k.property
  obtain ⟨g, hg, hd, hb⟩ := sourceFiniteKPProjectiveBorel_compact_lift K hζ P h6 b k₀ (hbk.trans hk₀.symm)
  rw [hb, sourceKPTameBorelTwist_normalized]
  change Complex.exp (-(s+1/6) * (sourceKPValuationOrder ν₀ (GeneralLinearGroup.det g) : ℂ) *
    (Real.log Q₀ : ℂ)) = 1
  rw [sourceKPValuationOrder_of_unit ν₀ _ hd]
  simp

theorem sourceKPTameParametricBorel_compact_fixed (s : ℂ) (b : SourceFiniteKPProjectiveBorel K hζ P)
    (k : SourceFiniteKP2ProjectiveCompact K hζ P h6) (hbk : b.val = k.val) :
    sourceKPTameParametricBorelRepresentation K hζ P h6 uniformizer hUniformizer s b (sourceJacquetBasis 0) =
      sourceJacquetBasis 0 := by
  change sourceKPTameBorelTwist K hζ P s b •
    sourceKPTameBorelRepresentation K hζ P h6 uniformizer hUniformizer b (sourceJacquetBasis 0) = _
  rw [sourceKPTameBorelTwist_compact K hζ P h6 s b k hbk,
    sourceKPTameBorelRepresentation_compact_fixed K hζ P h6 uniformizer hUniformizer b k hbk, one_smul]

abbrev SourceKPTameParametricInducedSpace (s : ℂ) :=
  sourceAlgebraicInducedSpace (sourceFiniteKPNormalizedBorelToProjective K hζ P).range
    (sourceKPTameParametricBorelRepresentation K hζ P h6 uniformizer hUniformizer s)

def sourceKPTameParametricSphericalSection (s : ℂ) :
    SourceKPTameParametricInducedSpace K hζ P h6 uniformizer hUniformizer s :=
  sourceAlgebraicSphericalSection (sourceFiniteKPNormalizedBorelToProjective K hζ P).range
    (sourceKPTameParametricBorelRepresentation K hζ P h6 uniformizer hUniformizer s)
    (sourceFiniteKP2ProjectiveCompactSection K hζ P h6).range (sourceJacquetBasis 0)
    (sourceFiniteKP2Projective_Iwasawa_range K hζ P h6)
    (sourceKPTameParametricBorel_compact_fixed K hζ P h6 uniformizer hUniformizer s)

theorem sourceKPTameParametricSphericalSection_factor (s : ℂ)
    (g : SourceFiniteKP2Projective K hζ P) (b : SourceFiniteKPProjectiveBorel K hζ P)
    (k : SourceFiniteKP2ProjectiveCompact K hζ P h6) (hg : g = b.val * k.val) :
    (sourceKPTameParametricSphericalSection K hζ P h6 uniformizer hUniformizer s).val g =
      sourceKPTameBorelTwist K hζ P s b •
        (sourceKPTameSphericalSection K hζ P h6 uniformizer hUniformizer).val g := by
  unfold sourceKPTameParametricSphericalSection sourceKPTameSphericalSection
  rw [sourceAlgebraicSphericalSection_factor _ _ _ _ _ _ hg,
    sourceAlgebraicSphericalSection_factor _ _ _ _ _ _ hg]
  rfl


theorem sourceKPTameParametricSphericalSection_one (s : ℂ) :
    (sourceKPTameParametricSphericalSection K hζ P h6 uniformizer hUniformizer s).val 1 = sourceJacquetBasis 0 :=
  sourceAlgebraicSphericalSection_one _ _ _ _ _ _

end
end ArtinMatthews
