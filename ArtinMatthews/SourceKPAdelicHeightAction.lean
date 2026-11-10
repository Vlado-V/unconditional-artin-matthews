module

public import ArtinMatthews.SourceKPAdelicHeight
public import ArtinMatthews.SourceKPAdelicHeightFactor
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact Borel covariance and compact invariance of the actual
adelic Iwasawa height. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicHeight_left_borel (b g : GL (Fin 2) 𝔸[K])
    (hb : b ∈ sourceKPRingNormalizedBorel 𝔸[K]) :
    sourceKPAdelicHeight K hζ (b*g) =
      sourceKPIdeleAbsoluteNorm K (GeneralLinearGroup.det b) * sourceKPAdelicHeight K hζ g := by
  have hbg : b * sourceKPAdelicIwasawaBorel K hζ g ∈ sourceKPRingNormalizedBorel 𝔸[K] :=
    (sourceKPRingNormalizedBorel 𝔸[K]).mul_mem hb (sourceKPAdelicIwasawaBorel_mem K hζ g)
  have he : b*g = (b*sourceKPAdelicIwasawaBorel K hζ g) *
      GeneralLinearGroup.scalar (Fin 2) (sourceKPAdelicIwasawaScalar K hζ g) *
        sourceKPAdelicIwasawaCompact K hζ g := by
    conv_lhs => rw [sourceKPAdelicIwasawa_factor K hζ g]
    group
  rw [sourceKPAdelicHeight_factor K hζ _ _ _ _ hbg
    (sourceKPAdelicIwasawaCompact_mem K hζ g) he, map_mul, map_mul]
  rfl

theorem sourceKPAdelicHeight_right_baseCompact (g k : GL (Fin 2) 𝔸[K])
    (hk : k ∈ SourceKPAdelicBaseCompactMatrix K hζ) :
    sourceKPAdelicHeight K hζ (g*k) = sourceKPAdelicHeight K hζ g := by
  have hk' : sourceKPAdelicIwasawaCompact K hζ g * k ∈ SourceKPAdelicBaseCompactMatrix K hζ :=
    (SourceKPAdelicBaseCompactMatrix K hζ).mul_mem (sourceKPAdelicIwasawaCompact_mem K hζ g) hk
  have he : g*k = sourceKPAdelicIwasawaBorel K hζ g *
      GeneralLinearGroup.scalar (Fin 2) (sourceKPAdelicIwasawaScalar K hζ g) *
        (sourceKPAdelicIwasawaCompact K hζ g*k) := by
    conv_lhs => rw [sourceKPAdelicIwasawa_factor K hζ g]
    group
  exact sourceKPAdelicHeight_factor K hζ _ _ _ _
    (sourceKPAdelicIwasawaBorel_mem K hζ g) hk' he

theorem sourceKPAdelicHeight_left_rationalBorel (b : GL (Fin 2) K)
    (hb : b ∈ sourceKPRingNormalizedBorel K) (g : GL (Fin 2) 𝔸[K]) :
    sourceKPAdelicHeight K hζ (GeneralLinearGroup.map (algebraMap K 𝔸[K]) b*g) =
      sourceKPAdelicHeight K hζ g := by
  have hb' : GeneralLinearGroup.map (algebraMap K 𝔸[K]) b ∈ sourceKPRingNormalizedBorel 𝔸[K] := by
    constructor
    · change algebraMap K 𝔸[K] (b 1 0) = 0
      rw [hb.1, map_zero]
    · change algebraMap K 𝔸[K] (b 1 1) = 1
      rw [hb.2, map_one]
  rw [sourceKPAdelicHeight_left_borel K hζ _ g hb', GeneralLinearGroup.map_det]
  change sourceKPIdeleAbsoluteNorm K (IdeleGroup.unitEmbedding (𝓞 K) K
    (GeneralLinearGroup.det b)) * sourceKPAdelicHeight K hζ g = _
  rw [sourceKPIdeleAbsoluteNorm_principal, one_mul]

end
end ArtinMatthews
