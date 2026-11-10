module

public import ArtinMatthews.SourceFiniteKPProjectiveBorel
public import ArtinMatthews.SourceFiniteKP2CompactSection
public import ArtinMatthews.SourceKPIwasawaMatrices
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Iwasawa decomposition on the actual local projective cubic cover.
The scalar in the integral matrix decomposition is removed by the
proved scalar quotient. The residual phase stays in the Borel lift. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (h6 : (6 : 𝓞 K) ∉ P.asIdeal)

def sourceFiniteKP2ProjectiveCompactSection :
    SourceFiniteKP2Integral K P →* SourceFiniteKP2Projective K hζ P :=
  (sourceFiniteKP2ProjectiveMk K hζ P).comp (sourceFiniteKP2CompactSection K hζ P h6)

abbrev SourceFiniteKP2ProjectiveCompact := (sourceFiniteKP2ProjectiveCompactSection K hζ P h6).range

theorem sourceFiniteKP2Projective_Iwasawa (g : SourceFiniteKP2Projective K hζ P) :
    ∃ (b : SourceFiniteKPProjectiveBorel K hζ P) (k : SourceFiniteKP2Integral K P),
      g = b.val * sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (sourceFiniteKP2Scalar K hζ P).range g
  change sourceFiniteKP2ProjectiveMk K hζ P x = g at hx
  obtain ⟨b₀, d, k₀, hb₀, hk₀, hfactor⟩ :=
    sourceKPIwasawa_matrix_factor (sourceKPFiniteVal K P) x.base
  let k : SourceFiniteKP2Integral K P := ⟨k₀, hk₀⟩
  let l := sourceFiniteKP2CompactSection K hζ P h6 k
  let s := sourceFiniteKP2Scalar K hζ P d
  let b₁ := x * l⁻¹ * s⁻¹
  have hbase : b₁.base = b₀ := by
    let p := sourceFiniteKP2Projection K hζ P
    change p (x * l⁻¹ * s⁻¹) = b₀
    rw [map_mul p, map_mul p, map_inv p, map_inv p]
    change x.base * k₀⁻¹ * (GeneralLinearGroup.scalar (Fin 2) d)⁻¹ = b₀
    rw [hfactor, mul_inv_cancel_right, mul_inv_cancel_right]
  have hb₁ : b₁ ∈ sourceFiniteKPNormalizedBorelSubgroup K hζ P := by
    change b₁.base ∈ sourceGL2NormalizedBorel (P.adicCompletion K)
    rwa [hbase]
  refine ⟨sourceFiniteKPProjectiveBorelEquiv K hζ P ⟨b₁, hb₁⟩, k, ?_⟩
  rw [sourceFiniteKPProjectiveBorelEquiv_val]
  let m := sourceFiniteKP2ProjectiveMk K hζ P
  change g = m (x * l⁻¹ * s⁻¹) * m l
  rw [map_mul m, map_mul m, map_inv m, map_inv m]
  change g = m x * (m l)⁻¹ * (m (sourceFiniteKP2Scalar K hζ P d))⁻¹ * m l
  rw [sourceFiniteKP2ProjectiveMk_scalar, inv_one, mul_one, inv_mul_cancel_right, hx]

theorem sourceFiniteKP2Projective_Iwasawa_range (g : SourceFiniteKP2Projective K hζ P) :
    ∃ (b : SourceFiniteKPProjectiveBorel K hζ P) (k : SourceFiniteKP2ProjectiveCompact K hζ P h6),
      g = b.val * k.val := by
  obtain ⟨b, k, h⟩ := sourceFiniteKP2Projective_Iwasawa K hζ P h6 g
  exact ⟨b, ⟨sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k, ⟨k, rfl⟩⟩, h⟩

end
end ArtinMatthews
