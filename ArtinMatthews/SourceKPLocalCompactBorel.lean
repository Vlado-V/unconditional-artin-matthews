module

public import ArtinMatthews.SourceKPLocalCompactGroup
public import ArtinMatthews.SourceKPTameParametric
public import ArtinMatthews.SourceKPCompactDiagonal
public import ArtinMatthews.SourceKPIntegralMatrixValuation
public import ArtinMatthews.SourceKubotaFullScalars
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

/-! On the compact Borel intersection the normalized diagonal ratio
has valuation zero. Consequently the actual spectral parameter twist
is trivial there, including at ramified places. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "O" => P.adicCompletionIntegers K
local notation "C" => sourceKPLocalCompactCover K hζ P
local notation "B" => SourceFiniteKPProjectiveBorel K hζ P
local notation "ν₀" => sourceKPFiniteVal K P
local notation "i₀" => sourceKPIntegralMatrixMap K P
local notation "e₀" => sourceFiniteKPProjectiveBorelEquiv K hζ P
local notation "p₀" => sourceFiniteKP2ProjectiveProjection K hζ P
local notation "d₀" => sourceFiniteKPNormalizedBorelBase K hζ P

theorem sourceKPLocalCompactBorel_base_valuation (b : B) (hb : b.val ∈ C) :
    ν₀ ((d₀ ((e₀).symm b) : Lˣ) : L) = 1 := by
  let q := (e₀).symm b
  obtain ⟨a,ha⟩ := hb
  let A := i₀ a
  have hq : ProjGenLinGroup.mk A = ProjGenLinGroup.mk q.val.base := by
    change ProjGenLinGroup.mk A = p₀ (sourceFiniteKP2ProjectiveMk K hζ P q.val)
    rw [← sourceFiniteKPProjectiveBorelEquiv_val K hζ P q]
    change (ProjGenLinGroup.mk.comp i₀) a = p₀ (e₀ ((e₀).symm b)).val
    rw [MulEquiv.apply_symm_apply]
    exact ha
  obtain ⟨t,ht⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hq
  have hbot := sourceFiniteKPNormalizedBorel_bottom K hζ P q
  have hA := sourceKPIntegralMatrixMap_integral K P a
  have hleft := congrArg (fun g : GL (Fin 2) L => g 1 0) ht
  change (A*GeneralLinearGroup.scalar (Fin 2) t) 1 0 = q.val.base 1 0 at hleft
  rw [sourceGL2_right_scalar_apply, hbot.1] at hleft
  have hA₀ : A 1 0 = 0 := (mul_eq_zero.mp hleft).resolve_right t.ne_zero
  have hA₁ : ν₀ (A 1 1) = 1 := by
    rcases sourceKPIntegralMatrix_bottom_unit ν₀ hA with h | h
    · rw [hA₀,map_zero] at h
      exact (zero_ne_one h).elim
    · exact h
  have hright := congrArg (fun g : GL (Fin 2) L => g 1 1) ht
  change (A*GeneralLinearGroup.scalar (Fin 2) t) 1 1 = q.val.base 1 1 at hright
  rw [sourceGL2_right_scalar_apply,hbot.2] at hright
  have htν : ν₀ (t : L) = 1 := by
    have h := congrArg ν₀ hright
    rwa [map_mul,hA₁,one_mul,map_one] at h
  change ν₀ (GeneralLinearGroup.det q.val.base : L) = 1
  rw [← ht, map_mul, Units.val_mul, map_mul, sourceGL2_scalar_det]
  change ν₀ (GeneralLinearGroup.det A : L) * ν₀ ((t : L)^2) = 1
  rw [hA.det_unit, map_pow, htν, one_pow, mul_one]

theorem sourceKPLocalCompactBorel_order_zero (b : B) (hb : b.val ∈ C) :
    sourceKPValuationOrder ν₀ (d₀ ((e₀).symm b)) = 0 :=
  sourceKPValuationOrder_of_unit ν₀ _ (sourceKPLocalCompactBorel_base_valuation K hζ P b hb)

theorem sourceKPLocalCompactBorel_twist_one (s : ℂ) (b : B) (hb : b.val ∈ C) :
    sourceKPTameBorelTwist K hζ P s b = 1 := by
  change Complex.exp (-(s+1/6) * (sourceKPValuationOrder ν₀ (d₀ ((e₀).symm b)) : ℂ) *
    (Real.log (Ideal.absNorm P.asIdeal : ℝ) : ℂ)) = 1
  rw [sourceKPLocalCompactBorel_order_zero K hζ P b hb]
  simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero]

end
end ArtinMatthews
