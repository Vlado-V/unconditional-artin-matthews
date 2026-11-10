module

public import ArtinMatthews.SourceFiniteKPProjectiveBorel
public import ArtinMatthews.SourceKPDeepCongruence
public import ArtinMatthews.SourceKPIntegralMatrixTopology
public import ArtinMatthews.SourceKPIntegralMatrixValuation
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

/-! The genuine compact part of the local cubic cover is the full
preimage of the projectivized integral matrix group. This includes the
wild places, where the full compact group has no chosen splitting.
The given deep subgroup has the actual phase-one splitting. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "O" => P.adicCompletionIntegers K
local notation "G" => SourceFiniteKP2Projective K hζ P
local notation "p₀" => sourceFiniteKP2ProjectiveProjection K hζ P
local notation "z₀" => sourceFiniteKP2ProjectiveCenter K hζ P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P
local notation "i₀" => sourceKPIntegralMatrixMap K P

def sourceKPLocalCompactBase : Subgroup PGL(2, L) :=
  (ProjGenLinGroup.mk.comp i₀).range

def sourceKPLocalCompactCover : Subgroup G :=
  (sourceKPLocalCompactBase K P).comap p₀

local notation "C" => sourceKPLocalCompactCover K hζ P

theorem sourceKPLocalCompactLift_projection (z : rootsOfUnity 3 L) (a : GL (Fin 2) O) :
    p₀ (z₀ z*l₀ (i₀ a)) = ProjGenLinGroup.mk (i₀ a) := by
  rw [map_mul]
  change (ProjGenLinGroup.mk (1 : GL (Fin 2) L)) * ProjGenLinGroup.mk (i₀ a) = _
  rw [map_one, one_mul]

def sourceKPLocalCompactLift (z : rootsOfUnity 3 L) (a : GL (Fin 2) O) : C :=
  ⟨z₀ z*l₀ (i₀ a), by
    change p₀ (z₀ z*l₀ (i₀ a)) ∈ sourceKPLocalCompactBase K P
    rw [sourceKPLocalCompactLift_projection K hζ P]
    exact ⟨a,rfl⟩⟩

theorem sourceKPLocalCompactLift_surjective (g : C) :
    ∃ (z : rootsOfUnity 3 L) (a : GL (Fin 2) O), g = sourceKPLocalCompactLift K hζ P z a := by
  obtain ⟨a,ha⟩ := g.property
  let h := l₀ (i₀ a)
  have he : p₀ h = p₀ g.val := ha
  have hk : g.val*h⁻¹ ∈ (p₀).ker := by
    change p₀ (g.val*h⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  rw [← sourceFiniteKP2Projective_exact K hζ P] at hk
  obtain ⟨z,hz⟩ := hk
  refine ⟨z,a,Subtype.ext ?_⟩
  change g.val = z₀ z*h
  rw [hz, inv_mul_cancel_right]

def sourceKPLocalCompactDeepLift : sourceKPDeepIntegralGroup K P →* C :=
  ((sourceFiniteKP2ProjectiveMk K hζ P).comp (sourceKPDeepLocalSection K P hζ)).codRestrict C
    (fun a => ⟨a.val, rfl⟩)

def sourceKPLocalCompactDeep : Subgroup C := (sourceKPLocalCompactDeepLift K hζ P).range

theorem sourceKPLocalCompactDeepLift_val (a : sourceKPDeepIntegralGroup K P) :
    (sourceKPLocalCompactDeepLift K hζ P a).val = l₀ (i₀ a.val) := rfl

theorem sourceKPLocalCompactCover_Iwasawa (g : G) :
    ∃ (b : SourceFiniteKPProjectiveBorel K hζ P) (k : C), g = b.val*k.val := by
  obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (sourceFiniteKP2Scalar K hζ P).range g
  change sourceFiniteKP2ProjectiveMk K hζ P x = g at hx
  obtain ⟨b₀,d,k₀,hb,hk,hx₀⟩ := sourceKPIwasawa_matrix_factor (sourceKPFiniteVal K P) x.base
  obtain ⟨a,ha⟩ := (sourceKPIntegralMatrixMap_mem_range K P k₀).mpr hk
  let k := sourceFiniteKP2Lift K hζ P k₀
  let t := sourceFiniteKP2Scalar K hζ P d
  let b := x*k⁻¹*t⁻¹
  have hb₀ : b.base = b₀ := by
    let p := sourceFiniteKP2Projection K hζ P
    change p (x*k⁻¹*t⁻¹) = b₀
    rw [map_mul p, map_mul p, map_inv p, map_inv p]
    change x.base*k₀⁻¹*(GeneralLinearGroup.scalar (Fin 2) d)⁻¹ = b₀
    rw [hx₀, mul_inv_cancel_right, mul_inv_cancel_right]
  have hb₁ : b ∈ sourceFiniteKPNormalizedBorelSubgroup K hζ P := by
    change b.base ∈ sourceGL2NormalizedBorel L
    rwa [hb₀]
  let kb : C := ⟨l₀ k₀,⟨a,congrArg ProjGenLinGroup.mk ha⟩⟩
  refine ⟨sourceFiniteKPProjectiveBorelEquiv K hζ P ⟨b,hb₁⟩,kb,?_⟩
  rw [sourceFiniteKPProjectiveBorelEquiv_val]
  let m := sourceFiniteKP2ProjectiveMk K hζ P
  change g = m (x*k⁻¹*t⁻¹)*m k
  rw [map_mul m, map_mul m, map_inv m, map_inv m]
  change g = m x*(m k)⁻¹*(m (sourceFiniteKP2Scalar K hζ P d))⁻¹*m k
  rw [sourceFiniteKP2ProjectiveMk_scalar, inv_one, mul_one, inv_mul_cancel_right, hx]

end
end ArtinMatthews
