module

public import ArtinMatthews.SourceKPLocalCompactGroup
public import ArtinMatthews.SourceKPDeepCongruenceTopology
public import ArtinMatthews.SourceKPLocalCompactCosets
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

/-! The projected compact group and the actual deep image are
compact-open in the native projective topology. On the phase-one
deep subgroup the covering projection is injective. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Topology
open scoped MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "G" => SourceFiniteKP2Projective K hζ P
local notation "C" => sourceKPLocalCompactCover K hζ P
local notation "J" => sourceKPLocalCompactDeep K hζ P
local notation "p₀" => sourceFiniteKP2ProjectiveProjection K hζ P

def sourceKPLocalProjectiveTopology : TopologicalSpace PGL(2, L) :=
  inferInstanceAs (TopologicalSpace (GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L)))

attribute [local instance] sourceKPLocalProjectiveTopology

theorem sourceKPLocalProjective_mk_isOpenMap : IsOpenMap (ProjGenLinGroup.mk : GL (Fin 2) L → PGL(2, L)) :=
  QuotientGroup.isOpenQuotientMap_mk.isOpenMap

theorem sourceKPLocalProjective_mk_continuous : Continuous (ProjGenLinGroup.mk : GL (Fin 2) L → PGL(2, L)) :=
  QuotientGroup.continuous_mk

def sourceKPLocalCompactDeepBase : Subgroup PGL(2, L) :=
  (ProjGenLinGroup.mk.comp (sourceKPDeepLocalBase K P)).range

theorem sourceKPLocalCompactBase_set :
    (sourceKPLocalCompactBase K P : Set PGL(2, L)) =
      ProjGenLinGroup.mk '' Set.range (sourceKPIntegralMatrixMap K P) := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨_,⟨a,rfl⟩,rfl⟩
  · rintro ⟨_,⟨a,rfl⟩,rfl⟩
    exact ⟨a,rfl⟩

theorem sourceKPLocalCompactDeepBase_set :
    (sourceKPLocalCompactDeepBase K P : Set PGL(2, L)) =
      ProjGenLinGroup.mk '' Set.range (sourceKPDeepLocalBase K P) := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨_,⟨a,rfl⟩,rfl⟩
  · rintro ⟨_,⟨a,rfl⟩,rfl⟩
    exact ⟨a,rfl⟩

theorem sourceKPLocalCompactBase_isOpen : IsOpen (sourceKPLocalCompactBase K P : Set PGL(2, L)) := by
  rw [sourceKPLocalCompactBase_set]
  exact sourceKPLocalProjective_mk_isOpenMap K P _ (sourceKPIntegralMatrixGroup_isOpen K P)

theorem sourceKPLocalCompactBase_isCompact : IsCompact (sourceKPLocalCompactBase K P : Set PGL(2, L)) := by
  rw [sourceKPLocalCompactBase_set]
  exact (sourceKPIntegralMatrixGroup_isCompact K P).image (sourceKPLocalProjective_mk_continuous K P)

theorem sourceKPLocalCompactDeepBase_isOpen : IsOpen (sourceKPLocalCompactDeepBase K P : Set PGL(2, L)) := by
  rw [sourceKPLocalCompactDeepBase_set]
  exact sourceKPLocalProjective_mk_isOpenMap K P _ (sourceKPDeepLocalBase_range_isOpen K P)

theorem sourceKPLocalCompactDeepBase_isCompact : IsCompact (sourceKPLocalCompactDeepBase K P : Set PGL(2, L)) := by
  rw [sourceKPLocalCompactDeepBase_set]
  exact (sourceKPDeepLocalBase_range_isCompact K P).image (sourceKPLocalProjective_mk_continuous K P)

def sourceKPLocalCompactDeepCoverLevel : Subgroup G := (J).map (C).subtype

theorem sourceKPLocalCompactDeepCoverLevel_projection :
    (sourceKPLocalCompactDeepCoverLevel K hζ P).map p₀ = sourceKPLocalCompactDeepBase K P := by
  ext x
  constructor
  · rintro ⟨_,⟨a,⟨b,rfl⟩,rfl⟩,rfl⟩
    exact ⟨b,rfl⟩
  · rintro ⟨b,rfl⟩
    let a := sourceKPLocalCompactDeepLift K hζ P b
    exact ⟨a.val,⟨a,⟨b,rfl⟩,rfl⟩,rfl⟩

theorem sourceKPLocalCompactDeepCoverLevel_projection_injective :
    Set.InjOn p₀ (sourceKPLocalCompactDeepCoverLevel K hζ P : Set G) := by
  intro x hx y hy hp
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,rfl⟩ := hy
  change p₀ a.val = p₀ b.val at hp
  let j : J := ⟨a⁻¹*b,(J).mul_mem ((J).inv_mem ha) hb⟩
  have h : p₀ j.val.val = 1 := by
    change p₀ (a.val⁻¹*b.val) = 1
    rw [map_mul,map_inv,hp,inv_mul_cancel]
  have hj := sourceKPLocalCompactDeep_projection_eq_one K hζ P j h
  have he : a⁻¹*b = 1 := congrArg Subtype.val hj
  exact congrArg Subtype.val (inv_mul_eq_one.mp he)

end
end ArtinMatthews
