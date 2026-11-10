module

public import ArtinMatthews.SourceFiniteKPTameUnits
public import ArtinMatthews.SixthLocalHensel
public import ArtinMatthews.StandardLocalBall
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
public import Mathlib.Topology.Algebra.Ring.Compact
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Compact-open local unit and cube-unit groups, including places above six. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain SourcePhysical Topology
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "O" => P.adicCompletionIntegers K

lemma sourceKPLocalIntegers_isCompact : IsCompact (O : Set L) := by
  rw [← sourceLocalBall_zero K P]
  exact sourceLocalBall_isCompact K P 0

lemma sourceKPLocalIntegers_isOpen : IsOpen (O : Set L) := by
  rw [← sourceLocalBall_zero K P]
  exact sourceLocalBall_isOpen K P 0

def sourceKPLocalIntegerUnitMap : Oˣ →* Lˣ := Units.map (algebraMap O L).toMonoidHom

lemma sourceKPLocalIntegerUnitMap_continuous : Continuous (sourceKPLocalIntegerUnitMap K P) :=
  (continuous_subtype_val : Continuous (fun a : O => (a : L))).units_map _

lemma sourceKPLocalIntegerUnitMap_range :
    Set.range (sourceKPLocalIntegerUnitMap K P) = ((O).units : Set Lˣ) := by
  ext u
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w.val.property, w.inv.property⟩
  · intro hu
    let w : Oˣ :=
      { val := ⟨u.val, hu.1⟩
        inv := ⟨u.inv, hu.2⟩
        val_inv := Subtype.ext u.val_inv
        inv_val := Subtype.ext u.inv_val }
    exact ⟨w, Units.ext rfl⟩

lemma sourceKPLocalIntegerUnitMap_isOpenEmbedding :
    IsOpenEmbedding (sourceKPLocalIntegerUnitMap K P) := by
  have hi : IsClosedEmbedding (fun a : O => (a : L)) :=
    (sourceKPLocalIntegers_isCompact K P).isClosed.isClosedEmbedding_subtypeVal
  refine ⟨?_, ?_⟩
  · exact (hi.units_map (f := (algebraMap O L).toMonoidHom)).isEmbedding
  · rw [sourceKPLocalIntegerUnitMap_range]
    exact Submonoid.isOpen_units (sourceKPLocalIntegers_isOpen K P)

def sourceKPLocalIntegerCubeUnits : Subgroup Oˣ := (powMonoidHom (3 : ℕ)).range

def sourceKPLocalCubeUnits : Subgroup Lˣ :=
  (sourceKPLocalIntegerCubeUnits K P).map (sourceKPLocalIntegerUnitMap K P)

lemma sourceKPLocalIntegerCubeUnits_isOpen : IsOpen (sourceKPLocalIntegerCubeUnits K P : Set Oˣ) := by
  let : CompactSpace O := isCompact_iff_compactSpace.mp (sourceKPLocalIntegers_isCompact K P)
  let N : Set Oˣ := {u | (u : O) - 1 ∈ IsLocalRing.maximalIdeal O ^ sixthLocalHenselDepth P}
  have hN : IsOpen N :=
    (IsLocalRing.isOpen_maximalIdeal_pow O (sixthLocalHenselDepth P)).preimage
      (Units.continuous_val.sub continuous_const)
  have h1 : (1 : Oˣ) ∈ N := by simp [N]
  have hsub : N ⊆ (sourceKPLocalIntegerCubeUnits K P : Set Oˣ) := by
    intro u hu
    obtain ⟨w, hw⟩ := sixthLocal_exists_root P u hu
    refine ⟨w^2, ?_⟩
    change (w^2)^3 = u
    rw [← pow_mul]
    exact hw
  apply (sourceKPLocalIntegerCubeUnits K P).isOpen_of_mem_nhds (g := 1)
  exact Filter.mem_of_superset (hN.mem_nhds h1) hsub

lemma sourceKPLocalIntegerCubeUnits_isCompact : IsCompact (sourceKPLocalIntegerCubeUnits K P : Set Oˣ) := by
  let : CompactSpace O := isCompact_iff_compactSpace.mp (sourceKPLocalIntegers_isCompact K P)
  change IsCompact (Set.range (fun u : Oˣ => u^3))
  exact isCompact_range (continuous_pow 3)

lemma sourceKPLocalCubeUnits_isOpen : IsOpen (sourceKPLocalCubeUnits K P : Set Lˣ) := by
  rw [sourceKPLocalCubeUnits, Subgroup.coe_map]
  exact (sourceKPLocalIntegerUnitMap_isOpenEmbedding K P).isOpenMap _
    (sourceKPLocalIntegerCubeUnits_isOpen K P)

lemma sourceKPLocalCubeUnits_isCompact : IsCompact (sourceKPLocalCubeUnits K P : Set Lˣ) := by
  rw [sourceKPLocalCubeUnits, Subgroup.coe_map]
  exact (sourceKPLocalIntegerCubeUnits_isCompact K P).image
    (sourceKPLocalIntegerUnitMap_continuous K P)

lemma sourceKPLocalUnits_isOpen : IsOpen ((O).units : Set Lˣ) :=
  Submonoid.isOpen_units (sourceKPLocalIntegers_isOpen K P)

lemma sourceKPLocalUnits_isCompact : IsCompact ((O).units : Set Lˣ) :=
  Submonoid.units_isCompact (sourceKPLocalIntegers_isCompact K P)

lemma sourceKPLocalCubeUnits_mem_iff (u : Lˣ) :
    u ∈ sourceKPLocalCubeUnits K P ↔
      sourceKPFiniteVal K P (u : L) = 1 ∧ ∃ a : Lˣ, a^3 = u := by
  constructor
  · rintro ⟨v, ⟨w, rfl⟩, rfl⟩
    refine ⟨?_, sourceKPLocalIntegerUnitMap K P w, (map_pow _ _ _).symm⟩
    apply (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one (K := K) (v := P)).mp
    exact (Set.ext_iff.mp (sourceKPLocalIntegerUnitMap_range K P) _).mp ⟨w^3, rfl⟩
  · rintro ⟨hu, a, ha⟩
    have hun : ‖(u : L)‖ = 1 := Valued.toNormedField.norm_eq_one_iff.mpr hu
    have han : ‖(a : L)‖ = 1 := by
      apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (3 : ℕ) ≠ 0)).mp
      rw [← norm_pow, ← Units.val_pow_eq_pow_val, ha, hun]
    have hav : sourceKPFiniteVal K P (a : L) = 1 := Valued.toNormedField.norm_eq_one_iff.mp han
    have hamem : a ∈ (O).units := (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one (K := K) (v := P)).mpr hav
    have hrange : a ∈ Set.range (sourceKPLocalIntegerUnitMap K P) :=
      (Set.ext_iff.mp (sourceKPLocalIntegerUnitMap_range K P) a).mpr hamem
    obtain ⟨w, hw⟩ := hrange
    refine ⟨w^3, ⟨w, rfl⟩, ?_⟩
    rw [map_pow, hw, ha]

end
end ArtinMatthews
