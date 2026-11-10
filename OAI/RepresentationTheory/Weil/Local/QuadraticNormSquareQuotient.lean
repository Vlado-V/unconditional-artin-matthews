module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.QuadraticHilbert
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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


set_option backward.privateInPublic true
@[expose] public section

/-! # Quadratic Norm Square Quotient -/

namespace OAI.RepresentationTheory.Weil.Local.QuadraticNormSquareQuotient.Construction

noncomputable section

/-! Identifying quadratic norms modulo field squares with norm-one elements modulo squares. -/

variable {k : Type*} [Field k] [CharZero k]

theorem quadraticHilbert90_mem_squares_iff (z : (QuadraticNormUnits.Construction.QuadraticNormAlgebra k)ˣ) :
    QuadraticHilbert.Construction.quadraticHilbert90 z ∈ QuadraticNormSubgroup.Construction.squareUnitsSubgroup (QuadraticNormAt.Construction.QuadraticNormOne k) ↔
      QuadraticNormUnits.Construction.quadraticNormUnits z ∈ QuadraticNormSubgroup.Construction.squareUnitsSubgroup kˣ := by
  constructor
  · rintro ⟨p, hp⟩
    change p ^ 2 = QuadraticHilbert.Construction.quadraticHilbert90 z at hp
    have hk : QuadraticHilbert.Construction.quadraticHilbert90 (z / QuadraticNormUnits.Construction.quadraticNormOneUnits p) = 1 := by
      rw [map_div, QuadraticHilbert.Construction.quadraticHilbert90_normOne]
      rw [← hp, div_self']
    obtain ⟨a, ha⟩ := (QuadraticHilbert.Construction.quadraticHilbert90_kernel _).mp hk
    have hn := congrArg QuadraticNormUnits.Construction.quadraticNormUnits ha
    rw [QuadraticNormUnits.Construction.quadraticNormUnits_scalar, map_div, QuadraticNormUnits.Construction.quadraticNormOneUnits_norm, div_one] at hn
    exact ⟨a, hn⟩
  · rintro ⟨a, ha⟩
    change a ^ 2 = QuadraticNormUnits.Construction.quadraticNormUnits z at ha
    let w := z / QuadraticNormUnits.Construction.quadraticScalarUnits a
    have hw : QuadraticNormUnits.Construction.quadraticNormUnits w = 1 := by
      change QuadraticNormUnits.Construction.quadraticNormUnits (z / QuadraticNormUnits.Construction.quadraticScalarUnits a) = 1
      rw [map_div, QuadraticNormUnits.Construction.quadraticNormUnits_scalar]
      rw [← ha, div_self']
    let p := QuadraticNormUnits.Construction.quadraticNormOneOfUnit w hw
    have he : QuadraticNormUnits.Construction.quadraticNormOneUnits p = w := QuadraticNormUnits.Construction.quadraticNormOneUnits_ofUnit w hw
    have hd : QuadraticHilbert.Construction.quadraticHilbert90 w = QuadraticHilbert.Construction.quadraticHilbert90 z := by
      change QuadraticHilbert.Construction.quadraticHilbert90 (z / QuadraticNormUnits.Construction.quadraticScalarUnits a) = QuadraticHilbert.Construction.quadraticHilbert90 z
      rw [map_div, QuadraticHilbert.Construction.quadraticHilbert90_scalar, div_one]
    refine ⟨p, ?_⟩
    change p ^ 2 = QuadraticHilbert.Construction.quadraticHilbert90 z
    rw [← QuadraticHilbert.Construction.quadraticHilbert90_normOne, he, hd]

theorem quadraticNorm_square_comap_eq :
    (QuadraticNormSubgroup.Construction.squareUnitsSubgroup kˣ).comap QuadraticNormUnits.Construction.quadraticNormUnits =
      (QuadraticNormSubgroup.Construction.squareUnitsSubgroup (QuadraticNormAt.Construction.QuadraticNormOne k)).comap QuadraticHilbert.Construction.quadraticHilbert90 := by
  ext z
  exact (quadraticHilbert90_mem_squares_iff z).symm

theorem quadraticNorm_square_relIndex :
    (QuadraticNormSubgroup.Construction.squareUnitsSubgroup kˣ).relIndex (QuadraticNormSubgroup.Construction.quadraticNormSubgroup k) =
      (QuadraticNormSubgroup.Construction.squareUnitsSubgroup (QuadraticNormAt.Construction.QuadraticNormOne k)).index := by
  calc
    (QuadraticNormSubgroup.Construction.squareUnitsSubgroup kˣ).relIndex (QuadraticNormSubgroup.Construction.quadraticNormSubgroup k) =
        ((QuadraticNormSubgroup.Construction.squareUnitsSubgroup kˣ).comap QuadraticNormUnits.Construction.quadraticNormUnits).index := by
      rw [Subgroup.index_comap, QuadraticNormUnits.Construction.quadraticNormUnits_range]
    _ = ((QuadraticNormSubgroup.Construction.squareUnitsSubgroup (QuadraticNormAt.Construction.QuadraticNormOne k)).comap QuadraticHilbert.Construction.quadraticHilbert90).index := by
      rw [quadraticNorm_square_comap_eq]
    _ = (QuadraticNormSubgroup.Construction.squareUnitsSubgroup (QuadraticNormAt.Construction.QuadraticNormOne k)).index :=
      Subgroup.index_comap_of_surjective _ QuadraticHilbert.Construction.quadraticHilbert90_surjective

end

end OAI.RepresentationTheory.Weil.Local.QuadraticNormSquareQuotient.Construction
