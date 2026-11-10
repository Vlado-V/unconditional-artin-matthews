module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! # Nat Volume -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.NatVolume.CM

noncomputable section

/-! Exact volumes of the actual normalized integral finite lattices,
without a Weil-data input. -/

open scoped Classical ENNReal
open _root_.MeasureTheory OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure.CM
variable (I : Type*) [Fintype I]

theorem finiteLattice_nat_volume (n : ℕ) (hn : 0 < n) :
    (Constructed.FiniteMeasure.CM.measure I).real (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := I) (n : ℚ) (by exact_mod_cast hn.ne') : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) =
      ((n : ℝ) ^ Fintype.card I)⁻¹ := by
  let : NeZero n := ⟨hn.ne'⟩
  let L := RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := I) (n : ℚ) (by exact_mod_cast hn.ne')
  have hcoset (r : I → ZMod n) : (Constructed.FiniteMeasure.CM.measure I) {x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf | x - RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.residuePoint r ∈ L} =
      (Constructed.FiniteMeasure.CM.measure I) (L : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) := by
    simpa only [sub_eq_add_neg, Set.preimage, SetLike.mem_coe] using
      measure_preimage_add_right (Constructed.FiniteMeasure.CM.measure I) (-RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.residuePoint r) (L : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf))
  have hmeasure : (Constructed.FiniteMeasure.CM.measure I) (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors (ι := I) : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) =
      (n : ℝ≥0∞) ^ Fintype.card I * (Constructed.FiniteMeasure.CM.measure I) (L : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) := by
    rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors_residue_partition n hn]
    rw [measure_iUnion (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.residue_cosets_disjoint n hn)
      (fun r => (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_measurableSet (n : ℚ) (by exact_mod_cast hn.ne')).preimage
        (measurable_id.sub measurable_const))]
    change (∑' r : I → ZMod n, (Constructed.FiniteMeasure.CM.measure I) {x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf | x - RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.residuePoint r ∈ L}) = _
    simp only [hcoset, tsum_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, ZMod.card, nsmul_eq_mul, Nat.cast_pow]
  have hreal := congrArg ENNReal.toReal hmeasure
  change (Constructed.FiniteMeasure.CM.measure I).real (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors (ι := I) : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) = _ at hreal
  rw [Constructed.FiniteMeasure.CM.integral_real_volume I] at hreal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast] at hreal
  have hnreal : (n : ℝ) ^ Fintype.card I ≠ 0 := pow_ne_zero _ (by exact_mod_cast hn.ne')
  apply (mul_left_cancel₀ hnreal)
  rw [mul_inv_cancel₀ hnreal]
  exact hreal.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.NatVolume.CM
