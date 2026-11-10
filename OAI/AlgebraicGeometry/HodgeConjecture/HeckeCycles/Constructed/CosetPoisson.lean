module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.AdelicCharacter
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteFourier
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.NatVolume
public import OAI.RepresentationTheory.Theta.CosetPoisson
public import OAI.RepresentationTheory.Theta.RealPoisson


set_option backward.privateInPublic true
@[expose] public section

/-! # Coset Poisson -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.CosetPoisson.CM

noncomputable section

/-! Actual adelic Poisson summation on finite-lattice coset tensors,
proved from the constructed character and normalized Haar measure. -/

open scoped Classical
open _root_.MeasureTheory OAI.RepresentationTheory.Theta.CosetPoisson.AutomorphyConstruction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure.CM
variable {I : Type*} [Fintype I]

theorem finiteCharacter_negative_rational_pairing (x a : I → ℚ) :
    AdelicCharacter.CM.Finite.character (-(∑ i, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x i * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal a i)) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (∑ i, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.rationalReal x i * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.rationalReal a i) := by
  have heq : -(∑ i, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x i * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal a i) =
      algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (-(∑ i, x i * a i)) := by
    simp only [map_neg, map_sum, map_mul, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal]
  rw [heq, AdelicCharacter.CM.Finite.character_rational]
  simp only [Rat.cast_neg, Rat.cast_sum, Rat.cast_mul, neg_neg, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.rationalReal]

theorem coset_poisson_summation (n : ℕ) (hn : 0 < n) (a : I → ℚ)
    (f : SchwartzMap (I → ℝ) ℂ) :
    (∑' x : I → ℚ, f (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.rationalReal x) *
      RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator (n : ℚ) (by exact_mod_cast hn.ne') (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal a) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x)) =
    ∑' x : I → ℚ, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter volume f (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.rationalReal x) *
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier AdelicCharacter.CM.Finite.character (FiniteMeasure.CM.measure I)
        (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator (n : ℚ) (by exact_mod_cast hn.ne') (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal a)) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x) := by
  let hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  let v : ℂ := ((n : ℝ) ^ Fintype.card I)⁻¹
  calc
    _ = ∑' m : I → ℤ, f (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.rationalReal a + (n : ℝ) • RepresentationTheory.Theta.RealFourier.PoissonAutomorphyConstruction.integerReal m) := by
      rw [RepresentationTheory.Theta.CosetPoisson.AutomorphyConstruction.rational_coset_sum]
      simp only [RepresentationTheory.Theta.CosetPoisson.AutomorphyConstruction.rationalReal_grid, Rat.cast_natCast]
    _ = v * ∑' k : I → ℤ, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter volume f
        ((n : ℝ)⁻¹ • RepresentationTheory.Theta.RealFourier.PoissonAutomorphyConstruction.integerReal k) * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter
          (∑ i, (k i : ℝ) * ((n : ℝ)⁻¹ * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.rationalReal a i)) :=
      by simpa only [v, Complex.ofReal_inv, Complex.ofReal_pow] using
        RepresentationTheory.Theta.RealPoisson.AutomorphyConstruction.real_poisson_summation_scaled (n : ℝ) (by exact_mod_cast hn) f (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.rationalReal a)
    _ = v * ∑' x : I → ℚ,
        (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter volume f (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.rationalReal x) *
          AdelicCharacter.CM.Finite.character (-(∑ i, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x i * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal a i))) *
            RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator (n : ℚ)⁻¹ (inv_ne_zero hnq) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x) := by
      congr 1
      rw [RepresentationTheory.Theta.CosetPoisson.AutomorphyConstruction.rational_lattice_sum]
      apply tsum_congr
      intro k
      rw [finiteCharacter_negative_rational_pairing]
      have hreal : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.rationalReal (RepresentationTheory.Theta.CosetPoisson.AutomorphyConstruction.rationalGrid (n : ℚ)⁻¹ 0 k) =
          (n : ℝ)⁻¹ • RepresentationTheory.Theta.RealFourier.PoissonAutomorphyConstruction.integerReal k := by
        ext i
        simp [RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.rationalReal, RepresentationTheory.Theta.CosetPoisson.AutomorphyConstruction.rationalGrid, RepresentationTheory.Theta.RealFourier.PoissonAutomorphyConstruction.integerReal]
      rw [hreal]
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.smul_apply, smul_eq_mul, RepresentationTheory.Theta.RealFourier.PoissonAutomorphyConstruction.integerReal]
      ring
    _ = _ := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro x
      rw [FiniteFourier.CM.latticeCosetIndicator_fourier, Finite.NatVolume.CM.finiteLattice_nat_volume I n hn]
      dsimp [v]
      push_cast
      ring

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.CosetPoisson.CM
