module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Theta.Generators
public import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init
public import OAI.RepresentationTheory.Theta.AdelicTopology


set_option backward.privateInPublic true
@[expose] public section

/-! # Real Generators -/

namespace OAI.RepresentationTheory.Theta.RealGenerators.PoissonAutomorphyConstruction

noncomputable section

/-! Real generator normalization extracted from the supplied rational action. -/

open scoped Classical
open _root_.MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)

theorem vacuum_zero : D.vacuum.val 0 = 1 := by
  rw [D.vacuum_eq]
  simp

theorem scalar_standard_gaussian_integral :
    (∫ t : ℝ, Complex.exp (-((Real.pi : ℂ) * (t : ℂ) ^ 2))) = 1 := by
  have h := integral_gaussian_complex (b := (Real.pi : ℂ)) (by simpa using Real.pi_pos)
  simpa only [neg_mul, div_self (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero), Complex.one_cpow] using h

theorem vacuum_integral : (∫ x : ι → ℝ, D.vacuum.val x) = 1 := by
  have heq : D.vacuum.val = fun x : ι → ℝ =>
      ∏ i, Complex.exp (-((Real.pi : ℂ) * (x i : ℂ) ^ 2)) := by
    funext x
    rw [D.vacuum_eq, ← Complex.exp_sum]
    congr 1
    simp only [Finset.sum_neg_distrib, Finset.mul_sum]
  rw [heq]
  calc
    _ = ∏ _i : ι, ∫ t : ℝ, Complex.exp (-((Real.pi : ℂ) * (t : ℂ) ^ 2)) := by
      convert! integral_fintype_prod_volume_eq_prod
        (fun _i : ι => fun t : ℝ => Complex.exp (-((Real.pi : ℂ) * (t : ℂ) ^ 2)))
        using 1
    _ = _ := by simp only [scalar_standard_gaussian_integral, Finset.prod_const_one]

theorem vacuum_fourier_zero : PoissonAutomorphyNormalizationData.fourier PoissonAutomorphyNormalizationData.standardRealCharacter volume D.vacuum.val 0 = 1 := by
  simp only [PoissonAutomorphyNormalizationData.fourier, Pi.zero_apply, zero_mul, Finset.sum_const_zero, neg_zero,
    AddChar.map_zero_eq_one, mul_one]
  exact vacuum_integral D

def adelicAtReal (x : ι → ℝ) : ι → PoissonAutomorphyNormalizationData.AQ := fun i => (x i, 0)

theorem realAction_formula_from_vacuum (γ : PoissonAutomorphyNormalizationData.Sp ι ℚ) (T : PoissonAutomorphyNormalizationData.realSchwartz ι → (ι → ℝ) → ℂ)
    (hT : ∀ f x, (D.rationalAction γ (PoissonAutomorphyNormalizationData.tensor f PoissonAutomorphyFiniteFourier.Construction.integralTestFunction)).val (adelicAtReal x) = T f x)
    (hTv : T D.vacuum 0 = 1) (f : PoissonAutomorphyNormalizationData.realSchwartz ι) (x : ι → ℝ) :
    (D.real.action (D.normalizedRealLift γ) f).val x =
      (PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks γ) (PoissonAutomorphyNormalizationData.toSiegel (PoissonAutomorphyNormalizationData.basePeriod ι)))⁻¹ * T f x := by
  let b := (D.finiteAction γ PoissonAutomorphyFiniteFourier.Construction.integralTestFunction).val 0
  let c := (D.real.action (D.normalizedRealLift γ) D.vacuum).val 0
  have heq (g : PoissonAutomorphyNormalizationData.realSchwartz ι) (y : ι → ℝ) :
      (D.real.action (D.normalizedRealLift γ) g).val y * b = T g y := by
    have h := congrArg (fun F : PoissonAutomorphyNormalizationData.adelicSchwartz ι => F.val (adelicAtReal y))
      (D.rationalAction_tensor γ g PoissonAutomorphyFiniteFourier.Construction.integralTestFunction)
    exact h.symm.trans (hT g y)
  have hcb : c * b = 1 := (heq D.vacuum 0).trans hTv
  calc
    _ = c * ((D.real.action (D.normalizedRealLift γ) f).val x * b) := by
      rw [mul_left_comm, hcb, mul_one]
    _ = c * T f x := by rw [heq]
    _ = _ := by rw [show c = _ from D.normalizedRealLift_coefficient γ]

theorem realAction_weyl (f : PoissonAutomorphyNormalizationData.realSchwartz ι) (x : ι → ℝ) :
    (D.real.action (D.normalizedRealLift (Generators.PoissonAutomorphyConstruction.weyl ι)) f).val x =
      (PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)) (PoissonAutomorphyNormalizationData.toSiegel (PoissonAutomorphyNormalizationData.basePeriod ι)))⁻¹ *
        PoissonAutomorphyNormalizationData.fourier PoissonAutomorphyNormalizationData.standardRealCharacter volume f.val x := by
  apply realAction_formula_from_vacuum D (Generators.PoissonAutomorphyConstruction.weyl ι)
    (fun f x => PoissonAutomorphyNormalizationData.fourier PoissonAutomorphyNormalizationData.standardRealCharacter volume f.val x) ?_ (vacuum_fourier_zero D)
  intro g y
  calc
    _ = PoissonAutomorphyNormalizationData.fourier D.character (PoissonAutomorphyNormalizationData.adelicMeasure D.finiteMeasure)
        (PoissonAutomorphyNormalizationData.pureTensor g PoissonAutomorphyFiniteFourier.Construction.integralTestFunction) (adelicAtReal y) :=
      D.rational_fourier (Generators.PoissonAutomorphyConstruction.weyl ι) rfl (PoissonAutomorphyNormalizationData.tensor g PoissonAutomorphyFiniteFourier.Construction.integralTestFunction) (adelicAtReal y)
    _ = _ := by
      rw [AdelicTopology.PoissonAutomorphyConstruction.adelic_fourier_pureTensor]
      change PoissonAutomorphyNormalizationData.fourier PoissonAutomorphyNormalizationData.standardRealCharacter volume g.val y *
        PoissonAutomorphyNormalizationData.fourier D.finiteCharacter D.finiteMeasure PoissonAutomorphyFiniteFourier.Construction.integralIndicator 0 = _
      rw [PoissonAutomorphyFiniteFourier.Construction.integralIndicator_selfFourier D, PoissonAutomorphyFiniteFourier.Construction.integralIndicator_of_mem PoissonAutomorphyFiniteFourier.Construction.integralVectors.zero_mem, mul_one]

end

end OAI.RepresentationTheory.Theta.RealGenerators.PoissonAutomorphyConstruction
