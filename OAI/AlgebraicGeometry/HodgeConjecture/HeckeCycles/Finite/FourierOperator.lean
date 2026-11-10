module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.AdelicCharacter
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure
public import OAI.RepresentationTheory.Theta.CosetTests
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
public import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.Topology.Sheaves.Init
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteFourier


set_option backward.privateInPublic true
@[expose] public section

/-! # Fourier Operator -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FourierOperator.CM

noncomputable section

/-! The Fourier transform for the constructed finite character and
measure is a linear operator on actual finite Schwartz functions. -/

open scoped Classical
open _root_.MeasureTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure.CM

variable {I : Type*} [Fintype I]

theorem phase_locallyConstant (a : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    IsLocallyConstant (fun x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf =>
      Constructed.AdelicCharacter.CM.Finite.character (-(∑ i, x i * a i))) := by
  have hc : Continuous (fun x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => -(∑ i, x i * a i)) :=
    (continuous_finsetSum Finset.univ (fun i _ =>
      (continuous_apply i).mul continuous_const)).neg
  exact Constructed.AdelicCharacter.CM.Finite.character_locallyConstant.comp_continuous hc

def modulation (a : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I := by
  refine ⟨fun x => Constructed.AdelicCharacter.CM.Finite.character (-(∑ i, x i * a i)) * f.val x,
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mpr ⟨?_, ?_⟩⟩
  · exact (phase_locallyConstant a).mul ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff f.val).mp f.property).1
  · exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_hasCompactSupport f).mul_left

theorem kernel_integrable (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    Integrable (fun y => f.val y *
      Constructed.AdelicCharacter.CM.Finite.character (-(∑ i, x i * y i))) (Constructed.FiniteMeasure.CM.measure I) := by
  have h := RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteSchwartz_integrable (modulation x f) (Constructed.FiniteMeasure.CM.measure I)
  convert h using 1
  funext y
  change f.val y * Constructed.AdelicCharacter.CM.Finite.character (-(∑ i, x i * y i)) =
    Constructed.AdelicCharacter.CM.Finite.character (-(∑ i, y i * x i)) * f.val y
  simp only [mul_comm]

def transform : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I →ₗ[ℂ] ((I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) → ℂ) where
  toFun f := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier Constructed.AdelicCharacter.CM.Finite.character (Constructed.FiniteMeasure.CM.measure I) f.val
  map_add' f h := by
    funext x
    change (∫ y, (f.val y + h.val y) * _ ∂(Constructed.FiniteMeasure.CM.measure I)) = _
    simp only [add_mul]
    exact integral_add (kernel_integrable f x) (kernel_integrable h x)
  map_smul' c f := by
    funext x
    change (∫ y, (c * f.val y) * _ ∂(Constructed.FiniteMeasure.CM.measure I)) = c * _
    simp only [mul_assoc, integral_const_mul]
    rfl

theorem transform_coset_mem (q : ℚ) (hq : q ≠ 0) (a : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    transform (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq a) ∈ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I := by
  have h : transform (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq a) =
      (((Constructed.FiniteMeasure.CM.measure I).real (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := I) q hq : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) : ℂ) •
        modulation a (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q⁻¹ (inv_ne_zero hq))).val := by
    funext x
    change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier Constructed.AdelicCharacter.CM.Finite.character (Constructed.FiniteMeasure.CM.measure I)
      (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator q hq a) x = _
    rw [Constructed.FiniteFourier.CM.latticeCosetIndicator_fourier]
    change _ = _ * (Constructed.AdelicCharacter.CM.Finite.character _ *
      RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q⁻¹ (inv_ne_zero hq) x)
    ring
  rw [h]
  exact Subtype.property _

theorem transform_mem (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : transform f ∈ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I := by
  obtain ⟨n, hn, s, hf⟩ := RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.finiteSchwartz_coset_expansion_eq f
  rw [hf, map_sum]
  apply (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I).sum_mem
  intro c hc
  rw [map_smul]
  exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I).smul_mem _ (transform_coset_mem _ _ _)

def fourierMap : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I :=
  transform.codRestrict (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) transform_mem

theorem fourierMap_apply (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (fourierMap f).val x =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier Constructed.AdelicCharacter.CM.Finite.character (Constructed.FiniteMeasure.CM.measure I) f.val x := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FourierOperator.CM
