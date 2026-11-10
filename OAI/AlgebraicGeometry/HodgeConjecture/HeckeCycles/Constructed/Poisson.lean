module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Fourier
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
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.CosetPoisson
public import OAI.RepresentationTheory.Theta.Convergence


set_option backward.privateInPublic true
@[expose] public section

/-! # Poisson -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Poisson.CM

noncomputable section

/-! Actual adelic Poisson summation and Fourier invariance of the
rational theta functional, without a rational split or Weil-data input. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Fourier.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure.CM
variable (N : ℕ)

theorem theta_fourier_coset (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin N)) (n : ℕ) (hn : 0 < n) (a : Fin N → ℚ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaFunctional (Adelic.Fourier.CM.fourierEquiv N
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest (n : ℚ) (by exact_mod_cast hn.ne') (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal a)))) =
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaFunctional (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest (n : ℚ) (by exact_mod_cast hn.ne') (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal a))) := by
  let φ := RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest (n : ℚ) (by exact_mod_cast hn.ne') (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal a)
  obtain ⟨F, hF⟩ := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.realSchwartz_mem_iff f.val).mp f.property
  calc
    _ = ∑' x : Fin N → ℚ, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter MeasureTheory.volume f.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.rationalReal x) *
        RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier AdelicCharacter.CM.Finite.character (FiniteMeasure.CM.measure (Fin N)) φ.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x) := by
      apply tsum_congr
      intro x
      exact (Adelic.Fourier.CM.fourierEquiv_apply N (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal x)).trans
        (Adelic.Fourier.CM.adelic_fourier_tensor_function f.val φ.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal x))
    _ = _ := by
      change (∑' x : Fin N → ℚ, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter MeasureTheory.volume f.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.rationalReal x) *
        RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier AdelicCharacter.CM.Finite.character (FiniteMeasure.CM.measure (Fin N))
          (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator (n : ℚ) (by exact_mod_cast hn.ne') (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal a)) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x)) =
        ∑' x : Fin N → ℚ, f.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.rationalReal x) *
          RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator (n : ℚ) (by exact_mod_cast hn.ne') (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal a) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x)
      rw [hF]
      exact (CosetPoisson.CM.coset_poisson_summation n hn a F).symm

theorem theta_fourier_tensor (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin N)) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin N)) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaFunctional (Adelic.Fourier.CM.fourierEquiv N (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ)) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaFunctional (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) := by
  let A : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin N) →ₗ[ℂ] ℂ :=
    (RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional.comp (Adelic.Fourier.CM.fourierEquiv N).toLinearMap).comp (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.tensorLeft f)
  let B : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin N) →ₗ[ℂ] ℂ := RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional.comp (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.tensorLeft f)
  change A φ = B φ
  obtain ⟨n, hn, s, hφ⟩ := RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.finiteSchwartz_coset_expansion_eq φ
  rw [hφ]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  exact theta_fourier_coset N f n hn (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteQuotientRep (n : ℚ) (by exact_mod_cast hn.ne') c)

theorem theta_fourier_invariant (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin N)) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaFunctional (Adelic.Fourier.CM.fourierEquiv N f) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaFunctional f := by
  let A : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin N) →ₗ[ℂ] ℂ :=
    RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional.comp (Adelic.Fourier.CM.fourierEquiv N).toLinearMap
  let B : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin N) →ₗ[ℂ] ℂ := RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional
  change A f = B f
  rcases f with ⟨f, hf⟩
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨g, φ, rfl⟩ := hf
      exact theta_fourier_tensor N g φ
  | zero =>
      change A 0 = B 0
      rw [map_zero, map_zero]
  | add f g hf hg ihf ihg =>
      change A (⟨f, hf⟩ + ⟨g, hg⟩) = B (⟨f, hf⟩ + ⟨g, hg⟩)
      rw [map_add, map_add, ihf, ihg]
  | smul c f hf ih =>
      change A (c • ⟨f, hf⟩) = B (c • ⟨f, hf⟩)
      rw [map_smul, map_smul, ih]

theorem adelic_poisson_summation (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin N)) :
    (∑' x : Fin N → ℚ, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier AdelicCharacter.CM.character (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure (FiniteMeasure.CM.measure (Fin N))) f.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal x)) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaFunctional f := by
  calc
    _ = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaFunctional (Adelic.Fourier.CM.fourierEquiv N f) := by
      apply tsum_congr
      intro x
      exact (Adelic.Fourier.CM.fourierEquiv_apply N f (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal x)).symm
    _ = _ := theta_fourier_invariant N f

theorem theta_inverse_fourier (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin N)) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaFunctional ((Adelic.Fourier.CM.fourierEquiv N).symm f) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaFunctional f := by
  have h := theta_fourier_invariant N ((Adelic.Fourier.CM.fourierEquiv N).symm f)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Poisson.CM
