module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanPositionPairing
public import OAI.RepresentationTheory.Weil.AdelicSplitting.LatticePoisson
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
public import OAI.RepresentationTheory.Weil.AdelicSplitting.RationalLevi


set_option backward.privateInPublic true
@[expose] public section

/-! # Archimedean Position Fourier -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanPositionFourier.Construction

noncomputable section

/-! The actual archimedean Fourier product, transported by the additive
Minkowski chart, is a real bilinear Fourier transform for a Haar measure. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.MeasureTheory

open OAI.RepresentationTheory.Weil.AdelicSplitting.LatticePoisson.LocalAnalysis

local instance archFourierMeasurableSpace (F : Type) [Field F]
    (v : InfinitePlace F) : MeasurableSpace v.Completion := borel v.Completion

local instance archFourierBorelSpace (F : Type) [Field F]
    (v : InfinitePlace F) : BorelSpace v.Completion := ⟨rfl⟩

local instance archFourierSecondCountable (F : Type) [Field F] [NumberField F]
    (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
  RationalLevi.Construction.completionSecondCountableTopology F (.inl v)

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
variable (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)

def archimedeanPositionMeasure : Measure (Fin N → mixedEmbedding.mixedSpace F) :=
  (Measure.pi (fun v : InfinitePlace F =>
    Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inl v)) N (Characters.Construction.localAdditiveCharacter F ψ (.inl v)))).map
      (ArchimedeanPositionPairing.Construction.archimedeanPositionAddChart F N)

variable (hμ : ∀ v : InfinitePlace F,
  (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inl v)) N (Characters.Construction.localAdditiveCharacter F ψ (.inl v))).IsAddHaarMeasure)

include hμ in
theorem archimedeanPositionMeasure_isAddHaarMeasure :
    (archimedeanPositionMeasure F N ψ).IsAddHaarMeasure := by
  let : ∀ v : InfinitePlace F,
      (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inl v)) N (Characters.Construction.localAdditiveCharacter F ψ (.inl v))).IsAddHaarMeasure := hμ
  exact (ArchimedeanPositionPairing.Construction.archimedeanPositionAddChart F N).isAddHaarMeasure_map _

include hμ in
theorem archimedean_fourier_product (hc : Continuous ψ)
    (L : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hL : ∀ x, ArchimedeanCharacterLattice.Construction.archimedeanCharacter F ψ x = RealCharacters.LocalAnalysis.realCharacter 1 (L x))
    (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalFourier F N ψ a)
    (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (ξ : Fin N → mixedEmbedding.mixedSpace F) :
    (f.act F N ψ a).mixedProductRapid F N ξ =
      LatticePoisson.LocalAnalysis.realBilinearFourier (ArchimedeanPositionPairing.Construction.mixedPositionPairing F N L) (archimedeanPositionMeasure F N ψ)
        (f.mixedProductRapid F N) ξ := by
  let μ (v : InfinitePlace F) :=
    Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inl v)) N (Characters.Construction.localAdditiveCharacter F ψ (.inl v))
  let : ∀ v, (μ v).IsAddHaarMeasure := hμ
  let e := ArchimedeanPositionPairing.Construction.archimedeanPositionAddChart F N
  let η := e.symm ξ
  have he (y : ∀ v : InfinitePlace F, Local.FunctionsMetaplectic.Construction.Position v.Completion N) :
      (f.mixedProductRapid F N) (e y) = ∏ v : InfinitePlace F, (f (.inl v)).val (y v) := by
    change (f.archimedeanProductRapid F N) ((ArchimedeanPositionChart.Construction.archimedeanPositionChart F N).symm
      (ArchimedeanPositionChart.Construction.archimedeanPositionChart F N y)) = _
    rw [(ArchimedeanPositionChart.Construction.archimedeanPositionChart F N).symm_apply_apply]
    rfl
  have hphase (y : ∀ v : InfinitePlace F, Local.FunctionsMetaplectic.Construction.Position v.Completion N) :
      RealCharacters.LocalAnalysis.realCharacter 1 (-(ArchimedeanPositionPairing.Construction.mixedPositionPairing F N L ξ (e y))) =
        ∏ v : InfinitePlace F, Characters.Construction.localAdditiveCharacter F ψ (.inl v) (-Local.FunctionsMetaplectic.Construction.dot (η v) (y v)) := by
    rw [ArchimedeanPositionPairing.Construction.mixedPositionPairing_apply, ← map_neg L, ← hL]
    have hξ : ξ = ArchimedeanPositionChart.Construction.archimedeanPositionChart F N η := (e.apply_symm_apply ξ).symm
    rw [hξ]
    exact ArchimedeanPositionPairing.Construction.archimedeanPosition_dot_phase F N ψ hc η y
  have hint := e.toHomeomorph.isClosedEmbedding.integral_map (μ := Measure.pi μ)
    (fun y => (f.mixedProductRapid F N) y *
      RealCharacters.LocalAnalysis.realCharacter 1 (-(ArchimedeanPositionPairing.Construction.mixedPositionPairing F N L ξ y)))
  have ecoe : (e.toHomeomorph : (∀ v : InfinitePlace F, Local.FunctionsMetaplectic.Construction.Position v.Completion N) →
      (Fin N → mixedEmbedding.mixedSpace F)) = e := rfl
  rw [ecoe] at hint
  change _ = ∫ y, (f.mixedProductRapid F N) y *
    RealCharacters.LocalAnalysis.realCharacter 1 (-(ArchimedeanPositionPairing.Construction.mixedPositionPairing F N L ξ y)) ∂((Measure.pi μ).map e)
  rw [hint]
  simp_rw [he, hphase, ← Finset.prod_mul_distrib]
  refine Eq.trans ?_ (integral_fintype_prod_eq_prod (μ := μ)
    (fun (v : InfinitePlace F) (x : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inl v)) N) =>
      (f (.inl v)).val x * Characters.Construction.localAdditiveCharacter F ψ (.inl v) (-Local.FunctionsMetaplectic.Construction.dot (η v) x))).symm
  change (∏ v : InfinitePlace F, ((f.act F N ψ a) (.inl v)).val (η v)) = _
  apply Finset.prod_congr rfl
  intro v _
  exact ha.2 (.inl v) (f (.inl v)) (η v)

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanPositionFourier.Construction
