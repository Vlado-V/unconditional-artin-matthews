module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteHeisenberg
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.PhaseAction


set_option backward.privateInPublic true
@[expose] public section

/-! # Coset Phase -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.CosetPhase.CM

noncomputable section

/-! A neighborhood condition for an arbitrary translate of a lattice
test. The translating vector need not be integral. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.PhaseAction.TestTransport

variable {I : Type*} [Fintype I] [DecidableEq I]
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA)

theorem translate (r : ℚ) (hr : r ≠ 0) (p q a : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    (hp : p ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice r⁻¹ (inv_ne_zero hr))
    (hqa : q - a ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice r hr)
    (hphase : (∑ i, p i * (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (1 / 2) q) i) ∈ RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele)
    (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter p q (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction r hr).val x =
      (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest r hr a).val x := by
  have hshift : (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction r hr).val (x - q) =
      (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction r hr).val (x - a) := by
    convert RepresentationTheory.Hecke.RadialDilation.FiniteHeisenberg.Realization.latticeTestFunction_translation r hr (q - a) hqa (x - a) using 1
    abel_nf
  change D.finiteCharacter _ * (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction r hr).val (x - q) =
    (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction r hr).val (x - a)
  rw [← hshift]
  by_cases hx : x - q ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice r hr
  · have he : (∑ i, p i * (x i - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * q i)) =
        (∑ i, p i * (x - q) i) + ∑ i, p i * (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (1 / 2) q) i := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale, Pi.sub_apply]
      have hh : (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2)) + algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) = 1 := by
        rw [← map_add]
        norm_num
      linear_combination -(p i * q i) * hh
    rw [he, D.finiteCharacter.map_add_eq_mul,
      (RepresentationTheory.Hecke.RadialDilation.FiniteHeisenberg.Realization.finite_lattice_annihilator D r hr (x - q)).mp hx p hp,
      RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteCharacter_integral D _ hphase, one_mul, one_mul]
  · change _ * RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator r hr (x - q) = RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator r hr (x - q)
    rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator_of_notMem r hr hx, mul_zero]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.CosetPhase.CM
