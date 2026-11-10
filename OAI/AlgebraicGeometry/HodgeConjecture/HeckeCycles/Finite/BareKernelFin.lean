module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.OperatorFamily
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
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareBy
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.FamilyKernel
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.GeneratorProjection


set_option backward.privateInPublic true
@[expose] public section

/-! # Bare Kernel Fin -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareKernelFin.CM

noncomputable section

/-! Every actual finite bare operator is realized by finite products of
local bare operators. The local sign theorem therefore proves the global
bare-kernel sign theorem on a finite coordinate set. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe.CM.Group
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.OperatorFamily.CM.LocalFamily
variable (n : ℕ)

theorem bare_realized : BareNe.CM.Group.bareSubgroup (I := Fin n) ≤ OperatorFamily.CM.LocalFamily.realized n := by
  rw [BareBy.CM.Generators.bare_eq_generated, BareBy.CM.Generators.generated,
    Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | ⟨B, hB, rfl⟩ | ⟨B, hB, rfl⟩
  · let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact Local.FamilyKernel.CM.MinusFamily.minus_realized n (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime 2)
  · exact Local.GeneratorProjection.CM.upper_realized n B hB
  · exact Local.GeneratorProjection.CM.lower_realized n B hB

theorem kernel_sign (g : BareNe.CM.Group.BareGroup (I := Fin n)) (hg : BareNe.CM.Group.bareProjection g = 1) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n), BareNe.CM.Group.bareAction g f = ε • f := by
  obtain ⟨u, hu, hf⟩ := bare_realized n g.property
  have hup (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : OperatorFamily.CM.LocalFamily.localProjection n v (u v) = 1 :=
    (hu v).trans (Local.FamilyKernel.CM.MinusFamily.globalProjection_kernel n g.val hg v)
  obtain ⟨S, hS⟩ := hf RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction
  obtain ⟨ε, hε, he⟩ := Local.FamilyKernel.CM.Family.product_kernel_sign n S u (fun v _ => hup v)
  obtain ⟨c, _, hc⟩ := BareNe.CM.OscillatorKernel.kernel_scalar g.val hg
  have htest : ε • (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction (ι := Fin n)) = c • RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction :=
    (he RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction).symm.trans ((hS S (Finset.Subset.refl S)).trans (hc RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction))
  have hεc := congrArg (fun f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n) => f.val 0) htest
  change ε * RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator (0 : Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) = c * RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator (0 : Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) at hεc
  rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator_of_mem RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors.zero_mem, mul_one, mul_one] at hεc
  refine ⟨ε, hε, ?_⟩
  intro f
  exact (hc f).trans (congrArg (fun z : ℂ => z • f) hεc.symm)

theorem kernel_exact (g : BareNe.CM.Group.BareGroup (I := Fin n)) (hg : BareNe.CM.Group.bareProjection g = 1) :
    g = 1 ∨ g = BareNe.CM.Group.negOne := by
  obtain ⟨ε, hε, hf⟩ := kernel_sign n g hg
  rcases sq_eq_one_iff.mp hε with rfl | rfl
  · left
    apply BareNe.CM.Group.faithful
    change (BareNe.CM.Group.bareProjection g, BareNe.CM.Group.bareAction g) = (BareNe.CM.Group.bareProjection 1, BareNe.CM.Group.bareAction 1)
    apply Prod.ext
    · exact hg.trans BareNe.CM.Group.bareProjection.map_one.symm
    · apply LinearEquiv.ext
      intro f
      rw [map_one]
      change BareNe.CM.Group.bareAction g f = f
      exact (hf f).trans (one_smul ℂ f)
  · right
    apply BareNe.CM.Group.faithful
    apply Prod.ext
    · exact hg.trans BareNe.CM.Group.project_negOne.symm
    · apply LinearEquiv.ext
      intro f
      rw [hf, BareNe.CM.Group.genuine]
      exact neg_one_smul ℂ f

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareKernelFin.CM
