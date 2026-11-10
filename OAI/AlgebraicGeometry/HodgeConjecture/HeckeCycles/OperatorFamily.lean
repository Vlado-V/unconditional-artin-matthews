module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.CommutingProduct
public import OAI.RepresentationTheory.Hecke.RadialDilation.PositionReindex
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Schrodinger
public import OAI.RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators
public import OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticSwap
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
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeIntertwiner


set_option backward.privateInPublic true
@[expose] public section

/-! # Operator Family -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.OperatorFamily.CM.LocalFamily

noncomputable section

/-! Families of actual p-adic bare operators indexed by finite places,
with their finite products acting on the actual adelic test space. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization

def number (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : ℕ := (Rat.HeightOneSpectrum.primesEquiv (R := ℤ) v).val

instance number_prime (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : Fact (number v).Prime :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv (R := ℤ) v).property⟩

theorem rationalPrime_number (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime (number v) = v :=
  (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm_apply_apply v

theorem number_injective : Function.Injective number := by
  intro v w h
  have he := congrArg (fun p : {p : ℕ // p.Prime} =>
    (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p)
    (Subtype.ext h : Rat.HeightOneSpectrum.primesEquiv (R := ℤ) v =
      Rat.HeightOneSpectrum.primesEquiv (R := ℤ) w)
  simpa only [Equiv.symm_apply_apply] using he

local instance (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : MeasurableSpace ℚ_[number v] := borel ℚ_[number v]
local instance (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : BorelSpace ℚ_[number v] := ⟨rfl⟩

variable (n : ℕ)
abbrev Local (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) := Local.Schrodinger.CM.LocalMetaplectic (number v) n
abbrev Family := ∀ v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace, Local n v

def operator (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : Local n v →* (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n)) :=
  (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom (number v) n).comp
    (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[number v] n (PadicCharacter.CM.character (number v)))

theorem operators_commute : Pairwise fun v w => ∀ a b, Commute (operator n v a) (operator n w b) := by
  intro v w hvw a b
  exact PrimeIntertwiner.CM.OperatorCommutation.bare_operators_commute (number v) (number w) n
    (fun h => hvw (number_injective h.symm)) a b

def product (S : Finset RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : Family n →*
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n)) :=
  Finite.CommutingProduct.CM.product (operator n) (operators_commute n) S

def localProjection (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : Local n v →* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ_[number v] :=
  RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[number v] n (PadicCharacter.CM.character (number v))

def globalProjection (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : Finite.FiniteOscillator.CM.Oscillator (I := Fin n) →*
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ_[number v] :=
  RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom.comp ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection (number v)).toRingHom).comp
    ((@RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf _ _ (Classical.decEq _) inferInstance _
      (Equiv.refl (Fin n))).comp Finite.FiniteOscillator.CM.projection))

def realized : Subgroup (Finite.FiniteOscillator.CM.Oscillator (I := Fin n)) :=
  Finite.CommutingProduct.CM.realized (product n) Finite.FiniteOscillator.CM.action
    (localProjection n) (globalProjection n)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.OperatorFamily.CM.LocalFamily
