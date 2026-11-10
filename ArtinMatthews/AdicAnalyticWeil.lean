module

public import ArtinMatthews.AdicConductorBridge
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic
public import ArtinMatthews.AnalyticTameComparison
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

/-! The genuine analytic quadratic Weil factor on the actual Mathlib adic
completion, with its existing valued norm. The residue Gauss comparison
therefore uses the same local analytic object as the adelic product. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField ArtinMatthews.QuadraticGauss
open OAI.RepresentationTheory.Weil.Local
open scoped NumberField ValuativeRel Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local instance adicAnalyticMeasurable : MeasurableSpace (v.adicCompletion F) := borel (v.adicCompletion F)
local instance adicAnalyticBorel : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

theorem adic_normalizedAnalyticWeil_eq_tame (ψ : AddChar (v.adicCompletion F) ℂ)
    (hψ : adicConductorZero F v ψ) (hu : ∀ x, ‖ψ x‖ = 1) (hc : Continuous ψ)
    (h2 : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) 2 = 1)
    (x : (v.adicCompletion F)ˣ) :
    letI : ValuativeRel (v.adicCompletion F) := adicRelation F v
    letI : IsNonarchimedeanLocalField (v.adicCompletion F) := adicLocalField F v
    FunctionsMetaplectic.Construction.gaussianIndex (v.adicCompletion F) ψ (2 * (x : v.adicCompletion F)) /
        FunctionsMetaplectic.Construction.gaussianIndex (v.adicCompletion F) ψ 2 =
      localTameGaussSection (v.adicCompletion F)
        (conductorResidueChar (v.adicCompletion F) ψ hψ) x := by
  let C := v.adicCompletion F
  let : CharZero C := charZero_of_injective_ringHom (algebraMap F C).injective
  let ν : Valuation C (WithZero (Multiplicative ℤ)) := Valued.v
  let : NontriviallyNormedField C := Valued.toNontriviallyNormedField C (WithZero (Multiplicative ℤ))
  let : ValuativeRel C := adicRelation F v
  let : IsNonarchimedeanLocalField C := adicLocalField F v
  let : ν.Compatible := Valuation.Compatible.ofValuation ν
  have hi : ∀ x : C, x ∈ (ValuativeRel.valuation C).integer ↔ ‖x‖ ≤ 1 := by
    intro x
    rw [adic_mem_integer_iff F v]
    change ν x ≤ 1 ↔ ‖x‖ ≤ 1
    exact (Valued.toNormedField.norm_le_one_iff).symm
  have htwo : ValuativeRel.valuation C (2 : C) = 1 := by
    have hrel : (2 : C) =ᵥ (1 : C) := (Valuation.veq_iff_eq ν).mpr (by simpa only [map_one] using h2)
    simpa only [map_one] using (Valuation.veq_iff_eq (ValuativeRel.valuation C)).mp hrel
  exact normalizedAnalyticWeil_eq_localTameGaussSection C hi ψ hψ hu hc htwo x

end

end ArtinMatthews.QuadraticWeil
