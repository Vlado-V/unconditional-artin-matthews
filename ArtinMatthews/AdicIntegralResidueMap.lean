module

public import ArtinMatthews.AdicConductorBridge
public import ArtinMatthews.StandardAdelicLocalQuotient
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! The actual integer-to-completed-residue ring map has exactly the
height-one prime as kernel. No quotient equivalence is assumed. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open scoped NumberField ValuativeRel Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local instance integerResidueRelation : ValuativeRel (v.adicCompletion F) := adicRelation F v
local instance integerResidueLocalField : IsNonarchimedeanLocalField (v.adicCompletion F) := adicLocalField F v

def adicIntegralOfInteger : 𝓞 F →+* 𝒪[v.adicCompletion F] where
  toFun x := ⟨algebraMap (𝓞 F) (v.adicCompletion F) x,
    (adic_mem_integer_iff F v _).mpr (HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := F) v x)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x y)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)

theorem adicIntegralOfInteger_val (x : 𝓞 F) :
    (adicIntegralOfInteger F v x : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) x := rfl

def adicResidueOfInteger : 𝓞 F →+* 𝓀[v.adicCompletion F] :=
  (IsLocalRing.residue 𝒪[v.adicCompletion F]).comp (adicIntegralOfInteger F v)

theorem adicResidueOfInteger_apply (x : 𝓞 F) :
    adicResidueOfInteger F v x =
      IsLocalRing.residue 𝒪[v.adicCompletion F] (adicIntegralOfInteger F v x) := rfl

theorem adic_residue_eq_zero_iff (x : 𝒪[v.adicCompletion F]) :
    IsLocalRing.residue 𝒪[v.adicCompletion F] x = 0 ↔
      ValuativeRel.valuation (v.adicCompletion F) (x : v.adicCompletion F) < 1 := by
  calc
    _ ↔ ¬ IsUnit x := by
      simpa only [not_ne_iff] using not_congr (IsLocalRing.residue_ne_zero_iff_isUnit x)
    _ ↔ _ := Valuation.Integer.not_isUnit_iff_valuation_lt_one

theorem adicResidueOfInteger_eq_zero_iff (x : 𝓞 F) :
    adicResidueOfInteger F v x = 0 ↔ x ∈ v.asIdeal := by
  let C := v.adicCompletion F
  let ν : Valuation C (WithZero (Multiplicative ℤ)) := Valued.v
  let : ν.Compatible := Valuation.Compatible.ofValuation ν
  rw [adicResidueOfInteger_apply, adic_residue_eq_zero_iff, adicIntegralOfInteger_val]
  calc
    _ ↔ ν (algebraMap (𝓞 F) C x) < 1 :=
      (Valuation.vlt_one_iff (ValuativeRel.valuation C)).symm.trans (Valuation.vlt_one_iff ν)
    _ ↔ v.intValuation x < 1 := by rw [StandardAdelic.localInteger_valuation]
    _ ↔ _ := v.intValuation_lt_one_iff_mem x

theorem adicResidueOfInteger_ker : RingHom.ker (adicResidueOfInteger F v) = v.asIdeal := by
  ext x
  exact adicResidueOfInteger_eq_zero_iff F v x

end

end ArtinMatthews.QuadraticWeil
