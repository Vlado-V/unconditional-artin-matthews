module

public import ArtinMatthews.AdicConductorBridge
public import ArtinMatthews.AdicConductorUniformizer
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


set_option backward.privateInPublic true
@[expose] public section

/-! A literal residue character associated to any actual adic prime
u with valuation exp(-1). It evaluates to ψ(x/u), without replacing u by
the chosen CFT uniformizer or discarding the comparison unit. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField ArtinMatthews.QuadraticGauss
open scoped NumberField ValuativeRel Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local instance primeResidueRelation : ValuativeRel (v.adicCompletion F) := adicRelation F v
local instance primeResidueLocalField : IsNonarchimedeanLocalField (v.adicCompletion F) := adicLocalField F v

variable (ψ : AddChar (v.adicCompletion F) ℂ) (hψ : adicConductorZero F v ψ)
  (u : v.adicCompletion F)
  (hu : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) u =
    WithZero.exp (-1 : ℤ))

def primeIntegerShift : AddChar 𝒪[v.adicCompletion F] ℂ where
  toFun x := ψ (u⁻¹ * (x : v.adicCompletion F))
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    change ψ (u⁻¹ * ((x : v.adicCompletion F) + (y : v.adicCompletion F))) = _
    rw [mul_add, ψ.map_add_eq_mul]

include hψ hu in
theorem primeIntegerShift_maximal (x : 𝒪[v.adicCompletion F])
    (hx : x ∈ (𝓂[v.adicCompletion F] : Ideal 𝒪[v.adicCompletion F])) :
    primeIntegerShift F v ψ u x = 1 := by
  let C := v.adicCompletion F
  rw [chosenIntegerRingUniformizer_maximalIdeal_eq, Ideal.mem_span_singleton] at hx
  obtain ⟨z, hz⟩ := hx
  have hzk := congrArg (fun a : 𝒪[C] => (a : C)) hz
  change (x : C) = (chosenIntegerRingUniformizer C : C) * (z : C) at hzk
  let r : 𝒪[C] := ⟨(chosenIntegerRingUniformizer C : C) * u⁻¹,
    adic_chosenPrime_div_prime_integral F v u hu⟩
  have heq : u⁻¹ * (x : C) = ((r * z : 𝒪[C]) : C) := by
    rw [hzk]
    change u⁻¹ * ((chosenIntegerRingUniformizer C : C) * (z : C)) =
      ((chosenIntegerRingUniformizer C : C) * u⁻¹) * (z : C)
    ring
  change ψ (u⁻¹ * (x : C)) = 1
  rw [heq]
  exact hψ.integer (r * z)

def adicPrimeResidueChar : AddChar 𝓀[v.adicCompletion F] ℂ :=
  AddChar.toAddMonoidHomEquiv.symm
    (QuotientAddGroup.lift (𝓂[v.adicCompletion F] : Ideal 𝒪[v.adicCompletion F]).toAddSubgroup
      (primeIntegerShift F v ψ u).toAddMonoidHom (by
        intro x hx
        change primeIntegerShift F v ψ u x = 1
        exact primeIntegerShift_maximal F v ψ hψ u hu x hx))

theorem adicPrimeResidueChar_apply (x : 𝒪[v.adicCompletion F]) :
    adicPrimeResidueChar F v ψ hψ u hu (IsLocalRing.residue 𝒪[v.adicCompletion F] x) =
      ψ (u⁻¹ * (x : v.adicCompletion F)) := rfl

theorem adicPrimeResidueChar_nontrivial : adicPrimeResidueChar F v ψ hψ u hu ≠ 1 := by
  intro he
  have hann : ∀ x ∈ v.adicCompletionIntegers F, ψ (u⁻¹ * x) = 1 := by
    intro x hx
    let xO : 𝒪[v.adicCompletion F] := ⟨x, (adic_mem_integer_iff F v x).mpr hx⟩
    have h := congrArg (fun χ : AddChar 𝓀[v.adicCompletion F] ℂ =>
      χ (IsLocalRing.residue 𝒪[v.adicCompletion F] xO)) he
    rw [adicPrimeResidueChar_apply, AddChar.one_apply] at h
    exact h
  have hinv := (adicConductorZero_dual F v ψ hψ u⁻¹).mp hann
  change (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) u⁻¹ ≤ 1 at hinv
  rw [map_inv₀, hu] at hinv
  exact (by decide : ¬ (WithZero.exp (-1 : ℤ))⁻¹ ≤ 1) hinv

theorem adicPrimeResidueChar_quadratic (x : 𝒪[v.adicCompletion F]) :
    adicPrimeResidueChar F v ψ hψ u hu (IsLocalRing.residue 𝒪[v.adicCompletion F] x ^ 2) =
      ψ (u⁻¹ * (x : v.adicCompletion F) ^ 2) := by
  calc
    _ = adicPrimeResidueChar F v ψ hψ u hu
        (IsLocalRing.residue 𝒪[v.adicCompletion F] (x ^ 2)) :=
      congrArg (adicPrimeResidueChar F v ψ hψ u hu)
        (map_pow (IsLocalRing.residue 𝒪[v.adicCompletion F]) x 2).symm
    _ = ψ (u⁻¹ * ((x ^ 2 : 𝒪[v.adicCompletion F]) : v.adicCompletion F)) :=
      adicPrimeResidueChar_apply F v ψ hψ u hu (x ^ 2)
    _ = _ := congrArg (fun z : v.adicCompletion F => ψ (u⁻¹ * z))
      (map_pow (ValuativeRel.valuation (v.adicCompletion F)).integer.subtype x 2)

end

end ArtinMatthews.QuadraticWeil
