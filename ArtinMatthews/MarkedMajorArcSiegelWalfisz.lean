module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.FunLike.Fintype
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
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
public import OAI.NumberTheory.PrimeGaps.Main


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine proved primitive Siegel-Walfisz estimate, extended to every
Dirichlet character with its exact finite prime-power conductor correction. -/
namespace ArtinMatthews
open Finset Filter
open scoped Topology

 theorem marked_all_character_mangoldt_log_bound (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q:ℝ) ≤ (Real.log x)^B →
        ‖(∑ n ∈ Ioc 0 ⌊x⌋₊, χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ))-
          (if χ=1 then (x:ℂ) else 0)‖ ≤
          M*x*(Real.log x)^(-A)+(Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  classical
  obtain ⟨M,hM,x₀,_,hSW⟩ := OAI.LargePrimeGaps.siegelWalfisz A B hA hB
  refine ⟨M,hM,?_⟩
  filter_upwards [eventually_ge_atTop x₀] with x hx
  intro q _ χ hq
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hcq : (χ.conductor:ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
  have hp := hSW x hx χ.conductor (NeZero.pos _) (hcq.trans hq)
    χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
  have hb := (OAI.LargePrimeGaps.primeCharacterError_le_primitive x (NeZero.pos q) χ).trans
    (add_le_add hp le_rfl)
  by_cases hχ : χ=1
  · simpa only [OAI.LargePrimeGaps.primeCharacterError,OAI.LargePrimeGaps.primeCharacterPrefix,ite_eq_left hχ] using hb
  · simpa only [OAI.LargePrimeGaps.primeCharacterError,OAI.LargePrimeGaps.primeCharacterPrefix,ite_eq_right hχ] using hb

end ArtinMatthews
