module

public import ArtinMatthews.SourceKPCuspTraceFrequency
public import ArtinMatthews.SourceKPCuspTraceModeDictionary
public import ArtinMatthews.SourceKPCuspTraceModePhase
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


set_option backward.privateInPublic true
@[expose] public section

/-! Nonzero integer modes give exactly the units in the fixed trace dual.
This reindexes sums on the principal torus when the summand vanishes
outside that dual. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain Module.Free
open scoped NumberField nonZeroDivisors
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable (d : 𝓞 K) (hd : d ≠ 0)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "J" => {n : I → ℤ // n ≠ 0}
local notation "D[" d "]" => FractionalIdeal.dual ℤ ℚ
  ((Ideal.span ({d} : Set (𝓞 K)) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)

def sourceKPCuspTraceModeUnit (n : J) : Kˣ :=
  Units.mk0 (sourceKPCuspTraceFrequency K d n.val)
    (sourceKPCuspTraceFrequency_ne_zero K d hd n.property)

@[simp]
theorem sourceKPCuspTraceModeUnit_val (n : J) :
    (sourceKPCuspTraceModeUnit K d hd n : K) = sourceKPCuspTraceFrequency K d n.val := rfl

theorem sourceKPCuspTraceModeUnit_injective : Function.Injective (sourceKPCuspTraceModeUnit K d hd) := by
  intro n k h
  apply Subtype.ext
  apply (sourceKPCuspTraceDualIndexEquiv K d hd).injective
  apply Subtype.ext
  exact congrArg (fun m : Kˣ => (m : K)) h

theorem sourceKPCuspTraceModeUnit_range :
    Set.range (sourceKPCuspTraceModeUnit K d hd) = {m : Kˣ | (m : K) ∈ D[d]} := by
  ext m
  constructor
  · rintro ⟨n, rfl⟩
    exact sourceKPCuspTraceFrequency_mem_dual K d n.val
  · intro hm
    obtain ⟨n, hn⟩ := (sourceKPCuspTraceDualIndexEquiv K d hd).surjective ⟨(m : K), hm⟩
    have hfreq : sourceKPCuspTraceFrequency K d n = (m : K) := congrArg Subtype.val hn
    have hne : n ≠ 0 := fun hn₀ =>
      m.ne_zero (hfreq.symm.trans ((sourceKPCuspTraceFrequency_zero_iff K d hd n).2 hn₀))
    exact ⟨⟨n, hne⟩, Units.ext hfreq⟩

theorem sourceKPCuspTraceModeUnit_hasSum_iff (f : Kˣ → ℂ)
    (hzero : ∀ m : Kˣ, (m : K) ∉ D[d] → f m = 0) (a : ℂ) :
    HasSum (fun n : J => f (sourceKPCuspTraceModeUnit K d hd n)) a ↔ HasSum f a := by
  apply (sourceKPCuspTraceModeUnit_injective K d hd).hasSum_iff
  intro m hm
  rw [sourceKPCuspTraceModeUnit_range K d hd] at hm
  exact hzero m hm

end
end ArtinMatthews
