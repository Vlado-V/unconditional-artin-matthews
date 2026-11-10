module

public import ArtinMatthews.SourcePrincipalBallCoset
public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDualLattice
public import ArtinMatthews.SourceFractionalIdealDualValuation
public import ArtinMatthews.SourcePrincipalBallQuotientKernel
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

/-! Identify the actual trace-dual lattice with source S-integer
frequencies divided by the modulus generator, retaining each finite
ball condition. The generator valuations are used explicitly. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain FractionalIdeal SIntegerPrincipalization
open StandardAdelic VaryingKummerAnalytic
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "FI" => FractionalIdeal (𝓞 K)⁰ K
local notation "S" => principalizingSet S₀
local notation "OS" => PrincipalIntegerRing S₀
local notation "d" => principalizingDenominator S₀

def SourcePrincipalBallFrequencies (e : S → ℤ) (a : OS) :=
  {h : OS // ∀ v : S, algebraMap K (v.val.adicCompletion K) ((h : K) / (a : K)) ∈
    sourceLocalBall K v.val ((sourceDifferentExponent K v.val : ℤ) + e v)}

theorem sourcePrincipalBallDual_valuation_iff (e : S → ℤ) (M : Ideal (𝓞 K))
    (hM : M ≠ ⊥) (hc : IsCoprime M (Ideal.span {d})) (hS : traceBadPlaces K ⊆ S)
    (a : OS) (ha : ∀ P : HeightOneSpectrum (𝓞 K), P ∉ S →
      P.valuation K (a : K) = WithZero.exp (-FractionalIdeal.count K P (M : FI))) (y : K) :
    y ∈ (mixedTraceDualIdeal K (sourcePrincipalBallProductUnit K S₀ e M hM)).val ↔
      (∀ P : HeightOneSpectrum (𝓞 K), P ∉ S → P.valuation K ((a : K) * y) ≤ 1) ∧
      ∀ v : S, algebraMap K (v.val.adicCompletion K) y ∈
        sourceLocalBall K v.val ((sourceDifferentExponent K v.val : ℤ) + e v) := by
  have hMF : (M : FI) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hM
  have hJ := sourceFiniteBallIdeal_ne_zero K S e
  have hcount (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ S) :
      FractionalIdeal.count K P (sourcePrincipalBallProductUnit K S₀ e M hM).val =
        FractionalIdeal.count K P (M : FI) := by
    rw [sourcePrincipalBallProductUnit_val, FractionalIdeal.count_mul K P hMF hJ,
      sourceFiniteBallIdeal_count K S e, dite_eq_right hP, add_zero]
  have hout (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ S) :
      P.valuation K y ≤ WithZero.exp ((sourceDifferentExponent K P : ℤ) +
        FractionalIdeal.count K P (sourcePrincipalBallProductUnit K S₀ e M hM).val) ↔
      P.valuation K ((a : K) * y) ≤ 1 := by
    rw [hcount P hP, (sourceDifferentExponent_eq_zero_iff K P).mpr (fun h => hP (hS h)),
      Int.natCast_zero, zero_add, map_mul, ha P hP]
    let k := FractionalIdeal.count K P (M : FI)
    have he : WithZero.exp (-k) * WithZero.exp k = 1 := by
      rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    rw [← he, mul_le_mul_iff_right₀ (pos_iff_ne_zero.mpr WithZero.exp_ne_zero)]
  rw [sourceTraceDualIdeal_mem_iff]
  constructor
  · intro h
    refine ⟨fun P hP => (hout P hP).mp (h P), fun v => ?_⟩
    have hv := h v.val
    rw [sourcePrincipalBallProductUnit_val, sourceFiniteBallIdeal_product_count_at_S K S e
      (M : FI) hMF (sourcePrincipalExteriorModulus_count_inS K S₀ M hM hc) v] at hv
    change Valued.v (y : v.val.adicCompletion K) ≤ _
    rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  · rintro ⟨h₁, h₂⟩ P
    by_cases hP : P ∈ S
    · let v : S := ⟨P, hP⟩
      rw [sourcePrincipalBallProductUnit_val, sourceFiniteBallIdeal_product_count_at_S K S e
        (M : FI) hMF (sourcePrincipalExteriorModulus_count_inS K S₀ M hM hc) v]
      have hv := h₂ v
      change Valued.v (y : P.adicCompletion K) ≤ _ at hv
      rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
    · exact (hout P hP).mpr (h₁ P hP)

def sourcePrincipalBallDualFrequencyEquiv (e : S → ℤ) (M : Ideal (𝓞 K))
    (hM : M ≠ ⊥) (hc : IsCoprime M (Ideal.span {d})) (hS : traceBadPlaces K ⊆ S)
    (a : OS) (ha : a ≠ 0) (hv : ∀ P : HeightOneSpectrum (𝓞 K), P ∉ S →
      P.valuation K (a : K) = WithZero.exp (-FractionalIdeal.count K P (M : FI))) :
    (mixedTraceDualIdeal K (sourcePrincipalBallProductUnit K S₀ e M hM)).val ≃
      SourcePrincipalBallFrequencies K S₀ e a := by
  have haK : (a : K) ≠ 0 := fun h => ha (Subtype.ext h)
  let H := sourcePrincipalBallDual_valuation_iff K S₀ e M hM hc hS a hv
  refine
    { toFun := fun y => ⟨⟨(a : K) * (y : K), ((H (y : K)).mp y.property).1⟩, ?_⟩
      invFun := fun h => ⟨((h.val : OS) : K) / (a : K), (H _).mpr ⟨?_, h.property⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro v
    change algebraMap K (v.val.adicCompletion K) ((a : K) * (y : K) / (a : K)) ∈ _
    rw [mul_div_cancel_left₀ _ haK]
    exact ((H (y : K)).mp y.property).2 v
  · intro P hP
    have hh : (a : K) * (((h.val : OS) : K) / (a : K)) = (h.val : K) := by
      rw [mul_comm, div_mul_cancel₀ _ haK]
    rw [hh]
    exact h.val.property P hP
  · intro y
    apply Subtype.ext
    exact mul_div_cancel_left₀ _ haK
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    change (a : K) * ((h.val : K) / (a : K)) = (h.val : K)
    rw [mul_comm, div_mul_cancel₀ _ haK]

end
end ArtinMatthews.SourcePhysical
