module

public import ArtinMatthews.SourceFiniteBallIdeal
public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDualLattice
public import ArtinMatthews.SourceFractionalIdealValuation
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

/-! Actual trace-dual lattice bounds and comparison of the archimedean
and source S-place phases. No exterior-character comparison is assumed. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain FractionalIdeal StandardAdelic VaryingKummerAnalytic
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable (K : Type) [Field K] [NumberField K]

local notation "FI" => FractionalIdeal (𝓞 K)⁰ K

theorem sourceFractionalIdeal_dual_count (I : FI) (hI : I ≠ 0)
    (P : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K P (FractionalIdeal.dual ℤ ℚ I) =
      -(sourceDifferentExponent K P : ℤ) - FractionalIdeal.count K P I := by
  have hD : FractionalIdeal.dual ℤ ℚ (1 : FI) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  rw [FractionalIdeal.dual_eq_mul_inv ℤ ℚ,
    FractionalIdeal.count_mul K P hD (inv_ne_zero hI), sourceCodifferent_count K P,
    FractionalIdeal.count_inv, sub_eq_add_neg]

theorem sourceFractionalIdeal_dual_mem_iff (I : FI) (hI : I ≠ 0) (y : K) :
    y ∈ FractionalIdeal.dual ℤ ℚ I ↔ ∀ P : HeightOneSpectrum (𝓞 K),
      P.valuation K y ≤ WithZero.exp ((sourceDifferentExponent K P : ℤ) +
        FractionalIdeal.count K P I) := by
  rw [sourceFractionalIdeal_mem_iff_valuation K _ (FractionalIdeal.dual_ne_zero ℤ ℚ hI)]
  simp only [sourceFractionalIdeal_dual_count K I hI, neg_sub, sub_neg_eq_add, add_comm]

theorem sourceTraceDualIdeal_mem_iff (I : FIˣ) (y : K) :
    y ∈ (mixedTraceDualIdeal K I).val ↔ ∀ P : HeightOneSpectrum (𝓞 K),
      P.valuation K y ≤ WithZero.exp ((sourceDifferentExponent K P : ℤ) +
        FractionalIdeal.count K P I.val) :=
  sourceFractionalIdeal_dual_mem_iff K I.val I.ne_zero y

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

theorem sourceFiniteBallIdeal_product_count_at_S (e : S → ℤ) (M : FI) (hM : M ≠ 0)
    (hMS : ∀ v : S, FractionalIdeal.count K v.val M = 0) (v : S) :
    FractionalIdeal.count K v.val (M * sourceFiniteBallIdeal K S e) = e v := by
  rw [FractionalIdeal.count_mul K v.val hM (sourceFiniteBallIdeal_ne_zero K S e),
    hMS v, sourceFiniteBallIdeal_count K S e, dite_eq_left v.property, zero_add]

theorem sourceFiniteBallIdeal_product_dual_inS (e : S → ℤ) (M : FI) (hM : M ≠ 0)
    (hMS : ∀ v : S, FractionalIdeal.count K v.val M = 0)
    (y : K) (hy : y ∈ FractionalIdeal.dual ℤ ℚ (M * sourceFiniteBallIdeal K S e))
    (v : S) :
    algebraMap K (v.val.adicCompletion K) y ∈ sourceLocalBall K v.val
      ((sourceDifferentExponent K v.val : ℤ) + e v) := by
  have h := (sourceFractionalIdeal_dual_mem_iff K _
    (mul_ne_zero hM (sourceFiniteBallIdeal_ne_zero K S e)) y).mp hy v.val
  rw [sourceFiniteBallIdeal_product_count_at_S K S e M hM hMS v] at h
  change Valued.v (y : v.val.adicCompletion K) ≤ _
  rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

theorem sourceFiniteBallIdeal_product_dual_phase (e : S → ℤ) (M : FI) (hM : M ≠ 0)
    (hMS : ∀ v : S, FractionalIdeal.count K v.val M = 0)
    (x y : K) (hx : x ∈ sourceFiniteBallIdeal K S e)
    (hy : y ∈ FractionalIdeal.dual ℤ ℚ (M * sourceFiniteBallIdeal K S e)) :
    sCharacter K S (y * x) = rationalCharacter K (y * x) := by
  change rationalCharacter K (y * x) * (∏ v ∈ S,
    localFiniteCharacter K v (algebraMap K (v.adicCompletion K) (y * x))) = _
  have h : (∏ v ∈ S, localFiniteCharacter K v (algebraMap K (v.adicCompletion K) (y * x))) = 1 := by
    apply Finset.prod_eq_one
    intro P hP
    let v : S := ⟨P, hP⟩
    have hxv := ((sourceFiniteBallIdeal_mem_iff K S e x).mp hx).2 v
    have hyv := sourceFiniteBallIdeal_product_dual_inS K S e M hM hMS y hy v
    apply sourceLocalCharacter_codifferent K P
    change sourceLocalValuation K P (algebraMap K (P.adicCompletion K) (y * x)) ≤ _
    rw [map_mul, map_mul]
    have he : (sourceDifferentExponent K P : ℤ) + e v + -(e v) =
        (sourceDifferentExponent K P : ℤ) := by ring
    rw [← he, WithZero.exp_add]
    exact mul_le_mul' hyv hxv
  rw [h, mul_one]

end
end ArtinMatthews.SourcePhysical
