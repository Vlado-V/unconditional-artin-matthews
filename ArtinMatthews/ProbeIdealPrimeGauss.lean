module

public import ArtinMatthews.ProbeIdealPrimeFourier
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

/-! Actual Gauss sums on P^n for arbitrary nonzero prime ideals P. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain WithZero
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def probeIdealResidueReduction (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) (hn : 0 < n) :
    ((𝓞 K) ⧸ P.asIdeal ^ n) →+* ((𝓞 K) ⧸ P.asIdeal) :=
  Ideal.Quotient.factor (Ideal.pow_le_self (Nat.ne_of_gt hn))

omit [NumberField K] in
theorem probeIdealResidueReduction_mk (P : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (hn : 0 < n) (x : 𝓞 K) :
    probeIdealResidueReduction K P n hn (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk P.asIdeal x := rfl

def probeIdealResiduePhase (P : HeightOneSpectrum (𝓞 K)) :
    AddChar ((𝓞 K) ⧸ P.asIdeal) ℂ := (idealTraceAddChar K P.asIdeal P.ne_bot)⁻¹

theorem probeIdealResiduePhase_primitive (P : HeightOneSpectrum (𝓞 K)) :
    (probeIdealResiduePhase K P).IsPrimitive := by
  intro x hx
  rw [probeIdealResiduePhase, AddChar.inv_mulShift, AddChar.mulShift_mulShift, neg_one_mul]
  exact idealTraceAddChar_isPrimitive K P.asIdeal P.ne_bot (neg_ne_zero.mpr hx)

theorem probeIdealPhase_one_mk (P : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    probeIdealPhase K P 1 (Ideal.Quotient.mk (P.asIdeal ^ 1) x) =
      probeIdealResiduePhase K P (Ideal.Quotient.mk P.asIdeal x) := by
  simp only [probeIdealPhase, probeIdealCoherentTrace, probeIdealTraceData,
    probeIdealReferenceTrace, probeIdealResiduePhase, AddChar.inv_apply',
    idealTraceAddChar_mk, pow_one]

def probeIdealGaussAt (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) (hn : 0 < n) (h : 𝓞 K) : ℂ :=
  ∑' x : ((𝓞 K) ⧸ P.asIdeal ^ n),
    χ (probeIdealResidueReduction K P n hn x) *
      probeIdealPhase K P n (Ideal.Quotient.mk _ h * x)

theorem probeIdealGaussAt_fourier (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n k : ℕ) (hn : 0 < n) (h : 𝓞 K) :
    probeIdealGaussAt K P χ (n + k) (by omega) h =
      probeIdealFourierSum K P n k (fun x => χ (probeIdealResidueReduction K P n hn x)) h := by
  unfold probeIdealGaussAt probeIdealFourierSum
  apply tsum_congr
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem probeIdealGaussAt_lift (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n k : ℕ) (hn : 0 < n) (h : 𝓞 K) :
    probeIdealGaussAt K P χ (n + k) (by omega) (probeIdealUniformizer P ^ k * h) =
      (Ideal.absNorm P.asIdeal : ℂ) ^ k * probeIdealGaussAt K P χ n hn h := by
  rw [probeIdealGaussAt_fourier K P χ n k hn, probeIdealFourierSum_lift]
  rfl

theorem probeIdealGaussAt_frequency_congr (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) (hn : 0 < n) (h h' : 𝓞 K)
    (hh : h - h' ∈ P.asIdeal ^ n) :
    probeIdealGaussAt K P χ n hn h = probeIdealGaussAt K P χ n hn h' := by
  have he : Ideal.Quotient.mk (P.asIdeal ^ n) h = Ideal.Quotient.mk _ h' :=
    Ideal.Quotient.eq.mpr hh
  simp only [probeIdealGaussAt, he]

theorem probeIdealGaussAt_support (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) (hn : 0 < n) (h : 𝓞 K)
    (hG : probeIdealGaussAt K P χ n hn h ≠ 0) : h ∈ P.asIdeal ^ (n - 1) := by
  have hdeg : 1 + (n - 1) = n := by omega
  have he : probeIdealGaussAt K P χ n hn h =
      probeIdealFourierSum K P 1 (n - 1)
        (fun x => χ (probeIdealResidueReduction K P 1 (by decide) x)) h := by
    simpa only [hdeg] using probeIdealGaussAt_fourier K P χ 1 (n - 1) (by decide) h
  exact probeIdealFourierSum_support K P 1 (n - 1) _ h (he ▸ hG)

theorem probeIdealGaussAt_zero_off_support (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) (hn : 0 < n) (h : 𝓞 K)
    (hh : h ∉ P.asIdeal ^ (n - 1)) : probeIdealGaussAt K P χ n hn h = 0 := by
  by_contra hG
  exact hh (probeIdealGaussAt_support K P χ n hn h hG)

def probeIdealResidueTransform (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (v : ℕ) (h : 𝓞 K) : ℂ :=
  ∑' x : ((𝓞 K) ⧸ P.asIdeal), (χ ^ v) x *
    probeIdealResiduePhase K P (Ideal.Quotient.mk _ h * x)

def probeIdealTau (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) : ℂ :=
  ∑' x : ((𝓞 K) ⧸ P.asIdeal), χ x * probeIdealResiduePhase K P x

theorem probeIdealGaussAt_one (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (h : 𝓞 K) :
    probeIdealGaussAt K P χ 1 (by decide) h =
      ∑' x : ((𝓞 K) ⧸ P.asIdeal), χ x * probeIdealResiduePhase K P (Ideal.Quotient.mk _ h * x) := by
  let e : ((𝓞 K) ⧸ P.asIdeal ^ 1) ≃+* ((𝓞 K) ⧸ P.asIdeal) :=
    Ideal.quotEquivOfEq (pow_one P.asIdeal)
  have hm (x : 𝓞 K) : e.symm (Ideal.Quotient.mk P.asIdeal x) =
      Ideal.Quotient.mk (P.asIdeal ^ 1) x := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (Ideal.quotEquivOfEq_mk (pow_one P.asIdeal) x).symm
  unfold probeIdealGaussAt
  rw [← e.symm.toEquiv.tsum_eq]
  apply tsum_congr
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change χ (probeIdealResidueReduction K P 1 _ (e.symm (Ideal.Quotient.mk _ x))) *
    probeIdealPhase K P 1 (Ideal.Quotient.mk _ h * e.symm (Ideal.Quotient.mk _ x)) = _
  rw [hm, probeIdealResidueReduction_mk, ← map_mul, probeIdealPhase_one_mk, map_mul]

theorem probeIdealUniformizer_pow_mem_iff (P : HeightOneSpectrum (𝓞 K)) (m n : ℕ) :
    probeIdealUniformizer P ^ m ∈ P.asIdeal ^ n ↔ n ≤ m := by
  rw [← P.intValuation_le_pow_iff_mem, probeIdealUniformizer_pow_valuation,
    WithZero.exp_le_exp]
  omega

theorem probeIdealGaussAt_prime_power (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n J : ℕ) (hn : 0 < n) :
    probeIdealGaussAt K P χ n hn (probeIdealUniformizer P ^ J) =
      if n - 1 ≤ J then (Ideal.absNorm P.asIdeal : ℂ) ^ (n - 1) *
        (∑' x : ((𝓞 K) ⧸ P.asIdeal), χ x * probeIdealResiduePhase K P
          (Ideal.Quotient.mk _ (probeIdealUniformizer P ^ (J - (n - 1))) * x)) else 0 := by
  by_cases hJ : n - 1 ≤ J
  · rw [ite_eq_left hJ]
    have hdeg : 1 + (n - 1) = n := by omega
    have hpow : probeIdealUniformizer P ^ J =
        probeIdealUniformizer P ^ (n - 1) * probeIdealUniformizer P ^ (J - (n - 1)) := by
      rw [← pow_add, Nat.add_sub_of_le hJ]
    have he := probeIdealGaussAt_lift K P χ 1 (n - 1) (by decide)
      (probeIdealUniformizer P ^ (J - (n - 1)))
    rw [probeIdealGaussAt_one] at he
    simpa only [hdeg, ← hpow] using he
  · rw [ite_eq_right hJ]
    exact probeIdealGaussAt_zero_off_support K P χ n hn _
      (fun hm => hJ ((probeIdealUniformizer_pow_mem_iff K P J (n - 1)).mp hm))

end

end ArtinMatthews.VaryingKummerAnalytic
