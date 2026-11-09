module

public import ArtinMatthews.ProbeIdealPrimeGauss
public import ArtinMatthews.ProbeIdealResidueDivision


set_option backward.privateInPublic true
@[expose] public section

/-! The exact congruence/removal identity for arbitrary ideal-prime powers. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def probeIdealResidueGauss (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) (hn : 0 < n)
    (h : (𝓞 K) ⧸ P.asIdeal ^ n) : ℂ :=
  ∑' x : ((𝓞 K) ⧸ P.asIdeal ^ n),
    χ (probeIdealResidueReduction K P n hn x) * probeIdealPhase K P n (h * x)

theorem probeIdealResidueGauss_mk (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) (hn : 0 < n) (h : 𝓞 K) :
    probeIdealResidueGauss K P χ n hn (Ideal.Quotient.mk (P.asIdeal ^ n) h) =
      probeIdealGaussAt K P χ n hn h := rfl

theorem probeIdealGaussAt_lift_residue (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) (h : 𝓞 K) :
    probeIdealGaussAt K P χ (n + 1) (Nat.succ_pos n) (probeIdealUniformizer P ^ n * h) =
      (Ideal.absNorm P.asIdeal : ℂ) ^ n *
        ∑' x : ((𝓞 K) ⧸ P.asIdeal), χ x * probeIdealResiduePhase K P (Ideal.Quotient.mk _ h * x) := by
  have he := probeIdealGaussAt_lift K P χ 1 n (by decide) h
  rw [probeIdealGaussAt_one] at he
  simpa only [Nat.add_comm] using he

theorem probeIdealGaussAt_divide (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n k : ℕ) (hn : 0 < n)
    (h : 𝓞 K) (hh : h ∈ P.asIdeal ^ k) :
    probeIdealGaussAt K P χ (n + k) (by omega) h =
      (Ideal.absNorm P.asIdeal : ℂ) ^ k *
        probeIdealResidueGauss K P χ n hn (probeIdealDivideResidue P n k h hh) := by
  let q := probeIdealDivideResidue P n k h hh
  let a : 𝓞 K := Quotient.out q
  have hqa : Ideal.Quotient.mk (P.asIdeal ^ n) a = q := Ideal.Quotient.mk_out q
  have hm : h - probeIdealUniformizer P ^ k * a ∈ P.asIdeal ^ (n + k) := by
    apply Ideal.Quotient.eq.mp
    calc
      Ideal.Quotient.mk (P.asIdeal ^ (n + k)) h = probePrimePowerScale P n k q :=
        (probeIdealDivideResidue_spec P n k h hh).symm
      _ = probePrimePowerScale P n k (Ideal.Quotient.mk (P.asIdeal ^ n) a) := by rw [hqa]
      _ = _ := probePrimePowerScale_mk P n k a
  calc
    _ = probeIdealGaussAt K P χ (n + k) (by omega) (probeIdealUniformizer P ^ k * a) :=
      probeIdealGaussAt_frequency_congr K P χ (n + k) (by omega) _ _ hm
    _ = (Ideal.absNorm P.asIdeal : ℂ) ^ k * probeIdealGaussAt K P χ n hn a :=
      probeIdealGaussAt_lift K P χ n k hn a
    _ = _ := by rw [← probeIdealResidueGauss_mk, hqa]

theorem probeIdealGaussAt_exactQuotient (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n k : ℕ) (hn : 0 < n) (h : 𝓞 K) :
    (if hh : h ∈ P.asIdeal ^ k then
      probeIdealResidueGauss K P χ n hn (probeIdealDivideResidue P n k h hh) else 0) =
      ((Ideal.absNorm P.asIdeal : ℂ) ^ k)⁻¹ *
        probeIdealGaussAt K P χ (n + k) (by omega) h := by
  have hQ : (Ideal.absNorm P.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot
  by_cases hh : h ∈ P.asIdeal ^ k
  · rw [dite_eq_left hh, probeIdealGaussAt_divide K P χ n k hn h hh,
      ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero k hQ), one_mul]
  · rw [dite_eq_right hh]
    have hzero : probeIdealGaussAt K P χ (n + k) (by omega) h = 0 := by
      apply probeIdealGaussAt_zero_off_support
      intro hm
      apply hh
      exact (Ideal.pow_le_pow_right (by omega : k ≤ n + k - 1)) hm
    rw [hzero, mul_zero]

end

end ArtinMatthews.VaryingKummerAnalytic
