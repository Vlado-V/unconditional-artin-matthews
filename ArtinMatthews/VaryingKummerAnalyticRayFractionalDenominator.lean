module

public import ArtinMatthews.VaryingKummerAnalyticRayCharacter
public import Mathlib.RingTheory.DedekindDomain.AdicValuation


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine denominator clearing away from a nonzero ideal. Local adic
integrality constructs the denominator ideal, and the maximal-ideal
criterion plus CRT supplies a denominator coprime to the modulus. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal IsDedekindDomain
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def rayFractionalDenominatorIdeal (x : K) : Ideal (𝓞 K) where
  carrier := {b | ∃ a : 𝓞 K, x * (b : K) = (a : K)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro b c ⟨a, ha⟩ ⟨d, hd⟩
    refine ⟨a + d, ?_⟩
    change x * ((b : K) + (c : K)) = (a : K) + (d : K)
    rw [mul_add, ha, hd]
  smul_mem' := by
    rintro r b ⟨a, ha⟩
    refine ⟨r * a, ?_⟩
    change x * ((r : K) * (b : K)) = (r : K) * (a : K)
    rw [mul_left_comm, ha]

theorem rayFractionalDenominatorIdeal_coprime
    (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (x : K)
    (hlocal : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ M → v.valuation K x ≤ 1) :
    IsCoprime (rayFractionalDenominatorIdeal K x) M := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hn
  obtain ⟨P, hP, hDP⟩ := Ideal.exists_le_maximal
    (rayFractionalDenominatorIdeal K x ⊔ M) hn
  have hMP : M ≤ P := le_trans le_sup_right hDP
  let v : HeightOneSpectrum (𝓞 K) := ⟨P, hP.isPrime, ne_bot_of_le_ne_bot hM hMP⟩
  have hvM : v.asIdeal ∣ M := Ideal.dvd_iff_le.mpr hMP
  obtain ⟨a, b, hb⟩ := v.exists_primeCompl_mul_eq_of_integer x (hlocal v hvM)
  have hbD : b.val ∈ rayFractionalDenominatorIdeal K x := ⟨a, hb⟩
  exact b.property (hDP (Submodule.mem_sup_left hbD))

theorem ray_span_coprime_of_local_units (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (a : 𝓞 K)
    (hlocal : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ M →
      v.valuation K (a : K) = 1) : IsCoprime (Ideal.span {a}) M := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hn
  obtain ⟨P, hP, hAP⟩ := Ideal.exists_le_maximal (Ideal.span {a} ⊔ M) hn
  have hMP : M ≤ P := le_trans le_sup_right hAP
  let v : HeightOneSpectrum (𝓞 K) := ⟨P, hP.isPrime, ne_bot_of_le_ne_bot hM hMP⟩
  have hvM : v.asIdeal ∣ M := Ideal.dvd_iff_le.mpr hMP
  have haP : a ∈ v.asIdeal := hAP (Submodule.mem_sup_left (Ideal.mem_span_singleton_self a))
  have ha := (v.valuation_lt_one_iff_mem (K := K) a).mpr haP
  rw [hlocal v hvM] at ha
  exact lt_irrefl 1 ha

theorem exists_nonzero_integral_fraction (x : Kˣ) :
    ∃ a b : 𝓞 K, a ≠ 0 ∧ b ≠ 0 ∧ (x : K) = (a : K) / (b : K) := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 K) (x : K)
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have ha0 : a ≠ 0 := by
    intro ha
    apply x.ne_zero
    rw [← hab, ha, map_zero, zero_div]
  exact ⟨a, b, ha0, hb0, hab.symm⟩

/-- An actual field unit which is an adic unit at every prime dividing M
has an integral numerator and denominator both coprime to M. -/
theorem exists_coprime_integral_fraction_of_local_units
    (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (x : Kˣ)
    (hlocal : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ M → v.valuation K (x : K) = 1) :
    ∃ a b : 𝓞 K, a ≠ 0 ∧ b ≠ 0 ∧ IsCoprime (Ideal.span {a}) M ∧
      IsCoprime (Ideal.span {b}) M ∧ (x : K) = (a : K) / (b : K) := by
  by_cases htop : M = ⊤
  · obtain ⟨a, b, ha, hb, hab⟩ := exists_nonzero_integral_fraction K x
    refine ⟨a, b, ha, hb, ?_, ?_, hab⟩ <;>
      rw [htop, ← Ideal.one_eq_top] <;> exact isCoprime_one_right
  · have hD := rayFractionalDenominatorIdeal_coprime K M hM (x : K)
      (fun v hv => (hlocal v hv).le)
    obtain ⟨b, hbD, c, hcM, hbc⟩ := Ideal.isCoprime_iff_exists.mp hD
    have hb1 : b - 1 ∈ M := by
      have he : b - 1 = -c := by rw [← hbc]; ring
      rw [he]
      exact M.neg_mem hcM
    have hb0 : b ≠ 0 := by
      intro hz
      have h1 : (1 : 𝓞 K) ∈ M := by
        simpa only [hz, zero_sub, neg_neg] using M.neg_mem hb1
      exact htop ((Ideal.eq_top_iff_one M).mpr h1)
    obtain ⟨a, ha⟩ := hbD
    have hbK : (b : K) ≠ 0 := NumberField.RingOfIntegers.coe_ne_zero_iff.mpr hb0
    have haK : (a : K) ≠ 0 := by rw [← ha]; exact mul_ne_zero x.ne_zero hbK
    have ha0 : a ≠ 0 := NumberField.RingOfIntegers.coe_ne_zero_iff.mp haK
    have hbq : Ideal.Quotient.mk M b = 1 := by
      have H := Ideal.Quotient.eq_zero_iff_mem.mpr hb1
      simpa only [map_sub, map_one, sub_eq_zero] using H
    have hbcop : IsCoprime (Ideal.span {b}) M :=
      (quotient_isUnit_iff_span_coprime M b).mp (by rw [hbq]; exact isUnit_one)
    have hacop : IsCoprime (Ideal.span {a}) M := by
      apply ray_span_coprime_of_local_units K M hM a
      intro v hvM
      have hbn : b ∉ v.asIdeal := by
        intro hbp
        exact v.prime.not_isUnit
          (hbcop.isUnit_of_dvd' (Ideal.dvd_span_singleton.mpr hbp) hvM)
      have hbv : v.valuation K (b : K) = 1 := v.valuation_eq_one_iff_notMem.mpr hbn
      rw [← ha, map_mul, hlocal v hvM, hbv, one_mul]
    exact ⟨a, b, ha0, hb0, hacop, hbcop, (eq_div_iff hbK).mpr ha⟩

end
end ArtinMatthews.VaryingKummerAnalytic
