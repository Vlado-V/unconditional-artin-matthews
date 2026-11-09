module

public import ArtinMatthews.MarkedMemoryPotentialBirths
public import ArtinMatthews.MarkedMemoryBirthAtom
public import ArtinMatthews.MarkedMinorArcDirtyScalar


set_option backward.privateInPublic true
@[expose] public section

/-! The rank coefficient base at the actual moment length and the actual
memory cap B=ceil((log x)^2). The coarser encoding bound costs a fourth
power of the address count and is still absorbed by the birth atom. -/

noncomputable section
namespace ArtinMatthews
open Filter

def markedMemoryPotentialAddressCount (K : ℕ) (x : ℝ) : ℕ :=
  K*markedPadSlots x + (markedMemoryMomentLength x+1)*K*markedDirtyMemoryCutoff x +
    markedMemoryMomentLength x*K

theorem markedMemoryPotentialAddress_actual_card {J : Type*} [Fintype J] (x : ℝ) :
    Fintype.card (MarkedMemoryPotentialAddress J (markedPadSlots x)
      (markedDirtyMemoryCutoff x) (markedMemoryMomentLength x)) =
        markedMemoryPotentialAddressCount (Fintype.card J) x :=
  markedMemoryPotentialAddress_card _ _ _

theorem markedMemoryPotentialAddressCount_polynomial (K : ℕ) {x : ℝ}
    (hlog : 1 ≤ Real.log x) :
    (markedMemoryPotentialAddressCount K x : ℝ) ≤ 16*(K:ℝ)*(Real.log x)^3 := by
  let L := Real.log x
  have hL : 1 ≤ L := hlog
  have hL₀ : 0 ≤ L := zero_le_one.trans hL
  have hMpow : L^(1/100:ℝ) ≤ L := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (1/100:ℝ) ≤ 1)
  have hNpow : L^(1/2:ℝ) ≤ L := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (1/2:ℝ) ≤ 1)
  have hM : (markedPadSlots x:ℝ) ≤ 2*L := by
    have hh := Nat.floor_le (Real.rpow_nonneg hL₀ (1/100:ℝ))
    unfold markedPadSlots
    push_cast
    linarith
  have hN : (markedMemoryMomentLength x:ℝ) ≤ 3*L := by
    have hh := Nat.ceil_lt_add_one (div_nonneg (Real.rpow_nonneg hL₀ (1/2:ℝ))
      (by norm_num : (0:ℝ) ≤ 2))
    unfold markedMemoryMomentLength
    push_cast
    linarith
  have hB : (markedDirtyMemoryCutoff x:ℝ) ≤ 2*L^2 := by
    have hh := Nat.ceil_lt_add_one (sq_nonneg L)
    have hsq := one_le_pow₀ hL (n := 2)
    change (⌈L^2⌉₊:ℝ) ≤ _
    linarith
  have hNB : ((markedMemoryMomentLength x:ℝ)+1)*(markedDirtyMemoryCutoff x:ℝ) ≤
      (4*L)*(2*L^2) :=
    mul_le_mul (by linarith) hB (Nat.cast_nonneg _) (by positivity)
  have hLcube : L ≤ L^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hL (by norm_num : 1 ≤ 3)
  unfold markedMemoryPotentialAddressCount
  push_cast
  calc
    _ = (K:ℝ)*((markedPadSlots x:ℝ)+
        ((markedMemoryMomentLength x:ℝ)+1)*(markedDirtyMemoryCutoff x:ℝ)+
        (markedMemoryMomentLength x:ℝ)) := by ring
    _ ≤ (K:ℝ)*(16*L^3) := mul_le_mul_of_nonneg_left (by nlinarith) (Nat.cast_nonneg _)
    _ = _ := by dsimp [L]; ring

theorem markedMemoryBirth_rank_ratio_eventually (K : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      (((markedMemoryPotentialAddressCount K x:ℝ)^2+1)^2)*markedMemoryBirthAtomEnvelope x ≤
        Real.exp (-((Real.log x)^(1/10:ℝ))/2) := by
  let C := (((16*(K:ℝ))^2+1)^2)*(4/Real.log 2)
  have ht := ((rpow_mul_exp_neg_rpow_tendsto (12:ℝ)
    (by norm_num : (0:ℝ)<1/10) (by norm_num : (0:ℝ)<1/2)).const_mul C).comp
      Real.tendsto_log_atTop
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hlog
  have hL₀ : 0 ≤ Real.log x := zero_le_one.trans hlog
  have hQ := markedMemoryPotentialAddressCount_polynomial K hlog
  have hpow : (((markedMemoryPotentialAddressCount K x:ℝ)^2+1)^2) ≤
      (((16*(K:ℝ))^2+1)^2)*(Real.log x)^12 := by
    have hL6 : 1 ≤ (Real.log x)^6 := one_le_pow₀ hlog
    have hQ2 := pow_le_pow_left₀ (Nat.cast_nonneg (markedMemoryPotentialAddressCount K x)) hQ 2
    have hbase : (markedMemoryPotentialAddressCount K x:ℝ)^2+1 ≤
        ((16*(K:ℝ))^2+1)*(Real.log x)^6 := by nlinarith [hQ2]
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ (markedMemoryPotentialAddressCount K x:ℝ)^2+1) hbase 2
    convert hs using 1
    ring
  have hsmall : C*(Real.log x)^12*Real.exp (-((Real.log x)^(1/10:ℝ))/2) ≤ 1 := by
    apply le_of_lt
    have he : -(1/2:ℝ)*(Real.log x)^(1/10:ℝ) = -((Real.log x)^(1/10:ℝ))/2 := by ring
    simpa only [Function.comp_def,Real.rpow_natCast,Real.rpow_ofNat,he,mul_assoc] using hx
  calc
    _ ≤ ((((16*(K:ℝ))^2+1)^2)*(Real.log x)^12)*markedMemoryBirthAtomEnvelope x :=
      mul_le_mul_of_nonneg_right hpow (markedMemoryBirthAtomEnvelope_pos x).le
    _ = (C*(Real.log x)^12*Real.exp (-((Real.log x)^(1/10:ℝ))/2))*
        Real.exp (-((Real.log x)^(1/10:ℝ))/2) := by
      unfold markedMemoryBirthAtomEnvelope
      have he : Real.exp (-((Real.log x)^(1/10:ℝ))) =
          Real.exp (-((Real.log x)^(1/10:ℝ))/2)*Real.exp (-((Real.log x)^(1/10:ℝ))/2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he]
      dsimp [C]
      ring
    _ ≤ _ := mul_le_of_le_one_left (Real.exp_nonneg _) hsmall

end ArtinMatthews
