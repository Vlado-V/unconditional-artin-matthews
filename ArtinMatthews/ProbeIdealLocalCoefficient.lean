module

public import ArtinMatthews.ProbeIdealLocalHigher
public import ArtinMatthews.ProbeIdealLocalAbsent
public import ArtinMatthews.ProbeIdealSixthTable


set_option backward.privateInPublic true
@[expose] public section

/-! A single notation for all literal local coefficient cases. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def probeIdealLocalCoefficient (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (t k J : ℕ) : ℂ :=
  match t, k with
  | 0, 0 => probePrimeLocalBothAbsent
  | 0, k + 1 => probeIdealLocalInnerAbsent K P χ k J
  | n + 1, 0 => probeIdealLocalCZero K P χ n J
  | n + 1, 1 => probeIdealLocalCOne K P χ n J
  | n + 1, k + 2 => probeIdealLocalHigher K P χ n (k + 1) J

theorem probeIdealLocalCoefficient_zero_zero (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (J : ℕ) :
    probeIdealLocalCoefficient K P χ 0 0 J = 1 :=
  probePrimeLocalBothAbsent_eq_one

theorem probeIdealLocalCoefficient_zero_succ (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k r : ℕ) :
    probeIdealLocalCoefficient K P χ 0 (k + 1) (6 * r) =
      if r = 0 then 1 else 0 := by
  rw [probeIdealLocalCoefficient, probeIdealLocalInnerAbsent_eq K P]
  simp

theorem probeIdealLocalCoefficient_higher (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n k J : ℕ) :
    probeIdealLocalCoefficient K P χ (n + 1) (k + 2) J = 0 := by
  rw [probeIdealLocalCoefficient]
  exact probeIdealLocalHigher_eq_zero K P χ n (k + 1) J (Nat.succ_pos k)

theorem probeIdealLocalCoefficient_zero_odd (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (d k r : ℕ) :
    probeIdealLocalCoefficient K P χ (6 * d + 3) k (6 * r) = 0 := by
  have ht : 6 * d + 3 = (6 * d + 2) + 1 := by omega
  rw [ht]
  cases k with
  | zero =>
      exact probeIdealLocalCZero_off_classes K P χ hχ (6 * d + 2) r (by omega) (by omega)
  | succ k =>
      cases k with
      | zero =>
          exact probeIdealLocalCOne_off_classes K P χ hχ hminus (6 * d + 2) r (by omega) (by omega)
      | succ k => exact probeIdealLocalCoefficient_higher K P χ _ k _

theorem probeIdealLocalCoefficient_one_odd (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (d k r : ℕ) :
    probeIdealLocalCoefficient K P χ (6 * d + 4) k (6 * r) = 0 := by
  have ht : 6 * d + 4 = (6 * d + 3) + 1 := by omega
  rw [ht]
  cases k with
  | zero =>
      exact probeIdealLocalCZero_off_classes K P χ hχ (6 * d + 3) r (by omega) (by omega)
  | succ k =>
      cases k with
      | zero =>
          exact probeIdealLocalCOne_off_classes K P χ hχ hminus (6 * d + 3) r (by omega) (by omega)
      | succ k => exact probeIdealLocalCoefficient_higher K P χ _ k _

end

end ArtinMatthews.VaryingKummerAnalytic
