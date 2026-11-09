module

public import ArtinMatthews.SpectralDyadicPrefixWeight
public import ArtinMatthews.SpectralKloostermanDiagonalWeilSum


set_option backward.privateInPublic true
@[expose] public section

/-! The full power-cutoff diagonal Weil sum and its physical ABL scale. -/

noncomputable section
open OAI.Erdos970

namespace ArtinMatthews

def spectralABLWeightedDiagWeight (N : ℕ) [NeZero N] (n : ℤ)
    (L : ℝ) (A k : ℕ) : ℝ :=
  spectralKloostermanDiagWeight N n k * min 1 ((L/((k+1 : ℕ) : ℝ))^(2*A))

theorem spectralABLWeightedDiagSum_weil_divisors {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) :
    ∃ D : ℝ, 0 < D ∧ ∀ (N : ℕ) [NeZero N] (n : ℤ), n ≠ 0 →
      ∀ (L : ℝ), 0 < L → ∀ (A : ℕ), 1 ≤ A →
        Summable (spectralABLWeightedDiagWeight N n L A) ∧
        (∑' k, spectralABLWeightedDiagWeight N n L A k) ≤
          D*((N : ℝ)*L)^δ*(n.natAbs.divisors.card : ℝ)*
            Real.sqrt ((Nat.gcd N n.natAbs : ℝ)*L/(N : ℝ)) := by
  obtain ⟨D,hD,hweil⟩ := spectralKloostermanDiagSum_weil hδ
  refine ⟨4*D, by positivity, ?_⟩
  intro N inst n hn L hL A hA
  let g := Real.sqrt (Nat.gcd N n.natAbs : ℝ)
  let C := D*(N : ℝ)^δ*(n.natAbs.divisors.card : ℝ)*g/Real.sqrt (N : ℝ)
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN
  have hC : 0 ≤ C := by dsimp only [C,g]; positivity
  have hprefix (T : ℝ) (hT : 0 < T) :
      (∑ k ∈ Finset.range ⌊T⌋₊, spectralKloostermanDiagWeight N n k) ≤ C*T^((1/2 : ℝ)+δ) := by
    have hw := hweil N n hn ((N : ℝ)*T) (mul_pos hN hT)
    unfold spectralKloostermanDiagSum at hw
    rw [mul_div_cancel_left₀ T hN.ne', Real.mul_rpow hN.le hT.le,
      Real.sqrt_mul hN.le] at hw
    refine hw.trans_eq ?_
    rw [Real.rpow_add hT, ← Real.sqrt_eq_rpow]
    dsimp only [C,g]
    field_simp [hN.ne', hsN.ne']
    rw [Real.sq_sqrt hN.le]
  obtain ⟨hs,hb⟩ := spectral_weighted_prefix_bound (spectralKloostermanDiagWeight N n)
    (fun k => by unfold spectralKloostermanDiagWeight; positivity) hC (by linarith : (1/2:ℝ)+δ ≤ 1)
    hL A hA hprefix
  refine ⟨hs,hb.trans_eq ?_⟩
  rw [Real.rpow_add hL, ← Real.sqrt_eq_rpow, Real.mul_rpow hN.le hL.le,
    Real.sqrt_div (mul_nonneg (Nat.cast_nonneg _) hL.le), Real.sqrt_mul (Nat.cast_nonneg _)]
  dsimp only [C,g]
  ring

theorem spectralABLWeightedDiagSum_weil {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (n : ℤ), n ≠ 0 →
      ∀ (L : ℝ), 0 < L → ∀ (A : ℕ), 1 ≤ A →
        Summable (spectralABLWeightedDiagWeight N n L A) ∧
        (∑' k, spectralABLWeightedDiagWeight N n L A k) ≤
          C*((N : ℝ)*(1+L)*(n.natAbs : ℝ))^ε*
            Real.sqrt ((Nat.gcd N n.natAbs : ℝ)*L/(N : ℝ)) := by
  let δ := min ε (1/4 : ℝ)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδ1 : δ ≤ 1/2 := (min_le_right _ _).trans (by norm_num)
  obtain ⟨D,hD,hW⟩ := spectralABLWeightedDiagSum_weil_divisors hδ hδ1
  obtain ⟨E,hE,hdiv⟩ := ErdosDivisorBounds.divisor_power_subpower 1 hδ
  refine ⟨D*E, by positivity, ?_⟩
  intro N inst n hn L hL A hA
  have hN : 1 ≤ (N : ℝ) := by exact_mod_cast NeZero.one_le
  have hm : 1 ≤ n.natAbs := Nat.succ_le_of_lt (Int.natAbs_pos.mpr hn)
  have hmR : 1 ≤ (n.natAbs : ℝ) := by exact_mod_cast hm
  have hcard : (n.natAbs.divisors.card : ℝ) ≤ E*(n.natAbs : ℝ)^δ := by
    simpa only [pow_one] using hdiv n.natAbs hm
  have hb : 1 ≤ (N : ℝ)*(1+L)*(n.natAbs : ℝ) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hN (by linarith)) hmR
  have hp : ((N : ℝ)*L)^δ*(n.natAbs : ℝ)^δ ≤ ((N : ℝ)*(1+L)*(n.natAbs : ℝ))^ε := by
    rw [← Real.mul_rpow (mul_nonneg (Nat.cast_nonneg _) hL.le) (Nat.cast_nonneg _)]
    apply le_trans (Real.rpow_le_rpow (by positivity) _ hδ.le)
      (Real.rpow_le_rpow_of_exponent_le hb hδε)
    gcongr
    linarith
  obtain ⟨hs,hw⟩ := hW N n hn L hL A hA
  refine ⟨hs,hw.trans ?_⟩
  calc
    _ ≤ D*((N : ℝ)*L)^δ*(E*(n.natAbs : ℝ)^δ)*
        Real.sqrt ((Nat.gcd N n.natAbs : ℝ)*L/(N : ℝ)) := by gcongr
    _ = (D*E)*(((N : ℝ)*L)^δ*(n.natAbs : ℝ)^δ)*
        Real.sqrt ((Nat.gcd N n.natAbs : ℝ)*L/(N : ℝ)) := by ring
    _ ≤ _ := by gcongr

theorem spectralABLWeightedDiagSum_weil_physical {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (n : ℤ), n ≠ 0 →
      ∀ (a : ℝ), 0 < a → a ≤ 1 → ∀ (A : ℕ), 1 ≤ A →
        let L := 4*Real.pi*(n.natAbs : ℝ)/((N : ℝ)*a^2)
        Summable (spectralABLWeightedDiagWeight N n L A) ∧
        (∑' k, spectralABLWeightedDiagWeight N n L A k) ≤
          C*((N : ℝ)*(n.natAbs : ℝ)/a)^ε*
            (Real.sqrt ((n.natAbs : ℝ)*(Nat.gcd N n.natAbs : ℝ))/((N : ℝ)*a)) := by
  let δ := min (ε/2) (1/4 : ℝ)
  have hδ : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδε : 2*δ ≤ ε := by have h := min_le_left (ε/2) (1/4 : ℝ); dsimp only [δ]; linarith
  have hδ1 : δ ≤ 1/2 := (min_le_right _ _).trans (by norm_num)
  obtain ⟨D,hD,hW⟩ := spectralABLWeightedDiagSum_weil_divisors hδ hδ1
  obtain ⟨E,hE,hdiv⟩ := ErdosDivisorBounds.divisor_power_subpower 1 hδ
  let κ : ℝ := 4*Real.pi
  have hκ : 0 < κ := mul_pos (by norm_num) Real.pi_pos
  refine ⟨D*E*κ^δ*Real.sqrt κ, by positivity, ?_⟩
  intro N inst n hn a ha ha1 A hA
  dsimp only
  let m : ℝ := n.natAbs
  let g : ℝ := Nat.gcd N n.natAbs
  let L := κ*m/((N : ℝ)*a^2)
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast NeZero.one_le
  have hmNat : 1 ≤ n.natAbs := Nat.succ_le_of_lt (Int.natAbs_pos.mpr hn)
  have hm1 : 1 ≤ m := by
    change (1 : ℝ) ≤ (n.natAbs : ℝ)
    exact_mod_cast hmNat
  have hm : 0 < m := zero_lt_one.trans_le hm1
  have hg : 0 ≤ g := Nat.cast_nonneg _
  have hL : 0 < L := div_pos (mul_pos hκ hm) (mul_pos hN (pow_pos ha _))
  have hcard : (n.natAbs.divisors.card : ℝ) ≤ E*m^δ := by
    simpa only [pow_one] using hdiv n.natAbs hmNat
  have hp : ((N : ℝ)*L)^δ*m^δ = κ^δ*(m/a)^(2*δ) := by
    have hbase : (N : ℝ)*L*m = κ*(m/a)^2 := by
      dsimp only [L]
      field_simp [hN.ne',ha.ne']
    rw [← Real.mul_rpow (mul_nonneg hN.le hL.le) hm.le, hbase,
      Real.mul_rpow hκ.le (sq_nonneg _)]
    rw [← Real.rpow_natCast_mul (div_nonneg hm.le ha.le) 2 δ]
    norm_num
  have hscale : (m/a)^(2*δ) ≤ ((N : ℝ)*m/a)^ε := by
    have h1 : 1 ≤ m/a := (one_le_div ha).mpr (ha1.trans hm1)
    refine (Real.rpow_le_rpow_of_exponent_le h1 hδε).trans
      (Real.rpow_le_rpow (div_nonneg hm.le ha.le) ?_ hε.le)
    exact div_le_div_of_nonneg_right (le_mul_of_one_le_left hm.le hN1) ha.le
  have hsqrt : Real.sqrt (g*L/(N : ℝ)) =
      Real.sqrt κ*(Real.sqrt (m*g)/((N : ℝ)*a)) := by
    have hbase : g*L/(N : ℝ) = κ*(m*g)/((N : ℝ)*a)^2 := by
      dsimp only [L]
      field_simp [hN.ne',ha.ne']
    rw [hbase, Real.sqrt_div (mul_nonneg hκ.le (mul_nonneg hm.le hg)),
      Real.sqrt_mul hκ.le, Real.sqrt_sq (mul_nonneg hN.le ha.le)]
    ring
  obtain ⟨hs,hw⟩ := hW N n hn L hL A hA
  change Summable (spectralABLWeightedDiagWeight N n L A) ∧
    (∑' k, spectralABLWeightedDiagWeight N n L A k) ≤
      (D*E*κ^δ*Real.sqrt κ)*((N : ℝ)*m/a)^ε*(Real.sqrt (m*g)/((N : ℝ)*a))
  refine ⟨hs,hw.trans ?_⟩
  calc
    _ ≤ D*((N : ℝ)*L)^δ*(E*m^δ)*Real.sqrt (g*L/(N : ℝ)) := by gcongr
    _ = D*E*(((N : ℝ)*L)^δ*m^δ)*Real.sqrt (g*L/(N : ℝ)) := by ring
    _ = (D*E*κ^δ*Real.sqrt κ)*(m/a)^(2*δ)*(Real.sqrt (m*g)/((N : ℝ)*a)) := by
      rw [hp, hsqrt]
      ring
    _ ≤ _ := by gcongr

end ArtinMatthews
