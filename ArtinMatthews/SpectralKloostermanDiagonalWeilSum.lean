module

public import ArtinMatthews.SpectralKloostermanDiagGcdSum
public import ArtinMatthews.SpectralMixedSameCuspDiagonalGramBound


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine finite diagonal modulus sum has the square-root
cutoff bound, retaining the complete frequency gcd and divisor factors. -/

noncomputable section
open scoped BigOperators
open OAI.Erdos970.ErdosKloosterman

namespace ArtinMatthews

theorem spectralKloostermanDiagSum_weil {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (N : ℕ) [NeZero N] (n : ℤ), n ≠ 0 → ∀ Q : ℝ, 0 < Q →
      spectralKloostermanDiagSum N n Q ≤
        D*Q^ε*(n.natAbs.divisors.card : ℝ)*Real.sqrt (Nat.gcd N n.natAbs : ℝ)*
          Real.sqrt Q/(N : ℝ) := by
  obtain ⟨D,hD,hWeil⟩ := standardKloosterman_weil_bound hε
  refine ⟨2*D,by positivity,?_⟩
  intro N inst n hn Q hQ
  let L := ⌊Q/(N : ℝ)⌋₊
  let m := n.natAbs
  let g := Real.sqrt (Nat.gcd N m : ℝ)
  let U := D*Q^ε*(g/Real.sqrt (N : ℝ))
  have hm : 0 < m := Int.natAbs_pos.mpr hn
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hU : 0 ≤ U := by dsimp only [U,g]; positivity
  have hpoint (k : ℕ) (hk : k ∈ Finset.range L) :
      spectralKloostermanDiagWeight N n k ≤
        U*(Real.sqrt (Nat.gcd (k+1) m : ℝ)/Real.sqrt ((k+1 : ℕ) : ℝ)) := by
    let v := k+1
    let C := N*v
    let c : ℝ := C
    let G := Real.sqrt (Nat.gcd C m : ℝ)
    let g' := Real.sqrt (Nat.gcd v m : ℝ)
    have hv : 0 < v := Nat.succ_pos k
    let _ : NeZero C := ⟨(Nat.mul_pos (NeZero.pos N) hv).ne'⟩
    have hc : 0 < c := Nat.cast_pos.mpr (NeZero.pos C)
    have hcs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
    have hcv : (v : ℝ) ≤ Q/(N : ℝ) := (Nat.le_floor_iff' (Nat.succ_ne_zero k)).mp
      (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
    have hC : c ≤ Q := by
      dsimp only [c,C]
      rw [Nat.cast_mul,mul_comm]
      exact (le_div_iff₀ hN).mp hcv
    have hW : ‖standardSum C n n‖ ≤ D*c^((1/2 : ℝ)+ε)*G := by
      simpa only [Int.gcd_def,Nat.gcd_self,← Real.sqrt_eq_rpow,c,G,m] using hWeil C n n
    have hExp : c^((1/2 : ℝ)+ε)/c = c^ε/Real.sqrt c := by
      rw [Real.rpow_add hc,← Real.sqrt_eq_rpow]
      apply (div_eq_div_iff hc.ne' hcs.ne').mpr
      calc
        _ = (Real.sqrt c)^2*c^ε := by ring
        _ = _ := by rw [Real.sq_sqrt hc.le,mul_comm]
    have hGcd : Nat.gcd C m ∣ Nat.gcd N m*Nat.gcd v m := by
      have h := gcd_mul_dvd_mul_gcd m N v
      change Nat.gcd m (N*v) ∣ Nat.gcd m N*Nat.gcd m v at h
      simpa only [C,Nat.gcd_comm m (N*v),Nat.gcd_comm m N,Nat.gcd_comm m v] using h
    have hgg : G ≤ g*g' := by
      have hprod : 0 < Nat.gcd N m*Nat.gcd v m :=
        Nat.mul_pos (Nat.gcd_pos_of_pos_left m (NeZero.pos N)) (Nat.gcd_pos_of_pos_left m hv)
      have hle := Real.sqrt_le_sqrt (Nat.cast_le.mpr (Nat.le_of_dvd hprod hGcd))
      simpa only [G,g,g',Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg (Nat.gcd N m))] using hle
    have hs : Real.sqrt c = Real.sqrt (N : ℝ)*Real.sqrt (v : ℝ) := by
      dsimp only [c,C]
      rw [Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg N)]
    have hratio : G/Real.sqrt c ≤ (g/Real.sqrt (N : ℝ))*(g'/Real.sqrt (v : ℝ)) := by
      rw [div_mul_div_comm,← hs]
      exact div_le_div_of_nonneg_right hgg hcs.le
    change ‖standardSum C n n‖/c ≤ U*(g'/Real.sqrt (v : ℝ))
    calc
      _ ≤ (D*c^((1/2 : ℝ)+ε)*G)/c := div_le_div_of_nonneg_right hW hc.le
      _ = (D*c^ε)*(G/Real.sqrt c) := by
        rw [show D*c^((1/2 : ℝ)+ε)*G/c = D*(c^((1/2 : ℝ)+ε)/c)*G by ring,hExp]
        ring
      _ ≤ (D*Q^ε)*(G/Real.sqrt c) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hc.le hC hε.le) hD.le) (by dsimp only [G]; positivity)
      _ ≤ (D*Q^ε)*((g/Real.sqrt (N : ℝ))*(g'/Real.sqrt (v : ℝ))) :=
        mul_le_mul_of_nonneg_left hratio (mul_nonneg hD.le (Real.rpow_nonneg hQ.le _))
      _ = _ := by dsimp only [U]; ring
  have hL : (L : ℝ) ≤ Q/(N : ℝ) := Nat.floor_le (div_nonneg hQ.le hN.le)
  have hRs : (g/Real.sqrt (N : ℝ))*(Real.sqrt Q/Real.sqrt (N : ℝ)) =
      g*Real.sqrt Q/(N : ℝ) := by rw [div_mul_div_comm,← sq,Real.sq_sqrt hN.le]
  change (∑ k ∈ Finset.range L, spectralKloostermanDiagWeight N n k) ≤
    (2*D)*Q^ε*(m.divisors.card : ℝ)*g*Real.sqrt Q/(N : ℝ)
  calc
    _ ≤ U*(∑ k ∈ Finset.range L,
        Real.sqrt (Nat.gcd (k+1) m : ℝ)/Real.sqrt ((k+1 : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hpoint
    _ ≤ U*(2*Real.sqrt (L : ℝ)*(m.divisors.card : ℝ)) :=
      mul_le_mul_of_nonneg_left (spectral_sum_sqrt_gcd_div_sqrt_le m L hm) hU
    _ ≤ U*(2*Real.sqrt (Q/(N : ℝ))*(m.divisors.card : ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hL) (by norm_num)) (Nat.cast_nonneg _)) hU
    _ = _ := by
      rw [Real.sqrt_div hQ.le]
      dsimp only [U]
      calc
        _ = (2*D)*Q^ε*(m.divisors.card : ℝ)*
            ((g/Real.sqrt (N : ℝ))*(Real.sqrt Q/Real.sqrt (N : ℝ))) := by ring
        _ = _ := by rw [hRs]; ring

end ArtinMatthews
