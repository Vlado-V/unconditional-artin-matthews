module

public import ArtinMatthews.SpectralABLSameCuspWeightedSeries


set_option backward.privateInPublic true
@[expose] public section

/-! The exact finite modulus cutoff for the compact exceptional test is
bounded by the genuine weighted ordinary Weil series. -/

noncomputable section
namespace ArtinMatthews

theorem spectralABLExceptional_compact_prefix_weil {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (N : ℕ) [NeZero N] (n : ℤ), n ≠ 0 →
      ∀ a : ℝ, 0 < a → a ≤ 1 →
      spectralKloostermanDiagSum N n (|cuspFourierFrequency 1 n|/(a^2/2)) ≤
        D*((N : ℝ)*(n.natAbs : ℝ)/a)^ε*
          (Real.sqrt ((n.natAbs : ℝ)*(Nat.gcd N n.natAbs : ℝ))/((N : ℝ)*a)) := by
  obtain ⟨D,hD,hWeil⟩ := spectralABLWeightedDiagSum_weil_physical hε
  refine ⟨D,hD,?_⟩
  intro N inst n hn a ha ha1
  let L := 4*Real.pi*(n.natAbs : ℝ)/((N : ℝ)*a^2)
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨hs, hbd⟩ := hWeil N n hn a ha ha1 1 le_rfl
  change Summable (spectralABLWeightedDiagWeight N n L 1) at hs
  change (∑' k, spectralABLWeightedDiagWeight N n L 1 k) ≤ _ at hbd
  have hL : |cuspFourierFrequency 1 n|/(a^2/2)/(N : ℝ) = L := by
    have he := spectralABL_diagonal_argument_scale n
    dsimp only [L]
    field_simp [ha.ne',hN.ne']
    linear_combination he
  unfold spectralKloostermanDiagSum
  rw [hL]
  calc
    _ = ∑ k ∈ Finset.range ⌊L⌋₊, spectralABLWeightedDiagWeight N n L 1 k := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkL : ((k+1 : ℕ) : ℝ) ≤ L := (Nat.le_floor_iff' (Nat.succ_ne_zero k)).mp
        (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
      have hratio : 1 ≤ L/((k+1 : ℕ) : ℝ) := (one_le_div (by positivity)).mpr hkL
      rw [spectralABLWeightedDiagWeight,
        min_eq_left (one_le_pow₀ hratio),mul_one]
    _ ≤ ∑' k, spectralABLWeightedDiagWeight N n L 1 k :=
      hs.sum_le_tsum _ (fun k _ => by unfold spectralABLWeightedDiagWeight spectralKloostermanDiagWeight; positivity)
    _ ≤ _ := hbd

end ArtinMatthews
