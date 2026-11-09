module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option backward.privateInPublic true
@[expose] public section

/-! Exponent iteration in the quadratic Hecke sieve. The initial estimate
and the analytic improvement are kept as separate explicit inputs. -/
namespace ArtinMatthews

/-- The exponent bound for the squarefree quadratic Hecke sieve energy. -/
def QuadraticHeckeSieveExponentBound (energy : ℝ → ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
    energy M N ≤ C * (M * N) ^ ε * (M + N ^ a)

theorem quadraticHeckeSieveExponentBound_bootstrap
    (energy : ℝ → ℝ → ℝ) (hbase : QuadraticHeckeSieveExponentBound energy 2)
    (hstep : ∀ a : ℝ, 1 < a → QuadraticHeckeSieveExponentBound energy a →
      QuadraticHeckeSieveExponentBound energy (2 - a⁻¹)) :
    QuadraticHeckeSieveExponentBound energy 1 := by
  have hseq (n : ℕ) : QuadraticHeckeSieveExponentBound energy (1 + ((n : ℝ) + 1)⁻¹) := by
    induction n with
    | zero => norm_num at *; exact hbase
    | succ n ih =>
      have hn : 0 < (n : ℝ) + 1 := by positivity
      have hstepn := hstep (1 + ((n : ℝ) + 1)⁻¹) (by linarith [inv_pos.mpr hn]) ih
      have he : 2 - (1 + ((n : ℝ) + 1)⁻¹)⁻¹ = 1 + ((n.succ : ℝ) + 1)⁻¹ := by
        push_cast
        field_simp
        ring
      rwa [← he]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / ε)
  let δ := ((n : ℝ) + 1)⁻¹
  have hδ : δ ≤ ε / 2 := by
    have hε' : 0 < ε / 2 := half_pos hε
    have hn' : (ε / 2)⁻¹ < (n : ℝ) + 1 := by
      rw [inv_div]
      linarith
    exact (inv_le_comm₀ (by positivity : 0 < (n : ℝ) + 1) hε').mpr hn'.le
  obtain ⟨C, hC, hb⟩ := hseq n (ε / 2) (half_pos hε)
  refine ⟨C, hC, ?_⟩
  intro M N hM hN
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hMN : 1 ≤ M * N := one_le_mul_of_one_le_of_one_le hM hN
  have hMNpos : 0 < M * N := zero_lt_one.trans_le hMN
  have hpow : N ^ δ ≤ (M * N) ^ (ε / 2) :=
    (Real.rpow_le_rpow_of_exponent_le hN hδ).trans
      (Real.rpow_le_rpow hNpos.le (le_mul_of_one_le_left hNpos.le hM) (half_pos hε).le)
  have hmajor : M + N ^ (1 + δ) ≤ (M * N) ^ (ε / 2) * (M + N) := by
    rw [Real.rpow_add hNpos, Real.rpow_one, mul_add]
    exact add_le_add (le_mul_of_one_le_left (zero_lt_one.trans_le hM).le
      (Real.one_le_rpow hMN (half_pos hε).le))
      (by simpa only [mul_comm N] using mul_le_mul_of_nonneg_left hpow hNpos.le)
  calc
    energy M N ≤ C * (M * N) ^ (ε / 2) * (M + N ^ (1 + δ)) := hb M N hM hN
    _ ≤ C * (M * N) ^ (ε / 2) * ((M * N) ^ (ε / 2) * (M + N)) :=
      mul_le_mul_of_nonneg_left hmajor (by positivity)
    _ = C * (M * N) ^ ε * (M + N ^ (1 : ℝ)) := by
      rw [Real.rpow_one, ← show (M * N) ^ (ε / 2) * (M * N) ^ (ε / 2) = (M * N) ^ ε by
        rw [← Real.rpow_add hMNpos, add_halves]]
      ac_rfl

end ArtinMatthews
