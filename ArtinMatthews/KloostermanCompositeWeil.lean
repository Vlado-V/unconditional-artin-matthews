module

public import ArtinMatthews.KloostermanPrimePowerWeil


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine CRT assembly of the square-root estimate at every nonzero modulus. -/
noncomputable section
open OAI.Erdos970.ErdosKloosterman
namespace ArtinMatthews.PrimePowerWeil

def SqrtBoundAt (N : ℕ) : Prop := ∀ [NeZero N] (h k : ℤ),
  ‖standardSum N h k‖ ≤ sqrtEnvelope N h k

theorem sqrtBoundAt_zero : SqrtBoundAt 0 := by
  intro h0 h k
  exact False.elim (NeZero.ne 0 rfl)

theorem sqrtBoundAt_one : SqrtBoundAt 1 := by
  intro _ h k
  simp [standardSum_one,sqrtEnvelope_one]

theorem sqrtBoundAt_coprime (m n : ℕ) (hm : 1 < m) (hn : 1 < n) (hmn : m.Coprime n)
    (hbm : SqrtBoundAt m) (hbn : SqrtBoundAt n) : SqrtBoundAt (m*n) := by
  let : NeZero m := ⟨by omega⟩
  let : NeZero n := ⟨by omega⟩
  intro _ h k
  rw [norm_standardSum_crt m n hmn]
  calc
    _ ≤ sqrtEnvelope m (Nat.gcdB m n*h) (Nat.gcdB m n*k)*
        sqrtEnvelope n (Nat.gcdA m n*h) (Nat.gcdA m n*k) :=
      mul_le_mul (hbm _ _) (hbn _ _) (norm_nonneg _) (sqrtEnvelope_nonneg _ _ _)
    _ = _ := sqrtEnvelope_crt_scaled m n hmn h k

theorem sqrtBoundAt_prime_power (p a : ℕ) (hp : p.Prime) (ha : 0 < a) : SqrtBoundAt (p^a) := by
  let : Fact p.Prime := ⟨hp⟩
  intro _ h k
  exact standardSum_prime_power_sqrtEnvelope p a ha h k

theorem sqrtBoundAt_all : ∀ N : ℕ, SqrtBoundAt N :=
  Nat.recOnPosPrimePosCoprime sqrtBoundAt_prime_power sqrtBoundAt_zero sqrtBoundAt_one sqrtBoundAt_coprime

theorem standardSum_weil_divisor_bound (N : ℕ) [NeZero N] (h k : ℤ) :
    ‖standardSum N h k‖ ≤ (N.divisors.card:ℝ)^3*Real.sqrt N*
      Real.sqrt ((Nat.gcd N (Int.gcd h k):ℕ):ℝ) :=
  sqrtBoundAt_all N h k

end ArtinMatthews.PrimePowerWeil
