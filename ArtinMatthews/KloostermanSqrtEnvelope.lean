module

public import OAI.NumberTheory.Jacobsthal.Estimates.ScalarErrorBudget


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine square-root and gcd envelope, with exact CRT and common-frequency scaling. -/
noncomputable section
open OAI.Erdos970.ErdosKloosterman
namespace ArtinMatthews.PrimePowerWeil

def sqrtEnvelope (N : ℕ) (h k : ℤ) : ℝ :=
  (N.divisors.card:ℝ)^3*Real.sqrt N*Real.sqrt (frequencyGcd N h k)

theorem sqrtEnvelope_nonneg (N : ℕ) (h k : ℤ) : 0≤sqrtEnvelope N h k := by
  unfold sqrtEnvelope
  positivity

theorem sqrtEnvelope_coprime_mul (m n : ℕ) (hmn : m.Coprime n) (h k : ℤ) :
    sqrtEnvelope (m*n) h k=sqrtEnvelope m h k*sqrtEnvelope n h k := by
  unfold sqrtEnvelope
  rw [hmn.card_divisors_mul,frequencyGcd_coprime_mul m n hmn]
  push_cast
  rw [Real.sqrt_mul (Nat.cast_nonneg m),Real.sqrt_mul (Nat.cast_nonneg _)]
  ring

theorem sqrtEnvelope_scale (N : ℕ) (c A B h k : ℤ) (hab : (N:ℤ)*A+c*B=1) :
    sqrtEnvelope N (c*h) (c*k)=sqrtEnvelope N h k := by
  unfold sqrtEnvelope
  rw [frequencyGcd_scale N c A B h k hab]

theorem sqrtEnvelope_crt_scaled (m n : ℕ) (hmn : m.Coprime n) (h k : ℤ) :
    sqrtEnvelope m (Nat.gcdB m n*h) (Nat.gcdB m n*k)*
      sqrtEnvelope n (Nat.gcdA m n*h) (Nat.gcdA m n*k)=sqrtEnvelope (m*n) h k := by
  have hab : (m:ℤ)*Nat.gcdA m n+(n:ℤ)*Nat.gcdB m n=1 := by
    rw [← Nat.gcd_eq_gcd_ab,hmn.gcd_eq_one]
    rfl
  rw [sqrtEnvelope_scale m (Nat.gcdB m n) (Nat.gcdA m n) n h k (by nlinarith [hab]),
    sqrtEnvelope_scale n (Nat.gcdA m n) (Nat.gcdB m n) m h k (by nlinarith [hab]),
    sqrtEnvelope_coprime_mul m n hmn]

theorem sqrtEnvelope_one (h k : ℤ) : sqrtEnvelope 1 h k=1 := by
  simp [sqrtEnvelope,frequencyGcd]

theorem sqrtEnvelope_prime_power (p a : ℕ) [Fact p.Prime] (h k : ℤ) :
    sqrtEnvelope (p^a) h k=((a+1:ℕ):ℝ)^3*Real.sqrt ((p^a:ℕ):ℝ)*
      Real.sqrt ((Nat.gcd (p^a) (Int.gcd h k):ℕ):ℝ) := by
  have hc : (p^a).divisors.card=a+1 := by
    rw [← ArithmeticFunction.sigma_zero_apply,ArithmeticFunction.sigma_zero_apply_prime_pow (Fact.out : p.Prime)]
  simp only [sqrtEnvelope,frequencyGcd,hc]

theorem sqrtEnvelope_ge_primitive (p a : ℕ) [Fact p.Prime] (ha : 0<a) (h k : ℤ) :
    8*Real.sqrt ((p^a:ℕ):ℝ)≤sqrtEnvelope (p^a) h k := by
  have hg : 0<Nat.gcd (p^a) (Int.gcd h k) := Nat.gcd_pos_of_pos_left _
    (pow_pos (Fact.out : p.Prime).pos a)
  have hg1 : (1:ℝ)≤((Nat.gcd (p^a) (Int.gcd h k):ℕ):ℝ) := by exact_mod_cast hg
  have hgsqrt : 1≤Real.sqrt ((Nat.gcd (p^a) (Int.gcd h k):ℕ):ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hg1
  have hc : (8:ℝ)≤((a+1:ℕ):ℝ)^3 := by
    have ha2 : (2:ℝ)≤((a+1:ℕ):ℝ) := by exact_mod_cast (by omega : 2≤a+1)
    exact (by norm_num : (8:ℝ)=(2:ℝ)^3).le.trans (pow_le_pow_left₀ (by norm_num) ha2 3)
  rw [sqrtEnvelope_prime_power]
  exact (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)).trans
    (le_mul_of_one_le_right (by positivity) hgsqrt)

theorem sqrt_half_scale (p Q g : ℝ) (hp : 0≤p) :
    p*(Real.sqrt Q*Real.sqrt g)=Real.sqrt (p*Q)*Real.sqrt (p*g) := by
  rw [Real.sqrt_mul hp,Real.sqrt_mul hp]
  have hs : Real.sqrt p*Real.sqrt p=p := Real.mul_self_sqrt hp
  calc
    _ = (Real.sqrt p*Real.sqrt p)*(Real.sqrt Q*Real.sqrt g) := by rw [hs]
    _ = _ := by ring

theorem sqrtEnvelope_common_frequency_scale (p a : ℕ) [Fact p.Prime] (h k : ℤ) :
    (p:ℝ)*sqrtEnvelope (p^a) h k≤sqrtEnvelope (p^(a+1)) ((p:ℤ)*h) ((p:ℤ)*k) := by
  have hc : ((a+1:ℕ):ℝ)^3≤((a+1+1:ℕ):ℝ)^3 :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.le_succ (a+1)) 3
  rw [sqrtEnvelope_prime_power,sqrtEnvelope_prime_power,
    OAI.Erdos970.ErdosKloosterman.PrimePower.common_frequency_gcd,pow_succ' p a,Nat.cast_mul,Nat.cast_mul]
  calc
    _ = ((a+1:ℕ):ℝ)^3*((p:ℝ)*(Real.sqrt ((p^a:ℕ):ℝ)*
        Real.sqrt ((Nat.gcd (p^a) (Int.gcd h k):ℕ):ℝ))) := by ring
    _ = _ := by rw [sqrt_half_scale _ _ _ (Nat.cast_nonneg p)]
    _ ≤ ((a+1+1:ℕ):ℝ)^3*(Real.sqrt ((p:ℝ)*((p^a:ℕ):ℝ))*
        Real.sqrt ((p:ℝ)*((Nat.gcd (p^a) (Int.gcd h k):ℕ):ℝ))) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

end ArtinMatthews.PrimePowerWeil
