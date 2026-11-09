module

public import PrimeNumberTheoremAnd.IEANTN.Mertens
public import Mathlib.NumberTheory.SumPrimeReciprocals
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! The actual small-prime Euler product used by the positive sieve.
The pinned Mertens theorem supplies both the explicit logarithmic upper
bound and the normalized limiting constant, including a real power cutoff. -/

namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

noncomputable def markedSieveEulerProduct (y : ℝ) : ℝ :=
  ∏ p ∈ Nat.primesLE ⌊y⌋₊, (1 - 1 / (p : ℝ))

theorem markedSieveEulerProduct_pos (y : ℝ) : 0 < markedSieveEulerProduct y := by
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
  exact sub_pos.mpr ((div_lt_one (by linarith)).mpr hp1)

/-- Mertens' exact remainder identity, with the cutoff written as `primesLE`. -/
theorem markedSieveEulerProduct_eq {y : ℝ} (hy : 1 < y) :
    markedSieveEulerProduct y =
      Real.exp (-Real.eulerMascheroniConstant) * Real.exp (Mertens.E₃ y) / Real.log y := by
  have hset : Nat.primesLE ⌊y⌋₊ = (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hp, hprime⟩
      exact ⟨⟨hprime.pos, hp⟩, hprime⟩
    · rintro ⟨⟨_, hp⟩, hprime⟩
      exact ⟨hp, hprime⟩
  unfold markedSieveEulerProduct
  rw [hset]
  exact Mertens.prod_one_minus_div_prime_eq hy

/-- The explicit upper constant follows once the genuine Mertens remainder
is at most one; its eventual smallness is proved in the imported library. -/
theorem markedSieveEulerProduct_upper_eventually :
    ∀ᶠ y : ℝ in atTop,
      markedSieveEulerProduct y ≤ Real.exp (1 - Real.eulerMascheroniConstant) / Real.log y := by
  have hE := (Asymptotics.isLittleO_one_iff ℝ).mp Mertens.E₃.bound'
  filter_upwards [hE.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (1 : ℝ)] with y hE hy
  rw [markedSieveEulerProduct_eq hy]
  apply div_le_div_of_nonneg_right _ (Real.log_pos hy).le
  calc
    _ ≤ Real.exp (-Real.eulerMascheroniConstant) * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hE.le) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The normalized Euler product has Mertens' exact positive constant. -/
theorem markedSieveEulerProduct_log_tendsto :
    Tendsto (fun y : ℝ => Real.log y * markedSieveEulerProduct y) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  have hE := (Asymptotics.isLittleO_one_iff ℝ).mp Mertens.E₃.bound'
  have h := hE.rexp.const_mul (Real.exp (-Real.eulerMascheroniConstant))
  simp only [Real.exp_zero, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
  rw [markedSieveEulerProduct_eq hy]
  field_simp [(Real.log_pos hy).ne']

/-- At cutoff `x^γ`, the logarithmic upper constant is divided by `γ`. -/
theorem markedSieveEulerProduct_power_upper_eventually {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop,
      markedSieveEulerProduct (x ^ γ) ≤
        (Real.exp (1 - Real.eulerMascheroniConstant) / γ) / Real.log x := by
  filter_upwards [(tendsto_rpow_atTop hγ).eventually markedSieveEulerProduct_upper_eventually,
    eventually_gt_atTop (0 : ℝ)] with x h hx
  rw [Real.log_rpow hx] at h
  convert h using 1
  ring

/-- The density constant at a real power cutoff, with the floor retained
inside the actual prime product. -/
theorem markedSieveEulerProduct_power_log_tendsto {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun x : ℝ => Real.log x * markedSieveEulerProduct (x ^ γ)) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant) / γ)) := by
  have h := (markedSieveEulerProduct_log_tendsto.comp (tendsto_rpow_atTop hγ)).div_const γ
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp only [Function.comp_def]
  rw [Real.log_rpow hx]
  field_simp

end ArtinMatthews
