module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import OAI.NumberTheory.DirichletL.PrimeCounting.AnnularPrimeMass
public import OAI.NumberTheory.DirichletL.PrimeCounting.PrimeMass


set_option backward.privateInPublic true
@[expose] public section

/-! Rational-prime supply on a fixed relative interval, from the checked
modulus-one prime logarithmic mass. The stated square-root count is
sufficient for the logarithmic scale enlargement. -/
namespace ArtinMatthews.QuadraticScale

open Filter ArithmeticFunction
open scoped BigOperators Topology

noncomputable section

def rationalPrimeBand (y z : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊z⌋₊).filter (fun p => y < (p : ℝ))

theorem mem_rationalPrimeBand {y z : ℝ} (hz : 0 ≤ z) {p : ℕ} :
    p ∈ rationalPrimeBand y z ↔ p.Prime ∧ y < (p : ℝ) ∧ (p : ℝ) ≤ z := by
  simp only [rationalPrimeBand, Finset.mem_filter, Nat.mem_primesLE, Nat.le_floor_iff hz]
  tauto

private def primeLogPrefix (x : ℝ) : ℝ := ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p

private def primeLogCoeff (n : ℕ) : ℝ :=
  if n.Prime then Real.log n else 0

private theorem primeLogPrefix_eq_cumulative (x : ℝ) :
    primeLogPrefix x = OAI.SevenEighths.PNT.AnnularPrimeMass.cumulative primeLogCoeff x := by
  have hset : Nat.primesLE ⌊x⌋₊ = (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime := by
    ext n
    simp only [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  rw [primeLogPrefix, hset, Finset.sum_filter]
  rfl

private theorem primeLogCoeff_ratio :
    Tendsto (fun N : ℕ => cumsum primeLogCoeff N / N) atTop (𝓝 1) := by
  have h := OAI.SevenEighths.PNT.prime_residueClass_ratio_tendsto (1 : ZMod 1) isUnit_one
  have hc (n : ℕ) : (if n.Prime then vonMangoldt.residueClass (1 : ZMod 1) n else 0) =
      primeLogCoeff n := by
    unfold primeLogCoeff
    by_cases hn : n.Prime
    · rw [ite_eq_left hn, ite_eq_left hn]
      change Set.indicator {k : ℕ | (k : ZMod 1) = 1} vonMangoldt n = Real.log n
      rw [Set.indicator_of_mem (show n ∈ {k : ℕ | (k : ZMod 1) = 1} from Subsingleton.elim _ _)]
      exact vonMangoldt_apply_prime hn
    · simp [hn]
  simpa only [hc, Nat.totient_one, Nat.cast_one, inv_one] using h

private theorem rationalPrimeBand_logMass_eq {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z) :
    (∑ p ∈ rationalPrimeBand y z, Real.log p) = primeLogPrefix z - primeLogPrefix y := by
  have hsub : Nat.primesLE ⌊y⌋₊ ⊆ Nat.primesLE ⌊z⌋₊ := by
    intro p hp
    have h := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨h.1.trans (Nat.floor_mono hyz), h.2⟩
  have hset : rationalPrimeBand y z = Nat.primesLE ⌊z⌋₊ \ Nat.primesLE ⌊y⌋₊ := by
    ext p
    simp only [rationalPrimeBand, Finset.mem_filter, Finset.mem_sdiff, Nat.mem_primesLE,
      Nat.le_floor_iff hy, Nat.le_floor_iff (hy.trans hyz)]
    rw [← not_le]
    tauto
  rw [hset]
  have h := Finset.sum_sdiff (f := fun p : ℕ => Real.log p) hsub
  unfold primeLogPrefix
  linarith

theorem rationalPrimeBand_logMass_tendsto (b : ℝ) (hb : 1 ≤ b) :
    Tendsto (fun y : ℝ => (∑ p ∈ rationalPrimeBand y (b * y), Real.log p) / y)
      atTop (𝓝 (b - 1)) := by
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have h1 := OAI.SevenEighths.PNT.AnnularPrimeMass.scaledCumulative_tendsto
    primeLogCoeff_ratio hb0
  have h2 := OAI.SevenEighths.PNT.AnnularPrimeMass.scaledCumulative_tendsto
    primeLogCoeff_ratio (y := 1) zero_lt_one
  have h := h1.sub h2
  rw [one_mul, one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  rw [rationalPrimeBand_logMass_eq (zero_le_one.trans hy) (le_mul_of_one_le_left (zero_le_one.trans hy) hb),
    primeLogPrefix_eq_cumulative, primeLogPrefix_eq_cumulative, sub_div]
  simp [OAI.SevenEighths.PNT.AnnularPrimeMass.scaledCumulative, mul_comm y b]

theorem rationalPrimeBand_card_eventually (b : ℝ) (hb : 1 < b) :
    ∀ᶠ y : ℝ in atTop, y ^ (1 / 2 : ℝ) ≤ ((rationalPrimeBand y (b * y)).card : ℝ) := by
  let c := (b - 1) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hmass : ∀ᶠ y : ℝ in atTop,
      c < (∑ p ∈ rationalPrimeBand y (b * y), Real.log p) / y :=
    (rationalPrimeBand_logMass_tendsto b hb.le).eventually
      (Ioi_mem_nhds (show c < b - 1 by dsimp [c]; linarith))
  have hlog : ∀ᶠ y : ℝ in atTop, Real.log (b * y) ≤ c * y ^ (1 / 2 : ℝ) := by
    have h := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).bound
      (show 0 < c / b ^ (1 / 2 : ℝ) by positivity [hc, hb])
    have ht : Tendsto (fun y : ℝ => b * y) atTop atTop :=
      tendsto_id.const_mul_atTop (lt_of_lt_of_le zero_lt_one hb.le)
    filter_upwards [ht.eventually h, eventually_ge_atTop (1 : ℝ)] with y hy hpos
    have hbp : 0 < b ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have hy0 : 0 ≤ y := zero_le_one.trans hpos
    have hnorm : |Real.log (b * y)| ≤ (c / b ^ (1 / 2 : ℝ)) * (b * y) ^ (1 / 2 : ℝ) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg
        (Real.rpow_nonneg (mul_nonneg (by linarith : 0 ≤ b) hy0) _)] using hy
    calc
      _ ≤ |Real.log (b * y)| := le_abs_self _
      _ ≤ _ := hnorm
      _ = _ := by
        rw [Real.mul_rpow (by linarith : 0 ≤ b) hy0, ← mul_assoc, div_mul_cancel₀ _ hbp.ne']
  filter_upwards [hmass, hlog, eventually_ge_atTop (1 : ℝ)] with y hmass hlog hy
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hb0 : 0 < b := by linarith
  let P := rationalPrimeBand y (b * y)
  have hbound : (∑ p ∈ P, Real.log p) ≤ P.card * Real.log (b * y) := by
    calc
      _ ≤ ∑ _p ∈ P, Real.log (b * y) := by
        apply Finset.sum_le_sum
        intro p hp
        have h := (mem_rationalPrimeBand (mul_nonneg hb0.le hy0.le)).mp hp
        exact Real.log_le_log (by exact_mod_cast h.1.pos) h.2.2
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hmain := ((lt_div_iff₀ hy0).mp hmass).le.trans
    (hbound.trans (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)))
  have hyhalf : 0 < y ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hy0 _
  have hyprod : y ^ (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ) = y := by
    rw [← Real.rpow_add hy0, add_halves, Real.rpow_one]
  apply (le_of_mul_le_mul_right _ (mul_pos hc hyhalf))
  calc
    y ^ (1 / 2 : ℝ) * (c * y ^ (1 / 2 : ℝ)) = c * y := by
      calc
        _ = c * (y ^ (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ)) := by ring
        _ = _ := congrArg (c * ·) hyprod
    _ ≤ _ := hmain

end
end ArtinMatthews.QuadraticScale
