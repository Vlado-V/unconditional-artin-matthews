module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! The top-down prime blocks of Section 7. Their index is computed from
the exact logarithmic ratio, with the original open lower and closed upper
endpoints. -/

noncomputable section
namespace ArtinMatthews

def cubicSieveBlockIndex (z : ℝ) (p : ℕ) : ℕ :=
  Nat.log 2 ⌊Real.log z / Real.log (p : ℝ)⌋₊

def cubicSieveBlockIndices (z : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊z⌋₊).image (cubicSieveBlockIndex z)

def cubicSieveBlock (z : ℝ) (j : ℕ) : Finset ℕ :=
  (Nat.primesLE ⌊z⌋₊).filter (fun p => cubicSieveBlockIndex z p = j)

theorem cubicSieveBlock_disjoint (z : ℝ) : Pairwise fun i j =>
    Disjoint (cubicSieveBlock z i) (cubicSieveBlock z j) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact hij ((Finset.mem_filter.mp hp).2.symm.trans (Finset.mem_filter.mp hq).2)

theorem cubicSieveBlock_union (z : ℝ) :
    (cubicSieveBlockIndices z).biUnion (cubicSieveBlock z) = Nat.primesLE ⌊z⌋₊ := by
  ext p
  constructor
  · intro hp
    obtain ⟨j, _hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_filter.mp hpj).1
  · intro hp
    exact Finset.mem_biUnion.mpr ⟨cubicSieveBlockIndex z p,
      Finset.mem_image.mpr ⟨p, hp, rfl⟩, Finset.mem_filter.mpr ⟨hp, rfl⟩⟩

theorem cubicSieveBlockIndices_mem_iff (z : ℝ) (j : ℕ) :
    j ∈ cubicSieveBlockIndices z ↔ (cubicSieveBlock z j).Nonempty := by
  unfold cubicSieveBlockIndices cubicSieveBlock
  simp only [Finset.mem_image, Finset.Nonempty, Finset.mem_filter]

private theorem cubicSieve_log_floor_index_iff {t : ℝ} (ht : 1 ≤ t) (j : ℕ) :
    Nat.log 2 ⌊t⌋₊ = j ↔ (2 : ℝ) ^ j ≤ t ∧ t < (2 : ℝ) ^ (j + 1) := by
  have hpos : 0 < ⌊t⌋₊ := Nat.le_floor (n := 1) (by simpa only [Nat.cast_one] using ht)
  have ht₀ := zero_le_one.trans ht
  rw [Nat.log_eq_iff (Or.inr ⟨by decide, hpos.ne'⟩), Nat.le_floor_iff ht₀, Nat.floor_lt ht₀]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

private theorem cubicSieveBlockIndex_iff {z : ℝ} (hz : 1 < z) {p j : ℕ}
    (hp : p.Prime) (hpz : (p : ℝ) ≤ z) :
    cubicSieveBlockIndex z p = j ↔
      z ^ ((1 / 2 : ℝ) ^ (j + 1)) < (p : ℝ) ∧ (p : ℝ) ≤ z ^ ((1 / 2 : ℝ) ^ j) := by
  have hz₀ := zero_lt_one.trans hz
  have hp₁ : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp₀ := zero_lt_one.trans hp₁
  have hlogp := Real.log_pos hp₁
  let t := Real.log z / Real.log (p : ℝ)
  have ht : 1 ≤ t := (le_div_iff₀ hlogp).mpr
    (by simpa only [one_mul] using Real.log_le_log hp₀ hpz)
  have hpow (k : ℕ) : (1 / 2 : ℝ) ^ k * Real.log z = Real.log z / (2 : ℝ) ^ k := by
    rw [div_pow, one_pow, one_div_mul_eq_div]
  have hlow : z ^ ((1 / 2 : ℝ) ^ (j + 1)) < (p : ℝ) ↔ t < (2 : ℝ) ^ (j + 1) := by
    rw [← Real.log_lt_log_iff (Real.rpow_pos_of_pos hz₀ _) hp₀, Real.log_rpow hz₀,
      hpow, div_lt_iff₀ (by positivity : 0 < (2 : ℝ) ^ (j + 1))]
    dsimp only [t]
    rw [div_lt_iff₀ hlogp, mul_comm (Real.log (p : ℝ))]
  have hhigh : (p : ℝ) ≤ z ^ ((1 / 2 : ℝ) ^ j) ↔ (2 : ℝ) ^ j ≤ t := by
    rw [← Real.log_le_log_iff hp₀ (Real.rpow_pos_of_pos hz₀ _), Real.log_rpow hz₀,
      hpow, le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ j)]
    dsimp only [t]
    rw [le_div_iff₀ hlogp, mul_comm (Real.log (p : ℝ))]
  change Nat.log 2 ⌊t⌋₊ = j ↔ _
  rw [cubicSieve_log_floor_index_iff ht, hlow, hhigh, and_comm]

theorem mem_cubicSieveBlock {z : ℝ} (hz : 1 < z) {j p : ℕ} :
    p ∈ cubicSieveBlock z j ↔
      p.Prime ∧ z ^ ((1 / 2 : ℝ) ^ (j + 1)) < (p : ℝ) ∧ (p : ℝ) ≤ z ^ ((1 / 2 : ℝ) ^ j) := by
  constructor
  · intro hp
    obtain ⟨hP, hidx⟩ := Finset.mem_filter.mp hp
    obtain ⟨hcap, hprime⟩ := Nat.mem_primesLE.mp hP
    have hpz : (p : ℝ) ≤ z :=
      (Nat.cast_le.mpr hcap).trans (Nat.floor_le (zero_le_one.trans hz.le))
    exact ⟨hprime, (cubicSieveBlockIndex_iff hz hprime hpz).mp hidx⟩
  · rintro ⟨hprime, hlo, hhi⟩
    have he : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hpz : (p : ℝ) ≤ z := hhi.trans
      ((Real.rpow_le_rpow_of_exponent_le hz.le he).trans_eq (Real.rpow_one z))
    exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hpz, hprime⟩,
      (cubicSieveBlockIndex_iff hz hprime hpz).mpr ⟨hlo, hhi⟩⟩

end ArtinMatthews
