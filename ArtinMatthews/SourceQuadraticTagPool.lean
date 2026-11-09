module

public import ArtinMatthews.QuadraticRationalPrimeBand
public import ArtinMatthews.SourceQuadraticRationalTags
public import ArtinMatthews.SourceQuadraticSupport


set_option backward.privateInPublic true
@[expose] public section

/-! The prime number theorem supplies the actual disjoint norm tags.
A fixed power of the logarithm pays for the degree of the field. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain VaryingKummerAnalytic QuadraticScale Filter
open scoped NumberField Classical BigOperators Topology

noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

local notation "P" => SourceExteriorPrime F S₀
local notation "d" => Module.finrank ℚ F
local notation "w" => sourceReflectionPrimeNorm F S₀

theorem sourceQuadraticTagPools_eventually :
    ∀ᶠ X : ℝ in atTop, ∃ pool : Finset (Finset P),
      (↑pool : Set (Finset P)).PairwiseDisjoint id ∧
      (∀ t ∈ pool, X ≤ supportNorm w t ∧ supportNorm w t ≤ (4 / 3) * X) ∧
      X ^ ((2 * d : ℕ) : ℝ)⁻¹ ≤ (pool.card : ℝ) := by
  have hd : 0 < (d : ℝ) := by exact_mod_cast (Module.finrank_pos : 0 < d)
  let b : ℝ := (4 / 3 : ℝ) ^ (d : ℝ)⁻¹
  have hb : 1 < b := Real.one_lt_rpow (by norm_num) (inv_pos.mpr hd)
  have hscale : Tendsto (fun X : ℝ => X ^ (d : ℝ)⁻¹) atTop atTop :=
    tendsto_rpow_atTop (inv_pos.mpr hd)
  filter_upwards [hscale.eventually (rationalPrimeBand_card_eventually b hb),
    hscale.eventually (eventually_gt_atTop (sourceQuadraticRationalCutoff F S₀ : ℝ)),
    eventually_ge_atTop (1 : ℝ)] with X hcard hcut hX
  let y := X ^ (d : ℝ)⁻¹
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hy : 0 ≤ y := Real.rpow_nonneg hX0 _
  have hby : 0 ≤ b * y := mul_nonneg (by linarith) hy
  let primes := rationalPrimeBand y (b * y)
  have hp (p : primes) : p.val.Prime ∧ y < (p.val : ℝ) ∧ (p.val : ℝ) ≤ b * y :=
    (mem_rationalPrimeBand hby).mp p.property
  have hpbig (p : primes) : sourceQuadraticRationalCutoff F S₀ < p.val :=
    Nat.cast_lt.mp (lt_trans hcut (hp p).2.1)
  let tag (p : primes) : Finset P :=
    (sourceQuadraticRationalTag F S₀ p.val (hp p).1 (hpbig p)).val.support
  have hnorm (p : primes) : supportNorm w (tag p) = (p.val : ℝ) ^ d := by
    let e := sourceQuadraticRationalTag F S₀ p.val (hp p).1 (hpbig p)
    change supportNorm w e.val.support = _
    rw [← sourceQuadraticActive_norm F S₀, sourceQuadraticActive_of_squarefree F S₀ e.property]
    change (sourcePrimeExponentNorm F S₀ (sourceQuadraticRationalTag F S₀ p.val (hp p).1
      (hpbig p)).val : ℝ) = _
    rw [sourceQuadraticRationalTag_norm, Nat.cast_pow]
  have htag : Function.Injective tag := by
    intro p r h
    apply Subtype.ext
    have he := congrArg (supportNorm w) h
    rw [hnorm, hnorm] at he
    have hd' : d ≠ 0 := by exact_mod_cast hd.ne'
    have hr := (pow_left_strictMonoOn₀ hd').injOn (Nat.cast_nonneg p.val : 0 ≤ (p.val : ℝ))
      (Nat.cast_nonneg r.val : 0 ≤ (r.val : ℝ)) he
    exact_mod_cast hr
  let em : primes ↪ Finset P := ⟨tag, htag⟩
  let pool : Finset (Finset P) := Finset.univ.map em
  have hpoolcard : pool.card = primes.card := by
    simp [pool]
  refine ⟨pool, ?_, ?_, ?_⟩
  · intro t ht u hu hne
    obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp (show t ∈ pool from ht)
    obtain ⟨r, _, rfl⟩ := Finset.mem_map.mp (show u ∈ pool from hu)
    have hpr : p.val ≠ r.val := fun h => hne (congrArg em (Subtype.ext h))
    exact sourceQuadraticRationalTag_support_disjoint F S₀ (hp p).1 (hp r).1
      (hpbig p) (hpbig r) hpr
  · intro t ht
    obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp ht
    change X ≤ supportNorm w (tag p) ∧ supportNorm w (tag p) ≤ (4 / 3) * X
    rw [hnorm p]
    have hY : y ^ d = X := by
      dsimp [y]
      rw [← Real.rpow_natCast, Real.rpow_inv_rpow hX0 hd.ne']
    have hB : b ^ d = (4 / 3 : ℝ) := by
      dsimp [b]
      rw [← Real.rpow_natCast, Real.rpow_inv_rpow (by norm_num) hd.ne']
    refine ⟨hY ▸ pow_le_pow_left₀ hy (hp p).2.1.le _, ?_⟩
    calc
      _ ≤ (b * y) ^ d := pow_le_pow_left₀ (Nat.cast_nonneg _) (hp p).2.2 _
      _ = _ := by rw [mul_pow, hB, hY]
  · rw [hpoolcard]
    have hpow : y ^ (1 / 2 : ℝ) = X ^ ((2 * d : ℕ) : ℝ)⁻¹ := by
      dsimp [y]
      rw [← Real.rpow_mul hX0]
      congr 1
      push_cast
      field_simp
    rw [← hpow]
    exact hcard

theorem exists_sourceQuadraticTagPool :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ M N X : ℝ, 1 ≤ M → 1 ≤ N →
      A * (1 + Real.log (M * N)) ^ (2 * d : ℕ) ≤ X →
      ∃ pool : Finset (Finset P), AnnularTagPool w X M N pool := by
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp (sourceQuadraticTagPools_eventually F S₀)
  let k := 2 * d
  let A := max 1 (max X₀ ((4 / Real.log 2) ^ k))
  have hk : 0 < (k : ℝ) := by
    have hd : 0 < d := Module.finrank_pos
    exact_mod_cast (show 0 < k by dsimp [k]; omega)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 1 ≤ A := le_max_left _ _
  refine ⟨A, hA, ?_⟩
  intro M N X hM hN hX
  let U := 1 + Real.log (M * N)
  have hMN : 1 ≤ M * N := one_le_mul_of_one_le_of_one_le hM hN
  have hU : 1 ≤ U := by dsimp [U]; linarith [Real.log_nonneg hMN]
  have hA' : A ≤ X :=
    (le_mul_of_one_le_right (zero_le_one.trans hA) (one_le_pow₀ hU)).trans hX
  have hX1 : 1 ≤ X := hA.trans hA'
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hcut : X₀ ≤ X := (le_max_left _ _).trans ((le_max_right _ _).trans hA')
  obtain ⟨pool, hd, hscale, hcard⟩ := hX₀ X hcut
  have hcard0 : (0 : ℝ) < pool.card :=
    (Real.rpow_pos_of_pos hXpos _).trans_le hcard
  have hbase : (4 / Real.log 2) ^ k ≤ A :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hpow : (4 / Real.log 2 * U) ^ k ≤ X := by
    rw [mul_pow]
    exact (mul_le_mul_of_nonneg_right hbase (by positivity)).trans hX
  have hroot : 4 / Real.log 2 * U ≤ X ^ (k : ℝ)⁻¹ :=
    (Real.le_rpow_inv_iff_of_pos (by positivity) hXpos.le hk).mpr (by
      simpa only [Real.rpow_natCast] using hpow)
  have hmass := mul_le_mul_of_nonneg_right (hroot.trans hcard) hl2.le
  have hfactor : (4 / Real.log 2 * U) * Real.log 2 = 4 * U := by
    rw [mul_right_comm, div_mul_cancel₀ _ hl2.ne']
  rw [hfactor] at hmass
  have hlog : Real.log (2 * (M * N)) ≤ U := by
    rw [Real.log_mul (by norm_num) (lt_of_lt_of_le zero_lt_one hMN).ne']
    have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ))
    dsimp [U]
    linarith
  exact ⟨pool, Finset.card_pos.mp (by exact_mod_cast hcard0), hd, hscale,
    (mul_le_mul_of_nonneg_left hlog (by norm_num)).trans hmass⟩

end
end ArtinMatthews.SourceEulerAssembly
