module

public import ArtinMatthews.GiantSignedSmallOmissions
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Algebra.Order.Floor.Ring


set_option backward.privateInPublic true
@[expose] public section

/-! The original quadratic memory limit and the final fixed copied-slot
choice give the stated rare-transfer scalar saving. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

def giantSignedSourceMemoryLimit (L : ℝ) : ℕ := ⌈L ^ 2⌉₊

theorem giantSignedSourceMemoryLimit_le {L : ℝ} (hL : 1 ≤ L) :
    (giantSignedSourceMemoryLimit L : ℝ) ≤ 2 * L ^ 2 := by
  have hceil := Nat.ceil_lt_add_one (sq_nonneg L)
  have hs : 1 ≤ L ^ 2 := by nlinarith
  exact hceil.le.trans (by nlinarith)

theorem giantSignedCopied_choose_lower (kCopy ell : ℕ) (hell : 0 < ell) :
    kCopy + 1 ≤ (kCopy + ell).choose ell := by
  have h := Nat.choose_le_choose kCopy (show kCopy + 1 ≤ kCopy + ell by omega)
  rw [Nat.choose_symm_add (a := kCopy) (b := 1),
    Nat.choose_symm_add (a := kCopy) (b := ell), Nat.choose_one_right] at h
  exact h

theorem giantSignedCopied_log_gap_exists (c₀ Cₐ G : ℝ) (hc₀ : 0 < c₀)
    (ell : ℕ) (hell : 0 < ell) :
    ∃ k₀ : ℕ, ∀ kCopy ≥ k₀,
      Cₐ + G + 3 ≤ c₀ / 2 * Real.log ((kCopy + ell).choose ell : ℝ) := by
  let R := 2 * (Cₐ + G + 3) / c₀
  refine ⟨⌈Real.exp R⌉₊, ?_⟩
  intro kCopy hk
  have hchoose : Real.exp R ≤ ((kCopy + ell).choose ell : ℝ) := calc
    Real.exp R ≤ (⌈Real.exp R⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (kCopy : ℝ) := by exact_mod_cast hk
    _ ≤ ((kCopy + ell).choose ell : ℝ) := by
      exact_mod_cast (Nat.le_succ kCopy).trans (giantSignedCopied_choose_lower kCopy ell hell)
  have hlog := Real.log_le_log (Real.exp_pos R) hchoose
  rw [Real.log_exp] at hlog
  have h := (div_le_iff₀ hc₀).mp hlog
  nlinarith

theorem giantSignedSourceOmissionGain_of_log_gap
    {S : Type*} [Fintype S] (kCopy ell : ℕ) (c₀ Cₐ G L : ℝ)
    (hL : 3 ≤ L)
    (hgroups : c₀ * Real.log L ≤ (Fintype.card S : ℝ))
    (hgap : Cₐ + G + 3 ≤ c₀ / 2 * Real.log ((kCopy + ell).choose ell : ℝ)) :
    2 * L ^ Cₐ * Real.sqrt
        ((giantSignedSourceMemoryLimit L : ℝ) /
          (giantSignedSmallOmissionNumber S (kCopy+ell) ell : ℝ)) ≤
      (1 / 2 : ℝ) * L ^ (-G) := by
  let C : ℝ := ((kCopy + ell).choose ell : ℕ)
  let A := c₀ / 2 * Real.log C
  let D : ℝ := (giantSignedSmallOmissionNumber S (kCopy+ell) ell : ℕ)
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hC1 : 1 ≤ C := by
    change (1 : ℝ) ≤ ((kCopy + ell).choose ell : ℝ)
    exact_mod_cast (Nat.succ_le_of_lt (Nat.choose_pos (show ell ≤ kCopy+ell by omega)))
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC1
  have hD0 : 0 < D := by
    change (0 : ℝ) < (giantSignedSmallOmissionNumber S (kCopy+ell) ell : ℝ)
    exact_mod_cast (giantSignedSmallOmissionNumber_pos S kCopy ell)
  have hlogD : 2 * A * Real.log L ≤ Real.log D := by
    have h := mul_le_mul_of_nonneg_right hgroups hlogC
    dsimp [D, giantSignedSmallOmissionNumber]
    rw [Nat.cast_pow, Real.log_pow]
    calc
      2 * A * Real.log L = (c₀ * Real.log L) * Real.log C := by dsimp [A]; ring
      _ ≤ _ := h
  have hpowD : L ^ (2 * A) ≤ D := by
    apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hL0 _) hD0).mp
    rw [Real.log_rpow hL0]
    exact hlogD
  have hden : L ^ A ≤ Real.sqrt D := by
    have h := Real.sqrt_le_sqrt hpowD
    have he : L ^ (2 * A) = (L ^ A) ^ (2 : ℕ) := by
      calc
        _ = L ^ (A * (2 : ℕ)) := by congr 1; norm_num; ring
        _ = _ := Real.rpow_mul_natCast hL0.le A 2
    rw [he, Real.sqrt_sq (Real.rpow_nonneg hL0.le A)] at h
    exact h
  have hnum : Real.sqrt (giantSignedSourceMemoryLimit L : ℝ) ≤ 2 * L := by
    have hbound := giantSignedSourceMemoryLimit_le hL1
    have hsq : (giantSignedSourceMemoryLimit L : ℝ) ≤ (2 * L) ^ 2 := by nlinarith
    simpa only [Real.sqrt_sq (by positivity : 0 ≤ 2 * L)] using Real.sqrt_le_sqrt hsq
  have hratio : Real.sqrt ((giantSignedSourceMemoryLimit L : ℝ) / D) ≤
      2 * L / L ^ A := by
    rw [Real.sqrt_div (Nat.cast_nonneg _) D]
    exact (div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg D)).trans
      (div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hL0 A) hden)
  change 2 * L ^ Cₐ * Real.sqrt ((giantSignedSourceMemoryLimit L : ℝ) / D) ≤ _
  calc
    _ ≤ 2 * L ^ Cₐ * (2 * L / L ^ A) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = 4 * L ^ (Cₐ + 1 - A) := by
      rw [Real.rpow_sub hL0, Real.rpow_add hL0, Real.rpow_one]
      ring
    _ ≤ 4 * L ^ (-G - 2) := by
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 ?_) (by norm_num)
      dsimp [A, C]
      linarith
    _ ≤ (1 / 2 : ℝ) * L ^ (-G) := by
      rw [Real.rpow_sub hL0, Real.rpow_two, ← mul_div_assoc]
      apply (div_le_iff₀ (sq_pos_of_pos hL0)).mpr
      have hs : 8 ≤ L ^ 2 := by nlinarith
      have hp : 0 ≤ L ^ (-G) := Real.rpow_nonneg hL0.le _
      nlinarith [mul_le_mul_of_nonneg_right hs hp]

theorem giantSignedSourceOmissionGain
    (c₀ Cₐ G : ℝ) (hc₀ : 0 < c₀) (ell : ℕ) (hell : 0 < ell) :
    ∃ k₀ : ℕ, ∀ kCopy ≥ k₀, ∀ (S : Type*) [Fintype S], ∀ L : ℝ,
      3 ≤ L → c₀ * Real.log L ≤ (Fintype.card S : ℝ) →
      2 * L ^ Cₐ * Real.sqrt
        ((giantSignedSourceMemoryLimit L : ℝ) /
          (giantSignedSmallOmissionNumber S (kCopy+ell) ell : ℝ)) ≤
        (1 / 2 : ℝ) * L ^ (-G) := by
  obtain ⟨k₀, hk₀⟩ := giantSignedCopied_log_gap_exists c₀ Cₐ G hc₀ ell hell
  refine ⟨k₀, ?_⟩
  intro kCopy hk S _ L hL hgroups
  exact giantSignedSourceOmissionGain_of_log_gap kCopy ell c₀ Cₐ G L hL hgroups
    (hk₀ kCopy hk)

end
end ArtinMatthews
