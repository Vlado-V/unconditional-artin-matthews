module

public import ArtinMatthews.GiantSignedSourceTiltedAtom


set_option backward.privateInPublic true
@[expose] public section

/-! The sharp tilted mass used in the original chronological birth rows.
Its initial power stays bounded at the actual number of big active slots. -/
namespace ArtinMatthews
open Filter
noncomputable section

def giantSignedSourceConditionalMass (c x : ℝ) : ℝ :=
  (1 - ((giantTwoSidedSourceMomentLength x + 1 : ℕ) : ℝ) /
    Real.exp ((Real.log x)^c))⁻¹

theorem giantSignedSourceInitialConditionalMass_eventually
    {q c C₀ vmin : ℝ} (k ell : ℕ) (hM : 1 ≤ k+ell)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : 0 < c) (hC₀ : 0 ≤ C₀)
    (hvmin : 0 < vmin) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (B : Type*) [Fintype B] (PB : B → Finset ℕ),
        (∀ g, vmin ≤ bandReciprocalMass (PB g)) →
        (∀ g (p : PB g), Real.exp ((Real.log x)^c) ≤ (p.val : ℝ)) →
        (Fintype.card B : ℝ) ≤ C₀ * Real.log (Real.log x) →
        let n := giantTwoSidedSourceMomentLength x
        let ν := fun g => giantSignedTiltedPrimeLaw (PB g) (giantSignedSourceVisitQ q n)
        let mass := giantSignedSourceConditionalMass c x
        1 ≤ mass ∧ mass ≤ 2 ∧ mass^(Fintype.card B*(k+ell)) ≤ 2 ∧
        (∀ g p, 0 ≤ ν g p) ∧ (∀ g, (∑ p : PB g, ν g p) ≤ mass) ∧
        (∀ g p, ν g p ≤ (2/vmin)/Real.exp ((Real.log x)^c)) := by
  have hb := Real.tendsto_log_atTop.eventually
    (giantSignedResidualBudget_eventually 1 c 0 (C₀+1) 2 0 0 k ell zero_lt_one hc (by linarith))
  filter_upwards [hb, Real.tendsto_log_atTop.eventually (eventually_ge_atTop (5 : ℝ)),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))] with x hbudget hL5 hlogL
  intro B _ PB hVB hp hgroups
  let L := Real.log x
  let n := giantTwoSidedSourceMomentLength x
  let Pmin := Real.exp (L^c)
  let ε := ((n+1 : ℕ) : ℝ)/Pmin
  let visitQ := giantSignedSourceVisitQ q n
  let ν := fun g => giantSignedTiltedPrimeLaw (PB g) visitQ
  let dim := Fintype.card B*(k+ell)
  have hL1 : 1 ≤ L := by change 5 ≤ L at hL5; linarith
  have hPmin : 0 < Pmin := Real.exp_pos _
  have hε : 0 ≤ ε := div_nonneg (Nat.cast_nonneg _) hPmin.le
  have hn : ((n+1 : ℕ) : ℝ) ≤ L^(2 : ℝ) := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hL1 (show (13/25 : ℝ) ≤ 1 by norm_num)
    rw [Real.rpow_one] at hpow
    have hlen := giantTwoSidedSourceMomentLength_le (x := x) hL1
    change (n : ℝ) ≤ 4*L^(13/25 : ℝ) at hlen
    rw [Nat.cast_add, Nat.cast_one, Real.rpow_two]
    have h5 : 5 ≤ L := hL5
    nlinarith [mul_le_mul_of_nonneg_right h5 (zero_le_one.trans hL1)]
  have hg : ((Fintype.card B+1 : ℕ) : ℝ) ≤ (C₀+1)*Real.log L := by
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact add_le_add hgroups hlogL
  obtain ⟨hlen, _, hd, _⟩ := hbudget (Fintype.card B+1) (n+1) 0 hg hn (by simp)
  have hd' : (((Fintype.card B+1)*(k+ell) : ℕ) : ℝ)*ε ≤ 1/2 := hd
  have hhalf : ε ≤ 1/2 := by
    refine (le_mul_of_one_le_left hε ?_).trans hd'
    exact_mod_cast (Nat.mul_le_mul (Nat.succ_le_succ (Nat.zero_le (Fintype.card B))) hM)
  have hdim : (dim : ℝ)*ε ≤ 1/2 := by
    refine (mul_le_mul_of_nonneg_right ?_ hε).trans hd'
    exact_mod_cast (Nat.mul_le_mul_right (k+ell) (Nat.le_succ (Fintype.card B)))
  have hden : 0 < 1-ε := by linarith
  have hpow : (1/2 : ℝ) ≤ (1-ε)^dim := by
    rw [sub_eq_add_neg]
    exact (show (1/2 : ℝ) ≤ 1+(dim : ℝ)*(-ε) by linarith).trans
      (one_add_mul_le_pow (show (-2 : ℝ) ≤ -ε by linarith) dim)
  have hqi0 (i : Fin (n+1)) : 0 ≤ visitQ i :=
    (giantSignedSourceVisitQ_bounds hq0 hq1 n i).1
  have hqi1 (i : Fin (n+1)) : visitQ i ≤ 1 := by
    have hs : Real.sqrt q ≤ 1 := by nlinarith [Real.sq_sqrt hq0, Real.sqrt_nonneg q]
    exact (giantSignedSourceVisitQ_bounds hq0 hq1 n i).2.trans hs
  change 1 ≤ (1-ε)⁻¹ ∧ (1-ε)⁻¹ ≤ 2 ∧ ((1-ε)⁻¹)^dim ≤ 2 ∧
    (∀ g p, 0 ≤ ν g p) ∧ (∀ g, (∑ p : PB g, ν g p) ≤ (1-ε)⁻¹) ∧
    (∀ g p, ν g p ≤ (2/vmin)/Pmin)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [← one_div]
    exact (le_div_iff₀ hden).mpr (by linarith)
  · rw [← one_div]
    exact (div_le_iff₀ hden).mpr (by linarith)
  · rw [inv_pow, ← one_div]
    exact (div_le_iff₀ (pow_pos hden _)).mpr (by linarith)
  · intro g p
    rw [show ν g p = markedHarmonicAtom (PB g) p * giantSignedPrimeDensity visitQ p.val
      from giantSignedTiltedPrimeLaw_eq (PB g) visitQ p]
    exact mul_nonneg (markedHarmonicAtom_nonneg (PB g) (hvmin.trans_le (hVB g)))
      (zero_le_one.trans (giantSignedPrimeDensity_band_bounds visitQ hqi0 hqi1 Pmin hPmin (hp g p) hlen).1)
  · intro g
    exact (giantSignedTiltedPrimeLaw_sum_bounds (PB g) visitQ (hvmin.trans_le (hVB g))
      hqi0 hqi1 Pmin hPmin (hp g) hlen).2
  · intro g p
    exact giantSignedTiltedPrimeLaw_atom_le (PB g) visitQ hqi0 hqi1 hvmin (hVB g)
      hPmin hhalf p (hp g p)

end
end ArtinMatthews
