module

public import ArtinMatthews.MarkedMajorArcLinearPhase
public import OAI.NumberTheory.JointDickman.Analysis.CharacterFourierExpansion


set_option backward.privateInPublic true
@[expose] public section

/-! Logarithmic phase sums with arbitrary bounded residue restrictions. -/

namespace ArtinMatthews

open Finset Filter OAI.JointDickman OAI.Problem337
open scoped Topology

noncomputable section

private def periodicFourierCoefficient {q : ℕ} [NeZero q]
    (w : ZMod q → ℂ) (k : ZMod q) : ℂ :=
  (q:ℂ)⁻¹ * ZMod.dft w k

private theorem periodicFourierCoefficient_norm_le {q : ℕ} [NeZero q]
    (w : ZMod q → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1) (k : ZMod q) :
    ‖periodicFourierCoefficient w k‖ ≤ 1 := by
  have hsum : ‖ZMod.dft w k‖ ≤ (q:ℝ) := by
    rw [ZMod.dft_apply]
    calc
      _ ≤ ∑ n : ZMod q, ‖ZMod.stdAddChar (-(n*k)) • w n‖ := norm_sum_le _ _
      _ ≤ ∑ _n : ZMod q, (1:ℝ) := by
        apply sum_le_sum
        intro n _
        simpa [smul_eq_mul, norm_mul, ZMod.stdAddChar_apply] using hw n
      _ = q := by simp
  rw [periodicFourierCoefficient, norm_mul, norm_inv, Complex.norm_natCast]
  have hq : 0 < (q:ℝ) := by exact_mod_cast NeZero.pos q
  exact (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hq.le)).trans_eq
    (inv_mul_cancel₀ hq.ne')

private theorem periodic_fourier_expansion {q : ℕ} [NeZero q]
    (w : ZMod q → ℂ) (n : ZMod q) :
    w n = ∑ k : ZMod q, periodicFourierCoefficient w k * ZMod.stdAddChar (k*n) := by
  have h := congrFun ((ZMod.dft (N := q) (E := ℂ)).symm_apply_apply w) n
  rw [ZMod.invDFT_apply] at h
  rw [←h, smul_eq_mul, mul_sum]
  apply sum_congr rfl
  intro k _
  simp only [periodicFourierCoefficient, smul_eq_mul]
  ring

private theorem periodic_log_phase_bound {q : ℕ} [NeZero q]
    (w : ZMod q → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1) (S : Finset ℕ) (Z K : ℝ)
    (hbound : ∀ k : ZMod q, ‖∑ n ∈ S, ExponentialSum.phase
      ((k.val:ℝ)/q*(n:ℝ)+Z*Real.log (n:ℝ))‖ ≤ K) :
    ‖∑ n ∈ S, w (n:ZMod q)*ExponentialSum.phase (Z*Real.log (n:ℝ))‖ ≤ (q:ℝ)*K := by
  have he : (∑ n ∈ S, w (n:ZMod q)*ExponentialSum.phase (Z*Real.log (n:ℝ))) =
      ∑ k : ZMod q, periodicFourierCoefficient w k *
        ∑ n ∈ S, ExponentialSum.phase ((k.val:ℝ)/q*(n:ℝ)+Z*Real.log (n:ℝ)) := by
    conv_lhs => arg 2; ext n; rw [periodic_fourier_expansion w (n:ZMod q), sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    rw [mul_sum]
    apply sum_congr rfl
    intro n _
    have hphase : ZMod.stdAddChar (k*(n:ZMod q)) =
        ExponentialSum.phase ((k.val:ℝ)/q*(n:ℝ)) := by
      simpa only [Int.cast_natCast, differencingPhase, ExponentialSum.phase] using
        stdAddChar_mul_int_as_phase k (n:ℤ)
    rw [hphase, ExponentialSum.phase_add, mul_assoc]
  rw [he]
  calc
    _ ≤ ∑ k : ZMod q, ‖periodicFourierCoefficient w k *
        ∑ n ∈ S, ExponentialSum.phase ((k.val:ℝ)/q*(n:ℝ)+Z*Real.log (n:ℝ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _k : ZMod q, K := by
      apply sum_le_sum
      intro k _
      rw [norm_mul]
      exact (mul_le_mul (periodicFourierCoefficient_norm_le w hw k) (hbound k)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = (q:ℝ)*K := by simp

private theorem rational_additive_log_phase_first_bound {q : ℕ} [NeZero q]
    (k : ZMod q) {U Z : ℝ} (hU : 1 ≤ U) (hZ : 0 < Z) (hZU : 4*(q:ℝ)*Z ≤ U)
    (l r : ℕ) (hl : U ≤ (l:ℝ)) (hr : (r:ℝ) ≤ 2*U) :
    ‖∑ n ∈ Icc l r, ExponentialSum.phase ((k.val:ℝ)/q*(n:ℝ)+Z*Real.log (n:ℝ))‖ ≤
      8*U/Z := by
  have hU0 : 0 < U := by linarith
  have hq : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
  have hk : (k.val:ℝ)+1 ≤ q := by exact_mod_cast k.val_lt
  let a : ℝ := (k.val:ℝ)/q
  let β : ℝ := Z/(4*U)
  let f : ℕ → ℝ := fun n => a*n+Z*Real.log (n:ℝ)
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a+1/(q:ℝ) ≤ 1 := by
    dsimp [a]
    rw [← add_div]
    exact (div_le_one hq).mpr hk
  have hβ : 0 < β := by dsimp [β]; positivity
  have hsmall : Z/U ≤ 1/(4*(q:ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0:ℝ) < 4*(q:ℝ))).mpr
    rw [div_mul_eq_mul_div, div_le_iff₀ hU0]
    linarith
  have hstep (n : ℕ) : f (n+1)-f n =
      a+Z*(Real.log ((n:ℝ)+1)-Real.log (n:ℝ)) := by
    simp only [f, Nat.cast_add, Nat.cast_one]
    ring
  have hd (i : ℕ) (hil : l ≤ i) (hir : i ≤ r) :
      β ≤ f (i+1)-f i ∧ f (i+1)-f i ≤ 1-β := by
    have hi : U ≤ (i:ℝ) := hl.trans (by exact_mod_cast hil)
    have hi2 : (i:ℝ) ≤ 2*U := (by exact_mod_cast hir : (i:ℝ) ≤ r).trans hr
    have hi0 : (0:ℝ) < i := hU0.trans_le hi
    obtain ⟨hlo, hhi⟩ := log_step_bounds hi0
    rw [hstep]
    constructor
    · have hb : β ≤ Z*((1:ℝ)/(i+1)) := by
        dsimp [β]
        rw [mul_one_div]
        exact div_le_div_of_nonneg_left hZ.le (by positivity) (by linarith)
      linarith [mul_le_mul_of_nonneg_left hlo hZ.le]
    · have hu : Z*((1:ℝ)/i) ≤ Z/U := by
        rw [mul_one_div]
        exact div_le_div_of_nonneg_left hZ.le hU0 hi
      have hb : β ≤ Z/U := by
        dsimp [β]
        exact div_le_div_of_nonneg_left hZ.le hU0 (by linarith)
      have hh : 2*(1/(4*(q:ℝ))) ≤ 1/(q:ℝ) := by
        rw [show (2:ℝ)*(1/(4*(q:ℝ))) = 1/(2*(q:ℝ)) by ring]
        exact div_le_div_of_nonneg_left zero_le_one hq (by linarith)
      linarith [mul_le_mul_of_nonneg_left hhi hZ.le]
  have hmono : AntitoneOn (fun i => f (i+1)-f i) (Set.Icc l r) := by
    intro i hi j _ hij
    change f (j+1)-f j ≤ f (i+1)-f i
    rw [hstep, hstep]
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ hZ.le
    exact log_step_antitone (hU0.trans_le (hl.trans (by exact_mod_cast hi.1)))
      (by exact_mod_cast hij)
  have hh := ExponentialSum.first_derivative_sum_bound_Icc f l r β 0 hβ
    (fun i hil hir => by simpa using (hd i hil hir).1)
    (fun i hil hir => by simpa using (hd i hil hir).2) (Or.inr hmono)
  change ‖∑ n ∈ Icc l r, ExponentialSum.phase (f n)‖ ≤ _
  exact hh.trans_eq (by dsimp [β]; field_simp; ring)

/-- The moderate-time progression sum has reciprocal, square-integrable
decay. It includes arbitrary bounded periodic restrictions and both signs. -/
theorem sourceComparisonPeriodic_phase_moderate {q : ℕ} [NeZero q]
    (w : ZMod q → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1) {U Z : ℝ} (hU : 1 ≤ U)
    (hZ : Z ≠ 0) (hZU : 4*(q:ℝ)*|Z| ≤ U)
    (l r : ℕ) (hl : U ≤ (l:ℝ)) (hr : (r:ℝ) ≤ 2*U) :
    ‖∑ n ∈ Icc l r, w (n:ZMod q)*ExponentialSum.phase (Z*Real.log (n:ℝ))‖ ≤
      (q:ℝ)*(8*U/|Z|) := by
  have hbound (v : ZMod q → ℂ) (hv : ∀ n, ‖v n‖ ≤ 1) :
      ‖∑ n ∈ Icc l r, v (n:ZMod q)*ExponentialSum.phase (|Z| * Real.log (n:ℝ))‖ ≤
        (q:ℝ)*(8*U/|Z|) :=
    periodic_log_phase_bound v hv _ _ _ fun k =>
      rational_additive_log_phase_first_bound k hU (abs_pos.mpr hZ) hZU l r hl hr
  by_cases hp : 0 ≤ Z
  · simpa only [abs_of_nonneg hp] using hbound w hw
  · let v : ZMod q → ℂ := fun n => (starRingEnd ℂ) (w n)
    have hv (n) : ‖v n‖ ≤ 1 := by simpa only [v, Complex.norm_conj] using hw n
    have he : (∑ n ∈ Icc l r, w (n:ZMod q)*ExponentialSum.phase (Z*Real.log (n:ℝ))) =
        (starRingEnd ℂ) (∑ n ∈ Icc l r,
          v (n:ZMod q)*ExponentialSum.phase (|Z| * Real.log (n:ℝ))) := by
      rw [map_sum]
      apply sum_congr rfl
      intro n _
      rw [map_mul, ← ExponentialSum.phase_neg, ← neg_mul, abs_of_neg (lt_of_not_ge hp), neg_neg]
      simp [v]
    rw [he, Complex.norm_conj]
    exact hbound v hv

/-- Uniform large-time cancellation on the same residue-restricted sums. -/
theorem sourceComparisonPeriodic_phase_uniform (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ U₀ : ℝ, 0 < A ∧ 0 < δ ∧ δ ≤ 1/2 ∧ 0 < U₀ ∧
      ∀ (q : ℕ) [NeZero q] (w : ZMod q → ℂ) (U Z : ℝ) (l r : ℕ),
        (∀ n, ‖w n‖ ≤ 1) → U₀ ≤ U → 1 ≤ |Z| → |Z| ≤ U^B →
        U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U →
        ‖∑ n ∈ Icc l r, w (n:ZMod q)*ExponentialSum.phase (Z*Real.log (n:ℝ))‖ ≤
          (q:ℝ)*A*(U/Real.sqrt |Z|+U^(1-δ)) := by
  obtain ⟨A, δ, hA, hδ, hδhalf, hbound⟩ := marked_linear_log_phase_uniform B hB
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hbound
  refine ⟨A, δ, max U₀ 1, hA, hδ, hδhalf,
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro q _ w U Z l r hw hU hZ hZU hl hr
  rw [mul_assoc]
  exact periodic_log_phase_bound w hw _ _ _ fun k =>
    hU₀ U ((le_max_left _ _).trans hU) ((k.val:ℝ)/q) Z l r hZ hZU hl hr

end
end ArtinMatthews
