module

public import ArtinMatthews.SourceComparisonConstantEnergy
public import ArtinMatthews.SourceComparisonDivisorPhase


set_option backward.privateInPublic true
@[expose] public section

/-! High-time cancellation for the actual small-prime factor times a
residue-restricted marked weight with its truncated divisor expansion. -/

namespace ArtinMatthews

open Finset Filter MeasureTheory
open scoped Topology

noncomputable section

private theorem rpow_le_exp_eventually (a c d : ℝ) (hd : 0 < d) :
    ∀ᶠ X : ℝ in atTop, c*X^a ≤ Real.exp (d*X) := by
  have h : Tendsto (fun X : ℝ => c*(X^a*Real.exp (-d*X))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a d hd).const_mul c
  filter_upwards [h.eventually (gt_mem_nhds zero_lt_one)] with X hX
  have hx : c*(X^a*Real.exp (-d*X)) ≤ 1 := hX.le
  rw [← mul_assoc, neg_mul, Real.exp_neg, ← div_eq_mul_inv] at hx
  exact (div_le_one (Real.exp_pos _)).mp hx

private theorem exp_sublinear_le_eventually (d : ℝ) (hd : 0 < d) :
    ∀ᶠ X : ℝ in atTop, Real.exp (X^(91/(100:ℝ))) ≤ Real.exp (d*X) := by
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 9/100)).eventually
    (gt_mem_nhds hd)
  filter_upwards [h, eventually_gt_atTop (0:ℝ)] with X hX hX0
  apply Real.exp_le_exp.mpr
  conv_lhs => rw [show (91/(100:ℝ)) = -(9/(100:ℝ))+1 by norm_num]
  rw [Real.rpow_add hX0, Real.rpow_one]
  exact mul_le_mul_of_nonneg_right hX.le hX0.le

private theorem dyadic_polynomial_sub (l r : ℕ) (U : ℝ) (a b : ℕ → ℂ) (t : ℝ) :
    markedDyadicPolynomial l r U a t - markedDyadicPolynomial l r U b t =
      markedDyadicPolynomial l r U (fun n => a n-b n) t := by
  simp only [markedDyadicPolynomial, sub_mul, sum_sub_distrib, sub_div]

private theorem divisor_phase_moderate_window (d a E : ℝ) (hd : 0 < d) :
    ∀ᶠ X : ℝ in atTop, ∀ {ι : Type*} (J : Finset ι) (divisor : ι → ℕ) (coeff : ι → ℂ)
      (q : ℕ) [NeZero q] (w : ZMod q → ℂ) (M N : ℕ) (H t : ℝ),
      (∀ n, ‖w n‖ ≤ 1) → (q:ℝ) ≤ X^a → 0 < H → t ≠ 0 →
      H ≤ (M:ℝ)+1 → (N:ℝ) ≤ 2*H →
      (∀ i ∈ J, 0 < divisor i ∧ Real.exp (d*X) ≤ H/divisor i) →
      (∑ i ∈ J, ‖coeff i‖/(divisor i:ℝ)) ≤ X^E →
      |t| ≤ Real.exp ((d/2)*X) →
      ‖markedDyadicPolynomial (M+1) N H
        (fun n => markedMajorDivisorPolynomial J divisor coeff n*w (n:ZMod q)) t‖ ≤
        (16*Real.pi*X^(a+E))/|t| := by
  filter_upwards [rpow_le_exp_eventually a 4 (d/2) (half_pos hd),
    eventually_gt_atTop (0:ℝ)] with X hXq hX0
  intro ι J divisor coeff q _ w M N H t hw hq hH ht0 hM hN hdJ hmass htv
  let Vmid := Real.exp ((d/2)*X)
  let S₀ := Real.exp (d*X)
  let C₀ := 16*Real.pi*X^(a+E)
  have hpi0 : 0 < 2*Real.pi := by positivity
  have hpi1 : 1 ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
  have hZ : 4*(q:ℝ)*|t/(2*Real.pi)| ≤ S₀ := by
    rw [abs_div, abs_of_pos hpi0]
    calc
      _ ≤ (4*X^a)*Vmid := by
        have hZ : |t|/(2*Real.pi) ≤ Vmid := (div_le_self (abs_nonneg t) hpi1).trans htv
        gcongr
      _ ≤ Vmid*Vmid := mul_le_mul_of_nonneg_right hXq (Real.exp_pos _).le
      _ = S₀ := by dsimp [Vmid, S₀]; rw [← Real.exp_add]; congr 1; ring
  have hh := sourceComparisonDivisorPhase_moderate J divisor coeff w hw M N H t hH ht0 hM hN
    (fun i hi => ⟨(hdJ i hi).1,
      (Real.one_le_exp (by positivity : 0 ≤ d*X)).trans (hdJ i hi).2,
      hZ.trans (hdJ i hi).2⟩)
  apply hh.trans
  calc
    _ ≤ (X^a*16*Real.pi/|t|)*X^E := by
      have hs : 0 ≤ ∑ i ∈ J, ‖coeff i‖/(divisor i:ℝ) := sum_nonneg (fun _ _ => by positivity)
      gcongr
    _ = _ := by rw [Real.rpow_add hX0 a E]; ring

private theorem divisor_phase_large_window (d a E : ℝ) (hd : 0 < d) :
    ∃ G κ : ℝ, 0 < G ∧ 0 < κ ∧
    ∀ᶠ X : ℝ in atTop, ∀ {ι : Type*} (J : Finset ι) (divisor : ι → ℕ) (coeff : ι → ℂ)
      (q : ℕ) [NeZero q] (w : ZMod q → ℂ) (M N : ℕ) (H t : ℝ),
      (∀ n, ‖w n‖ ≤ 1) → (q:ℝ) ≤ X^a → 0 < H →
      H ≤ (M:ℝ)+1 → (N:ℝ) ≤ 2*H →
      (∀ i ∈ J, 0 < divisor i ∧ Real.exp (d*X) ≤ H/divisor i) →
      (∑ i ∈ J, ‖coeff i‖/(divisor i:ℝ)) ≤ X^E →
      Real.exp ((d/2)*X) < |t| → |t| ≤ Real.exp (2*X) →
      ‖markedDyadicPolynomial (M+1) N H
        (fun n => markedMajorDivisorPolynomial J divisor coeff n*w (n:ZMod q)) t‖ ≤
        4*G*X^(a+E)*Real.exp (-κ*X) := by
  let V := max (1/2:ℝ) (2/d)
  have hV : 1/2 ≤ V := le_max_left _ _
  obtain ⟨G, δ, U₀, hG, hδ, _, hU₀, hphase⟩ := sourceComparisonDivisorPhase_uniform V hV
  let κ := min (d/4) (δ*d)
  have hκ : 0 < κ := lt_min (by positivity) (mul_pos hδ hd)
  have hκ₁ : κ ≤ d/4 := min_le_left _ _
  have hκ₂ : κ ≤ δ*d := min_le_right _ _
  have hmid : Tendsto (fun X : ℝ => Real.exp ((d/2)*X)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (half_pos hd))
  have hscale : Tendsto (fun X : ℝ => Real.exp (d*X)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hd)
  refine ⟨G, κ, hG, hκ, ?_⟩
  filter_upwards [hmid.eventually (eventually_ge_atTop (8:ℝ)),
    hscale.eventually (eventually_ge_atTop U₀),
    eventually_gt_atTop (0:ℝ)] with X hXmid hXscale hX0
  intro ι J divisor coeff q _ w M N H t hw hq hH hM hN hdJ hmass htv hTU
  let Vmid := Real.exp ((d/2)*X)
  let S₀ := Real.exp (d*X)
  let m := 4*G*X^(a+E)*Real.exp (-κ*X)
  have hpi0 : 0 < 2*Real.pi := by positivity
  have hpi1 : 1 ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
  have hpi8 : 2*Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
  have hZeq : |t/(2*Real.pi)| = |t|/(2*Real.pi) := by rw [abs_div, abs_of_pos hpi0]
  have hZlo : 1 ≤ |t/(2*Real.pi)| := by
    rw [hZeq, le_div_iff₀ hpi0]
    exact (one_mul _).trans_le (hpi8.trans (hXmid.trans htv.le))
  have hZhi : |t/(2*Real.pi)| ≤ Real.exp (2*X) := by
    rw [hZeq]
    exact (div_le_self (abs_nonneg t) hpi1).trans hTU
  have hpow (i : ι) (hi : i ∈ J) : Real.exp (2*X) ≤ (H/divisor i)^V := by
    have hv : 2/d ≤ V := le_max_right _ _
    have hvd : 2 ≤ V*d := (div_le_iff₀ hd).mp hv
    calc
      _ ≤ Real.exp (d*X*V) := Real.exp_le_exp.mpr (by nlinarith)
      _ = S₀^V := by dsimp [S₀]; rw [Real.exp_mul]
      _ ≤ _ := Real.rpow_le_rpow (Real.exp_pos _).le (hdJ i hi).2 (by linarith)
  have hphase := hphase J divisor coeff q w M N H t S₀ hw hH hXscale hZlo hM hN
    (fun i hi => ⟨(hdJ i hi).1, (hdJ i hi).2, hZhi.trans (hpow i hi)⟩)
  have hZ8 : Vmid/8 ≤ |t/(2*Real.pi)| := by
    rw [hZeq]
    exact (div_le_div_of_nonneg_right htv.le (by norm_num : 0 ≤ (8:ℝ))).trans
      (div_le_div_of_nonneg_left (abs_nonneg t) hpi0 hpi8)
  have hroot : Real.exp ((d/4)*X)/3 ≤ Real.sqrt |t/(2*Real.pi)| := by
    apply (Real.le_sqrt (by positivity) (abs_nonneg _)).mpr
    calc
      _ ≤ Vmid/8 := by
        rw [div_pow, ← Real.exp_nat_mul]
        dsimp [Vmid]
        rw [show (2:ℝ)*((d/4)*X) = (d/2)*X by ring]
        linarith [Real.exp_pos ((d/2)*X)]
      _ ≤ _ := hZ8
  have hrootdecay : 1/Real.sqrt |t/(2*Real.pi)| ≤ 3*Real.exp (-κ*X) := by
    calc
      _ ≤ 1/(Real.exp ((d/4)*X)/3) :=
        div_le_div_of_nonneg_left zero_le_one (by positivity) hroot
      _ = 3*Real.exp (-(d/4)*X) := by
        rw [neg_mul, Real.exp_neg]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by norm_num)
  have hpowerdecay : S₀^(-δ) ≤ Real.exp (-κ*X) := by
    dsimp [S₀]
    rw [← Real.exp_mul]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hs : 0 ≤ ∑ i ∈ J, ‖coeff i‖/(divisor i:ℝ) := sum_nonneg (fun _ _ => by positivity)
  calc
    _ ≤ ((q:ℝ)*G*(1/Real.sqrt |t/(2*Real.pi)|+S₀^(-δ))) *
        (∑ i ∈ J, ‖coeff i‖/(divisor i:ℝ)) := hphase
    _ ≤ (X^a*G*(3*Real.exp (-κ*X)+Real.exp (-κ*X)))*X^E := by
      refine mul_le_mul ?_ hmass hs (by positivity)
      refine mul_le_mul (mul_le_mul_of_nonneg_right hq hG.le)
        (add_le_add hrootdecay hpowerdecay) (by positivity) (by positivity)
    _ = _ := by rw [Real.rpow_add hX0 a E]; ring

/-- The constant branch has arbitrary logarithmic high-time saving. The
input is the literal divisor coefficients and their squared approximation
error on the same dyad. Both bounds retain the normalization by (H). -/
theorem sourceComparisonHighTime_constant
    (c C d a D E A : ℝ)
    (hc : 0 < c) (hC : 0 < C) (hd : 0 < d) (ha : 0 ≤ a)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hA : 0 ≤ A) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ X : ℝ in atTop,
      ∀ {ι : Type*} (J : Finset ι) (divisor : ι → ℕ) (coeff : ι → ℂ)
        (P T H : ℝ) (M N : ℕ) (β : ℕ → ℂ),
        1 < P → c*X^(1/(10:ℝ)) ≤ Real.log P → Real.log P ≤ C*X →
        1 < T → T ≤ Real.exp (2*X) → T ≤ H →
        H ≤ (M:ℝ)+1 → (N:ℝ) ≤ 2*H →
        (∀ n ∈ Finset.Icc (M+1) N, ‖β n‖ ≤ X^D) →
        (∀ i ∈ J, 0 < divisor i ∧ Real.exp (d*X) ≤ H/divisor i) →
        (∑ i ∈ J, ‖coeff i‖/(divisor i:ℝ)) ≤ X^E →
        ∀ (q : ℕ) [NeZero q] (w : ZMod q → ℂ), (q:ℝ) ≤ X^a →
          (∀ n, ‖w n‖ ≤ 1) →
          (∑ n ∈ Finset.Icc (M+1) N,
            ‖(β n - markedMajorDivisorPolynomial J divisor coeff n*w (n:ZMod q))/H‖^2) ≤
              X^(-(A+2))/H →
          ∀ (k : ℕ) (χ : DirichletCharacter ℂ k) (ξ : ℝ) (S : Finset ℕ),
            (∀ p ∈ S, p.Prime) → (∀ p ∈ S, (p:ℝ) ≤ 2*P) →
            (∫ t in sourceComparisonHighTimes T (X^B),
              ‖markedPrimePolynomial S P χ ξ t * markedDyadicPolynomial (M+1) N H β t‖^2) ≤
                X^(-A) := by
  let B := 2*(a+E)+A+2
  let F := D+A+2
  have hB : 0 < B := by dsimp [B]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  obtain ⟨G, κ, hG, hκ, hlargePhase⟩ := divisor_phase_large_window d a E hd
  let E₁ := 48*Real.exp 1
  let E₂ := 24*Real.exp 1
  let E₃ := 16*(16*Real.pi)^2+4*(E₁+E₂)+1+8*E₂
  refine ⟨B, hB, ?_⟩
  filter_upwards [sourceComparisonPrime_exceptionalIntervals_card c C 2 F hc hC (by norm_num) hF,
    eventually_ge_atTop (max 1 E₃), divisor_phase_moderate_window d a E hd,
    hlargePhase, exp_sublinear_le_eventually κ hκ,
    rpow_le_exp_eventually (2*(a+E)+A+2) (384*G^2) κ hκ]
    with X hcount hX hmoderate hlargePhase hXsub hXabsorb
  have hX1 : 1 ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := zero_lt_one.trans_le hX1
  have hE₃X : E₃ ≤ X := (le_max_right _ _).trans hX
  intro ι J divisor coeff P T H M N β hP hlo hhi hT hTU hTH hM hN hβ hdJ hmass
    q _ w hq hw herror k χ ξ S hS hScap
  let Psmall := markedPrimePolynomial S P χ ξ
  let D0 : ℕ → ℂ := fun n => markedMajorDivisorPolynomial J divisor coeff n*w (n:ZMod q)
  let Q := markedDyadicPolynomial (M+1) N H D0
  let R := markedDyadicPolynomial (M+1) N H β
  let I := markedExceptionalUnitIntervals Psmall T (X^(-F))
  let Vmid := Real.exp ((d/2)*X)
  let C₀ := 16*Real.pi*X^(a+E)
  let m := 4*G*X^(a+E)*Real.exp (-κ*X)
  let W := sourceComparisonHighTimes T (X^B)
  have hH : 0 < H := by linarith
  have hl : H ≤ ((M+1:ℕ):ℝ) := by exact_mod_cast hM
  have hmean : (∫ t in Set.Icc (-T) T, ‖R t‖^2) ≤ E₁*X^(2*D) := by
    have hm := sourceComparisonDyadicPolynomial_mean_square (M+1) N H T β hH
      (by linarith) hl hN
    have hs := sourceComparisonDyadicCoefficient_square_mass (M+1) N H (X^D) β hH hl hN hβ
    calc
      _ ≤ 8*Real.exp 1*(3*H)*(2*(X^D)^2/H) := hm.trans (by gcongr; linarith)
      _ = _ := by
        rw [show 2*D = D*2 by ring, Real.rpow_mul hX0.le, Real.rpow_two]
        dsimp [E₁]
        field_simp <;> norm_num
  have herr : (∫ t in Set.Icc (-T) T, ‖R t-Q t‖^2) ≤ E₂*X^(-(A+2)) := by
    simp_rw [R, Q, dyadic_polynomial_sub]
    have hm := sourceComparisonDyadicPolynomial_mean_square (M+1) N H T
      (fun n => β n-D0 n) hH (by linarith) hl hN
    calc
      _ ≤ 8*Real.exp 1*(3*H)*(X^(-(A+2))/H) := hm.trans (by gcongr; linarith)
      _ = _ := by dsimp [E₂]; field_simp <;> norm_num
  have hmod : ∀ t ∈ W, |t| ≤ Vmid → ‖Q t‖ ≤ C₀/|t| := by
    intro t ht htv
    have ht0 : t ≠ 0 := abs_ne_zero.mp (ne_of_gt ((Real.rpow_pos_of_pos hX0 _).trans_le ht.2))
    exact hmoderate J divisor coeff q w M N H t hw hq hH ht0 hM hN hdJ hmass htv
  have hlarge : ∀ t ∈ W, Vmid < |t| → ‖Q t‖ ≤ m := by
    intro t ht htv
    exact hlargePhase J divisor coeff q w M N H t hw hq hH hM hN hdJ hmass htv
      ((abs_le.mpr ht.1).trans hTU)
  have h := sourceComparisonConstant_window_energy Psmall R Q I T (X^B) Vmid (X^(-F))
    C₀ m (E₁*X^(2*D)) (E₂*X^(-(A+2))) (by positivity) (by positivity)
    (markedPrimePolynomial_continuous S P χ ξ)
    (markedDyadicPolynomial_continuous _ _ _ _) (markedDyadicPolynomial_continuous _ _ _ _)
    (fun t => markedPrimePolynomial_norm_le_two S (by linarith) χ ξ t hS hScap)
    (fun t ht hPt => markedExceptionalUnitIntervals_cover Psmall T (X^(-F)) t ht hPt.le)
    hmod hlarge hmean herr
  have hcard : (I.card:ℝ) ≤ 3*Real.exp (X^(91/(100:ℝ))) :=
    hcount P T hP hlo hhi hT hTU k χ ξ S hS hScap
  have hsq (z : ℝ) : (X^z)^2 = X^(z*2) := by rw [Real.rpow_mul hX0.le, Real.rpow_two]
  have hmiddle : 16*C₀^2/X^B = 16*(16*Real.pi)^2*X^(-A-2) := by
    dsimp [C₀]
    rw [mul_pow, hsq, div_eq_mul_inv, ← Real.rpow_neg hX0.le]
    rw [show 16*((16*Real.pi)^2*X^((a+E)*2))*X^(-B) =
      16*(16*Real.pi)^2*(X^((a+E)*2)*X^(-B)) by ring, ← Real.rpow_add hX0]
    congr 1
    dsimp [B]
    ring
  have hordinary : 4*(X^(-F))^2*(E₁*X^(2*D)+E₂*X^(-(A+2))) ≤
      4*(E₁+E₂)*X^(-A-2) := by
    have hpow : X^(-(A+2)) ≤ X^(2*D) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    calc
      _ ≤ 4*(X^(-F))^2*((E₁+E₂)*X^(2*D)) := by
        rw [add_mul]
        gcongr
      _ = 4*(E₁+E₂)*X^(-F*2+(2*D)) := by
        rw [hsq, Real.rpow_add hX0 (-F*2) (2*D)]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by dsimp [E₁,E₂]; positivity)
        apply Real.rpow_le_rpow_of_exponent_le hX1
        dsimp [F]
        linarith
  have hrare : 8*m^2*(I.card:ℝ) ≤ X^(-A-2) := by
    have hdec : 384*G^2*X^((a+E)*2)*Real.exp (-κ*X) ≤ X^(-A-2) := by
      rw [show -A-2 = -(A+2) by ring, Real.rpow_neg hX0.le, ← one_div]
      apply (le_div_iff₀ (Real.rpow_pos_of_pos hX0 _)).mpr
      have h1 := mul_le_mul_of_nonneg_right hXabsorb (Real.exp_pos (-κ*X)).le
      rw [← Real.exp_add, show κ*X+ -κ*X = 0 by ring, Real.exp_zero] at h1
      rw [show 2*(a+E)+A+2 = (a+E)*2+(A+2) by ring, Real.rpow_add hX0] at h1
      nlinarith only [h1]
    calc
      _ ≤ 8*m^2*(3*Real.exp (κ*X)) :=
        mul_le_mul_of_nonneg_left (hcard.trans (by gcongr)) (by positivity)
      _ = 384*G^2*X^((a+E)*2)*Real.exp (-κ*X) := by
        dsimp [m]
        rw [mul_pow, mul_pow, hsq, ← Real.exp_nat_mul]
        norm_num only [Nat.cast_ofNat]
        rw [show (2:ℝ)*(-κ*X) = -κ*X+-κ*X by ring, Real.exp_add]
        have he : Real.exp (-κ*X)*Real.exp (κ*X) = 1 := by
          rw [← Real.exp_add, show -κ*X+κ*X = 0 by ring, Real.exp_zero]
        calc
          _ = (384*G^2*X^((a+E)*2)*Real.exp (-κ*X)) *
              (Real.exp (-κ*X)*Real.exp (κ*X)) := by ring
          _ = _ := by rw [he, mul_one]
      _ ≤ _ := hdec
  apply h.trans
  calc
    _ ≤ E₃*X^(-A-2) := by
      rw [hmiddle]
      have herrorEq : X^(-(A+2)) = X^(-A-2) := by congr 1; ring
      rw [herrorEq] at hordinary ⊢
      have hh := add_le_add (add_le_add (le_refl (16*(16*Real.pi)^2*X^(-A-2))) hordinary) hrare
      calc
        _ ≤ 16*(16*Real.pi)^2*X^(-A-2)+4*(E₁+E₂)*X^(-A-2)+
            X^(-A-2)+8*(E₂*X^(-A-2)) := add_le_add_left hh _
        _ = _ := by dsimp [E₃]; ring
    _ ≤ X*X^(-A-2) := mul_le_mul_of_nonneg_right hE₃X (by positivity)
    _ ≤ X^(-A) := by
      conv_lhs => lhs; rw [← Real.rpow_one X]
      rw [← Real.rpow_add hX0]
      apply Real.rpow_le_rpow_of_exponent_le hX1
      linarith

end
end ArtinMatthews
