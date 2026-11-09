module

public import ArtinMatthews.MarkedMajorLabelSumEnergy
public import ArtinMatthews.MarkedMajorArcIsolatedCancellation


set_option backward.privateInPublic true
@[expose] public section

/-! Arbitrary logarithmic saving for the complete prime-label major-arc
energy. The actual dyad partition, normalized Mellin coefficient, and
proved shifted-prime cancellation are all instantiated. -/
namespace ArtinMatthews
open Finset Filter MeasureTheory
open scoped Topology ContDiff

set_option maxHeartbeats 800000 in
theorem marked_major_label_cancellation
    (cutoff : ℝ → ℂ) (hcutoff : ContDiff ℝ ∞ cutoff) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) (hsupp : Function.support cutoff ⊆ Set.Icc lo hi)
    (c C₁ C₂ d a η τ C b K σ b₀ D P A₀ Kθ v₀ : ℝ)
    (hc : 0 < c) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hd : 0 < d)
    (ha : 0 ≤ a) (hη : 0 < η) (hτ : 0 < τ) (hC : 0 ≤ C)
    (hσ : 0 ≤ σ) (hb₀ : 0 ≤ b₀) (hD : 0 ≤ D) (hP : 0 ≤ P)
    (hA₀ : 0 ≤ A₀) (_hKθ : 0 ≤ Kθ) (hv₀ : 0 < v₀) :
    ∀ᶠ L : ℝ in atTop,∀ {J : Type} [Fintype J] [DecidableEq J]
      (P₀ : Finset ℕ) (bands : J → Finset ℕ),
      (∀ p ∈ P₀,p.Prime) → (∀ j p,p ∈ bands j → p.Prime) →
      (∀ j,Disjoint P₀ (bands j)) → Pairwise (fun i j => Disjoint (bands i) (bands j)) →
      v₀ ≤ bandReciprocalMass P₀ → (∀ j,0 < bandReciprocalMass (bands j)) →
      (∀ p ∈ P₀,c*L^(1/(10:ℝ)) ≤ Real.log p) →
      (∀ p ∈ P₀,Real.log p ≤ C₁*L^(1/(5:ℝ))) →
      ∀ (Y θ T H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ),
      0 < Y → |θ| ≤ Kθ*L^A₀ → 1 < T → Real.log T ≤ C₂*L →
      T ≤ K*Real.exp L*L^b → Real.exp (τ*L) ≤ H → H ≤ u → u ≤ v →
      v ≤ 2*H → v ≤ Real.exp (η*L) → Real.exp (d*L) ≤ U →
      U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U → H*U ≤ Real.exp (σ*L) → T/(H*U) ≤ L^b₀ →
      (∀ n ∈ Icc l r,‖β n‖ ≤ L^D) →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (modulation : ℝ),
      (q:ℝ) ≤ L^a → |modulation| ≤ L^C →
      ∀ (k : ℕ) (χb : DirichletCharacter ℂ k),
      (∫ t in Set.Icc (-T) T,
        ‖markedMajorLabelPolynomial (fun j : Option J => j.elim P₀ bands) cutoff χb θ Y t*
          markedMajorCenteredSum χ (Real.exp (L^(6/25:ℝ))) modulation t H u v*
          markedDyadicPolynomial l r U β t‖^2) ≤ L^(-P) := by
  obtain ⟨F,hF,hdyad⟩ := markedMajorLabelDyad_energy_of_isolated cutoff hcutoff hlo hhi hsupp
  let R := P+4*A₀+3
  have hR : 0 ≤ R := by dsimp [R]; linarith
  let Kd := 1+C₁/Real.log 2
  have hKd : 0 ≤ Kd := by dsimp [Kd]; positivity
  let Z := Kd^2*F*v₀⁻¹^2*hi^2*(1+Kθ)^4
  filter_upwards [marked_major_isolated_prime_cancellation (c/2) C₁ C₂ d a η τ C b K σ b₀ D R
      (by positivity) hC₁ hC₂ hd ha hη hτ hC hσ hb₀ hD hR,
    markedMajorPrimeDyads_uniform c C₁ hc hC₁,eventually_ge_atTop (max 1 Z)] with L hiso hdys hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hZL : Z ≤ L := (le_max_right _ _).trans hL
  intro J _ _ P₀ bands hP₀ hbands hdis₀ hdis hV₀ hV hloP hhiP
    Y θ T H u v U l r β hY hθ hT hTlog hTupper hH hHu huv hvH hvhi hU hl hr hHU hratio hβ
    q _ χ modulation hq hmod k χb
  let V := bandReciprocalMass P₀
  let M := fun t => markedMajorCenteredSum χ (Real.exp (L^(6/25:ℝ))) modulation t H u v
  let N := markedDyadicPolynomial l r U β
  obtain ⟨MB,hMB⟩ := marked_centered_sum_bounded χ (Real.exp (L^(6/25:ℝ))) modulation H u v
  obtain ⟨NB,hNB⟩ := marked_dyadic_sum_bounded l r U β
  have hMc := marked_centered_sum_continuous χ (Real.exp (L^(6/25:ℝ))) modulation H u v
  have hNc := markedDyadicPolynomial_continuous l r U β
  have hVp : 0 < V := hv₀.trans_le hV₀
  obtain ⟨hcard,hscales⟩ := hdys P₀ hP₀ hloP hhiP
  have hpiece : ∀ j ∈ markedMajorPrimeDyadIndices P₀,
      (∫ t in Set.Icc (-T) T,‖markedMajorLabelDyad bands (markedMajorPrimeDyad P₀ j) cutoff χb θ Y V t*M t*N t‖^2) ≤
        F*V⁻¹^2*hi^2*(1+|θ|)^4*L^(-R) := by
    intro j hj
    obtain ⟨hYj,hYlo,hYhi⟩ := hscales j hj
    have hsp : ∀ p ∈ markedMajorPrimeDyad P₀ j,p.Prime :=
      fun p hp => (markedMajorPrimeDyad_bounds P₀ j p hP₀ hp).1
    have hsl : ∀ p ∈ markedMajorPrimeDyad P₀ j,((2:ℕ)^j:ℝ) ≤ p := by
      intro p hp
      exact_mod_cast (markedMajorPrimeDyad_bounds P₀ j p hP₀ hp).2.1
    have hsu : ∀ p ∈ markedMajorPrimeDyad P₀ j,(p:ℝ) ≤ 2*((2:ℕ)^j:ℝ) := by
      intro p hp
      exact_mod_cast (markedMajorPrimeDyad_bounds P₀ j p hP₀ hp).2.2.le
    apply hdyad bands hbands hdis hV (markedMajorPrimeDyad P₀ j) hsp Y (((2:ℕ)^j:ℝ)) V θ T
      hY (by linarith) hVp hsl hsu χb M N hMc hNc MB NB (L^(-R)) hMB hNB (by positivity)
    intro ξ
    exact hiso (((2:ℕ)^j:ℝ)) T H u v U l r β hYj hYlo hYhi hT hTlog hTupper hH hHu huv hvH hvhi
      hU hl hr hHU hratio hβ q χ modulation hq hmod k χb ξ (markedMajorPrimeDyad P₀ j) hsp hsu
  have hfinite := markedMajor_finite_sum_energy (markedMajorPrimeDyadIndices P₀)
    (fun j t => markedMajorLabelDyad bands (markedMajorPrimeDyad P₀ j) cutoff χb θ Y V t*M t*N t)
    (fun j _ => ((markedMajorLabelDyad_continuous bands _ cutoff χb θ Y V).mul hMc).mul hNc)
    T (F*V⁻¹^2*hi^2*(1+|θ|)^4*L^(-R)) hpiece
  have hid (t : ℝ) :
      markedMajorLabelPolynomial (fun j : Option J => j.elim P₀ bands) cutoff χb θ Y t*M t*N t =
      ∑ j ∈ markedMajorPrimeDyadIndices P₀,
        markedMajorLabelDyad bands (markedMajorPrimeDyad P₀ j) cutoff χb θ Y V t*M t*N t := by
    rw [markedMajorLabelPolynomial_dyad_sum P₀ bands hP₀ hbands hdis₀ hdis]
    simp only [sum_mul,V]
  change (∫ t in Set.Icc (-T) T,
    ‖markedMajorLabelPolynomial (fun j : Option J => j.elim P₀ bands) cutoff χb θ Y t*M t*N t‖^2) ≤ _
  simp_rw [hid]
  apply hfinite.trans
  have hVinv : V⁻¹ ≤ v₀⁻¹ := inv_anti₀ hv₀ hV₀
  have hpow1 : 1 ≤ L^A₀ := Real.one_le_rpow hL1 hA₀
  have hθb : 1+|θ| ≤ (1+Kθ)*L^A₀ := by nlinarith
  have hcardsq := pow_le_pow_left₀ (Nat.cast_nonneg (markedMajorPrimeDyadIndices P₀).card) hcard 2
  have hVsq := pow_le_pow_left₀ (inv_nonneg.mpr hVp.le) hVinv 2
  have hθpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|θ|) hθb 4
  have hc1 := mul_le_mul_of_nonneg_right hcardsq (show 0 ≤ F*V⁻¹^2*hi^2*(1+|θ|)^4*L^(-R) by positivity)
  have hc2 := mul_le_mul_of_nonneg_left hVsq (show 0 ≤ (Kd*L)^2*F*hi^2*(1+|θ|)^4*L^(-R) by positivity)
  have hc3 := mul_le_mul_of_nonneg_left hθpow (show 0 ≤ (Kd*L)^2*F*v₀⁻¹^2*hi^2*L^(-R) by positivity)
  have hmajor : ((markedMajorPrimeDyadIndices P₀).card:ℝ)^2*(F*V⁻¹^2*hi^2*(1+|θ|)^4*L^(-R)) ≤
      Z*L^(-P-1) := by
    have hp : (L^A₀)^4 = L^(4*A₀) := by
      rw [mul_comm (4:ℝ),Real.rpow_mul hLp.le]
      norm_num
    have he : (Kd*L)^2*F*v₀⁻¹^2*hi^2*((1+Kθ)*L^A₀)^4*L^(-R) = Z*L^(-P-1) := by
      simp only [mul_pow, hp]
      dsimp [Z,R]
      have hpow : L^2*L^(4*A₀)*L^(-(P+4*A₀+3)) = L^(-P-1) := by
        rw [← Real.rpow_two,← Real.rpow_add hLp,← Real.rpow_add hLp]
        congr 1
        ring
      calc
        _ = (Kd^2*F*v₀⁻¹^2*hi^2*(1+Kθ)^4)*(L^2*L^(4*A₀)*L^(-(P+4*A₀+3))) := by ring
        _ = _ := by rw [hpow]
    rw [← he]
    calc
      _ ≤ (Kd*L)^2*(F*V⁻¹^2*hi^2*(1+|θ|)^4*L^(-R)) := hc1
      _ ≤ (Kd*L)^2*(F*v₀⁻¹^2*hi^2*(1+|θ|)^4*L^(-R)) := by
        convert hc2 using 1 <;> ring
      _ ≤ _ := by
        convert hc3 using 1 <;> ring
  apply hmajor.trans
  calc
    Z*L^(-P-1) ≤ L*L^(-P-1) := mul_le_mul_of_nonneg_right hZL (by positivity)
    _ = L^(-P) := by
      conv_lhs => lhs; rw [← Real.rpow_one L]
      rw [← Real.rpow_add hLp]
      congr 1
      ring

end ArtinMatthews
