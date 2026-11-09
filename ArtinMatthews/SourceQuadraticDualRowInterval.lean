module

public import ArtinMatthews.SourceQuadraticSmallEulerBall


set_option backward.privateInPublic true
@[expose] public section

/-! A weighted complete row interval for the dual contour. The two
column coefficients may carry different norm-decreasing phases. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain QuadraticScale StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀

def sourceQuadraticDualEulerRowSum (rows cols : Finset E) (v w : E → ℂ) (s : ℂ) : ℂ :=
  ∑ a ∈ rows, (q a : ℂ) ^ (-(s / 2)) *
    sourceQuadraticSmallCoprimePair F S₀ hζ cols a
      (fun b => v b * star (quadraticSmallEuler F (I b) s))
      (sourceQuadraticSmallEulerCoeff F S₀ w s)

theorem sourceQuadraticDualRowFactor_norm {L : ℝ} (hL : 0 < L) (a : E)
    (ha : L ≤ (q a : ℝ)) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(q a : ℂ) ^ (-(s / 2))‖ ≤ L ^ (-(s.re / 2)) := by
  rw [← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ a))]
  simp only [Complex.neg_re, Complex.div_ofNat_re]
  exact Real.rpow_le_rpow_of_nonpos hL ha (by linarith)

theorem sourceQuadraticDual_coeffMass_le (cols : Finset E) (u v : E → ℂ)
    (hv : ∀ b ∈ cols, ‖v b‖ ≤ ‖u b‖) : coeffMass cols v ≤ coeffMass cols u := by
  apply Finset.sum_le_sum
  intro b hb
  exact pow_le_pow_left₀ (norm_nonneg _) (hv b hb) 2

variable [IsTotallyComplex F]

theorem sourceQuadraticDualEulerRowSum_interval_bound {α : ℝ}
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ L K P : ℝ, 0 < L → 1 ≤ K → 1 ≤ P →
      ∀ rows cols : Finset E,
      (∀ a ∈ rows, sourceReflectionIsSquarefree a ∧ L ≤ (q a : ℝ) ∧ (q a : ℝ) ≤ K) →
      (∀ b ∈ cols, sourceReflectionIsSquarefree b ∧ (q b : ℝ) ≤ 2 * P) →
      ∀ u v w : E → ℂ, (∀ b ∈ cols, ‖v b‖ ≤ ‖u b‖) →
      (∀ b ∈ cols, ‖w b‖ ≤ ‖u b‖) → ∀ s : ℂ, 0 ≤ s.re →
      ‖sourceQuadraticDualEulerRowSum F S₀ hζ rows cols v w s‖ ≤
        C * (K * P) ^ η * (2 * P) ^ η * L ^ (-(s.re / 2)) *
          (P + K ^ α) * coeffMass cols u := by
  obtain ⟨Cb, hCb, hb⟩ := sourceQuadraticSmallCoprimePair_ball_bound F S₀ hζ htrace hE η hη
  obtain ⟨Cm, hCm, hm⟩ := sourceQuadraticSmallEulerCoeff_mass F S₀ η hη
  refine ⟨Cb * Cm, by positivity, ?_⟩
  intro L K P hL hK hP rows cols hrows hcols u v w hv hw s hs
  let vl : E → ℂ := fun b => v b * star (quadraticSmallEuler F (I b) s)
  let wr := sourceQuadraticSmallEulerCoeff F S₀ w s
  let mass := Cm * (2 * P) ^ η * coeffMass cols u
  have hmass : 0 ≤ mass := by
    dsimp [mass]
    exact mul_nonneg (mul_nonneg hCm.le (Real.rpow_nonneg (by linarith) _))
      (coeffMass_nonneg _ _)
  have hvMass : sourceQuadraticSmallWeightedMass F S₀ cols vl ≤ mass := by
    rw [sourceQuadraticSmallEulerCoeff_star_mass]
    exact (hm (2 * P) (by linarith) cols (fun b hb' => (hcols b hb').2) v s hs).trans
      (mul_le_mul_of_nonneg_left (sourceQuadraticDual_coeffMass_le F S₀ cols u v hv)
        (by positivity))
  have hwMass : sourceQuadraticSmallWeightedMass F S₀ cols wr ≤ mass :=
    (hm (2 * P) (by linarith) cols (fun b hb' => (hcols b hb').2) w s hs).trans
      (mul_le_mul_of_nonneg_left (sourceQuadraticDual_coeffMass_le F S₀ cols u w hw)
        (by positivity))
  have hpair := hb K P hK hP rows cols
    (fun a ha => ⟨(hrows a ha).1, (hrows a ha).2.2⟩) hcols vl wr
  have hsqr : Real.sqrt (sourceQuadraticSmallWeightedMass F S₀ cols vl) *
      Real.sqrt (sourceQuadraticSmallWeightedMass F S₀ cols wr) ≤ mass := by
    calc
      _ ≤ Real.sqrt mass * Real.sqrt mass := by gcongr
      _ = mass := Real.mul_self_sqrt hmass
  calc
    _ ≤ ∑ a ∈ rows, L ^ (-(s.re / 2)) *
        ‖sourceQuadraticSmallCoprimePair F S₀ hζ cols a vl wr‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a ha
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (sourceQuadraticDualRowFactor_norm F S₀ hL a (hrows a ha).2.1 hs) (norm_nonneg _)
    _ = L ^ (-(s.re / 2)) *
        ∑ a ∈ rows, ‖sourceQuadraticSmallCoprimePair F S₀ hζ cols a vl wr‖ := by
      rw [Finset.mul_sum]
    _ ≤ L ^ (-(s.re / 2)) *
        (Cb * (K * P) ^ η * (P + K ^ α) * mass) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hL.le _)
      apply hpair.trans
      calc
        _ = (Cb * (K * P) ^ η * (P + K ^ α)) *
            (Real.sqrt (sourceQuadraticSmallWeightedMass F S₀ cols vl) *
              Real.sqrt (sourceQuadraticSmallWeightedMass F S₀ cols wr)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hsqr (by positivity)
    _ = _ := by dsimp [mass]; ring

end
end ArtinMatthews.SourceEulerAssembly
