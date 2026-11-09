module

public import ArtinMatthews.SourceQuadraticSmallSpectral
public import ArtinMatthews.SourceQuadraticSmallAmplitudeBound
public import ArtinMatthews.SourceQuadraticSmallPower


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain MeasureTheory Set QuadraticScale StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

def quadraticSmallErrorLine (ε : ℝ) : ℝ := min (ε / 2) (1 / 2)

theorem quadraticSmallErrorLine_pos {ε : ℝ} (hε : 0 < ε) :
    0 < quadraticSmallErrorLine ε := lt_min (by positivity) (by norm_num)

theorem quadraticSmallErrorLine_lt_one (ε : ℝ) : quadraticSmallErrorLine ε < 1 :=
  (min_le_right _ _).trans_lt (by norm_num)

theorem sourceQuadraticOriginalSmallErrorBlock_zero {K : ℝ} (hK : 0 ≤ K) (hK1 : K < 1)
    (M σ : ℝ) (cols : Finset E) (u : E → ℂ) (g : E) :
    sourceQuadraticOriginalSmallErrorBlock F S₀ hζ M K σ cols u g = 0 := by
  simp only [sourceQuadraticOriginalSmallErrorBlock, sourceQuadraticOriginalSmallError,
    sourceQuadraticSmallRows_empty F S₀ hK hK1 g, Finset.sum_empty, mul_zero,
    Finset.sum_const_zero]

/-- The actual original Small contour errors satisfy the reciprocal scale,
including every finite row and divisor sum. -/
theorem sourceQuadraticOriginalSmallErrorBlock_bound {α : ℝ}
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M K P : ℝ, 1 ≤ M → 1 ≤ P → 0 ≤ K → K ≤ M →
      ∀ cols : Finset E,
      (∀ b ∈ cols, sourceReflectionIsSquarefree b ∧ (q b : ℝ) ≤ 2 * P) →
      (∀ b ∈ cols, ∀ c ∈ cols,
        sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) →
      ∀ (u : E → ℂ) (g : E), g ∈ sourceQuadraticCommonIdeals F S₀ cols →
      ‖sourceQuadraticOriginalSmallErrorBlock F S₀ hζ M K (quadraticSmallErrorLine ε) cols u g‖ ≤
        C * (M * P) ^ ε * (P + K ^ α) * coeffMass cols u := by
  let η := ε / 4
  let σ := quadraticSmallErrorLine ε
  have hη : 0 < η := by dsimp [η]; positivity
  have hσ : 0 < σ := quadraticSmallErrorLine_pos hε
  have hσone : σ < 1 := quadraticSmallErrorLine_lt_one ε
  have hσtop : σ ≤ 5 / 4 := by linarith
  obtain ⟨Ca, hCa, ha⟩ := sourceQuadraticOriginalSmallAmplitude_bound F S₀ hζ htrace hE η hη
  let H := quadraticSmallContourKernel F sourceQuadraticBlockProfile σ
  have hHi : Integrable H := quadraticSmallContourKernel_integrable F sourceQuadraticBlockProfile
    sourceQuadraticBlockProfile_compact sourceQuadraticBlockProfile_positive
    sourceQuadraticBlockProfile_smooth hσ hσtop (ne_of_lt hσone)
  let L : ℝ := 1 + ∫ t : ℝ, ‖H t‖
  have hL : 0 < L := by
    have hn : 0 ≤ ∫ t : ℝ, ‖H t‖ := integral_nonneg (fun _ => norm_nonneg _)
    dsimp only [L]
    linarith
  refine ⟨Ca * L * 2 ^ (2 * η), by positivity, ?_⟩
  intro M K P hM hP hK hKM cols hcols hclass u g hg
  have hmass : 0 ≤ coeffMass cols u := coeffMass_nonneg _ _
  by_cases hK1 : 1 ≤ K
  · have hM0 := zero_lt_one.trans_le hM
    have hgn := sourceQuadraticSmallCommon_norm F S₀ P cols (fun b hb => (hcols b hb).2) g hg
    let A := Ca * (K * P) ^ η * (2 * P) ^ (2 * η) * (P + K ^ α) * coeffMass cols u
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hamp (t : ℝ) :
        ‖sourceQuadraticOriginalSmallAmplitude F S₀ hζ K cols u g (quadraticPoissonLine σ t)‖ ≤ A :=
      ha K P hK1 hP cols hcols hclass u g hgn _
        (by rw [quadraticPoissonLine_re]; exact hσ.le)
    rw [sourceQuadraticOriginalSmallErrorBlock_eq_integral F S₀ hζ hM0 hσ hσtop
      (ne_of_lt hσone) cols u g]
    have hint : ‖∫ t : ℝ, H t * (M : ℂ) ^ (quadraticPoissonLine σ t / 2) *
        sourceQuadraticOriginalSmallAmplitude F S₀ hζ K cols u g (quadraticPoissonLine σ t)‖ ≤
        (∫ t : ℝ, ‖H t‖) * (M ^ (σ / 2) * A) := by
      have hb : ‖∫ t : ℝ, H t * (M : ℂ) ^ (quadraticPoissonLine σ t / 2) *
          sourceQuadraticOriginalSmallAmplitude F S₀ hζ K cols u g (quadraticPoissonLine σ t)‖ ≤
          ∫ t : ℝ, ‖H t‖ * (M ^ (σ / 2) * A) :=
        norm_integral_le_of_norm_le (hHi.norm.mul_const (M ^ (σ / 2) * A)) (by
        filter_upwards with t
        rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hM0]
        have hre : (quadraticPoissonLine σ t / 2).re = σ / 2 := by
          rw [Complex.div_ofNat_re, quadraticPoissonLine_re]
        rw [hre]
        exact (mul_le_mul_of_nonneg_left (hamp t) (by positivity)).trans_eq (mul_assoc _ _ _))
      simpa only [integral_mul_const] using hb
    have hloss : 3 * η + σ / 2 ≤ ε := by
      have hσle : σ ≤ ε / 2 := min_le_left _ _
      dsimp only [η]
      linarith
    calc
      _ ≤ (∫ t : ℝ, ‖H t‖) * (M ^ (σ / 2) * A) := hint
      _ ≤ L * (M ^ (σ / 2) * A) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp only [L]
        linarith
      _ = (Ca * L) * (M ^ (σ / 2) * (K * P) ^ η * (2 * P) ^ (2 * η)) *
          (P + K ^ α) * coeffMass cols u := by dsimp [A]; ring
      _ ≤ (Ca * L) * (2 ^ (2 * η) * (M * P) ^ ε) *
          (P + K ^ α) * coeffMass cols u := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (quadraticSmall_power_absorb hM hP hK hKM hη.le hσ.le hloss) (by positivity))
            (by positivity)) hmass
      _ = _ := by ring
  · rw [sourceQuadraticOriginalSmallErrorBlock_zero F S₀ hζ hK (lt_of_not_ge hK1), norm_zero]
    positivity

/-- The same actual error fits the Small contribution in the B3 cutoff scale. -/
theorem sourceQuadraticOriginalSmallErrorBlock_cutoff_bound {α : ℝ}
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M K P : ℝ, 1 ≤ M → 1 ≤ P → 0 ≤ K → K ≤ M →
      ∀ cols : Finset E,
      (∀ b ∈ cols, sourceReflectionIsSquarefree b ∧ (q b : ℝ) ≤ 2 * P) →
      (∀ b ∈ cols, ∀ c ∈ cols,
        sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) →
      ∀ (u : E → ℂ) (g : E), g ∈ sourceQuadraticCommonIdeals F S₀ cols →
      ‖sourceQuadraticOriginalSmallErrorBlock F S₀ hζ M K (quadraticSmallErrorLine ε) cols u g‖ ≤
        C * (M * P) ^ ε * (P + Real.sqrt M * K ^ (α - 1 / 2)) * coeffMass cols u := by
  obtain ⟨C, hC, hb⟩ := sourceQuadraticOriginalSmallErrorBlock_bound F S₀ hζ htrace hE ε hε
  refine ⟨C, hC, ?_⟩
  intro M K P hM hP hK hKM cols hcols hclass u g hg
  have hmass : 0 ≤ coeffMass cols u := coeffMass_nonneg _ _
  by_cases hK1 : 1 ≤ K
  · exact (hb M K P hM hP hK hKM cols hcols hclass u g hg).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl (quadraticSmall_cutoff_power hK1 hKM))
          (by positivity)) (coeffMass_nonneg _ _))
  · rw [sourceQuadraticOriginalSmallErrorBlock_zero F S₀ hζ hK (lt_of_not_ge hK1), norm_zero]
    positivity

end
end ArtinMatthews.SourceEulerAssembly
