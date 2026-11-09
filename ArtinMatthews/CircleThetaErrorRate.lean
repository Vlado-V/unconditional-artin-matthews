module

public import ArtinMatthews.CircleThetaSourceBound
public import ArtinMatthews.CircleErrorRate
public import ArtinMatthews.CircleNormalizerSmooth


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite theta source, with the literal smooth modulus cutoff,
converges to the original shifted sum at an explicit power rate. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

local instance : FunLike (UpperHalfPlane → ℂ) UpperHalfPlane ℂ :=
  ⟨id, Function.injective_id⟩

def circleThetaSourceError (χ : OAI.SevenEighths.HeckeFamily.Character)
    (m1 m2 K1 K2 : ℕ) (H1 H2 : ℝ → ℂ) (F r L : ℕ) : ℝ :=
  let d := m1.gcd m2
  let A := cuspSourcePair (heckeTheta χ) H1 H2
  ‖(∑ k∈((Finset.Icc 1 K1) ×ˢ (Finset.Icc 1 K2)).filter
        (fun k => (d : ℤ)∣((k.1 : ℤ)-1)),
        A k*circleDetector (circleModuli F r L) (circleSmoothWeight L)
          (circleShiftedFrequency (m1/d) (m2/d) k)) -
      (∑ n∈(Finset.range (K1+1)).filter (fun n => m1*n+1≤K1 ∧ m2*n+1≤K2),
        A (m1*n+1,m2*n+1))‖

theorem circleThetaSourceError_bound :
    ∃ C : ℝ, 0<C ∧ ∀ F r L : ℕ, 0<F → 0<r → F.Coprime r →
      4*(F*r)≤L → ∀ (χ : OAI.SevenEighths.HeckeFamily.Character)
      (m1 m2 K1 K2 : ℕ), 0 < m1 → Squarefree m1 →
      ∀ (H1 H2 : ℝ → ℂ) (B1 B2 : ℝ), 0≤B1 → 0≤B2 →
      (∀ n∈Finset.Icc 1 K1, ‖H1 n‖≤B1) →
      (∀ n∈Finset.Icc 1 K2, ‖H2 n‖≤B2) →
      circleThetaSourceError χ m1 m2 K1 K2 H1 H2 F r L ≤
        C*((K1 : ℝ)*K2)^2*B1*B2*(F : ℝ)*(r : ℝ)*
          (((m2/(m1.gcd m2))*K1+(m1/(m1.gcd m2))*K2 : ℕ) : ℝ)^2 /
            Real.sqrt L := by
  obtain ⟨C,hC,hbound⟩ := circleDetector_error_sqrt (1/2) (by norm_num) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro F r L hF hr hFr hL χ m1 m2 K1 K2 hm1 hs1 H1 H2 B1 B2 hB1 hB2 hw1 hw2
  have hLpos : 0<L := lt_of_lt_of_le (by positivity : 0<4*(F*r)) hL
  have hω : ∀ q∈circleModuli F r L, 0≤circleSmoothWeight L q :=
    fun q _ => circleSmoothWeight_nonneg L q
  have hplateau : ∀ q : ℕ, 4*L≤q → q≤5*L → 1≤circleSmoothWeight L q := by
    intro q hl hh
    rw [circleSmoothWeight_plateau hLpos hl hh]
  have he := circleTheta_original_approximation χ m1 m2 K1 K2 hm1 hs1
    H1 H2 B1 B2 hB1 hB2 hw1 hw2 (circleModuli F r L) (circleSmoothWeight L) hω
    (circleNormalizer_positive hF hr hFr hL _ hω hplateau)
  change circleThetaSourceError χ m1 m2 K1 K2 H1 H2 F r L ≤ _ at he
  apply he.trans
  have hb := hbound F r L hF hr hFr hL (circleSmoothWeight L) 1 (by norm_num)
    hω (fun q _ => circleSmoothWeight_le_one L q) hplateau
    ((m2/(m1.gcd m2))*K1+(m1/(m1.gcd m2))*K2)
  have hm := mul_le_mul_of_nonneg_left hb
    (mul_nonneg (mul_nonneg (sq_nonneg ((K1 : ℝ)*K2)) hB1) hB2)
  convert hm using 1
  ring

end ArtinMatthews
