module

public import ArtinMatthews.GiantOrdinaryProxyTuple
public import ArtinMatthews.GiantActualSlotWeights
public import ArtinMatthews.GiantCofactorReciprocalMoment
public import ArtinMatthews.GiantHyperbolaRows
public import ArtinMatthews.PrimeExtractionCutoffShift


set_option backward.privateInPublic true
@[expose] public section

/-! Separate the original smooth cutoff from the genuine slot coefficient.
Only the cofactor factor changes when the coefficient is truncated. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

def giantOrdinarySlotCore {J : Type*} [Fintype J]
    (e : J → ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    (x γ : ℝ) (β : ℕ → ℂ) (m n : ℕ) : ℂ :=
  χ (m*n) * giantCenteredSlotCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) m *
    β n * (literalMarkedArrayWeight e x (m*n-1):ℂ) * G x (m*n-1)

def giantSlotCutoffSum (X : ℕ) (A : ℕ → ℕ → ℂ) (φ : ℕ → ℂ) : ℂ :=
  ∑ mn ∈ ((Ioc 0 X)×ˢ(Ioc 0 X)).filter (fun mn => mn.1*mn.2 ≤ X),
    A mn.1 mn.2 * φ (mn.1*mn.2)

theorem giantOrdinarySlotDiscrepancy_eq_cutoffSum {J : Type*} [Fintype J]
    (e : J → ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    (Φ : ℝ → ℝ) (T γ : ℝ) {k : ℕ} (i : Fin (k+1)) (x : ℝ) :
    giantOrdinarySlotDiscrepancy e χ G Φ T γ i x =
      giantSlotCutoffSum ⌊T*x⌋₊ (giantOrdinarySlotCore e χ G x γ
        (giantMixedCofactorCoefficient i (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ)))
        (fun n => (Φ (((n-1:ℕ):ℝ)/x):ℂ)) := by
  unfold giantOrdinarySlotDiscrepancy giantSlotCutoffSum
  apply sum_congr rfl
  intro mn _
  simp only [giantOrdinarySlotCore,giantCenteredSlotCoefficient,markedExtractionWeight]
  ring

theorem giantOrdinarySlotCore_norm_le {J : Type*} [Fintype J]
    (e : J → ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    (x γ : ℝ) (β : ℕ → ℂ) (m n : ℕ) {A B V C : ℝ}
    (hA : ‖giantCenteredSlotCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) m‖ ≤ A)
    (hB : ‖β n‖ ≤ B) (hV : literalMarkedArrayWeight e x (m*n-1) ≤ V) (hG : ‖G x (m*n-1)‖ ≤ C) :
    ‖giantOrdinarySlotCore e χ G x γ β m n‖ ≤ A*B*V*C := by
  have hw : ‖(literalMarkedArrayWeight e x (m*n-1):ℂ)‖ ≤ V := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (literalMarkedArrayWeight_nonneg e x (m*n-1))] using hV
  have hχ := χ.norm_le_one ((m:ZMod q)*(n:ZMod q))
  have hA₀ : 0 ≤ A := (norm_nonneg _).trans hA
  have hB₀ : 0 ≤ B := (norm_nonneg _).trans hB
  have hV₀ : 0 ≤ V := (norm_nonneg _).trans hw
  simp only [giantOrdinarySlotCore,norm_mul]
  calc
    _ ≤ 1*A*B*V*C := by gcongr
    _ = _ := by rw [one_mul]

theorem giantOrdinarySlotCore_support {J : Type*} [Fintype J]
    (e : J → ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    (x γ : ℝ) (β : ℕ → ℂ) (m n : ℕ)
    (hβ : ∀ l,β l ≠ 0 → x^γ < (l:ℝ))
    (h : giantOrdinarySlotCore e χ G x γ β m n ≠ 0) :
    x^γ < (m:ℝ) ∧ x^γ < (n:ℝ) := by
  constructor
  · by_contra hm
    exact h (by simp [giantOrdinarySlotCore,giantCenteredSlotCoefficient,hm])
  · apply hβ
    intro hn
    exact h (by simp [giantOrdinarySlotCore,hn])

theorem giantSlotCutoff_cofactor_difference {J : Type*} [Fintype J]
    (e : J → ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    (Φ : ℝ → ℝ) (x γ : ℝ) (X : ℕ) (β β' : ℕ → ℂ) {D A : ℝ}
    (hD : 0 ≤ D) (hA : 0 ≤ A)
    (hw : ∀ v : ℕ,v ≤ X → ‖markedExtractionWeight e G Φ x v‖ ≤ D)
    (hα : ∀ m,‖giantCenteredSlotCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) m‖ ≤ A) :
    ‖giantSlotCutoffSum X (giantOrdinarySlotCore e χ G x γ β) (fun n => (Φ (((n-1:ℕ):ℝ)/x):ℂ)) -
      giantSlotCutoffSum X (giantOrdinarySlotCore e χ G x γ β') (fun n => (Φ (((n-1:ℕ):ℝ)/x):ℂ))‖ ≤
      (D*A)*(X:ℝ)*(∑ n ∈ Ioc 0 X, ‖β n-β' n‖/(n:ℝ)) := by
  let a (m n : ℕ) := markedExtractionWeight e G Φ x (m*n)*χ (m*n)*
    giantCenteredSlotCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) m
  unfold giantSlotCutoffSum
  rw [← sum_sub_distrib]
  have he : (∑ mn ∈ ((Ioc 0 X)×ˢ(Ioc 0 X)).filter (fun mn => mn.1*mn.2 ≤ X),
      (giantOrdinarySlotCore e χ G x γ β mn.1 mn.2 * (Φ (((mn.1*mn.2-1:ℕ):ℝ)/x):ℂ) -
        giantOrdinarySlotCore e χ G x γ β' mn.1 mn.2 * (Φ (((mn.1*mn.2-1:ℕ):ℝ)/x):ℂ))) =
    ∑ mn ∈ ((Ioc 0 X)×ˢ(Ioc 0 X)).filter (fun mn => mn.1*mn.2 ≤ X),
      a mn.1 mn.2*(β mn.2-β' mn.2) := by
    apply sum_congr rfl
    intro mn _
    simp only [a,giantOrdinarySlotCore,markedExtractionWeight]
    ring
  rw [he]
  apply giant_hyperbola_norm_le X a (fun n => β n-β' n) (mul_nonneg hD hA)
  intro m n _ _ hmn
  simp only [a,norm_mul]
  have hc := χ.norm_le_one ((m:ZMod q)*(n:ZMod q))
  calc
    _ ≤ (D*1)*A := mul_le_mul
      (mul_le_mul (hw _ hmn) hc (norm_nonneg _) hD) (hα m) (norm_nonneg _) (mul_nonneg hD zero_le_one)
    _ = _ := by rw [mul_one]

theorem giantSlotCutoff_shift_le (X : ℕ) (A : ℕ → ℕ → ℂ) (Φ : ℝ → ℝ)
    {x D : ℝ} (hx : 0 < x) (hD : 0 ≤ D) {K : NNReal} (hΦ : LipschitzWith K Φ)
    (hA : ∀ m n,0 < m → 0 < n → m*n ≤ X → ‖A m n‖ ≤ D) :
    ‖giantSlotCutoffSum X A (fun n => (Φ (((n-1:ℕ):ℝ)/x):ℂ)) -
      giantSlotCutoffSum X A (fun n => (Φ ((n:ℝ)/x):ℂ))‖ ≤
        (D*((K:ℝ)/x))*(X:ℝ)*(1+Real.log (X:ℝ)) := by
  let B (m n : ℕ) := A m n * ((Φ (((m*n-1:ℕ):ℝ)/x)-Φ (((m*n:ℕ):ℝ)/x):ℝ):ℂ)
  have hB (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m*n ≤ X) :
      ‖B m n‖ ≤ D*((K:ℝ)/x) := by
    dsimp only [B]
    rw [norm_mul]
    exact mul_le_mul (hA m n hm hn hmn) (prime_extraction_cutoff_shift_pointwise Φ hΦ hx
      (Nat.mul_pos hm hn)) (norm_nonneg _) hD
  have he : giantSlotCutoffSum X A (fun n => (Φ (((n-1:ℕ):ℝ)/x):ℂ)) -
      giantSlotCutoffSum X A (fun n => (Φ ((n:ℝ)/x):ℂ)) =
    ∑ mn ∈ ((Ioc 0 X)×ˢ(Ioc 0 X)).filter (fun mn => mn.1*mn.2 ≤ X),B mn.1 mn.2 * (1:ℂ) := by
    unfold giantSlotCutoffSum
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro mn _
    simp only [B,Complex.ofReal_sub,mul_one,mul_sub]
  rw [he]
  refine (giant_hyperbola_norm_le X B (fun _ => 1) (by positivity) hB).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simp only [norm_one]
  have hI : Ioc 0 X = Icc 1 X := by
    ext n
    simp only [mem_Ioc,mem_Icc]
    omega
  rw [hI]
  simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
    using harmonic_le_one_add_log X

end
end ArtinMatthews
