module

public import ArtinMatthews.MarkedPhysicalBandLineObservable
public import ArtinMatthews.MarkedPhysicalBonferroniExpectedTail


set_option backward.privateInPublic true
@[expose] public section

/-! Performed Bonferroni truncation of the actual common full-band
line observable. The exact active guard is retained; the resulting
mean error is the already proved selected-modulus odd-tail mean. -/

noncomputable section
namespace ArtinMatthews
open OAI.Erdos970.NumberTheoryLean
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}

def markedPhysicalBandLineUsedWeight (hP : ∀ j p,p∈P j → p.Prime) (ell : MarkedPhysicalBandLines P)
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) : ℝ :=
  ∏ p ∈ markedPhysicalPathUsedPrimes I a,markedPhysicalBandLinePrimePathFactor hP ell I a r z hz p

def markedPhysicalBandLineLoss (hP : ∀ j p,p∈P j → p.Prime) (ell : MarkedPhysicalBandLines P)
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (p : ℕ) : ℝ :=
  1-markedPhysicalBandLinePrimePathFactor hP ell I a r z hz p

def markedPhysicalBandLinePolynomial (hP : ∀ j p,p∈P j → p.Prime) (ell : MarkedPhysicalBandLines P)
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (k : ℕ) : ℝ :=
  markedPhysicalBandLineUsedWeight hP ell I a r z hz *
    BonferroniDensity.densityPolynomial k (markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes I a)
      (markedPhysicalBandLineLoss hP ell I a r z hz)

theorem markedPhysicalBandLinePrimePathFactor_mem_unitInterval
    (hP : ∀ j p,p∈P j → p.Prime) (ell : MarkedPhysicalBandLines P)
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (p : ℕ) :
    0 ≤ markedPhysicalBandLinePrimePathFactor hP ell I a r z hz p ∧
      markedPhysicalBandLinePrimePathFactor hP ell I a r z hz p ≤ 1 := by
  have hf (v : ι) (hv : v∈I) :
      0 ≤ markedPhysicalBandLineVisitFactor hP ell (markedPhysicalActivePrimes (a v)) (r v) (z v) (hz v) p ∧
      markedPhysicalBandLineVisitFactor hP ell (markedPhysicalActivePrimes (a v)) (r v) (z v) (hz v) p ≤ 1 := by
    have hh := hr v hv
    unfold markedPhysicalBandLineVisitFactor
    split_ifs <;> constructor <;> linarith
  exact ⟨Finset.prod_nonneg (fun v hv => (hf v hv).1),
    Finset.prod_le_one₀ (fun v hv => (hf v hv).1) (fun v hv => (hf v hv).2)⟩

theorem markedPhysicalBandLineWeight_split
    (hP : ∀ j p,p∈P j → p.Prime) (ell : MarkedPhysicalBandLines P)
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) :
    markedPhysicalBandLineWeight hP ell I a r z hz =
      markedPhysicalBandLineUsedWeight hP ell I a r z hz *
        ∏ p ∈ markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes I a,
          (1-markedPhysicalBandLineLoss hP ell I a r z hz p) := by
  simp only [markedPhysicalBandLineLoss,sub_sub_cancel]
  rw [mul_comm]
  exact (Finset.prod_sdiff (markedPhysicalPathUsedPrimes_subset I a)).symm

theorem markedPhysicalBandLineTail_eq
    (hP : ∀ j p,p∈P j → p.Prime) (ell : MarkedPhysicalBandLines P)
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (k : ℕ) :
    markedPhysicalBandLineTail hP ell I a r z hz k =
      markedPhysicalBandLineUsedWeight hP ell I a r z hz *
        BonferroniDensity.elementarySum (markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes I a)
          (markedPhysicalBandLineLoss hP ell I a r z hz) k := by
  rw [BonferroniDensity.elementarySum,Finset.mul_sum]
  rfl

theorem markedPhysicalBandLineTail_nonneg
    (hP : ∀ j p,p∈P j → p.Prime) (ell : MarkedPhysicalBandLines P)
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (k : ℕ) :
    0 ≤ markedPhysicalBandLineTail hP ell I a r z hz k := by
  rw [markedPhysicalBandLineTail_eq]
  exact mul_nonneg (Finset.prod_nonneg (fun p _ =>
    (markedPhysicalBandLinePrimePathFactor_mem_unitInterval hP ell I a r hr z hz p).1))
    (BonferroniDensity.elementarySum_nonneg _ _ (fun p _ =>
      sub_nonneg.mpr (markedPhysicalBandLinePrimePathFactor_mem_unitInterval hP ell I a r hr z hz p).2) k)

theorem markedPhysicalBandLinePolynomial_monomials
    (hP : ∀ j p,p∈P j → p.Prime) (ell : MarkedPhysicalBandLines P)
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (k : ℕ) :
    markedPhysicalBandLinePolynomial hP ell I a r z hz k =
      ∑ j ∈ Finset.range (k+1),(-1:ℝ)^j*
        ∑ T ∈ (markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes I a).powersetCard j,
          markedPhysicalBandLineMonomial hP ell I a r z hz T := by
  unfold markedPhysicalBandLinePolynomial BonferroniDensity.densityPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold BonferroniDensity.elementarySum markedPhysicalBandLineMonomial markedPhysicalBandLineUsedWeight
    markedPhysicalBandLineLoss
  rw [← Finset.mul_sum]
  ring

theorem markedPhysicalBandLinePolynomial_error
    (hP : ∀ j p,p∈P j → p.Prime) (ell : MarkedPhysicalBandLines P)
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (m : ℕ) :
    |markedPhysicalBandLineWeight hP ell I a r z hz-
      markedPhysicalBandLinePolynomial hP ell I a r z hz (2*m)| ≤
      markedPhysicalBandLineTail hP ell I a r z hz (2*m+1) := by
  have hf (p : ℕ) := markedPhysicalBandLinePrimePathFactor_mem_unitInterval hP ell I a r hr z hz p
  have hu : 0 ≤ markedPhysicalBandLineUsedWeight hP ell I a r z hz :=
    Finset.prod_nonneg (fun p _ => (hf p).1)
  have hb := BonferroniDensity.densityPolynomial_bounds
    (markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes I a)
    (markedPhysicalBandLineLoss hP ell I a r z hz)
    (fun p _ => sub_nonneg.mpr (hf p).2) (fun p _ => by
      unfold markedPhysicalBandLineLoss
      linarith [(hf p).1]) m
  have hbounds := And.intro (mul_le_mul_of_nonneg_left hb.1 hu) (mul_le_mul_of_nonneg_left hb.2 hu)
  simp only [← markedPhysicalBandLineWeight_split] at hbounds
  change markedPhysicalBandLinePolynomial hP ell I a r z hz (2*m+1) ≤ _ ∧
    _ ≤ markedPhysicalBandLinePolynomial hP ell I a r z hz (2*m) at hbounds
  have hgap : markedPhysicalBandLinePolynomial hP ell I a r z hz (2*m)-
      markedPhysicalBandLinePolynomial hP ell I a r z hz (2*m+1) =
      markedPhysicalBandLineTail hP ell I a r z hz (2*m+1) := by
    rw [markedPhysicalBandLinePolynomial,markedPhysicalBandLinePolynomial,← mul_sub,
      BonferroniDensity.densityPolynomial_gap,markedPhysicalBandLineTail_eq]
  rw [abs_of_nonpos (sub_nonpos.mpr hbounds.2)]
  linarith

def markedPhysicalIndependentBonferroni {N : ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (a : Fin (N+1) → MarkedPhysicalMarking P M) (q : ℝ)
    (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (k : ℕ) : ℝ :=
  (∑ ell : MarkedPhysicalBandLines P,if MarkedPhysicalBandLineGuard hP a z hz ell then
    markedPhysicalBandLinePolynomial hP ell Finset.univ a (markedMemoryVisitQ q N) z hz k else 0)/
      (Fintype.card (MarkedPhysicalBandLines P):ℝ)

theorem markedPhysicalIndependentBonferroni_error {N : ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (a : Fin (N+1) → MarkedPhysicalMarking P M) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (m : ℕ) :
    |markedMemoryIndependentLineExpectation (markedMemoryBandPrimeUnion (fun j => markedRawPrimeBand (P j)))
        (markedPhysicalMarkingPathRawSlots hP a) q z hz-
      markedPhysicalIndependentBonferroni hP a q z hz (2*m)| ≤
      markedPhysicalBonferroniTailMean hP Finset.univ a (markedMemoryVisitQ q N) z hz (2*m+1) := by
  rw [markedPhysicalIndependentLineExpectation_eq,markedPhysicalIndependentBonferroni,← sub_div,
    abs_div,abs_of_nonneg (show 0≤(Fintype.card (MarkedPhysicalBandLines P):ℝ) from Nat.cast_nonneg _),
    markedPhysicalBonferroniTailMean_common_lines,
    ← Finset.sum_sub_distrib]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro ell _
  split_ifs
  · exact markedPhysicalBandLinePolynomial_error hP ell Finset.univ a (markedMemoryVisitQ q N)
      (fun v _ => markedPhysicalVisitQ_mem_unitInterval hq0 hq1 N v) z hz m
  · simpa only [sub_self,abs_zero] using markedPhysicalBandLineTail_nonneg hP ell Finset.univ a
      (markedMemoryVisitQ q N) (fun v _ => markedPhysicalVisitQ_mem_unitInterval hq0 hq1 N v) z hz (2*m+1)

theorem markedPhysicalIndependentBonferroni_log_saving
    (e : J → ℝ) (he : ∀ j,0 < e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hinj : Function.Injective e) (B A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ x : ℝ in atTop,∀
      (a : Fin (markedMemoryMomentLength x+1) →
        MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x))
      (q : ℝ) (_hq0 : 0 ≤ q) (_hq1 : q ≤ 1)
      (z : Fin (markedMemoryMomentLength x+1) → ℤ × ℤ)
      (hz : ∀ v,IsCoprime (z v).1 (z v).2),
      Real.exp (B*(Real.log x)^(73/100:ℝ))*
        |markedMemoryIndependentLineExpectation (markedMemoryBandPrimeUnion (markedRawActualPrimeBand e x))
            (markedPhysicalMarkingPathRawSlots (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) a) q z hz-
          markedPhysicalIndependentBonferroni (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
            a q z hz (2*markedPhysicalBonferroniDepth x)| ≤
      (Real.log x)^(-A*(markedMemoryMomentLength x:ℝ)) := by
  filter_upwards [markedPhysicalActualVisitQTailMean_log_saving e he heUpper hinj B A hA] with x hx
  intro a q hq0 hq1 z hz
  exact (mul_le_mul_of_nonneg_left
    (markedPhysicalIndependentBonferroni_error (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
      a hq0 hq1 z hz (markedPhysicalBonferroniDepth x)) (Real.exp_nonneg _)).trans (hx a q hq0 hq1 z hz)

end ArtinMatthews
