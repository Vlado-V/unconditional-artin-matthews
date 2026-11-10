module

public import ArtinMatthews.MarkedProgressionIndexed
public import Mathlib.NumberTheory.Harmonic.Defs
public import ArtinMatthews.GiantFixedResidueCounting
public import ArtinMatthews.MarkedProgressionCoprime
public import ArtinMatthews.MarkedProgressionUnrestricted
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Signed divisor-polynomial progressions in a fixed unit residue class.
The local condition at the fixed modulus is exact in the main term. -/
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators
noncomputable section

def giantFixedResidueSet (M a r : ℕ) (T : ℝ) : Finset ℕ :=
  (Finset.Icc 0 ⌊T⌋₊).filter (fun u => r ∣ u+1 ∧ Nat.ModEq M (u+1) a)

def giantFixedResidueScale (M r : ℕ) (I : ℝ) : ℝ :=
  if r.Coprime M then I / (r*M : ℕ) else 0

theorem giantFixedResidueSet_subset (M a r : ℕ) (T : ℝ) :
    giantFixedResidueSet M a r T ⊆ (Finset.Icc 0 ⌊T⌋₊).filter (fun u => r ∣ u+1) := by
  intro u hu
  obtain ⟨hU,hr,_⟩ := Finset.mem_filter.mp hu
  exact Finset.mem_filter.mpr ⟨hU,hr⟩

theorem giantFixedResidueScale_nonneg (M r : ℕ) {I : ℝ} (hI : 0≤I) :
    0≤giantFixedResidueScale M r I := by
  unfold giantFixedResidueScale
  split_ifs
  · exact div_nonneg hI (Nat.cast_nonneg _)
  · exact le_rfl

theorem giantFixedResidueScale_le (M r : ℕ) (hM : 0<M) {I : ℝ} (hI : 0≤I) :
    giantFixedResidueScale M r I ≤ I/(r:ℝ) := by
  unfold giantFixedResidueScale
  by_cases h : r.Coprime M
  · rw [ite_eq_left h,Nat.cast_mul,← div_div]
    exact div_le_self (div_nonneg hI (Nat.cast_nonneg _)) (by exact_mod_cast hM)
  · rw [ite_eq_right h]
    exact div_nonneg hI (Nat.cast_nonneg _)

theorem giantFixedResiduePolynomial_sum {ι : Type*} (D : Finset ι)
    (d : ι → ℕ) (c : ι → ℝ) (M a r : ℕ) (f : ℝ → ℝ) (T : ℝ) :
    (∑ u ∈ giantFixedResidueSet M a r T, f u*markedIndexedDivisorPolynomial D d c u) =
      ∑ j ∈ D, c j * ∑ u ∈ (giantFixedResidueSet M a r T).filter (fun u => d j∣u), f u := by
  classical
  unfold markedIndexedDivisorPolynomial
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : d j∣u <;> simp [hu,mul_comm]

theorem giantFixedResidue_divisor_smooth_scale (M a d r : ℕ)
    (hM : 0<M) (hd : 0<d) (hr : 0<r) (ha : a.Coprime M) (hdM : d.Coprime M)
    (f : ℝ → ℝ) {T : ℝ} (hT : 0≤T) (hf : Differentiable ℝ f)
    (hderiv : Continuous (deriv f)) (hfT : f T=0) :
    |(∑ u ∈ (giantFixedResidueSet M a r T).filter (fun u => d∣u), f u) -
      (if d.Coprime r then giantFixedResidueScale M r (∫ t in Set.Ioc 0 T, f t)/(d:ℝ) else 0)| ≤
      3*∫ t in Set.Ioc 0 T, |deriv f t| := by
  classical
  have h := giant_fixed_residue_divisor_smooth_error M a d r hM hd hr ha hdM f hT hf hderiv hfT
  have hs : (giantFixedResidueSet M a r T).filter (fun u => d∣u) =
      (Finset.Icc 0 ⌊T⌋₊).filter (fun u => d∣u ∧ r∣u+1 ∧ Nat.ModEq M (u+1) a) := by
    unfold giantFixedResidueSet
    ext u
    simp only [Finset.mem_filter]
    tauto
  rw [hs]
  convert h using 2
  unfold giantFixedResidueScale
  by_cases hdr : d.Coprime r
  · by_cases hrM : r.Coprime M
    · rw [ite_eq_left hdr,ite_eq_left hrM,ite_eq_left (And.intro hdr hrM),div_div]
      push_cast
      ring
    · rw [ite_eq_left hdr,ite_eq_right hrM,zero_div,ite_eq_right (fun h => hrM h.2)]
  · rw [ite_eq_right hdr,ite_eq_right (fun h => hdr h.1)]

theorem giantFixedResiduePolynomial_smooth_error {ι : Type*} (D : Finset ι)
    (d : ι → ℕ) (c : ι → ℝ) (M a r : ℕ) (hM : 0<M) (hr : 0<r) (ha : a.Coprime M)
    (hD : ∀ j∈D,0<d j ∧ (d j).Coprime M)
    (f : ℝ → ℝ) {T : ℝ} (hT : 0≤T) (hf : Differentiable ℝ f)
    (hderiv : Continuous (deriv f)) (hfT : f T=0) :
    |(∑ u ∈ giantFixedResidueSet M a r T,f u*markedIndexedDivisorPolynomial D d c u) -
      ∑ j ∈ D,c j*(if (d j).Coprime r then
        giantFixedResidueScale M r (∫ t in Set.Ioc 0 T, f t)/(d j:ℝ) else 0)| ≤
      (3*∫ t in Set.Ioc 0 T, |deriv f t|)*∑ j∈D,|c j| := by
  classical
  rw [giantFixedResiduePolynomial_sum,← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  apply (Finset.abs_sum_le_sum_abs _ D).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [abs_mul,mul_comm (3*∫ t in Set.Ioc 0 T, |deriv f t|)]
  exact mul_le_mul_of_nonneg_left
    (giantFixedResidue_divisor_smooth_scale M a (d j) r hM (hD j hj).1 hr ha (hD j hj).2
      f hT hf hderiv hfT) (abs_nonneg _)

private theorem giantFixedResidue_scale_main_le {ι : Type*} (D : Finset ι) (d : ι → ℕ)
    (c : ι → ℝ) (M r : ℕ) (I : ℝ) :
    |(∑ j∈D,c j*(if (d j).Coprime r then giantFixedResidueScale M r I/(d j:ℝ) else 0)) -
      giantFixedResidueScale M r I*(∑ j∈D,c j/(d j:ℝ))| ≤
    |(∑ j∈D,c j*(if (d j).Coprime r then (I/(M:ℝ))/(d j*r:ℕ) else 0)) -
      ((I/(M:ℝ))/(r:ℝ))*(∑ j∈D,c j/(d j:ℝ))| := by
  classical
  unfold giantFixedResidueScale
  by_cases hrM : r.Coprime M
  · rw [ite_eq_left hrM]
    have hscale : I/(r*M:ℕ) = I/(M:ℝ)/(r:ℝ) := by
      rw [Nat.cast_mul,div_div,mul_comm]
    rw [hscale]
    have hj (j : ι) : (I/(M:ℝ)/(r:ℝ))/(d j:ℝ) = (I/(M:ℝ))/(d j*r:ℕ) := by
      rw [div_div,Nat.cast_mul,mul_comm]
    simp only [hj,le_refl]
  · simp only [ite_eq_right hrM,zero_div,ite_self,mul_zero,Finset.sum_const_zero,zero_mul,sub_zero,
      abs_zero,abs_nonneg]

theorem giantFixedResiduePolynomial_summed_error {ι : Type*} (D : Finset ι)
    (d : ι → ℕ) (c : ι → ℝ) (M a R : ℕ) (hM : 0<M) (ha : a.Coprime M)
    (hD : ∀ j∈D,0<d j ∧ (d j).Coprime M)
    (f : ℝ → ℝ) {T : ℝ} (hT : 0≤T) (hf : Differentiable ℝ f)
    (hderiv : Continuous (deriv f)) (hfT : f T=0) :
    (∑ r∈Finset.Icc 1 R,|(∑ u∈giantFixedResidueSet M a r T,
      f u*markedIndexedDivisorPolynomial D d c u) -
      giantFixedResidueScale M r (∫ t in Set.Ioc 0 T, f t)*(∑ j∈D,c j/(d j:ℝ))|) ≤
      (R:ℝ)*(3*∫ t in Set.Ioc 0 T, |deriv f t|)*(∑ j∈D,|c j|) +
      |∫ t in Set.Ioc 0 T, f t| * (harmonic R:ℝ)*
        ∑ j∈D,(|c j|/(d j:ℝ))*∑ p∈(d j).primeFactors,1/(p:ℝ) := by
  classical
  let I := ∫ t in Set.Ioc 0 T, f t
  let V := 3*∫ t in Set.Ioc 0 T, |deriv f t|
  let C := ∑ j∈D, |c j|
  let Q (r : ℕ) := ∑ j∈D,c j*(if (d j).Coprime r then (I/(M:ℝ))/(d j*r:ℕ) else 0)
  let L := ∑ j∈D,(|c j|/(d j:ℝ))*∑ p∈(d j).primeFactors,1/(p:ℝ)
  have hlocal := marked_indexed_main_summed_error R D d c (fun j hj => (hD j hj).1) (I/(M:ℝ))
  have hHar : 0≤(harmonic R:ℝ) := by
    rw [← reciprocal_Icc_eq_harmonic]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hL : 0≤L := by
    exact Finset.sum_nonneg (fun _ _ => mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun _ _ => by positivity)))
  have hI : |I/(M:ℝ)|≤|I| := by
    simp only [abs_div,abs_of_nonneg (show (0:ℝ)≤(M:ℝ) from Nat.cast_nonneg M)]
    exact div_le_self (abs_nonneg _) (by exact_mod_cast hM)
  calc
    _ ≤ ∑ r∈Finset.Icc 1 R,(V*C + |Q r - ((I/(M:ℝ))/(r:ℝ))*(∑ j∈D,c j/(d j:ℝ))|) := by
      apply Finset.sum_le_sum
      intro r hr
      let M₀ := ∑ j∈D,c j*(if (d j).Coprime r then giantFixedResidueScale M r I/(d j:ℝ) else 0)
      apply (abs_sub_le _ M₀ _).trans
      exact add_le_add
        (giantFixedResiduePolynomial_smooth_error D d c M a r hM (Finset.mem_Icc.mp hr).1
          ha hD f hT hf hderiv hfT)
        (giantFixedResidue_scale_main_le D d c M r I)
    _ = (R:ℝ)*V*C + ∑ r∈Finset.Icc 1 R,
        |Q r-((I/(M:ℝ))/(r:ℝ))*(∑ j∈D,c j/(d j:ℝ))| := by
      rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]
      simp only [Nat.card_Icc,Nat.add_sub_cancel,mul_assoc]
    _ ≤ _ := add_le_add le_rfl (hlocal.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hI hHar) hL))

end
end ArtinMatthews
