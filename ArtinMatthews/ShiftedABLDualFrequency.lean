module

public import ArtinMatthews.ShiftedABLDualPartition
public import ArtinMatthews.ShiftedABLSourceParameters
public import ArtinMatthews.CubicThetaCircleDyadic
public import ArtinMatthews.ShiftedConvolutionCoefficients


set_option backward.privateInPublic true
@[expose] public section

/-! Exact grouping of a retained smooth dual block by its actual signed
frequency and the literal congruence-constrained coefficient. -/

noncomputable section
open OAI OAI.Erdos970.ErdosKloosterman
open scoped BigOperators

namespace ArtinMatthews

def shiftedABLDualWindow (j : ℕ) : Finset ℕ := Finset.Icc 1 (2*2^j)

theorem shiftedABLDualWindow_mem {j k : ℕ} (hk : spectralDyadicBlock j k ≠ 0) :
    k ∈ shiftedABLDualWindow j := by
  obtain ⟨hlo,hhi⟩ := shiftedABLDualWindow_bounds hk
  apply Finset.mem_Icc.mpr
  refine ⟨?_, by exact_mod_cast hhi⟩
  by_contra! hz
  have hz' : k = 0 := by omega
  simp only [hz', Nat.cast_zero, mul_zero] at hlo
  exact not_le_of_gt (by positivity : 0 < (2 : ℝ)^j) hlo

/-- The actual signed nonzero frequencies of the finite dual rectangle. -/
def shiftedABLDualFrequencies (m3 m4 : ℕ) (d : ℕ × ℕ) : Finset ℤ :=
  (((shiftedABLDualWindow d.1).product (shiftedABLDualWindow d.2)).filter
      (fun k => shiftedABLDualFrequency m3 m4 k.1 k.2 ≠ 0)).image
    (fun k => shiftedABLDualFrequency m3 m4 k.1 k.2)

/-- The ABL radius index and the sign of the actual integer frequency. -/
def shiftedABLSignedFrequencyIndex (ρ : ℤ) : ℕ × Bool :=
  (Nat.log 2 ρ.natAbs, decide (ρ < 0))

theorem shiftedABLDualFrequencies_witness {m3 m4 : ℕ} {d : ℕ × ℕ} {ρ : ℤ}
    (hρ : ρ ∈ shiftedABLDualFrequencies m3 m4 d) :
    ρ ≠ 0 ∧ ∃ k1 k2 : ℕ, (k1 : ℝ) ≤ 2*(2 : ℝ)^d.1 ∧
      (k2 : ℝ) ≤ 2*(2 : ℝ)^d.2 ∧ shiftedABLDualFrequency m3 m4 k1 k2 = ρ := by
  obtain ⟨k,hk,hkρ⟩ := Finset.mem_image.mp hρ
  obtain ⟨hprod,hnz⟩ := Finset.mem_filter.mp hk
  obtain ⟨hk1,hk2⟩ := Finset.mem_product.mp hprod
  exact ⟨hkρ ▸ hnz, k.1,k.2,by exact_mod_cast (Finset.mem_Icc.mp hk1).2,
    by exact_mod_cast (Finset.mem_Icc.mp hk2).2,hkρ⟩

/-- The actual block coefficient, with both smooth dual weights and the
original congruence. -/
def shiftedABLThetaRhoCoefficient (χ : SevenEighths.HeckeFamily.Character)
    (W1 W2 : SchwartzMap ℝ ℂ) (K1 K2 : ℝ) (D m3 m4 q : ℕ)
    (d : ℕ × ℕ) (ρ : ℤ) : ℂ :=
  shiftedConvolutionCoeff (shiftedABLDualWindow d.1) (shiftedABLDualWindow d.2)
    m3 m4 D
    (fun k => thetaBesselCoeff χ W1 K1 ((q : ℝ)^2) k * (spectralDyadicBlock d.1 k : ℂ))
    (fun k => thetaBesselCoeff χ W2 K2 ((q : ℝ)^2) k * (spectralDyadicBlock d.2 k : ℂ)) ρ

/-- The original Kloosterman term with the signed frequency as its
second argument and the inverse cofactor product unchanged. -/
def shiftedABLThetaRhoKloosterman (q : ℕ) [NeZero q] (m3 m4 : ℕ) (ρ : ℤ) : ℂ :=
  sum ZMod.stdAddChar ((m3 : ZMod q) - (m4 : ZMod q))
    (((m3 : ZMod q) * (m4 : ZMod q))⁻¹ * (ρ : ZMod q))

private theorem shiftedABLDual_congruence {D m3 m4 k1 k2 : ℕ} :
    Int.ModEq (D : ℤ) ((m3 : ℤ)^2*k1) ((m4 : ℤ)^2*k2) ↔
      (m3^2*k1 : ZMod D) = (m4^2*k2 : ZMod D) := by
  have h := (ZMod.natCast_eq_natCast_iff (m3^2*k1) (m4^2*k2) D).symm
  rw [← Int.natCast_modEq_iff] at h
  push_cast at h
  exact h

private theorem shiftedABLDual_frequency_zero {m3 m4 k1 k2 : ℕ} :
    shiftedABLDualFrequency m3 m4 k1 k2 = 0 ↔ m4*k2 = m3*k1 := by
  unfold shiftedABLDualFrequency
  rw [sub_eq_zero]
  norm_cast

private theorem shiftedABLThetaDyadic_inner_reindex (q : ℕ) [NeZero q]
    (D m3 m4 : ℕ) (a b : ℕ → ℂ) (d : ℕ × ℕ) :
    (∑' k : ℕ × ℕ, spectralDyadicCoefficient
      (shiftedDualNonzeroTerm q D m3 m4 a b k) k.1 k.2 d) =
      ∑ ρ ∈ shiftedABLDualFrequencies m3 m4 d,
        shiftedConvolutionCoeff (shiftedABLDualWindow d.1) (shiftedABLDualWindow d.2) m3 m4 D
          (fun k => a k * (spectralDyadicBlock d.1 k : ℂ))
          (fun k => b k * (spectralDyadicBlock d.2 k : ℂ)) ρ *
        shiftedABLThetaRhoKloosterman q m3 m4 ρ := by
  classical
  let S := (shiftedABLDualWindow d.1).product (shiftedABLDualWindow d.2)
  let f (k : ℕ × ℕ) := shiftedABLDualFrequency m3 m4 k.1 k.2
  let R := shiftedABLDualFrequencies m3 m4 d
  let u (k : ℕ × ℕ) : ℂ :=
    if (m3^2*k.1 : ZMod D) = (m4^2*k.2 : ZMod D) then
      (a k.1 * (spectralDyadicBlock d.1 k.1 : ℂ)) *
        (b k.2 * (spectralDyadicBlock d.2 k.2 : ℂ)) *
        shiftedABLThetaRhoKloosterman q m3 m4 (f k) else 0
  have hfinite : (∑' k : ℕ × ℕ, spectralDyadicCoefficient
      (shiftedDualNonzeroTerm q D m3 m4 a b k) k.1 k.2 d) =
      ∑ k ∈ S, spectralDyadicCoefficient
        (shiftedDualNonzeroTerm q D m3 m4 a b k) k.1 k.2 d := by
    apply tsum_eq_sum
    intro k hk
    by_cases h₁ : spectralDyadicBlock d.1 k.1 = 0
    · simp [spectralDyadicCoefficient, h₁]
    by_cases h₂ : spectralDyadicBlock d.2 k.2 = 0
    · simp [spectralDyadicCoefficient, h₂]
    exact (hk (Finset.mem_product.mpr ⟨shiftedABLDualWindow_mem h₁,shiftedABLDualWindow_mem h₂⟩)).elim
  rw [hfinite]
  have hfibre := Finset.sum_fiberwise_of_maps_to
    (s := S.filter (fun k => f k ≠ 0)) (t := R) (g := f)
    (fun k hk => Finset.mem_image_of_mem f hk) u
  calc
    _ = ∑ k ∈ S.filter (fun k => f k ≠ 0), u k := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hzero : f k = 0
      · have hn : m4*k.2 = m3*k.1 := shiftedABLDual_frequency_zero.mp hzero
        simp [hzero, hn, spectralDyadicCoefficient, shiftedDualNonzeroTerm]
      · have hn : m4*k.2 ≠ m3*k.1 := fun h => hzero (shiftedABLDual_frequency_zero.mpr h)
        simp only [hzero, ne_eq, not_false_eq_true, ite_true, shiftedDualNonzeroTerm,
          hn, ite_false, shiftedDualTerm, shiftedABLDual_congruence, u,
          spectralDyadicCoefficient, Complex.ofReal_mul]
        have hf : ((f k : ℤ) : ZMod q) =
            (m4 : ZMod q)*k.2-(m3 : ZMod q)*k.1 := by
          simp [f, shiftedABLDualFrequency]
        simp only [shiftedABLThetaRhoKloosterman, hf]
        split_ifs <;> ring
    _ = ∑ ρ ∈ R, ∑ k ∈ (S.filter (fun k => f k ≠ 0)).filter (fun k => f k = ρ), u k :=
      hfibre.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      have hρ0 := (shiftedABLDualFrequencies_witness hρ).1
      rw [Finset.sum_filter, Finset.sum_filter]
      change (∑ k ∈ (shiftedABLDualWindow d.1 ×ˢ shiftedABLDualWindow d.2),
        if f k ≠ 0 then if f k = ρ then u k else 0 else 0) = _
      rw [Finset.sum_product]
      unfold shiftedConvolutionCoeff
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k1 _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k2 _
      by_cases hfreq : f (k1,k2) = ρ
      · have hnonzero : f (k1,k2) ≠ 0 := by rw [hfreq]; exact hρ0
        have hraw : (m4 : ℤ)*k2-(m3 : ℤ)*k1 = ρ := hfreq
        simp only [hnonzero, ne_eq, not_false_eq_true, ite_true, hfreq, hraw, true_and, u]
        split_ifs <;> simp
      · have hraw : (m4 : ℤ)*k2-(m3 : ℤ)*k1 ≠ ρ := hfreq
        simp [hfreq,hraw]

theorem shiftedABLThetaDyadicNormalized_eq_rho
    (χ : SevenEighths.HeckeFamily.Character) (W1 W2 : SchwartzMap ℝ ℂ)
    (K1 K2 : ℝ) (D m3 m4 q : ℕ) [NeZero q] (d : ℕ × ℕ) :
    thetaDualDyadicNormalized χ W1 W2 K1 K2 D m3 m4 q d =
      (cubicThetaNebentypus (-((m3 : ℕ) : ℤ) * m4) / (q : ℂ)^2) *
        ∑ ρ ∈ shiftedABLDualFrequencies m3 m4 d,
          shiftedABLThetaRhoCoefficient χ W1 W2 K1 K2 D m3 m4 q d ρ *
          shiftedABLThetaRhoKloosterman q m3 m4 ρ := by
  simp only [thetaDualDyadicNormalized, dite_eq_right (NeZero.ne q), shiftedABLThetaRhoCoefficient]
  rw [shiftedABLThetaDyadic_inner_reindex]

end ArtinMatthews
