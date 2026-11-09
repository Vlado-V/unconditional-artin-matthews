module

public import ArtinMatthews.MarkedPhysicalMarking
public import ArtinMatthews.MarkedPhysicalEndpointArithmetic
public import Mathlib.Data.Nat.Log


set_option backward.privateInPublic true
@[expose] public section

/-! Exact ordinary dyads and harmonic normalization for the actual ordered
auxiliary pads. The dyad reciprocal cancels the physical d0/D multiplier;
the two unshared-label normalizers remain separate. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalMass_add {J : Type*} [Fintype J] (V : J → ℝ) (a b : ℕ) :
    markedPhysicalMass V (a+b)=markedPhysicalMass V a*markedPhysicalMass V b := by
  simp only [markedPhysicalMass,pow_add,Finset.prod_mul_distrib]

theorem markedPhysicalPad_dyad_weight {J : Type*} [Fintype J]
    (V : J → ℝ) (pads : ℕ) (d₀ D : ℝ) (hd₀ : d₀≠0) :
    (d₀:ℂ)⁻¹*(markedPhysicalMass V (pads+2):ℂ)*((d₀/D:ℝ):ℂ)=
      ((markedPhysicalMass V pads/D:ℝ):ℂ)*(markedPhysicalMass V 2:ℂ) := by
  rw [markedPhysicalMass_add]
  push_cast
  have hdc : (d₀:ℂ)≠0 := by exact_mod_cast hd₀
  field_simp

theorem markedPhysicalPad_weight_eq_harmonic {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (pads : ℕ) (c : MarkedPhysicalMarking P pads) :
    markedPhysicalMass (fun j => bandReciprocalMass (P j)) pads/(markedPhysicalMarkingProduct c:ℝ)=
      ∏ j,∏ k,markedHarmonicAtom (P j) (c j k) := by
  rw [div_eq_mul_inv,← one_div,← markedPhysicalReciprocalProduct_eq]
  exact markedPhysicalMass_mul_reciprocal P pads c

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (pads : ℕ)

def markedPhysicalPadDyadIndices : Finset ℕ :=
  Finset.univ.image (fun c : MarkedPhysicalMarking P pads => Nat.log 2 (markedPhysicalMarkingProduct c))

include hP

omit [DecidableEq J] in
theorem markedPhysicalPad_dyad_iff (c : MarkedPhysicalMarking P pads) (j : ℕ) :
    (((2:ℕ)^j:ℝ)≤(markedPhysicalMarkingProduct c:ℝ) ∧
      (markedPhysicalMarkingProduct c:ℝ)<2*((2:ℕ)^j:ℝ)) ↔
      Nat.log 2 (markedPhysicalMarkingProduct c)=j := by
  have hD := markedPhysicalMarkingProduct_pos hP c
  constructor
  · rintro ⟨hl,hu⟩
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · exact_mod_cast hl
    · have h : markedPhysicalMarkingProduct c<2*(2:ℕ)^j := by exact_mod_cast hu
      simpa only [pow_succ'] using h
  · intro hj
    constructor
    · exact_mod_cast (hj ▸ Nat.pow_log_le_self 2 hD.ne')
    · have h := Nat.lt_pow_succ_log_self (by norm_num : 1<(2:ℕ)) (markedPhysicalMarkingProduct c)
      rw [hj] at h
      exact_mod_cast (show markedPhysicalMarkingProduct c<2*(2:ℕ)^j from by
        simpa only [pow_succ'] using h)

theorem markedPhysicalPad_dyad_selector (c : MarkedPhysicalMarking P pads) (F : ℕ → ℂ) :
    (∑ j ∈ markedPhysicalPadDyadIndices P pads,
      if ((2:ℕ)^j:ℝ)≤(markedPhysicalMarkingProduct c:ℝ) ∧
          (markedPhysicalMarkingProduct c:ℝ)<2*((2:ℕ)^j:ℝ) then F j else 0)=
      F (Nat.log 2 (markedPhysicalMarkingProduct c)) := by
  have hm : Nat.log 2 (markedPhysicalMarkingProduct c)∈markedPhysicalPadDyadIndices P pads :=
    Finset.mem_image.mpr ⟨c,Finset.mem_univ _,rfl⟩
  rw [Finset.sum_eq_single (Nat.log 2 (markedPhysicalMarkingProduct c))]
  · rw [ite_eq_left ((markedPhysicalPad_dyad_iff P hP pads c _).mpr rfl)]
  · intro j _ hj
    exact ite_eq_right (fun h => hj ((markedPhysicalPad_dyad_iff P hP pads c j).mp h).symm)
  · exact fun h => (h hm).elim

theorem markedPhysicalPad_dyad_harmonic (V : J → ℝ)
    (F : ℕ → MarkedPhysicalMarking P pads → ℂ) :
    (∑ j ∈ markedPhysicalPadDyadIndices P pads,(((2:ℕ)^j:ℝ):ℂ)⁻¹*
      ∑ c : MarkedPhysicalMarking P pads,
        if ((2:ℕ)^j:ℝ)≤(markedPhysicalMarkingProduct c:ℝ) ∧
            (markedPhysicalMarkingProduct c:ℝ)<2*((2:ℕ)^j:ℝ) then
          (markedPhysicalMass V (pads+2):ℂ)*
            (((((2:ℕ)^j:ℝ)/(markedPhysicalMarkingProduct c:ℝ)):ℝ):ℂ)*F j c
        else 0)=
      (markedPhysicalMass V 2:ℂ)*∑ c : MarkedPhysicalMarking P pads,
        ((markedPhysicalMass V pads/(markedPhysicalMarkingProduct c:ℝ):ℝ):ℂ)*
          F (Nat.log 2 (markedPhysicalMarkingProduct c)) c := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  have he (j : ℕ) :
      (((2:ℕ)^j:ℝ):ℂ)⁻¹*
        (if ((2:ℕ)^j:ℝ)≤(markedPhysicalMarkingProduct c:ℝ) ∧
            (markedPhysicalMarkingProduct c:ℝ)<2*((2:ℕ)^j:ℝ) then
          (markedPhysicalMass V (pads+2):ℂ)*
            (((((2:ℕ)^j:ℝ)/(markedPhysicalMarkingProduct c:ℝ)):ℝ):ℂ)*F j c else 0)=
        (markedPhysicalMass V 2:ℂ)*((markedPhysicalMass V pads/(markedPhysicalMarkingProduct c:ℝ):ℝ):ℂ)*
          (if ((2:ℕ)^j:ℝ)≤(markedPhysicalMarkingProduct c:ℝ) ∧
            (markedPhysicalMarkingProduct c:ℝ)<2*((2:ℕ)^j:ℝ) then F j c else 0) := by
    split_ifs
    · calc
        _ = ((((2:ℕ)^j:ℝ):ℂ)⁻¹*(markedPhysicalMass V (pads+2):ℂ)*
            (((((2:ℕ)^j:ℝ)/(markedPhysicalMarkingProduct c:ℝ)):ℝ):ℂ))*F j c := by ring
        _ = _ := by
          rw [markedPhysicalPad_dyad_weight V pads _ _ (by positivity)]
          ring
    · simp only [mul_zero]
  simp_rw [he]
  rw [← Finset.mul_sum,markedPhysicalPad_dyad_selector P hP pads c]
  ring

theorem markedPhysicalPad_dyad_actual_harmonic
    (F : ℕ → MarkedPhysicalMarking P pads → ℂ) :
    (∑ j ∈ markedPhysicalPadDyadIndices P pads,(((2:ℕ)^j:ℝ):ℂ)⁻¹*
      ∑ c : MarkedPhysicalMarking P pads,
        if ((2:ℕ)^j:ℝ)≤(markedPhysicalMarkingProduct c:ℝ) ∧
            (markedPhysicalMarkingProduct c:ℝ)<2*((2:ℕ)^j:ℝ) then
          (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (pads+2):ℂ)*
            (((((2:ℕ)^j:ℝ)/(markedPhysicalMarkingProduct c:ℝ)):ℝ):ℂ)*F j c
        else 0)=
      (markedPhysicalMass (fun j => bandReciprocalMass (P j)) 2:ℂ)*
        ∑ c : MarkedPhysicalMarking P pads,
          ((∏ j,∏ k,markedHarmonicAtom (P j) (c j k):ℝ):ℂ)*
            F (Nat.log 2 (markedPhysicalMarkingProduct c)) c := by
  rw [markedPhysicalPad_dyad_harmonic P hP pads]
  simp_rw [markedPhysicalPad_weight_eq_harmonic]

end
end ArtinMatthews
