module

public import ArtinMatthews.ShiftedABLRhoFullSeparation
public import ArtinMatthews.ShiftedABLRhoSourceModulus


set_option backward.privateInPublic true
@[expose] public section

/-! The exact source packet uses the genuine finite signed index type. -/

noncomputable section
open Set OAI
open scoped BigOperators
namespace ArtinMatthews

def shiftedABLSourceRhoIndex (m3 m4 : ℕ) (d : ℕ × ℕ) (i : ℕ × Bool) : Finset ℤ :=
  (shiftedABLDualFrequencies m3 m4 d).filter (fun ρ => shiftedABLSignedFrequencyIndex ρ = i)

def shiftedABLSourceRhoPacketCoefficient (χ : SevenEighths.HeckeFamily.Character)
    (D m3 m4 : ℕ) (d : ℕ × ℕ) (i : ℕ × Bool) (z : ℝ × ℝ) (t : ℝ)
    (ρ : shiftedABLSourceRhoIndex m3 m4 d i) : ℂ :=
  shiftedABLMellinRhoCoefficient χ D m3 m4 d ρ.val z*
    shiftedABLRhoBlockPhase ((2 : ℝ)^i.1) (t+shiftedABLRhoHeight z) ρ.val

theorem shiftedABLSourceRhoPacketCoefficient_sq (χ : SevenEighths.HeckeFamily.Character)
    (D m3 m4 : ℕ) (d : ℕ × ℕ) (i : ℕ × Bool) (z : ℝ × ℝ) (t : ℝ) :
    (∑ ρ ∈ (shiftedABLSourceRhoIndex m3 m4 d i).attach,
      ‖shiftedABLSourceRhoPacketCoefficient χ D m3 m4 d i z t ρ‖^2) =
      ∑ ρ ∈ shiftedABLSourceRhoIndex m3 m4 d i, ‖shiftedABLMellinRhoCoefficient χ D m3 m4 d ρ z‖^2 := by
  unfold shiftedABLSourceRhoPacketCoefficient
  simp only [norm_mul,shiftedABLRhoBlockPhase_norm,mul_one]
  exact Finset.sum_attach _ (fun ρ => ‖shiftedABLMellinRhoCoefficient χ D m3 m4 d ρ z‖^2)

theorem shiftedABLSourceRhoIndex_sameSign {m3 m4 : ℕ} {d : ℕ × ℕ} {i : ℕ × Bool}
    (ρ : shiftedABLSourceRhoIndex m3 m4 d i) (n : ℤ) (hn : n ≠ 0)
    (hi : i.2 = decide (n < 0)) : 0 < ρ.val*n := by
  have hρ : ρ.val ≠ 0 := (shiftedABLRhoSignedBlock_band ρ.property).1
  have hd := congrArg Prod.snd (Finset.mem_filter.mp ρ.property).2
  change decide (ρ.val < 0) = i.2 at hd
  rw [hi,decide_eq_decide] at hd
  by_cases h : n < 0
  · exact mul_pos_of_neg_of_neg (hd.mpr h) h
  · exact mul_pos (lt_of_le_of_ne (not_lt.mp (fun hr => h (hd.mp hr))) (Ne.symm hρ))
      (lt_of_le_of_ne (not_lt.mp h) (Ne.symm hn))

theorem shiftedABLSourceRhoIndex_oppositeSign {m3 m4 : ℕ} {d : ℕ × ℕ} {i : ℕ × Bool}
    (ρ : shiftedABLSourceRhoIndex m3 m4 d i) (n : ℤ) (hn : n ≠ 0)
    (hi : i.2 ≠ decide (n < 0)) : ρ.val*n < 0 := by
  have hρ : ρ.val ≠ 0 := (shiftedABLRhoSignedBlock_band ρ.property).1
  have hd := congrArg Prod.snd (Finset.mem_filter.mp ρ.property).2
  change decide (ρ.val < 0) = i.2 at hd
  have hne : decide (ρ.val < 0) ≠ decide (n < 0) := hd ▸ hi
  by_cases h : n < 0
  · have hr : ¬ρ.val < 0 := fun hp => hne (by simp [hp,h])
    exact mul_neg_of_pos_of_neg (lt_of_le_of_ne (not_lt.mp hr) (Ne.symm hρ)) h
  · have hr : ρ.val < 0 := by
      by_contra hp
      exact hne (by simp [hp,h])
    exact mul_neg_of_neg_of_pos hr (lt_of_le_of_ne (not_lt.mp h) (Ne.symm hn))

theorem shiftedABLFullSeparatedSignedSum_eq_source_tsum
    (χ : SevenEighths.HeckeFamily.Character) (D m3 m4 F L : ℕ) [NeZero F]
    (hr : (m3*m4).Coprime F) (hL : 0 < L) (hm3 : 0 < m3) (hm4 : 0 < m4) (hne : m3 ≠ m4)
    (d : ℕ × ℕ) (i : ℕ × Bool) (z : ℝ × ℝ) (t : ℝ) :
    let r := m3*m4
    let n := (m3 : ℤ)-(m4 : ℤ)
    let a := shiftedABLRhoBlockScale L (shiftedABLFirstIndex m3 m4) r ((2 : ℝ)^i.1)
    let f := shiftedABLRhoCommonTest a (t+shiftedABLRhoHeight z)
    shiftedABLFullSeparatedSignedSum χ D m3 m4 F r L d i z t =
      ∑ ρ ∈ (shiftedABLSourceRhoIndex m3 m4 d i).attach,
        shiftedABLSourceRhoPacketCoefficient χ D m3 m4 d i z t ρ*
        (∑' c, gamma0MixedSourceModulusTerm r F hr ρ.val n
          (fun C => f (4*Real.pi*Real.sqrt (|(ρ.val : ℝ)*(n : ℝ)|)/C)) c) := by
  dsimp only
  unfold shiftedABLFullSeparatedSignedSum
  let U := shiftedABLSourceRhoIndex m3 m4 d i
  change (∑ ρ ∈ U, _) = _
  rw [← Finset.sum_attach U]
  apply Finset.sum_congr rfl
  intro ρ _
  refine congrArg (shiftedABLSourceRhoPacketCoefficient χ D m3 m4 d i z t ρ*·) ?_
  exact shiftedABLRhoCommonModulusSum_eq_tsum F L m3 m4 hr hL hm3 hm4 hne
    (by positivity) (shiftedABLRhoSignedBlock_band ρ.property).2.2 (t+shiftedABLRhoHeight z)

end ArtinMatthews
