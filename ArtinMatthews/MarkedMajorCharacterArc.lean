module

public import ArtinMatthews.MarkedMajorCharacterPhase


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite character separation on one rational arc. The original
determinant cutoff and the residual label phases are retained literally. -/
namespace ArtinMatthews
open Finset
noncomputable section

def markedMajorLabelArcPhase (θ Y : ℝ) (s : ℕ) : ℂ :=
  Complex.exp (((-2*Real.pi*θ*(s:ℝ)/Y:ℝ):ℂ)*Complex.I)

theorem markedMajor_arc_phase_split (q : ℕ) (h : ℤ) (θ Y : ℝ)
    (z z' : ℕ×(ℕ×ℕ)) :
    OAI.Problem337.RealPhase.phase
      (((h:ℝ)/(q:ℝ)+θ/Y)*((markedMajorIntegerDeterminant z z':ℤ)-(z.1:ℤ)+(z'.1:ℤ):ℤ)) =
      markedMajorIntegerArcPhase q h z z' * markedMajorLabelArcPhase θ Y z.1 *
        markedMajorLabelArcPhase (-θ) Y z'.1 *
        OAI.Problem337.RealPhase.phase (θ*((markedMajorIntegerDeterminant z z':ℤ):ℝ)/Y) := by
  unfold OAI.Problem337.RealPhase.phase markedMajorIntegerArcPhase markedMajorLabelArcPhase
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  ring

def markedMajorArcSourceSum (S T : Finset (ℕ×(ℕ×ℕ)))
    (A B : ℕ×(ℕ×ℕ) → ℂ) (ψ : ℝ → ℂ) (q : ℕ) (h : ℤ) (θ Y : ℝ) : ℂ :=
  ∑ z ∈ S,∑ z' ∈ T,A z*B z'*ψ ((markedMajorIntegerDeterminant z z':ℤ)/Y)*
    OAI.Problem337.RealPhase.phase
      (((h:ℝ)/(q:ℝ)+θ/Y)*((markedMajorIntegerDeterminant z z':ℤ)-(z.1:ℤ)+(z'.1:ℤ):ℤ))

def markedMajorArcCharacterTerm (S T : Finset (ℕ×(ℕ×ℕ)))
    (A B : ℕ×(ℕ×ℕ) → ℂ) (ψ : ℝ → ℂ) (q : ℕ) [NeZero q]
    (χ : AddChar (MarkedUnitTuple q) ℂ) (θ Y : ℝ) : ℂ :=
  ∑ z ∈ S,∑ z' ∈ T,
    (A z*markedMajorLabelArcPhase θ Y z.1*markedMajorCharacterLeft q χ z)*
    (B z'*markedMajorLabelArcPhase (-θ) Y z'.1*markedMajorCharacterRight q χ z')*
    (ψ ((markedMajorIntegerDeterminant z z':ℤ)/Y)*
      OAI.Problem337.RealPhase.phase (θ*((markedMajorIntegerDeterminant z z':ℤ):ℝ)/Y))

theorem markedMajor_arc_character_expansion (S T : Finset (ℕ×(ℕ×ℕ)))
    (A B : ℕ×(ℕ×ℕ) → ℂ) (ψ : ℝ → ℂ) (q : ℕ) [NeZero q] (h : ℤ) (θ Y : ℝ)
    (hA : ∀ z ∈ S,A z ≠ 0 → IsUnit (z.1:ZMod q) ∧ IsUnit (z.2.1:ZMod q) ∧ IsUnit (z.2.2:ZMod q))
    (hB : ∀ z ∈ T,B z ≠ 0 → IsUnit (z.1:ZMod q) ∧ IsUnit (z.2.1:ZMod q) ∧ IsUnit (z.2.2:ZMod q)) :
    markedMajorArcSourceSum S T A B ψ q h θ Y =
      ∑ χ : AddChar (MarkedUnitTuple q) ℂ,
        markedFourierCoeff (markedResiduePhase q h) χ * markedMajorArcCharacterTerm S T A B ψ q χ θ Y := by
  classical
  have hpoint (z z' : ℕ×(ℕ×ℕ)) (hz : z ∈ S) (hz' : z' ∈ T) :
      A z*B z'*ψ ((markedMajorIntegerDeterminant z z':ℤ)/Y)*
        OAI.Problem337.RealPhase.phase
          (((h:ℝ)/(q:ℝ)+θ/Y)*((markedMajorIntegerDeterminant z z':ℤ)-(z.1:ℤ)+(z'.1:ℤ):ℤ)) =
      ∑ χ : AddChar (MarkedUnitTuple q) ℂ,
        markedFourierCoeff (markedResiduePhase q h) χ *
        ((A z*markedMajorLabelArcPhase θ Y z.1*markedMajorCharacterLeft q χ z)*
        (B z'*markedMajorLabelArcPhase (-θ) Y z'.1*markedMajorCharacterRight q χ z')*
        (ψ ((markedMajorIntegerDeterminant z z':ℤ)/Y)*
          OAI.Problem337.RealPhase.phase (θ*((markedMajorIntegerDeterminant z z':ℤ):ℝ)/Y))) := by
    by_cases haz : A z=0
    · simp [haz]
    by_cases hbz : B z'=0
    · simp [hbz]
    rw [markedMajor_arc_phase_split,markedMajor_character_phase q h z z' (hA z hz haz) (hB z' hz' hbz)]
    simp only [sum_mul,mul_sum]
    apply sum_congr rfl
    intro χ _
    ring
  have H := sum_congr (s₁ := S) (s₂ := S) rfl (fun z hz =>
    sum_congr (s₁ := T) (s₂ := T) rfl (fun z' hz' => hpoint z z' hz hz'))
  unfold markedMajorArcSourceSum
  rw [H]
  simp only [markedMajorArcCharacterTerm,mul_sum]
  simp_rw [sum_comm (s := T) (t := univ)]
  rw [sum_comm]

end
end ArtinMatthews
