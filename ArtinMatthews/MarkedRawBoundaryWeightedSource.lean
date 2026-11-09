module

public import ArtinMatthews.MarkedRawBoundary
public import ArtinMatthews.MarkedMinorArcRawGhostWeight


set_option backward.privateInPublic true
@[expose] public section

/-! Exact source-boundary collapse for the positive conditional word.
The literal empty pending memory has factorial mass one and Schur weight
one. No arbitrary-state L² projection estimate is used. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedRawBoundaryEmptyMemory_schur {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) (B : ℕ) (v₀ : ℝ) :
    markedRawMemorySchurWeight v₀ (markedRawBoundaryEmptyMemory P B)=1 := by
  simp only [markedRawMemorySchurWeight,markedRawBoundaryEmptyMemory,Finset.sum_const_zero,pow_zero]

theorem markedRawBoundary_weighted_source_sum
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (z₀ : Z) (v₀ : ℝ) (F : MarkedRawActive P M → ℝ) :
    (∑ s : MarkedRawState P M B Z,
      markedRawStateMass ν s*‖markedRawBoundary z₀ s‖*
        markedRawMemorySchurWeight v₀ s.2.2*F s.2.1) =
      ∑ a : MarkedRawActive P M,markedRawActiveMass ν a*F a := by
  classical
  have hterm (z : Z) (a : MarkedRawActive P M) (m : MarkedRawMemory P B) :
      markedRawStateMass ν (z,a,m)*‖markedRawBoundary z₀ (z,a,m)‖*
        markedRawMemorySchurWeight v₀ m*F a =
      if z=z₀ then (if m=markedRawBoundaryEmptyMemory P B then markedRawActiveMass ν a*F a else 0) else 0 := by
    by_cases hz : z=z₀ <;> by_cases hm : m=markedRawBoundaryEmptyMemory P B
    · subst m
      simp [markedRawBoundary,markedRawStateMass,hz,markedRawBoundaryEmptyMemory_mass,markedRawBoundaryEmptyMemory_schur]
    · simp [markedRawBoundary,hz,hm]
    · simp [markedRawBoundary,hz]
    · simp [markedRawBoundary,hz]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type,hterm]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem markedRawBoundary_norm_le_schur
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (z₀ : Z) {v₀ : ℝ} (hv₀ : 0 < v₀) (s : MarkedRawState P M B Z) :
    ‖markedRawBoundary z₀ s‖ ≤ markedRawMemorySchurWeight v₀ s.2.2 := by
  classical
  by_cases hs : s.1=z₀ ∧ s.2.2=markedRawBoundaryEmptyMemory P B
  · rw [markedRawBoundary,ite_eq_left hs,norm_one,hs.2,markedRawBoundaryEmptyMemory_schur]
  · rw [markedRawBoundary,ite_eq_right hs,norm_zero]
    exact (markedRawMemorySchurWeight_pos hv₀ _).le

end ArtinMatthews
