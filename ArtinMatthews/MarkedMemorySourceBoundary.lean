module

public import ArtinMatthews.MarkedMemoryTiltBasic
public import ArtinMatthews.MarkedRawBoundary


set_option backward.privateInPublic true
@[expose] public section

/-! Exact source-boundary summation. Initial active nu atoms remain in
the raw source measure; neither the boundary vector nor the chronological
birth coefficient absorbs them. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {M B : ℕ} {Z : Finset (ℤ × ℤ)}
  (nu : (j : J) → ↥(P j) → ℝ) (z₀ : Z)

def markedMemoryBoundarySource (a : MarkedRawActive P M) : MarkedRawState P M B Z :=
  (z₀,a,markedRawBoundaryEmptyMemory P B)

theorem markedMemoryBoundarySource_mass (a : MarkedRawActive P M) :
    markedRawStateMass nu (markedMemoryBoundarySource (B := B) z₀ a)=markedRawActiveMass nu a := by
  rw [markedMemoryBoundarySource,markedRawStateMass,markedRawBoundaryEmptyMemory_mass,mul_one]

theorem markedMemorySourceBoundary_sum (F : MarkedRawState P M B Z → ℂ) :
    (∑ s : MarkedRawState P M B Z,(markedRawStateMass nu s : ℂ)*
      star (markedRawBoundary z₀ s)*F s)=
      ∑ a : MarkedRawActive P M,(markedRawActiveMass nu a : ℂ)*F (markedMemoryBoundarySource z₀ a) := by
  have ht (z : Z) (a : MarkedRawActive P M) (m : MarkedRawMemory P B) :
      (markedRawStateMass nu (z,a,m) : ℂ)*star (markedRawBoundary z₀ (z,a,m))*F (z,a,m)=
        if z=z₀ then if m=markedRawBoundaryEmptyMemory P B then
          (markedRawActiveMass nu a : ℂ)*F (z₀,a,markedRawBoundaryEmptyMemory P B) else 0 else 0 := by
    by_cases hz : z=z₀ <;> by_cases hm : m=markedRawBoundaryEmptyMemory P B
    · subst z; subst m
      simp [markedRawBoundary,markedRawStateMass,markedRawBoundaryEmptyMemory_mass]
    · simp [markedRawBoundary,hz,hm]
    · simp [markedRawBoundary,hz,hm]
    · simp [markedRawBoundary,hz,hm]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type,ht]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rfl

theorem markedMemoryBoundarySource_tilt_normalization (V : J → ℝ) (q : ℝ) (N : ℕ)
    (a : MarkedRawActive P M)
    (hb : ∀ j k,markedMemoryBaseline q N ((a j k).1:ℕ)≠0) :
    (∏ j,∏ k,markedMemoryBaseline q N ((a j k).1:ℕ))*
        markedRawStateMass (fun j p => markedMemoryPrimeAtom (V j) q N p.1)
          (markedMemoryBoundarySource (B := B) z₀ a) =
      markedPhysicalMass V M * ∏ j,∏ k,(1/(((a j k).1:ℝ)+1)) := by
  rw [markedMemoryBoundarySource_mass]
  exact markedMemoryBaseline_rawActiveMass P V q N M a hb

end
end ArtinMatthews
