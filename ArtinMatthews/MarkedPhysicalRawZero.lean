module

public import ArtinMatthews.MarkedPhysicalEdgeReindex
public import ArtinMatthews.MarkedPhysicalEndpointNormActual


set_option backward.privateInPublic true
@[expose] public section

/-! Exact empty-memory transport of the physical counting measure. The
atom is the original constant `V⁻¹`; no tilted measure is substituted. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalRawMemory_zero_eq {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) (m : MarkedRawMemory P 0) :
    m = markedPhysicalEmptyMemory P := by
  rcases m with ⟨k,m⟩
  have hk : k = (markedPhysicalEmptyMemory P).1 := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    have hj := (k.1 j).2
    simp only [markedPhysicalEmptyMemory,Fin.val_zero]
    omega
  cases hk
  congr
  funext j i
  exact Fin.elim0 i

def markedPhysicalRawZeroEquiv {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime)
    (M : ℕ) (Z : Finset (ℤ × ℤ)) :
    MarkedRawState (fun j => markedRawPrimeBand (P j)) M 0 Z ≃
      Z × MarkedPhysicalMarking P M where
  toFun s := (s.1,markedPhysicalMarkingEquiv P hP M s.2.1)
  invFun s := (s.1,(markedPhysicalMarkingEquiv P hP M).symm s.2,
    markedPhysicalEmptyMemory (fun j => markedRawPrimeBand (P j)))
  left_inv s := by
    rcases s with ⟨z,a,m⟩
    simp only [Equiv.symm_apply_apply]
    rw [markedPhysicalRawMemory_zero_eq _ m]
  right_inv s := by
    rcases s with ⟨z,a⟩
    simp only [Equiv.apply_symm_apply]

def markedPhysicalRawZeroVector {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime)
    (M : ℕ) (Z : Finset (ℤ × ℤ)) (f : MarkedPhysicalState P M Z → ℂ) :
    MarkedRawState (fun j => markedRawPrimeBand (P j)) M 0 Z → ℂ :=
  fun s => markedPhysicalStateExtend f (markedPhysicalRawZeroEquiv P hP M Z s)

theorem markedPhysicalRawZeroVector_at_state {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime)
    (M : ℕ) (Z : Finset (ℤ × ℤ)) (f : MarkedPhysicalState P M Z → ℂ)
    (s : MarkedPhysicalState P M Z) :
    markedPhysicalRawZeroVector P hP M Z f (markedPhysicalStateToRaw P hP M Z s) = f s := by
  simp only [markedPhysicalRawZeroVector,markedPhysicalRawZeroEquiv,
    markedPhysicalStateToRaw,Equiv.coe_fn_mk,Equiv.apply_symm_apply]
  exact dite_eq_left s.2

theorem markedPhysicalRawZero_mass {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (M : ℕ) (Z : Finset (ℤ × ℤ))
    (s : MarkedRawState (fun j => markedRawPrimeBand (P j)) M 0 Z) :
    markedRawStateMass (fun j _ => (V j)⁻¹) s = markedPhysicalMass V M := by
  unfold markedRawStateMass
  rw [markedPhysicalRawMemory_zero_eq _ s.2.2,markedPhysicalEmptyMemory_mass,mul_one]
  exact (markedPhysicalMass_eq_rawActiveMass _ V M s.2.1).symm

theorem markedPhysicalRawZeroVector_energy {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime)
    (V : J → ℝ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (f : MarkedPhysicalState P M Z → ℂ) :
    (∑ s : MarkedRawState (fun j => markedRawPrimeBand (P j)) M 0 Z,
      markedRawStateMass (fun j _ => (V j)⁻¹) s *
        ‖markedPhysicalRawZeroVector P hP M Z f s‖^2) =
      ∑ s : MarkedPhysicalState P M Z,markedPhysicalMass V M*‖f s‖^2 := by
  simp only [markedPhysicalRawZero_mass,markedPhysicalRawZeroVector]
  rw [Equiv.sum_comp (markedPhysicalRawZeroEquiv P hP M Z)
    (fun s => markedPhysicalMass V M*‖markedPhysicalStateExtend f s‖^2)]
  exact Finset.sum_congr_set
    {s : Z × MarkedPhysicalMarking P M | MarkedPhysicalStateCondition s.1.1 s.2}
    (fun s => markedPhysicalMass V M*‖markedPhysicalStateExtend f s‖^2)
    (fun s => markedPhysicalMass V M*‖f s‖^2)
    (fun s hs => by
      change MarkedPhysicalStateCondition s.1.1 s.2 at hs
      simp only [markedPhysicalStateExtend,dite_eq_left hs])
    (fun s hs => by
      change ¬MarkedPhysicalStateCondition s.1.1 s.2 at hs
      simp only [markedPhysicalStateExtend,dite_eq_right hs,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero])

def markedPhysicalRawEndpoint {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime)
    (M : ℕ) (Z : Finset (ℤ × ℤ)) (α β : ℕ → ℂ) :=
  markedPhysicalRawZeroVector P hP M Z
    (fun s => markedPhysicalEndpointVector P M α β s.1.1.1)

theorem markedPhysicalRawEndpoint_energy {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime)
    (V : J → ℝ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (α β : ℕ → ℂ) :
    (∑ s : MarkedRawState (fun j => markedRawPrimeBand (P j)) M 0 Z,
      markedRawStateMass (fun j _ => (V j)⁻¹) s *
        ‖markedPhysicalRawEndpoint P hP M Z α β s‖^2) =
      markedPhysicalEndpointEnergy P M Z V α β :=
  markedPhysicalRawZeroVector_energy P hP V M Z _

end ArtinMatthews
