module

public import ArtinMatthews.MarkedMemoryCopiedSlotGeometry
public import ArtinMatthews.MarkedPhysicalEndpointDamping


set_option backward.privateInPublic true
@[expose] public section

/-! Exact weighted quotient of the compatible slot decorations. Arbitrary
ordered-state tests remain transported explicitly. Position/pending
observables and the actual physical endpoint vector give concrete
constant-fiber coefficients, with both slot normalizations retained. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section SlotFamilies
variable {J : Type*} {I : J → Type*} {pads : ℕ}
  (src dst : (j : J) → Fin (pads+1) ↪ I j) (out inc : J → Fin (pads+1))

abbrev MarkedMemorySlotFamilyFiber := (j : J) → MarkedMemorySlotPairFiber (src j) (dst j) (out j) (inc j)

def markedMemorySlotFamilySource (pair : MarkedMemorySlotFamilyFiber src dst out inc) :
    J → Equiv.Perm (Fin (pads+1)) := fun j => (pair j).1.1

def markedMemorySlotFamilyTargetInverse (pair : MarkedMemorySlotFamilyFiber src dst out inc) :
    J → Equiv.Perm (Fin (pads+1)) := fun j => (pair j).1.2.symm

theorem markedMemorySlotFamilySource_last (pair : MarkedMemorySlotFamilyFiber src dst out inc) (j : J) :
    markedMemorySlotFamilySource src dst out inc pair j (Fin.last pads) = out j := (pair j).2.1

theorem markedMemorySlotFamilyTargetInverse_last (pair : MarkedMemorySlotFamilyFiber src dst out inc) (j : J) :
    markedMemorySlotFamilyTargetInverse src dst out inc pair j (Fin.last pads) = inc j := by
  apply (pair j).1.2.injective
  change (pair j).1.2 ((pair j).1.2.symm (Fin.last pads)) = (pair j).1.2 (inc j)
  rw [Equiv.apply_symm_apply, (pair j).2.2.1]

variable [Fintype J] [DecidableEq J] [∀ j, DecidableEq (I j)]

theorem markedMemorySlotFamilyFiber_card
    (hremaining : ∀ j, (markedMemoryBirthBatch (src j)).erase (src j (out j)) =
      (markedMemoryBirthBatch (dst j)).erase (dst j (inc j))) :
    Fintype.card (MarkedMemorySlotFamilyFiber src dst out inc) = pads.factorial ^ Fintype.card J := by
  rw [Fintype.card_pi]
  simp_rw [markedMemorySlotPairFiber_card _ _ _ _ (hremaining _)]
  exact Finset.prod_const _
end SlotFamilies

section RawCoefficient
variable {J : Type*} [Fintype J] [DecidableEq J] {I : J → Type*}
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
  (src dst : (j : J) → Fin (pads+1) ↪ I j) (out inc : J → Fin (pads+1))

theorem markedRawEdgeJointCoefficient_slotFiber_core
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (s t : MarkedRawState P (pads+1) B Z) (pair : MarkedMemorySlotFamilyFiber src dst out inc) :
    markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ (fun _ => 1)
      (markedRawSlotEquiv (markedMemorySlotFamilySource src dst out inc pair) s)
      (markedRawSlotEquiv (markedMemorySlotFamilyTargetInverse src dst out inc pair) t) =
    markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ (fun _ => 1)
      (markedRawSlotEquiv (fun j => Equiv.swap (Fin.last pads) (out j)) s)
      (markedRawSlotEquiv (fun j => Equiv.swap (Fin.last pads) (inc j)) t) := by
  apply markedRawEdgeJointCoefficient_slots_core
  · intro j
    rw [markedMemorySlotFamilySource_last, Equiv.swap_apply_left]
  · intro j
    rw [markedMemorySlotFamilyTargetInverse_last, Equiv.swap_apply_left]

/-- No arbitrary observable is silently made symmetric: the two original
tests are still evaluated on the corresponding permuted states. -/
theorem markedRawEdgeJointCoefficient_slotFiber_tests
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s t : MarkedRawState P (pads+1) B Z) (pair : MarkedMemorySlotFamilyFiber src dst out inc) :
    markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ
      (markedRawSlotEquiv (markedMemorySlotFamilySource src dst out inc pair) s)
      (markedRawSlotEquiv (markedMemorySlotFamilyTargetInverse src dst out inc pair) t) =
    markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ (fun _ => 1)
      (markedRawSlotEquiv (fun j => Equiv.swap (Fin.last pads) (out j)) s)
      (markedRawSlotEquiv (fun j => Equiv.swap (Fin.last pads) (inc j)) t) *
      χ (markedRawSlotEquiv (markedMemorySlotFamilySource src dst out inc pair) s) *
      χ (markedRawSlotEquiv (markedMemorySlotFamilyTargetInverse src dst out inc pair) t) := by
  rw [markedRawEdgeJointCoefficient_test_factor hZ ψ η d₀ Y Q ρ χ,
    markedRawEdgeJointCoefficient_slotFiber_core hZ src dst out inc]

theorem markedRawEdgeJointCoefficient_slotFiber_positionMemory
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (F : Z → MarkedRawMemory P B → ℂ)
    (s t : MarkedRawState P (pads+1) B Z) (pair : MarkedMemorySlotFamilyFiber src dst out inc) :
    markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ (fun u => F u.1 u.2.2)
      (markedRawSlotEquiv (markedMemorySlotFamilySource src dst out inc pair) s)
      (markedRawSlotEquiv (markedMemorySlotFamilyTargetInverse src dst out inc pair) t) =
    markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ (fun u => F u.1 u.2.2)
      (markedRawSlotEquiv (fun j => Equiv.swap (Fin.last pads) (out j)) s)
      (markedRawSlotEquiv (fun j => Equiv.swap (Fin.last pads) (inc j)) t) := by
  apply markedRawEdgeJointCoefficient_slots_positionMemory
  · intro j
    rw [markedMemorySlotFamilySource_last, Equiv.swap_apply_left]
  · intro j
    rw [markedMemorySlotFamilyTargetInverse_last, Equiv.swap_apply_left]

variable [∀ j, DecidableEq (I j)]

omit [∀ j, DecidableEq (I j)] in
/-- Arbitrary tests and label observables stay inside their exact finite
fiber sum; only the literal physical core is extracted. -/
theorem markedRawEdgeJointCoefficient_slotFiber_test_sum
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s t : MarkedRawState P (pads+1) B Z) :
    (∑ pair : MarkedMemorySlotFamilyFiber src dst out inc,
      (Fintype.card (J → Equiv.Perm (Fin (pads+1))) : ℂ)⁻¹ *
        markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ
          (markedRawSlotEquiv (markedMemorySlotFamilySource src dst out inc pair) s)
          (markedRawSlotEquiv (markedMemorySlotFamilyTargetInverse src dst out inc pair) t) *
        (Fintype.card (J → Equiv.Perm (Fin (pads+1))) : ℂ)⁻¹) =
      (Fintype.card (J → Equiv.Perm (Fin (pads+1))) : ℂ)⁻¹ *
        markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ (fun _ => 1)
          (markedRawSlotEquiv (fun j => Equiv.swap (Fin.last pads) (out j)) s)
          (markedRawSlotEquiv (fun j => Equiv.swap (Fin.last pads) (inc j)) t) *
        (Fintype.card (J → Equiv.Perm (Fin (pads+1))) : ℂ)⁻¹ *
        ∑ pair : MarkedMemorySlotFamilyFiber src dst out inc,
          χ (markedRawSlotEquiv (markedMemorySlotFamilySource src dst out inc pair) s) *
          χ (markedRawSlotEquiv (markedMemorySlotFamilyTargetInverse src dst out inc pair) t) := by
  simp_rw [markedRawEdgeJointCoefficient_slotFiber_tests hZ src dst out inc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair _
  ring

omit [∀ j, DecidableEq (I j)] in
/-- An additional endpoint observable is retained at the actual ordered
states. This includes the original target test in an edge operator. -/
theorem markedRawEdgeJointCoefficient_slotFiber_observable_sum
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (G : MarkedRawState P (pads+1) B Z → MarkedRawState P (pads+1) B Z → ℂ)
    (s t : MarkedRawState P (pads+1) B Z) :
    (∑ pair : MarkedMemorySlotFamilyFiber src dst out inc,
      (Fintype.card (J → Equiv.Perm (Fin (pads+1))) : ℂ)⁻¹ *
        markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ
          (markedRawSlotEquiv (markedMemorySlotFamilySource src dst out inc pair) s)
          (markedRawSlotEquiv (markedMemorySlotFamilyTargetInverse src dst out inc pair) t) *
        (Fintype.card (J → Equiv.Perm (Fin (pads+1))) : ℂ)⁻¹ *
        G (markedRawSlotEquiv (markedMemorySlotFamilySource src dst out inc pair) s)
          (markedRawSlotEquiv (markedMemorySlotFamilyTargetInverse src dst out inc pair) t)) =
      (Fintype.card (J → Equiv.Perm (Fin (pads+1))) : ℂ)⁻¹ *
        markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ (fun _ => 1)
          (markedRawSlotEquiv (fun j => Equiv.swap (Fin.last pads) (out j)) s)
          (markedRawSlotEquiv (fun j => Equiv.swap (Fin.last pads) (inc j)) t) *
        (Fintype.card (J → Equiv.Perm (Fin (pads+1))) : ℂ)⁻¹ *
        ∑ pair : MarkedMemorySlotFamilyFiber src dst out inc,
          χ (markedRawSlotEquiv (markedMemorySlotFamilySource src dst out inc pair) s) *
          χ (markedRawSlotEquiv (markedMemorySlotFamilyTargetInverse src dst out inc pair) t) *
          G (markedRawSlotEquiv (markedMemorySlotFamilySource src dst out inc pair) s)
            (markedRawSlotEquiv (markedMemorySlotFamilyTargetInverse src dst out inc pair) t) := by
  simp_rw [markedRawEdgeJointCoefficient_slotFiber_tests hZ src dst out inc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair _
  ring

theorem markedRawEdgeJointCoefficient_slotFiber_weighted_sum
    (hremaining : ∀ j, (markedMemoryBirthBatch (src j)).erase (src j (out j)) =
      (markedMemoryBirthBatch (dst j)).erase (dst j (inc j)))
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (F : Z → MarkedRawMemory P B → ℂ) (s t : MarkedRawState P (pads+1) B Z) :
    (∑ pair : MarkedMemorySlotFamilyFiber src dst out inc,
      (Fintype.card (J → Equiv.Perm (Fin (pads+1))) : ℂ)⁻¹ *
        markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ (fun u => F u.1 u.2.2)
          (markedRawSlotEquiv (markedMemorySlotFamilySource src dst out inc pair) s)
          (markedRawSlotEquiv (markedMemorySlotFamilyTargetInverse src dst out inc pair) t) *
        (Fintype.card (J → Equiv.Perm (Fin (pads+1))) : ℂ)⁻¹) =
      ((pads.factorial : ℂ) ^ Fintype.card J /
        (((pads+1).factorial : ℂ) ^ Fintype.card J)^2) *
      markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ (fun u => F u.1 u.2.2)
        (markedRawSlotEquiv (fun j => Equiv.swap (Fin.last pads) (out j)) s)
        (markedRawSlotEquiv (fun j => Equiv.swap (Fin.last pads) (inc j)) t) := by
  simp_rw [markedRawEdgeJointCoefficient_slotFiber_positionMemory hZ src dst out inc]
  rw [Finset.sum_const, Finset.card_univ, markedMemorySlotFamilyFiber_card src dst out inc hremaining,
    nsmul_eq_mul]
  simp only [Fintype.card_fun, Fintype.card_perm, Fintype.card_fin, Nat.cast_pow, div_eq_mul_inv]
  ring
end RawCoefficient

end
end ArtinMatthews
