module

public import ArtinMatthews.MarkedMemoryHistoryLifespanScalarResidual
public import ArtinMatthews.MarkedMemoryMeasureRescale


set_option backward.privateInPublic true
@[expose] public section

/-! The arithmetic part of an actual chronological history is independent
of its edge kernels. Initial atoms are not included here: they belong to
the source measure. All ghost signs, old-memory charges and birth
factorials are retained. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)

def markedMemoryHistoryArithmeticWeight (qStage : ℕ → ℝ) (offset : ℕ)
    {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) : ℝ :=
  markedMemoryHistoryPrimeMass ν V hZ H *
    (markedMemoryHistoryGhostScalarProduct hZ H qStage offset /
      markedMemoryHistoryBirthFactorials hZ H)

omit [DecidableEq J] in
theorem markedMemoryHistoryPrimeMass_zero (s : MarkedRawState P (pads+1) B Z)
    (H : MarkedMemoryGhostChoice hZ s) :
    markedMemoryHistoryPrimeMass ν V hZ (n := 0) H=
      ∏ b : MarkedMemoryGhostBirthIndex H,V b.1*ν b.1 (H.births b.1 b.2) := by
  unfold markedMemoryHistoryPrimeMass
  rw [markedMemoryHistoryPromotionMass_zero V hZ s H,mul_one]
  rfl

omit [DecidableEq J] in
theorem markedMemoryHistoryPrimeMass_succ {n : ℕ}
    {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ (n+1) s) :
    markedMemoryHistoryPrimeMass ν V hZ H=
      (∏ b : MarkedMemoryGhostBirthIndex H.1,V b.1*ν b.1 (H.1.births b.1 b.2))*
      markedRawEdgeChoicePrimeMass ν V hZ
        (markedRawSlotEquiv H.2.1.1 (markedMemoryGhostChoiceTarget hZ s H.1)) H.2.1.2.1 *
      markedMemoryHistoryPrimeMass ν V hZ H.2.2 := by
  rw [markedMemoryHistoryPrimeMass,markedMemoryHistoryBirthMass_succ,
    markedMemoryHistoryPromotionMass_succ,markedMemoryEdgeChoicePrimeMass_split]
  unfold markedMemoryHistoryPrimeMass
  ring

omit [DecidableEq J] in
theorem markedMemoryHistoryArithmeticWeight_zero (qStage : ℕ → ℝ) (offset : ℕ)
    (s : MarkedRawState P (pads+1) B Z) (H : MarkedMemoryGhostChoice hZ s) :
    (markedMemoryHistoryArithmeticWeight ν V hZ qStage offset (n := 0) H:ℂ)=
      markedMemoryGhostChoiceWeight ν V (qStage offset) 1 hZ s H := by
  change ((markedMemoryHistoryPrimeMass ν V hZ (n := 0) H *
    (markedMemoryHistoryGhostScalarProduct hZ (n := 0) H qStage offset /
      markedMemoryHistoryBirthFactorials hZ (n := 0) H):ℝ):ℂ)=_
  rw [markedMemoryHistoryPrimeMass_zero ν V hZ s H,
    markedMemoryHistoryGhostScalarProduct_zero hZ s H,
    markedMemoryHistoryBirthFactorials_zero hZ s H,
    markedMemoryGhostChoiceWeight_prime_factor ν V hZ (qStage offset) s H,
    markedMemoryGhostResidual_scalar hZ s H (qStage offset)]
  push_cast
  rfl

omit [DecidableEq J] in
theorem markedMemoryHistoryArithmeticWeight_succ (qStage : ℕ → ℝ) (offset : ℕ)
    {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ (n+1) s) :
    (markedMemoryHistoryArithmeticWeight ν V hZ qStage offset H:ℂ)=
      markedMemoryGhostChoiceWeight ν V (qStage offset) 1 hZ s H.1 *
      (markedRawEdgeChoicePrimeMass ν V hZ
        (markedRawSlotEquiv H.2.1.1 (markedMemoryGhostChoiceTarget hZ s H.1)) H.2.1.2.1:ℂ)*
      (markedMemoryHistoryArithmeticWeight ν V hZ qStage (offset+1) H.2.2:ℂ) := by
  rw [markedMemoryHistoryArithmeticWeight,markedMemoryHistoryPrimeMass_succ,
    markedMemoryHistoryGhostScalarProduct_succ,markedMemoryHistoryBirthFactorials_succ,
    markedMemoryGhostChoiceWeight_prime_factor,markedMemoryGhostResidual_scalar]
  unfold markedMemoryHistoryArithmeticWeight
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem markedMemoryChronologicalWeight_arithmetic
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
    (qStage : ℕ → ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (n offset : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q 1 qStage χ n offset H=
      (markedMemoryHistoryArithmeticWeight ν V hZ qStage offset H:ℂ)*
        markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n offset H := by
  rw [markedMemoryChronologicalWeight_prime_factor,markedMemoryHistoryResidual_ghostScalar]
  unfold markedMemoryHistoryArithmeticWeight
  push_cast
  ring

omit [DecidableEq J] in
theorem markedMemoryHistoryArithmeticWeight_rescale (hV : ∀ j,V j≠0)
    (qStage : ℕ → ℝ) (n offset : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryHistoryArithmeticWeight ν V hZ qStage offset H=
      (∏ j,(V j)⁻¹)^n *
        markedMemoryHistoryArithmeticWeight (markedMemoryScaledAtoms ν V) (fun _ => 1)
          hZ qStage offset H := by
  apply Complex.ofReal_injective
  induction n generalizing offset s with
  | zero =>
    simpa only [pow_zero,one_mul] using
      (markedMemoryHistoryArithmeticWeight_zero ν V hZ qStage offset s H).trans
        ((markedMemoryGhostChoiceWeight_rescale ν V (qStage offset) 1 hZ s H).trans
          (markedMemoryHistoryArithmeticWeight_zero (markedMemoryScaledAtoms ν V) (fun _ => 1)
            hZ qStage offset s H).symm)
  | succ n ih =>
    rw [Complex.ofReal_mul,Complex.ofReal_pow,
      markedMemoryHistoryArithmeticWeight_succ,markedMemoryHistoryArithmeticWeight_succ,
      markedMemoryGhostChoiceWeight_rescale ν V,
      markedMemoryRawEdgePrimeMass_rescale ν V hV,ih]
    push_cast
    rw [pow_succ]
    ring

end
end ArtinMatthews
