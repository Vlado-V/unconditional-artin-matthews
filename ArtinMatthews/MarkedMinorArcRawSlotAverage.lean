module

public import ArtinMatthews.MarkedMinorArcRawCleanAction
public import Mathlib.Analysis.Normed.Lp.PiLp


set_option backward.privateInPublic true
@[expose] public section

/-! The actual independent uniform slot-permutation operator on full raw
states, preserving the true factorial-weighted physical measure. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators

/-- Literal source slot permutation, preserving positions and every pending index. -/
def markedRawActiveSlotEquiv {J : Type*} {P : J → Finset Nat.Primes} {M : ℕ}
    (σ : (j : J) → Equiv.Perm (Fin M)) : MarkedRawActive P M ≃ MarkedRawActive P M where
  toFun a j k := a j (σ j k)
  invFun a j k := a j ((σ j).symm k)
  left_inv a := by funext j k; simp
  right_inv a := by funext j k; simp

def markedRawSlotEquiv {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {M B : ℕ}
    {Z : Finset (ℤ × ℤ)} (σ : (j : J) → Equiv.Perm (Fin M)) :
    MarkedRawState P M B Z ≃ MarkedRawState P M B Z :=
  Equiv.prodCongr (Equiv.refl Z)
    (Equiv.prodCongr (markedRawActiveSlotEquiv σ) (Equiv.refl (MarkedRawMemory P B)))

theorem markedRawActiveMass_slots {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) {M : ℕ} (σ : (j : J) → Equiv.Perm (Fin M))
    (a : MarkedRawActive P M) : markedRawActiveMass ν (markedRawActiveSlotEquiv σ a)=markedRawActiveMass ν a := by
  unfold markedRawActiveMass markedRawActiveSlotEquiv
  apply Finset.prod_congr rfl
  intro j _
  exact Equiv.prod_comp (σ j) (fun k => ν j (a j k))

/-- The actual full physical measure is invariant under every source slot permutation. -/
theorem markedRawStateMass_slots {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (σ : (j : J) → Equiv.Perm (Fin M)) (s : MarkedRawState P M B Z) :
    markedRawStateMass ν (markedRawSlotEquiv σ s)=markedRawStateMass ν s := by
  change markedRawActiveMass ν (markedRawActiveSlotEquiv σ s.2.1)*markedRawMemoryMass ν s.2.2=_
  rw [markedRawActiveMass_slots]
  rfl

/-- Literal probability average over independent permutations in all groups. -/
noncomputable def markedRawSlotAverage {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (f : MarkedRawState P M B Z → ℂ) (s : MarkedRawState P M B Z) : ℂ :=
  ((Fintype.card ((j : J) → Equiv.Perm (Fin M)) : ℂ)⁻¹)*
    ∑ σ : (j : J) → Equiv.Perm (Fin M), f (markedRawSlotEquiv σ s)

/-- Every individual slot permutation preserves the actual weighted energy,
with all background factorials and zero atoms retained. -/
theorem markedRawSlotEquiv_energy {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) {M B : ℕ}
    {Z : Finset (ℤ × ℤ)} (σ : (j : J) → Equiv.Perm (Fin M)) (f : MarkedRawState P M B Z → ℂ) :
    (∑ s : MarkedRawState P M B Z, markedRawStateMass ν s*‖f (markedRawSlotEquiv σ s)‖^2) =
      ∑ s : MarkedRawState P M B Z, markedRawStateMass ν s*‖f s‖^2 := by
  classical
  have hh := Equiv.sum_comp (markedRawSlotEquiv σ)
    (fun s : MarkedRawState P M B Z => markedRawStateMass ν s*‖f s‖^2)
  simpa only [markedRawStateMass_slots] using hh

set_option maxHeartbeats 1000000 in
/-- The source uniform slot average is a contraction for the actual raw
weighted L² energy, not just for an auxiliary counting-space kernel. -/
theorem markedRawSlotAverage_energy_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (f : MarkedRawState P M B Z → ℂ) :
    (∑ s : MarkedRawState P M B Z, markedRawStateMass ν s*‖markedRawSlotAverage f s‖^2) ≤
      ∑ s : MarkedRawState P M B Z, markedRawStateMass ν s*‖f s‖^2 := by
  classical
  let State := MarkedRawState P M B Z
  let Slots := (j : J) → Equiv.Perm (Fin M)
  let N := Fintype.card Slots
  let v : EuclideanSpace ℂ State := WithLp.toLp 2 (markedWeightedCountingVector (markedRawStateMass ν) f)
  let T : Slots → EuclideanSpace ℂ State ≃ₗᵢ[ℂ] EuclideanSpace ℂ State :=
    fun σ => LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (markedRawSlotEquiv σ).symm
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero (α := Slots))
  have hN₀ : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hnorm : ‖((N : ℂ)⁻¹) • ∑ σ : Slots, T σ v‖ ≤ ‖v‖ := by
    rw [norm_smul,norm_inv,Complex.norm_natCast]
    calc
      _ ≤ (N : ℝ)⁻¹ * ∑ σ : Slots, ‖T σ v‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hN₀)
      _ = (N : ℝ)⁻¹*((N : ℝ)*‖v‖) := by
        congr 1
        simp only [LinearIsometryEquiv.norm_map, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rfl
      _ = _ := by field_simp
  have hvec : ((N : ℂ)⁻¹) • ∑ σ : Slots, T σ v =
      WithLp.toLp 2 (markedWeightedCountingVector (markedRawStateMass ν) (markedRawSlotAverage f)) := by
    apply PiLp.ext
    intro s
    simp only [PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul]
    change (N : ℂ)⁻¹*(∑ σ : Slots, (Real.sqrt (markedRawStateMass ν (markedRawSlotEquiv σ s)) : ℂ)*f (markedRawSlotEquiv σ s)) = _
    simp only [markedRawStateMass_slots]
    unfold markedWeightedCountingVector markedRawSlotAverage
    rw [← Finset.mul_sum]
    dsimp only [N,Slots]
    ring
  rw [hvec] at hnorm
  have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm
  rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq] at hs
  change (∑ i, ‖markedWeightedCountingVector (markedRawStateMass ν) (markedRawSlotAverage f) i‖^2) ≤
    (∑ i, ‖markedWeightedCountingVector (markedRawStateMass ν) f i‖^2) at hs
  rw [markedWeightedCountingVector_energy _ (markedRawStateMass_nonneg ν hν),
    markedWeightedCountingVector_energy _ (markedRawStateMass_nonneg ν hν)] at hs
  exact hs

end ArtinMatthews
