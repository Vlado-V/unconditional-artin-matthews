module

public import ArtinMatthews.MarkedMinorArcRawCleanKernel
public import ArtinMatthews.MarkedMinorArcBanRawCollision
public import ArtinMatthews.MarkedMinorArcBanAdjoint
public import ArtinMatthews.MarkedMinorArcBanError


set_option backward.privateInPublic true
@[expose] public section

/-! The literal clean raw-state ban coefficient, before taking rows or columns. -/
noncomputable section
namespace ArtinMatthews

open Matrix

def markedRawBanSourceActive {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (bg : MarkedRawBackground P pads B) (u : MarkedRawCleanFiber P Z) :
    MarkedRawActive P (pads+1) := ((markedRawStateSplit pads B Z).symm (bg,u)).2.1

theorem markedRawBanSourceActive_eq_snoc {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (bg : MarkedRawBackground P pads B) (u : MarkedRawCleanFiber P Z) :
    markedRawBanSourceActive bg u = fun j => Fin.snoc (bg.1 j) (u.2 j) := rfl

def MarkedRawCleanBan {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (bg : MarkedRawBackground P pads B)
    (u v : MarkedRawCleanFiber P Z) : Prop := MarkedRawFullCrossBan (markedRawBanSourceActive bg u) v.2

def markedRawBannedCleanKernel {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (K : MarkedRawBackground P pads B → Matrix (MarkedRawCleanFiber P Z) (MarkedRawCleanFiber P Z) ℂ)
    (bg : MarkedRawBackground P pads B) : Matrix (MarkedRawCleanFiber P Z) (MarkedRawCleanFiber P Z) ℂ := by
  classical
  exact fun u v => if MarkedRawCleanBan bg u v then 0 else K bg u v

def markedRawBanErrorKernel {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ) (bg : MarkedRawBackground P pads B) :
    Matrix (MarkedRawCleanFiber P Z) (MarkedRawCleanFiber P Z) ℂ :=
  fun u v => markedBanRemovedCoefficient (MarkedRawCleanBan bg u v)
    (markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ bg u v)

theorem markedRawBanErrorKernel_eq_difference {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ) (bg : MarkedRawBackground P pads B) :
    markedRawBanErrorKernel hZ ψ η d₀ Y Q ρ χ bg = markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ bg-
      markedRawBannedCleanKernel (markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ) bg := rfl

def markedRawBanPrefactor {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (η : ℝ → ℂ) (d₀ Y ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (bg : MarkedRawBackground P pads B) (u v : MarkedRawCleanFiber P Z) : ℂ :=
  ((d₀/(markedRawCopiedProduct bg.1:ℝ):ℝ):ℂ)*
    markedRawEndpointFactor hZ ρ χ ((markedRawStateSplit pads B Z).symm (bg,u))*
    η ((markedRawLastProduct u.2:ℝ)/Y)*η ((markedRawLastProduct v.2:ℝ)/Y)*
    markedRawEndpointFactor hZ ρ χ ((markedRawStateSplit pads B Z).symm (bg,v))

theorem markedBanRemovedCoefficient_mul (bad : Prop) (c d : ℂ) :
    markedBanRemovedCoefficient bad (c*d)=c*markedBanRemovedCoefficient bad d := by
  classical
  by_cases h : bad <;> simp [markedBanRemovedCoefficient,h]

theorem markedRawBanErrorKernel_entry_factor {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ) (bg : MarkedRawBackground P pads B)
    (u v : MarkedRawCleanFiber P Z) :
    markedRawBanErrorKernel hZ ψ η d₀ Y Q ρ χ bg u v =
      if d₀ ≤ (markedRawCopiedProduct bg.1:ℝ) ∧ (markedRawCopiedProduct bg.1:ℝ)<2*d₀ then
        if (markedRawCopiedProduct bg.1:ℤ) ∣ markedMinorIntegerDet u.1.1 v.1.1 then
          markedRawBanPrefactor hZ η d₀ Y ρ χ bg u v *
            markedBanRemovedCoefficient (MarkedRawCleanBan bg u v)
              (markedBanEdgeKernel ψ Q Y (markedRawLastProduct u.2:ℤ) (markedRawLastProduct v.2:ℤ)
                (markedBanNormalizedDet u.1.1 (markedRawCopiedProduct bg.1:ℤ) v.1.1))
        else 0 else 0 := by
  classical
  unfold markedRawBanErrorKernel markedRawCleanKernel
  dsimp only
  split_ifs
  · rw [← markedBanRemovedCoefficient_mul]
    congr 1
    rw [← markedBan_edge_minor_identity]
    unfold markedRawBanPrefactor markedBanNormalizedDet
    ring
  · simp [markedBanRemovedCoefficient]
  · simp [markedBanRemovedCoefficient]

theorem markedRawBanPrefactor_norm_le {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (η : ℝ → ℂ) (d₀ Y : ℝ) {ρ H : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hH : 0 ≤ H)
    (hη : ∀ u, ‖η u‖ ≤ H) (χ : MarkedRawState P (pads+1) B Z → ℂ) (hχ : ∀ s, ‖χ s‖ ≤ 1)
    (bg : MarkedRawBackground P pads B) (u v : MarkedRawCleanFiber P Z)
    (hdyad : d₀ ≤ (markedRawCopiedProduct bg.1:ℝ) ∧ (markedRawCopiedProduct bg.1:ℝ)<2*d₀) :
    ‖markedRawBanPrefactor hZ η d₀ Y ρ χ bg u v‖ ≤ H^2 := by
  have hD : 0 < (markedRawCopiedProduct bg.1:ℝ) := by exact_mod_cast markedRawCopiedProduct_pos bg.1
  have hd₀ : 0 ≤ d₀ := by linarith [hdyad.2]
  have hscale : ‖((d₀/(markedRawCopiedProduct bg.1:ℝ):ℝ):ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_of_nonneg (div_nonneg hd₀ hD.le)]
    exact (div_le_one hD).mpr hdyad.1
  have hsource := markedRawEndpointFactor_norm_le hZ hρ₀ hρ₁ χ hχ
    ((markedRawStateSplit pads B Z).symm (bg,u))
  have htarget := markedRawEndpointFactor_norm_le hZ hρ₀ hρ₁ χ hχ
    ((markedRawStateSplit pads B Z).symm (bg,v))
  unfold markedRawBanPrefactor
  simp only [norm_mul]
  calc
    _ ≤ 1*1*H*H*1 := by gcongr <;> first | exact hscale | exact hsource | exact htarget | apply hη
    _ = _ := by ring

theorem markedRawBanErrorKernel_entry_norm_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q : ℝ) {ρ H : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hH : 0 ≤ H)
    (hη : ∀ u, ‖η u‖ ≤ H) (χ : MarkedRawState P (pads+1) B Z → ℂ) (hχ : ∀ s, ‖χ s‖ ≤ 1)
    (bg : MarkedRawBackground P pads B) (u v : MarkedRawCleanFiber P Z) :
    ‖markedRawBanErrorKernel hZ ψ η d₀ Y Q ρ χ bg u v‖ ≤
      H^2*(if (markedRawCopiedProduct bg.1:ℤ) ∣ markedMinorIntegerDet u.1.1 v.1.1 then
        ‖markedBanRemovedCoefficient (MarkedRawCleanBan bg u v)
          (markedBanEdgeKernel ψ Q Y (markedRawLastProduct u.2:ℤ) (markedRawLastProduct v.2:ℤ)
            (markedBanNormalizedDet u.1.1 (markedRawCopiedProduct bg.1:ℤ) v.1.1))‖ else 0) := by
  classical
  rw [markedRawBanErrorKernel_entry_factor]
  by_cases hd : d₀ ≤ (markedRawCopiedProduct bg.1:ℝ) ∧ (markedRawCopiedProduct bg.1:ℝ)<2*d₀
  · rw [ite_eq_left hd]
    split_ifs
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (markedRawBanPrefactor_norm_le hZ η d₀ Y hρ₀ hρ₁ hH hη χ hχ bg u v hd)
        (norm_nonneg _)
    · simp
  · rw [ite_eq_right hd]
    split_ifs <;> simp only [norm_zero, mul_zero]
    · exact mul_nonneg (sq_nonneg H) (norm_nonneg _)
    · exact le_rfl

end ArtinMatthews
