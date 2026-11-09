module

public import ArtinMatthews.MarkedMinorArcRawCleanAction
public import ArtinMatthews.MarkedMinorArcRawGoodFirst
public import ArtinMatthews.MarkedMinorArcRawLinePartition
public import ArtinMatthews.MarkedMinorArcActualCleanBlock


set_option backward.privateInPublic true
@[expose] public section

/-! The literal clean raw-edge kernel before removal-error restoration of
the cross-edge ban. Copied slots, pending damping, physical distinctness,
cutoffs, determinant divisibility and pad dyad are all retained. -/
namespace ArtinMatthews
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

/-- The physical full-list distinctness test, with all numeric prime values
retained by their typed-band membership. -/
def MarkedRawActiveDistinct {J : Type*} {P : J → Finset Nat.Primes} {M : ℕ}
    (a : MarkedRawActive P M) : Prop := ∀ j, Function.Injective (a j)

/-- The actual clean pending damping and physical endpoint projection. The
remaining endpoint tests are kept as the literal arbitrary multiplierχ. -/
noncomputable def markedRawEndpointFactor {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ρ : ℝ) (χ : MarkedRawState P M B Z → ℂ)
    (s : MarkedRawState P M B Z) : ℂ := by
  classical
  exact if MarkedRawActiveDistinct s.2.1 then
    ((ρ^(markedRawPendingHits s.2.2 s.1.1 (hZ _ s.1.2)) : ℝ) : ℂ)*χ s else 0

theorem markedRawEndpointFactor_norm_le {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (χ : MarkedRawState P M B Z → ℂ) (hχ : ∀ s, ‖χ s‖ ≤ 1) (s : MarkedRawState P M B Z) :
    ‖markedRawEndpointFactor hZ ρ χ s‖ ≤ 1 := by
  classical
  unfold markedRawEndpointFactor
  split_ifs
  · rw [norm_mul]
    exact (mul_le_mul (markedRawPendingDamping_norm_le s.2.2 s.1.1 (hZ _ s.1.2) hρ₀ hρ₁)
      (hχ s) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  · simp

/-- Every actual numeric unshared product, with no artificial support cutoff. -/
noncomputable def markedRawProductSupport {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset Nat.Primes) : Finset ℤ := by
  classical
  exact Finset.univ.image (fun last : (j : J) → ↥(P j) => (markedRawLastProduct last : ℤ))

noncomputable def markedRawProductMap {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {Z : Finset (ℤ × ℤ)}
    (u : MarkedRawCleanFiber P Z) : Z × ↥(markedRawProductSupport P) :=
  (u.1,⟨(markedRawLastProduct u.2 : ℤ),Finset.mem_image.mpr ⟨u.2,Finset.mem_univ _,rfl⟩⟩)

/-- Literal geometry of the source no-store/no-promote rule. Its only
remaining joint restriction, the cross-edge ban, is restored separately. -/
noncomputable def markedRawCleanKernel {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (b : MarkedRawBackground P pads B) : Matrix (MarkedRawCleanFiber P Z) (MarkedRawCleanFiber P Z) ℂ := by
  classical
  exact fun u v =>
    let D := markedRawCopiedProduct b.1
    let t := markedMinorIntegerDet u.1.1 v.1.1/(D : ℤ)
    if d₀ ≤ (D : ℝ) ∧ (D : ℝ) < 2*d₀ then
      if (D : ℤ) ∣ markedMinorIntegerDet u.1.1 v.1.1 then
        ((d₀/(D : ℝ) : ℝ) : ℂ)*
          markedRawEndpointFactor hZ ρ χ ((markedRawStateSplit pads B Z).symm (b,u))*
          η ((markedRawLastProduct u.2 : ℝ)/Y)*η ((markedRawLastProduct v.2 : ℝ)/Y)*
          ψ ((t : ℝ)/Y)*
          (∫ θ : AddCircle (1:ℝ) in (markedMinorCircleMajor Q Y)ᶜ,
            fourier (t-(markedRawLastProduct u.2 : ℤ)+(markedRawLastProduct v.2 : ℤ)) θ
              ∂AddCircle.haarAddCircle)*
          markedRawEndpointFactor hZ ρ χ ((markedRawStateSplit pads B Z).symm (b,v))
      else 0
    else 0

/-- Exact entry formula of the already checked unnormalized product kernel. -/
theorem markedMinorActualCleanRawMatrix_apply (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (D : ℕ) {Y : ℝ} (hY : 0 < Y) (Q : ℝ) (Z : Finset (ℤ × ℤ)) (S : Finset ℤ)
    (u v : Z × S) :
    markedMinorActualCleanRawMatrix ψ η D Y Q Z S u v=
      η ((u.2.1 : ℝ)/Y)*η ((v.2.1 : ℝ)/Y)*
      ψ (((markedMinorIntegerDet u.1.1 v.1.1/(D : ℤ) : ℤ) : ℝ)/Y)*
        (∫ θ : AddCircle (1:ℝ) in (markedMinorCircleMajor Q Y)ᶜ,
          fourier (markedMinorIntegerDet u.1.1 v.1.1/(D : ℤ)-u.2.1+v.2.1) θ ∂AddCircle.haarAddCircle) := by
  unfold markedMinorActualCleanRawMatrix markedMinorEndpointMatrix markedMinorPositionCleanProductMatrix
  change η ((u.2.1 : ℝ)/Y) * ((Y : ℂ) * (((Y : ℂ)⁻¹) *
      ψ (((markedMinorIntegerDet u.1.1 v.1.1/(D : ℤ) : ℤ) : ℝ)/Y) *
        (∫ θ : AddCircle (1:ℝ) in (markedMinorCircleMajor Q Y)ᶜ,
          fourier (markedMinorIntegerDet u.1.1 v.1.1/(D : ℤ)-u.2.1+v.2.1) θ ∂AddCircle.haarAddCircle))) *
      η ((v.2.1 : ℝ)/Y) = _
  field_simp [show (Y : ℂ) ≠ 0 by exact_mod_cast hY.ne']

/-- Actual raw clean entries are exactly bounded endpoint factors around the
checked literal numeric-product kernel; no analytic estimate is assumed. -/
theorem markedRawCleanKernel_factor {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (hY : 0 < Y) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (b : MarkedRawBackground P pads B) (u v : MarkedRawCleanFiber P Z) :
    markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ b u v=
      if d₀ ≤ (markedRawCopiedProduct b.1 : ℝ) ∧ (markedRawCopiedProduct b.1 : ℝ) < 2*d₀ then
        if (markedRawCopiedProduct b.1 : ℤ) ∣ markedMinorIntegerDet u.1.1 v.1.1 then
          ((d₀/(markedRawCopiedProduct b.1 : ℝ) : ℝ) : ℂ)*
            markedRawEndpointFactor hZ ρ χ ((markedRawStateSplit pads B Z).symm (b,u))*
            markedMinorActualCleanRawMatrix ψ η (markedRawCopiedProduct b.1) Y Q Z (markedRawProductSupport P)
              (markedRawProductMap u) (markedRawProductMap v)*
            markedRawEndpointFactor hZ ρ χ ((markedRawStateSplit pads B Z).symm (b,v))
        else 0 else 0 := by
  classical
  dsimp only [markedRawCleanKernel]
  split_ifs
  · rw [markedMinorActualCleanRawMatrix_apply ψ η _ hY]
    simp only [markedRawProductMap,Int.cast_natCast]
    ring
  · rfl
  · rfl

/-- The literal shared-determinant gate is precisely the actual line-block
gate in the raw state, with no omitted congruence or support hypothesis. -/
theorem markedRawCleanKernel_line_gate {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (b : MarkedRawBackground P pads B)
    (hD : Squarefree (markedRawCopiedProduct b.1)) (u v : MarkedRawCleanFiber P Z) :
    ((markedRawCopiedProduct b.1 : ℤ) ∣ markedMinorIntegerDet u.1.1 v.1.1) ↔
      markedRawPositionLineTuple (markedRawCopiedProduct b.1) u.1.1 (hZ _ u.1.2)=
        markedRawPositionLineTuple (markedRawCopiedProduct b.1) v.1.1 (hZ _ v.1.2) :=
  (markedRawPositionLineTuple_eq_iff hD _ _ (hZ _ u.1.2) (hZ _ v.1.2)).symm

end ArtinMatthews
