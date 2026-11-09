module

public import ArtinMatthews.MarkedMinorArcRawShiftBound
public import ArtinMatthews.MarkedMinorArcRawShiftFibers
public import ArtinMatthews.MarkedMinorArcRectangular


set_option backward.privateInPublic true
@[expose] public section

/-! Actual rectangular class-block estimates, derived from literal raw
entries and their genuine good-state geometry. No block norm is assumed. -/
namespace ArtinMatthews
open Matrix Filter
open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 1500000 in
/-- Every actual root-line/cell rectangular shift block satisfies the true
clean saving, including empty or identically zero physical blocks. There
is no factor from the number of cells, root lines, or raw backgrounds. -/
theorem marked_minor_actual_raw_shift_class_opNorm {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (hη : Function.support η ⊆ Set.Icc 1 4) (hηnorm : ∀ t, ‖η t‖ ≤ 1)
    {G H c L : ℝ} (hG : 0 < G) (hH : 1 ≤ H) (hc : 0 < c) (hL : 0 ≤ L) (N : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (q r d₀ Y ρ : ℝ)
      (w : Z → ℤ × ℤ) (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
      (bg : MarkedRawBackground (markedRawActualPrimeBand e x) pads B) (shift : ℤ)
      (key : MarkedRootLineTuple (markedRawCopiedProduct bg.1) × ℤ),
      0 ≤ q → q ≤ 1 → 0 < d₀ → 0 ≤ ρ → ρ ≤ 1 →
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → Y ≤ Real.exp (H*(Real.log x)^(1/5:ℝ)) →
      (∀ z, markedMinorIntegerDet z.1 (w z)=1) →
      (∀ z ∈ Z, c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ L) →
      (∀ s, ‖χ s‖ ≤ 1) → |shift| ≤ (N : ℤ) →
      ‖(markedRawCleanShiftCountingMatrix (markedRawActualPrimeAtom e q x) hZ ψ η r d₀ Y
        ((Real.log x)^(G+4)) ρ (markedRawFirstGoodCutoff r d₀ Y w χ) bg shift).submatrix
        (fun u : MarkedRawPositionClass (markedRawActualPrimeBand e x) hZ r d₀ Y
          (markedRawCopiedProduct bg.1) key => u.1)
        (fun v : MarkedRawPositionClass (markedRawActualPrimeBand e x) hZ r d₀ Y
          (markedRawCopiedProduct bg.1) (markedRawShiftKey shift key) => v.1)‖ ≤
        (Real.log x)^(-G) := by
  classical
  filter_upwards [marked_minor_actual_raw_shift_union_opNorm e he hinj ψ η hη hηnorm hG hH hc hL N,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hlog
  intro pads B Z hZ q r d₀ Y ρ w χ bg shift key hq₀ hq₁ hd₀ hρ₀ hρ₁ hYlo hYhi hw hτ hχ hshift
  let A := (markedRawCleanShiftCountingMatrix (markedRawActualPrimeAtom e q x) hZ ψ η r d₀ Y
    ((Real.log x)^(G+4)) ρ (markedRawFirstGoodCutoff r d₀ Y w χ) bg shift).submatrix
    (fun u : MarkedRawPositionClass (markedRawActualPrimeBand e x) hZ r d₀ Y
      (markedRawCopiedProduct bg.1) key => u.1)
    (fun v : MarkedRawPositionClass (markedRawActualPrimeBand e x) hZ r d₀ Y
      (markedRawCopiedProduct bg.1) (markedRawShiftKey shift key) => v.1)
  change ‖A‖ ≤ _
  by_cases hzero : A=0
  · rw [hzero,norm_zero]
    exact Real.rpow_nonneg (by linarith : (0:ℝ)≤Real.log x) _
  · have hex : ∃ u v, A u v ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hzero
      ext u v
      exact hn u v
    obtain ⟨u,v,huv⟩ := hex
    have hraw : markedRawCleanKernel hZ ψ η d₀ Y ((Real.log x)^(G+4)) ρ
        (markedRawFirstGoodCutoff r d₀ Y w χ) bg u.1 v.1 ≠ 0 := by
      intro hz
      apply huv
      change (Real.sqrt (markedRawLastMass (markedRawActualPrimeAtom e q x) u.1.2) : ℂ)*
        markedRawCleanShiftKernel hZ ψ η r d₀ Y ((Real.log x)^(G+4)) ρ
          (markedRawFirstGoodCutoff r d₀ Y w χ) bg shift u.1 v.1*
        (Real.sqrt (markedRawLastMass (markedRawActualPrimeAtom e q x) v.1.2) : ℂ)=0
      rw [markedRawCleanShiftKernel_class_apply,hz,mul_zero,zero_mul]
    have hlocal := hx pads B Z hZ q r d₀ Y ρ w χ bg u.1 v.1 shift
      hq₀ hq₁ hd₀ hρ₀ hρ₁ hYlo hYhi hw hτ hχ hshift hraw
    have hid := markedRawCleanShiftCountingMatrix_class_block
      (markedRawActualPrimeAtom e q x) hZ ψ η r d₀ Y ((Real.log x)^(G+4)) ρ
      (markedRawFirstGoodCutoff r d₀ Y w χ) bg shift key u
    change A=_ at hid
    rw [hid]
    exact (markedMinorRectangularSubmatrix_norm_le _ _ _
      (markedRawClassRowIntoUnion_injective hZ r d₀ Y _ key u shift)
      (markedRawClassColIntoUnion_injective hZ r d₀ Y _ key u shift)).trans hlocal

end ArtinMatthews
