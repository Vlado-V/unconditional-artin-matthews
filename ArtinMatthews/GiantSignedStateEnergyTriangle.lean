module

public import ArtinMatthews.GiantSignedStatePairingEnergy
public import ArtinMatthews.GiantSignedStateFiniteSumEnergy
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Adding the two signed parts adds their norm bounds on the original
state space, including all unbounded factorial-memory degrees. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {M : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

theorem giantSignedStatePairing_add_right
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (w f g : GiantSignedState PS PB M → ℂ)
    (hw : giantSignedStateEnergy PS ν w ≠ ∞)
    (hf : giantSignedStateEnergy PS ν f ≠ ∞) (hg : giantSignedStateEnergy PS ν g ≠ ∞) :
    giantSignedStatePairing PS ν w (fun s => f s + g s) =
      giantSignedStatePairing PS ν w f + giantSignedStatePairing PS ν w g := by
  have hsf := giantSignedStatePairing_summable PS hVS ν hν w f hw hf
  have hsg := giantSignedStatePairing_summable PS hVS ν hν w g hw hg
  have hs : Summable (fun s => (giantSignedStateMass PS ν s : ℂ) * star (w s) * (f s + g s)) := by
    simpa only [mul_add] using hsf.add hsg
  rw [giantSignedStatePairing_eq_tsum PS ν w (fun s => f s + g s) hs,
    giantSignedStatePairing_eq_tsum PS ν w f hsf, giantSignedStatePairing_eq_tsum PS ν w g hsg]
  simp only [mul_add]
  exact hsf.tsum_add hsg

private theorem norm_le_iff_weighted_square (z : ℂ) {C : ℝ} (hC : 0 ≤ C)
    {e₁ e₂ : ℝ≥0∞} (h₁ : e₁ ≠ ∞) (h₂ : e₂ ≠ ∞) :
    ‖z‖ ≤ C * Real.sqrt e₁.toReal * Real.sqrt e₂.toReal ↔
      ENNReal.ofReal (‖z‖ ^ 2) ≤ ENNReal.ofReal (C ^ 2) * e₁ * e₂ := by
  have hfin : ENNReal.ofReal (C ^ 2) * e₁ * e₂ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h₁) h₂
  rw [← ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfin,
    ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg _), ← sq_le_sq₀ (norm_nonneg z)
      (mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)),
    mul_pow, mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg, Real.sq_sqrt ENNReal.toReal_nonneg]

theorem giantSignedStateEnergy_add_bound
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (w f g : GiantSignedState PS PB M → ℂ)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hf : giantSignedStateEnergy PS ν f ≤ ENNReal.ofReal (A ^ 2) * giantSignedStateEnergy PS ν w)
    (hg : giantSignedStateEnergy PS ν g ≤ ENNReal.ofReal (D ^ 2) * giantSignedStateEnergy PS ν w) :
    giantSignedStateEnergy PS ν (fun s => f s + g s) ≤
      ENNReal.ofReal ((A + D) ^ 2) * giantSignedStateEnergy PS ν w := by
  let F (i : Fin 2) := if i = 0 then f else g
  have he : giantSignedStateEnergy PS ν (fun s => f s + g s) ≤
      2 * (giantSignedStateEnergy PS ν f + giantSignedStateEnergy PS ν g) := by
    simpa [F, Fin.sum_univ_two] using giantSignedStateEnergy_sum_le PS hVS ν hν F
  by_cases hw : giantSignedStateEnergy PS ν w = ∞
  · by_cases hzero : A + D = 0
    · have hA0 : A = 0 := by linarith
      have hD0 : D = 0 := by linarith
      have hf0 : giantSignedStateEnergy PS ν f = 0 :=
        le_antisymm (by simpa only [hA0, zero_pow (by decide : 2 ≠ 0),
          ENNReal.ofReal_zero, zero_mul] using hf) zero_le
      have hg0 : giantSignedStateEnergy PS ν g = 0 :=
        le_antisymm (by simpa only [hD0, zero_pow (by decide : 2 ≠ 0),
          ENNReal.ofReal_zero, zero_mul] using hg) zero_le
      simpa only [hf0, hg0, hzero, zero_add, mul_zero, zero_pow (by decide : 2 ≠ 0),
        ENNReal.ofReal_zero, zero_mul] using he
    · have hpos : ENNReal.ofReal ((A+D)^2) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (lt_of_le_of_ne (add_nonneg hA hD) (Ne.symm hzero)))).ne'
      rw [hw, ENNReal.mul_top hpos]
      exact le_top
  have hff := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hw) hf
  have hgg := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hw) hg
  have hsum : giantSignedStateEnergy PS ν (fun s => f s + g s) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ he
    exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.add_ne_top.mpr ⟨hff, hgg⟩)
  apply giantSignedStateEnergy_le_of_pairing PS hVS ν hν (fun s => f s + g s) hsum
  intro v hv
  let Ev := giantSignedStateEnergy PS ν v
  let Ew := giantSignedStateEnergy PS ν w
  have h1 : ‖giantSignedStatePairing PS ν v f‖ ≤
      A * Real.sqrt Ew.toReal * Real.sqrt Ev.toReal := by
    apply (norm_le_iff_weighted_square _ hA hw hv).mpr
    calc
      _ ≤ Ev * giantSignedStateEnergy PS ν f :=
        giantSignedStatePairing_energy PS hVS ν hν v f hv hff
      _ ≤ Ev * (ENNReal.ofReal (A ^ 2) * Ew) := mul_le_mul_right hf Ev
      _ = ENNReal.ofReal (A ^ 2) * Ew * Ev := mul_comm _ _
  have h2 : ‖giantSignedStatePairing PS ν v g‖ ≤
      D * Real.sqrt Ew.toReal * Real.sqrt Ev.toReal := by
    apply (norm_le_iff_weighted_square _ hD hw hv).mpr
    calc
      _ ≤ Ev * giantSignedStateEnergy PS ν g :=
        giantSignedStatePairing_energy PS hVS ν hν v g hv hgg
      _ ≤ Ev * (ENNReal.ofReal (D ^ 2) * Ew) := mul_le_mul_right hg Ev
      _ = ENNReal.ofReal (D ^ 2) * Ew * Ev := mul_comm _ _
  apply (norm_le_iff_weighted_square _ (add_nonneg hA hD) hw hv).mp
  rw [giantSignedStatePairing_add_right PS hVS ν hν v f g hv hff hgg]
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by rw [← add_mul, ← add_mul]))

end
end ArtinMatthews
