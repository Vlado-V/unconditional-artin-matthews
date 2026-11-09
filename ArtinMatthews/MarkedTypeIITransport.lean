module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-!
# Exact transport of root ratios in the determinant lift

The real root matrix in PD §3.4 is `[[u,ur],[v,vr+1/u]]`. Its action and
the transported complement ratio are explicit. These formulas prove the
derivative and injectivity used to control archimedean test boundaries.
They do not assume or prove the root-residue equidistribution estimate.
-/

namespace ArtinMatthews

noncomputable section

def markedVectorDet (z w : Fin 2 → ℝ) : ℝ := z 0 * w 1 - z 1 * w 0

def markedTau (r : ℝ) (z : Fin 2 → ℝ) : ℝ := z 0 + r * z 1

/-- Action of the exact real root matrix on a two-dimensional vector. -/
def markedRootTransport (u v r : ℝ) (z : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![u * markedTau r z, v * markedTau r z + z 1 / u]

@[simp] theorem markedRootTransport_first (u v r : ℝ) (z : Fin 2 → ℝ) :
    markedRootTransport u v r z 0 = u * markedTau r z := rfl

@[simp] theorem markedRootTransport_second (u v r : ℝ) (z : Fin 2 → ℝ) :
    markedRootTransport u v r z 1 = v * markedTau r z + z 1 / u := rfl

/-- The transported determinant is unchanged because the root matrix has determinant one. -/
theorem markedRootTransport_det {u : ℝ} (hu : u ≠ 0) (v r : ℝ)
    (z w : Fin 2 → ℝ) :
    markedVectorDet (markedRootTransport u v r z) (markedRootTransport u v r w) =
      markedVectorDet z w := by
  unfold markedVectorDet
  simp only [markedRootTransport_first, markedRootTransport_second]
  unfold markedTau
  field_simp
  ring

/-- The ratio of the first coordinates of the transported complement and vector. -/
def markedTransportedRatio (r : ℝ) (z w : Fin 2 → ℝ) : ℝ :=
  markedTau r w / markedTau r z

theorem markedTransportedRatio_eq_first_ratio {u : ℝ} (hu : u ≠ 0)
    (v r : ℝ) (z w : Fin 2 → ℝ) :
    markedTransportedRatio r z w =
      markedRootTransport u v r w 0 / markedRootTransport u v r z 0 := by
  simp only [markedRootTransport_first, markedTransportedRatio]
  rw [mul_div_mul_left _ _ hu]

/-- The cross-multiplied difference of two transported ratios. -/
theorem markedTau_cross_difference (r s : ℝ) (z w : Fin 2 → ℝ) :
    markedTau r w * markedTau s z - markedTau s w * markedTau r z =
      markedVectorDet z w * (r - s) := by
  unfold markedTau markedVectorDet
  ring

/-- A nondegenerate completion ratio has no repeated value away from its pole. -/
theorem markedTransportedRatio_injective {z w : Fin 2 → ℝ}
    (hdet : markedVectorDet z w ≠ 0) {r s : ℝ}
    (hr : markedTau r z ≠ 0) (hs : markedTau s z ≠ 0)
    (heq : markedTransportedRatio r z w = markedTransportedRatio s z w) : r = s := by
  have hcross := (div_eq_div_iff hr hs).mp heq
  have hzero : markedVectorDet z w * (r - s) = 0 := by
    rw [← markedTau_cross_difference]
    exact sub_eq_zero.mpr hcross
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hdet)

theorem markedTau_hasDerivAt (r : ℝ) (z : Fin 2 → ℝ) :
    HasDerivAt (fun t => markedTau t z) (z 1) r := by
  simpa [markedTau] using ((hasDerivAt_id r).mul_const (z 1)).const_add (z 0)

/-- The exact derivative of the root-ratio Möbius transformation. -/
theorem markedTransportedRatio_hasDerivAt (r : ℝ) (z w : Fin 2 → ℝ)
    (hz : markedTau r z ≠ 0) :
    HasDerivAt (fun t => markedTransportedRatio t z w)
      (markedVectorDet z w / (markedTau r z) ^ 2) r := by
  convert (markedTau_hasDerivAt r w).div (markedTau_hasDerivAt r z) hz using 1
  · rfl
  · unfold markedVectorDet markedTau
    congr 1
    ring

/-- For an integral complement of determinant one this is the positive derivative
`1 / τ(z)^2` used in the source's boundary budget. -/
theorem markedTransportedRatio_hasDerivAt_of_det_one (r : ℝ) (z w : Fin 2 → ℝ)
    (hdet : markedVectorDet z w = 1) (hz : markedTau r z ≠ 0) :
    HasDerivAt (fun t => markedTransportedRatio t z w)
      (1 / (markedTau r z) ^ 2) r := by
  simpa only [hdet] using markedTransportedRatio_hasDerivAt r z w hz

/-- A positive lower bound for `τ(z)` uniformly controls the derivative. -/
theorem markedTransportedRatio_deriv_le (r : ℝ) (z w : Fin 2 → ℝ)
    (hdet : markedVectorDet z w = 1) {c : ℝ} (hc : 0 < c)
    (hz : c ≤ markedTau r z) :
    0 < deriv (fun t => markedTransportedRatio t z w) r ∧
      deriv (fun t => markedTransportedRatio t z w) r ≤ 1 / c ^ 2 := by
  have hz0 : markedTau r z ≠ 0 := ne_of_gt (hc.trans_le hz)
  rw [(markedTransportedRatio_hasDerivAt_of_det_one r z w hdet hz0).deriv]
  refine ⟨by positivity, ?_⟩
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hc.le hz 2)

end

end ArtinMatthews
