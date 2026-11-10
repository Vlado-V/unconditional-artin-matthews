module

public import ArtinMatthews.MarkedTypeIITransport
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import ArtinMatthews.MarkedRootAffineStrip
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Actual normalized box-face tubes for the determinant-one root matrix.
The transverse slopes come from the positive first-coordinate box. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory

def markedNormalizedRootMeasure : Measure (ℝ × (ℝ × ℝ)) :=
  (volume.restrict (Set.Icc (0:ℝ) 1)).prod
    ((volume.restrict (Set.Icc (1:ℝ) 16)).prod (volume.restrict (Set.Icc (1:ℝ) 2)))

def markedRootBoxFirst (z : Fin 2 → ℝ) (p : ℝ × (ℝ × ℝ)) : ℝ :=
  p.2.1*markedTau p.1 z

def markedRootBoxSecond (U V : ℝ) (z : Fin 2 → ℝ) (p : ℝ × (ℝ × ℝ)) : ℝ :=
  p.2.2*markedTau p.1 z+z 1/(U*V*p.2.1)

def markedRootFirstFace (z : Fin 2 → ℝ) (c ε : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  {p | |markedRootBoxFirst z p-c| ≤ ε}

def markedRootSecondFace (U V : ℝ) (z : Fin 2 → ℝ) (c ε : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  {p | (1/2:ℝ) ≤ markedRootBoxFirst z p ∧ |markedRootBoxSecond U V z p-c| ≤ ε}

def markedRootBoxFaceTube (U V : ℝ) (z : Fin 2 → ℝ) (ε : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  ((markedRootFirstFace z 1 ε ∪ markedRootFirstFace z 16 ε) ∪
    markedRootSecondFace U V z 1 ε) ∪ markedRootSecondFace U V z 2 ε

theorem markedRootBoxFirst_transport {U : ℝ} (hU : U ≠ 0)
    (V r a b : ℝ) (z : Fin 2 → ℝ) :
    markedRootBoxFirst z (r,a,b) = markedRootTransport (U*a) (V*b) r z 0/U := by
  simp only [markedRootBoxFirst,markedRootTransport_first]
  field_simp

theorem markedRootBoxSecond_transport {U V a : ℝ} (hU : U ≠ 0) (hV : V ≠ 0) (ha : a ≠ 0)
    (r b : ℝ) (z : Fin 2 → ℝ) :
    markedRootBoxSecond U V z (r,a,b) = markedRootTransport (U*a) (V*b) r z 1/V := by
  simp only [markedRootBoxSecond,markedRootTransport_second]
  field_simp

theorem markedRootFirstFace_measurable (z : Fin 2 → ℝ) (c ε : ℝ) :
    MeasurableSet (markedRootFirstFace z c ε) := by
  unfold markedRootFirstFace markedRootBoxFirst markedTau
  measurability

theorem markedRootSecondFace_measurable (U V : ℝ) (z : Fin 2 → ℝ) (c ε : ℝ) :
    MeasurableSet (markedRootSecondFace U V z c ε) := by
  unfold markedRootSecondFace markedRootBoxFirst markedRootBoxSecond markedTau
  measurability

theorem markedRootFirstFace_measure_le (z : Fin 2 → ℝ) {c ε : ℝ}
    (hc : 1 ≤ c) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1/2) :
    markedNormalizedRootMeasure (markedRootFirstFace z c ε) ≤ ENNReal.ofReal (64*ε) := by
  unfold markedNormalizedRootMeasure
  rw [Measure.prod_apply (markedRootFirstFace_measurable z c ε)]
  calc
    _ ≤ ∫⁻ _r : ℝ,ENNReal.ofReal (64*ε) ∂volume.restrict (Set.Icc (0:ℝ) 1) := by
      apply lintegral_mono
      intro r
      dsimp only
      have he : Prod.mk r ⁻¹' markedRootFirstFace z c ε =
          {a : ℝ | |a*markedTau r z-c| ≤ ε} ×ˢ (Set.univ : Set ℝ) := by
        ext p
        simp only [Set.mem_preimage,markedRootFirstFace,Set.mem_ofPred_eq,markedRootBoxFirst,
          Set.mem_prod,Set.mem_univ,and_true]
      have hb : (volume.restrict (Set.Icc (1:ℝ) 2)) Set.univ = 1 := by
        simp only [Measure.restrict_apply_univ,Real.volume_Icc]
        norm_num
      rw [he,Measure.prod_prod,hb,mul_one]
      exact markedRoot_first_face_slice hc hε₀ hε₁
    _ = _ := by
      rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc]
      norm_num

theorem markedRootSecondFace_measure_le (U V : ℝ) (z : Fin 2 → ℝ) (c : ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) :
    markedNormalizedRootMeasure (markedRootSecondFace U V z c ε) ≤ ENNReal.ofReal (960*ε) := by
  unfold markedNormalizedRootMeasure
  rw [Measure.prod_apply (markedRootSecondFace_measurable U V z c ε)]
  calc
    _ ≤ ∫⁻ _r : ℝ,ENNReal.ofReal (960*ε) ∂volume.restrict (Set.Icc (0:ℝ) 1) := by
      apply lintegral_mono
      intro r
      dsimp only
      rw [Measure.prod_apply ((markedRootSecondFace_measurable U V z c ε).preimage measurable_prodMk_left)]
      calc
        _ ≤ ∫⁻ _a : ℝ,ENNReal.ofReal (64*ε) ∂volume.restrict (Set.Icc (1:ℝ) 16) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with a ha
          by_cases hx : (1/2:ℝ) ≤ a*markedTau r z
          · have he : Prod.mk a ⁻¹' (Prod.mk r ⁻¹' markedRootSecondFace U V z c ε) =
                {b : ℝ | |markedTau r z*b+z 1/(U*V*a)-c| ≤ ε} := by
              ext b
              simp only [Set.mem_preimage,markedRootSecondFace,Set.mem_ofPred_eq,
                markedRootBoxFirst,markedRootBoxSecond,hx,true_and,mul_comm]
            rw [he]
            apply (Measure.restrict_apply_le _ _).trans
            exact markedRoot_affine_strip_volume_le (markedRoot_first_box_slope ha hx) hε
          · have he : Prod.mk a ⁻¹' (Prod.mk r ⁻¹' markedRootSecondFace U V z c ε) = ∅ := by
              ext b
              simp only [Set.mem_preimage,markedRootSecondFace,Set.mem_ofPred_eq,
                markedRootBoxFirst,hx,false_and,Set.mem_empty_iff_false]
            rw [he,measure_empty]
            positivity
        _ = _ := by
          rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc]
          norm_num
          ring
    _ = _ := by
      rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc]
      norm_num

theorem markedRootBoxFaceTube_measure_le (U V : ℝ) (z : Fin 2 → ℝ) {ε : ℝ}
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1/2) :
    markedNormalizedRootMeasure (markedRootBoxFaceTube U V z ε) ≤ ENNReal.ofReal (2048*ε) := by
  unfold markedRootBoxFaceTube
  calc
    _ ≤ ((markedNormalizedRootMeasure (markedRootFirstFace z 1 ε)+
        markedNormalizedRootMeasure (markedRootFirstFace z 16 ε))+
        markedNormalizedRootMeasure (markedRootSecondFace U V z 1 ε))+
        markedNormalizedRootMeasure (markedRootSecondFace U V z 2 ε) :=
      (measure_union_le _ _).trans (add_le_add
        ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
    _ ≤ (ENNReal.ofReal (64*ε)+ENNReal.ofReal (64*ε))+ENNReal.ofReal (960*ε)+ENNReal.ofReal (960*ε) := by
      gcongr
      · exact markedRootFirstFace_measure_le z (by norm_num) hε₀ hε₁
      · exact markedRootFirstFace_measure_le z (by norm_num) hε₀ hε₁
      · exact markedRootSecondFace_measure_le U V z 1 hε₀
      · exact markedRootSecondFace_measure_le U V z 2 hε₀
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 64*ε) (by positivity : 0 ≤ 64*ε),
        ← ENNReal.ofReal_add (by positivity : 0 ≤ 64*ε+64*ε) (by positivity : 0 ≤ 960*ε),
        ← ENNReal.ofReal_add (by positivity : 0 ≤ 64*ε+64*ε+960*ε) (by positivity : 0 ≤ 960*ε)]
      congr 1
      ring

end ArtinMatthews
