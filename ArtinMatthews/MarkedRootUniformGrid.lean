module

public import ArtinMatthews.MarkedRootBoxGridTube
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! A literal finite closed grid on [0,1]×[1,16]×[1,2]. Its bad-face cells
are bounded by the derived moving-face tube, not by an assumed grid estimate. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory
attribute [local instance] Classical.propDecidable

abbrev MarkedRootGridIndex (N : ℕ) := Fin N × (Fin (15*N) × Fin N)

def markedRootGridCell (N : ℕ) (i : MarkedRootGridIndex N) : Set (ℝ × (ℝ × ℝ)) :=
  {p | p.1 ∈ Set.Icc ((i.1 : ℝ)/N) (((i.1 : ℝ)+1)/N) ∧
    p.2.1 ∈ Set.Icc (1+(i.2.1 : ℝ)/N) (1+((i.2.1 : ℝ)+1)/N) ∧
    p.2.2 ∈ Set.Icc (1+(i.2.2 : ℝ)/N) (1+((i.2.2 : ℝ)+1)/N)}

theorem markedRootGrid_interval_bounds (N k i : ℕ) (hN : 0 < N) (hi : i < k*N)
    (s x : ℝ) (hx : x ∈ Set.Icc (s+(i:ℝ)/N) (s+((i:ℝ)+1)/N)) :
    x ∈ Set.Icc s (s+k) := by
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hN
  have hlo : 0 ≤ (i:ℝ)/N := div_nonneg (Nat.cast_nonneg i) hNr.le
  have hi' : (i:ℝ)+1 ≤ (k:ℝ)*N := by exact_mod_cast (show i+1 ≤ k*N by omega)
  have hhi : ((i:ℝ)+1)/N ≤ (k:ℝ) := (div_le_iff₀ hNr).mpr hi'
  exact ⟨by linarith [hx.1],by linarith [hx.2]⟩

theorem markedRootGrid_interval_close (N i : ℕ) (s x y : ℝ)
    (hx : x ∈ Set.Icc (s+(i:ℝ)/N) (s+((i:ℝ)+1)/N))
    (hy : y ∈ Set.Icc (s+(i:ℝ)/N) (s+((i:ℝ)+1)/N)) :
    |x-y| ≤ 1/(N:ℝ) := by
  have hw : ((i:ℝ)+1)/N-(i:ℝ)/N = 1/(N:ℝ) := by ring
  apply abs_le.mpr
  constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]

theorem markedRootGrid_interval_cover (N k : ℕ) (hN : 0 < N) (hk : 0 < k)
    (s x : ℝ) (hx : x ∈ Set.Icc s (s+k)) :
    ∃ i : ℕ,i < k*N ∧ x ∈ Set.Icc (s+(i:ℝ)/N) (s+((i:ℝ)+1)/N) := by
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hN
  have hkn : 0 < k*N := Nat.mul_pos hk hN
  let t := (x-s)*(N:ℝ)
  have ht : 0 ≤ t := mul_nonneg (sub_nonneg.mpr hx.1) hNr.le
  let i := min ⌊t⌋₊ (k*N-1)
  have hi : i < k*N := (min_le_right _ _).trans_lt (by omega)
  refine ⟨i,hi,?_,?_⟩
  · have hie : (i:ℝ) ≤ t := (Nat.cast_le.mpr (min_le_left _ _)).trans (Nat.floor_le ht)
    have hh : (i:ℝ)/(N:ℝ) ≤ x-s := (div_le_iff₀ hNr).mpr hie
    linarith
  · by_cases hf : ⌊t⌋₊ ≤ k*N-1
    · have hie : i = ⌊t⌋₊ := min_eq_left hf
      have hh : t < (i:ℝ)+1 := by rw [hie]; exact Nat.lt_floor_add_one t
      dsimp only [t] at hh
      have hdiv : x-s < ((i:ℝ)+1)/(N:ℝ) := (lt_div_iff₀ hNr).mpr hh
      linarith
    · have hie : i = k*N-1 := min_eq_right (le_of_not_ge hf)
      have hip : i+1=k*N := by rw [hie]; omega
      have hipr : (i:ℝ)+1=(k:ℝ)*N := by exact_mod_cast hip
      rw [hipr,mul_div_cancel_right₀ _ hNr.ne']
      exact hx.2

theorem markedRootGridCell_subset (N : ℕ) (hN : 0 < N) (i : MarkedRootGridIndex N) :
    markedRootGridCell N i ⊆ markedRootBoxDomain := by
  intro p hp
  have hr := markedRootGrid_interval_bounds N 1 i.1 hN (by simpa only [one_mul] using i.1.isLt)
    0 p.1 (by simpa only [zero_add] using hp.1)
  have ha := markedRootGrid_interval_bounds N 15 i.2.1 hN i.2.1.isLt 1 p.2.1 hp.2.1
  have hb := markedRootGrid_interval_bounds N 1 i.2.2 hN (by simpa only [one_mul] using i.2.2.isLt)
    1 p.2.2 hp.2.2
  exact ⟨by simpa using hr,by norm_num at ha ⊢; exact ha,by norm_num at hb ⊢; exact hb⟩

theorem markedRootGridCell_close (N : ℕ) (i : MarkedRootGridIndex N)
    (p q : ℝ × (ℝ × ℝ)) (hp : p ∈ markedRootGridCell N i) (hq : q ∈ markedRootGridCell N i) :
    MarkedRootBoxClose (1/(N:ℝ)) p q := by
  exact ⟨markedRootGrid_interval_close N i.1 0 p.1 q.1
      (by simpa only [zero_add] using hp.1) (by simpa only [zero_add] using hq.1),
    markedRootGrid_interval_close N i.2.1 1 p.2.1 q.2.1 hp.2.1 hq.2.1,
    markedRootGrid_interval_close N i.2.2 1 p.2.2 q.2.2 hp.2.2 hq.2.2⟩

theorem markedRootGridCell_cover (N : ℕ) (hN : 0 < N) {p : ℝ × (ℝ × ℝ)}
    (hp : p ∈ markedRootBoxDomain) : ∃ i : MarkedRootGridIndex N,p ∈ markedRootGridCell N i := by
  obtain ⟨r,hr,hrp⟩ := markedRootGrid_interval_cover N 1 hN (by decide) 0 p.1 (by simpa using hp.1)
  obtain ⟨a,ha,hap⟩ := markedRootGrid_interval_cover N 15 hN (by decide) 1 p.2.1 (by convert hp.2.1 using 1; norm_num)
  obtain ⟨b,hb,hbp⟩ := markedRootGrid_interval_cover N 1 hN (by decide) 1 p.2.2 (by convert hp.2.2 using 1; norm_num)
  refine ⟨(⟨r,by simpa using hr⟩,⟨a,ha⟩,⟨b,by simpa using hb⟩),?_,hap,hbp⟩
  simpa only [zero_add] using hrp

theorem markedRootGridIndex_card (N : ℕ) : Fintype.card (MarkedRootGridIndex N) = 15*N^3 := by
  simp only [MarkedRootGridIndex,Fintype.card_prod,Fintype.card_fin]
  ring

def markedRootBadGridIndices (N : ℕ) (U V : ℝ) (z : Fin 2 → ℝ) : Finset (MarkedRootGridIndex N) :=
  Finset.univ.filter (fun i => ∃ q ∈ markedRootGridCell N i,q ∈ markedRootPhysicalBoxBoundary U V z)

def markedRootBadGridUnion (N : ℕ) (U V : ℝ) (z : Fin 2 → ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  ⋃ i ∈ markedRootBadGridIndices N U V z,markedRootGridCell N i

theorem markedRootBadGridUnion_measure_le (N : ℕ) (hN : 0 < N)
    {U V H : ℝ} (hUV : 1 ≤ U*V) (hH : 0 ≤ H) (hsmall : 20*H/(N:ℝ) ≤ 1/2)
    (z : Fin 2 → ℝ) (hz : ∀ i,|z i| ≤ H) :
    markedNormalizedRootMeasure (markedRootBadGridUnion N U V z) ≤ ENNReal.ofReal (40960*H/(N:ℝ)) := by
  have hsub : markedRootBadGridUnion N U V z ⊆
      markedRootBoxBoundaryGridCover U V z (1/(N:ℝ)) := by
    intro p hp
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
    obtain ⟨hi,hp⟩ := Set.mem_iUnion.mp hi
    unfold markedRootBadGridIndices at hi
    obtain ⟨q,hq,hface⟩ := (Finset.mem_filter.mp hi).2
    exact ⟨markedRootGridCell_subset N hN i hp,q,markedRootGridCell_subset N hN i hq,hface,
      markedRootGridCell_close N i p q hp hq⟩
  apply (measure_mono hsub).trans
  simpa only [one_div,div_eq_mul_inv,mul_assoc,one_mul] using
    markedRootBoxBoundaryGridCover_measure_le hH (by positivity : 0 ≤ 1/(N:ℝ)) hUV
      (by simpa only [one_div,div_eq_mul_inv,mul_assoc,one_mul] using hsmall) z hz

end ArtinMatthews
