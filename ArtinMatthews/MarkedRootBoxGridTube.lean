module

public import ArtinMatthews.MarkedRootBoxLipschitz
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


set_option backward.privateInPublic true
@[expose] public section

/-! Every normalized grid cell meeting a true transported box face lies in
an explicit face tube. Its volume is derived from the transport formulas. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory

def markedRootPhysicalBoxBoundary (U V : ℝ) (z : Fin 2 → ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  {q | ((markedRootBoxFirst z q=1 ∨ markedRootBoxFirst z q=16) ∧
      markedRootBoxSecond U V z q ∈ Set.Icc (1:ℝ) 2) ∨
    (markedRootBoxFirst z q ∈ Set.Icc (1:ℝ) 16 ∧
      (markedRootBoxSecond U V z q=1 ∨ markedRootBoxSecond U V z q=2))}

def markedRootBoxBoundaryGridCover (U V : ℝ) (z : Fin 2 → ℝ) (h : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  {p | p ∈ markedRootBoxDomain ∧ ∃ q ∈ markedRootBoxDomain,
    q ∈ markedRootPhysicalBoxBoundary U V z ∧ MarkedRootBoxClose h p q}

theorem markedRootBoxBoundaryGridCover_subset {H h U V : ℝ}
    (hH : 0 ≤ H) (hh : 0 ≤ h) (hUV : 1 ≤ U*V) (hsmall : 20*H*h ≤ 1/2)
    (z : Fin 2 → ℝ) (hz : ∀ i,|z i| ≤ H) :
    markedRootBoxBoundaryGridCover U V z h ⊆ markedRootBoxFaceTube U V z (20*H*h) := by
  rintro p ⟨hp,q,hq,hface,hpq⟩
  have hpos : 0 ≤ H*h := mul_nonneg hH hh
  have hfirst : |markedRootBoxFirst z p-markedRootBoxFirst z q| ≤ 20*H*h :=
    (markedRootBoxFirst_lipschitz hH hh z hz p q hp hq hpq).trans (by nlinarith)
  have hsecond : |markedRootBoxSecond U V z p-markedRootBoxSecond U V z q| ≤ 20*H*h :=
    (markedRootBoxSecond_lipschitz hH hh hUV z hz p q hp hq hpq).trans (by nlinarith)
  rcases hface with ⟨hf,_⟩ | ⟨hf,hg⟩
  · rcases hf with hf | hf
    · exact Or.inl (Or.inl (Or.inl (by simpa only [markedRootFirstFace,Set.mem_ofPred_eq,hf] using hfirst)))
    · exact Or.inl (Or.inl (Or.inr (by simpa only [markedRootFirstFace,Set.mem_ofPred_eq,hf] using hfirst)))
  · have hx : (1/2:ℝ) ≤ markedRootBoxFirst z p := by
      nlinarith [(abs_le.mp hfirst).1,hf.1]
    rcases hg with hg | hg
    · exact Or.inl (Or.inr ⟨hx,by simpa only [hg] using hsecond⟩)
    · exact Or.inr ⟨hx,by simpa only [hg] using hsecond⟩

theorem markedRootBoxBoundaryGridCover_measure_le {H h U V : ℝ}
    (hH : 0 ≤ H) (hh : 0 ≤ h) (hUV : 1 ≤ U*V) (hsmall : 20*H*h ≤ 1/2)
    (z : Fin 2 → ℝ) (hz : ∀ i,|z i| ≤ H) :
    markedNormalizedRootMeasure (markedRootBoxBoundaryGridCover U V z h) ≤
      ENNReal.ofReal (40960*H*h) := by
  apply (measure_mono (markedRootBoxBoundaryGridCover_subset hH hh hUV hsmall z hz)).trans
  convert markedRootBoxFaceTube_measure_le U V z (by positivity : 0 ≤ 20*H*h) hsmall using 1
  congr 1
  ring

theorem markedRootGridCell_boundary_subset {H h U V : ℝ}
    (hH : 0 ≤ H) (hh : 0 ≤ h) (hUV : 1 ≤ U*V) (hsmall : 20*H*h ≤ 1/2)
    (z : Fin 2 → ℝ) (hz : ∀ i,|z i| ≤ H) (cell : Set (ℝ × (ℝ × ℝ)))
    (hcell : cell ⊆ markedRootBoxDomain)
    (hdiam : ∀ p ∈ cell,∀ q ∈ cell,MarkedRootBoxClose h p q)
    (hface : ∃ q ∈ cell,q ∈ markedRootPhysicalBoxBoundary U V z) :
    cell ⊆ markedRootBoxFaceTube U V z (20*H*h) := by
  apply Set.Subset.trans _ (markedRootBoxBoundaryGridCover_subset hH hh hUV hsmall z hz)
  intro p hp
  obtain ⟨q,hq,hb⟩ := hface
  exact ⟨hcell hp,q,hcell hq,hb,hdiam p hp q hq⟩

end ArtinMatthews
