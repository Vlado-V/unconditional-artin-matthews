module

public import ArtinMatthews.SourceKPCompactH1Completion
public import ArtinMatthews.SourceKPCompactChartPlateau
public import ArtinMatthews.SourceKPCompactEnergyCover
public import ArtinMatthews.SourceKPCompactFormLocalization
public import ArtinMatthews.SourceKPCompactLocalizedEnergy
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

/-! Closability on the actual compact-cover quotient, from its genuine local closed graphs. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen Filter
open scoped NumberField MatrixGroups AdeleRing Topology BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "T" => SourceKPCompactFormCore K hζ
local notation "V" => SourceKPCompactH1 K hζ
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

theorem sourceKPCompactH1_eq_zero_of_mass_zero (u : V)
    (hu : sourceKPCompactH1Mass K hζ u = 0) : u = 0 := by
  let i := sourceKPCompactH1Core K hζ
  have hcl : u ∈ closure (Set.range i) := by
    rw [(sourceKPCompactH1Core_denseRange K hζ).closure_eq]
    exact Set.mem_univ u
  obtain ⟨z,hz,ht⟩ := mem_closure_iff_seq_limit.mp hcl
  choose f hf using hz
  have hfseq : Tendsto (fun n => i (f n)) atTop (𝓝 u) := by
    simpa only [hf] using ht
  have hm : Tendsto (fun n => sourceKPCompactFormCoreMassLinear K hζ (f n)) atTop (𝓝 0) := by
    have h := ((sourceKPCompactH1Mass K hζ).continuous.tendsto u).comp hfseq
    change Tendsto (fun n => sourceKPCompactH1Mass K hζ (i (f n))) atTop
      (𝓝 (sourceKPCompactH1Mass K hζ u)) at h
    simpa only [i,sourceKPCompactH1Mass_core,hu] using h
  choose b p hp using sourceKPUpperToCompact_cover K hζ
  choose η W hWo hWmem hWsub hη using
    (fun y : Y => sourceKPCompactChartPlateau_exists K hζ (b y) (p y))
  let e (n : ℕ) := sourceKPCompactCoreEnergy K hζ (f n).val
  have hlocal (y : Y) : Tendsto (fun n => ∫ x in W y, e n x ∂μ) atTop (𝓝 0) := by
    let L := sourceKPCompactH1Localization K hζ (b y) (p y) (η y)
    let G := h1EnergyGradient (InfinitePlace K)
    have hL : L u = 0 := sourceKPCompactH1Localization_zero_of_mass_zero K hζ (b y) (p y) (η y) u hu
    have hG : Tendsto (fun n => G (L (i (f n)))) atTop (𝓝 0) := by
      have h := ((G.continuous.comp L.continuous).tendsto u).comp hfseq
      change Tendsto (fun n => G (L (i (f n)))) atTop (𝓝 (G (L u))) at h
      rwa [hL,map_zero] at h
    have hG2 : Tendsto (fun n =>
        ‖h1TestGradient (sourceKPCompactCoreLocalized K hζ (f n).val (b y) (p y) (η y)).val‖ ^ 2)
        atTop (𝓝 0) := by
      simpa only [i,L,G,sourceKPCompactH1Localization_core,h1EnergyGradient_core,norm_zero,zero_pow
        (by decide : (2 : ℕ) ≠ 0)] using hG.norm.pow 2
    exact squeeze_zero
      (fun n => integral_nonneg (sourceKPCompactCoreEnergy_nonneg K hζ (f n).val))
      (fun n => sourceKPCompactCoreLocalized_energy_controls K hζ (f n).val (b y) (p y)
        (η y) (W y) (hWo y) (hWsub y) (hη y)) hG2
  have hbound (g : T) : ‖u‖ ^ 2 ≤ ‖u-i g‖ ^ 2 := by
    have hcover (y : Y) : y ∈ ⋃ x, W x := by
      have hy := hWmem y
      rw [hp y] at hy
      exact Set.mem_iUnion.mpr ⟨y,hy⟩
    obtain ⟨S,hS⟩ := g.val.prop.2.1.elim_finite_subcover W hWo (fun y _ => hcover y)
    have hsum : Tendsto (fun n => ∑ y ∈ S, ∫ x in W y, e n x ∂μ) atTop (𝓝 0) := by
      simpa only [Finset.sum_const_zero] using
        (tendsto_finsetSum S (a := fun _ => (0 : ℝ)) (fun y _ => hlocal y))
    have hd : Tendsto (fun n => ‖f n-g‖ ^ 2) atTop (𝓝 (‖u-i g‖ ^ 2)) := by
      simpa only [← map_sub,LinearIsometry.norm_map] using
        (hfseq.sub (tendsto_const_nhds (x := i g))).norm.pow 2
    have hl : Tendsto (fun n => ‖f n‖ ^ 2) atTop (𝓝 (‖u‖ ^ 2)) := by
      simpa only [LinearIsometry.norm_map] using hfseq.norm.pow 2
    have hr : Tendsto (fun n => ‖sourceKPCompactFormCoreMassLinear K hζ (f n)‖ ^ 2 +
        (‖f n-g‖ ^ 2 + ∑ y ∈ S, ∫ x in W y, e n x ∂μ)) atTop (𝓝 (‖u-i g‖ ^ 2)) := by
      simpa using (hm.norm.pow 2).add (hd.add hsum)
    apply le_of_tendsto_of_tendsto hl hr
    exact Eventually.of_forall fun n => by
      change ‖f n‖ ^ 2 ≤ ‖sourceKPCompactFormCoreMassLinear K hζ (f n)‖ ^ 2 +
        (‖f n-g‖ ^ 2 + ∑ y ∈ S, ∫ x in W y, e n x ∂μ)
      rw [sourceKPCompactFormCore_norm_sq]
      exact add_le_add (le_refl _) (sourceKPCompactCoreEnergy_le_cover K hζ g (f n) S W
        (fun y _ => (hWo y).measurableSet) hS)
  have hzero : ‖u‖ ^ 2 ≤ ‖u-u‖ ^ 2 :=
    (sourceKPCompactH1Core_denseRange K hζ).induction_on
      (p := fun v : V => ‖u‖ ^ 2 ≤ ‖u-v‖ ^ 2) u
      (isClosed_le continuous_const ((continuous_const.sub continuous_id).norm.pow 2)) hbound
  rw [sub_self,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)] at hzero
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg u]

theorem sourceKPCompactH1Mass_injective : Function.Injective (sourceKPCompactH1Mass K hζ) := by
  intro f g h
  apply sub_eq_zero.mp
  apply sourceKPCompactH1_eq_zero_of_mass_zero K hζ
  rw [map_sub,h,sub_self]

end
end ArtinMatthews
