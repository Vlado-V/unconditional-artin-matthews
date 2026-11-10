module

public import ArtinMatthews.SpectralAmbientStieltjes
public import ArtinMatthews.SpectralContinuousAtomVector
public import ArtinMatthews.SpectralContinuousAtomOrthogonality
public import ArtinMatthews.SpectralContinuousQuadraticIntegral
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual ambient energy measure has full mass and its point masses
are exactly the orthogonal components in the genuine energy eigenspaces. -/
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ENNReal
namespace ArtinMatthews

theorem gamma0GreenPositiveSpectrum_compl_eq_zero (N : ℕ) [NeZero N] :
    (gamma0GreenPositiveSpectrum N)ᶜ=spectralQuadraticAtomSet (gamma0Green N) 0 := by
  ext x
  obtain ⟨r,hr,_,he⟩ := gamma0Green_spectrum_complex_mem_real_unit N x.property
  change (¬0<(x:ℂ).re) ↔ (x:ℂ)=0
  rw [he,Complex.ofReal_re,Complex.ofReal_eq_zero]
  exact ⟨fun h => le_antisymm (le_of_not_gt h) hr,fun h => by rw [h];exact lt_irrefl 0⟩

theorem gamma0GreenQuadraticMeasure_zero_atom (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) :
    gamma0GreenQuadraticMeasure N u (spectralQuadraticAtomSet (gamma0Green N) 0)=0 :=
  spectralQuadraticMeasure_atom_zero_of_injective (gamma0Green N)
    (gamma0Green_selfAdjoint N).isStarNormal (gamma0Green_injective N) u

theorem gamma0AmbientSpectralMeasure_univ (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) :
    gamma0AmbientSpectralMeasure N u univ=ENNReal.ofReal (‖u‖^2) := by
  unfold gamma0AmbientSpectralMeasure
  rw [Measure.map_apply (gamma0GreenEnergyCoordinate_measurable N) MeasurableSet.univ,
    preimage_univ,Measure.restrict_apply_univ]
  let μ := gamma0GreenQuadraticMeasure N u
  let U := gamma0GreenPositiveSpectrum N
  have hz : μ Uᶜ=0 := by
    change μ (gamma0GreenPositiveSpectrum N)ᶜ=0
    rw [gamma0GreenPositiveSpectrum_compl_eq_zero N]
    exact gamma0GreenQuadraticMeasure_zero_atom N u
  calc
    μ U = μ U+μ Uᶜ := by rw [hz,add_zero]
    _ = μ univ := measure_add_measure_compl (gamma0GreenPositiveSpectrum_measurable N)
    _ = _ := spectralQuadraticMeasure_univ (gamma0Green N) (gamma0Green_selfAdjoint N).isStarNormal u

def gamma0AmbientSpectralAtomVector (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) (l : ℝ) :
    Gamma0RegionL2 N :=
  spectralQuadraticAtomVector (gamma0Green N) (gamma0Green_selfAdjoint N).isStarNormal u (((l+1)⁻¹:ℝ):ℂ)

theorem gamma0AmbientSpectralAtomVector_green (N : ℕ) [NeZero N]
    (u : Gamma0RegionL2 N) (l : ℝ) :
    gamma0Green N (gamma0AmbientSpectralAtomVector N u l)=
      (((l+1)⁻¹:ℝ):ℂ) • gamma0AmbientSpectralAtomVector N u l :=
  spectralQuadraticAtomVector_eigen (gamma0Green N) (gamma0Green_selfAdjoint N).isStarNormal u _

theorem gamma0AmbientSpectralAtomVector_orthogonal (N : ℕ) [NeZero N]
    (u w : Gamma0RegionL2 N) (l : ℝ) (hw : gamma0Green N w=(((l+1)⁻¹:ℝ):ℂ) • w) :
    inner ℂ w (u-gamma0AmbientSpectralAtomVector N u l)=0 :=
  spectralQuadraticAtomVector_orthogonal (gamma0Green N) (gamma0Green_selfAdjoint N) u w _ hw

theorem gamma0GreenEnergyCoordinate_atom_preimage (N : ℕ) [NeZero N]
    (l : ℝ) (hl : 0≤l) :
    ((gamma0GreenEnergyCoordinate N) ⁻¹' {l})∩gamma0GreenPositiveSpectrum N=
      spectralQuadraticAtomSet (gamma0Green N) (((l+1)⁻¹:ℝ):ℂ) := by
  ext x
  obtain ⟨r,_,_,he⟩ := gamma0Green_spectrum_complex_mem_real_unit N x.property
  simp only [mem_inter_iff,mem_preimage,mem_singleton_iff,gamma0GreenEnergyCoordinate,
    gamma0GreenPositiveSpectrum,spectralQuadraticAtomSet,mem_ofPred_eq,he,Complex.ofReal_re,Complex.ofReal_inj]
  constructor
  · rintro ⟨h,_⟩
    have hR : r⁻¹=l+1 := by linarith
    simpa only [inv_inv] using congrArg Inv.inv hR
  · intro h
    rw [h,inv_inv]
    exact ⟨by ring,inv_pos.mpr (by linarith)⟩

theorem gamma0AmbientSpectralMeasure_atom (N : ℕ) [NeZero N]
    (u : Gamma0RegionL2 N) (l : ℝ) (hl : 0≤l) :
    gamma0AmbientSpectralMeasure N u {l}=ENNReal.ofReal (‖gamma0AmbientSpectralAtomVector N u l‖^2) := by
  unfold gamma0AmbientSpectralMeasure
  rw [Measure.map_apply (gamma0GreenEnergyCoordinate_measurable N) (measurableSet_singleton l),
    Measure.restrict_apply ((gamma0GreenEnergyCoordinate_measurable N) (measurableSet_singleton l)),
    gamma0GreenEnergyCoordinate_atom_preimage N l hl]
  exact spectralQuadraticMeasure_atom (gamma0Green N) (gamma0Green_selfAdjoint N).isStarNormal u _

theorem gamma0AmbientSpectralAtomVector_energy_pencil (N : ℕ) [NeZero N]
    (u : Gamma0RegionL2 N) (l : ℝ) (hl : 0≤l) :
    ∃ v : gamma0EnergySpace N, gamma0EnergyInclusion N v=gamma0AmbientSpectralAtomVector N u l ∧
      gamma0EnergyResolventPencil N (l:ℂ) v=0 := by
  let m := gamma0AmbientSpectralAtomVector N u l
  let a : ℂ := ((l+1:ℝ):ℂ)
  let v := a • gamma0EnergyMassAdjoint N m
  have ha : a≠0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hG : gamma0Green N m=a⁻¹ • m := by
    simpa only [a,Complex.ofReal_inv] using gamma0AmbientSpectralAtomVector_green N u l
  have hv : gamma0EnergyInclusion N v=m := by
    rw [show v=a • gamma0EnergyMassAdjoint N m from rfl,map_smul]
    change a • gamma0Green N m=m
    rw [hG,smul_smul,mul_inv_cancel₀ ha,one_smul]
  refine ⟨v,hv,?_⟩
  change v-((l:ℂ)+1) • gamma0EnergyMassAdjoint N (gamma0EnergyInclusion N v)=0
  have he : (l:ℂ)+1=a := by simp [a]
  rw [hv,he]
  exact sub_self _

end ArtinMatthews
