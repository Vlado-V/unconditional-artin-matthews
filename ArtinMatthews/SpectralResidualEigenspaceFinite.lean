module

public import ArtinMatthews.SpectralResidualProbeProfile
public import ArtinMatthews.SpectralAmbientEnergyEigenspace
public import ArtinMatthews.SpectralAmbientCriticalEigenmodes
public import ArtinMatthews.SpectralCuspFiniteChartMean
public import ArtinMatthews.SpectralCuspGlobalOutgoingEigenmode
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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
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

/-! The residual eigenspace is genuinely finite dimensional. A fixed
finite family of compact probes is injective on it. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

def gamma0ResidualEnergyEigenspace (N : ℕ) [NeZero N] (l : ℝ) : Submodule ℂ (Gamma0RegionL2 N) :=
  gamma0AmbientEnergyEigenspace N l ⊓ (gamma0AllHeightCuspidalMassSpace N)ᗮ

theorem gamma0ResidualEigen_zero_of_probes (N : ℕ) [NeZero N] (l : ℝ) (hl : 0≤l)
    (m : Gamma0RegionL2 N) (hm : m∈gamma0ResidualEnergyEigenspace N l)
    (hprobe : ∀ i : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
      inner ℂ (gamma0ResidualProbeMass N i.out) m=0) : m=0 := by
  have hcus : m∈gamma0AllHeightCuspidalMassSpace N := by
    rcases le_or_gt (1/4:ℝ) l with hc | hc
    · exact gamma0AmbientEnergyEigenspace_cuspidal_of_critical N l hc m hm.1
    · apply gamma0Mass_cuspidal_of_finiteChart_means_zero N m
      intro i
      obtain ⟨u,hu,hp⟩ := gamma0AmbientEnergyEigenspace_energy_pencil N l hl m hm.1
      let a : ℝ := 1/2+Real.sqrt (1/4-l)
      let s : ℂ := (a:ℂ)
      let q : ℝ := 1-a
      obtain ⟨hs,hspec⟩ := gamma0SubcriticalEigen_parameter hl hc
      have hpu : gamma0EnergyResolventPencil N (s*(1-s)) u=0 := by rw [hspec]; exact hp
      obtain ⟨B,hB⟩ := gamma0EnergyMass_global_outgoing_eigenmode N i.out s hs u hpu
      rw [hu] at hB
      have hq : (q:ℂ)=1-s := by simp only [q,s,Complex.ofReal_sub,Complex.ofReal_one]
      rw [← hq] at hB
      have hzero := gamma0ResidualProbeMass_mode_zero N i.out m q B hB (hprobe i)
      change gamma0GlobalCuspConstantTerm N i.out m=ᵐ[volume.restrict (Ioi 0)] (fun _ => (0:ℂ))
      simpa only [hzero,zero_mul] using hB
  have horth := hm.2 m hcus
  exact inner_self_eq_zero.mp horth

def gamma0ResidualProbeMap (N : ℕ) [NeZero N] (l : ℝ) :
    gamma0ResidualEnergyEigenspace N l →ₗ[ℂ] ((SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) → ℂ) :=
  LinearMap.pi (fun i =>
    (innerSL ℂ (gamma0ResidualProbeMass N i.out)).toLinearMap.comp (gamma0ResidualEnergyEigenspace N l).subtype)

theorem gamma0ResidualProbeMap_injective (N : ℕ) [NeZero N] (l : ℝ) (hl : 0≤l) :
    Function.Injective (gamma0ResidualProbeMap N l) := by
  have hzero (m : gamma0ResidualEnergyEigenspace N l) (hm : gamma0ResidualProbeMap N l m=0) : m=0 := by
    apply Subtype.ext
    apply gamma0ResidualEigen_zero_of_probes N l hl m.val m.property
    intro i
    exact congrArg (fun v => v i) hm
  intro m n hmn
  have hz : gamma0ResidualProbeMap N l (m-n)=0 := by rw [map_sub,hmn,sub_self]
  exact sub_eq_zero.mp (hzero (m-n) hz)

theorem gamma0ResidualEnergyEigenspace_finiteDimensional (N : ℕ) [NeZero N] (l : ℝ) (hl : 0≤l) :
    FiniteDimensional ℂ (gamma0ResidualEnergyEigenspace N l) :=
  FiniteDimensional.of_injective (gamma0ResidualProbeMap N l) (gamma0ResidualProbeMap_injective N l hl)

end ArtinMatthews
